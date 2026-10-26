/*
 * PvP Life
 * Copyright (C) 2026 iCore
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "PvPLifeMgr.h"
#include "PvPLifeDuelSelection.h"
#include "PvPLifeDuelRequestPolicy.h"
#include "PvPLifeAudit.h"
#include "LifeBotReservation.h"

#include "Chat.h"
#include "Config.h"
#include "DatabaseEnv.h"
#include "DBCStores.h"
#include "GameTime.h"
#include "Group.h"
#include "Log.h"
#include "Map.h"
#include "MapMgr.h"
#include "MotionMaster.h"
#include "ObjectAccessor.h"
#include "ObjectGuid.h"
#include "Opcodes.h"
#include "Player.h"
#include "PlayerbotAI.h"
#include "Playerbots.h"
#include "PositionValue.h"
#include "Random.h"
#include "RandomPlayerbotMgr.h"
#include "SharedDefines.h"
#include "SocialMgr.h"
#include "SpellInfo.h"
#include "SpellMgr.h"
#include "StringFormat.h"
#include "World.h"
#include "WorldPacket.h"
#include "WorldSession.h"
#include "WorldSessionMgr.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <set>
#include <sstream>
#include <shared_mutex>

namespace
{
    inline bool IsLifeBotReserved(uint32 guidLow)
    {
        return PlayerbotsLife::IsReserved(guidLow);
    }

    std::string Lower(std::string value)
    {
        std::transform(value.begin(), value.end(), value.begin(),
            [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
        return value;
    }

    std::vector<std::string> Tokenize(std::string const& text)
    {
        std::istringstream stream(text);
        std::vector<std::string> out;
        std::string token;
        while (stream >> token)
            out.push_back(token);
        return out;
    }

    uint32 GameTimeSeconds()
    {
        return static_cast<uint32>(GameTime::GetGameTime().count());
    }

    uint32 GameTimeMS()
    {
        return static_cast<uint32>(GameTime::GetGameTimeMS().count());
    }

    char const* TypeName(PvPLife::ActivityType type)
    {
        switch (type)
        {
            case PvPLife::ActivityType::Skirmish: return "Skirmish";
            case PvPLife::ActivityType::Duel: return "Duel";
            case PvPLife::ActivityType::ForTheHorde: return "ForTheHorde";
            case PvPLife::ActivityType::ForTheAlliance: return "ForTheAlliance";
        }
        return "Unknown";
    }

    char const* TeamName(PvPLife::TeamSide team)
    {
        switch (team)
        {
            case PvPLife::TeamSide::Alliance: return "Alliance";
            case PvPLife::TeamSide::Horde: return "Horde";
            default: return "Any";
        }
    }

    bool ParseTeam(std::string token, PvPLife::TeamSide& out)
    {
        token = Lower(token);
        if (token == "a" || token == "ally" || token == "alliance")
        {
            out = PvPLife::TeamSide::Alliance;
            return true;
        }
        if (token == "h" || token == "horde")
        {
            out = PvPLife::TeamSide::Horde;
            return true;
        }
        if (token == "any" || token == "both")
        {
            out = PvPLife::TeamSide::Any;
            return true;
        }
        return false;
    }

    bool ParseType(std::string token, PvPLife::ActivityType& out)
    {
        token = Lower(token);
        if (token == "skirmish" || token == "world" || token == "worldpvp")
        {
            out = PvPLife::ActivityType::Skirmish;
            return true;
        }
        if (token == "duel")
        {
            out = PvPLife::ActivityType::Duel;
            return true;
        }
        if (token == "forthehorde" || token == "fth")
        {
            out = PvPLife::ActivityType::ForTheHorde;
            return true;
        }
        if (token == "forthealliance" || token == "fta" || token == "fortheally")
        {
            out = PvPLife::ActivityType::ForTheAlliance;
            return true;
        }
        return false;
    }
}

namespace PvPLife
{
    Manager& Manager::Instance()
    {
        static Manager instance;
        return instance;
    }

    void Manager::AuditLog(std::string const& tag, std::string const& text) const
    {
        if (_auditEnable)
            sPvPLifeAudit.Log(tag, text);
    }

    void Manager::Shutdown()
    {
        ++_dataGeneration;
        PlayerbotsLife::CancelAdmissionRequest(0, PlayerbotsLife::ReservationOwner::PvPLife);
        for (ActiveEvent& e : _activeEvents)
            EndEvent(e, "shutdown");
        _activeEvents.clear();
        _moveQueue.clear();
        _duelQueue.clear();
        _engagementQueue.clear();
        _chatQueue.clear();

        for (ReleasingParticipant const& rp : _releasingParticipants)
        {
            if (rp.Part.Token.GuidLow != 0)
                PlayerbotsLife::ReleaseLeaseExact(const_cast<PlayerbotsLife::LeaseToken&>(rp.Part.Token));
        }
        _releasingParticipants.clear();

        for (PendingRaidResponse& p : _pendingResponses)
        {
            for (BotCandidate const& b : p.Bots)
            {
                if (b.Token.GuidLow != 0)
                    PlayerbotsLife::ReleaseLeaseExact(const_cast<PlayerbotsLife::LeaseToken&>(b.Token));
            }
            p.Bots.clear();
            p.Cancelled = true;
        }
        _pendingResponses.clear();
        _botLastRelocateTime.clear();

        sPvPLifeAudit.Shutdown();
    }

    void Manager::LoadConfig()
    {
        for (ActiveEvent& event : _activeEvents)
            if (!event.FullyPrepared)
                EndEvent(event, "config-reload");
        CancelPendingRaidResponse(0, "config-reload");
        ++_dataGeneration;
        _lastCensusTimeMs = 0;
        bool prevEnable = _enable;
        _enable = sConfigMgr->GetOption<bool>("PvPLife.Enable", true);
        if (prevEnable && !_enable)
        {
            _draining = true;
            for (ActiveEvent& e : _activeEvents)
                EndEvent(e, "config-disabled");
            _activeEvents.clear();
            CancelPendingRaidResponse(0, "config-disabled");
            _moveQueue.clear();
            _duelQueue.clear();
            _engagementQueue.clear();
            _chatQueue.clear();
            _botLastRelocateTime.clear();
            _draining = false;
        }

        _debug = sConfigMgr->GetOption<bool>("PvPLife.Debug", false);
        _announce = sConfigMgr->GetOption<bool>("PvPLife.Announce", false);
        _startupDelaySeconds = sConfigMgr->GetOption<uint32>("PvPLife.StartupDelaySeconds", 90);
        _tickSeconds = std::max<uint32>(5, sConfigMgr->GetOption<uint32>("PvPLife.TickSeconds", 20));
        _maxActiveEvents = sConfigMgr->GetOption<uint32>("PvPLife.Events.MaxActive", 0);

        // 2. Bot Selection & Filtering
        _requireBotEligibility = sConfigMgr->GetOption<bool>("PvPLife.Bots.RequireBotEligibility", true);
        _usePlayerbotConfig = sConfigMgr->GetOption<bool>("PvPLife.Bots.UsePlayerbotConfig", true);
        _botAccountPrefix = sConfigMgr->GetOption<std::string>("PvPLife.Bots.AccountPrefix", "auto");
        _botAccountMin = sConfigMgr->GetOption<uint32>("PvPLife.Bots.AccountMin", 0);
        _botAccountMax = sConfigMgr->GetOption<uint32>("PvPLife.Bots.AccountMax", 0);
        std::string filterModeStr = Lower(sConfigMgr->GetOption<std::string>("PvPLife.Bots.AccountFilterMode", "legacy_any"));
        _accountFilterMode = (filterModeStr == "all") ? AccountFilterMode::All : AccountFilterMode::LegacyAny;

        _botQueryLimit = sConfigMgr->GetOption<uint32>("PvPLife.Bots.QueryLimit", 500);
        _minOnlineRequired = sConfigMgr->GetOption<uint32>("PvPLife.Bots.MinOnlineRequired", 2);
        _globalMinLevel = static_cast<uint8>(std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Bots.GlobalMinLevel", 20), 1, 80));

        _skipGroupedBots = sConfigMgr->GetOption<bool>("PvPLife.Bots.SkipGrouped", true);
        _respectPlayerbotActivity = sConfigMgr->GetOption<bool>("PvPLife.Bots.RespectPlayerbotActivity", false);
        _allowPartialTeams = sConfigMgr->GetOption<bool>("PvPLife.Bots.AllowPartialTeams", true);
        _minimumBotsPerSide = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Bots.MinimumPerSide", 1), 1, 10);
        _maxBotsPerSide = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Bots.MaxPerSide", 100), 1, 200);
        _minimumBotsPerSide = std::min(_minimumBotsPerSide, _maxBotsPerSide);
        _returnBots = sConfigMgr->GetOption<bool>("PvPLife.Bots.ReturnAfterActivity", true);

        // 3. Movement & Combat
        _teleportOnArrival = sConfigMgr->GetOption<bool>("PvPLife.Movement.TeleportOnArrival", true);
        _useMovePoint = sConfigMgr->GetOption<bool>("PvPLife.Movement.UseMovePoint", true);
        _hardTeleportToTarget = sConfigMgr->GetOption<bool>("PvPLife.Movement.HardTeleportToTarget", false);
        _positionJitter = sConfigMgr->GetOption<uint32>("PvPLife.Movement.PositionJitter", 10);
        _arrivalStaggerMin = sConfigMgr->GetOption<uint32>("PvPLife.Movement.ArrivalStaggerMinSeconds", 2);
        _arrivalStaggerMax = sConfigMgr->GetOption<uint32>("PvPLife.Movement.ArrivalStaggerMaxSeconds", 12);
        _moveAfterArrivalMin = sConfigMgr->GetOption<uint32>("PvPLife.Movement.MoveAfterArrivalMinSeconds", 6);
        _moveAfterArrivalMax = sConfigMgr->GetOption<uint32>("PvPLife.Movement.MoveAfterArrivalMaxSeconds", 20);

        _strategiesEnable = sConfigMgr->GetOption<bool>("PvPLife.Strategies.Enable", true);
        _forcePvpFlag = sConfigMgr->GetOption<bool>("PvPLife.Combat.ForcePvpFlag", true);
        _forceAttackOnEngage = sConfigMgr->GetOption<bool>("PvPLife.Combat.ForceAttackOnEngage", true);
        _engageAfterMoveSeconds = sConfigMgr->GetOption<uint32>("PvPLife.Combat.EngageAfterMoveSeconds", 4);
        _engageRetrySeconds = std::max<uint32>(1, sConfigMgr->GetOption<uint32>("PvPLife.Combat.EngageRetrySeconds", 5));
        _engageMaxRetries = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Combat.EngageMaxRetries", 12), 1, 50);

        _pvpCombatStrategies = sConfigMgr->GetOption<std::string>("PvPLife.Strategies.Combat", "+pvp,+boost,+dps debuff,-passive,-stay,-chat,-emote,-rpg,-travel");
        _pvpNonCombatStrategies = sConfigMgr->GetOption<std::string>("PvPLife.Strategies.NonCombat", "+pvp,+boost,-passive,-stay,-chat,-emote,-rpg,-travel");
        _duelNonCombatStrategies = sConfigMgr->GetOption<std::string>("PvPLife.Strategies.DuelNonCombat", "+duel,+pvp,+boost,+stay,-follow,-passive,-grind,-chat,-emote,-rpg,-travel");

        // 4. Persistent World PvP
        _alwaysActiveWorldPvp = sConfigMgr->GetOption<bool>("PvPLife.World.AlwaysActive", true);
        _minActiveSkirmishes = sConfigMgr->GetOption<uint32>("PvPLife.World.MinActiveHotspots", 1);
        _maxActiveSkirmishes = std::max(_minActiveSkirmishes, sConfigMgr->GetOption<uint32>("PvPLife.World.MaxActiveHotspots", 3));
        _randomSkirmishChance = std::min<uint32>(100, sConfigMgr->GetOption<uint32>("PvPLife.World.RandomStartChance", 35));

        // 5. Duel Zones
        _duelEnable = sConfigMgr->GetOption<bool>("PvPLife.Duel.Enable", true);
        _duelAlwaysActive = sConfigMgr->GetOption<bool>("PvPLife.Duel.AlwaysActive", true);
        _duelSpellId = sConfigMgr->GetOption<uint32>("PvPLife.Duel.SpellId", 7266);
        _duelPairLimit = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Duel.PairLimit", 12), 1, 40);
        _duelPairDelayMin = sConfigMgr->GetOption<uint32>("PvPLife.Duel.PairDelayMinSeconds", 5);
        _duelPairDelayMax = sConfigMgr->GetOption<uint32>("PvPLife.Duel.PairDelayMaxSeconds", 18);
        _duelLeashRadius = std::max<uint32>(10, sConfigMgr->GetOption<uint32>("PvPLife.Duel.LeashRadius", 40));
        _duelGuardIntervalMs = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Duel.GuardIntervalMs", 1000), 250, 5000);
        _challengeRealPlayers = sConfigMgr->GetOption<bool>("PvPLife.Duel.ChallengeRealPlayers", true);
        _realPlayerChallengeChance = std::min<uint32>(100, sConfigMgr->GetOption<uint32>("PvPLife.Duel.PlayerChallengeChance", 25));
        _realPlayerScanRadius = sConfigMgr->GetOption<uint32>("PvPLife.Duel.PlayerScanRadius", 55);
        _realPlayerMaxLevelDifference = sConfigMgr->GetOption<uint32>("PvPLife.Duel.MaxLevelDifference", 5);
        _realPlayerCooldownSeconds = sConfigMgr->GetOption<uint32>("PvPLife.Duel.PlayerChallengeCooldownSeconds", 900);
        _botChallengeCooldownSeconds = sConfigMgr->GetOption<uint32>("PvPLife.Duel.BotChallengeCooldownSeconds", 180);
        _botDuelCooldownSeconds = sConfigMgr->GetOption<uint32>("PvPLife.Duel.BotVsBotCooldownSeconds", 45);
        _botDuelMaxLevelDifference = sConfigMgr->GetOption<uint32>("PvPLife.Duel.BotVsBotMaxLevelDifference", 5);
        _duelRelocateCooldownSeconds = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Duel.RelocateCooldownSeconds", 20), 5, 120);

        // 6. Campaigns & Chat
        _forTheHordeEnable = sConfigMgr->GetOption<bool>("PvPLife.ForTheHorde.Enable", true);
        _forTheAllianceEnable = sConfigMgr->GetOption<bool>("PvPLife.ForTheAlliance.Enable", true);
        _factionCampaignChance = std::min<uint32>(100, sConfigMgr->GetOption<uint32>("PvPLife.FactionCampaign.ChancePerTick", 12));
        _factionCampaignGlobalCooldown = sConfigMgr->GetOption<uint32>("PvPLife.FactionCampaign.GlobalCooldownSeconds", 3600);

        _botChatEnable = sConfigMgr->GetOption<bool>("PvPLife.BotChat.Enable", false);
        _botChatYellChance = std::min<uint32>(100, sConfigMgr->GetOption<uint32>("PvPLife.BotChat.YellChance", 0));
        _botChatWorldChance = std::min<uint32>(100, sConfigMgr->GetOption<uint32>("PvPLife.BotChat.WorldChance", 0));

        // 7. Reactive Raid Response
        _reactiveEnable = sConfigMgr->GetOption<bool>("PvPLife.ReactiveRaidResponse.Enable", true);
        _reactiveAllianceEnable = sConfigMgr->GetOption<bool>("PvPLife.ReactiveRaidResponse.AllianceEnable", true);
        _reactiveHordeEnable = sConfigMgr->GetOption<bool>("PvPLife.ReactiveRaidResponse.HordeEnable", true);
        _reactiveMinGroupSize = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.MinGroupSize", 20), 2, 40);
        _reactiveMaxResponders = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.MaxResponders", 25), 1, 40);
        std::string lvlModeStr = Lower(sConfigMgr->GetOption<std::string>("PvPLife.ReactiveRaidResponse.LevelMode", "raid"));
        _reactiveLevelMode = (lvlModeStr == "fixed") ? ResponderLevelMode::Fixed : ResponderLevelMode::Raid;
        _reactiveFixedLevel = static_cast<uint8>(std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.FixedLevel", 60), 1, 80));
        _reactiveMaxLevelDifference = static_cast<uint8>(std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.MaxLevelDifference", 5), 0, 30));

        _reactiveLoginOfflineBots = sConfigMgr->GetOption<bool>("PvPLife.ReactiveRaidResponse.LoginOfflineBots", false);
        _reactiveLoginDelaySeconds = std::max<uint32>(1, sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.LoginDelaySeconds", 20));
        _reactiveLoginTimeoutSeconds = std::max<uint32>(_reactiveLoginDelaySeconds + 5, sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.LoginTimeoutSeconds", 60));
        _reactiveMaxConcurrentLogins = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.MaxConcurrentLogins", 4), 1, 20);
        _reactiveCooldownSeconds = sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.CooldownSeconds", 1800);
        _reactiveDurationMinutes = std::max<uint32>(1, sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.DurationMinutes", 20));
        _reactiveRallyDistance = std::max<float>(20.0f, sConfigMgr->GetOption<float>("PvPLife.ReactiveRaidResponse.RallyDistance", 120.0f));
        _reactiveLaneSpacing = std::max<float>(1.0f, sConfigMgr->GetOption<float>("PvPLife.ReactiveRaidResponse.LaneSpacing", 4.0f));
        _reactiveFormationColumns = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.ReactiveRaidResponse.FormationColumns", 9), 1, 15);
        _reactiveAdvanceDistance = std::max<float>(5.0f, sConfigMgr->GetOption<float>("PvPLife.ReactiveRaidResponse.AdvanceDistance", 25.0f));

        // 8. Population Borrowing Budget
        _populationBudgetEnable = sConfigMgr->GetOption<bool>("PvPLife.Population.Enable", true);
        std::string budgetModeStr = Lower(sConfigMgr->GetOption<std::string>("PvPLife.Population.BudgetMode", "percentage"));
        _budgetMode = (budgetModeStr == "fixed") ? BudgetMode::Fixed : BudgetMode::Percentage;
        _fixedCount = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Population.FixedCount", 100), 2, 500);
        _borrowPercent = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Population.BorrowPercent", 10), 1, 100);
        _maxTotal = sConfigMgr->GetOption<uint32>("PvPLife.Population.MaxTotal", 120);
        if (_maxTotal > 1000)
            _maxTotal = 1000;
        std::string demandModeStr = Lower(sConfigMgr->GetOption<std::string>("PvPLife.Population.DemandMode", "hybrid"));
        if (demandModeStr == "fixed")
            _demandMode = DemandMode::Fixed;
        else if (demandModeStr == "dynamic")
            _demandMode = DemandMode::Dynamic;
        else
            _demandMode = DemandMode::Hybrid;
        _baselinePercent = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Population.BaselinePercent", 20), 1, 100);
        _burstGraceSeconds = sConfigMgr->GetOption<uint32>("PvPLife.Population.BurstGraceSeconds", 180);
        _maxChangesPerTick = std::clamp<uint32>(sConfigMgr->GetOption<uint32>("PvPLife.Population.MaxChangesPerTick", 3), 1, 20);
        _proportionalZoneScaling = sConfigMgr->GetOption<bool>("PvPLife.Population.ProportionalZoneScaling", true);

        // 9. Compatibility & Anti-Stealing Barrier
        _harmonyEnable = sConfigMgr->GetOption<bool>("PvPLife.Compatibility.CityLife.EnableHarmony", true);
        _respectCityLifeReservations = sConfigMgr->GetOption<bool>("PvPLife.Compatibility.CityLife.RespectReservations", true);
        _excludeCityLifeAccounts = sConfigMgr->GetOption<bool>("PvPLife.Compatibility.CityLife.ExcludeCityLifeAccounts", true);
        _independentHookProcessing = sConfigMgr->GetOption<bool>("PvPLife.Compatibility.CityLife.IndependentHookProcessing", true);

        // 10. Audit Logging
        _auditEnable = sConfigMgr->GetOption<bool>("PvPLife.Audit.Enable", true);
        _auditFilePath = sConfigMgr->GetOption<std::string>("PvPLife.Audit.FilePath", "Logs/pvplife_audit.log");
        sPvPLifeAudit.Configure(_auditEnable, _auditFilePath);

        // Sanity adjustments
        if (_arrivalStaggerMax < _arrivalStaggerMin)
            _arrivalStaggerMax = _arrivalStaggerMin;
        if (_moveAfterArrivalMax < _moveAfterArrivalMin)
            _moveAfterArrivalMax = _moveAfterArrivalMin;
        if (_duelPairDelayMax < _duelPairDelayMin)
            _duelPairDelayMax = _duelPairDelayMin;

        ImportPlayerbotDefaults();
        _botAccountCache.clear();
        RefreshAccountCache();
        _offlineCandidateCache.clear();
        _offlineCandidateRefresh.clear();
        _offlineCandidateQueries.clear();
        if (!_botChatEnable)
            _chatQueue.clear();
        if (_botChatYellChance == 0)
            _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
                [](ChatStep const& s) { return s.Channel == ChatChannel::Yell; }), _chatQueue.end());
        if (_botChatWorldChance == 0)
            _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
                [](ChatStep const& s) { return s.Channel == ChatChannel::World; }), _chatQueue.end());
        for (ActiveEvent& event : _activeEvents)
            if ((event.EventZone.Type == ActivityType::Duel && !_duelEnable) ||
                (event.EventZone.Type == ActivityType::ForTheHorde && !_forTheHordeEnable) ||
                (event.EventZone.Type == ActivityType::ForTheAlliance && !_forTheAllianceEnable))
                EndEvent(event, "activity-disabled");
        _zoneConfig.clear();
        _startupElapsedMs = 0;
        _timerMs = 0;
        _duelGuardTimerMs = 0;

        if (!_requireBotEligibility)
        {
            LOG_ERROR("module", "[PvPLife] SAFETY CHECK FAILED: PvPLife.Bots.RequireBotEligibility must be enabled.");
            _enable = false;
        }

        _databaseReady = VerifyDatabase();
        if (_enable && !_databaseReady)
            _enable = false;
        if (_databaseReady)
            LoadZoneConfig();

        LOG_INFO("module", "[PvPLife] Master: enable={} DB={} alwaysWorld={} duel={} reactive={} budget={}({}%) "
            "prefix='{}' globalMinLvl={} respectReservations={}",
            _enable ? 1 : 0, _databaseReady ? 1 : 0, _alwaysActiveWorldPvp ? 1 : 0, _duelEnable ? 1 : 0,
            _reactiveEnable ? 1 : 0, _populationBudgetEnable ? 1 : 0, _borrowPercent,
            _botAccountPrefix, _globalMinLevel, _respectCityLifeReservations ? 1 : 0);

        AuditLog("CONFIG", "enabled=" + std::to_string(_enable ? 1 : 0) + " prefix=" + _botAccountPrefix +
            " globalMin=" + std::to_string(_globalMinLevel) + " budgetPercent=" + std::to_string(_borrowPercent) +
            " reactive=" + std::to_string(_reactiveEnable ? 1 : 0));
    }

    void Manager::ImportPlayerbotDefaults()
    {
        if (!_usePlayerbotConfig)
            return;

        std::string configuredPrefix = sConfigMgr->GetOption<std::string>("Playerbots.RandomBotAccountPrefix",
            sConfigMgr->GetOption<std::string>("AiPlayerbot.RandomBotAccountPrefix", "rndbot", false), false);
        uint32 loginDelay = sConfigMgr->GetOption<uint32>("Playerbots.DisabledWithoutRealPlayerLoginDelay",
            sConfigMgr->GetOption<uint32>("AiPlayerbot.DisabledWithoutRealPlayerLoginDelay", 30, false), false);
        std::string lowered = Lower(_botAccountPrefix);
        if (lowered.empty() || lowered == "auto" || lowered == "playerbot" || lowered == "playerbots")
            _botAccountPrefix = configuredPrefix;
        _startupDelaySeconds = std::max(_startupDelaySeconds, loginDelay);
    }

    bool Manager::VerifyDatabase()
    {
        if (!WorldDatabase.Query("SHOW TABLES LIKE 'pvp_life_zone'"))
        {
            LOG_ERROR("module", "[PvPLife] Missing WORLD table pvp_life_zone. Apply data/sql/manual/world_pvp_life.sql");
            return false;
        }
        if (!WorldDatabase.Query("SHOW TABLES LIKE 'pvp_life_chat'"))
        {
            LOG_ERROR("module", "[PvPLife] Missing WORLD table pvp_life_chat. Apply data/sql/manual/world_pvp_life.sql");
            return false;
        }

        QueryResult columnsResult = WorldDatabase.Query("SHOW COLUMNS FROM pvp_life_zone");
        if (!columnsResult)
        {
            LOG_ERROR("module", "[PvPLife] Failed to inspect columns of pvp_life_zone.");
            return false;
        }

        std::unordered_set<std::string> columns;
        do
        {
            Field* fields = columnsResult->Fetch();
            columns.insert(Lower(fields[0].Get<std::string>()));
        } while (columnsResult->NextRow());

        static const std::vector<std::string> requiredCols = {
            "id", "name", "enabled", "activity_type", "attacker_team", "defender_team",
            "min_level", "max_level", "map_id", "rally_x", "rally_y", "rally_z", "rally_o",
            "target_x", "target_y", "target_z", "target_o", "attackers_min", "attackers_max",
            "defenders_min", "defenders_max", "duration_min", "duration_max", "weight",
            "cooldown_seconds", "last_start", "challenge_players", "bot_chat"
        };

        for (std::string const& col : requiredCols)
        {
            if (!columns.count(col))
            {
                LOG_ERROR("module", "[PvPLife] Table pvp_life_zone is missing required column '{}'. Please apply latest database updates.", col);
                return false;
            }
        }

        return true;
    }

    std::string Manager::ZoneSelectSql(std::string const& suffix) const
    {
        return "SELECT id,name,enabled,activity_type,attacker_team,defender_team,min_level,max_level,map_id,"
               "rally_x,rally_y,rally_z,rally_o,target_x,target_y,target_z,target_o,"
               "attackers_min,attackers_max,defenders_min,defenders_max,duration_min,duration_max,weight,"
               "cooldown_seconds,last_start,challenge_players,bot_chat FROM pvp_life_zone " + suffix;
    }

    Zone Manager::ReadZone(Field* f)
    {
        Zone z;
        z.Id = f[0].Get<uint32>();
        z.Name = f[1].Get<std::string>();
        z.Enabled = f[2].Get<uint8>() != 0;
        z.Type = static_cast<ActivityType>(f[3].Get<uint8>());
        z.AttackerTeam = static_cast<TeamSide>(f[4].Get<uint8>());
        z.DefenderTeam = static_cast<TeamSide>(f[5].Get<uint8>());
        if (z.Type == ActivityType::Skirmish && z.AttackerTeam != TeamSide::Any && z.AttackerTeam == z.DefenderTeam)
            z.Type = ActivityType::Duel;
        z.MinLevel = f[6].Get<uint8>();
        z.MaxLevel = f[7].Get<uint8>();
        z.MapId = f[8].Get<uint32>();
        z.RallyX = f[9].Get<float>(); z.RallyY = f[10].Get<float>(); z.RallyZ = f[11].Get<float>(); z.RallyO = f[12].Get<float>();
        z.TargetX = f[13].Get<float>(); z.TargetY = f[14].Get<float>(); z.TargetZ = f[15].Get<float>(); z.TargetO = f[16].Get<float>();
        z.AttackersMin = f[17].Get<uint32>(); z.AttackersMax = f[18].Get<uint32>();
        z.DefendersMin = f[19].Get<uint32>(); z.DefendersMax = f[20].Get<uint32>();
        z.PopulationMin = z.AttackersMin + z.DefendersMin;
        z.PopulationMax = z.AttackersMax + z.DefendersMax;
        z.DurationMin = f[21].Get<uint32>(); z.DurationMax = f[22].Get<uint32>();
        z.Weight = f[23].Get<uint32>(); z.CooldownSeconds = f[24].Get<uint32>(); z.LastStart = f[25].Get<uint32>();
        z.ChallengePlayers = f[26].Get<uint8>() != 0;
        z.BotChat = f[27].Get<uint8>() != 0;
        z.ZoneId = sMapMgr->GetZoneId(PHASEMASK_NORMAL, z.MapId, z.RallyX, z.RallyY, z.RallyZ);
        return z;
    }

    void Manager::LoadZoneConfig()
    {
        uint64 generation = _dataGeneration;
        uint64 snapshot = ++_zoneSnapshotGeneration;
        _queryProcessor.AddCallback(WorldDatabase.AsyncQuery(ZoneSelectSql("ORDER BY id")).WithCallback(
            [this, generation, snapshot](QueryResult result)
            {
                if (generation != _dataGeneration || snapshot != _zoneSnapshotGeneration)
                    return;
                if (!result)
                {
                    _zoneCache.clear();
                    _zoneConfig.clear();
                    LOG_WARN("module", "[PvPLife] Zone snapshot is empty or unavailable; no new zones scheduled.");
                    return;
                }
                _zoneConfig.clear();
                _zoneCache.clear();
                uint32 minimumPopulation = _minimumBotsPerSide * 2;
                uint32 maximumPopulation = _maxBotsPerSide * 2;
                do
                {
                    Zone zone = ReadZone(result->Fetch());
                    ZoneConfig config;
                    std::string prefix = "PvPLife.Zone." + zone.Name;
                    config.Enabled = sConfigMgr->GetOption<bool>(prefix + ".Enable", zone.Enabled, false);
                    config.MinPopulation = std::clamp<uint32>(
                        sConfigMgr->GetOption<uint32>(prefix + ".MinPopulation", zone.PopulationMin, false),
                        minimumPopulation, maximumPopulation);
                    config.MaxPopulation = std::clamp<uint32>(
                        sConfigMgr->GetOption<uint32>(prefix + ".MaxPopulation", zone.PopulationMax, false),
                        config.MinPopulation, maximumPopulation);
                    _zoneConfig[zone.Name] = config;
                    _zoneCache.push_back(zone);
                } while (result->NextRow());
            }));
        _queryProcessor.AddCallback(WorldDatabase.AsyncQuery(
            "SELECT activity_type,channel,speaker_team,text,weight FROM pvp_life_chat WHERE enabled=1 ORDER BY id").WithCallback(
            [this, generation, snapshot](QueryResult result)
            {
                if (generation != _dataGeneration || snapshot != _zoneSnapshotGeneration)
                    return;
                std::vector<CachedChatLine> lines;
                if (result)
                    do
                    {
                        Field* fields = result->Fetch();
                        lines.push_back({ static_cast<ActivityType>(fields[0].Get<uint8>()),
                            static_cast<ChatChannel>(fields[1].Get<uint8>()),
                            static_cast<TeamSide>(fields[2].Get<uint8>()), fields[3].Get<std::string>(),
                            std::max<uint32>(1, fields[4].Get<uint32>()) });
                    } while (result->NextRow());
                _chatCache = std::move(lines);
            }));
    }

    void Manager::ApplyZoneConfig(Zone& zone) const
    {
        auto it = _zoneConfig.find(zone.Name);
        if (it != _zoneConfig.end())
        {
            zone.Enabled = it->second.Enabled;
            zone.PopulationMin = it->second.MinPopulation;
            zone.PopulationMax = it->second.MaxPopulation;
        }
    }

    std::vector<Zone> Manager::LoadZones(bool readyOnly, int typeFilter)
    {
        std::vector<Zone> zones;
        uint32 now = GameTimeSeconds();
        for (Zone zone : _zoneCache)
        {
            ApplyZoneConfig(zone);
            if (!zone.Enabled || !zone.Weight || (typeFilter >= 0 && int(zone.Type) != typeFilter) ||
                (readyOnly && zone.LastStart && (zone.LastStart + zone.CooldownSeconds > now)))
                continue;
            zones.push_back(zone);
        }
        std::sort(zones.begin(), zones.end(), [](Zone const& a, Zone const& b)
        {
            return a.Weight != b.Weight ? a.Weight > b.Weight : a.Id < b.Id;
        });
        return zones;
    }

    bool Manager::LoadZoneByName(std::string name, Zone& out)
    {
        auto zone = std::find_if(_zoneCache.begin(), _zoneCache.end(),
            [&](Zone const& current) { return Lower(current.Name) == Lower(name); });
        if (zone == _zoneCache.end())
            return false;
        out = *zone;
        ApplyZoneConfig(out);
        return true;
    }

    TeamSide Manager::TeamForRace(uint8 race) const
    {
        switch (race)
        {
            case RACE_HUMAN:
            case RACE_DWARF:
            case RACE_NIGHTELF:
            case RACE_GNOME:
            case RACE_DRAENEI:
                return TeamSide::Alliance;
            case RACE_ORC:
            case RACE_UNDEAD_PLAYER:
            case RACE_TAUREN:
            case RACE_TROLL:
            case RACE_BLOODELF:
                return TeamSide::Horde;
            default:
                return TeamSide::Any;
        }
    }

    Player* Manager::FindPlayer(uint32 guidLow) const
    {
        ObjectGuid guid = ObjectGuid::Create<HighGuid::Player>(guidLow);
        if (Player* p = ObjectAccessor::FindConnectedPlayer(guid))
            return p;
        return ObjectAccessor::FindPlayer(guid);
    }

    void Manager::RefreshAccountCache()
    {
        std::string prefix = Lower(_botAccountPrefix);
        LoginDatabase.EscapeString(prefix);
        std::string sql = Acore::StringFormat(
            "SELECT id,username FROM account WHERE ({} > 0 AND id BETWEEN {} AND {}) OR "
            "({} > 0 AND LEFT(LOWER(username),{})='{}')",
            _botAccountMax, _botAccountMin, _botAccountMax, _botAccountPrefix.size(), _botAccountPrefix.size(), prefix);
        uint64 generation = _dataGeneration;
        _queryProcessor.AddCallback(LoginDatabase.AsyncQuery(sql).WithCallback([this, generation](QueryResult result)
        {
            if (generation != _dataGeneration || !result)
                return;
            do
            {
                uint32 id = result->Fetch()[0].Get<uint32>();
                bool range = _botAccountMax > 0 && id >= _botAccountMin && id <= _botAccountMax;
                bool prefixMatch = !_botAccountPrefix.empty() &&
                    Lower(result->Fetch()[1].Get<std::string>()).rfind(Lower(_botAccountPrefix), 0) == 0;
                bool all = _accountFilterMode == AccountFilterMode::All &&
                    _botAccountMax > 0 && !_botAccountPrefix.empty();
                _botAccountCache[id] = all ? range && prefixMatch : range || prefixMatch;
            } while (result->NextRow());
        }));
    }

    bool Manager::IsConfiguredBotAccount(uint32 accountId)
    {
        auto cached = _botAccountCache.find(accountId);
        if (cached != _botAccountCache.end())
            return cached->second;
        bool range = accountId && _botAccountMax > 0 && _botAccountMax >= _botAccountMin &&
            accountId >= _botAccountMin && accountId <= _botAccountMax;
        return range && !(_accountFilterMode == AccountFilterMode::All && !_botAccountPrefix.empty());
    }

    bool Manager::IsRealPlayer(Player const* player) const
    {
        if (!player || !player->GetSession())
            return false;
        return ::IsRealPlayer(const_cast<Player*>(player));
    }

    bool Manager::IsSafeBot(Player* player, bool allowPvPLifeReservation) const
    {
        if (!player || !player->GetSession() || !player->IsInWorld() || player->IsBeingTeleported())
            return false;
        if (!sRandomPlayerbotMgr.IsRandomBot(player) &&
            !const_cast<Manager*>(this)->IsConfiguredBotAccount(player->GetSession()->GetAccountId()))
            return false;

        uint32 guid = player->GetGUID().GetCounter();
        if (!allowPvPLifeReservation)
        {
            if (IsLifeBotReserved(guid))
                return false;
        }
        else
        {
            if (PlayerbotsLife::IsReservedBy(guid, PlayerbotsLife::ReservationOwner::CityLife))
                return false;
            if (PlayerbotsLife::IsReservedBy(guid, PlayerbotsLife::ReservationOwner::Artisans))
                return false;
        }

        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai || ::IsRealPlayer(player) || ai->HasGameClientMaster())
            return false;
        if (_respectPlayerbotActivity && !ai->AllowActivity(ALL_ACTIVITY))
            return false;
        if (!player->IsAlive() || player->IsInCombat() || player->IsInFlight() || player->duel)
            return false;
        if (player->InBattleground() || player->InBattlegroundQueue())
            return false;
        if (player->GetMap() && player->GetMap()->Instanceable())
            return false;
        if (_skipGroupedBots && player->GetGroup())
            return false;
        return true;
    }

    bool Manager::IsParticipant(uint32 guidLow) const
    {
        for (ActiveEvent const& e : _activeEvents)
            for (Participant const& p : e.Members)
                if (p.Bot.GuidLow == guidLow)
                {
                    if (!PlayerbotsLife::ValidateLease(p.Token))
                        return false;
                    return true;
                }

        for (PendingRaidResponse const& r : _pendingResponses)
            for (BotCandidate const& b : r.Bots)
                if (b.GuidLow == guidLow)
                {
                    if (!PlayerbotsLife::ValidateLease(b.Token))
                        return false;
                    return true;
                }

        for (ReleasingParticipant const& rp : _releasingParticipants)
            if (rp.Part.Bot.GuidLow == guidLow && PlayerbotsLife::ValidateLeaseState(rp.Part.Token, PlayerbotsLife::LeaseState::Releasing))
                return true;

        return false;
    }

    void Manager::OnPlayerLogout(uint32 guidLow)
    {
        if (IsParticipant(guidLow))
            DisengageParticipant(guidLow);
    }

    void Manager::OnAddGroupMember(uint32 guidLow)
    {
        if (IsParticipant(guidLow))
            DisengageParticipant(guidLow);
    }

    void Manager::CaptureAIState(Player* player, AIStateJournal& journal) const
    {
        if (!player || journal.Captured)
            return;

        journal.OriginalPvPFlag = player->IsPvP();
        if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
        {
            journal.CombatStrategies = ai->GetStrategies(BOT_STATE_COMBAT);
            journal.NonCombatStrategies = ai->GetStrategies(BOT_STATE_NON_COMBAT);
            PositionMap& positions = ai->GetAiObjectContext()->GetValue<PositionMap&>("position")->Get();
            PositionInfo stay = positions["stay"];
            journal.HadStayPosition = stay.isSet();
            if (stay.isSet())
            {
                journal.StayX = stay.x;
                journal.StayY = stay.y;
                journal.StayZ = stay.z;
                journal.StayMapId = stay.mapId;
            }
        }
        journal.Captured = true;
    }

    void Manager::RestoreAIState(Player* player, AIStateJournal const& journal) const
    {
        if (!player || !journal.Captured || IsHumanControlled(player))
            return;

        if (player->GetGroup())
        {
            for (GroupReference const* ref = player->GetGroup()->GetFirstMember(); ref != nullptr; ref = ref->next())
            {
                Player* member = ref->GetSource();
                if (member && member->GetSession() && !GET_PLAYERBOT_AI(member))
                    return; // Yield completely to human party leader
            }
        }

        if (player->IsPvP() == journal.AppliedPvPFlag && player->IsPvP() != journal.OriginalPvPFlag)
            player->SetPvP(journal.OriginalPvPFlag);

        if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
        {
            if (ai->GetStrategies(BOT_STATE_COMBAT) == journal.AppliedCombatStrategies)
            {
                ai->ClearStrategies(BOT_STATE_COMBAT);
                for (std::string const& s : journal.CombatStrategies)
                    ai->ChangeStrategy("+" + s, BOT_STATE_COMBAT);
            }
            if (ai->GetStrategies(BOT_STATE_NON_COMBAT) == journal.AppliedNonCombatStrategies)
            {
                ai->ClearStrategies(BOT_STATE_NON_COMBAT);
                for (std::string const& s : journal.NonCombatStrategies)
                    ai->ChangeStrategy("+" + s, BOT_STATE_NON_COMBAT);
            }

            PositionMap& positions = ai->GetAiObjectContext()->GetValue<PositionMap&>("position")->Get();
            PositionInfo stay = positions["stay"];
            if (journal.HadStayPosition)
                stay.Set(journal.StayX, journal.StayY, journal.StayZ, journal.StayMapId);
            else
                stay.Reset();
            positions["stay"] = stay;
        }
    }

    void Manager::CloseNativeDuel(Player* player, Participant const& part) const
    {
        if (!player || !player->duel || !part.DuelArbiter || !player->duel->Opponent ||
            player->GetGuidValue(PLAYER_DUEL_ARBITER).GetRawValue() != part.DuelArbiter ||
            player->duel->Opponent->GetGUID().GetCounter() != part.DuelOpponentGuid)
            return;
        WorldPacket packet(CMSG_DUEL_CANCELLED, 8);
        packet << player->GetGuidValue(PLAYER_DUEL_ARBITER);
        if (player->GetSession())
            player->GetSession()->HandleDuelCancelledOpcode(packet);
    }

    void Manager::RememberDuelIdentity(uint64 eventId, Player* challenger, Player* target)
    {
        if (!challenger || !target || !challenger->duel || !target->duel ||
            challenger->duel->Opponent != target || target->duel->Opponent != challenger ||
            challenger->GetGuidValue(PLAYER_DUEL_ARBITER) != target->GetGuidValue(PLAYER_DUEL_ARBITER))
            return;
        for (ActiveEvent& event : _activeEvents)
            if (event.EventId == eventId && !event.Closing)
                for (Participant& part : event.Members)
                {
                    Player* player = part.Bot.GuidLow == challenger->GetGUID().GetCounter() ? challenger :
                        (part.Bot.GuidLow == target->GetGUID().GetCounter() ? target : nullptr);
                    if (player && PlayerbotsLife::ValidateActiveLease(part.Token))
                    {
                        part.DuelArbiter = player->GetGuidValue(PLAYER_DUEL_ARBITER).GetRawValue();
                        part.DuelOpponentGuid = player->duel->Opponent->GetGUID().GetCounter();
                    }
                }
    }

    bool Manager::IsHumanControlled(Player* player) const
    {
        if (!player || !player->GetSession())
            return true;
        PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
        if (!ai || ::IsRealPlayer(player) || ::IsSelfBot(player) || ai->HasGameClientMaster())
            return true;
        if (Group* group = player->GetGroup())
            for (GroupReference const* ref = group->GetFirstMember(); ref; ref = ref->next())
                if (Player* member = ref->GetSource(); member && (::IsRealPlayer(member) || ::IsSelfBot(member)))
                    return true;
        return false;
    }

    bool Manager::IsOwnedActor(Player* player, Participant const& part, uint64 eventId) const
    {
        if (!player || !player->IsInWorld() || player->IsBeingTeleported())
            return false;
        if (part.Token.GuidLow != part.Bot.GuidLow || part.Token.ActivityId != eventId ||
            part.Token.Owner != PlayerbotsLife::ReservationOwner::PvPLife ||
            !PlayerbotsLife::ValidateActiveLease(part.Token))
            return false;
        if (IsHumanControlled(player) || !player->IsAlive() || player->IsInFlight())
            return false;
        if (player->InBattleground() || player->InBattlegroundQueue())
            return false;
        if (player->GetMap() && player->GetMap()->Instanceable())
            return false;
        return true;
    }

    bool Manager::CanExecuteStep(uint64 eventId, uint64 generation, uint32 guidLow, bool allowPreparing) const
    {
        auto event = std::find_if(_activeEvents.begin(), _activeEvents.end(),
            [eventId](ActiveEvent const& current) { return current.EventId == eventId; });
        uint32 now = GameTimeSeconds();
        if (event == _activeEvents.end() || event->Closing || event->EndsAt <= now ||
            (!allowPreparing && !event->FullyPrepared) || event->AdmissionRequestId != 0)
            return false;
        auto part = std::find_if(event->Members.begin(), event->Members.end(),
            [guidLow](Participant const& current) { return current.Bot.GuidLow == guidLow; });
        if (part == event->Members.end() || !part->Deployed || part->Token.Generation != generation ||
            part->Token.GuidLow != guidLow || part->Token.ActivityId != eventId ||
            part->Token.Owner != PlayerbotsLife::ReservationOwner::PvPLife ||
            !PlayerbotsLife::ValidateActiveLease(part->Token))
            return false;
        Player* player = FindPlayer(guidLow);
        return player && player->IsInWorld() && player->IsAlive() && !IsHumanControlled(player) &&
            !player->IsInFlight() && !player->InBattleground() && !player->InBattlegroundQueue() &&
            player->GetMap() && !player->GetMap()->Instanceable();
    }

    bool Manager::IsDuelSlotInUse(uint32 slotId) const
    {
        if (slotId == 0)
            return false;
        for (ActiveEvent const& event : _activeEvents)
        {
            for (Participant const& part : event.Members)
                if (part.DuelStagingSlotId == slotId)
                    return true;
            for (DuelPair const& pair : event.DuelPairs)
                if (pair.StagingSlotId == slotId)
                    return true;
        }
        for (ReleasingParticipant const& releasing : _releasingParticipants)
        {
            if (releasing.Part.DuelStagingSlotId == slotId)
                return true;
        }
        return false;
    }

    void Manager::DisengageParticipant(uint32 guidLow)
    {
        for (ActiveEvent& event : _activeEvents)
        {
            auto it = std::find_if(event.Members.begin(), event.Members.end(),
                [guidLow](Participant const& part) { return part.Bot.GuidLow == guidLow; });
            if (it == event.Members.end() || !PlayerbotsLife::ValidateLease(it->Token))
                continue;
            Participant departing = *it;
            uint32 slotId = departing.DuelStagingSlotId;
            event.Members.erase(it);
            QueueParticipantRelease(departing, false);
            event.DuelPairs.erase(std::remove_if(event.DuelPairs.begin(), event.DuelPairs.end(),
                [guidLow](DuelPair const& pair) { return pair.ChallengerGuidLow == guidLow || pair.TargetGuidLow == guidLow; }),
                event.DuelPairs.end());
            if (slotId && !IsDuelSlotInUse(slotId))
                PlayerbotsLife::ReleaseDuelStagingSlot(slotId, PlayerbotsLife::ReservationOwner::PvPLife);
            _botLastRelocateTime.erase(guidLow);
            break;
        }
        for (PendingRaidResponse& pending : _pendingResponses)
        {
            auto it = std::find_if(pending.Bots.begin(), pending.Bots.end(),
                [guidLow](BotCandidate const& bot) { return bot.GuidLow == guidLow; });
            if (it != pending.Bots.end() && PlayerbotsLife::ValidateLease(it->Token))
            {
                PlayerbotsLife::ReleaseLeaseExact(it->Token);
                pending.Bots.erase(it);
            }
        }
        _moveQueue.erase(std::remove_if(_moveQueue.begin(), _moveQueue.end(),
            [guidLow](MoveStep const& step) { return step.GuidLow == guidLow; }), _moveQueue.end());
        _duelQueue.erase(std::remove_if(_duelQueue.begin(), _duelQueue.end(),
            [guidLow](DuelStep const& step) { return step.ChallengerGuidLow == guidLow || step.TargetGuidLow == guidLow; }), _duelQueue.end());
        _engagementQueue.erase(std::remove_if(_engagementQueue.begin(), _engagementQueue.end(),
            [guidLow](EngagementStep const& step) { return step.BotGuidLow == guidLow || step.TargetGuidLow == guidLow; }), _engagementQueue.end());
        _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
            [guidLow](ChatStep const& step) { return step.SpeakerGuidLow == guidLow; }), _chatQueue.end());
    }

    uint8 Manager::EffectiveMinLevel(uint8 minLevel, ActivityType type) const
    {
        if (type == ActivityType::Duel)
            return static_cast<uint8>(std::clamp<uint32>(minLevel, 1, 80));
        uint32 effective = std::max<uint32>(minLevel, _globalMinLevel);
        return static_cast<uint8>(std::min<uint32>(effective, 80));
    }

    std::vector<BotCandidate> Manager::LoadCandidates(TeamSide team, uint8 minLevel, uint8 maxLevel,
        std::unordered_set<uint32> const& excluded, uint32 deficit)
    {
        std::vector<BotCandidate> candidates;
        uint8 effectiveMin = minLevel;
        if (maxLevel < effectiveMin)
            return candidates;

        std::vector<uint32> onlineGuids;
        {
            std::shared_lock<std::shared_mutex> playerLock(*HashMapHolder<Player>::GetLock());
            HashMapHolder<Player>::MapType const& players = ObjectAccessor::GetPlayers();
            onlineGuids.reserve(players.size());
            for (auto const& pair : players)
                if (pair.second)
                    onlineGuids.push_back(pair.second->GetGUID().GetCounter());
        }

        if (onlineGuids.empty())
            return candidates;

        // Smart Hybrid Dynamic QueryLimit:
        // 1. Calculate dynamic census ceiling
        uint32 dynamicCeiling = _botQueryLimit;
        if (dynamicCeiling == 0)
        {
            uint32 liveBots = static_cast<uint32>(onlineGuids.size());
            dynamicCeiling = std::clamp<uint32>(liveBots / 2, 100, 1500);
        }

        // 2. Demand-driven early exit target
        uint32 reqDeficit = (deficit > 0) ? deficit : 10;
        uint32 candidateTarget = std::min<uint32>(dynamicCeiling, std::max<uint32>(20, reqDeficit * 5));

        // 3. Rotational sampling across online bots
        size_t n = onlineGuids.size();
        size_t offset = urand(0, static_cast<uint32>(n - 1));

        for (size_t i = 0; i < n; ++i)
        {
            uint32 guidLow = onlineGuids[(offset + i) % n];
            Player* player = FindPlayer(guidLow);
            if (!player || !player->GetSession() || player->GetLevel() < effectiveMin || player->GetLevel() > maxLevel)
                continue;

            BotCandidate b;
            b.GuidLow = guidLow;
            b.AccountId = player->GetSession()->GetAccountId();
            b.Name = player->GetName();
            b.Level = player->GetLevel();
            b.Race = player->getRace();
            b.Class = player->getClass();
            b.Team = TeamForRace(b.Race);
            b.Online = true;

            if (excluded.find(b.GuidLow) != excluded.end() || IsParticipant(b.GuidLow))
                continue;
            if (PlayerbotsLife::IsReserved(b.GuidLow))
                continue;
            if (team != TeamSide::Any && b.Team != team)
                continue;
            if (!IsSafeBot(player))
                continue;
            candidates.push_back(b);

            if (candidates.size() >= candidateTarget)
                break;
        }

        for (size_t i = candidates.size(); i > 1; --i)
            std::swap(candidates[i - 1], candidates[urand(0, static_cast<uint32>(i - 1))]);

        return candidates;
    }

    std::vector<BotCandidate> Manager::LoadOfflineCandidates(TeamSide team, uint8 level,
        std::unordered_set<uint32> const& excluded)
    {
        uint32 now = GameTimeSeconds();
        auto refreshed = _offlineCandidateRefresh.find(level);
        if (!_offlineCandidateQueries.count(level) &&
            (refreshed == _offlineCandidateRefresh.end() || now - refreshed->second >= 30))
        {
            _offlineCandidateQueries.insert(level);
            uint64 generation = _dataGeneration;
            uint32 ceiling = _botQueryLimit ? _botQueryLimit : 100;
            std::string sql = Acore::StringFormat(
                "SELECT guid,account,name,level,race,class FROM characters "
                "WHERE online=0 AND level={} ORDER BY RAND() LIMIT {}", level, ceiling);
            _queryProcessor.AddCallback(CharacterDatabase.AsyncQuery(sql).WithCallback(
                [this, generation, level](QueryResult result)
                {
                    if (generation != _dataGeneration)
                        return;
                    _offlineCandidateQueries.erase(level);
                    std::vector<BotCandidate> candidates;
                    if (result)
                        do
                        {
                            Field* fields = result->Fetch();
                            BotCandidate bot;
                            bot.GuidLow = fields[0].Get<uint32>();
                            bot.AccountId = fields[1].Get<uint32>();
                            bot.Name = fields[2].Get<std::string>();
                            bot.Level = fields[3].Get<uint8>();
                            bot.Race = fields[4].Get<uint8>();
                            bot.Class = fields[5].Get<uint8>();
                            bot.Team = TeamForRace(bot.Race);
                            bot.Online = false;
                            candidates.push_back(std::move(bot));
                        } while (result->NextRow());
                    _offlineCandidateCache[level] = std::move(candidates);
                    _offlineCandidateRefresh[level] = GameTimeSeconds();
                }));
        }
        std::vector<BotCandidate> candidates;
        auto cached = _offlineCandidateCache.find(level);
        if (cached == _offlineCandidateCache.end())
            return candidates;
        for (BotCandidate const& bot : cached->second)
            if (!FindPlayer(bot.GuidLow) && !excluded.count(bot.GuidLow) && !IsParticipant(bot.GuidLow) &&
                !PlayerbotsLife::IsReserved(bot.GuidLow) && (team == TeamSide::Any || bot.Team == team) &&
                IsConfiguredBotAccount(bot.AccountId))
                candidates.push_back(bot);
        return candidates;
    }

    float Manager::Jitter() const
    {
        if (!_positionJitter)
            return 0.0f;
        return static_cast<float>(irand(-static_cast<int32>(_positionJitter), static_cast<int32>(_positionJitter)));
    }

    uint32 Manager::GetLiveWorldBotCount() const
    {
        uint32 now = GameTimeMS();
        if (_lastCensusTimeMs && now - _lastCensusTimeMs < 5000)
            return _cachedLiveBotCount;
        uint32 count = 0;
        std::shared_lock<std::shared_mutex> playerLock(*HashMapHolder<Player>::GetLock());
        for (auto const& entry : ObjectAccessor::GetPlayers())
        {
            Player* player = entry.second;
            if (!player || !player->GetSession() || !player->IsInWorld())
                continue;
            if (::IsRealPlayer(player))
            {
                _zoneLastRealPlayerTime[player->GetZoneId()] = GameTimeSeconds();
                continue;
            }
            if (IsHumanControlled(player) || !player->IsAlive() || player->InBattleground() ||
                player->InBattlegroundQueue() || !player->GetMap() || player->GetMap()->Instanceable())
                continue;
            if (sRandomPlayerbotMgr.IsRandomBot(player) ||
                const_cast<Manager*>(this)->IsConfiguredBotAccount(player->GetSession()->GetAccountId()))
                ++count;
        }
        _lastCensusTimeMs = now;
        _cachedLiveBotCount = count;
        return count;
    }

    void Manager::UpdateRealPlayersSnapshot() const
    {
        uint32 now = GameTimeMS();
        if (_lastRealPlayerCensusTimeMs && now - _lastRealPlayerCensusTimeMs < 3000)
            return;

        std::vector<RealPlayerSnapshotEntry> snapshot;
        {
            std::shared_lock<std::shared_mutex> playerLock(*HashMapHolder<Player>::GetLock());
            for (auto const& entry : ObjectAccessor::GetPlayers())
            {
                Player* player = entry.second;
                if (!player || !player->GetSession() || !player->IsInWorld() || !::IsRealPlayer(player))
                    continue;

                RealPlayerSnapshotEntry rpe;
                rpe.GuidLow = player->GetGUID().GetCounter();
                rpe.MapId = player->GetMapId();
                rpe.ZoneId = player->GetZoneId();
                rpe.AreaId = player->GetAreaId();
                rpe.Team = player->GetTeamId() == TEAM_ALLIANCE ? TeamSide::Alliance : TeamSide::Horde;
                rpe.Level = player->GetLevel();
                rpe.X = player->GetPositionX();
                rpe.Y = player->GetPositionY();
                rpe.Z = player->GetPositionZ();
                rpe.O = player->GetOrientation();
                rpe.IsAlive = player->IsAlive();
                rpe.IsPvP = player->IsPvP();
                rpe.InCombat = player->IsInCombat();
                rpe.HasDuel = (player->duel != nullptr);
                rpe.IsGameMaster = player->IsGameMaster();
                rpe.Security = player->GetSession()->GetSecurity();

                Group* group = player->GetGroup();
                rpe.IsGroupLeader = (group && group->IsLeader(player->GetGUID()));
                rpe.GroupMembersCount = group ? group->GetMembersCount() : 0;

                snapshot.push_back(std::move(rpe));
            }
        }
        _lastRealPlayerCensusTimeMs = now;
        _cachedRealPlayers = std::move(snapshot);
    }

    void Manager::PruneExpiredCooldowns()
    {
        uint32 now = GameTimeSeconds();
        auto pruneMap = [now](std::unordered_map<uint32, uint32>& map, size_t maxCap)
        {
            for (auto it = map.begin(); it != map.end();)
            {
                if (now >= it->second)
                    it = map.erase(it);
                else
                    ++it;
            }
            if (map.size() > maxCap)
            {
                std::vector<std::pair<uint32, uint32>> entries(map.begin(), map.end());
                std::sort(entries.begin(), entries.end(), [](auto const& a, auto const& b) { return a.second < b.second; });
                size_t toRemove = map.size() - maxCap;
                for (size_t i = 0; i < toRemove; ++i)
                    map.erase(entries[i].first);
            }
        };

        pruneMap(_playerChallengeCooldown, 512);
        pruneMap(_botChallengeCooldown, 512);
        pruneMap(_botDuelCooldown, 512);

        for (auto it = _botLastRelocateTime.begin(); it != _botLastRelocateTime.end(); )
        {
            if (!IsParticipant(it->first))
                it = _botLastRelocateTime.erase(it);
            else
                ++it;
        }
    }

    uint32 Manager::CalculatePopulationBudget() const
    {
        if (!_populationBudgetEnable)
            return _maxTotal > 0 ? _maxTotal : 500;

        uint32 eligiblePool = GetLiveWorldBotCount();
        if (eligiblePool == 0)
            return 0;

        uint32 budget = _fixedCount;
        if (_budgetMode == BudgetMode::Percentage)
            budget = (eligiblePool * _borrowPercent) / 100;

        uint32 ceiling = (_maxTotal > 0) ? _maxTotal : eligiblePool;
        uint32 upper = std::min<uint32>(ceiling, eligiblePool);
        if (upper == 0)
            return 0;

        return std::clamp<uint32>(budget, 1, upper);
    }

    uint32 Manager::RandomCount(uint32 minCount, uint32 maxCount) const
    {
        minCount = std::min(minCount, _maxBotsPerSide);
        maxCount = std::min(maxCount, _maxBotsPerSide);
        if (maxCount < minCount)
            maxCount = minCount;
        return urand(minCount, maxCount);
    }

    void Manager::CalculatePopulation(Zone const& zone, uint32& attackerCount, uint32& defenderCount) const
    {
        if (_draining)
        {
            attackerCount = 0;
            defenderCount = 0;
            return;
        }

        uint32 minimumPopulation = std::clamp<uint32>(zone.PopulationMin, 1, _maxBotsPerSide * 2);
        uint32 maximumPopulation = std::clamp(zone.PopulationMax, minimumPopulation, _maxBotsPerSide * 2);

        if (_proportionalZoneScaling)
        {
            uint32 liveBots = GetLiveWorldBotCount();
            float scale = (liveBots > 0) ? (static_cast<float>(liveBots) / 1000.0f) : 1.0f;
            scale = std::clamp(scale, 0.5f, 2.5f);
            minimumPopulation = std::max<uint32>(2, static_cast<uint32>(std::lround(minimumPopulation * scale)));
            maximumPopulation = std::max<uint32>(minimumPopulation, static_cast<uint32>(std::lround(maximumPopulation * scale)));
        }

        minimumPopulation = std::min(minimumPopulation, _maxBotsPerSide * 2);
        maximumPopulation = std::clamp(maximumPopulation, minimumPopulation, _maxBotsPerSide * 2);
        uint32 totalPopulation = urand(minimumPopulation, maximumPopulation);

        // DemandMode execution: Fixed, Dynamic, Hybrid
        uint32 zoneId = zone.ZoneId ? zone.ZoneId : sMapMgr->GetZoneId(PHASEMASK_NORMAL, zone.MapId, zone.RallyX, zone.RallyY, zone.RallyZ);
        if (_demandMode != DemandMode::Fixed && zoneId != 0)
        {
            uint32 nowSec = GameTimeSeconds();
            bool hasRealPlayerPresence = false;
            auto it = _zoneLastRealPlayerTime.find(zoneId);
            if (it != _zoneLastRealPlayerTime.end() && (nowSec - it->second <= _burstGraceSeconds))
                hasRealPlayerPresence = true;

            if (_demandMode == DemandMode::Dynamic && !hasRealPlayerPresence)
            {
                attackerCount = 0;
                defenderCount = 0;
                return;
            }
            else if (_demandMode == DemandMode::Hybrid && !hasRealPlayerPresence)
            {
                float baselineFactor = static_cast<float>(_baselinePercent) / 100.0f;
                totalPopulation = std::max<uint32>(2, static_cast<uint32>(std::lround(totalPopulation * baselineFactor)));
            }
        }

        uint32 budget = CalculatePopulationBudget();
        uint32 currentActive = PlayerbotsLife::GetCooperationSnapshot().PvPLifeCount;

        uint32 availableBudget = (budget > currentActive) ? (budget - currentActive) : 0;
        if (availableBudget < 2)
        {
            attackerCount = 0;
            defenderCount = 0;
            return;
        }

        if (totalPopulation > availableBudget)
            totalPopulation = availableBudget;

        if (zone.Type == ActivityType::Duel)
        {
            if (totalPopulation % 2 != 0)
                totalPopulation = (totalPopulation > 2) ? totalPopulation - 1 : 2;
            attackerCount = std::min(totalPopulation / 2, _maxBotsPerSide);
            defenderCount = attackerCount;
        }
        else
        {
            uint64 attackerWeight = static_cast<uint64>(zone.AttackersMin) + zone.AttackersMax;
            uint64 defenderWeight = static_cast<uint64>(zone.DefendersMin) + zone.DefendersMax;
            uint64 totalWeight = attackerWeight + defenderWeight;
            if (!totalWeight)
            {
                attackerWeight = 1;
                totalWeight = 2;
            }

            attackerCount = static_cast<uint32>(
                (static_cast<uint64>(totalPopulation) * attackerWeight + totalWeight / 2) / totalWeight);
            attackerCount = std::clamp<uint32>(attackerCount, 1, totalPopulation - 1);
            defenderCount = totalPopulation - attackerCount;

            if (attackerCount > _maxBotsPerSide)
            {
                attackerCount = _maxBotsPerSide;
                defenderCount = totalPopulation - attackerCount;
            }
            if (defenderCount > _maxBotsPerSide)
            {
                defenderCount = _maxBotsPerSide;
                attackerCount = totalPopulation - defenderCount;
            }
        }
    }

    void Manager::ApplyPvpStrategies(Player* player, bool duelMode) const
    {
        if (!player)
            return;
        if (_forcePvpFlag)
            player->SetPvP(true);
        if (_strategiesEnable)
        {
            if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
            {
                std::string combatStrats = _pvpCombatStrategies;
                std::string nonCombatStrats = duelMode ? _duelNonCombatStrategies : _pvpNonCombatStrategies;
                combatStrats += ",-rpg,-travel";
                nonCombatStrats += ",-rpg,-travel";
                if (!_botChatEnable || (_botChatYellChance == 0 && _botChatWorldChance == 0))
                {
                    combatStrats += ",-chat,-emote";
                    nonCombatStrats += ",-chat,-emote";
                }
                ai->ChangeStrategy(combatStrats, BOT_STATE_COMBAT);
                ai->ChangeStrategy(nonCombatStrats, BOT_STATE_NON_COMBAT);
                if (duelMode)
                    ai->ChangeStrategy("+stay,-follow,-passive,-grind,-rpg,-travel", BOT_STATE_NON_COMBAT);
            }
        }
    }

    void Manager::ScheduleMove(uint64 eventId, PlayerbotsLife::LeaseToken const& token, uint32 guidLow,
        std::string const& name, uint32 mapId, float x, float y, float z, float o, uint32 delaySeconds, bool teleport)
    {
        MoveStep step;
        step.EventId = eventId;
        step.Generation = token.Generation;
        step.Token = token;
        step.GuidLow = guidLow;
        step.Name = name;
        step.ExecuteAt = GameTimeSeconds() + delaySeconds;
        step.MapId = mapId;
        step.X = x; step.Y = y; step.Z = z; step.O = o;
        step.Teleport = teleport;
        _moveQueue.push_back(step);
    }

    void Manager::ScheduleDuel(uint64 eventId, uint64 pairId, PlayerbotsLife::LeaseToken const& challengerToken,
        PlayerbotsLife::LeaseToken const& targetToken, uint32 challengerGuid, uint32 targetGuid,
        std::string const& challengerName, std::string const& targetName, uint32 delaySeconds,
        bool realPlayerTarget)
    {
        if (!challengerGuid || !targetGuid || challengerGuid == targetGuid)
            return;
        std::set<std::pair<uint32, uint32>> busyPairs;
        for (DuelStep const& queued : _duelQueue)
        {
            if (queued.ChallengerGuidLow == challengerGuid || queued.TargetGuidLow == challengerGuid ||
                queued.ChallengerGuidLow == targetGuid || queued.TargetGuidLow == targetGuid)
                return;
            if (queued.EventId == eventId)
                busyPairs.emplace(std::min(queued.ChallengerGuidLow, queued.TargetGuidLow),
                    std::max(queued.ChallengerGuidLow, queued.TargetGuidLow));
        }
        for (ActiveEvent const& event : _activeEvents)
            if (event.EventId == eventId)
                for (Participant const& participant : event.Members)
                    if (Player* player = FindPlayer(participant.Bot.GuidLow); player && player->duel && player->duel->Opponent)
                    {
                        uint32 a = player->GetGUID().GetCounter();
                        uint32 b = player->duel->Opponent->GetGUID().GetCounter();
                        busyPairs.emplace(std::min(a, b), std::max(a, b));
                    }
        if (busyPairs.size() >= _duelPairLimit)
            return;

        DuelStep step;
        step.EventId = eventId;
        step.Generation = challengerToken.Generation;
        step.PairId = pairId;
        step.ChallengerToken = challengerToken;
        step.TargetToken = targetToken;
        step.ChallengerGuidLow = challengerGuid;
        step.TargetGuidLow = targetGuid;
        step.ChallengerName = challengerName;
        step.TargetName = targetName;
        step.ExecuteAt = GameTimeSeconds() + delaySeconds;
        step.TargetIsRealPlayer = realPlayerTarget;
        _duelQueue.push_back(step);
    }

    void Manager::ScheduleEngagement(uint64 eventId, PlayerbotsLife::LeaseToken const& botToken,
        uint32 botGuid, uint32 targetGuid, uint32 delaySeconds)
    {
        EngagementStep step;
        step.EventId = eventId;
        step.Generation = botToken.Generation;
        step.BotToken = botToken;
        step.BotGuidLow = botGuid;
        step.TargetGuidLow = targetGuid;
        step.ExecuteAt = GameTimeSeconds() + delaySeconds;
        step.RetryCount = 0;
        step.MaxRetries = static_cast<uint8>(_engageMaxRetries);
        _engagementQueue.push_back(step);
    }

    void Manager::MoveBot(Player* player, uint32 mapId, float x, float y, float z, float o, bool teleport) const
    {
        if (!player || player->IsBeingTeleported())
            return;
        if (!std::isfinite(x) || !std::isfinite(y) || !std::isfinite(z) || !std::isfinite(o) || z <= -1000.0f)
            return;
        if (player->IsInCombat())
            player->CombatStop(true);

        if (teleport || player->GetMapId() != mapId || !_useMovePoint)
        {
            player->TeleportTo(mapId, x, y, z, o);
            if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
                ai->HandleTeleportAck();
        }
        else
        {
            if (player->GetMap() && player->GetMapId() == mapId)
            {
                float probedZ = player->GetMap()->GetHeight(player->GetPhaseMask(), x, y, z);
                if (probedZ > -1000.0f && std::abs(probedZ - z) < 15.0f)
                    z = probedZ;
            }

            if (player->isMoving() && player->GetDistance2d(x, y) <= 2.0f)
                return;

            player->ClearUnitState(UNIT_STATE_CHASE | UNIT_STATE_FOLLOW);
            player->GetMotionMaster()->Clear();
            player->GetMotionMaster()->MovePoint(0, x, y, z);
        }
    }

    void Manager::EngageTarget(Player* bot, Player* target)
    {
        if (!bot || !target || !bot->IsAlive() || !target->IsAlive())
            return;
        if (bot->GetMapId() != target->GetMapId())
            return;

        if (!bot->IsValidAttackTarget(target))
            return;

        AreaTableEntry const* botArea = sAreaTableStore.LookupEntry(bot->GetAreaId());
        AreaTableEntry const* targetArea = sAreaTableStore.LookupEntry(target->GetAreaId());
        if ((botArea && (botArea->flags & AREA_FLAG_SANCTUARY)) || (targetArea && (targetArea->flags & AREA_FLAG_SANCTUARY)))
            return;

        if (_forcePvpFlag && !bot->IsPvP())
            bot->SetPvP(true);

        if (_strategiesEnable)
            ApplyPvpStrategies(bot, false);

        bot->SetSelection(target->GetGUID());
        bot->Attack(target, true);

        if (PlayerbotAI* ai = GET_PLAYERBOT_AI(bot))
        {
            ai->ChangeEngineOnCombat();
        }
    }

    void Manager::DeployEventMembers(ActiveEvent& event, uint32& changesCount, uint32 maxChanges)
    {
        if (event.Closing || event.AdmissionRequestId != 0 || event.FullyPrepared)
            return;
        uint32 now = GameTimeSeconds();
        auto deploy = [&](Participant& part, bool duelMode, uint32 index)
        {
            if (part.Deployed)
                return true;
            if (changesCount >= maxChanges)
                return false;
            Player* player = FindPlayer(part.Bot.GuidLow);
            if (!IsOwnedActor(player, part, event.EventId))
                return false;
            part.OriginalMap = player->GetMapId();
            part.OriginalX = player->GetPositionX();
            part.OriginalY = player->GetPositionY();
            part.OriginalZ = player->GetPositionZ();
            part.OriginalO = player->GetOrientation();
            CaptureAIState(player, part.Journal);
            ApplyPvpStrategies(player, duelMode);
            PlayerbotAI* ai = GET_PLAYERBOT_AI(player);
            part.Journal.AppliedCombatStrategies = ai->GetStrategies(BOT_STATE_COMBAT);
            part.Journal.AppliedNonCombatStrategies = ai->GetStrategies(BOT_STATE_NON_COMBAT);
            part.Journal.AppliedPvPFlag = player->IsPvP();
            if (sRandomPlayerbotMgr.IsRandomBot(player))
                sRandomPlayerbotMgr.ScheduleTeleport(part.Bot.GuidLow, event.EndsAt - now + 60);
            uint32 arrival = urand(_arrivalStaggerMin, _arrivalStaggerMax) + index;
            part.Deployed = true;
            ++changesCount;
            ScheduleMove(event.EventId, part.Token, part.Bot.GuidLow, part.Bot.Name, event.EventZone.MapId,
                part.ActivityX, part.ActivityY, part.ActivityZ, part.ActivityO, arrival, _teleportOnArrival);
            if (!duelMode && part.Attacker)
            {
                uint32 moveDelay = arrival + urand(_moveAfterArrivalMin, _moveAfterArrivalMax);
                ScheduleMove(event.EventId, part.Token, part.Bot.GuidLow, part.Bot.Name, event.EventZone.MapId,
                    event.EventZone.TargetX + Jitter(), event.EventZone.TargetY + Jitter(),
                    event.EventZone.TargetZ, event.EventZone.TargetO, moveDelay, _hardTeleportToTarget);
                uint32 targetGuid = event.TriggerGuidLow;
                if (event.Origin != EventOrigin::ReactiveRaidResponse)
                    for (Participant const& target : event.Members)
                        if (!target.Attacker)
                        {
                            targetGuid = target.Bot.GuidLow;
                            break;
                        }
                if (_forceAttackOnEngage && targetGuid)
                    ScheduleEngagement(event.EventId, part.Token, part.Bot.GuidLow, targetGuid,
                        moveDelay + _engageAfterMoveSeconds);
            }
            return true;
        };
        if (event.EventZone.Type == ActivityType::Duel)
        {
            for (uint32 index = 0; index < event.DuelPairs.size(); ++index)
            {
                DuelPair& pair = event.DuelPairs[index];
                if (pair.Deployed)
                    continue;
                auto a = std::find_if(event.Members.begin(), event.Members.end(),
                    [&](Participant const& part) { return part.Bot.GuidLow == pair.ChallengerGuidLow; });
                auto b = std::find_if(event.Members.begin(), event.Members.end(),
                    [&](Participant const& part) { return part.Bot.GuidLow == pair.TargetGuidLow; });
                if (a == event.Members.end() || b == event.Members.end())
                    continue;
                bool firstReady = deploy(*a, true, index);
                bool secondReady = deploy(*b, true, index);
                if (!firstReady || !secondReady)
                    continue;
                uint32 delay = _arrivalStaggerMax + index + _duelPairDelayMax;
                ScheduleDuel(event.EventId, pair.PairId, a->Token, b->Token,
                    a->Bot.GuidLow, b->Bot.GuidLow, a->Bot.Name, b->Bot.Name, delay);
                pair.Deployed = true;
            }
        }
        else
            for (uint32 index = 0; index < event.Members.size(); ++index)
                deploy(event.Members[index], false, index);
        uint32 attackers = static_cast<uint32>(std::count_if(event.Members.begin(), event.Members.end(),
            [](Participant const& part) { return part.Deployed && part.Attacker; }));
        uint32 defenders = static_cast<uint32>(std::count_if(event.Members.begin(), event.Members.end(),
            [](Participant const& part) { return part.Deployed && !part.Attacker; }));
        if (attackers < event.RequiredAttackers || defenders < event.RequiredDefenders ||
            attackers + defenders < event.MinimumTotal)
            return;
        if (std::all_of(event.Members.begin(), event.Members.end(),
            [](Participant const& part) { return part.Deployed; }))
        {
            event.FullyPrepared = true;
            event.StartedAt = now;
            event.EndsAt = now + event.DurationSeconds;
            if (event.EventZone.BotChat && _botChatEnable)
                ScheduleEventChat(event);
        }
    }

    void Manager::ProcessAdmissionGrants()
    {
        uint32 now = GameTimeSeconds();
        for (ActiveEvent& event : _activeEvents)
        {
            if (!event.AdmissionRequestId || event.Closing)
                continue;
            if (event.PrepareDeadline <= now)
            {
                EndEvent(event, "admission-timeout");
                continue;
            }
            std::vector<PlayerbotsLife::LeaseToken> tokens;
            if (!PlayerbotsLife::TakeAdmissionGrant(event.AdmissionRequestId, PlayerbotsLife::ReservationOwner::PvPLife, tokens))
                continue;
            event.AdmissionRequestId = 0;
            bool viable = tokens.size() == event.Members.size() &&
                PlayerbotsLife::GetCooperationSnapshot().PvPLifeCount <= CalculatePopulationBudget();
            for (Participant& part : event.Members)
            {
                auto token = std::find_if(tokens.begin(), tokens.end(),
                    [&](PlayerbotsLife::LeaseToken const& lease) { return lease.GuidLow == part.Bot.GuidLow; });
                if (token == tokens.end())
                {
                    viable = false;
                    continue;
                }
                part.Token = *token;
                if (!PlayerbotsLife::PromoteLease(part.Token, event.EventId))
                    viable = false;
            }
            if (!viable)
            {
                EndEvent(event, "invalid-admission");
                for (auto const& token : tokens)
                    PlayerbotsLife::ReleaseLeaseExact(token);
            }
        }
        for (PendingRaidResponse& pending : _pendingResponses)
        {
            if (!pending.AdmissionRequestId || pending.Cancelled)
                continue;
            std::vector<PlayerbotsLife::LeaseToken> tokens;
            if (!PlayerbotsLife::TakeAdmissionGrant(pending.AdmissionRequestId, PlayerbotsLife::ReservationOwner::PvPLife, tokens))
                continue;
            pending.AdmissionRequestId = 0;
            pending.LeasesGranted = tokens.size() == pending.Bots.size();
            for (BotCandidate& bot : pending.Bots)
            {
                auto token = std::find_if(tokens.begin(), tokens.end(),
                    [&](PlayerbotsLife::LeaseToken const& lease) { return lease.GuidLow == bot.GuidLow; });
                if (token != tokens.end())
                    bot.Token = *token;
                else
                    pending.LeasesGranted = false;
            }
            if (!pending.LeasesGranted || pending.Deadline <= now)
            {
                pending.Cancelled = true;
                for (auto const& token : tokens)
                    PlayerbotsLife::ReleaseLeaseExact(token);
                continue;
            }
            for (uint32 guid : pending.PendingLoginGuids)
            {
                auto bot = std::find_if(pending.Bots.begin(), pending.Bots.end(),
                    [guid](BotCandidate const& candidate) { return candidate.GuidLow == guid; });
                if (bot != pending.Bots.end() &&
                    PlayerbotsLife::ValidateLeaseState(bot->Token, PlayerbotsLife::LeaseState::Provisional))
                    sRandomPlayerbotMgr.AddPlayerBot(ObjectGuid::Create<HighGuid::Player>(guid), 0);
            }
        }
    }

    void Manager::ProcessPreparingEvents()
    {
        uint32 now = GameTimeSeconds();
        for (ActiveEvent& event : _activeEvents)
        {
            if (event.Closing || event.FullyPrepared || event.AdmissionRequestId != 0)
                continue;
            if (event.PrepareDeadline <= now)
            {
                uint32 attackers = static_cast<uint32>(std::count_if(event.Members.begin(), event.Members.end(),
                    [](Participant const& part) { return part.Deployed && part.Attacker; }));
                uint32 defenders = static_cast<uint32>(std::count_if(event.Members.begin(), event.Members.end(),
                    [](Participant const& part) { return part.Deployed && !part.Attacker; }));
                if (attackers >= event.RequiredAttackers && defenders >= event.RequiredDefenders &&
                    (attackers + defenders) >= event.MinimumTotal)
                {
                    for (auto it = event.Members.begin(); it != event.Members.end(); )
                    {
                        if (!it->Deployed)
                        {
                            if (it->DuelStagingSlotId != 0)
                                PlayerbotsLife::ReleaseDuelStagingSlot(it->DuelStagingSlotId, PlayerbotsLife::ReservationOwner::PvPLife);
                            if (it->Token.GuidLow != 0)
                                PlayerbotsLife::ReleaseLeaseExact(const_cast<PlayerbotsLife::LeaseToken&>(it->Token));
                            it = event.Members.erase(it);
                        }
                        else
                            ++it;
                    }
                    event.FullyPrepared = true;
                    event.StartedAt = now;
                    event.EndsAt = now + event.DurationSeconds;
                    if (event.EventZone.BotChat && _botChatEnable)
                        ScheduleEventChat(event);
                    LOG_INFO("module", "[PvPLife] Event #{} {} started with partial deployment (attackers={}, defenders={})",
                        event.EventId, event.EventZone.Name, attackers, defenders);
                    continue;
                }
                EndEvent(event, "prep-timeout");
                continue;
            }
            if (_changesThisTick < _maxChangesPerTick)
                DeployEventMembers(event, _changesThisTick, _maxChangesPerTick);
        }
        _activeEvents.erase(std::remove_if(_activeEvents.begin(), _activeEvents.end(),
            [](ActiveEvent const& event) { return event.Closing; }), _activeEvents.end());
    }

    bool Manager::StartZone(Zone const& zone, ChatHandler* handler, bool forced)
    {
        if (!zone.Enabled && !forced)
            return false;
        if (zone.Type == ActivityType::Duel && !_duelEnable && !forced)
            return false;
        if (zone.Type == ActivityType::ForTheHorde && !_forTheHordeEnable && !forced)
            return false;
        if (zone.Type == ActivityType::ForTheAlliance && !_forTheAllianceEnable && !forced)
            return false;

        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents && !forced)
            return false;

        if (!forced && _maxChangesPerTick > 0 && _changesThisTick >= _maxChangesPerTick)
            return false;

        for (ActiveEvent const& e : _activeEvents)
            if (e.EventZone.Id == zone.Id)
                return false;

        std::unordered_set<uint32> excluded;
        for (ActiveEvent const& e : _activeEvents)
            for (Participant const& p : e.Members)
                excluded.insert(p.Bot.GuidLow);
        for (PendingRaidResponse const& r : _pendingResponses)
            for (BotCandidate const& b : r.Bots)
                excluded.insert(b.GuidLow);
        for (ReleasingParticipant const& rp : _releasingParticipants)
            excluded.insert(rp.Part.Bot.GuidLow);

        uint32 attackerNeed = 0;
        uint32 defenderNeed = 0;
        CalculatePopulation(zone, attackerNeed, defenderNeed);
        uint8 effMinLevel = EffectiveMinLevel(zone.MinLevel, zone.Type);
        std::vector<BotCandidate> attackerPool =
            LoadCandidates(zone.AttackerTeam, effMinLevel, zone.MaxLevel, excluded, attackerNeed);
        std::vector<BotCandidate> defenderPool =
            LoadCandidates(zone.DefenderTeam, effMinLevel, zone.MaxLevel, excluded, defenderNeed);
        std::unordered_set<uint32> attackerIds;
        std::unordered_set<uint32> defenderIds;
        for (BotCandidate const& bot : attackerPool)
            attackerIds.insert(bot.GuidLow);
        for (BotCandidate const& bot : defenderPool)
            defenderIds.insert(bot.GuidLow);

        std::vector<BotCandidate> attackers;
        std::vector<BotCandidate> defenders;
        std::vector<BotCandidate> shared;
        for (BotCandidate const& bot : attackerPool)
        {
            if (defenderIds.count(bot.GuidLow))
                shared.push_back(bot);
            else if (attackers.size() < attackerNeed)
                attackers.push_back(bot);
        }
        for (BotCandidate const& bot : defenderPool)
            if (!attackerIds.count(bot.GuidLow) && defenders.size() < defenderNeed)
                defenders.push_back(bot);

        for (BotCandidate const& bot : shared)
        {
            bool attackerNeedsBot = attackers.size() < attackerNeed;
            bool defenderNeedsBot = defenders.size() < defenderNeed;
            if (!attackerNeedsBot && !defenderNeedsBot)
                break;

            if (attackerNeedsBot && (!defenderNeedsBot || attackers.size() <= defenders.size()))
                attackers.push_back(bot);
            else
                defenders.push_back(bot);
        }

        if (zone.Type == ActivityType::Duel)
        {
            auto pairs = SelectDiverseDuelPairs(attackerPool, defenderPool,
                std::min(attackerNeed, defenderNeed), _botDuelMaxLevelDifference);
            attackers = std::move(pairs.first);
            defenders = std::move(pairs.second);
        }

        uint32 requiredAttackers = _allowPartialTeams ? _minimumBotsPerSide : attackerNeed;
        uint32 requiredDefenders = _allowPartialTeams ? _minimumBotsPerSide : defenderNeed;
        uint32 requiredTotal = (zone.Type == ActivityType::Duel) ? 2 :
            (_allowPartialTeams ? std::max<uint32>(2, std::min<uint32>(_minOnlineRequired, requiredAttackers + requiredDefenders)) : _minOnlineRequired);
        uint32 now = GameTimeSeconds();

        if (attackers.size() < requiredAttackers || defenders.size() < requiredDefenders ||
            (attackers.size() + defenders.size()) < requiredTotal)
        {
            if (_debug)
                LOG_INFO("module", "[PvPLife] '{}' lacks bots: attackers {}/{} defenders {}/{} total {} (min required {})",
                    zone.Name, attackers.size(), attackerNeed, defenders.size(), defenderNeed,
                    attackers.size() + defenders.size(), requiredTotal);
            if (handler)
                handler->PSendSysMessage("PvP Life: Insufficient eligible bots for {} (attackers {}/{}, defenders {}/{}).",
                    zone.Name, attackers.size(), attackerNeed, defenders.size(), defenderNeed);
            return false;
        }

        ActiveEvent event;
        event.EventId = _nextEventId++;
        event.EventZone = zone;
        event.Origin = EventOrigin::Zone;
        event.StartedAt = now;
        uint32 dmin = std::max<uint32>(1, zone.DurationMin);
        uint32 dmax = std::max(dmin, zone.DurationMax);
        event.DurationSeconds = urand(dmin, dmax) * MINUTE;
        event.RequiredAttackers = requiredAttackers;
        event.RequiredDefenders = requiredDefenders;
        event.MinimumTotal = requiredTotal;
        uint32 plannedMembers = static_cast<uint32>(attackers.size() + defenders.size());
        uint32 queuedWork = plannedMembers + static_cast<uint32>(_releasingParticipants.size());
        for (ActiveEvent const& queued : _activeEvents)
            if (!queued.Closing)
                queuedWork += static_cast<uint32>(std::count_if(queued.Members.begin(), queued.Members.end(),
                    [](Participant const& part) { return !part.Deployed; }));
        uint32 batches = (queuedWork + _maxChangesPerTick - 1) / _maxChangesPerTick;
        event.PrepareDeadline = now + std::max<uint32>(60, 2 * _tickSeconds * batches + _arrivalStaggerMax);
        event.EndsAt = event.PrepareDeadline + event.DurationSeconds;

        // Rollback helper in case atomic batch acquisition does not satisfy minimums
        auto rollback = [&]()
        {
            for (Participant const& part : event.Members)
            {
                if (part.DuelStagingSlotId != 0)
                    PlayerbotsLife::ReleaseDuelStagingSlot(part.DuelStagingSlotId, PlayerbotsLife::ReservationOwner::PvPLife);
                if (Player* p = FindPlayer(part.Bot.GuidLow))
                    RestoreAIState(p, part.Journal);
                if (part.Token.GuidLow != 0)
                    PlayerbotsLife::ReleaseLeaseExact(const_cast<PlayerbotsLife::LeaseToken&>(part.Token));
            }
            uint64 evId = event.EventId;
            _moveQueue.erase(std::remove_if(_moveQueue.begin(), _moveQueue.end(),
                [evId](MoveStep const& s) { return s.EventId == evId; }), _moveQueue.end());
            _duelQueue.erase(std::remove_if(_duelQueue.begin(), _duelQueue.end(),
                [evId](DuelStep const& s) { return s.EventId == evId; }), _duelQueue.end());
            _engagementQueue.erase(std::remove_if(_engagementQueue.begin(), _engagementQueue.end(),
                [evId](EngagementStep const& s) { return s.EventId == evId; }), _engagementQueue.end());
            _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
                [evId](ChatStep const& s) { return s.EventId == evId; }), _chatQueue.end());
            PlayerbotsLife::ReleaseDuelStagingSlotByActivity(evId, PlayerbotsLife::ReservationOwner::PvPLife);
            event.Members.clear();
            event.DuelPairs.clear();
        };

        if (zone.Type == ActivityType::Duel)
        {
            uint32 numPairs = std::min(attackers.size(), defenders.size());
            numPairs = std::min(numPairs, _duelPairLimit);
            uint32 eventDurationMs = (event.EndsAt > now ? (event.EndsAt - now) : 600) * 1000;

            for (uint32 i = 0; i < numPairs; ++i)
            {
                BotCandidate const& candA = attackers[i];
                BotCandidate const& candB = defenders[i];

                Player* playerA = FindPlayer(candA.GuidLow);
                Player* playerB = FindPlayer(candB.GuidLow);
                if (!IsSafeBot(playerA) || !IsSafeBot(playerB))
                    continue;

                Participant partA;
                Participant partB;
                uint64 pairId = _nextPairId++;

                // Duel pair staging: allocate a single DuelStagingSlot per pair (PV-17)
                uint32 duelJitter = std::min<uint32>(_positionJitter, 1);
                float laneOffset = (float(i) - float(numPairs - 1) * 0.5f) * 8.0f;
                float sx = (zone.RallyX + zone.TargetX) * 0.5f +
                    static_cast<float>(irand(-static_cast<int32>(duelJitter), static_cast<int32>(duelJitter)));
                float sy = (zone.RallyY + zone.TargetY) * 0.5f + laneOffset +
                    static_cast<float>(irand(-static_cast<int32>(duelJitter), static_cast<int32>(duelJitter)));
                float sz = (zone.RallyZ + zone.TargetZ) * 0.5f;

                PlayerbotsLife::DuelStagingSlot slot;
                uint32 slotId = 0;
                if (!PlayerbotsLife::ClaimDuelStagingSlot(zone.MapId, sx, sy, sz, 30.0f, event.EventId,
                    PlayerbotsLife::ReservationOwner::PvPLife, GameTimeMS(), eventDurationMs, slot, pairId))
                {
                    // Defer pair if staging slot unclaimable: never deploy at an unreserved fallback center!
                    PlayerbotsLife::ReleaseLeaseExact(partA.Token);
                    PlayerbotsLife::ReleaseLeaseExact(partB.Token);
                    continue;
                }

                slotId = slot.SlotId;
                sx = slot.CenterX;
                sy = slot.CenterY;
                sz = slot.CenterZ;

                Map* zoneMap = sMapMgr->FindBaseMap(zone.MapId);
                if (zoneMap)
                {
                    float probedCenter = zoneMap->GetHeight(sx, sy, sz);
                    if (probedCenter > -1000.0f)
                        sz = probedCenter;
                }

                // Varied pair orientation and distance so bots face each other naturally without identical lines
                float pairAngle = Position::NormalizeOrientation(zone.RallyO + static_cast<float>(i) * 1.047197f + frand(-0.35f, 0.35f));
                float offsetDist = 2.5f + frand(0.0f, 1.2f);

                float ax = sx - std::cos(pairAngle) * offsetDist;
                float ay = sy - std::sin(pairAngle) * offsetDist;
                float az = sz;
                if (zoneMap)
                {
                    float probedZ = zoneMap->GetHeight(ax, ay, sz);
                    if (probedZ > -1000.0f)
                        az = probedZ;
                }
                float ao = pairAngle;

                float bx = sx + std::cos(pairAngle) * offsetDist;
                float by = sy + std::sin(pairAngle) * offsetDist;
                float bz = sz;
                if (zoneMap)
                {
                    float probedZ = zoneMap->GetHeight(bx, by, sz);
                    if (probedZ > -1000.0f)
                        bz = probedZ;
                }
                float bo = Position::NormalizeOrientation(pairAngle + 3.14159265f);

                // Setup Part A
                partA.Bot = candA;
                partA.Attacker = true;
                partA.OriginalMap = playerA->GetMapId();
                partA.OriginalX = playerA->GetPositionX();
                partA.OriginalY = playerA->GetPositionY();
                partA.OriginalZ = playerA->GetPositionZ();
                partA.OriginalO = playerA->GetOrientation();
                partA.ActivityX = ax; partA.ActivityY = ay; partA.ActivityZ = az; partA.ActivityO = ao;
                partA.PairId = pairId;
                partA.DuelStagingSlotId = slotId;
                partA.Deployed = false;

                // Setup Part B
                partB.Bot = candB;
                partB.Attacker = false;
                partB.OriginalMap = playerB->GetMapId();
                partB.OriginalX = playerB->GetPositionX();
                partB.OriginalY = playerB->GetPositionY();
                partB.OriginalZ = playerB->GetPositionZ();
                partB.OriginalO = playerB->GetOrientation();
                partB.ActivityX = bx; partB.ActivityY = by; partB.ActivityZ = bz; partB.ActivityO = bo;
                partB.PairId = pairId;
                partB.DuelStagingSlotId = slotId;
                partB.Deployed = false;

                event.Members.push_back(partA);
                event.Members.push_back(partB);

                DuelPair dp;
                dp.PairId = pairId;
                dp.EventId = event.EventId;
                dp.ChallengerGuidLow = candA.GuidLow;
                dp.TargetGuidLow = candB.GuidLow;
                dp.StagingSlotId = slotId;
                dp.State = DuelPairState::Approaching;
                dp.Deployed = false;
                event.DuelPairs.push_back(dp);
            }
            AuditLog("DUEL_QUEUE", "event=" + std::to_string(event.EventId) + " spot=" + zone.Name + " pairs=" + std::to_string(event.DuelPairs.size()));
        }
        else
        {
            auto add = [&](BotCandidate const& bot, bool attacker, uint32 /*index*/)
            {
                Player* player = FindPlayer(bot.GuidLow);
                if (!IsSafeBot(player))
                    return;

                Participant part;
                part.Bot = bot;
                part.Attacker = attacker;
                part.OriginalMap = player->GetMapId();
                part.OriginalX = player->GetPositionX();
                part.OriginalY = player->GetPositionY();
                part.OriginalZ = player->GetPositionZ();
                part.OriginalO = player->GetOrientation();

                float sx = (attacker ? zone.RallyX : zone.TargetX) + Jitter();
                float sy = (attacker ? zone.RallyY : zone.TargetY) + Jitter();
                float sz = attacker ? zone.RallyZ : zone.TargetZ;
                float so = attacker ? zone.RallyO : zone.TargetO;

                part.ActivityX = sx;
                part.ActivityY = sy;
                part.ActivityZ = sz;
                part.ActivityO = so;
                part.Deployed = false;
                event.Members.push_back(part);
            };

            uint32 idx = 0;
            for (BotCandidate const& b : attackers)
                add(b, true, idx++);
            idx = 0;
            for (BotCandidate const& b : defenders)
                add(b, false, idx++);
        }

        // Check if atomic batch reservation satisfied minimum requirements (PV-12)
        uint32 actualAttackers = 0;
        uint32 actualDefenders = 0;
        for (Participant const& p : event.Members)
        {
            if (p.Attacker)
                ++actualAttackers;
            else
                ++actualDefenders;
        }

        if (actualAttackers < requiredAttackers || actualDefenders < requiredDefenders ||
            (actualAttackers + actualDefenders) < requiredTotal)
        {
            if (_debug)
                LOG_INFO("module", "[PvPLife] '{}' aborted: actual leased attackers {}/{} defenders {}/{} total {} (min required {})",
                    zone.Name, actualAttackers, requiredAttackers, actualDefenders, requiredDefenders,
                    actualAttackers + actualDefenders, requiredTotal);
            if (handler)
                handler->PSendSysMessage("PvP Life: Insufficient successfully leased bots for {} (attackers {}/{}, defenders {}/{}).",
                    zone.Name, actualAttackers, requiredAttackers, actualDefenders, requiredDefenders);
            rollback();
            return false;
        }

        std::vector<uint32> admissionGuids;
        for (Participant const& part : event.Members)
            admissionGuids.push_back(part.Bot.GuidLow);
        event.AdmissionRequestId = PlayerbotsLife::SubmitAdmissionRequest(
            PlayerbotsLife::ReservationOwner::PvPLife, event.EventId, admissionGuids,
            CalculatePopulationBudget(), now, event.PrepareDeadline);
        if (!event.AdmissionRequestId)
        {
            rollback();
            return false;
        }
        _activeEvents.push_back(event);
        WorldDatabase.Execute("UPDATE pvp_life_zone SET last_start={} WHERE id={}", now, zone.Id);
        for (Zone& cached : _zoneCache)
            if (cached.Id == zone.Id)
                cached.LastStart = now;

        std::string label = std::string(TypeName(zone.Type)) + " at " + zone.Name;
        LOG_INFO("module", "[PvPLife] START #{} {} attackers={} defenders={} duration={}m",
            event.EventId, label, actualAttackers, actualDefenders, (event.EndsAt - event.StartedAt) / MINUTE);

        AuditLog("START", "event=" + std::to_string(event.EventId) + " spot=" + zone.Name +
            " mode=" + (zone.Type == ActivityType::Duel ? "duel" : "world_pvp") +
            " attackerTeam=" + TeamName(zone.AttackerTeam) + " defenderTeam=" + TeamName(zone.DefenderTeam) +
            " attackers=" + std::to_string(actualAttackers) + " defenders=" + std::to_string(actualDefenders) +
            " durationSeconds=" + std::to_string(event.EndsAt - event.StartedAt));

        if (_announce)
            Announce("[World PvP] " + label);
        if (handler)
            handler->PSendSysMessage("PvP Life: #{} {} queued for admission (bots {} + {}).",
                event.EventId, label, actualAttackers, actualDefenders);
        return true;
    }

    void Manager::QueueParticipantRelease(Participant const& part, bool returnHome)
    {
        if (!PlayerbotsLife::BeginRelease(part.Token))
            return; // A stale record cannot clean another generation's actor.
        if (!part.Deployed || !part.Journal.Captured)
        {
            PlayerbotsLife::ReleaseLeaseExact(part.Token);
            return;
        }
        if (std::any_of(_releasingParticipants.begin(), _releasingParticipants.end(),
            [&](ReleasingParticipant const& current) { return current.Part.Token.Generation == part.Token.Generation; }))
            return;

        // Clear any queued bot-directed steps for this departing participant immediately (PVP-01)
        uint32 guid = part.Bot.GuidLow;
        _moveQueue.erase(std::remove_if(_moveQueue.begin(), _moveQueue.end(),
            [guid](MoveStep const& s) { return s.GuidLow == guid; }), _moveQueue.end());
        _duelQueue.erase(std::remove_if(_duelQueue.begin(), _duelQueue.end(),
            [guid](DuelStep const& s) { return s.ChallengerGuidLow == guid || s.TargetGuidLow == guid; }), _duelQueue.end());
        _engagementQueue.erase(std::remove_if(_engagementQueue.begin(), _engagementQueue.end(),
            [guid](EngagementStep const& s) { return s.BotGuidLow == guid || s.TargetGuidLow == guid; }), _engagementQueue.end());
        _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
            [guid](ChatStep const& s) { return s.SpeakerGuidLow == guid; }), _chatQueue.end());

        ReleasingParticipant releasing;
        releasing.Part = part;
        releasing.ReturnHome = returnHome;
        releasing.EnqueuedAt = GameTimeSeconds();
        releasing.LastProgress = releasing.EnqueuedAt;
        releasing.Deadline = releasing.EnqueuedAt + 60;
        releasing.Phase = ReleasePhase::PendingCombatExit;
        releasing.Attempts = 0;
        _releasingParticipants.push_back(releasing);
    }

    void Manager::EndEvent(ActiveEvent& event, std::string const& reason)
    {
        if (event.Closing)
            return;
        event.Closing = true; // Terminal before callbacks, queue purges, or cleanup.
        if (event.AdmissionRequestId != 0)
            PlayerbotsLife::CancelAdmissionRequest(event.AdmissionRequestId, PlayerbotsLife::ReservationOwner::PvPLife);
        event.AdmissionRequestId = 0;
        uint64 id = event.EventId;
        _moveQueue.erase(std::remove_if(_moveQueue.begin(), _moveQueue.end(),
            [id](MoveStep const& step) { return step.EventId == id; }), _moveQueue.end());
        _duelQueue.erase(std::remove_if(_duelQueue.begin(), _duelQueue.end(),
            [id](DuelStep const& step) { return step.EventId == id; }), _duelQueue.end());
        _engagementQueue.erase(std::remove_if(_engagementQueue.begin(), _engagementQueue.end(),
            [id](EngagementStep const& step) { return step.EventId == id; }), _engagementQueue.end());
        _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(),
            [id](ChatStep const& step) { return step.EventId == id; }), _chatQueue.end());
        for (Participant const& part : event.Members)
            QueueParticipantRelease(part, _returnBots);
        for (DuelPair const& pair : event.DuelPairs)
            if (pair.StagingSlotId && !IsDuelSlotInUse(pair.StagingSlotId))
                PlayerbotsLife::ReleaseDuelStagingSlot(pair.StagingSlotId, PlayerbotsLife::ReservationOwner::PvPLife);
        LOG_INFO("module", "[PvPLife] END #{} {} reason={}", id, event.EventZone.Name, reason);
        AuditLog("END", "event=" + std::to_string(id) + " reason=" + reason);
    }

    void Manager::ProcessReleasingParticipants()
    {
        auto it = _releasingParticipants.begin();
        uint32 now = GameTimeSeconds();
        auto releaseSlotIfUnused = [this](Participant const& part)
        {
            if (part.DuelStagingSlotId && !IsDuelSlotInUse(part.DuelStagingSlotId))
                PlayerbotsLife::ReleaseDuelStagingSlot(part.DuelStagingSlotId, PlayerbotsLife::ReservationOwner::PvPLife);
        };
        while (it != _releasingParticipants.end())
        {
            Participant const& part = it->Part;
            if (!PlayerbotsLife::ValidateLeaseState(part.Token, PlayerbotsLife::LeaseState::Releasing))
            {
                releaseSlotIfUnused(part);
                it = _releasingParticipants.erase(it);
                continue;
            }
            Player* player = FindPlayer(part.Bot.GuidLow);
            if (!player || !player->GetSession() || IsHumanControlled(player))
            {
                releaseSlotIfUnused(part);
                PlayerbotsLife::ReleaseLeaseExact(part.Token);
                it = _releasingParticipants.erase(it);
                continue;
            }

            // Timeout handling on stuck combat/transfer (PVP-01)
            if (now >= it->Deadline)
            {
                LOG_WARN("module", "[PvPLife] Release deadline reached for actor {} (phase={}, attempts={}); executing safe terminal disengage.",
                    part.Bot.GuidLow, static_cast<uint32>(it->Phase), it->Attempts);
                CloseNativeDuel(player, part);
                if (!IsHumanControlled(player))
                {
                    if (player->IsInCombat())
                        player->CombatStop(true);
                    RestoreAIState(player, part.Journal);
                }
                releaseSlotIfUnused(part);
                PlayerbotsLife::ReleaseLeaseExact(part.Token);
                it = _releasingParticipants.erase(it);
                continue;
            }

            if (!player->IsInWorld() || player->IsBeingTeleported())
            {
                ++it->Attempts;
                ++it;
                continue;
            }
            if (_changesThisTick >= _maxChangesPerTick)
            {
                ++it;
                continue;
            }

            CloseNativeDuel(player, part);

            if (it->Phase == ReleasePhase::PendingCombatExit)
            {
                if (player->IsInCombat())
                {
                    ++it->Attempts;
                    ++it;
                    continue;
                }
                it->Phase = ReleasePhase::RestoreWhenSafe;
                it->LastProgress = now;
            }

            if (it->Phase == ReleasePhase::RestoreWhenSafe)
            {
                RestoreAIState(player, part.Journal);
                if (sRandomPlayerbotMgr.IsRandomBot(player))
                    sRandomPlayerbotMgr.ScheduleTeleport(part.Bot.GuidLow);
                if (it->ReturnHome && player->IsAlive() && !player->IsInCombat())
                    player->TeleportTo(part.OriginalMap, part.OriginalX, part.OriginalY, part.OriginalZ, part.OriginalO);
                ++_changesThisTick;
                it->Phase = ReleasePhase::Released;
                releaseSlotIfUnused(part);
                PlayerbotsLife::ReleaseLeaseExact(part.Token);
                it = _releasingParticipants.erase(it);
            }
        }
    }

    void Manager::ExpireEvents()
    {
        uint32 now = GameTimeSeconds();
        for (ActiveEvent& event : _activeEvents)
        {
            if (event.Closing)
                continue;
            if (event.EndsAt <= now)
                EndEvent(event, "timer");
            else if (event.FullyPrepared && event.EventZone.Type == ActivityType::Duel)
            {
                uint32 alive = 0;
                for (Participant const& part : event.Members)
                    if (Player* player = FindPlayer(part.Bot.GuidLow); player && player->IsInWorld() && player->IsAlive())
                        ++alive;
                if (alive < 2)
                    EndEvent(event, "duel-population");
            }
        }
        _activeEvents.erase(std::remove_if(_activeEvents.begin(), _activeEvents.end(),
            [](ActiveEvent const& event) { return event.Closing; }), _activeEvents.end());
    }

    void Manager::ProcessMoveQueue()
    {
        uint32 now = GameTimeSeconds();
        std::vector<MoveStep> keep;
        for (MoveStep const& step : _moveQueue)
        {
            if (step.ExecuteAt > now)
            {
                keep.push_back(step);
                continue;
            }
            auto event = std::find_if(_activeEvents.begin(), _activeEvents.end(),
                [&](ActiveEvent const& current) { return current.EventId == step.EventId; });
            if (event == _activeEvents.end() || event->Closing || event->EndsAt <= now ||
                !PlayerbotsLife::ValidateActiveLease(step.Token))
                continue;
            Player* p = FindPlayer(step.GuidLow);
            if (!p || p->IsBeingTeleported())
            {
                if (step.RetryCount < 4 && (p || step.RetryCount < 2))
                {
                    MoveStep retry = step;
                    retry.ExecuteAt = now + 2;
                    ++retry.RetryCount;
                    keep.push_back(retry);
                }
                continue;
            }
            if (!CanExecuteStep(step.EventId, step.Generation, step.GuidLow, true))
                continue;
            MoveBot(p, step.MapId, step.X, step.Y, step.Z, step.O, step.Teleport);
            AuditLog("MOVE", "event=" + std::to_string(step.EventId) + " player=" + step.Name +
                " guid=" + std::to_string(step.GuidLow) + " map=" + std::to_string(step.MapId) +
                " x=" + std::to_string(step.X) + " y=" + std::to_string(step.Y) + " z=" + std::to_string(step.Z) +
                " mode=" + (step.Teleport ? "teleport" : "movepoint"));
        }
        _moveQueue.swap(keep);
    }

    void Manager::ProcessEngagementQueue()
    {
        if (_engagementQueue.empty())
            return;

        uint32 now = GameTimeSeconds();
        std::vector<EngagementStep> keep;
        for (EngagementStep const& step : _engagementQueue)
        {
            auto preparing = std::find_if(_activeEvents.begin(), _activeEvents.end(),
                [&](ActiveEvent const& event) { return event.EventId == step.EventId; });
            if (preparing != _activeEvents.end() && !preparing->Closing && !preparing->FullyPrepared &&
                preparing->PrepareDeadline > now)
            {
                keep.push_back(step);
                continue;
            }
            if (step.ExecuteAt > now)
            {
                keep.push_back(step);
                continue;
            }

            if (!CanExecuteStep(step.EventId, step.Generation, step.BotGuidLow))
                continue;

            Player* bot = FindPlayer(step.BotGuidLow);
            Player* target = FindPlayer(step.TargetGuidLow);
            if (!bot || !target || !bot->IsAlive() || !target->IsAlive())
                continue;

            EngageTarget(bot, target);

            if (!bot->IsInCombat() && step.RetryCount < step.MaxRetries)
            {
                EngagementStep retry = step;
                retry.ExecuteAt = now + _engageRetrySeconds;
                ++retry.RetryCount;
                keep.push_back(retry);
            }
        }
        _engagementQueue.swap(keep);
    }

    void Manager::ProcessDuelQueue()
    {
        uint32 now = GameTimeSeconds();
        std::vector<DuelStep> keep;
        for (DuelStep const& step : _duelQueue)
        {
            auto preparing = std::find_if(_activeEvents.begin(), _activeEvents.end(),
                [&](ActiveEvent const& event) { return event.EventId == step.EventId; });
            if (preparing != _activeEvents.end() && !preparing->Closing && !preparing->FullyPrepared &&
                preparing->PrepareDeadline > now)
            {
                keep.push_back(step);
                continue;
            }
            if (step.ExecuteAt > now)
            {
                keep.push_back(step);
                continue;
            }

            if (!CanExecuteStep(step.EventId, step.Generation, step.ChallengerGuidLow))
                continue;
            if (!step.TargetIsRealPlayer && !CanExecuteStep(step.EventId, step.TargetToken.Generation, step.TargetGuidLow))
                continue;

            auto event = std::find_if(_activeEvents.begin(), _activeEvents.end(), [&](ActiveEvent const& active)
            {
                return active.EventId == step.EventId && active.EventZone.Type == ActivityType::Duel && active.EndsAt > now;
            });
            if (event == _activeEvents.end())
                continue;
            Player* challenger = FindPlayer(step.ChallengerGuidLow);
            Player* target = FindPlayer(step.TargetGuidLow);
            if (!challenger || !target || challenger == target || !challenger->GetSession() || !target->GetSession())
                continue;
            if (!GET_PLAYERBOT_AI(challenger) || !IsConfiguredBotAccount(challenger->GetSession()->GetAccountId()))
                continue;
            if (step.TargetIsRealPlayer ? !IsRealPlayer(target) :
                (!GET_PLAYERBOT_AI(target) || !IsConfiguredBotAccount(target->GetSession()->GetAccountId())))
                continue;

            auto fail = [&](char const* reason, uint32 result = uint32(SPELL_CAST_OK))
            {
                uint32 until = now + std::max<uint32>(DuelFailureBackoff, _botDuelCooldownSeconds);
                _botDuelCooldown[step.ChallengerGuidLow] = std::max(_botDuelCooldown[step.ChallengerGuidLow], until);
                if (!step.TargetIsRealPlayer)
                    _botDuelCooldown[step.TargetGuidLow] = std::max(_botDuelCooldown[step.TargetGuidLow], until);
                LOG_WARN("module", "[PvPLife] Duel request deferred: {} -> {}; reason={} spell_result={} spell={} "
                    "area={}/{} dist={} phase={}/{} backoff={}s",
                    challenger->GetName(), target->GetName(), reason, result, _duelSpellId,
                    challenger->GetAreaId(), target->GetAreaId(), challenger->GetExactDist(target),
                    challenger->GetPhaseMask(), target->GetPhaseMask(), until - now);
            };
            if (!challenger->IsInWorld() || !target->IsInWorld() || !challenger->IsAlive() || !target->IsAlive() ||
                challenger->IsBeingTeleported() || target->IsBeingTeleported() ||
                challenger->IsInFlight() || target->IsInFlight())
                continue;
            if (challenger->GetMap() != target->GetMap() || !challenger->InSamePhase(target))
            {
                fail("Map or phase mismatch", SPELL_FAILED_BAD_TARGETS);
                continue;
            }

            bool matching = challenger->duel && target->duel &&
                challenger->duel->Opponent == target && target->duel->Opponent == challenger &&
                challenger->duel->Initiator == challenger && target->duel->Initiator == challenger &&
                challenger->GetGuidValue(PLAYER_DUEL_ARBITER) &&
                challenger->GetGuidValue(PLAYER_DUEL_ARBITER) == target->GetGuidValue(PLAYER_DUEL_ARBITER);
            bool started = matching &&
                (challenger->duel->State == DUEL_STATE_COUNTDOWN || challenger->duel->State == DUEL_STATE_IN_PROGRESS) &&
                (target->duel->State == DUEL_STATE_COUNTDOWN || target->duel->State == DUEL_STATE_IN_PROGRESS);
            DuelRequestAction action = EvaluateDuelRequest(step.RequestSent, challenger->duel || target->duel,
                matching, step.TargetIsRealPlayer, started, now, step.RequestDeadline);
            if (action == DuelRequestAction::Busy)
                continue;
            if (action == DuelRequestAction::Wait)
            {
                DuelStep waiting = step;
                waiting.ExecuteAt = now + 1;
                keep.push_back(waiting);
                continue;
            }
            if (action == DuelRequestAction::TimedOut)
            {
                fail("Duel state not created after cast");
                continue;
            }
            if (action == DuelRequestAction::AcceptBot || action == DuelRequestAction::Confirmed)
            {
                if (action == DuelRequestAction::AcceptBot)
                {
                    if (target->duel->State != DUEL_STATE_CHALLENGED || challenger->duel->State != DUEL_STATE_CHALLENGED)
                    {
                        fail("Duel accept state mismatch");
                        continue;
                    }
                    WorldPacket packet(CMSG_DUEL_ACCEPTED, 8);
                    packet << target->GetGuidValue(PLAYER_DUEL_ARBITER);
                    target->GetSession()->HandleDuelAcceptedOpcode(packet);
                    if (!challenger->duel || !target->duel ||
                        challenger->duel->State != DUEL_STATE_COUNTDOWN || target->duel->State != DUEL_STATE_COUNTDOWN)
                    {
                        fail("Countdown not verified after duel acceptance");
                        continue;
                    }
                }
                RememberDuelIdentity(step.EventId, challenger, target);
                if (step.TargetIsRealPlayer)
                {
                    _botChallengeCooldown[step.ChallengerGuidLow] = now + _botChallengeCooldownSeconds;
                    _playerChallengeCooldown[step.TargetGuidLow] = now + _realPlayerCooldownSeconds;
                    PlayerbotsLife::RecordRealPlayerChallenge(step.TargetGuidLow, now, _realPlayerCooldownSeconds);
                }
                else
                {
                    _botDuelCooldown[step.ChallengerGuidLow] = now + _botDuelCooldownSeconds;
                    _botDuelCooldown[step.TargetGuidLow] = now + _botDuelCooldownSeconds;
                }
                for (auto& pair : event->DuelPairs)
                {
                    if (pair.PairId == step.PairId ||
                        (pair.ChallengerGuidLow == step.ChallengerGuidLow && pair.TargetGuidLow == step.TargetGuidLow))
                    {
                        pair.State = DuelPairState::Active;
                        break;
                    }
                }

                LOG_INFO("module", "[PvPLife] Duel state confirmed: {} -> {}; state={}",
                    challenger->GetName(), target->GetName(), step.TargetIsRealPlayer ? "waiting/accepted by player" : "countdown/in-progress");
                AuditLog("DUEL", "event=" + std::to_string(step.EventId) + " challenger=" + challenger->GetName() +
                    " target=" + target->GetName() + " spell=" + std::to_string(_duelSpellId));
                continue;
            }

            if (challenger->IsInCombat() || target->IsInCombat() || challenger->IsPetInCombat() || target->IsPetInCombat())
            {
                fail("Self or pet in combat", SPELL_FAILED_TARGET_AFFECTING_COMBAT);
                continue;
            }
            SpellInfo const* spell = sSpellMgr->GetSpellInfo(_duelSpellId);
            if (!spell || !spell->HasEffect(SPELL_EFFECT_DUEL))
            {
                fail("Spell lacks duel effect", SPELL_FAILED_SPELL_UNAVAILABLE);
                continue;
            }
            AreaTableEntry const* casterArea = sAreaTableStore.LookupEntry(challenger->GetAreaId());
            AreaTableEntry const* targetArea = sAreaTableStore.LookupEntry(target->GetAreaId());
            if ((casterArea && !(casterArea->flags & AREA_FLAG_ALLOW_DUELS)) ||
                (targetArea && !(targetArea->flags & AREA_FLAG_ALLOW_DUELS)))
            {
                fail("Duels forbidden in area", SPELL_FAILED_NO_DUELING);
                continue;
            }
            if (!target->GetSocial() || target->GetSocial()->HasIgnore(challenger->GetGUID()))
            {
                fail("Social info not ready or target ignored", SPELL_FAILED_BAD_TARGETS);
                continue;
            }
            SpellCastResult targetResult = spell->CheckTarget(challenger, target, false);
            if (targetResult != SPELL_CAST_OK)
            {
                fail("Target requirements not met", targetResult);
                continue;
            }
            float const closeChallengeDistance = 4.0f;
            float const exactDist = challenger->GetExactDist(target);
            if (exactDist > closeChallengeDistance || !challenger->IsWithinLOSInMap(target))
            {
                DuelStep retry = step;
                if (retry.RetryCount++ < DuelApproachRetries)
                {
                    // Compute varied approach destination with flank arc offset so bots don't all follow the same straight line
                    float const baseAngle = target->GetAngle(challenger);
                    float const flankOffset = frand(-0.45f, 0.45f);
                    float const approachAngle = Position::NormalizeOrientation(baseAngle + flankOffset);
                    float const approachDist = 2.5f + frand(0.2f, 1.0f);

                    float nx = target->GetPositionX() + std::cos(approachAngle) * approachDist;
                    float ny = target->GetPositionY() + std::sin(approachAngle) * approachDist;
                    float nz = target->GetPositionZ();
                    if (target->GetMap())
                    {
                        float probedZ = target->GetMap()->GetHeight(target->GetPhaseMask(), nx, ny, nz);
                        if (probedZ > -1000.0f && std::abs(probedZ - nz) < 8.0f)
                            nz = probedZ;
                    }

                    challenger->SetSelection(target->GetGUID());
                    target->SetFacingToObject(challenger);

                    if (!challenger->isMoving() || challenger->GetDistance2d(nx, ny) > 2.0f)
                    {
                        challenger->ClearUnitState(UNIT_STATE_CHASE | UNIT_STATE_FOLLOW);
                        challenger->GetMotionMaster()->Clear();
                        challenger->GetMotionMaster()->MovePoint(0, nx, ny, nz);
                    }

                    retry.ExecuteAt = now + 1;
                    keep.push_back(retry);
                }
                else
                    fail("Approach or line-of-sight timeout", SPELL_FAILED_OUT_OF_RANGE);
                continue;
            }

            challenger->StopMoving();
            challenger->GetMotionMaster()->Clear();
            challenger->SetFacingToObject(target);
            if (!step.TargetIsRealPlayer)
            {
                target->StopMoving();
                target->GetMotionMaster()->Clear();
                target->SetFacingToObject(challenger);
                if (roll_chance_i(40))
                    challenger->HandleEmoteCommand(EMOTE_ONESHOT_BOW);
                challenger->SetHealth(challenger->GetMaxHealth());
                target->SetHealth(target->GetMaxHealth());
                challenger->SetPower(challenger->getPowerType(), challenger->GetMaxPower(challenger->getPowerType()));
                target->SetPower(target->getPowerType(), target->GetMaxPower(target->getPowerType()));
            }
            SpellCastResult result = challenger->CastSpell(target, _duelSpellId, true);
            if (result != SPELL_CAST_OK)
            {
                fail("Duel spell cast failed", result);
                continue;
            }
            RememberDuelIdentity(step.EventId, challenger, target);
            DuelStep waiting = step;
            waiting.RequestSent = true;
            waiting.RequestDeadline = now + DuelRequestTimeout;
            waiting.ExecuteAt = now + 1;
            keep.push_back(waiting);
        }
        _duelQueue.swap(keep);
    }

    std::string Manager::RandomChatLine(ActivityType type, ChatChannel channel, TeamSide speakerTeam)
    {
        uint64 total = 0;
        for (CachedChatLine const& line : _chatCache)
            if (line.Type == type && line.Channel == channel &&
                (line.Team == speakerTeam || line.Team == TeamSide::Any))
                total += line.Weight;
        if (!total)
            return {};
        uint64 roll = static_cast<uint64>(frand(0.0f, 1.0f) * total);
        roll = std::min(roll, total - 1);
        for (CachedChatLine const& line : _chatCache)
            if (line.Type == type && line.Channel == channel &&
                (line.Team == speakerTeam || line.Team == TeamSide::Any))
            {
                if (roll < line.Weight)
                    return line.Text;
                roll -= line.Weight;
            }
        return {};
    }

    void Manager::ScheduleEventChat(ActiveEvent const& event)
    {
        if (!_botChatEnable || !event.EventZone.BotChat)
            return;
        if (_botChatYellChance == 0 && _botChatWorldChance == 0)
            return;
        if (event.EventZone.Type != ActivityType::ForTheHorde && event.EventZone.Type != ActivityType::ForTheAlliance)
            return;

        std::vector<Participant const*> defenders;
        for (Participant const& p : event.Members)
            if (!p.Attacker)
                defenders.push_back(&p);
        if (defenders.empty())
            return;

        TeamSide team = event.EventZone.DefenderTeam;
        uint32 base = _arrivalStaggerMax + 8;
        if (_botChatYellChance > 0 && urand(1, 100) <= _botChatYellChance)
        {
            std::string line = RandomChatLine(event.EventZone.Type, ChatChannel::Yell, team);
            if (!line.empty())
            {
                Participant const* speaker = defenders[urand(0, static_cast<uint32>(defenders.size() - 1))];
                ChatStep step;
                step.EventId = event.EventId;
                step.Generation = speaker->Token.Generation;
                step.Token = speaker->Token;
                step.SpeakerGuidLow = speaker->Bot.GuidLow;
                step.ExecuteAt = GameTimeSeconds() + base + urand(1, 8);
                step.Channel = ChatChannel::Yell;
                step.Text = std::move(line);
                _chatQueue.push_back(step);
            }
        }
        if (_botChatWorldChance > 0 && urand(1, 100) <= _botChatWorldChance)
        {
            std::string line = RandomChatLine(event.EventZone.Type, ChatChannel::World, team);
            if (!line.empty())
            {
                Participant const* speaker = defenders[urand(0, static_cast<uint32>(defenders.size() - 1))];
                ChatStep step;
                step.EventId = event.EventId;
                step.Generation = speaker->Token.Generation;
                step.Token = speaker->Token;
                step.SpeakerGuidLow = speaker->Bot.GuidLow;
                step.ExecuteAt = GameTimeSeconds() + base + urand(8, 25);
                step.Channel = ChatChannel::World;
                step.Text = std::move(line);
                _chatQueue.push_back(step);
            }
        }
    }

    void Manager::ProcessChatQueue()
    {
        if (!_botChatEnable)
        {
            if (!_chatQueue.empty())
                _chatQueue.clear();
            return;
        }

        uint32 now = GameTimeSeconds();
        std::vector<ChatStep> keep;
        for (ChatStep const& step : _chatQueue)
        {
            if (step.Channel == ChatChannel::Yell && _botChatYellChance == 0)
                continue;
            if (step.Channel == ChatChannel::World && _botChatWorldChance == 0)
                continue;

            auto preparing = std::find_if(_activeEvents.begin(), _activeEvents.end(),
                [&](ActiveEvent const& event) { return event.EventId == step.EventId; });
            if (preparing != _activeEvents.end() && !preparing->Closing && !preparing->FullyPrepared &&
                preparing->PrepareDeadline > now)
            {
                keep.push_back(step);
                continue;
            }
            if (step.ExecuteAt > now)
            {
                keep.push_back(step);
                continue;
            }
            if (!CanExecuteStep(step.EventId, step.Generation, step.SpeakerGuidLow))
                continue;
            Player* speaker = FindPlayer(step.SpeakerGuidLow);
            if (!speaker)
                continue;
            PlayerbotAI* ai = GET_PLAYERBOT_AI(speaker);
            if (!ai)
                continue;
            if (step.Channel == ChatChannel::Yell)
            {
                if (_botChatYellChance > 0)
                    ai->Yell(step.Text);
            }
            else
            {
                if (_botChatWorldChance > 0)
                    ai->SayToWorld(step.Text);
            }
        }
        _chatQueue.swap(keep);
    }

    void Manager::MaintainBotDuels()
    {
        if (!_duelEnable)
            return;

        uint32 now = GameTimeSeconds();
        std::unordered_set<uint32> queued;
        for (DuelStep const& step : _duelQueue)
        {
            queued.insert(step.ChallengerGuidLow);
            queued.insert(step.TargetGuidLow);
        }

        for (ActiveEvent const& event : _activeEvents)
        {
            if (event.Closing || !event.FullyPrepared || event.EventZone.Type != ActivityType::Duel)
                continue;

            float centerX = (event.EventZone.RallyX + event.EventZone.TargetX) * 0.5f;
            float centerY = (event.EventZone.RallyY + event.EventZone.TargetY) * 0.5f;
            float centerZ = (event.EventZone.RallyZ + event.EventZone.TargetZ) * 0.5f;
            std::vector<uint32> available;
            for (Participant const& participant : event.Members)
            {
                if (!participant.Deployed || !PlayerbotsLife::ValidateActiveLease(participant.Token))
                    continue;

                uint32 guidLow = participant.Bot.GuidLow;
                if (queued.count(guidLow))
                    continue;

                Player* bot = FindPlayer(guidLow);
                if (IsHumanControlled(bot))
                    continue;
                if (!bot || !bot->IsAlive() || bot->IsBeingTeleported() || bot->duel || bot->IsInCombat())
                    continue;

                ApplyPvpStrategies(bot, true);
                if (bot->GetMapId() != event.EventZone.MapId ||
                    bot->GetDistance2d(participant.ActivityX, participant.ActivityY) > _duelLeashRadius)
                {
                    continue;
                }

                auto duelCd = _botDuelCooldown.find(guidLow);
                if (duelCd != _botDuelCooldown.end() && duelCd->second > now)
                    continue;
                auto playerCd = _botChallengeCooldown.find(guidLow);
                if (playerCd != _botChallengeCooldown.end() && playerCd->second > now)
                    continue;

                available.push_back(guidLow);
            }

            std::unordered_set<uint32> busy;
            for (Participant const& participant : event.Members)
                if (Player* member = FindPlayer(participant.Bot.GuidLow); member && (member->duel || queued.count(participant.Bot.GuidLow)))
                    busy.insert(participant.Bot.GuidLow);
            uint32 scheduled = (static_cast<uint32>(busy.size()) + 1) / 2;
            while (available.size() >= 2 && scheduled < _duelPairLimit)
            {
                uint32 firstIndex = urand(0, static_cast<uint32>(available.size() - 1));
                uint32 first = available[firstIndex];
                Player* a = FindPlayer(first);
                if (!a)
                {
                    available.erase(available.begin() + firstIndex);
                    continue;
                }

                std::vector<uint32> compatibleIndexes;
                for (uint32 i = 0; i < available.size(); ++i)
                {
                    if (i == firstIndex)
                        continue;
                    Player* candidate = FindPlayer(available[i]);
                    if (!candidate || a->GetTeamId() != candidate->GetTeamId())
                        continue;
                    if (a->GetDistance2d(candidate) > _duelLeashRadius * 2.0f)
                        continue;
                    uint32 levelDiff = std::abs(static_cast<int32>(a->GetLevel()) - static_cast<int32>(candidate->GetLevel()));
                    if (levelDiff <= _botDuelMaxLevelDifference)
                        compatibleIndexes.push_back(i);
                }

                if (compatibleIndexes.empty())
                {
                    available.erase(available.begin() + firstIndex);
                    continue;
                }

                // Prioritize closest available partners to eliminate unnecessary long-distance running across the duel field
                std::sort(compatibleIndexes.begin(), compatibleIndexes.end(), [&](uint32 idx1, uint32 idx2)
                {
                    Player* p1 = FindPlayer(available[idx1]);
                    Player* p2 = FindPlayer(available[idx2]);
                    if (!p1 || !p2) return p1 != nullptr;
                    return a->GetDistance2d(p1) < a->GetDistance2d(p2);
                });

                // Pick from nearest candidates (up to 2 closest) to preserve subtle variety while staying nearby
                uint32 pickLimit = std::min<uint32>(static_cast<uint32>(compatibleIndexes.size()), 2);
                uint32 secondIndex = compatibleIndexes[urand(0, pickLimit - 1)];
                uint32 second = available[secondIndex];
                Player* b = FindPlayer(second);

                if (secondIndex > firstIndex)
                {
                    available.erase(available.begin() + secondIndex);
                    available.erase(available.begin() + firstIndex);
                }
                else
                {
                    available.erase(available.begin() + firstIndex);
                    available.erase(available.begin() + secondIndex);
                }

                if (b)
                {
                    PlayerbotsLife::LeaseToken tokenA, tokenB;
                    for (Participant const& part : event.Members)
                    {
                        if (part.Bot.GuidLow == first)
                            tokenA = part.Token;
                        else if (part.Bot.GuidLow == second)
                            tokenB = part.Token;
                    }
                    ScheduleDuel(event.EventId, _nextPairId++, tokenA, tokenB, first, second, a->GetName(), b->GetName(), urand(_duelPairDelayMin, _duelPairDelayMax));
                    queued.insert(first);
                    queued.insert(second);
                    ++scheduled;
                }
            }
        }
    }

    void Manager::MaintainDuelParticipants()
    {
        uint32 now = GameTimeSeconds();
        for (ActiveEvent const& event : _activeEvents)
        {
            if (event.Closing || !event.FullyPrepared || event.EventZone.Type != ActivityType::Duel)
                continue;

            for (Participant const& participant : event.Members)
            {
                if (!participant.Deployed || !PlayerbotsLife::ValidateActiveLease(participant.Token))
                    continue;

                Player* bot = FindPlayer(participant.Bot.GuidLow);
                if (IsHumanControlled(bot))
                    continue;
                if (!bot || !bot->IsAlive() || bot->IsBeingTeleported())
                    continue;

                // If in active duel combat or normal combat, let combat AI run freely
                if (bot->duel || bot->IsInCombat())
                    continue;

                if (std::any_of(_duelQueue.begin(), _duelQueue.end(), [&](DuelStep const& step)
                    { return step.EventId == event.EventId && (step.ChallengerGuidLow == participant.Bot.GuidLow || step.TargetGuidLow == participant.Bot.GuidLow); }))
                    continue;

                if (std::any_of(_moveQueue.begin(), _moveQueue.end(), [&](MoveStep const& step)
                    { return step.EventId == event.EventId && step.GuidLow == participant.Bot.GuidLow; }))
                    continue;

                // Cooldown check for relocation / returning to staging
                auto cdIt = _botLastRelocateTime.find(participant.Bot.GuidLow);
                if (cdIt != _botLastRelocateTime.end() && now < cdIt->second + _duelRelocateCooldownSeconds)
                    continue;

                bool wrongMap = (bot->GetMapId() != event.EventZone.MapId);
                float dist = wrongMap ? 9999.0f : bot->GetDistance2d(participant.ActivityX, participant.ActivityY);
                float distFromCenter = wrongMap ? 9999.0f : bot->GetDistance2d(event.EventZone.RallyX, event.EventZone.RallyY);

                // If the bot has concluded a duel and is within the duel grounds, retain its current position
                // as its staging spot instead of forcing it to walk 40+ yards back to its initial slot.
                // This drastically reduces restless running across the duel grounds!
                if (!wrongMap && distFromCenter <= static_cast<float>(_duelLeashRadius) &&
                    std::hypot(bot->GetPositionX() - participant.ActivityX, bot->GetPositionY() - participant.ActivityY) > 4.0f)
                {
                    for (Participant& p : const_cast<ActiveEvent&>(event).Members)
                    {
                        if (p.Bot.GuidLow == participant.Bot.GuidLow)
                        {
                            p.ActivityX = bot->GetPositionX();
                            p.ActivityY = bot->GetPositionY();
                            p.ActivityZ = bot->GetPositionZ();
                            p.ActivityO = bot->GetOrientation();
                            dist = 0.0f;
                            break;
                        }
                    }
                }

                if (wrongMap || distFromCenter > static_cast<float>(_duelLeashRadius) * 1.3f)
                {
                    _botLastRelocateTime[participant.Bot.GuidLow] = now;
                    if (wrongMap || distFromCenter > 60.0f)
                    {
                        // Cross-map or extremely far: teleport
                        MoveBot(bot, event.EventZone.MapId, participant.ActivityX, participant.ActivityY,
                            participant.ActivityZ, participant.ActivityO, true);
                    }
                    else
                    {
                        // Natural pathing walk back to staging spot, no snap-teleporting!
                        MoveBot(bot, event.EventZone.MapId, participant.ActivityX, participant.ActivityY,
                            participant.ActivityZ, participant.ActivityO, false);
                    }
                    continue;
                }

                // Idle staging bots: maintain static position facing staging orientation
                if (PlayerbotAI* ai = GET_PLAYERBOT_AI(bot))
                {
                    if (!ai->HasStrategy("duel", BOT_STATE_NON_COMBAT) ||
                        !ai->HasStrategy("stay", BOT_STATE_NON_COMBAT))
                        ApplyPvpStrategies(bot, true);

                    PositionMap& positions = ai->GetAiObjectContext()->GetValue<PositionMap&>("position")->Get();
                    PositionInfo stay = positions["stay"];
                    if (!stay.isSet() || std::hypot(stay.x - participant.ActivityX, stay.y - participant.ActivityY) > 1.5f)
                    {
                        stay.Set(participant.ActivityX, participant.ActivityY, participant.ActivityZ,
                            event.EventZone.MapId);
                        positions["stay"] = stay;
                    }
                }

                if (bot->isMoving() && dist <= 2.0f)
                {
                    bot->StopMoving();
                    bot->GetMotionMaster()->Clear();
                    bot->ClearUnitState(UNIT_STATE_CHASE);
                    bot->ClearUnitState(UNIT_STATE_FOLLOW);
                }

                // Idle spectating: occasionally cheer/applaud nearby duels
                if (!bot->isMoving() && roll_chance_i(4))
                {
                    static uint32 const spectateEmotes[] = {
                        EMOTE_ONESHOT_APPLAUD, EMOTE_ONESHOT_CHEER, EMOTE_ONESHOT_ROAR, EMOTE_ONESHOT_FLEX
                    };
                    bot->HandleEmoteCommand(spectateEmotes[urand(0, 3)]);
                }
            }
        }
    }

    void Manager::ProcessRealPlayerChallenges()
    {
        if (!_duelEnable || !_challengeRealPlayers)
            return;

        uint32 now = GameTimeSeconds();
        UpdateRealPlayersSnapshot();

        for (ActiveEvent const& event : _activeEvents)
        {
            if (event.Closing || !event.FullyPrepared || event.EventZone.Type != ActivityType::Duel || !event.EventZone.ChallengePlayers)
                continue;

            struct RealPlayerTarget
            {
                uint32 GuidLow = 0;
                TeamSide Team = TeamSide::Any;
                uint8 Level = 0;
                float X = 0.0f;
                float Y = 0.0f;
            };

            std::vector<RealPlayerTarget> potentialTargets;
            for (RealPlayerSnapshotEntry const& player : _cachedRealPlayers)
            {
                if (!player.IsAlive || player.IsGameMaster || player.HasDuel || player.InCombat)
                    continue;
                if (player.Security > SEC_PLAYER)
                    continue;
                if (player.MapId != event.EventZone.MapId)
                    continue;
                uint32 playerGuid = player.GuidLow;
                if (!PlayerbotsLife::CanChallengeRealPlayer(playerGuid, now, _realPlayerCooldownSeconds))
                    continue;
                auto playerCd = _playerChallengeCooldown.find(playerGuid);
                if (playerCd != _playerChallengeCooldown.end() && playerCd->second > now)
                    continue;

                RealPlayerTarget rpt;
                rpt.GuidLow = playerGuid;
                rpt.Team = player.Team;
                rpt.Level = player.Level;
                rpt.X = player.X;
                rpt.Y = player.Y;
                potentialTargets.push_back(rpt);
            }

            if (potentialTargets.empty())
                continue;

            for (Participant const& participant : event.Members)
            {
                if (!participant.Deployed || !PlayerbotsLife::ValidateActiveLease(participant.Token))
                    continue;

                Player* bot = FindPlayer(participant.Bot.GuidLow);
                if (IsHumanControlled(bot))
                    continue;
                if (!bot || bot->duel || bot->IsInCombat() || bot->IsBeingTeleported())
                    continue;
                auto botCd = _botChallengeCooldown.find(participant.Bot.GuidLow);
                if (botCd != _botChallengeCooldown.end() && botCd->second > now)
                    continue;
                auto duelCd = _botDuelCooldown.find(participant.Bot.GuidLow);
                if (duelCd != _botDuelCooldown.end() && duelCd->second > now)
                    continue;
                if (urand(1, 100) > _realPlayerChallengeChance)
                    continue;

                std::vector<uint32> targets;
                TeamSide botTeam = bot->GetTeamId() == TEAM_ALLIANCE ? TeamSide::Alliance : TeamSide::Horde;
                float scanRadiusSq = static_cast<float>(_realPlayerScanRadius * _realPlayerScanRadius);
                float botX = bot->GetPositionX();
                float botY = bot->GetPositionY();

                for (RealPlayerTarget const& pt : potentialTargets)
                {
                    if (pt.Team != botTeam)
                        continue;
                    float dx = botX - pt.X;
                    float dy = botY - pt.Y;
                    if ((dx * dx + dy * dy) > scanRadiusSq)
                        continue;
                    uint32 diff = std::abs(static_cast<int32>(bot->GetLevel()) - static_cast<int32>(pt.Level));
                    if (diff > _realPlayerMaxLevelDifference)
                        continue;
                    targets.push_back(pt.GuidLow);
                }

                if (targets.empty())
                    continue;
                uint32 targetGuid = targets[urand(0, static_cast<uint32>(targets.size() - 1))];

                // Atomically claim challenge in shared registry (PVP-05)
                if (!PlayerbotsLife::TryClaimRealPlayerChallenge(targetGuid, now, _realPlayerCooldownSeconds))
                    continue;

                Player* targetPlayer = FindPlayer(targetGuid);
                if (targetPlayer && !targetPlayer->duel && !targetPlayer->IsInCombat())
                {
                    PlayerbotsLife::LeaseToken playerToken;
                    ScheduleDuel(event.EventId, 0, participant.Token, playerToken, bot->GetGUID().GetCounter(), targetGuid,
                        bot->GetName(), targetPlayer->GetName(), urand(1, 4), true);
                    _botChallengeCooldown[bot->GetGUID().GetCounter()] = now + _botChallengeCooldownSeconds;
                    _playerChallengeCooldown[targetGuid] = now + _realPlayerCooldownSeconds;
                }
                else
                {
                    PlayerbotsLife::ReleaseRealPlayerChallengeClaim(targetGuid, now + _realPlayerCooldownSeconds);
                }
            }
        }
    }

    void Manager::MaintainPersistentWorldPvp()
    {
        if (!_alwaysActiveWorldPvp)
            return;
        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
            return;

        uint32 active = 0;
        std::unordered_set<uint32> activeIds;
        for (ActiveEvent const& e : _activeEvents)
        {
            if (e.EventZone.Type == ActivityType::Skirmish)
                ++active;
            activeIds.insert(e.EventZone.Id);
        }
        if (active >= _minActiveSkirmishes)
            return;

        std::vector<Zone> zones = LoadZones(true, static_cast<int>(ActivityType::Skirmish));
        zones.erase(std::remove_if(zones.begin(), zones.end(), [&](Zone const& z) { return activeIds.count(z.Id) != 0; }), zones.end());

        while (!zones.empty() && active < _minActiveSkirmishes && active < _maxActiveSkirmishes)
        {
            if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
                break;

            uint32 totalWeight = 0;
            for (Zone const& z : zones)
                totalWeight += std::max<uint32>(1, z.Weight);

            uint32 roll = urand(1, std::max<uint32>(1, totalWeight));
            size_t chosen = 0;
            uint32 cursor = 0;
            for (size_t i = 0; i < zones.size(); ++i)
            {
                cursor += std::max<uint32>(1, zones[i].Weight);
                if (roll <= cursor)
                {
                    chosen = i;
                    break;
                }
            }

            Zone zone = zones[chosen];
            zones.erase(zones.begin() + chosen);
            if (StartZone(zone))
            {
                ++active;
                activeIds.insert(zone.Id);
            }
        }
    }

    void Manager::MaintainPersistentDuelZones()
    {
        if (!_duelEnable || !_duelAlwaysActive)
            return;
        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
            return;

        std::unordered_set<uint32> activeIds;
        for (ActiveEvent const& e : _activeEvents)
            if (e.EventZone.Type == ActivityType::Duel)
                activeIds.insert(e.EventZone.Id);

        std::vector<Zone> zones = LoadZones(false, static_cast<int>(ActivityType::Duel));
        for (Zone const& z : zones)
        {
            if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
                break;
            if (activeIds.find(z.Id) == activeIds.end())
                StartZone(z);
        }
    }

    void Manager::TryStartRandomSkirmish()
    {
        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
            return;

        uint32 active = 0;
        std::unordered_set<uint32> activeIds;
        for (ActiveEvent const& e : _activeEvents)
        {
            if (e.EventZone.Type == ActivityType::Skirmish)
                ++active;
            activeIds.insert(e.EventZone.Id);
        }
        if (active >= _maxActiveSkirmishes || urand(1, 100) > _randomSkirmishChance)
            return;

        std::vector<Zone> zones = LoadZones(true, static_cast<int>(ActivityType::Skirmish));
        zones.erase(std::remove_if(zones.begin(), zones.end(), [&](Zone const& z) { return activeIds.count(z.Id) != 0; }), zones.end());
        if (zones.empty())
            return;

        uint32 total = 0;
        for (Zone const& z : zones) total += z.Weight;
        uint32 roll = urand(1, std::max<uint32>(1, total));
        uint32 cursor = 0;
        for (Zone const& z : zones)
        {
            cursor += z.Weight;
            if (roll <= cursor)
            {
                StartZone(z);
                return;
            }
        }
    }

    void Manager::TryStartFactionCampaign()
    {
        if ((!_forTheHordeEnable && !_forTheAllianceEnable) || urand(1, 100) > _factionCampaignChance)
            return;
        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
            return;

        uint32 now = GameTimeSeconds();
        if (_lastFactionCampaign && _lastFactionCampaign + _factionCampaignGlobalCooldown > now)
            return;

        std::vector<Zone> zones;
        if (_forTheHordeEnable)
        {
            std::vector<Zone> fth = LoadZones(true, static_cast<int>(ActivityType::ForTheHorde));
            zones.insert(zones.end(), fth.begin(), fth.end());
        }
        if (_forTheAllianceEnable)
        {
            std::vector<Zone> fta = LoadZones(true, static_cast<int>(ActivityType::ForTheAlliance));
            zones.insert(zones.end(), fta.begin(), fta.end());
        }
        if (zones.empty())
            return;

        while (!zones.empty())
        {
            uint32 totalWeight = 0;
            for (Zone const& z : zones)
                totalWeight += std::max<uint32>(1, z.Weight);

            uint32 roll = urand(1, std::max<uint32>(1, totalWeight));
            size_t chosen = 0;
            uint32 cursor = 0;
            for (size_t i = 0; i < zones.size(); ++i)
            {
                cursor += std::max<uint32>(1, zones[i].Weight);
                if (roll <= cursor)
                {
                    chosen = i;
                    break;
                }
            }

            Zone zone = zones[chosen];
            zones.erase(zones.begin() + chosen);
            if (StartZone(zone))
            {
                _lastFactionCampaign = now;
                return;
            }
        }
    }

    // Reactive Raid Response
    void Manager::TryQueueReactiveRaidResponse()
    {
        if (!_reactiveEnable || !_pendingResponses.empty())
            return;
        if (_maxActiveEvents > 0 && _activeEvents.size() >= _maxActiveEvents)
            return;

        uint32 now = GameTimeSeconds();
        if (_lastReactiveResponse && _lastReactiveResponse + _reactiveCooldownSeconds > now)
            return;

        struct InvaderTarget
        {
            uint32 GuidLow = 0;
            std::string Name;
            TeamSide ResponseTeam = TeamSide::Any;
            uint32 MapId = 0;
            float X = 0.0f;
            float Y = 0.0f;
            float Z = 0.0f;
            float O = 0.0f;
            uint8 Level = 0;
            uint32 GroupCount = 0;
        };
        std::optional<InvaderTarget> target;

        UpdateRealPlayersSnapshot();
        for (RealPlayerSnapshotEntry const& candidate : _cachedRealPlayers)
        {
            if (!candidate.IsAlive || !candidate.IsPvP || candidate.IsGameMaster || candidate.Security > SEC_PLAYER)
                continue;
            if (!candidate.IsGroupLeader || candidate.GroupMembersCount < _reactiveMinGroupSize)
                continue;

            TeamSide responseTeam = candidate.Team == TeamSide::Alliance ? TeamSide::Horde : TeamSide::Alliance;
            if (responseTeam == TeamSide::Horde && !_reactiveHordeEnable)
                continue;
            if (responseTeam == TeamSide::Alliance && !_reactiveAllianceEnable)
                continue;

            Player* leader = FindPlayer(candidate.GuidLow);
            if (!leader || !leader->GetSession() || !leader->IsInWorld() || !leader->GetMap() || leader->GetMap()->Instanceable())
                continue;

            AreaTableEntry const* area = sAreaTableStore.LookupEntry(leader->GetAreaId());
            if (area && (area->flags & AREA_FLAG_SANCTUARY))
                continue;

            Group* group = leader->GetGroup();
            if (!group || !group->IsLeader(leader->GetGUID()) || group->GetMembersCount() < _reactiveMinGroupSize)
                continue;

            uint32 nearbyRealPlayers = 0;
            for (GroupReference const* ref = group->GetFirstMember(); ref != nullptr; ref = ref->next())
            {
                Player const* member = ref->GetSource();
                if (member && IsRealPlayer(member) && member->GetMapId() == leader->GetMapId() &&
                    member->GetExactDist(leader) <= 100.0f)
                {
                    ++nearbyRealPlayers;
                }
            }
            if (nearbyRealPlayers < _reactiveMinGroupSize)
                continue;

            InvaderTarget it;
            it.GuidLow = leader->GetGUID().GetCounter();
            it.Name = leader->GetName();
            it.ResponseTeam = responseTeam;
            it.MapId = leader->GetMapId();
            it.X = leader->GetPositionX();
            it.Y = leader->GetPositionY();
            it.Z = leader->GetPositionZ();
            it.O = leader->GetOrientation();
            it.Level = leader->GetLevel();
            it.GroupCount = nearbyRealPlayers;
            target = it;
            break;
        }

        if (!target)
            return;

        uint32 budget = CalculatePopulationBudget();
        uint32 currentActive = PlayerbotsLife::GetCooperationSnapshot().PvPLifeCount;

        uint32 availableBudget = (budget > currentActive) ? (budget - currentActive) : 0;
        if (availableBudget < 2)
            return;

        uint32 desired = std::min<uint32>(target->GroupCount, _reactiveMaxResponders);
        desired = std::min<uint32>(desired, availableBudget);

        std::unordered_set<uint32> excluded;
        for (ActiveEvent const& event : _activeEvents)
            for (Participant const& member : event.Members)
                excluded.insert(member.Bot.GuidLow);
        for (PendingRaidResponse const& r : _pendingResponses)
            for (BotCandidate const& b : r.Bots)
                excluded.insert(b.GuidLow);
        for (ReleasingParticipant const& rp : _releasingParticipants)
            excluded.insert(rp.Part.Bot.GuidLow);

        uint8 minLvl = target->Level;
        uint8 maxLvl = 80;
        if (_reactiveLevelMode == ResponderLevelMode::Fixed)
        {
            minLvl = _reactiveFixedLevel;
            maxLvl = _reactiveFixedLevel;
        }
        else
        {
            minLvl = static_cast<uint8>(std::max<int32>(1, static_cast<int32>(target->Level) - _reactiveMaxLevelDifference));
            maxLvl = static_cast<uint8>(std::min<int32>(80, static_cast<int32>(target->Level) + _reactiveMaxLevelDifference));
        }

        std::vector<BotCandidate> responders = LoadCandidates(target->ResponseTeam, minLvl, maxLvl, excluded, desired);
        if (responders.size() > desired)
            responders.resize(desired);
        for (BotCandidate const& bot : responders)
            excluded.insert(bot.GuidLow);

        std::vector<uint32> pendingLogins;
        if (responders.size() < desired && _reactiveLoginOfflineBots)
        {
            std::vector<BotCandidate> offline = LoadOfflineCandidates(target->ResponseTeam, minLvl, excluded);
            if (!_offlineCandidateCache.count(minLvl))
                return; // Re-evaluate the raid after the asynchronous snapshot is available.
            uint32 need = desired - static_cast<uint32>(responders.size());
            need = std::min<uint32>(need, _reactiveMaxConcurrentLogins);
            if (offline.size() > need)
                offline.resize(need);
            for (BotCandidate const& bot : offline)
            {
                responders.push_back(bot);
                pendingLogins.push_back(bot.GuidLow);
            }
        }

        if (responders.empty())
            return;

        PendingRaidResponse pending;
        pending.ResponseId = _nextResponseId++;
        pending.TriggerGuidLow = target->GuidLow;
        pending.ResponseTeam = target->ResponseTeam;
        pending.MapId = target->MapId;
        pending.TargetX = target->X;
        pending.TargetY = target->Y;
        pending.TargetZ = target->Z;
        pending.TargetO = target->O;
        pending.StartAt = now + _reactiveLoginDelaySeconds;
        pending.Deadline = now + _reactiveLoginTimeoutSeconds;
        pending.State = ResponseState::Reserved;
        pending.Bots = std::move(responders);
        pending.PendingLoginGuids = std::move(pendingLogins);

        std::vector<uint32> admissionGuids;
        for (BotCandidate const& bot : pending.Bots)
            admissionGuids.push_back(bot.GuidLow);
        pending.AdmissionRequestId = PlayerbotsLife::SubmitAdmissionRequest(
            PlayerbotsLife::ReservationOwner::PvPLife, (uint64(1) << 63) | pending.ResponseId,
            admissionGuids, budget, now, pending.Deadline);
        if (!pending.AdmissionRequestId)
            return;
        _pendingResponses.push_back(std::move(pending));
        _lastReactiveResponse = now;

        LOG_INFO("module", "[PvPLife] Queued {} raid response for {} invaders (leader {}).",
            TeamName(target->ResponseTeam), target->GroupCount, target->Name);
        AuditLog("REACTIVE_START", "responseId=" + std::to_string(_pendingResponses.back().ResponseId) +
            " trigger=" + std::to_string(target->GuidLow) +
            " team=" + TeamName(target->ResponseTeam) + " responders=" + std::to_string(_pendingResponses.back().Bots.size()));
    }

    void Manager::CancelPendingRaidResponse(uint64 responseId, std::string const& reason)
    {
        for (auto& pending : _pendingResponses)
        {
            if ((responseId == 0 || pending.ResponseId == responseId) && !pending.Cancelled)
            {
                LOG_INFO("module", "[PvPLife] Cancelled pending raid response #{} (reason: {})", pending.ResponseId, reason);
                for (BotCandidate const& b : pending.Bots)
                {
                    if (b.Token.GuidLow != 0)
                        PlayerbotsLife::ReleaseLeaseExact(const_cast<PlayerbotsLife::LeaseToken&>(b.Token));
                }
                if (pending.AdmissionRequestId)
                    PlayerbotsLife::CancelAdmissionRequest(pending.AdmissionRequestId, PlayerbotsLife::ReservationOwner::PvPLife);
                pending.Bots.clear();
                pending.Cancelled = true;
                if (responseId != 0)
                    break;
            }
        }
        _pendingResponses.erase(std::remove_if(_pendingResponses.begin(), _pendingResponses.end(),
            [](PendingRaidResponse const& p) { return p.Cancelled; }), _pendingResponses.end());
    }

    void Manager::StartPendingRaidResponses()
    {
        uint32 now = GameTimeSeconds();
        for (PendingRaidResponse& pending : _pendingResponses)
        {
            if (pending.Cancelled)
                continue;
            Player* leader = FindPlayer(pending.TriggerGuidLow);
            Group* group = leader ? leader->GetGroup() : nullptr;
            bool validTrigger = leader && IsRealPlayer(leader) && leader->IsInWorld() && leader->IsAlive() &&
                leader->IsPvP() && leader->GetMapId() == pending.MapId && group &&
                group->IsLeader(leader->GetGUID()) && group->GetMembersCount() >= _reactiveMinGroupSize;
            if (!validTrigger || pending.Deadline <= now)
            {
                if (pending.AdmissionRequestId)
                    PlayerbotsLife::CancelAdmissionRequest(pending.AdmissionRequestId, PlayerbotsLife::ReservationOwner::PvPLife);
                for (BotCandidate const& bot : pending.Bots)
                    PlayerbotsLife::ReleaseLeaseExact(bot.Token);
                pending.Cancelled = true;
                continue;
            }
            if (!pending.LeasesGranted || pending.StartAt > now)
                continue;
            bool online = std::all_of(pending.Bots.begin(), pending.Bots.end(), [&](BotCandidate const& bot)
            {
                Player* player = FindPlayer(bot.GuidLow);
                return player && player->IsInWorld() && !player->IsBeingTeleported();
            });
            if (!online)
                continue;
            ActiveEvent event;
            event.EventId = _nextEventId++;
            event.Origin = EventOrigin::ReactiveRaidResponse;
            event.TriggerGuidLow = pending.TriggerGuidLow;
            event.EventZone.Name = "Reactive Defense (" + std::string(TeamName(pending.ResponseTeam)) + ")";
            event.EventZone.MapId = pending.MapId;
            event.EventZone.Type = ActivityType::Skirmish;
            event.EventZone.BotChat = _botChatEnable;
            event.EventZone.TargetX = pending.TargetX;
            event.EventZone.TargetY = pending.TargetY;
            event.EventZone.TargetZ = pending.TargetZ;
            event.EventZone.TargetO = pending.TargetO;
            event.DurationSeconds = _reactiveDurationMinutes * MINUTE;
            uint32 queuedWork = static_cast<uint32>(pending.Bots.size() + _releasingParticipants.size());
            for (ActiveEvent const& queued : _activeEvents)
                if (!queued.Closing)
                    queuedWork += static_cast<uint32>(std::count_if(queued.Members.begin(), queued.Members.end(),
                        [](Participant const& part) { return !part.Deployed; }));
            uint32 batches = (queuedWork + _maxChangesPerTick - 1) / _maxChangesPerTick;
            event.PrepareDeadline = now + std::max<uint32>(60, 2 * _tickSeconds * batches + _arrivalStaggerMax);
            event.EndsAt = event.PrepareDeadline + event.DurationSeconds;
            event.MinimumTotal = 1;
            float angle = pending.TargetO + 3.14159265f;
            uint32 index = 0;
            for (BotCandidate const& bot : pending.Bots)
            {
                Player* player = FindPlayer(bot.GuidLow);
                if (!IsSafeBot(player, true) || IsHumanControlled(player))
                {
                    PlayerbotsLife::ReleaseLeaseExact(bot.Token);
                    continue;
                }
                Participant part;
                part.Bot = bot;
                part.Attacker = true;
                part.Token = bot.Token;
                if (!PlayerbotsLife::PromoteLease(part.Token, event.EventId))
                {
                    PlayerbotsLife::ReleaseLeaseExact(bot.Token);
                    continue;
                }
                float lane = static_cast<float>(static_cast<int32>(index % _reactiveFormationColumns) -
                    static_cast<int32>(_reactiveFormationColumns / 2)) * _reactiveLaneSpacing;
                part.ActivityX = pending.TargetX + std::cos(angle) * _reactiveRallyDistance - std::sin(angle) * lane;
                part.ActivityY = pending.TargetY + std::sin(angle) * _reactiveRallyDistance + std::cos(angle) * lane;
                part.ActivityZ = pending.TargetZ;
                part.ActivityO = angle;
                event.Members.push_back(part);
                ++index;
            }
            pending.Bots.clear();
            pending.Cancelled = true;
            if (!event.Members.empty())
                _activeEvents.push_back(std::move(event));
        }
        _pendingResponses.erase(std::remove_if(_pendingResponses.begin(), _pendingResponses.end(),
            [](PendingRaidResponse const& pending) { return pending.Cancelled; }), _pendingResponses.end());
    }

    void Manager::Announce(std::string const& text) const
    {
        if (!_announce)
            return;
        sWorldSessionMgr->SendServerMessage(SERVER_MSG_STRING, text);
    }

    void Manager::Update(uint32 diff)
    {
        bool managementTick = _timerMs <= diff;
        if (managementTick)
        {
            _timerMs = _tickSeconds * IN_MILLISECONDS;
            _changesThisTick = 0;
        }
        else
            _timerMs -= diff;
        _transactionProcessor.ProcessReadyCallbacks();
        _queryProcessor.ProcessReadyCallbacks();
        PlayerbotsLife::ResolveAdmissionRequests(GameTimeSeconds());
        ProcessReleasingParticipants(); // Works while disabled, reloading, or DB-unavailable.
        if (!_enable || !_databaseReady || _draining)
            return;
        if (_startupElapsedMs < _startupDelaySeconds * IN_MILLISECONDS)
        {
            _startupElapsedMs += diff;
            return;
        }
        ExpireEvents(); // Reject expired work before any movement or combat operation.
        ProcessAdmissionGrants();
        StartPendingRaidResponses();
        ProcessMoveQueue();
        ProcessDuelQueue();
        ProcessEngagementQueue();
        ProcessChatQueue();
        if (_duelGuardTimerMs <= diff)
        {
            _duelGuardTimerMs = _duelGuardIntervalMs;
            MaintainDuelParticipants();
        }
        else
            _duelGuardTimerMs -= diff;
        if (managementTick)
        {
            uint32 nowSec = GameTimeSeconds();
            PlayerbotsLife::ScavengeStaleLeases(nowSec);
            if (nowSec - _lastCooldownPruneTime >= 60)
            {
                _lastCooldownPruneTime = nowSec;
                PruneExpiredCooldowns();
                PlayerbotsLife::PruneRealPlayerCooldowns(nowSec);
            }
            ProcessPreparingEvents();
            TryQueueReactiveRaidResponse();
            MaintainPersistentDuelZones();
            MaintainPersistentWorldPvp();
            TryStartRandomSkirmish();
            TryStartFactionCampaign();
            MaintainBotDuels();
            ProcessRealPlayerChallenges();
        }
    }

    void Manager::PrintStatus(ChatHandler* handler) const
    {
        if (!handler)
            return;

        uint32 startupTarget = _startupDelaySeconds * IN_MILLISECONDS;
        uint32 startupLeft = _startupElapsedMs < startupTarget ?
            (startupTarget - _startupElapsedMs + 999) / 1000 : 0;
        handler->PSendSysMessage("PvP Life: enabled={} DB={} startup delay={}s events={} pendingResponses={} move={} duel={} engage={}",
            _enable ? 1 : 0, _databaseReady ? "ready" : "missing", startupLeft,
            _activeEvents.size(), _pendingResponses.size(), _moveQueue.size(), _duelQueue.size(), _engagementQueue.size());

        uint32 budget = CalculatePopulationBudget();
        uint32 liveBots = GetLiveWorldBotCount();
        handler->PSendSysMessage(
            "Population: budget={} (live bots={}) mode={} borrowPercent={}% maxTotal={} proportionalScaling={} bots: prefix='{}' respectActivity={} minOnlineReq={}",
            budget, liveBots, _budgetMode == BudgetMode::Percentage ? "percentage" : "fixed", _borrowPercent,
            _maxTotal == 0 ? "uncapped" : std::to_string(_maxTotal).c_str(),
            _proportionalZoneScaling ? 1 : 0,
            _botAccountPrefix, _respectPlayerbotActivity ? 1 : 0, _minOnlineRequired);

        handler->PSendSysMessage("Audit: linesWritten={} dropped={} openFailures={} writeFailures={} inQueue={}",
            sPvPLifeAudit.GetLinesWritten(), sPvPLifeAudit.GetDroppedCount(),
            sPvPLifeAudit.GetOpenFailures(), sPvPLifeAudit.GetWriteFailures(),
            sPvPLifeAudit.GetQueueSize());

        PlayerbotsLife::CooperationSnapshot snap = PlayerbotsLife::GetCooperationSnapshot();
        handler->PSendSysMessage("Reservations: total={} city={} pvp={} active={} releasing={} provisional={} duelSlots={} cap={}",
            snap.TotalReserved, snap.CityLifeCount, snap.PvPLifeCount, snap.ActiveCount, snap.ReleasingCount,
            snap.ProvisionalCount, snap.ActiveDuelSlots, snap.TotalReserved);

        uint32 now = GameTimeSeconds();
        for (ActiveEvent const& e : _activeEvents)
        {
            uint32 left = e.EndsAt > now ? e.EndsAt - now : 0;
            handler->PSendSysMessage("#{} {} [{}] origin={} level {}~{} bots={} time left={}m",
                e.EventId, e.EventZone.Name, TypeName(e.EventZone.Type),
                e.Origin == EventOrigin::ReactiveRaidResponse ? "ReactiveDefense" : "Zone",
                e.EventZone.MinLevel, e.EventZone.MaxLevel,
                e.Members.size(), left / MINUTE);
        }

        for (PendingRaidResponse const& p : _pendingResponses)
        {
            uint32 left = p.StartAt > now ? p.StartAt - now : 0;
            handler->PSendSysMessage("[Pending] Reactive Defense team={} triggerGuid={} responders={} startsIn={}s",
                TeamName(p.ResponseTeam), p.TriggerGuidLow, p.Bots.size(), left);
        }
    }

    void Manager::PrintScan(ChatHandler* handler, uint8 minLevel, uint8 maxLevel) const
    {
        if (!handler)
            return;

        uint8 effectiveMin = EffectiveMinLevel(minLevel);
        uint8 effectiveMax = maxLevel;
        if (effectiveMax < effectiveMin)
            effectiveMax = effectiveMin;

        uint32 alliance = 0;
        uint32 horde = 0;
        uint32 total = 0;

        uint32 queryLimit = _botQueryLimit > 0 ? _botQueryLimit : 500;
        QueryResult result = CharacterDatabase.Query(
            "SELECT guid,account,name,level,race,class,online FROM characters "
            "WHERE online=1 AND level BETWEEN {} AND {} ORDER BY level DESC LIMIT {}",
            effectiveMin, effectiveMax, queryLimit);

        if (result)
        {
            do
            {
                Field* f = result->Fetch();
                BotCandidate b;
                b.GuidLow = f[0].Get<uint32>();
                b.AccountId = f[1].Get<uint32>();
                b.Name = f[2].Get<std::string>();
                b.Level = f[3].Get<uint8>();
                b.Race = f[4].Get<uint8>();
                b.Class = f[5].Get<uint8>();
                b.Online = f[6].Get<uint8>() != 0;
                b.Team = TeamForRace(b.Race);

                if (!const_cast<Manager*>(this)->IsConfiguredBotAccount(b.AccountId))
                    continue;
                if (!IsSafeBot(FindPlayer(b.GuidLow)))
                    continue;

                ++total;
                if (b.Team == TeamSide::Alliance)
                    ++alliance;
                else if (b.Team == TeamSide::Horde)
                    ++horde;
            } while (result->NextRow());
        }

        handler->PSendSysMessage("PvP Life scan lvl {}..{} prefix='{}': Alliance={} Horde={} Total={} queryLimit={} globalMin={}.",
            effectiveMin, effectiveMax, _botAccountPrefix, alliance, horde, total, queryLimit, _globalMinLevel);

        std::vector<Zone> spots = const_cast<Manager*>(this)->LoadZones(true);
        if (spots.empty())
        {
            handler->PSendSysMessage("No enabled/cooldown-ready hotspots right now.");
            return;
        }

        std::unordered_set<uint32> exclude;
        uint32 shown = 0;
        for (Zone const& h : spots)
        {
            if (shown >= 12)
                break;
            std::vector<BotCandidate> attackers = const_cast<Manager*>(this)->LoadCandidates(h.AttackerTeam, h.MinLevel, h.MaxLevel, exclude);
            std::vector<BotCandidate> defenders = const_cast<Manager*>(this)->LoadCandidates(h.DefenderTeam, h.MinLevel, h.MaxLevel, exclude);
            handler->PSendSysMessage("{}: {} attackers={} need={}..{} / {} defenders={} need={}..{} lvl={}..{} weight={}",
                h.Name, TeamName(h.AttackerTeam), attackers.size(), h.AttackersMin, h.AttackersMax,
                TeamName(h.DefenderTeam), defenders.size(), h.DefendersMin, h.DefendersMax,
                EffectiveMinLevel(h.MinLevel, h.Type), h.MaxLevel, h.Weight);
            ++shown;
        }
    }

    void Manager::PrintCompat(ChatHandler* handler) const
    {
        if (!handler)
            return;

        uint32 activeFlags = PlayerbotsLife::GetActiveModules();
        bool clActive = (activeFlags & PlayerbotsLife::MODULE_CITY_LIFE) != 0;
        bool pvpActive = (activeFlags & PlayerbotsLife::MODULE_PVP_LIFE) != 0;
        bool artActive = (activeFlags & PlayerbotsLife::MODULE_ARTISANS) != 0;

        handler->PSendSysMessage("=== Life Modules Compatibility & Coexistence ===");
        handler->PSendSysMessage("CityLife: {}", clActive ? "|cff00ff00ACTIVE|r" : "|cffff0000INACTIVE|r");
        handler->PSendSysMessage("PvPLife:  {}", pvpActive ? "|cff00ff00ACTIVE|r" : "|cffff0000INACTIVE|r");
        handler->PSendSysMessage("Artisans: {}", artActive ? "|cff00ff00ACTIVE|r" : "|cffff0000INACTIVE|r");

        handler->PSendSysMessage("Protocol Version: {} | Registry Address: {:p}",
            PlayerbotsLife::GetReservationProtocolVersion(),
            PlayerbotsLife::GetReservationRegistryAddress());
        handler->PSendSysMessage("Exact ownership protection: ALWAYS ENABLED (legacy harmony setting={})", _harmonyEnable);
        handler->PSendSysMessage("Admission is automatic; accounts and existing assignments are not partitioned.");
        handler->PSendSysMessage("Respect Reservations:  {}", _respectCityLifeReservations ? "ENABLED" : "DISABLED");
        handler->PSendSysMessage("Exclude CL Accounts:   {}", _excludeCityLifeAccounts ? "ENABLED" : "DISABLED");
        handler->PSendSysMessage("Hooks Pass-Through:    {}", _independentHookProcessing ? "ENABLED" : "DISABLED");

        PrintReservations(handler);
    }

    void Manager::PrintReservations(ChatHandler* handler) const
    {
        if (!handler)
            return;

        auto snapshot = PlayerbotsLife::GetCooperationSnapshot(GameTimeSeconds());
        handler->PSendSysMessage("Total Reserved Bots: {} (CityLife: {}, PvPLife: {}, Artisans: {})",
            snapshot.TotalReserved, snapshot.CityLifeCount, snapshot.PvPLifeCount, snapshot.ArtisansCount);
        handler->PSendSysMessage("Lease States: Active={} | Provisional={} (stale={}, oldest={}s) | Releasing={} (stale={}, oldest={}s)",
            snapshot.ActiveCount, snapshot.ProvisionalCount, snapshot.StaleProvisionalCount, snapshot.OldestProvisionalAgeSec,
            snapshot.ReleasingCount, snapshot.StaleReleasingCount, snapshot.OldestReleasingAgeSec);
        handler->PSendSysMessage("Admission requests={} unacknowledged grants={} releasing actors={} work used={}/{}",
            snapshot.WaitingAdmissions, snapshot.UnacknowledgedGrants, _releasingParticipants.size(),
            _changesThisTick, _maxChangesPerTick);
    }

    void Manager::PrintDebugStatus(ChatHandler* handler) const
    {
        if (!handler)
            return;

        handler->PSendSysMessage("=== PvPLife Debug Counters ===");
        handler->PSendSysMessage("Active Events: {}", _activeEvents.size());
        handler->PSendSysMessage("Pending Moves: {}", _moveQueue.size());
        handler->PSendSysMessage("Pending Duels: {}", _duelQueue.size());
        handler->PSendSysMessage("Pending Engagements: {}", _engagementQueue.size());
        handler->PSendSysMessage("Pending Chats: {}", _chatQueue.size());
        handler->PSendSysMessage("Pending Raid Responses: {}", _pendingResponses.size());
        handler->PSendSysMessage("Cached Bot Accounts: {}", _botAccountCache.size());

        PlayerbotsLife::CooperationSnapshot snap = PlayerbotsLife::GetCooperationSnapshot();
        handler->PSendSysMessage("Cooperation: Reserved Total={} (City={}, PvP={}) | Leases: Prov={} Active={} Rel={} | DuelSlots={}",
            snap.TotalReserved, snap.CityLifeCount, snap.PvPLifeCount,
            snap.ProvisionalCount, snap.ActiveCount, snap.ReleasingCount, snap.ActiveDuelSlots);
    }

    void Manager::PrintHelp(ChatHandler* handler, bool isWpvp) const
    {
        if (!handler)
            return;
        std::string cmdPrefix = isWpvp ? ".wpvp" : ".pvplife";
        handler->PSendSysMessage("{} commands:", cmdPrefix);
        handler->PSendSysMessage("{} status", cmdPrefix);
        handler->PSendSysMessage("{} scan [minLvl] [maxLvl]", cmdPrefix);
        handler->PSendSysMessage("{} start <zone|spot>", cmdPrefix);
        handler->PSendSysMessage("{} stop <id|all>", cmdPrefix);
        handler->PSendSysMessage("{} compat", cmdPrefix);
        handler->PSendSysMessage("{} reservations", cmdPrefix);
        handler->PSendSysMessage("{} response status | stop <id|all>", cmdPrefix);
        handler->PSendSysMessage("{} zone list", cmdPrefix);
        handler->PSendSysMessage("{} zone create <name> <type> <attacker> <defender> <minLvl> <maxLvl>", cmdPrefix);
        handler->PSendSysMessage("{} zone rally <name> | target <name>   (save GM position)", cmdPrefix);
        handler->PSendSysMessage("{} zone counts <name> <attMin> <attMax> <defMin> <defMax>", cmdPrefix);
        handler->PSendSysMessage("{} zone duration <name> <minM> <maxM>", cmdPrefix);
        handler->PSendSysMessage("{} zone weight <name> <weight> | cooldown <name> <seconds>", cmdPrefix);
        handler->PSendSysMessage("{} zone challenge <name> <0|1> | chat <name> <0|1> | enable <name> <0|1>", cmdPrefix);
        if (isWpvp)
        {
            handler->PSendSysMessage(".wpvp spot list | create | rally | target | counts | duration | enable");
        }
    }

    bool Manager::TryParseUInt32(std::string const& str, uint32& outVal)
    {
        if (str.empty())
            return false;
        char* end = nullptr;
        errno = 0;
        unsigned long val = std::strtoul(str.c_str(), &end, 10);
        if (errno != 0 || end == str.c_str() || *end != '\0' || val > std::numeric_limits<uint32>::max())
            return false;
        outVal = static_cast<uint32>(val);
        return true;
    }

    bool Manager::TryParseUInt64(std::string const& str, uint64& outVal)
    {
        if (str.empty())
            return false;
        char* end = nullptr;
        errno = 0;
        unsigned long long val = std::strtoull(str.c_str(), &end, 10);
        if (errno != 0 || end == str.c_str() || *end != '\0')
            return false;
        outVal = static_cast<uint64>(val);
        return true;
    }

    bool Manager::TryParseFloat(std::string const& str, float& outVal)
    {
        if (str.empty())
            return false;
        char* end = nullptr;
        errno = 0;
        float val = std::strtof(str.c_str(), &end);
        if (errno != 0 || end == str.c_str() || *end != '\0')
            return false;
        outVal = val;
        return true;
    }

    bool Manager::QueueZoneMutation(std::string const& sql)
    {
        if (_pendingZoneWrites >= 32)
        {
            LOG_WARN("module", "[PvPLife] Zone write queue is full; GM edit was not submitted.");
            return false;
        }
        WorldDatabaseTransaction transaction = WorldDatabase.BeginTransaction();
        if (!transaction)
        {
            LOG_ERROR("module", "[PvPLife] Failed to begin database transaction; GM edit was not submitted.");
            return false;
        }
        transaction->Append(sql);
        ++_pendingZoneWrites;
        uint64 generation = _dataGeneration;
        _transactionProcessor.AddCallback(WorldDatabase.AsyncCommitTransaction(transaction)).AfterComplete(
            [this, generation](bool success)
            {
                --_pendingZoneWrites;
                if (!success)
                {
                    LOG_ERROR("module", "[PvPLife] Zone edit transaction failed; cached zones remain unchanged.");
                    return;
                }
                if (generation == _dataGeneration)
                    LoadZoneConfig(); // Refresh only after this write has committed.
            });
        return true;
    }

    bool Manager::HandleZoneCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 2)
        {
            PrintHelp(handler);
            return true;
        }
        std::string action = Lower(args[1]);
        if (action != "list" && _pendingZoneWrites >= 32)
        {
            handler->PSendSysMessage("PvP Life: Zone edit queue is full; retry after pending writes finish.");
            return true;
        }
        if (action == "list")
        {
            QueryResult result = WorldDatabase.Query(ZoneSelectSql("ORDER BY activity_type,name").c_str());
            if (!result)
            {
                handler->PSendSysMessage("PvP Life: No configured zones found.");
                return true;
            }
            do
            {
                Zone z = ReadZone(result->Fetch());
                ApplyZoneConfig(z);
                handler->PSendSysMessage("#{} {} [{}] enabled={} {}->{} level={}~{} pop={}~{} ratio={}~{} / {}~{} cooldown={}s challenge={} chat={}",
                    z.Id, z.Name, TypeName(z.Type), z.Enabled ? 1 : 0, TeamName(z.AttackerTeam), TeamName(z.DefenderTeam),
                    z.MinLevel, z.MaxLevel, z.PopulationMin, z.PopulationMax,
                    z.AttackersMin, z.AttackersMax, z.DefendersMin, z.DefendersMax,
                    z.CooldownSeconds, z.ChallengePlayers ? 1 : 0, z.BotChat ? 1 : 0);
            } while (result->NextRow());
            return true;
        }
        if (action == "create")
        {
            if (args.size() < 8)
            {
                handler->PSendSysMessage("Syntax: .pvplife zone create <name> <type> <attacker> <defender> <minLvl> <maxLvl>");
                return true;
            }
            Player* gm = handler->GetSession() ? handler->GetSession()->GetPlayer() : nullptr;
            if (!gm)
            {
                handler->PSendSysMessage("This command requires an in-game GM position.");
                return true;
            }
            if (!std::isfinite(gm->GetPositionX()) || !std::isfinite(gm->GetPositionY()) || !std::isfinite(gm->GetPositionZ()))
            {
                handler->PSendSysMessage("Invalid GM position coordinates.");
                return true;
            }
            ActivityType type;
            TeamSide attacker, defender;
            if (!ParseType(args[3], type) || !ParseTeam(args[4], attacker) || !ParseTeam(args[5], defender))
            {
                handler->PSendSysMessage("Invalid activity type or faction value.");
                return true;
            }
            std::string name = args[2];
            WorldDatabase.EscapeString(name);
            uint32 minLevelRaw = 0, maxLevelRaw = 0;
            if (!TryParseUInt32(args[6], minLevelRaw) || !TryParseUInt32(args[7], maxLevelRaw))
            {
                handler->PSendSysMessage("Invalid level numbers.");
                return true;
            }
            uint32 minLevel = std::clamp<uint32>(minLevelRaw, 1, 80);
            uint32 maxLevel = std::clamp<uint32>(maxLevelRaw, minLevel, 80);
            bool queued = QueueZoneMutation(Acore::StringFormat(
                "INSERT INTO pvp_life_zone (name,enabled,activity_type,attacker_team,defender_team,min_level,max_level,map_id,"
                "rally_x,rally_y,rally_z,rally_o,target_x,target_y,target_z,target_o) VALUES ('{}',1,{},{},{},{},{},{},{},{},{},{},{},{},{},{}) "
                "ON DUPLICATE KEY UPDATE activity_type=VALUES(activity_type),attacker_team=VALUES(attacker_team),defender_team=VALUES(defender_team),"
                "min_level=VALUES(min_level),max_level=VALUES(max_level)",
                name, static_cast<uint32>(type), static_cast<uint32>(attacker), static_cast<uint32>(defender), minLevel, maxLevel,
                gm->GetMapId(), gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(), gm->GetOrientation(),
                gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(), gm->GetOrientation()));
            if (queued)
                handler->PSendSysMessage("PvP Life: Queued creation/update of {}. Set rally and target after it appears in zone list.", args[2]);
            else
                handler->PSendSysMessage("PvP Life: Failed to queue creation of {}: write queue is full or database unavailable.", args[2]);
            return true;
        }
        if ((action == "rally" || action == "target") && args.size() >= 3)
        {
            Player* gm = handler->GetSession() ? handler->GetSession()->GetPlayer() : nullptr;
            if (!gm)
            {
                handler->PSendSysMessage("This command requires an in-game GM position.");
                return true;
            }
            if (!std::isfinite(gm->GetPositionX()) || !std::isfinite(gm->GetPositionY()) || !std::isfinite(gm->GetPositionZ()))
            {
                handler->PSendSysMessage("Invalid GM position coordinates.");
                return true;
            }
            std::string name = args[2];
            WorldDatabase.EscapeString(name);
            bool queued = false;
            if (action == "rally")
            {
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET map_id={},rally_x={},rally_y={},rally_z={},rally_o={} WHERE name='{}'",
                    gm->GetMapId(), gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(), gm->GetOrientation(), name));
            }
            else
            {
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET map_id={},target_x={},target_y={},target_z={},target_o={} WHERE name='{}'",
                    gm->GetMapId(), gm->GetPositionX(), gm->GetPositionY(), gm->GetPositionZ(), gm->GetOrientation(), name));
            }
            if (queued)
                handler->PSendSysMessage("PvP Life: Queued {} position update for {}.", action, args[2]);
            else
                handler->PSendSysMessage("PvP Life: Failed to queue {} position update for {}: write queue is full or database unavailable.", action, args[2]);
            return true;
        }
        if (action == "counts" && args.size() >= 7)
        {
            std::string name = args[2]; WorldDatabase.EscapeString(name);
            uint32 attMin = 0, attMax = 0, defMin = 0, defMax = 0;
            if (!TryParseUInt32(args[3], attMin) || !TryParseUInt32(args[4], attMax) ||
                !TryParseUInt32(args[5], defMin) || !TryParseUInt32(args[6], defMax))
            {
                handler->PSendSysMessage("Invalid count values.");
                return true;
            }
            bool queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET attackers_min={},attackers_max={},defenders_min={},defenders_max={} WHERE name='{}'",
                attMin, attMax, defMin, defMax, name));
            if (queued)
                handler->PSendSysMessage("PvP Life: Queued counts update for {}.", args[2]);
            else
                handler->PSendSysMessage("PvP Life: Failed to queue counts update for {}: write queue is full or database unavailable.", args[2]);
            return true;
        }
        if (action == "duration" && args.size() >= 5)
        {
            std::string name = args[2]; WorldDatabase.EscapeString(name);
            uint32 durMin = 0, durMax = 0;
            if (!TryParseUInt32(args[3], durMin) || !TryParseUInt32(args[4], durMax))
            {
                handler->PSendSysMessage("Invalid duration values.");
                return true;
            }
            bool queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET duration_min={},duration_max={} WHERE name='{}'",
                durMin, durMax, name));
            if (queued)
                handler->PSendSysMessage("PvP Life: Queued duration update for {}.", args[2]);
            else
                handler->PSendSysMessage("PvP Life: Failed to queue duration update for {}: write queue is full or database unavailable.", args[2]);
            return true;
        }
        if ((action == "weight" || action == "cooldown" || action == "challenge" || action == "chat" || action == "enable") && args.size() >= 4)
        {
            std::string name = args[2]; WorldDatabase.EscapeString(name);
            uint32 value = 0;
            if (!TryParseUInt32(args[3], value))
            {
                handler->PSendSysMessage("Invalid value parameter.");
                return true;
            }
            bool queued = false;
            if (action == "weight")
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET weight={} WHERE name='{}'", value, name));
            else if (action == "cooldown")
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET cooldown_seconds={} WHERE name='{}'", value, name));
            else if (action == "challenge")
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET challenge_players={} WHERE name='{}'", value ? 1 : 0, name));
            else if (action == "chat")
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET bot_chat={} WHERE name='{}'", value ? 1 : 0, name));
            else
                queued = QueueZoneMutation(Acore::StringFormat("UPDATE pvp_life_zone SET enabled={} WHERE name='{}'", value ? 1 : 0, name));

            if (queued)
                handler->PSendSysMessage("PvP Life: Queued {} update for {}.", action, args[2]);
            else
                handler->PSendSysMessage("PvP Life: Failed to queue {} update for {}: write queue is full or database unavailable.", action, args[2]);
            return true;
        }
        PrintHelp(handler);
        return true;
    }

    bool Manager::HandleSpotCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 2)
        {
            PrintHelp(handler, true);
            return true;
        }
        std::string action = Lower(args[1]);
        if (action == "list")
        {
            std::vector<std::string> forwardArgs = { "zone", "list" };
            return HandleZoneCommand(handler, forwardArgs);
        }
        if (action == "create")
        {
            if (args.size() < 7)
            {
                handler->PSendSysMessage("Syntax: .wpvp spot create <name> <attacker> <defender> <minLvl> <maxLvl>");
                return true;
            }
            TeamSide attacker, defender;
            if (!ParseTeam(args[3], attacker) || !ParseTeam(args[4], defender))
            {
                handler->PSendSysMessage("Bad team. Use alliance or horde.");
                return true;
            }
            ActivityType type = (attacker != TeamSide::Any && attacker == defender) ? ActivityType::Duel : ActivityType::Skirmish;
            std::string typeStr = (type == ActivityType::Duel) ? "duel" : "skirmish";
            std::vector<std::string> forwardArgs = { "zone", "create", args[2], typeStr, args[3], args[4], args[5], args[6] };
            return HandleZoneCommand(handler, forwardArgs);
        }
        if (action == "rally" || action == "target" || action == "counts" || action == "duration" ||
            action == "weight" || action == "cooldown" || action == "challenge" || action == "chat" || action == "enable")
        {
            std::vector<std::string> forwardArgs = args;
            forwardArgs[0] = "zone";
            return HandleZoneCommand(handler, forwardArgs);
        }
        PrintHelp(handler, true);
        return true;
    }

    bool Manager::HandleResponseCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 2)
        {
            handler->PSendSysMessage("Syntax: .pvplife response status | stop <id|all>");
            return true;
        }
        std::string sub = Lower(args[1]);
        if (sub == "status")
        {
            handler->PSendSysMessage("=== Reactive Raid Responses ===");
            handler->PSendSysMessage("Pending: {}", _pendingResponses.size());
            uint32 now = GameTimeSeconds();
            for (PendingRaidResponse const& p : _pendingResponses)
            {
                uint32 left = p.StartAt > now ? p.StartAt - now : 0;
                handler->PSendSysMessage("#{} team={} triggerGuid={} responders={} startsIn={}s",
                    p.ResponseId, TeamName(p.ResponseTeam), p.TriggerGuidLow, p.Bots.size(), left);
            }
            return true;
        }
        if (sub == "stop" && args.size() >= 3)
        {
            if (Lower(args[2]) == "all")
            {
                CancelPendingRaidResponse(0, "gm-stop-all");
                handler->PSendSysMessage("PvP Life: Stopped all pending raid responses.");
                return true;
            }
            uint64 id = 0;
            if (!TryParseUInt64(args[2], id))
            {
                handler->PSendSysMessage("Invalid response id.");
                return true;
            }
            CancelPendingRaidResponse(id, "gm-stop");
            handler->PSendSysMessage("PvP Life: Stopped pending response #{}.", id);
            return true;
        }
        handler->PSendSysMessage("Syntax: .pvplife response status | stop <id|all>");
        return true;
    }

    bool Manager::HandleDebugCommand(ChatHandler* handler, std::vector<std::string> const& args)
    {
        if (args.size() < 2)
        {
            PrintDebugStatus(handler);
            return true;
        }
        std::string sub = Lower(args[1]);
        if (sub == "status" || sub == "counters")
        {
            PrintDebugStatus(handler);
            return true;
        }
        if (sub == "validate")
        {
            bool db = VerifyDatabase();
            handler->PSendSysMessage("Database Validation: {}", db ? "OK" : "ERROR");
            PrintReservations(handler);
            return true;
        }
        if (sub == "bot" && args.size() >= 3)
        {
            uint32 guidLow = 0;
            if (!TryParseUInt32(args[2], guidLow))
            {
                Player* p = ObjectAccessor::FindPlayerByName(args[2]);
                if (p)
                    guidLow = p->GetGUID().GetCounter();
            }

            if (!guidLow)
            {
                handler->PSendSysMessage("Bot '{}' not found.", args[2]);
                return true;
            }

            Player* p = FindPlayer(guidLow);
            bool isPart = IsParticipant(guidLow);
            bool isRes = PlayerbotsLife::IsReserved(guidLow);
            handler->PSendSysMessage("Bot guid={}: online={} participant={} reserved={}",
                guidLow, p ? "YES" : "NO", isPart ? "YES" : "NO", isRes ? "YES" : "NO");
            return true;
        }
        PrintDebugStatus(handler);
        return true;
    }

    void Manager::StopEventById(uint64 id, ChatHandler* handler)
    {
        if (id == 0)
        {
            _draining = true;
            CancelPendingRaidResponse(0, "gm-stop");
            for (ActiveEvent& e : _activeEvents)
                EndEvent(e, "gm-stop");
            _activeEvents.clear();
            _moveQueue.clear();
            _duelQueue.clear();
            _engagementQueue.clear();
            _chatQueue.clear();
            _draining = false;
            if (handler)
                handler->PSendSysMessage("PvP Life: Stopped all activities.");
            return;
        }

        bool found = false;
        std::vector<ActiveEvent> keep;
        for (ActiveEvent& e : _activeEvents)
        {
            if (e.EventId == id)
            {
                EndEvent(e, "gm-stop");
                found = true;
            }
            else
                keep.push_back(e);
        }
        _activeEvents.swap(keep);
        _moveQueue.erase(std::remove_if(_moveQueue.begin(), _moveQueue.end(), [id](MoveStep const& s) { return s.EventId == id; }), _moveQueue.end());
        _duelQueue.erase(std::remove_if(_duelQueue.begin(), _duelQueue.end(), [id](DuelStep const& s) { return s.EventId == id; }), _duelQueue.end());
        _engagementQueue.erase(std::remove_if(_engagementQueue.begin(), _engagementQueue.end(), [id](EngagementStep const& s) { return s.EventId == id; }), _engagementQueue.end());
        _chatQueue.erase(std::remove_if(_chatQueue.begin(), _chatQueue.end(), [id](ChatStep const& s) { return s.EventId == id; }), _chatQueue.end());
        if (handler)
            handler->PSendSysMessage("PvP Life: {} #{}.", found ? "stopped" : "did not find", id);
    }

    bool Manager::HandleCommand(ChatHandler* handler, std::string const& text)
    {
        std::vector<std::string> args = Tokenize(text);
        if (!args.empty() && (Lower(args[0]) == ".pvplife" || Lower(args[0]) == "pvplife"))
            args.erase(args.begin());
        if (args.empty() || Lower(args[0]) == "help")
        {
            PrintHelp(handler);
            return true;
        }
        std::string cmd = Lower(args[0]);
        if (cmd == "status")
        {
            PrintStatus(handler);
            return true;
        }
        if (cmd == "scan")
        {
            uint32 minLevelVal = _globalMinLevel;
            uint32 maxLevelVal = 80;
            if (args.size() >= 2 && !TryParseUInt32(args[1], minLevelVal))
                minLevelVal = _globalMinLevel;
            if (args.size() >= 3 && !TryParseUInt32(args[2], maxLevelVal))
                maxLevelVal = 80;
            uint8 minLevel = static_cast<uint8>(std::clamp<uint32>(minLevelVal, 1, 80));
            uint8 maxLevel = static_cast<uint8>(std::clamp<uint32>(maxLevelVal, minLevel, 80));
            PrintScan(handler, minLevel, maxLevel);
            return true;
        }
        if (cmd == "compat")
        {
            PrintCompat(handler);
            return true;
        }
        if (cmd == "reservations")
        {
            PrintReservations(handler);
            return true;
        }
        if (cmd == "reload")
        {
            LoadConfig();
            handler->PSendSysMessage("PvP Life: Configuration and zone definitions reloaded.");
            return true;
        }
        if (cmd == "response")
            return HandleResponseCommand(handler, args);
        if (cmd == "debug")
            return HandleDebugCommand(handler, args);
        if (cmd == "zone" || cmd == "spot")
            return HandleZoneCommand(handler, args);
        if (cmd == "start")
        {
            if (args.size() < 2)
            {
                handler->PSendSysMessage("Syntax: .pvplife start <zone>");
                return true;
            }
            Zone zone;
            if (!LoadZoneByName(args[1], zone))
            {
                handler->PSendSysMessage("PvP Life: Zone '{}' not found.", args[1]);
                return true;
            }
            StartZone(zone, handler, true);
            return true;
        }
        if (cmd == "stop")
        {
            if (args.size() < 2 || Lower(args[1]) == "all")
            {
                StopEventById(0, handler);
                return true;
            }
            uint64 id = 0;
            if (!TryParseUInt64(args[1], id))
            {
                handler->PSendSysMessage("Invalid event id.");
                return true;
            }
            StopEventById(id, handler);
            return true;
        }
        PrintHelp(handler);
        return true;
    }

    bool Manager::HandleWpvpCommand(ChatHandler* handler, std::string const& text)
    {
        std::vector<std::string> args = Tokenize(text);
        if (!args.empty() && (Lower(args[0]) == ".wpvp" || Lower(args[0]) == "wpvp"))
            args.erase(args.begin());
        if (args.empty() || Lower(args[0]) == "help")
        {
            PrintHelp(handler, true);
            return true;
        }
        std::string cmd = Lower(args[0]);
        if (cmd == "status")
        {
            PrintStatus(handler);
            return true;
        }
        if (cmd == "scan")
        {
            uint32 minLevelVal = _globalMinLevel;
            uint32 maxLevelVal = 80;
            if (args.size() >= 2 && !TryParseUInt32(args[1], minLevelVal))
                minLevelVal = _globalMinLevel;
            if (args.size() >= 3 && !TryParseUInt32(args[2], maxLevelVal))
                maxLevelVal = 80;
            uint8 minLevel = static_cast<uint8>(std::clamp<uint32>(minLevelVal, 1, 80));
            uint8 maxLevel = static_cast<uint8>(std::clamp<uint32>(maxLevelVal, minLevel, 80));
            PrintScan(handler, minLevel, maxLevel);
            return true;
        }
        if (cmd == "compat")
        {
            PrintCompat(handler);
            return true;
        }
        if (cmd == "reservations")
        {
            PrintReservations(handler);
            return true;
        }
        if (cmd == "reload")
        {
            LoadConfig();
            handler->PSendSysMessage("PlayerbotWorldPvp: Configuration and spot definitions reloaded.");
            return true;
        }
        if (cmd == "response")
            return HandleResponseCommand(handler, args);
        if (cmd == "debug")
            return HandleDebugCommand(handler, args);
        if (cmd == "spot" || cmd == "zone")
            return HandleSpotCommand(handler, args);
        if (cmd == "start")
        {
            if (args.size() < 2)
            {
                handler->PSendSysMessage("Syntax: .wpvp start <spot>");
                return true;
            }
            Zone zone;
            if (!LoadZoneByName(args[1], zone))
            {
                handler->PSendSysMessage("PlayerbotWorldPvp: Spot '{}' not found.", args[1]);
                return true;
            }
            StartZone(zone, handler, true);
            return true;
        }
        if (cmd == "stop")
        {
            if (args.size() < 2 || Lower(args[1]) == "all")
            {
                StopEventById(0, handler);
                return true;
            }
            uint64 id = 0;
            if (!TryParseUInt64(args[1], id))
            {
                handler->PSendSysMessage("Invalid event id.");
                return true;
            }
            StopEventById(id, handler);
            return true;
        }
        PrintHelp(handler, true);
        return true;
    }

    uint32 Manager::GetActiveParticipantCount() const
    {
        uint32 count = 0;
        for (ActiveEvent const& e : _activeEvents)
            count += static_cast<uint32>(e.Members.size());
        return count;
    }

    static char const* ResolvePvPRole(Participant const& part, ActiveEvent const& e)
    {
        if (e.EventZone.Type == ActivityType::Duel)
            return "Duelist";
        if (part.Attacker)
            return "Assault";
        return "Defense";
    }

    static std::string ResolvePvPAction(Participant const& part, Player* p, ActiveEvent const& e)
    {
        if (p)
        {
            if (!p->IsAlive())
                return "Fallen in Battle";
            if (p->IsBeingTeleported())
                return "Deploying";
        }

        if (e.EventZone.Type == ActivityType::Duel || part.DuelOpponentGuid != 0)
        {
            if (p && p->duel && p->duel->Opponent)
            {
                if (p->duel->State == DUEL_STATE_COUNTDOWN)
                    return "Duel Countdown";
                if (Spell* sp = p->GetCurrentSpell(CURRENT_GENERIC_SPELL))
                    if (sp->GetSpellInfo() && sp->GetSpellInfo()->SpellName[0])
                        return "Casting " + std::string(sp->GetSpellInfo()->SpellName[0]);
                if (Unit* vic = p->GetVictim())
                    return "Attacking " + vic->GetName();
                return "Dueling (" + p->duel->Opponent->GetName() + ")";
            }
            return part.Deployed ? "Dueling" : "Preparing Duel";
        }

        if (p)
        {
            if (p->IsInCombat())
            {
                if (Spell* sp = p->GetCurrentSpell(CURRENT_GENERIC_SPELL))
                    if (sp->GetSpellInfo() && sp->GetSpellInfo()->SpellName[0])
                        return "Casting " + std::string(sp->GetSpellInfo()->SpellName[0]);
                if (Unit* vic = p->GetVictim())
                    return "Attacking " + vic->GetName();
                return "Engaged in Combat";
            }

            if (p->isMoving())
            {
                if (p->IsMounted())
                    return "Mounted Advance";
                return "Advancing on Objective";
            }

            if (p->IsMounted())
                return "Mounted Sentry";
        }

        return part.Attacker ? "Holding Frontline" : "Guarding Objective";
    }

    void Manager::BuildTelemetryRoster(std::vector<std::string>& outRecords) const
    {
        uint32 nowSec = GameTimeSeconds();
        for (ActiveEvent const& e : _activeEvents)
        {
            for (Participant const& part : e.Members)
            {
                ObjectGuid playerGuid = ObjectGuid::Create<HighGuid::Player>(part.Bot.GuidLow);
                char guidBuf[32];
                std::snprintf(guidBuf, sizeof(guidBuf), "0x%016llX", static_cast<unsigned long long>(playerGuid.GetRawValue()));

                std::string name = part.Bot.Name;
                std::string mod = "pvp";
                uint8 classId = part.Bot.Class;
                uint8 level = part.Bot.Level;
                std::string faction = (part.Bot.Team == TeamSide::Alliance) ? "alliance" : "horde";
                float x = part.ActivityX;
                float y = part.ActivityY;
                float z = part.ActivityZ;
                std::string loc = e.EventZone.Name;

                Player* p = ObjectAccessor::FindPlayer(playerGuid);
                if (p)
                {
                    classId = p->getClass();
                    level = p->GetLevel();
                    x = p->GetPositionX();
                    y = p->GetPositionY();
                    z = p->GetPositionZ();
                    if (p->GetTeamId() == TEAM_ALLIANCE)
                        faction = "alliance";
                    else
                        faction = "horde";
                }

                std::string act = "Skirmish";
                if (e.EventZone.Type == ActivityType::Duel) act = "Duel";
                else if (e.EventZone.Type == ActivityType::ForTheHorde) act = "ForTheHorde";
                else if (e.EventZone.Type == ActivityType::ForTheAlliance) act = "ForTheAlliance";

                std::string roleStr = ResolvePvPRole(part, e);
                std::string lastAct = ResolvePvPAction(part, p, e);
                if (lastAct.size() > 32)
                    lastAct = lastAct.substr(0, 32);

                std::string nextT = part.Attacker ? "Assault Objective" : "Defend Zone";
                if (e.EventZone.Type == ActivityType::Duel)
                    nextT = "Duel countdown / combat";

                int32 dueMs = 0;
                if (e.EndsAt > nowSec)
                    dueMs = static_cast<int32>((e.EndsAt - nowSec) * 1000);

                std::string truth = "Observed";
                std::string status = "Active";
                if (p && !p->IsAlive()) status = "Fallen";
                else if (p && p->IsInCombat()) status = "InCombat";
                else if (part.Deployed) status = "Active";
                else status = "Deploying";

                // Format: guid|name|module|classId|level|faction|location|activity|lastAction|nextTask|dueMs|truthClass|status|x|y|z|zone|role
                char rec[512];
                std::snprintf(rec, sizeof(rec), "%s|%s|%s|%u|%u|%s|%s|%s|%s|%s|%d|%s|%s|%.1f|%.1f|%.1f|%s|%s",
                    guidBuf, name.c_str(), mod.c_str(), static_cast<uint32>(classId), static_cast<uint32>(level),
                    faction.c_str(), loc.c_str(), act.c_str(), lastAct.c_str(), nextT.c_str(),
                    dueMs, truth.c_str(), status.c_str(), x, y, z, loc.c_str(), roleStr.c_str());

                outRecords.emplace_back(rec);
            }
        }
    }

    bool Manager::BuildBotDetail(uint32 guidLow, std::string& outPayload) const
    {
        Participant const* foundPart = nullptr;
        ActiveEvent const* foundEvent = nullptr;

        for (ActiveEvent const& e : _activeEvents)
        {
            for (Participant const& part : e.Members)
            {
                if (part.Bot.GuidLow == guidLow)
                {
                    foundPart = &part;
                    foundEvent = &e;
                    break;
                }
            }
            if (foundPart)
                break;
        }

        if (!foundPart || !foundEvent)
            return false;

        Player* player = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(guidLow));
        if (!player)
            return false;

        char guidBuf[32];
        std::snprintf(guidBuf, sizeof(guidBuf), "0x%016llX",
            static_cast<unsigned long long>(player->GetGUID().GetRawValue()));

        std::string role = ResolvePvPRole(*foundPart, *foundEvent);
        std::string action = ResolvePvPAction(*foundPart, player, *foundEvent);

        std::string targetName = "None";
        uint32 targetHp = 100;
        if (Unit* vic = player->GetVictim())
        {
            targetName = vic->GetName();
            targetHp = static_cast<uint32>(vic->GetHealthPct());
        }
        else if (foundPart->DuelOpponentGuid != 0)
        {
            if (Player* opp = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(foundPart->DuelOpponentGuid)))
            {
                targetName = opp->GetName();
                targetHp = static_cast<uint32>(opp->GetHealthPct());
            }
        }

        std::string spellName = "None";
        if (Spell* sp = player->GetCurrentSpell(CURRENT_GENERIC_SPELL))
            if (sp->GetSpellInfo() && sp->GetSpellInfo()->SpellName[0])
                spellName = sp->GetSpellInfo()->SpellName[0];

        std::string strategies = "None";
        std::string lastActions = "None";
        if (PlayerbotAI* ai = GET_PLAYERBOT_AI(player))
        {
            strategies = ai->HandleRemoteCommand("strategy");
            if (strategies.empty())
                strategies = "None";

            lastActions = ai->HandleRemoteCommand("action");
            if (lastActions.empty())
                lastActions = "None";
        }

        // Format: guid|role|action|targetName|targetHp|spellName|strategies|lastAction
        char buf[1024];
        std::snprintf(buf, sizeof(buf), "%s|%s|%s|%s|%u|%s|%s|%s",
            guidBuf, role.c_str(), action.c_str(), targetName.c_str(), targetHp,
            spellName.c_str(), strategies.c_str(), lastActions.c_str());

        outPayload = buf;
        return true;
    }

    void Manager::BuildTelemetryZones(std::string& outPayload) const
    {
        outPayload.clear();
        uint32 now = GameTimeSeconds();
        for (Zone const& z : _zoneCache)
        {
            if (!z.Enabled) continue;
            std::string actType = "Skirmish";
            if (z.Type == ActivityType::Duel) actType = "Duel";
            else if (z.Type == ActivityType::ForTheHorde) actType = "ForTheHorde";
            else if (z.Type == ActivityType::ForTheAlliance) actType = "ForTheAlliance";

            uint32 cd = 0;
            if (z.LastStart + z.CooldownSeconds > now)
                cd = (z.LastStart + z.CooldownSeconds) - now;

            uint32 actAll = 0, actHorde = 0;
            for (ActiveEvent const& e : _activeEvents)
            {
                if (e.EventZone.Id == z.Id)
                {
                    for (Participant const& p : e.Members)
                    {
                        if (p.Bot.Team == TeamSide::Alliance) ++actAll;
                        else ++actHorde;
                    }
                }
            }

            char line[256];
            std::snprintf(line, sizeof(line), "%u|%s|%s|%u|%u|%u|%u|%u\n",
                z.Id, z.Name.c_str(), actType.c_str(), static_cast<uint32>(z.MinLevel),
                static_cast<uint32>(z.MaxLevel), actAll, actHorde, cd);
            outPayload += line;
        }
    }

    void Manager::BuildTelemetryQueues(std::string& outPayload) const
    {
        outPayload.clear();
        uint32 now = GameTimeSeconds();
        uint32 taskId = 1;
        for (MoveStep const& m : _moveQueue)
        {
            int32 due = (m.ExecuteAt > now) ? static_cast<int32>((m.ExecuteAt - now) * 1000) : 0;
            char line[256];
            std::snprintf(line, sizeof(line), "%u|move|%s|Move to Objective|%d|Queued\n", taskId++, m.Name.c_str(), due);
            outPayload += line;
            if (taskId > 20) break;
        }
        for (DuelStep const& d : _duelQueue)
        {
            int32 due = (d.ExecuteAt > now) ? static_cast<int32>((d.ExecuteAt - now) * 1000) : 0;
            char line[256];
            std::snprintf(line, sizeof(line), "%u|duel|%s|Duel %s|%d|Deadline\n", taskId++, d.ChallengerName.c_str(), d.TargetName.c_str(), due);
            outPayload += line;
            if (taskId > 35) break;
        }
        for (EngagementStep const& eng : _engagementQueue)
        {
            int32 due = (eng.ExecuteAt > now) ? static_cast<int32>((eng.ExecuteAt - now) * 1000) : 0;
            std::string aName = "Bot";
            if (Player* p = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(eng.BotGuidLow)))
                aName = p->GetName();
            char line[256];
            std::snprintf(line, sizeof(line), "%u|engage|%s|Engage Enemy|%d|Observed\n", taskId++, aName.c_str(), due);
            outPayload += line;
            if (taskId > 50) break;
        }
    }
}
