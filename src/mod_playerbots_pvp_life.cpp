/*
 * PvP Life
 * Copyright (C) 2026 iCore
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "PvPLifeMgr.h"
#include "LifeBotReservation.h"

#include "Chat.h"
#include "CommandScript.h"
#include "ObjectAccessor.h"
#include "Player.h"
#include "Playerbots.h"
#include "PlayerScript.h"
#include "ScriptMgr.h"
#include "WorldScript.h"

using namespace Acore::ChatCommands;

class PvPLifeWorldScript : public WorldScript
{
public:
    PvPLifeWorldScript()
        : WorldScript("PvPLifeWorldScript", { WORLDHOOK_ON_AFTER_CONFIG_LOAD, WORLDHOOK_ON_UPDATE, WORLDHOOK_ON_SHUTDOWN })
    {
    }

    void OnAfterConfigLoad(bool /*reload*/) override
    {
        sPvPLifeMgr.LoadConfig();
    }

    void OnUpdate(uint32 diff) override
    {
        sPvPLifeMgr.Update(diff);
    }

    void OnShutdown() override
    {
        sPvPLifeMgr.Shutdown();
        PlayerbotsLife::UnregisterActiveModule(PlayerbotsLife::MODULE_PVP_LIFE);
    }
};

#include "Group.h"
#include "GroupScript.h"

class PvPLifePlayerScript : public PlayerScript
{
public:
    PvPLifePlayerScript()
        : PlayerScript("PvPLifePlayerScript", { PLAYERHOOK_ON_LOGOUT })
    {
    }

    void OnPlayerLogout(Player* player) override
    {
        if (player)
            sPvPLifeMgr.OnPlayerLogout(player->GetGUID().GetCounter());
    }
};

class PvPLifeGroupScript : public GroupScript
{
public:
    PvPLifeGroupScript()
        : GroupScript("PvPLifeGroupScript", { GROUPHOOK_ON_ADD_MEMBER })
    {
    }

    void OnAddMember(Group* group, ObjectGuid guid) override
    {
        if (!group)
            return;

        bool hasRealPlayer = false;
        for (GroupReference const* ref = group->GetFirstMember(); ref != nullptr; ref = ref->next())
        {
            Player* member = ref->GetSource();
            if (member && member->GetSession() && !GET_PLAYERBOT_AI(member))
            {
                hasRealPlayer = true;
                break;
            }
        }

        if (hasRealPlayer)
        {
            sPvPLifeMgr.OnAddGroupMember(guid.GetCounter());
            for (GroupReference const* ref = group->GetFirstMember(); ref != nullptr; ref = ref->next())
            {
                Player* member = ref->GetSource();
                if (member && member->GetSession() && GET_PLAYERBOT_AI(member))
                    sPvPLifeMgr.OnAddGroupMember(member->GetGUID().GetCounter());
            }
        }
    }
};

class PvPLifeCommandScript : public CommandScript
{
public:
    PvPLifeCommandScript() : CommandScript("PvPLifeCommandScript") { }

    ChatCommandTable GetCommands() const override
    {
        static ChatCommandTable commandTable =
        {
            { "pvplife", HandlePvPLifeCommand, SEC_GAMEMASTER, Console::Yes },
            { "wpvp",    HandleWpvpCommand,    SEC_GAMEMASTER, Console::Yes }
        };
        return commandTable;
    }

    static bool HandlePvPLifeCommand(ChatHandler* handler, char const* args)
    {
        return sPvPLifeMgr.HandleCommand(handler, args ? args : "");
    }

    static bool HandleWpvpCommand(ChatHandler* handler, char const* args)
    {
        return sPvPLifeMgr.HandleWpvpCommand(handler, args ? args : "");
    }
};

void AddPvPLifeScripts()
{
    static_assert(PlayerbotsLife::LIFE_BOT_RESERVATION_PROTOCOL_VERSION == 2026101104,
        "PvP Life requires LifeBotReservation protocol version 2026101104");

    PlayerbotsLife::RegisterActiveModule(PlayerbotsLife::MODULE_PVP_LIFE);
    new PvPLifeWorldScript();
    new PvPLifePlayerScript();
    new PvPLifeGroupScript();
    new PvPLifeCommandScript();
    LOG_INFO("server.loading", ">> Loaded mod-playerbots-pvp-life (protocol={}, registry={:p})",
        PlayerbotsLife::GetReservationProtocolVersion(), PlayerbotsLife::GetReservationRegistryAddress());
}
