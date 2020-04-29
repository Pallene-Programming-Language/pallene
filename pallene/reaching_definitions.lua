-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local ir = require "pallene.ir"
local location = require "pallene.location"
local Set = require "pallene.set"
local CFG = require "pallene.cfg"
--[[
local inspect = require "inspect"
ppi = function(t,f) return inspect(t,{newline='',process=f}) end
pp = function(t,f) return inspect(t,{process=f}) end
--]]
--TODO: 
-- separate data-flow from reaching definitions
-- change table operations for Set operations where applicable

local RD = {}


-- start definitions  -------------

local function find_defs_uses(cfg,index,df)
    --  TODO: bb has only one statement
    local node = cfg[index] and cfg[index].cmd 
    if not node or type(node) ~= 'table' then return end
    for _, v_id in ipairs(ir.get_dsts(node)) do
        table.insert(df.definitions,{
            cmd = node,
            bb = index,
            loc = node.loc,
            var = v_id
           })
        if not df.vars[v_id] then
            df.vars[v_id] = {defs={},uses={},loc=node.loc}
        end
        local new_def = #df.definitions
        table.insert(df.vars[v_id].defs,new_def)
        for _, val in ipairs(ir.get_srcs(node)) do
            if val._tag == "ir.Value.LocalVar" then
                df.definitions[new_def].value = val.id
                if not df.vars[val.id] then
                    df.vars[val.id] = {defs={},uses={}}
                end
                table.insert(df.vars[val.id].uses,new_def)
            end
        end
    end
    for _, val in ipairs(ir.get_srcs(node)) do
        if val._tag == "ir.Value.LocalVar" then
            table.insert(df.uses,{
                cmd = node,
                var = val.id,
                bb = index,
            })
        end
    end
end
-- end   definitions  -------------
-- start gen/kill  -------------

local function find_gen_kill(cfg,index,df)
    -- normal nodes have number indexes, entry and exit nodes have string indexes
    if type(index) ~= 'number' then return end
    local node = cfg[index] and cfg[index].cmd --  TODO: bb has only one statement
    assert(node,'no node at index '..index)
    df.GEN[index] = {}
    df.KILL[index] = {}
    for _, v_id in ipairs(ir.get_dsts(node)) do
        df.KILL[index] = Set.union(df.KILL[index],Set.copy(df.vars[v_id].defs))
    end
    for _, _ in ipairs(ir.get_srcs(node)) do
        local thisdef = nil
        for k,v in ipairs(df.definitions) do
            if v.cmd == node then
                thisdef = k
            end
        end
        df.GEN[index] = {thisdef}
    end
end
-- end   gen/kill  -------------
-- start in/out    -------------
local function Upred(graph,index,out)
    local ret = {}
    for _,pred in pairs(graph[index].from) do
        ret = Set.union(ret,out[pred])
    end
    return ret
end
local function find_in_out(cfg,df)
    for k,_ in pairs(cfg) do
        df.IN[k] = {}
        df.OUT[k] = {}
    end
    df.OUT[1] = {} -- RD
    local change = true
    while change do
        change = false
        for k,_ in ipairs(cfg) do
            df.IN[k] = Upred(cfg,k,df.OUT) --RD
            local oldOUT = df.OUT[k]
            --OUT[k] = (IN[K] - kill[K]) + gen[K] --RD
            df.OUT[k] = Set.union(Set.difference(df.IN[k],df.KILL[k]),df.GEN[k])
            --if oldOUT ~= OUT[k] then 
            if not Set.equal(oldOUT, df.OUT[k]) then
                change = true
            end
        end
    end
end
-- end   in/out    -------------
-- start analyses  -------------

-- variable not declared:
-- if a use of a variable doesn't reach any of its definitions, it is undeclared
local function undeclared_unused_vars(df)
    -- trivial cases
    for k,v in pairs(df.vars) do
        if Set.equal(v.defs,{}) then
            df.undeclared[k] = v.loc
        end
        if Set.equal(v.uses,{}) then
            df.unused[k] = v.loc
        end
    end
    local unused = Set.difference(df.OUT[#df.OUT],df.IN[#df.IN])
    for _,v in ipairs(unused) do
        df.unused[df.definitions[v].var] = df.definitions[v].loc
        --print(df.definitions[v].var, 'unused on bb',df.definitions[v].bb)
    end
end
-- shadowing:
-- if a definition reaches another definition
--    if the last OUT doesnt contain all the defs, the difference was shadowed
local function shadowing(df)
      local temp = Set.copy(df.OUT[#df.OUT])
      table.sort(temp)
      local t2 = {}
      for i=1,#temp do
        table.insert(t2,i)
      end
      local t3 = Set.difference(t2,temp)
      for _,v in ipairs(t3) do
        df.shadowed[df.definitions[v].var] = df.definitions[v].loc
      end
end
-- end   analyses  -------------

function RD.run(module)

    local errors = {}
    for _, func in ipairs(module.functions) do
        local cfg = CFG.new(func.body)        
        -- if the graph is not empty
        if cfg[1] then
            local df = {}
            df.unreachable = CFG.unreachable(cfg)
            for k,_ in pairs(df.unreachable) do
                if k == true then 
                    if func.loc then
                        table.insert(errors, location.format_error(func.loc,'unreachable code, possible infite loop'))
                    else
                        -- TODO: when does this happen?
                        table.insert(errors, 'unreachable code, possible infite loop')
                    end
                else
                    table.insert(errors, location.format_error(k,'unreachable code'))
                end
            end
            df.vars = {}
            df.uses = {}
            df.definitions = {}
            CFG.traverse_forward(cfg,function(cfg_,index) -- RD
                find_defs_uses(cfg_,index,df)
            end)
            -- print('vars defs/uses')
            -- for k,v in pairs(df.vars) do
            --     print(k,ppi(v.defs),ppi(v.uses))
            -- end
            -- print('defs')
            -- for k,v in pairs(df.definitions) do
            --     print(k,v.var, v.bb)
            -- end

            -- print('uses')
            -- for k,v in pairs(df.uses) do
            --     print(k,v.var, v.bb)
            -- end
            df.GEN = {}
            df.KILL = {}
            CFG.traverse_forward(cfg,function(cfg_,index) -- RD
                find_gen_kill(cfg_,index,df)
            end)
            -- check if all the nodes have GEN/KILL 
            -- traverse_forward may show false positives (not visiting nodes that should have GEN/KILL)
            for k,_ in ipairs(cfg) do
                assert(type(df.GEN[k])=='table','no GEN at '..k)
                assert(type(df.KILL[k])=='table','no KILL at '..k)
            end
            -- print('gen/kill')
            -- for k,_ in pairs(CFG) do
            --     print(k,ppi(df.GEN[k]),ppi(df.KILL[k]))
            -- end
            df.IN = {}
            df.OUT = {}
            find_in_out(cfg,df)
            -- print('IN/OUT')
            -- for k,_ in pairs(CFG) do
            --     print(k, ppi(df.IN[k]),ppi(df.OUT[k]))
            -- end
            df.unused = {}
            df.undeclared = {}
            undeclared_unused_vars(df)
            for k,v in pairs(df.unused) do
                if func.vars[k].name and not (func.vars[k].name == "ret1") then
                    table.insert(errors, location.format_error(v,func.vars[k].name..' unused'))
                end
            end
            for k,v in pairs(df.undeclared) do
                table.insert(errors, location.format_error(v,func.vars[k].name..' undeclared'))
            end
            df.shadowed = {}
            shadowing(df)
            for k,v in pairs(df.shadowed) do
                if func.vars[k].name and not (func.vars[k].name == "ret1") then
                    table.insert(errors, location.format_error(v,func.vars[k].name..' is shadowed'))
                end
            end
        end
    end
-- supressing errors for now
--[[
    if #errors == 0 then
        return module, {}
    else
        return false, errors
    end
--]]
    return module, {}
end

return RD


