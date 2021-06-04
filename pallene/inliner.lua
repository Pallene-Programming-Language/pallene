-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local ir = require "pallene.ir"
local util = require "pallene.util"
local inliner = {}

local inspect = require'inspect'


-- receives a local variable reference or a local variable id
-- and creates a variable in the function structure
-- if there isn't one already in the given id
local function maybe_create_var(var,typ,func)
    assert(typ)
    assert(var)
    if type(var) == "table" then
        if var._tag == "ir.Value.LocalVar" then
            if not func.vars[var.id] then
                func.vars[var.id] = ir.VarDecl(false, typ)
            -- else check if expected type?
            end
        elseif var._tag == "ir.Value.Integer" then
        elseif var._tag == "ir.Value.Bool" then
        elseif var._tag == "ir.Value.Nil" then
        elseif var._tag == "ir.Value.Float" then
        elseif var._tag == "ir.Value.String" then
        elseif var._tag == "ir.Value.Function" then
        else
            assert(false,'not treated '..inspect(var))
        end
    elseif type(var) == "number" then
        if not func.vars[var] then
            func.vars[var] = ir.VarDecl(false, typ)
        -- else check if expected type?
        end
    else
        assert(false,'not treated '..inspect(var))
    end

end

-- return moves corresponding to each argument as they where at the beginning of the inner scope
local function args_to_moves(args, cmd, top,func)
    local arguments = {}
    for k, arg in ipairs(args) do
        -- we can just use the srcs from the call (the arguments) on the rhs of the "move" commands
        -- at the same time, it is also convenient to adjust the dst (lhs) of the "move"
        -- to values that will not collide with the outer scope (adding top)
        -- see ir.lua "Function variables" for more details
        -- for example,
        --      x5 = f(x2,x3) -- with srcs = {2,3} and args = {5}
        --      in a function with a total of 9 variables (top = 9)
        -- would be translated to
        --      x(9+1) = x2
        --      x(9+2) = x3
        --      ...
        -- so the new variables will not collide with any of the variables already present in the outer scope
        -- it also have the nice property of being sequential to top

        maybe_create_var(k+top,            arg,func)
        maybe_create_var(cmd.srcs[k],arg,func)
        table.insert(arguments, ir.Cmd.Move(cmd.loc, k+top, cmd.srcs[k]))
    end
    return ir.Cmd.Seq(arguments)
end

-- changes the called function (a copy preferably) in place.
-- each return is turned into a sequence of moves.
local function return_to_moves(called, cmd,func,calledf)
        return ir.map_cmd(called, function (_cmd,inside_loop)

            if _cmd._tag == "ir.Cmd.Return" then
                local moves = {}
                for k=#_cmd.srcs,1,-1 do
                    local v = _cmd.srcs[k]
                    -- if the function call will put the results into a, b, c
                    -- and the called returns x, y, z
                    -- this creates moves corresponding to x = a, y = b and z = c
                    -- in reverse order (see execution_tests/assign_same_var_1)

                    maybe_create_var(cmd.dsts[k],calledf.typ.ret_types[k],func)
                    maybe_create_var(v          ,calledf.typ.ret_types[k],func)
                    table.insert(moves, ir.Cmd.Move(_cmd.loc, cmd.dsts[k], v))
                end
                if inside_loop then
                    table.insert(moves,ir.Cmd.Break())
                end
                return ir.Cmd.Seq(moves)
            end
        end)

end


-- find_top finds the highest variable index in the "cmd" subtree
-- this probably should use map_val
local function find_top(cmd)
    local top = 0
    local function change_top(val)
        if val > top then top = val end
    end
    local function findtop_localvar(val)
        if val._tag == 'ir.Value.LocalVar' then
            change_top(val.id)
        end
    end
    local function findtop(_cmd)
        if _cmd._tag == "ir.Cmd.Binop" then
            change_top(_cmd.dst)
            findtop_localvar(_cmd.src1)
            findtop_localvar(_cmd.src2)
            return _cmd
        end
        if _cmd._tag == "ir.Cmd.Move" then
            change_top(_cmd.dst)
            return _cmd
        end
        if _cmd._tag == "ir.Cmd.Return" then

            for _, value in pairs(_cmd.srcs) do
                findtop_localvar(value)
            end
            return _cmd
        end
    end
    ir.map_cmd(cmd, findtop)
    return top
end


-- auxiliary function to transform values
-- it should have one case for each constructor in ir.ir_cmd_constructors
-- maybe this should be on ir.lua
local function map_val(cmd, fval, flocalval)
    return ir.map_cmd(cmd, function (_cmd)
        if _cmd._tag == "ir.Cmd.Move" then
            _cmd.src = flocalval(_cmd.src)
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.GetGlobal" then
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.SetGlobal" then
            _cmd.src = flocalval(_cmd.src)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Unop" then
            _cmd.src = flocalval(_cmd.src)
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Binop" then
            _cmd.dst = fval(_cmd.dst)
            _cmd.src1 = flocalval(_cmd.src1)
            _cmd.src2 = flocalval(_cmd.src2)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Concat" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.ToFloat" then
            _cmd.dst = fval(_cmd.dst)
            _cmd.src = flocalval(_cmd.src)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.ToDyn" then
            _cmd.dst = fval(_cmd.dst)
            _cmd.src = flocalval(_cmd.src)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.FromDyn" then
            _cmd.src = flocalval(_cmd.src)
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.IsTruthy" then
            _cmd.src = flocalval(_cmd.src)
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.NewArr" then
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.GetArr" then
            _cmd.src_arr = flocalval(_cmd.src_arr )
            _cmd.src_i   = flocalval(_cmd.src_i   )
            _cmd.dst     =      fval(_cmd.dst     )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.SetArr" then
            _cmd.src_arr = flocalval(_cmd.src_arr )
            _cmd.src_i   = flocalval(_cmd.src_i   )
            _cmd.src_v   = flocalval(_cmd.src_v   )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.NewTable" then
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.GetTable" then
            _cmd.src_tab = flocalval(_cmd.src_tab )
            _cmd.src_k   = flocalval(_cmd.src_k   )
            _cmd.dst     =      fval(_cmd.dst     )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.SetTable" then
            _cmd.src_tab = flocalval(_cmd.src_tab )
            _cmd.src_k   = flocalval(_cmd.src_k   )
            _cmd.src_v   = flocalval(_cmd.src_v   )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.NewRecord" then
            _cmd.dst = fval(_cmd.dst)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.GetField" then
            _cmd.src_rec = flocalval(_cmd.src_rec )
            _cmd.field_name   = fval(_cmd.field_name   )
            _cmd.dst     =      fval(_cmd.dst     )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.SetField" then
            _cmd.src_rec = flocalval(_cmd.src_rec )
            _cmd.field_name   = fval(_cmd.field_name   )
            _cmd.src_v   = flocalval(_cmd.src_v   )
            return _cmd
        elseif _cmd._tag == "ir.Cmd.CallStatic" then
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.CallDyn" then
            _cmd.src_f = flocalval(_cmd.src_f )
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
        elseif _cmd._tag == "ir.Cmd.BuiltinIoWrite" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
        elseif _cmd._tag == "ir.Cmd.BuiltinMathSqrt" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.BuiltinStringChar" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.BuiltinStringSub" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.BuiltinType" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.BuiltinTostring" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            for key, value in pairs(_cmd.dsts) do
                _cmd.dsts[key] = fval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Nop" then
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Seq" then
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Return" then
            for key, value in pairs(_cmd.srcs) do
                _cmd.srcs[key] = flocalval(value)
            end
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Break" then
            return _cmd
        elseif _cmd._tag == "ir.Cmd.Loop" then
            return _cmd
        elseif _cmd._tag == "ir.Cmd.If" then
            _cmd.condition = flocalval(_cmd.condition)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.For" then
            _cmd.loop_var = fval(_cmd.loop_var)
            _cmd.step = flocalval(_cmd.step)
            _cmd.start = flocalval(_cmd.start)
            _cmd.limit = flocalval(_cmd.limit)
            return _cmd
        elseif _cmd._tag == "ir.Cmd.CheckGC" then
            return _cmd
        else
            assert(false,'not treated '.._cmd._tag)
        end
    end)
end

-- adjusts the function body to be inlined in respect to the outer function top
-- so the internal variables will not collide with the outer ones
local function inline_body(cmd, top,func,called)
    local function maybe_create(id,last_id)
        assert(called.vars[last_id],last_id)
        maybe_create_var(id,called.vars[last_id].typ,func)
    end
    local new_val = function(val)
        maybe_create(top+val,val)
        return top+val
    end
    local iflocalvar_new_val = function (val)
        if type(val) == 'number' then
            local tmp = new_val(val)
            maybe_create(tmp,val)
            val = tmp
        elseif val._tag == 'ir.Value.LocalVar' then
            local tmp = new_val(val.id)
            maybe_create(tmp,val.id)
            val.id = tmp
        end
        return val
    end
    return map_val(cmd, new_val, iflocalvar_new_val)
end

-- normal_form guarantess that the cmd subtree will be in normal form:
-- starting at the number of arguments+1
-- and every value is increased in order of appearance,
-- without holes
local function normal_form(cmd,num_args)
    local ids = {}
    ids.top = num_args+1
    local new_val = function(val)
        -- val can be string or int
        if type(val) == 'number' and val > num_args then
            if not ids[val] then
                ids[val] = ids.top
                ids.top = ids.top + 1
            end
            return ids[val]
        else
            return val
        end
    end

    local iflocalvar_new_val = function (val)
        if val._tag == "ir.Value.LocalVar" then
            if val.id > num_args then
                local tmp = new_val(val.id)
                val.id = tmp
            end
        elseif val._tag == "ir.Value.Integer" then
        elseif val._tag == "ir.Value.Float" then
        elseif val._tag == "ir.Value.Bool" then
        elseif val._tag == "ir.Value.Nil" then
        elseif val._tag == "ir.Value.String" then
        elseif val._tag == "ir.Value.Function" then
        else
            assert(false, 'not treated '..val._tag)
        end
        return val
    end

    return map_val(cmd, new_val, iflocalvar_new_val),ids
end

-- transform a whole module into normal form
-- now used just for testing purposes
function inliner.to_normal_module(module)
    for _, func in ipairs(module.functions) do
        local new_body, vars_map = normal_form(func.body,#func.typ.arg_types)
        func.body = new_body
        local new_vars = {}
        for k,v in pairs(vars_map) do
            new_vars[v] = func.vars[k]
        end
        for k,v in pairs(new_vars) do
            func.vars[k] = v
        end
    end
    return module
end

-- only inline first level calls.
-- inlines in order of appearance (maybe should mount a dependency tree)
function inliner.inline(module)

    local errors = {}
    for k, func in ipairs(module.functions) do
        module.functions[k].body = ir.map_cmd(func.body, function(cmd)
            if cmd._tag == "ir.Cmd.CallStatic" then
                -- top is the highest variable present in the host function
                -- it should be recalculated every time,
                -- since a previous inline could have altered it
                local top = find_top(func.body)+1
                local called = util.copy(module.functions[cmd.f_id])

                local args = args_to_moves(called.typ.arg_types, cmd, top, func)
                local body = inline_body(called.body, top, func, called)
                local rets = return_to_moves(body, cmd, func, called)
                return ir.Cmd.Seq({args, rets})
            end
        end)
        -- check consistency
        -- (for each command, it will print [x,y] indicating that the variables at x or y were not declared properly)
        --local flat_cmds = ir.flatten_cmd(module.functions[k].body)
    --     for i, cmd in ipairs(flat_cmds) do
    --         local st = cmd._tag..' ['
    --         for _, val in ipairs(ir.get_srcs(cmd)) do
    --             if type(val) == 'table' and val._tag == "ir.Value.LocalVar" then
    --                 local v_id = val.id
    --                 if not module.functions[k].vars[v_id] then
    --                     st = st .. (v_id)
    --                     found = true
    --                 end
    --             end
    --         end
    --         st = st .. (',')
    --         for _, v_id in ipairs(ir.get_dsts(cmd)) do
    --             if not module.functions[k].vars[v_id] then
    --                 st = st .. (v_id)
    --                 found = true
    --             end
    --         end
    --         st = st .. (']')
    --         print(st)
    --     end
    --     print('======')
    end

    module = inliner.to_normal_module(module)
    if #errors == 0 then
        return module, {}
    else
        return false, errors
    end
end

return inliner


