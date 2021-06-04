-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local ir = require "pallene.ir"
local typedecl = require "pallene.typedecl"

local uninitialized = {}

-- B <- A
local function copy(A)
    local B = {}
    for v, _ in pairs(A) do
        B[v] = true
    end
    return B
end

-- A <- A ∪ B
local function merge(A, B)
    for v, _ in pairs(B) do
        A[v] = true
    end
end

local function new_loop()
    return { is_infinite = true, uninit = {} }
end

-- This function detects when variables are used before being initialized, and when control flows to
-- the end of a non-void function without returning. The analysis is fundamentally a dataflow one,
-- but we exploit the structured control flow to finish it into a single pass. In the end it sort of
-- looks like an abstract interpretation. The analysis assumes that both branches of an if statement
-- can be taken. Make sure that you call ir.clean first, so that it does the right thing in the
-- presence of `while true` loops.
--
-- `uninit` is the set of variables that are potentially uninitialized just before the command
-- executes. We take the liberty of mutating this set in-place, so make a copy beforehand if you
-- need to.
--
-- If we are inside a loop, `loop` models what will happen once we break out of the loop.
-- `loop.is_infinite` is true if think the loop will surely loop forever. `loop.uninit` is the set
-- of potentially uninitialized variables after the loop.
--
-- If the execution can possibly fall through to the next command, returns `true` and the updated
-- set of uninitialized variables. Returns false if the execution unconditionally jumps or gets
-- stuck in an infinite loop.
--
local function test(cmd, uninit, loop)

    local function check_use(v)
        if uninit[v] then
            coroutine.yield({v = v, cmd = cmd})
        end
    end

    local tag = cmd._tag
    if     tag == "ir.Cmd.Nop" then
        return true, uninit

    elseif tag == "ir.Cmd.Seq" then
        for _, c in ipairs(cmd.cmds) do
            local ft
            ft, uninit = test(c, uninit, loop)
            if not ft then return false end
        end
        return true, uninit

    elseif tag == "ir.Cmd.Break" then
        assert(loop)
        loop.is_infinite = false
        merge(loop.uninit, uninit)
        return false

    elseif tag == "ir.Cmd.If" then
        check_use(cmd.condition)

        local ft1, uninit1 = test(cmd.then_, copy(uninit), loop)
        local ft2, uninit2 = test(cmd.else_,      uninit , loop)

        if ft1 and ft2 then
            merge(uninit1, uninit2)
            return true, uninit1
        elseif ft1 then
            return true, uninit1
        elseif ft2 then
            return true, uninit2
        else
            return false
        end

    elseif tag == "ir.Cmd.Loop" then
        loop = new_loop()
        test(cmd.body, uninit, loop)

        if loop.is_infinite then
            return false
        else
            return true, loop.uninit
        end

    elseif tag == "ir.Cmd.For" then
        check_use(cmd.start)
        check_use(cmd.limit)
        check_use(cmd.step)

        loop = new_loop()
        loop.is_infinite = false
        merge(loop.uninit, uninit)

        uninit[cmd.loop_var] = nil
        test(cmd.body, uninit, loop)

        if loop.is_infinite then
            return false
        else
            return true, loop.uninit
        end

    elseif typedecl.match_tag(cmd._tag, "ir.Cmd") then
        for _, val in ipairs(ir.get_srcs(cmd)) do
            if val._tag == "ir.Value.LocalVar" then
                check_use(val.id)
            end
        end
        for _, v_id in ipairs(ir.get_dsts(cmd)) do
            uninit[v_id] = nil
        end

        if tag == "ir.Cmd.Return" then
            return false
        else
            return true, uninit
        end
    else
        error("impossible")
    end
end

function uninitialized.verify_variables(module)

    local errors = {}

    for _, func in ipairs(module.functions) do

        local nvars = #func.vars
        local nargs = #func.typ.arg_types
        local nret  = #func.typ.ret_types

        local falls_through
        local analysis = coroutine.wrap(function()
            local uninit = {}
            for i = nargs+1, nvars do
                uninit[i] = true
            end
            falls_through = test(func.body, uninit, false)
        end)

        local reported_variables = {} -- (only one error message per variable)
        for o in analysis do
            local cmd, v = o.cmd, o.v
            if not reported_variables[v] then
                reported_variables[v] = true
                local name = func.vars[v].name or 'internal x'..v
                table.insert(errors, cmd.loc:format_error(
                        "error: variable '%s' is used before being initialized", name))
            end
        end

        if falls_through and nret > 0 then
            table.insert(errors, func.loc:format_error(
                "control reaches end of function with non-empty return type"))
        end
    end

    if #errors == 0 then
        return module, {}
    else
        return false, errors
    end
end

return uninitialized


