-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local C = require "pallene.C"
local ir = require "pallene.ir"
local util = require "pallene.util"
local typedecl = require "pallene.typedecl"

--
-- Generates a human-readable representation of the IR.
--

local function comma_concat(ss)
    return table.concat(ss, ", ")
end

local function Var(id)
    return "x"..id
end

local function Fun(id)
    if id == 1 then
        return "main"
    else
        return "f"..id
    end
end

local function Global(id)
    return "g"..id
end

local function Val(val)
    local tag = val._tag
    if     tag == "ir.Value.Nil"      then return "nil"
    elseif tag == "ir.Value.Bool"     then return tostring(val.value)
    elseif tag == "ir.Value.Integer"  then return tostring(val.value)
    elseif tag == "ir.Value.Float"    then return C.float(val.value)
    elseif tag == "ir.Value.String"   then return C.string(val.value)
    elseif tag == "ir.Value.LocalVar" then return Var(val.id)
    elseif tag == "ir.Value.Function" then return Fun(val.id)
    else
        typedecl.tag_error(tag)
    end
end

local function Vars(vs)
    local ss = {}
    for i, val in ipairs(vs) do
        ss[i] = Var(val)
    end
    return ss
end

local function Vals(vals)
    local ss = {}
    for i, val in ipairs(vals) do
        ss[i] = Val(val)
    end
    return ss
end

local function Unop(op, src1)
    local opstr
    if     op == "BitNeg"  then opstr = "~"
    elseif op == "BoolNot" then opstr = "not "
    elseif op:match("Len") then opstr = "#"
    elseif op:match("Neg") then opstr = "-"
    else
        error("impossible")
    end
    return opstr..Val(src1)
end

local function Binop(op, src1, src2)
    local opstr
    if     op == "BitAnd"    then opstr = "&"
    elseif op == "BitOr"     then opstr = "|"
    elseif op == "BitXor"    then opstr = "~"
    elseif op == "BitLShift" then opstr = "<<"
    elseif op == "BitRShift" then opstr = ">>"
    elseif op:match("Add")   then opstr = "+"
    elseif op:match("Sub")   then opstr = "-"
    elseif op:match("Mul")   then opstr = "*"
    elseif op:match("Divi")  then opstr = "//"
    elseif op:match("Mod")   then opstr = "%"
    elseif op:match("Div")   then opstr = "/"
    elseif op:match("Pow")   then opstr = "^"
    elseif op:match("Eq")    then opstr = "=="
    elseif op:match("Neq")   then opstr = "~="
    elseif op:match("Lt")    then opstr = "<"
    elseif op:match("Gt")    then opstr = ">"
    elseif op:match("Leq")   then opstr = "<="
    elseif op:match("Geq")   then opstr = ">="
    else
        error("impossible")
    end
    return Val(src1).." "..opstr.." "..Val(src2)
end

local function Bracket(t, k)
    return util.render("$t[$k]", { t = Val(t), k = Val(k) })
end

local function Field(t, field)
    return util.render("$t.$field", {  t = Val(t), field = field })
end

local function Call(fname, args)
    return fname .. "(" .. comma_concat(args) .. ")"
end

local function Cmd(cmd)
    local tag = cmd._tag

    -- Control-flow commands (potentially multi-line)

    if     tag == "ir.Cmd.Nop" then
        return ""
    elseif tag == "ir.Cmd.Seq" then
        local parts = {}
        for i, child in ipairs(cmd.cmds) do
            parts[i] = Cmd(child)
        end
        return table.concat(parts, "\n")
    elseif tag == "ir.Cmd.Return" then
        return "return " .. comma_concat(Vals(cmd.srcs))
    elseif tag == "ir.Cmd.ir.Cmd.Break" then
        return "break"
    elseif tag == "ir.Cmd.Loop" then
        return util.render([[
            loop {
                $body
            }
        ]], {
            body = Cmd(cmd.body)
        })
    elseif tag == "ir.Cmd.If" then
        local cond  = Val(cmd.condition)
        local then_ = Cmd(cmd.then_)
        local else_ = Cmd(cmd.else_)

        local A = (then_ ~= "")
        local B = (else_ ~= "")

        local tmpl
        if A and (not B) then
            tmpl = [[
                if $cond {
                    $then_
                }
            ]]
        elseif (not A) and B then
            tmpl = [[
                if not $cond {
                    $else_
                }
            ]]
        else
            tmpl = [[
                if $cond {
                    $then_
                } else {
                    $else_
                }
            ]]
        end

        return util.render(tmpl, {
            cond = cond,
            then_ = then_,
            else_ = else_,
        })

      elseif tag == "ir.Cmd.For" then
        return util.render([[
            for $v = $a, $b, $c {
                $body
            }
        ]], {
            v = Var(cmd.loop_var),
            a = Val(cmd.start),
            b = Val(cmd.limit),
            c = Val(cmd.step),
            body = Cmd(cmd.body),
        })
    end

    -- Leaf commands (single line)

    local lhs
    if     tag == "ir.Cmd.SetGlobal" then lhs = Global(cmd.global_id)
    elseif tag == "ir.Cmd.SetArr"    then lhs = Bracket(cmd.src_arr, cmd.src_i)
    elseif tag == "ir.Cmd.SetTable"  then lhs = Bracket(cmd.src_tab, cmd.src_k)
    elseif tag == "ir.Cmd.SetField"  then lhs = Field(cmd.src_rec, cmd.field_name)
    else
        lhs = comma_concat(Vars(ir.get_dsts(cmd)))
    end

    local rhs
    if     tag == "ir.Cmd.Move"       then rhs = Val(cmd.src)
    elseif tag == "ir.Cmd.GetGlobal"  then rhs = Global(cmd.global_id)
    elseif tag == "ir.Cmd.SetGlobal"  then rhs = Val(cmd.src)
    elseif tag == "ir.Cmd.Unop"       then rhs = Unop(cmd.op, cmd.src)
    elseif tag == "ir.Cmd.Binop"      then rhs = Binop(cmd.op, cmd.src1, cmd.src2)
    elseif tag == "ir.Cmd.GetArr"     then rhs = Bracket(cmd.src_arr, cmd.src_i)
    elseif tag == "ir.Cmd.SetArr"     then rhs = Val(cmd.src_v)
    elseif tag == "ir.Cmd.GetTable"   then rhs = Bracket(cmd.src_tab, cmd.src_k)
    elseif tag == "ir.Cmd.SetTable"   then rhs = Val(cmd.src_v)
    elseif tag == "ir.Cmd.NewRecord"  then rhs = "new ".. cmd.rec_typ.name .."()"
    elseif tag == "ir.Cmd.GetField"   then rhs = Field(cmd.src_rec, cmd.field_name)
    elseif tag == "ir.Cmd.SetField"   then rhs = Val(cmd.src_v)
    elseif tag == "ir.Cmd.CallStatic" then rhs = Call(Fun(cmd.f_id),  Vals(cmd.srcs))
    elseif tag == "ir.Cmd.CallDyn"    then rhs = Call(Val(cmd.src_f), Vals(cmd.srcs))
    else
        local tagname = assert(typedecl.match_tag(cmd._tag, "ir.Cmd"))
        rhs = Call(tagname, Vals(ir.get_srcs(cmd)))
    end

    if lhs == "" then
        return rhs
    else
        return lhs.." <- "..rhs
    end
end

local function print_func(func)

    return C.reformat(util.render([[
        -- $vars
        -- $type
        function f {
            $body
        }]], {
        vars  = require'inspect'(func.vars,{newline='', indent=""}),
        type  = require'inspect'(func.typ,{newline='', indent=""}),

        body  = Cmd(func.body),
    }))
end

return print_func
