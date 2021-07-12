-- Copyright (c) 2021, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local util     = require "pallene.util"
local typedecl = require "pallene.typedecl"
local types    = require "pallene.types"
local ast      = require "pallene.ast"
local checker  = require "pallene.checker"

local converter = {}

--
--  ASSIGNMENT CONVERSION
-- ======================
-- This Compiler pass handles mutable captured variables inside nested closures by
-- transforming AST Nodes that reference or re-assign to them. All captured variables
-- are 'boxed' inside records. For example, consider this code:
-- ```
-- function m.foo()
--     local x: integer = 10
--     local set_x: (integer) -> () = function (y)
--          x = y
--     end
--     local get_x: () -> integer = function () return x end
-- end
--```
-- The AST representation of the above snippet, will be converted in this pass to
-- something like the following:
-- ```
-- record $T
--     value: integer
-- end
--
-- function m.foo()
--     local x: $T = { value = 10 }
--     local set_x: (integer) -> () = function (y)
--          x.value = y
--     end
--     local get_x: () -> integer = function () return x.value end
-- end
-- ```

local Converter = util.Class()

function converter.convert(prog_ast)
    local conv = Converter.new()
    conv:visit_prog(prog_ast)

    -- transform the AST Nodes for captured vars.
    conv:apply_transformations()

    -- add the upvalue box record types to the AST
    for _, node in ipairs(conv.box_records) do
        table.insert(prog_ast.tls, node)
    end

    return prog_ast
end


-- Encapsulates an update to an AST Node.
-- `node`: The AST we will replace (we use it's location)
-- `update_fn`: A `node -> ()` function that is used to update the node.
local function NodeUpdate(node, update_fn)
    return {
        node = node,
        update_fn = update_fn,
    }
end

function Converter:init()
    self.update_ref_of_decl      = {} -- { ast.Decl => list of NodeUpdate }

    -- The `func_depth_of_decl` maps a decl to the depth of the function where it appears.
    -- This helps distinguish between mutated variables that are locals and globals from those
    -- that are captured upvalues and need to be transformed to a different kind of node.
    self.func_depth_of_decl      = {} -- { ast.Decl => integer }
    self.update_init_exp_of_decl = {} -- { ast.Decl => NodeUpdate }
    self.mutated_decls           = {} -- { ast.Decl }
    self.captured_decls          = {} -- { ast.Decl }
    self.box_records             = {} -- list of ast.Toplevel.Record
    self.lambda_of_param         = {} -- { ast.Decl => ast.Lambda }

    -- Variables that are not initialized upon declaration can still be captured as
    -- upvalues. In order to facilitate this, we add an `ast.Exp.UpvalueRecord` node
    -- to the corresponding ast.Decl node.
    self.add_init_exp_to_decl = {} -- { ast.Decl => NodeUpdate }

    -- used to assign unique names to subsequently generated record types
    self.typ_counter = 0

    -- Depth of current function's nesting.
    -- This does not take into account block scopes like `do...end`.
    self.func_depth  = 1
end

-- generates a unique type name each time
function Converter:type_name(var_name)
    self.typ_counter = self.typ_counter + 1
    return "$T_"..var_name.."_"..self.typ_counter
end

function Converter:add_box_type(loc, typ)
    local dummy_node = ast.Toplevel.Record(loc, types.tostring(typ), {})
    dummy_node._type = typ
    table.insert(self.box_records, dummy_node)
    return dummy_node
end

function Converter:register_decl(decl)
    if not self.update_ref_of_decl[decl] then
        self.update_ref_of_decl[decl] = {}
        self.func_depth_of_decl[decl] = self.func_depth
    end
end

function Converter:visit_prog(prog_ast)
    assert(prog_ast._tag == "ast.Program.Program")
    for _, tl_node in ipairs(prog_ast.tls) do
        if tl_node._tag == "ast.Toplevel.Stats" then
            for _, stat in ipairs(tl_node.stats) do
                self:visit_stat(stat)
            end
        else
            -- skip record declarations and type aliases
            assert(typedecl.match_tag(tl_node._tag, "ast.Toplevel"))
        end
    end
end

function Converter:visit_stats(stats)
    for _, stat in ipairs(stats) do
        self:visit_stat(stat)
    end
end

-- Goes over all the ast.Decls inside the AST that have been captured by some nested
-- function, transforms the decl node itself and all the references made to it.
function Converter:apply_transformations()
    local proxy_var_of_param       = {} -- { ast.Decl => ast.Decl }
    local proxy_stats_of_lambda    = {} -- { ast.Lambda => list of ast.Stat.Decl }

    for decl in pairs(self.mutated_decls) do
        if self.captured_decls[decl] then
            assert(not decl._exported_as)

            -- 1. Create a record type `$T` to hold this captured var.
            -- 2. Transform  node from `local x = value` to `local x: $T =  { value = value }`
            -- 3. Transform all references to the var from `ast.Var.Name` to ast.Var.Dot
            local typ = types.T.Record(
                self:type_name(decl.name),
                { "value" },
                { value = decl._type },
                true
            )

            self:add_box_type(decl.loc, typ)
            local is_param = self.lambda_of_param[decl]
            local init_exp_update = self.update_init_exp_of_decl[decl]

            if init_exp_update then
                local old_exp = init_exp_update.node
                decl._type = typ
                local update  = init_exp_update.update_fn

                local new_node = ast.Exp.InitList(old_exp.loc, {{ name = "value", exp = old_exp }})
                new_node._type = typ
                update(new_node)

            elseif is_param then
                --- Function parameters that are captured are implementing by "proxy"-ing them.
                --- Consider the following function that returns a closure:
                --- ```
                --- function m.foo(n: integer)
                ---   -- capture n
                --- end
                --- ```
                --- Since we cannot transform the declaration node of a function parameter,
                --- we create a variable to represent the boxed parameter which can be captured.
                --- ```
                --- function m.foo(n: integer)
                ---   local $n: $T = { value = n }
                ---   -- capture and mutate $n
                --- end
                local param = ast.Exp.Var(decl.loc, ast.Var.Name(decl.loc, decl.name))
                param.var._def = checker.Def.Variable(decl)
                param.var._type = assert(decl._type)
                param._type = decl._type

                local decl_lhs = ast.Decl.Decl(decl.loc, "$"..decl.name, false)
                local decl_rhs = ast.Exp.InitList(decl.loc, {{ name = "value", exp = param }})
                decl_rhs._type = typ
                decl_lhs._type = typ

                local stat = ast.Stat.Decl(decl.loc, { decl_lhs }, { decl_rhs })

                local lambda = self.lambda_of_param[decl]
                if not proxy_stats_of_lambda[lambda] then
                    proxy_stats_of_lambda[lambda] = {}
                end
                table.insert(proxy_stats_of_lambda[lambda], stat)
                proxy_var_of_param[decl] = decl_lhs

            else
                -- Capturing uninitialized decls as mutable upvalues
                decl._type = typ

                local ast_update = assert(self.add_init_exp_to_decl[decl])
                local update     = ast_update.update_fn

                local new_node = ast.Exp.UpvalueRecord(decl.loc)
                new_node._type = typ
                update(new_node)
            end

            --- Update all references made to the mutable upvalue. Replace all `ast.Var` nodes
            --- with `ast.Dot` nodes.
            for _, node_update in ipairs(self.update_ref_of_decl[decl]) do
                local old_var = node_update.node
                local loc     = old_var.loc
                local update  = node_update.update_fn

                local dot_exp
                local proxy_decl = proxy_var_of_param[decl]
                if proxy_decl then
                    -- references to captured parameters get replaced by references to `value` field of
                    -- their proxy variables.
                    local proxy_var = ast.Var.Name(old_var.loc, "$"..decl.name)
                    proxy_var._def  = checker.Def.Variable(proxy_decl)
                    dot_exp         = ast.Exp.Var(loc, proxy_var)
                else
                    dot_exp = ast.Exp.Var(loc, old_var)
                end

                local new_node = ast.Var.Dot(old_var.loc, dot_exp, "value")
                new_node.exp._type = typ
                update(new_node)
            end
        end
    end


    -- insert all the parameter proxy declarations
    for lambda, stats in pairs(proxy_stats_of_lambda) do
        for _, stat in ipairs(lambda.body.stats) do
            table.insert(stats, stat)
        end
        lambda.body.stats = stats
    end

end

function Converter:visit_lambda(lambda)
    self.func_depth = self.func_depth + 1
    for _, arg in ipairs(lambda.arg_decls) do
        self:register_decl(arg)
        self.lambda_of_param[arg] = lambda
    end

    self:visit_stats(lambda.body.stats)
    assert(self.func_depth > 1)
    self.func_depth = self.func_depth - 1
end

function Converter:visit_func(func)
    assert(func._tag == "ast.FuncStat.FuncStat")
    local lambda = func.value
    assert(lambda and lambda._tag == "ast.Exp.Lambda")
    self:visit_lambda(lambda)
end

function Converter:visit_stat(stat)
    local tag = stat._tag
    if tag == "ast.Stat.Functions" then
        for _, func in ipairs(stat.funcs) do
            self:visit_func(func)
        end

    elseif tag == "ast.Stat.Return" then
        for _, exp in ipairs(stat.exps) do
            self:visit_exp(exp)
        end

    elseif tag == "ast.Stat.Decl" then
        for i, decl in ipairs(stat.decls) do
            self:register_decl(decl)

            if i > #stat.exps then
                -- Uninitialized decls might be captured as upvalues.
                local update_decl = function (new_exp)
                    stat.exps[i] = new_exp
                end
                self.add_init_exp_to_decl[decl] = NodeUpdate(decl, update_decl)
            end
        end

        for i, exp in ipairs(stat.exps) do
            self:visit_exp(exp)
            -- do not register extra values on RHS
            if i <= #stat.decls then
                -- update the initializer expression of this decl in case it's being captured
                -- and mutated.
                local update_init = function (new_exp)
                    stat.exps[i] = new_exp
                end
                self.update_init_exp_of_decl[stat.decls[i]] = NodeUpdate(stat.exps[i], update_init)
            end
        end

    elseif tag == "ast.Stat.Block" then
        self:visit_stats(stat.stats)

    elseif tag == "ast.Stat.While" or tag == "ast.Stat.Repeat" then
        self:visit_stats(stat.block.stats)
        self:visit_exp(stat.condition)

    elseif tag == "ast.Stat.If" then
        self:visit_exp(stat.condition)
        self:visit_stats(stat.then_.stats)
        if stat.else_ then
            self:visit_stat(stat.else_)
        end

    elseif tag == "ast.Stat.ForNum" then
        self:visit_exp(stat.start)
        self:visit_exp(stat.limit)
        self:visit_exp(stat.step)

        self:register_decl(stat.decl)
        self:visit_stats(stat.block.stats)

    elseif tag == "ast.Stat.ForIn" then
        for _, decl in ipairs(stat.decls) do
            self:register_decl(decl)
        end

        for _, exp in ipairs(stat.exps) do
            self:visit_exp(exp)
        end

        self:visit_stats(stat.block.stats)

    elseif tag == "ast.Stat.Assign" then
        for i, var in ipairs(stat.vars) do
            self:visit_var(var, function (new_var)
                stat.vars[i] = new_var
            end)

            if var._tag == "ast.Var.Name" and not var._exported_as then
                if var._def._tag == "checker.Def.Variable" then
                    local decl = assert(var._def.decl)
                    self.mutated_decls[decl] = true
                end
            end
        end

        for _, exp in ipairs(stat.exps) do
            self:visit_exp(exp)
        end

    elseif tag == "ast.Stat.Decl" then
        for _, decl in ipairs(stat.decls) do
            self:register_decl(decl)
        end

        for _, exp in ipairs(stat.exps) do
            self:visit_exp(exp)
        end

    elseif tag == "ast.Stat.Call" then
        self:visit_exp(stat.call_exp)

    elseif  tag == "ast.Stat.Break" then
        -- empty
    else
        typedecl.tag_error(tag)
    end
end

-- This function takes an `ast.Var` node and a callback that should replace the reference to the
-- var at the call site with a transformed AST node, provided the new AST node as an argument.
-- If it is found out  later that `var` is being captured and mutated somewhere then `update_fn`
-- is called to transform it to an `ast.Var.Dot` Node.
--
-- @param var The `ast.Var` node.
-- @param update_fn An `(ast.Var) -> ()` function that should update an `ast.Var.Name` node
--        to a new `ast.Var.Dot` node by assigning it's argument to an appropriate location in the AST
function Converter:visit_var(var, update_fn)
    local vtag = var._tag

    if vtag == "ast.Var.Name" and not var._exported_as then
        if var._def._tag == "checker.Def.Variable" then
            local decl = assert(var._def.decl)
            assert(self.update_ref_of_decl[decl])
            local depth = self.func_depth_of_decl[decl]
            -- depth == 1 when the decl is that of a global
            if depth < self.func_depth and depth > 1 then
                self.captured_decls[decl] = true
            end
            table.insert(self.update_ref_of_decl[decl], NodeUpdate(var, update_fn))
        end

    elseif vtag == "ast.Var.Dot" then
        self:visit_exp(var.exp)

    elseif vtag == "ast.Var.Bracket" then
        self:visit_exp(var.t)
        self:visit_exp(var.k)

    end
end

-- If necessary, transforms `exp` or one of it's subexpression nodes in case they
-- reference a mutable upvalue.
-- Recursively visits all sub-expressions and applies an `ast.Var.Name => ast.Var.Dot`
-- transformation wherever necessary.
function Converter:visit_exp(exp)
    local tag = exp._tag

    if tag == "ast.Exp.InitList" then
        for _, field in ipairs(exp.fields) do
            self:visit_exp(field.exp)
        end

    elseif tag == "ast.Exp.Lambda" then
        self:visit_lambda(exp)

    elseif tag == "ast.Exp.CallFunc" or tag == "ast.Exp.CallMethod" then
        self:visit_exp(exp.exp)
        for _, arg in ipairs(exp.args) do
            self:visit_exp(arg)
        end

    elseif tag == "ast.Exp.Var" then
        self:visit_var(exp.var, function (new_var) exp.var = new_var  end)

    elseif tag == "ast.Exp.Unop"
        or tag == "ast.Exp.Cast"
        or tag == "ast.Exp.ToFloat"
        or tag == "ast.Exp.Paren" then
        self:visit_exp(exp.exp)

    elseif tag == "ast.Exp.Binop" then
        self:visit_exp(exp.lhs)
        self:visit_exp(exp.rhs)

    elseif not typedecl.match_tag(tag, "ast.Exp") then
        typedecl.tag_error(tag)
    end
end

return converter
