local checker = {}

local ast = require "titan-compiler.ast"
local location = require "titan-compiler.location"
local scope_analysis = require "titan-compiler.scope_analysis"
local types = require "titan-compiler.types"

local check_program
local check_type
local check_toplevel
local check_decl
local check_stat
--local check_then
local check_var
local check_exp
--local check_field

-- Type-check a Titan module
--
-- Sets a _type field on some AST nodes:
--  - Value declarations:
--      - ast.Toplevel.Func
--      - ast.Toplevel.Var
--      - ast.Decl.Decl
--  - ast.Exp
--  - ast.Var
--
-- Sets a _field_types field on ast.Toplevel.Record nodes, mapping field names
-- to their types.
--
-- @ param prog AST for the whole module
-- @ return true or false, followed by as list of compilation errors
function checker.check(filename, input)
    local prog, errors = scope_analysis.bind_names(filename, input)
    if not prog then return false, errors end
    check_program(prog, errors)
    return (#errors == 0 and prog), errors
end

--
-- local functions
--

local function type_error(errors, loc, fmt, ...)
    local errmsg = location.format_error(loc, "type error: "..fmt, ...)
    table.insert(errors, errmsg)
end

-- Checks if two types are the same, and logs an error message otherwise
--   term: string describing what is being compared
--   expected: type that is expected
--   found: type that was actually present
--   errors: list of compile-time errors
--   loc: location of the term that is being compared
local function checkmatch(term, expected, found, errors, loc)
    if not types.equals(expected, found) then
        local msg = "types in %s do not match, expected %s but found %s"
        msg = string.format(msg, term, types.tostring(expected), types.tostring(found))
        type_error(errors, loc, msg)
    end
end


local function is_numeric_type(typ)
    return typ._tag == types.T.Integer or typ._tag == types.T.Float
end

local function coerce_numeric_exp_to_float(exp)
    if exp._type._tag == types.T.Integer then
        local n = ast.Exp.Cast(exp.loc, exp, nil)
        n._type = types.T.Float()
        return n
    elseif exp._type._tag == types.T.Float then
        return exp
    else
        error("not a numeric type")
    end
end

--
-- check
--

check_program = function(prog, errors)
    for _, tlnode in ipairs(prog) do
        check_toplevel(tlnode, errors)
    end
end

check_type = function(typ, errors)
    local tag = typ._tag
    if     tag == ast.Type.Nil then
        return types.T.Nil()

    elseif tag == ast.Type.Boolean then
        return types.T.Boolean()

    elseif tag == ast.Type.Integer then
        return types.T.Integer()

    elseif tag == ast.Type.Float then
        return types.T.Float()

    elseif tag == ast.Type.String then
        return types.T.String()

    elseif tag == ast.Type.Name then
        return typ._decl._type

    elseif tag == ast.Type.Array then
        return types.T.Array(check_type(typ.subtype, errors))

    elseif tag == ast.Type.Function then
        if #typ.rettypes >= 2 then
            error("functions with 2+ return values are not yet implemented")
        end
        local ptypes = {}
        for _, ptype in ipairs(typ.argtypes) do
            table.insert(ptypes, check_type(ptype, errors))
        end
        local rettypes = {}
        for _, rettype in ipairs(typ.rettypes) do
            table.insert(rettypes, check_type(rettype, errors))
        end
        return types.T.Function(ptypes, rettypes)

    else
        error("impossible")
    end
end

check_toplevel = function(tl_node, errors)
    local tag = tl_node._tag
    if     tag == ast.Toplevel.Import then
        type_error(errors, tl_node.loc, "modules are not implemented yet")

    elseif tag == ast.Toplevel.Var then
        if tl_node.decl.type then
            tl_node._type = check_type(tl_node.decl.type, errors)
            check_exp(tl_node.value, errors, tl_node._type)
            checkmatch("declaration of module variable " .. tl_node.decl.name,
                       tl_node._type, tl_node.value._type, errors, tl_node.loc)
        else
            check_exp(tl_node.value, errors, nil)
            tl_node._type = tl_node.value._type
        end

    elseif tag == ast.Toplevel.Func then
        if #tl_node.rettypes >= 2 then
            error("functions with 2+ return values are not yet implemented")
        end

        local ptypes = {}
        for _, param in ipairs(tl_node.params) do
            param._type = check_type(param.type, errors)
            table.insert(ptypes, param._type)
        end

        local rettypes = {}
        for _, rt in ipairs(tl_node.rettypes) do
            table.insert(rettypes, check_type(rt, errors))
        end
        tl_node._type = types.T.Function(ptypes, rettypes)

        local ret = check_stat(tl_node.block, errors, rettypes)
        if not ret and #tl_node._type.rettypes > 0 then
            type_error(errors, tl_node.loc,
                "control reaches end of function with non-empty return type")
        end

    elseif tag == ast.Toplevel.Record then
        tl_node._field_types = {}
        for _, field_decl in ipairs(tl_node.field_decls) do
            local typ = check_type(field_decl.type, errors)
            tl_node._field_types[field_decl.name] = typ
        end
        tl_node._type = types.T.Record(tl_node)

    else
        error("impossible")
    end
end

check_decl = function(decl, errors)
    decl._type = decl._type or check_type(decl.type, errors)
end

-- @param rettypes Declared function return types (for return statements)
check_stat = function(stat, errors, rettypes)
    local tag = stat._tag
    if     tag == ast.Stat.Decl then
        if stat.decl.type then
            check_decl(stat.decl, errors)
            check_exp(stat.exp, errors, stat.decl._type)
        else
            check_exp(stat.exp, errors, nil)
            stat.decl._type = stat.exp._type
            check_decl(stat.decl, errors)
        end
        checkmatch("declaration of local variable " .. stat.decl.name,
            stat.decl._type, stat.exp._type, errors, stat.decl.loc)
        return false

    elseif tag == ast.Stat.Block then
        local ret = false
        for _, inner_stat in ipairs(stat.stats) do
            ret = ret or check_stat(inner_stat, errors, rettypes)
        end
        return ret

    elseif tag == ast.Stat.While then
        check_exp(stat.condition, errors, nil)
        checkmatch("while statement condition",
            types.T.Boolean(), stat.condition._type, errors, stat.condition.loc)
        check_stat(stat.block, errors, rettypes)
        return false

    elseif tag == ast.Stat.Repeat then
        for _, inner_stat in ipairs(stat.block.stats) do
            check_stat(inner_stat, errors, rettypes)
        end
        check_exp(stat.condition, errors, nil)
        checkmatch("repeat statement condition",
            types.T.Boolean(), stat.condition._type, errors, stat.condition.loc)
        return false

    elseif tag == ast.Stat.For then
        if stat.decl.type then
            check_decl(stat.decl, errors)
        end
        check_exp(stat.start, errors, stat.decl._type)
        check_exp(stat.finish, errors, stat.decl._type)
        if stat.inc then
            check_exp(stat.inc, errors, stat.decl._type)
        end
        if not stat.decl.type then
            stat.decl._type = stat.start._type
        end

        local loop_type_is_valid
        if     stat.decl._type._tag == types.T.Integer then
            loop_type_is_valid = true
            if not stat.inc then
                stat.inc = ast.Exp.Integer(stat.finish.loc, 1)
                stat.inc._type = types.T.Integer()
            end
        elseif stat.decl._type._tag == types.T.Float then
            loop_type_is_valid = true
            if not stat.inc then
                stat.inc = ast.Exp.Float(stat.finish.loc, 1.0)
                stat.inc._type = types.T.Float()
            end
        else
            loop_type_is_valid = false
            type_error(errors, stat.decl.loc,
                "type of for control variable %s must be integer or float",
                stat.decl.name)
        end

        if loop_type_is_valid then
            checkmatch("'for' start expression",
                stat.decl._type, stat.start._type, errors, stat.start.loc)
            checkmatch("'for' finish expression",
                stat.decl._type, stat.finish._type, errors, stat.finish.loc)
            checkmatch("'for' step expression",
                stat.decl._type, stat.inc._type, errors, stat.inc.loc)
        end

        check_stat(stat.block, errors, rettypes)
        return false

    elseif tag == ast.Stat.Assign then
        check_var(stat.var, errors)
        check_exp(stat.exp, errors, stat.var._type)
        local texp = stat.var._type
        if texp._tag == types.T.Module then
            type_error(errors, stat.loc, "trying to assign to a module")
        elseif texp._tag == types.T.Function then
            type_error(errors, stat.loc, "trying to assign to a function")
        else
            if stat.var._tag ~= ast.Var.Bracket or stat.exp._type._tag ~= types.T.Nil then
                checkmatch("assignment", stat.var._type, stat.exp._type, errors, stat.var.loc)
            end
        end
        return false

    elseif tag == ast.Stat.Call then
        check_exp(stat.callexp, errors, nil)
        return false

    elseif tag == ast.Stat.Return then
        assert(#rettypes <= 1)
        if #stat.exps ~= #rettypes then
            type_error(errors, stat.loc,
                "returning %d value(s) but function expects %s",
                #stat.exps, #rettypes)
        else
            for i = 1, #stat.exps do
                local exp = stat.exps[i]
                local rettype = rettypes[i]
                check_exp(exp, errors, rettype)
                checkmatch("return statement", rettype, exp._type, errors, exp.loc)
            end
        end
        return true

    elseif tag == ast.Stat.If then
        local ret = true
        for _, thn in ipairs(stat.thens) do
            check_exp(thn.condition, errors, nil)
            checkmatch("if statement condition",
                types.T.Boolean(), thn.condition._type, errors, thn.loc)
            ret = check_stat(thn.block, errors, rettypes) and ret
        end
        if stat.elsestat then
            ret = check_stat(stat.elsestat, errors, rettypes) and ret
        else
            ret = false
        end
        return ret

    else
        error("impossible")
    end
end

check_var = function(var, errors)
    local tag = var._tag
    if     tag == ast.Var.Name then
        var._type = var._decl._type

    elseif tag == ast.Var.Dot then
        check_exp(var.exp, errors, nil)
        local exptype = var.exp._type
        if exptype._tag == types.T.Record then
            local field_type = exptype.type_decl._field_types[var.name]
            if field_type then
                var._type = field_type
            else
                type_error(errors, var.loc,
                    "field '%s' not found in record '%s'",
                    var.name, exptype.type_decl.name)
                var._type = types.T.Invalid()
            end
        else
            type_error(errors, var.loc,
                "trying to access a member of value of type '%s'",
                types.tostring(exptype))
            var._type = types.T.Invalid()
        end

    elseif tag == ast.Var.Bracket then
        check_exp(var.exp1, errors, nil)
        if var.exp1._type._tag ~= types.T.Array then
            type_error(errors, var.exp1.loc,
                "array expression in indexing is not an array but %s",
                types.tostring(var.exp1._type))
            var._type = types.T.Invalid()
        else
            var._type = var.exp1._type.elem
        end
        check_exp(var.exp2, errors, nil)
        checkmatch("array indexing", types.T.Integer(), var.exp2._type, errors, var.exp2.loc)

    else
        error("impossible")
    end
end

-- @param typehint Expected type; Used to infer polymorphic/record constructors.
check_exp = function(exp, errors, typehint)
    local tag = exp._tag
    if     tag == ast.Exp.Nil then
        exp._type = types.T.Nil()

    elseif tag == ast.Exp.Bool then
        exp._type = types.T.Boolean()

    elseif tag == ast.Exp.Integer then
        exp._type = types.T.Integer()

    elseif tag == ast.Exp.Float then
        exp._type = types.T.Float()

    elseif tag == ast.Exp.String then
        exp._type = types.T.String()

    elseif tag == ast.Exp.Initlist then
        -- Determining the type for a table initializer *requires* a type hint.
        -- In theory, we could try to infer the type without a type hint for
        -- non-empty arrays whose contents are inferrable, but I am not sure
        -- we should treat that case differently from the others...
        if typehint then
            if typehint._tag == types.T.Array then
                for _, field in ipairs(exp.fields) do
                    if field.name then
                        type_error(errors, field.loc,
                            "named field %s in array initializer",
                            field.name)
                    else
                        local field_type = typehint.elem
                        check_exp(field.exp, errors, field_type)
                        checkmatch("array initializer",
                            field_type, field.exp._type, errors, field.loc)
                    end
                end

            elseif typehint._tag == types.T.Record then
                local initialized_fields = {}
                for _, field in ipairs(exp.fields) do
                    if field.name then
                        if initialized_fields[field.name] then
                            type_error(errors, field.loc,
                                "duplicate field %s in record initializer",
                                field.name)
                        end
                        initialized_fields[field.name] = true

                        local field_type = typehint.type_decl._field_types[field.name]
                        if field_type then
                            check_exp(field.exp, errors, field_type)
                            checkmatch("record initializer",
                                field_type, field.exp._type, errors, field.loc)
                        else
                            type_error(errors, field.loc,
                                "invalid field %s in record initializer for %s",
                                field.name, typehint.type_decl.name)
                        end
                    else
                        type_error(errors, field.loc,
                            "record initializer has array part")
                    end
                end

                for field_name, _ in pairs(typehint.type_decl._field_types) do
                    if not initialized_fields[field_name] then
                        type_error(errors, exp.loc,
                            "required field %s is missing from initializer",
                            field_name)
                    end
                end
            else
                type_error(errors, exp.loc,
                    "type hint for array or record initializer is not an array or record type")
            end
        else
            type_error(errors, exp.loc,
                "missing type hint for array or record initializer")
        end

        exp._type = typehint or types.T.Invalid()

    elseif tag == ast.Exp.Var then
        check_var(exp.var, errors)
        local texp = exp.var._type
        if texp._tag == types.T.Module then
            type_error(errors, exp.loc,
                "trying to access module '%s' as a first-class value",
                exp.var.name)
            exp._type = types.T.Invalid()
        elseif texp._tag == types.T.Function then
            type_error(errors, exp.loc,
                "trying to access a function as a first-class value")
            exp._type = types.T.Invalid()
        else
            exp._type = texp
        end

    elseif tag == ast.Exp.Unop then
        check_exp(exp.exp, errors, nil)
        local op = exp.op
        if op == "#" then
            if exp.exp._type._tag ~= types.T.Array and exp.exp._type._tag ~= types.T.String then
                type_error(errors, exp.loc,
                    "trying to take the length of a %s instead of an array or string",
                    types.tostring(exp.exp._type))
            end
            exp._type = types.T.Integer()
        elseif op == "-" then
            if exp.exp._type._tag ~= types.T.Integer and exp.exp._type._tag ~= types.T.Float then
                type_error(errors, exp.loc,
                    "trying to negate a %s instead of a number",
                    types.tostring(exp.exp._type))
            end
            exp._type = exp.exp._type
        elseif op == "~" then
            if exp.exp._type._tag ~= types.T.Integer then
                type_error(errors, exp.loc,
                    "trying to bitwise negate a %s instead of an integer",
                    types.tostring(exp.exp._type))
            end
            exp._type = types.T.Integer()
        elseif op == "not" then
            if exp.exp._type._tag ~= types.T.Boolean then
                -- Titan is being intentionaly restrictive here
                type_error(errors, exp.loc,
                    "trying to boolean negate a %s instead of a boolean",
                    types.tostring(exp.exp._type))
            end
            exp._type = types.T.Boolean()
        else
            error("impossible")
        end

    elseif tag == ast.Exp.Concat then
        for _, inner_exp in ipairs(exp.exps) do
            check_exp(inner_exp, errors, nil)
            local texp = inner_exp._type
            if texp._tag ~= types.T.String then
                type_error(errors, inner_exp.loc,
                    "cannot concatenate with %s value", types.tostring(texp))
            end
        end
        exp._type = types.T.String()

    elseif tag == ast.Exp.Binop then
        check_exp(exp.lhs, errors, nil)
        check_exp(exp.rhs, errors, nil)
        local op = exp.op
        if op == "==" or op == "~=" then
            if (exp.lhs._type._tag == types.T.Integer and exp.rhs._type._tag == types.T.Float) or
               (exp.lhs._type._tag == types.T.Float   and exp.rhs._type._tag == types.T.Integer) then
                type_error(errors, exp.loc,
                    "comparisons between float and integers are not yet implemented")
                -- note: use Lua's implementation of comparison, don't just cast to float
            elseif not types.equals(exp.lhs._type, exp.rhs._type) then
                type_error(errors, exp.loc,
                    "cannot compare %s and %s with %s",
                    types.tostring(exp.lhs._type), types.tostring(exp.rhs._type), op)
            end
            exp._type = types.T.Boolean()
        elseif op == "<" or op == ">" or op == "<=" or op == ">=" then
            if (exp.lhs._type._tag == types.T.Integer and exp.rhs._type._tag == types.T.Integer) or
               (exp.lhs._type._tag == types.T.Float   and exp.rhs._type._tag == types.T.Float) or
               (exp.lhs._type._tag == types.T.String  and exp.rhs._type._tag == types.T.String) then
               -- OK
            elseif (exp.lhs._type._tag == types.T.Integer and exp.rhs._type._tag == types.T.Float) or
                   (exp.lhs._type._tag == types.T.Float   and exp.rhs._type._tag == types.T.Integer) then
                type_error(errors, exp.loc,
                    "comparisons between float and integers are not yet implemented")
                -- note: use Lua's implementation of comparison, don't just cast to float
            else
                type_error(errors, exp.loc,
                    "cannot compare %s and %s with %s",
                    types.tostring(exp.lhs._type), types.tostring(exp.rhs._type), op)
            end
            exp._type = types.T.Boolean()

        elseif op == "+" or op == "-" or op == "*" or op == "%" or op == "//" then
            if is_numeric_type(exp.lhs._type) and is_numeric_type(exp.rhs._type) then
                if exp.lhs._type._tag == types.T.Integer and
                   exp.rhs._type._tag == types.T.Integer then
                    exp._type = types.T.Integer()
                else
                    exp.lhs = coerce_numeric_exp_to_float(exp.lhs)
                    exp.rhs = coerce_numeric_exp_to_float(exp.rhs)
                    exp._type = types.T.Float()
                end
            else
                if not is_numeric_type(exp.lhs._type) then
                    type_error(errors, exp.loc,
                        "left hand side of arithmetic expression is a %s instead of a number",
                        types.tostring(exp.lhs._type))
                end
                if not is_numeric_type(exp.rhs._type) then
                    type_error(errors, exp.loc,
                        "right hand side of arithmetic expression is a %s instead of a number",
                        types.tostring(exp.rhs._type))
                end
                exp._type = types.T.Invalid()
            end

        elseif op == "/" or op == "^" then
            if is_numeric_type(exp.lhs._type) and is_numeric_type(exp.rhs._type) then
                exp.lhs = coerce_numeric_exp_to_float(exp.lhs)
                exp.rhs = coerce_numeric_exp_to_float(exp.rhs)
                exp._type = types.T.Float()
            else
                if not is_numeric_type(exp.lhs._type._tag) then
                    type_error(errors, exp.loc,
                        "left hand side of arithmetic expression is a %s instead of a number",
                        types.tostring(exp.lhs._type))
                end
                if not is_numeric_type(exp.rhs._type._tag) then
                    type_error(errors, exp.loc,
                        "right hand side of arithmetic expression is a %s instead of a number",
                        types.tostring(exp.rhs._type))
                end
                exp._type = types.T.Float()
            end

        elseif op == "and" or op == "or" then
            if exp.lhs._type._tag ~= types.T.Boolean then
                type_error(errors, exp.loc,
                    "left hand side of logical expression is a %s instead of a boolean",
                    types.tostring(exp.lhs._type))
            end
            if exp.rhs._type._tag ~= types.T.Boolean then
                type_error(errors, exp.loc,
                    "right hand side of logical expression is a %s instead of a boolean",
                    types.tostring(exp.rhs._type))
            end
            exp._type = types.T.Boolean()
        elseif op == "|" or op == "&" or op == "~" or op == "<<" or op == ">>" then
            if exp.lhs._type._tag ~= types.T.Integer then
                type_error(errors, exp.loc,
                    "left hand side of arithmetic expression is a %s instead of an integer",
                    types.tostring(exp.lhs._type))
            end
            if exp.rhs._type._tag ~= types.T.Integer then
                type_error(errors, exp.loc,
                    "right hand side of arithmetic expression is a %s instead of an integer",
                    types.tostring(exp.rhs._type))
            end
            exp._type = types.T.Integer()
        else
            error("impossible")
        end

    elseif tag == ast.Exp.Call then
        assert(exp.exp._tag == ast.Exp.Var, "function calls are first-order only!")
        local var = exp.exp.var
        check_var(var, errors)
        exp.exp._type = var._type
        local fname = var._tag == ast.Var.Name and var.name or (var.exp.var.name .. "." .. var.name)
        if var._type._tag == types.T.Function then
            local ftype = var._type
            local nparams = #ftype.params
            local args = exp.args.args
            local nargs = #args
            local arity = math.max(nparams, nargs)
            for i = 1, arity do
                local arg = args[i]
                local ptype = ftype.params[i]
                local atype
                if not arg then
                    atype = ptype
                else
                    check_exp(arg, errors, ptype)
                    ptype = ptype or arg._type
                    atype = args[i]._type
                end
                if not ptype then
                    ptype = atype
                end
                checkmatch(
                    "argument " .. i .. " of call to function '" .. fname .. "'",
                    ptype, atype, errors, exp.exp.loc)
            end
            if nargs ~= nparams then
                type_error(errors, exp.loc,
                    "function %s called with %d arguments but expects %d",
                    fname, nargs, nparams)
            end
            assert(#ftype.rettypes <= 1)
            if #ftype.rettypes >= 1 then
                exp._type = ftype.rettypes[1]
            else
                exp._type = types.T.Void()
            end
        else
            type_error(errors, exp.loc,
                "'%s' is not a function but %s",
                fname, types.tostring(var._type))
            exp._type = types.T.Invalid()
        end

    elseif tag == ast.Exp.Cast then
        local target = check_type(exp.target, errors)
        check_exp(exp.exp, errors, target)
        if not types.coerceable(exp.exp._type, target) then
            type_error(errors, exp.loc,
                "cannot cast '%s' to '%s'",
                types.tostring(exp.exp._type), types.tostring(target))
        end
        exp._type = target

    else
        error("impossible")
    end
end

return checker
