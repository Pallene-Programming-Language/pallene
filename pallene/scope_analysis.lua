local scope_analysis = {}

local ast = require "pallene.ast"
local ast_iterator = require "pallene.ast_iterator"
local builtins = require "pallene.builtins"
local location = require "pallene.location"
local symtab = require "pallene.symtab"

local bind_names = ast_iterator.new()

-- Implement the lexical scoping for a Pallene module.
--
-- Sets a _decl field on Var.Name and Type.Name nodes.
-- This will need to be revised when we introduce modules, because then the "."
-- will mean more than one thing (C++'s "." and "::")
--
-- @param prog AST for the whole module
-- @return true or false, followed by a list of compilation errors
function scope_analysis.bind_names(prog)
    local errors = {}
    local st = symtab.new()
    bind_names:Program(prog, st, errors)
    return (#errors == 0 and prog), errors
end


--
-- Local functions
--

local function scope_error(errors, loc, fmt, ...)
    local errmsg = location.format_error(loc, fmt, ...)
    table.insert(errors, errmsg)
end

local function add_builtins_to_symbol_table(st)
    for name, decl in pairs(builtins) do
        st:add_symbol(name, decl)
    end
end

local function process_toplevel(prog, st, errors)

    local records   = {}
    local variables = {}
    local functions = {}
    for _, tlnode in ipairs(prog) do
        local tag = tlnode._tag
        if     tag == ast.Toplevel.Func   then
            table.insert(functions, tlnode)
        elseif tag == ast.Toplevel.Var    then
            table.insert(variables, tlnode)
        elseif tag == ast.Toplevel.Record then
            table.insert(records, tlnode)
        elseif tag == ast.Toplevel.Import then
            error("not implemented")
        else
            error("impossible")
        end
    end

    --
    -- Check for duplicates
    --
    do
        local names = {}
        for _, tlnode in ipairs(prog) do
            local name = ast.toplevel_name(tlnode)
            local dup = names[name]
            if dup then
                scope_error(errors, tlnode.loc,
                    "duplicate toplevel declaration for %s, previous one at line %d",
                    name, dup.loc.line)
            else
                names[name] = tlnode
            end
        end
    end


    st:with_block(function()
        for _, tlnode in ipairs(records) do
            bind_names:Toplevel(tlnode, st, errors)
            st:add_symbol(ast.toplevel_name(tlnode), tlnode)
        end

        for _, tlnode in ipairs(functions) do
            st:add_symbol(ast.toplevel_name(tlnode), tlnode)
        end

        for _, tlnode in ipairs(variables) do
            st:add_symbol(ast.toplevel_name(tlnode), tlnode)
            bind_names:Toplevel(tlnode, st, errors)
        end

        for _, tlnode in ipairs(functions) do
            bind_names:Toplevel(tlnode, st, errors)
        end
    end)
end

--
-- bind_names
--

function bind_names:Program(prog, st, errors)
    st:with_block(function()
        add_builtins_to_symbol_table(st)
        process_toplevel(prog, st, errors)
    end)
end

function bind_names:Type(type_node, st, errors)
    local tag = type_node._tag
    if tag == ast.Type.Name then
        local name = type_node.name
        local decl = st:find_symbol(name)
        if decl then
            type_node._decl = decl
        else
            scope_error(errors, type_node.loc, "type '%s' is not declared", name)
            type_node._decl = false
        end

    else
        ast_iterator.Type(self, type_node, st, errors)
    end
end

function bind_names:Toplevel(tlnode, st, errors)
    local tag = tlnode._tag
    if     tag == ast.Toplevel.Func then
        for _, decl in ipairs(tlnode.params) do
            bind_names:Decl(decl, st, errors)
        end
        for _, rettype in ipairs(tlnode.rettypes) do
            bind_names:Type(rettype, st, errors)
        end

        st:with_block(function()
            for _, decl in ipairs(tlnode.params) do
                if st:find_dup(decl.name) then
                    scope_error(errors, decl.loc,
                        "function '%s' has multiple parameters named '%s'",
                        tlnode.name, decl.name)
                else
                    st:add_symbol(decl.name, decl)
                end
            end
            bind_names:Stat(tlnode.block, st, errors)
        end)

    else
        ast_iterator.Toplevel(self, tlnode, st, errors)
    end
end

function bind_names:Stat(stat, st, errors)
    local tag = stat._tag
    if     tag == ast.Stat.Block then
        st:with_block(function()
            for _, inner_stat in ipairs(stat.stats) do
                bind_names:Stat(inner_stat, st, errors)
            end
        end)

    elseif tag == ast.Stat.Repeat then
        assert(stat.block._tag == ast.Stat.Block)
        st:with_block(function()
            for _, inner_stat in ipairs(stat.block.stats) do
                bind_names:Stat(inner_stat, st, errors)
            end
            bind_names:Exp(stat.condition, st, errors)
        end)

    elseif tag == ast.Stat.For then
        bind_names:Decl(stat.decl, st, errors)
        bind_names:Exp(stat.start, st, errors)
        bind_names:Exp(stat.limit, st, errors)
        if stat.step then
            bind_names:Exp(stat.step, st, errors)
        end
        st:with_block(function()
            st:add_symbol(stat.decl.name, stat.decl)
            bind_names:Stat(stat.block, st, errors)
        end)

    elseif tag == ast.Stat.Decl then
        bind_names:Decl(stat.decl, st, errors)
        bind_names:Exp(stat.exp, st, errors)
        st:add_symbol(stat.decl.name, stat.decl)

    else
        ast_iterator.Stat(self, stat, st, errors)
    end
end

function bind_names:Var(var, st, errors)
    local tag = var._tag
    if     tag == ast.Var.Name then
        local name = var.name
        local decl = st:find_symbol(name)
        if decl then
            var._decl = decl
        else
            scope_error(errors, var.loc, "variable '%s' is not declared", name)
            var._decl = false
        end

    else
        ast_iterator.Var(self, var, st, errors)
    end
end

return scope_analysis
