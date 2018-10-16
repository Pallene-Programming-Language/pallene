local driver = require "pallene.driver"
local util = require "pallene.util"

local ast = require "pallene.ast"
local builtins = require "pallene.builtins"

local function run_scope_analysis(code)
    assert(util.set_file_contents("test.pallene", code))
    local prog, errs = driver.test_ast("scope_analysis", "test.pallene")
    return prog, table.concat(errs, "\n")
end

describe("Scope analysis: ", function()

    teardown(function()
        os.remove("test.pallene")
    end)

    it("functions can see global variables", function()
        local prog, errs = run_scope_analysis([[
            local x: integer = 10
            function fn(): integer
                return x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- x
            prog[2].block.stats[1].exps[1].var._decl)
    end)

    it("global variables can see functions", function()
        local prog, errs = run_scope_analysis([[
            local f: integer->integer = foo
            local function foo(x:integer): integer
                return 17
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[2], -- foo
            prog[1].value.var._decl)
    end)

    it("function parameters work", function()
        local prog, errs = run_scope_analysis([[
            function fn(x: integer): integer
                return x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1].params[1], -- x
            prog[1].block.stats[1].exps[1].var._decl)
    end)

    it("local variables work", function()
        local prog, errs = run_scope_analysis([[
            function fn(): integer
                local x = 17
                return x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1].block.stats[1].decl, -- x
            prog[1].block.stats[2].exps[1].var._decl)
    end)

    it("functions can be recursive", function()
        local prog, errs = run_scope_analysis([[
            function fac(n: integer): integer
                if n == 0 then
                    return 1
                else
                    return n * fac(n-1)
                end
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- fac
            prog[1].block.stats[1].else_.stats[1].exps[1].rhs.exp.var._decl)
    end)

    it("allows type variables to be used before they are defined", function()
        local prog, errs = run_scope_analysis([[
            function fn(p: Point): integer
                return p.x
            end

            record Point
                x: integer
                y: integer
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[2], --Point
            prog[1].params[1].type._decl)
    end)

    it("builtins work", function()
        local prog, errs = run_scope_analysis([[
            function fn(xs:{integer})
                table_insert(xs, 17)
            end
        ]])
        assert(prog, errs)
        local exp = prog[1].block.stats[1].callexp
        assert.are.equal(ast.Exp.CallFunc, exp._tag)
        local f_exp = exp.exp
        assert.are.equal(ast.Exp.Var, f_exp._tag)
        local var = f_exp.var
        assert.are.equal(ast.Var.Name, var._tag)
        local decl = var._decl
        assert.are_equal(builtins.table_insert, decl)
    end)

    it("forbids variables from being used before they are defined", function()
        local prog, errs = run_scope_analysis([[
            function fn(): nil
                x = 17
                local x = 18
            end
        ]])
        assert.falsy(prog)
        assert.match("variable 'x' is not declared", errs)
    end)

    it("do-end limits variable scope", function()
        local prog, errs = run_scope_analysis([[
            function fn(): nil
                do
                    local x = 17
                end
                x = 18
            end
        ]])
        assert.falsy(prog)
        assert.match("variable 'x' is not declared", errs)
    end)

    it("local variable scope doesn't shadow its type annotation", function()
        local prog, errs = run_scope_analysis([[
            record x
                x: integer
                y: integer
            end

            function fn(): integer
                local x: x = { x=1, y=2 }
                return x.x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- global x
            prog[2].block.stats[1].decl.type._decl)
        assert.are.equal(
            prog[2].block.stats[1].decl, -- local x
            prog[2].block.stats[2].exps[1].var.exp.var._decl)
    end)

    it("local variable scope doesn't shadow its initializer", function()
        local prog, errs = run_scope_analysis([[
            local x = 17
            function fn(): integer
                local x = x + 1
                return x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- global x
            prog[2].block.stats[1].exp.lhs.var._decl)
        assert.are.equal(
            prog[2].block.stats[1].decl, -- local x
            prog[2].block.stats[2].exps[1].var._decl)
    end)

    it("repeat-until scope includes the condition", function()
        local prog, errs = run_scope_analysis([[
            function fn(): integer
                local x = 0
                repeat
                    x = x + 1
                    local limit = x * 10
                until limit >= 100
                return x
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1].block.stats[2].block.stats[2].decl, -- local limit
            prog[1].block.stats[2].condition.lhs.var._decl)
    end)

    it("for loop variable scope doesn't shadow its type annotation", function()
        local prog, errs = run_scope_analysis([[
            record x
                x: integer
                y: integer
            end
            function fn(): integer
                for x: x = 1, 10 do
                   return x
                end
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- global x
            prog[2].block.stats[1].decl.type._decl)
        assert.are.equal(
            prog[2].block.stats[1].decl, -- local x
            prog[2].block.stats[1].block.stats[1].exps[1].var._decl)
    end)

    it("for loop variable scope doesn't shadow its initializers", function()
        local prog, errs = run_scope_analysis([[
            function fn(): integer
                local x = 10
                for x: integer = x, x, x do
                   return x
                end
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1].block.stats[1].decl, -- local x
            prog[1].block.stats[2].start.var._decl)
        assert.are.equal(
            prog[1].block.stats[1].decl,
            prog[1].block.stats[2].limit.var._decl)
        assert.are.equal(
            prog[1].block.stats[1].decl,
            prog[1].block.stats[2].step.var._decl)
        assert.are.equal(
            prog[1].block.stats[2].decl, -- for x
            prog[1].block.stats[2].block.stats[1].exps[1].var._decl)
    end)

    it("forbids multiple toplevel declarations with the same name", function()
        local prog, errs = run_scope_analysis([[
            local x: integer = 10
            local x: integer = 11
        ]])
        assert.falsy(prog)
        assert.match("duplicate toplevel declaration", errs)
    end)

    it("forbids multiple function arguments with the same name", function()
        local prog, errs = run_scope_analysis([[
            function fn(x: integer, x:string)
            end
        ]])
        assert.falsy(prog)
        assert.match("function 'fn' has multiple parameters named 'x'", errs)
    end)

    it("forbids recursive types", function()
        local prog, errs = run_scope_analysis([[
            record A
                x: A
            end
        ]])
        assert.falsy(prog)
        assert.match("type 'A' is not declared", errs)
    end)

    it("forbids forward variable initializers", function()
        local prog, errs = run_scope_analysis([[
            local x = y
            local y = 10
        ]])
        assert.falsy(prog)
        assert.match("variable 'y' is not declared", errs)
    end)

    it("allows recursive functions", function()
        local prog, errs = run_scope_analysis([[
            local function fat(n: integer): integer
                if n == 0 then
                    return 1
                else
                    return n * fat(n - 1)
                end
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- fat
            prog[1].block.stats[1].else_.stats[1].exps[1].rhs.exp.var._decl)
    end)

    it("allows mutually recursive functions", function()
        local prog, errs = run_scope_analysis([[
            local function foo(): integer
                return bar()
            end

            local function bar(): integer
                return foo()
            end
        ]])
        assert(prog, errs)
        assert.are.equal(
            prog[1], -- foo
            prog[2].block.stats[1].exps[1].exp.var._decl)
        assert.are.equal(
            prog[2], -- bar
            prog[1].block.stats[1].exps[1].exp.var._decl)
    end)
end)
