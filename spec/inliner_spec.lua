local driver = require 'pallene.driver'
local print_ir = require 'pallene.print_ir'
local inliner = require 'pallene.inliner'



-- for debugging purposes
-- local function run_ir(code)
--     local module, errs = driver.compile_internal("__test__.pln", code, "ir")
--     return module, table.concat(errs, "\n")
-- end

local function run_inliner(code)
    local module, errs = driver.compile_internal("__test__.pln", code, "inliner")
    return module, table.concat(errs, "\n")
end

-- we want to compare if the code inlined is equivalent to another when both are in normal form
local function print_ir_normal(module)
    inliner.to_normal_module(module)
    return print_ir(module)
end

-- compare the textual PIR (in normal form) of two versions (that should be equivalent after inlining)
local function assert_inlines(code,equivalent)
    local module, errs = run_inliner(code)
    if #errs > 0 then print(errs) end
    assert.truthy(module)
    local module_equivalent, errs = run_inliner(equivalent)
    if #errs > 0 then print(errs) end
    assert.truthy(module_equivalent,"expected failed to compile")
    -- for debugging, sometimes it is useful to see the original PIR
    -- print(print_ir_normal(run_ir(code)))
    assert.equals(
        print_ir_normal(module_equivalent),
        print_ir_normal(module)
    )
end


describe("Function inline: ", function()

    it("empty function", function()
        assert_inlines([[
            local function B()
            end
            export function A()
                B()
            end
        ]],
        [[
            local function B()
            end
            export function A()
            end
        ]]
    )
    end)
    it("return value propagation", function()
        assert_inlines([[
            local function B() : integer
                return 5
            end
            export function A(): integer
                return B()
            end
        ]],
        [[
            local function B() : integer
                return 5
            end
            export function A(): integer
                local x1 = 5
                return x1
            end
        ]]
    )
    end)
    it("return value in expression", function()
        assert_inlines([[
            local function B() : integer
                return 5
            end
            export function A(): integer
                return 3 + B()
            end
        ]],
        [[
            local function B() : integer
                return 5
            end
            export function A(): integer
                local x1 = 5
                local x2 = 3 + x1
                return x2
            end
        ]]
    )
    end)
    it("returning argument", function()
        assert_inlines([[
            local function B(x : integer) : integer
                return x
            end
            export function A(): integer
                return 3 + B(5)
            end
        ]],
        [[
            local function B(x : integer) : integer
                return x
            end
            export function A(): integer
                local x0 = 5
                local x1 = x0
                local x2 = 3 + x1
                return x2
            end
        ]]
    )
    end)
    it("variables in function", function()
        assert_inlines([[
            local function B(x : integer) : integer
                local y = x + 5
                return y
            end
            export function A(): integer
                return 3 + B(5)
            end
        ]],
        [[
            local function B(x : integer) : integer
                local y = x + 5
                return y
            end
            export function A(): integer
                local x0 = 5
                local x1 = x0 + 5
                local x2 = x1
                local x3 = 3 + x2
                return x3
            end
        ]]
    )
    end)

   it("return expression", function()
        assert_inlines([[
            local function B(x : integer) : integer
                local y = 5
                return y+x
            end
            export function A(): integer
                local x = 0
                local x1 = 3
                local y = B(x)
                local z = y + 4
                local w = z + y
            end
        ]],
        [[
            local function B(x : integer) : integer
                local y = 5
                return y+x
            end
            export function A(): integer
                local x = 0
                local x1 = 3
                local _x = x
                local _y = 5
                local _z = _y+_x
                local y = _z
                local z = y + 4
                local w = z + y
            end
        ]]
    )
    end)



end)
