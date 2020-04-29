-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local c_compiler = require "pallene.c_compiler"
local checker = require "pallene.checker"
local constant_propagation = require "pallene.constant_propagation"
local reaching_definitions = require "pallene.reaching_definitions"
local coder = require "pallene.coder"
local parser = require "pallene.parser"
local to_ir = require "pallene.to_ir"
local uninitialized = require "pallene.uninitialized"
local util = require "pallene.util"

local driver = {}

local function check_source_filename(argv0, file_name, expected_ext)
    local name, ext = util.split_ext(file_name)
    if ext ~= expected_ext then
        local msg = string.format("%s: %s does not have a .%s extension",
            argv0, file_name, expected_ext)
        return false, msg
    end
    if not string.match(name, "^[a-zA-Z0-9_/]+$") then
        local msg = string.format("%s: filename %s is non-alphanumeric",
            argv0, file_name)
        return false, msg
    end
    return name
end

--
-- Run AST and IR passes, up-to and including the specified pass.
-- This is meant for unit tests.
--
function driver.compile_internal(filename, stop_after)
    stop_after = stop_after or "optimize"
    local err, errs

    local base_name
    base_name, err = check_source_filename("pallenec test", filename, "pln")
    if not base_name then
        return false, {err}
    end

    local input
    input, err = util.get_file_contents(filename)
    if not input then
        return false, {err}
    end

    local prog_ast
    prog_ast, errs = parser.parse(filename, input)
    if stop_after == "parser" or not prog_ast then
        return prog_ast, errs
    end

    local module
    module, errs = checker.check(prog_ast)
    if stop_after == "checker" or not module then
        return module, errs
    end

    module, errs = to_ir.convert(module)
    if stop_after == "to_ir" or not module then
        return module, errs
    end

    module, errs = uninitialized.verify_variables(module)
    if stop_after == "uninitialized" or not module then
        return module, errs
    end

    module, errs = constant_propagation.run(module)
    if stop_after == "constant_propagation" or not module then
        return module, errs
    end

    module, errs = reaching_definitions.run(module)
    if stop_after == "reaching_definitions" or not module then
        return module, errs
    end

    if stop_after == "optimize" or not module then
        return module, {}
    end

    error("impossible")
end

local function compile_pallene_to_c(pallene_filename, c_filename, mod_name)
    local ok, err, errs

    local module
    module, errs = driver.compile_internal(pallene_filename)
    if not module then
        return false, errs
    end

    local c_code
    c_code, errs = coder.generate(module, mod_name)
    if not c_code then
        return c_code, errs
    end

    ok, err = util.set_file_contents(c_filename, c_code)
    if not ok then
        return ok, {err}
    end

    return true, {}
end

local compiler_steps = {
    { name = "pln", f = compile_pallene_to_c },
    { name = "c",   f = c_compiler.compile_c_to_s },
    { name = "s",   f = c_compiler.compile_s_to_o },
    { name = "o",   f = c_compiler.compile_o_to_so},
    { name = "so",  f = false },
}
local step_index = {}
for i = 1, #compiler_steps do
    step_index[compiler_steps[i].name] = i
end

--
-- Compile an input file with extension [input_ext] to an output file of type
-- [output_ext]. Erases any intermediate files that are produced along the way.
--
-- Example:
--    compile("pln", "so", "foo.pln") --> outputs "foo.so"
--    compile("pln", "c", "foo.pln")  --> outputs "foo.c"
--    compile("c", "so", "foo.c)      --> outputs "foo.so"
--
function driver.compile(argv0, input_ext, output_ext, input_file_name)
    local base_name, err =
        check_source_filename(argv0, input_file_name, input_ext)
    if not base_name then return false, {err} end

    local mod_name = string.gsub(base_name, "/", "_")

    local first_step = step_index[input_ext]  or error("invalid extension")
    local last_step  = step_index[output_ext] or error("invalid extension")
    assert(first_step < last_step, "impossible order")

    local file_names = {}
    for i = first_step, last_step do
        local step = compiler_steps[i]
        if (i == first_step or i == last_step) then
            file_names[i] = base_name .. "." .. step.name
        else
            file_names[i] = os.tmpname()
        end
    end

    local ok, errs
    for i = first_step, last_step-1 do
        local f = compiler_steps[i].f
        local src = file_names[i]
        local out = file_names[i+1]
        ok, errs = f(src, out, mod_name)
        if not ok then break end
    end

    for i = first_step+1, last_step-1 do
        os.remove(file_names[i])
    end

    return ok, errs
end

return driver
