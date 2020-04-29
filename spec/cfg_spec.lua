--local driver = require 'pallene.driver'
--local util = require 'pallene.util'
local CFG = require 'pallene.cfg'

--local inspect = require "inspect"
--local ppi = function(t,f) return inspect(t,{newline='',process=f}) end
--local pp = function(t,f) return inspect(t,{process=f}) end

local function run(ir)
    local res = {}
    --assert(util.set_file_contents("__test__.pln", code))
    --local module, errs = driver.compile_internal("__test__.pln", "to_ir")
    
    --if module == false then
    --    print(table.concat(errs, "\n"))
    --else
        for _, func in ipairs(ir.functions) do
            --print(pp(func.body))
            local cfg = CFG.new(func.body)  
            res[func.name] = cfg
        end
    --end
    return res
end
-- local function assert_error(code)
--     local res = run(code)
--     assert.are.same(res,{})
-- end
local function assert_ok(ir, expected)
    local res = run(ir)
    assert.are.equals(#res,#expected)
    for f_name,func in pairs(expected) do
        assert.is.truthy(res[f_name])
        --print(pp(res[f_name]))
        assert.are.equals(#res[f_name],#func)
        for k,node in pairs(func) do
            -- if type(k) == 'number' then
            --     assert.are.same(res[f_name][k].cmd._tag,node.cmd._tag)
            -- end
            assert.are.same(res[f_name][k].to,node.to)
            assert.are.same(res[f_name][k].from,node.from)
        end
    end
end
local function assert_no_errors(ir) 
  run(ir)
end
local empty = CFG.new()
describe("CFG building: ", function()
    it("empty $init", function()
        --[[
            ""
        ]] 
        assert_ok({
            exports = {},
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              } },
            globals = {},
            record_types = {}
          }, {["$init"] = empty})
    end)
    it("empty function", function()
        --[[
            function fn(): integer
            end
        ]]
        assert_ok({
            exports = { 2 },
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              }, {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "fn",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = { {
                      _tag = "types.T.Integer"
                    } }
                },
                vars = {}
              } },
            globals = {},
            record_types = {}
          }, {["$init"] = empty,["fn"] = empty} )
    end)
    it("sequence", function()
        local res = {["$init"] = empty,["fn"] = {}}
        res["fn"].entry =      {from={},      to={1}}
        table.insert(res["fn"],{from={'entry'},to={2}}) -- a = 1
        table.insert(res["fn"],{from={1},      to={3}}) -- b = 2
        table.insert(res["fn"],{from={2},      to={'exit'}}) -- a + b
        -- c = (a+b) doesnt appear in ir
        res["fn"].exit =       {from={3},      to={}}
        --[[
            function fn(): integer
                local a = 1
                local b = 2
                local c = a + b
            end
        ]]
        assert_ok({
            exports = { 2 },
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              }, {
                body = {
                  _tag = "ir.Cmd.Seq",
                  cmds = { {
                      _tag = "ir.Cmd.Move",
                      dst = 1,
                      src = {
                        _tag = "ir.Value.Integer",
                        value = 1
                      }
                    }, {
                      _tag = "ir.Cmd.Move",
                      dst = 2,
                      src = {
                        _tag = "ir.Value.Integer",
                        value = 2
                      }
                    }, {
                      _tag = "ir.Cmd.Binop",
                      dst = 3,
                      op = "IntAdd",
                      src1 = {
                        _tag = "ir.Value.LocalVar",
                        id = 1
                      },
                      src2 = {
                        _tag = "ir.Value.LocalVar",
                        id = 2
                      }
                    } }
                },
                name = "fn",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = { {
                      _tag = "types.T.Integer"
                    } }
                },
                vars = { {
                    name = "a",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  }, {
                    name = "b",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  }, {
                    name = "c",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  } }
              } },
            globals = {},
            record_types = {}
          }, res )
    end)
    it("if const", function()
        local res = {["$init"] = empty,["fn"] = {}}
        res["fn"].entry =      {from={},       to={1}}
        table.insert(res["fn"],{from={'entry'},to={2}}) -- a = 0
        table.insert(res["fn"],{from={1},      to={3,4}}) -- 5 > 3
        table.insert(res["fn"],{from={2},      to={5}}) -- a = 2
        table.insert(res["fn"],{from={2},      to={5}}) -- a = 3
        table.insert(res["fn"],{from={3,4},    to={'exit'}}) -- return a
        res["fn"].exit =       {from={5},      to={}}
        --[[
            function fn(): integer
                local a = 0
                if 5 > 3 then
                    a = 2
                else
                    a = 3
                end
                return a
            end
        ]]
        assert_ok({
            exports = { 2 },
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              }, {
                body = {
                  _tag = "ir.Cmd.Seq",
                  cmds = { {
                      _tag = "ir.Cmd.Move",
                      dst = 1,
                      src = {
                        _tag = "ir.Value.Integer",
                        value = 0
                      }
                    }, {
                      _tag = "ir.Cmd.Binop",
                      dst = 2,
                      op = "IntGt",
                      src1 = {
                        _tag = "ir.Value.Integer",
                        value = 5
                      },
                      src2 = {
                        _tag = "ir.Value.Integer",
                        value = 3
                      }
                    }, {
                      _tag = "ir.Cmd.If",
                      condition = {
                        _tag = "ir.Value.LocalVar",
                        id = 2
                      },
                      else_ = {
                        _tag = "ir.Cmd.Move",
                        dst = 1,
                        src = {
                          _tag = "ir.Value.Integer",
                          value = 3
                        }
                      },
                      then_ = {
                        _tag = "ir.Cmd.Move",
                        dst = 1,
                        src = {
                          _tag = "ir.Value.Integer",
                          value = 2
                        }
                      }
                    }, {
                      _tag = "ir.Cmd.Return",
                      srcs = { {
                          _tag = "ir.Value.LocalVar",
                          id = 1
                        } }
                    } }
                },
                name = "fn",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = { {
                      _tag = "types.T.Integer"
                    } }
                },
                vars = { {
                    name = "a",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  }, {
                    name = false,
                    typ = {
                      _tag = "types.T.Boolean"
                    }
                  } }
              } },
            globals = {},
            record_types = {}
          }, res )
    end)
    it("if var", function()
        local res = {["$init"] = empty,["fn"] = {}}
        res["fn"].entry =      {from={},       to={1}}
        table.insert(res["fn"],{from={'entry'},to={2}}) -- a = 5
        table.insert(res["fn"],{from={1},      to={3,4}}) -- a > 3
        table.insert(res["fn"],{from={2},      to={5}}) -- a = 2
        table.insert(res["fn"],{from={2},      to={5}}) -- a = 3
        table.insert(res["fn"],{from={3,4},    to={'exit'}}) -- return a
        res["fn"].exit =       {from={5},      to={}}
        --[[
            function fn(): integer
                local a = 5
                if a > 3 then
                    a = 2
                else
                    a = 3
                end
                return a
            end
        ]]
        assert_ok({
            exports = { 2 },
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              }, {
                body = {
                  _tag = "ir.Cmd.Seq",
                  cmds = { {
                      _tag = "ir.Cmd.Move",
                      dst = 1,
                      src = {
                        _tag = "ir.Value.Integer",
                        value = 5
                      }
                    }, {
                      _tag = "ir.Cmd.Binop",
                      dst = 2,
                      op = "IntGt",
                      src1 = {
                        _tag = "ir.Value.LocalVar",
                        id = 1
                      },
                      src2 = {
                        _tag = "ir.Value.Integer",
                        value = 3
                      }
                    }, {
                      _tag = "ir.Cmd.If",
                      condition = {
                        _tag = "ir.Value.LocalVar",
                        id = 2
                      },
                      else_ = {
                        _tag = "ir.Cmd.Move",
                        dst = 1,
                        src = {
                          _tag = "ir.Value.Integer",
                          value = 3
                        }
                      },
                      then_ = {
                        _tag = "ir.Cmd.Move",
                        dst = 1,
                        src = {
                          _tag = "ir.Value.Integer",
                          value = 2
                        }
                      }
                    }, {
                      _tag = "ir.Cmd.Return",
                      srcs = { {
                          _tag = "ir.Value.LocalVar",
                          id = 1
                        } }
                    } }
                },
                name = "fn",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = { {
                      _tag = "types.T.Integer"
                    } }
                },
                vars = { {
                    name = "a",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  }, {
                    name = false,
                    typ = {
                      _tag = "types.T.Boolean"
                    }
                  } }
              } },
            globals = {},
            record_types = {}
          }, res )
    end)
    it("while", function()
        local res = {["$init"] = empty,["fn"] = {}}
        res["fn"].entry =      {from={},       to={1}}
        table.insert(res["fn"],{from={'entry'},to={2}}) -- a = 1
        table.insert(res["fn"],{from={1,3},      to={3,4}}) -- a < 3
        table.insert(res["fn"],{from={2},      to={2}}) -- a + 1
        table.insert(res["fn"],{from={2},      to={'exit'}}) -- return a
        res["fn"].exit =       {from={4},      to={}}
        --[[
            function fn(): integer
                local a = 1
                while a < 3 do
                    a = a + 1
                end
                return a
            end
        ]]
        assert_ok({
            exports = { 2 },
            functions = { {
                body = {
                  _tag = "ir.Cmd.Nop"
                },
                name = "$init",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = {}
                },
                vars = {}
              }, {
                body = {
                  _tag = "ir.Cmd.Seq",
                  cmds = { {
                      _tag = "ir.Cmd.Move",
                      dst = 1,
                      src = {
                        _tag = "ir.Value.Integer",
                        value = 1
                      }
                    }, {
                      _tag = "ir.Cmd.Loop",
                      body = {
                        _tag = "ir.Cmd.Seq",
                        cmds = { {
                            _tag = "ir.Cmd.Binop",
                            dst = 2,
                            op = "IntLt",
                            src1 = {
                              _tag = "ir.Value.LocalVar",
                              id = 1
                            },
                            src2 = {
                              _tag = "ir.Value.Integer",
                              value = 3
                            }
                          }, {
                            _tag = "ir.Cmd.If",
                            condition = {
                              _tag = "ir.Value.LocalVar",
                              id = 2
                            },
                            else_ = {
                              _tag = "ir.Cmd.Break"
                            },
                            then_ = {
                              _tag = "ir.Cmd.Nop"
                            }
                          }, {
                            _tag = "ir.Cmd.Binop",
                            dst = 1,
                            op = "IntAdd",
                            src1 = {
                              _tag = "ir.Value.LocalVar",
                              id = 1
                            },
                            src2 = {
                              _tag = "ir.Value.Integer",
                              value = 1
                            }
                          } }
                      }
                    }, {
                      _tag = "ir.Cmd.Return",
                      srcs = { {
                          _tag = "ir.Value.LocalVar",
                          id = 1
                        } }
                    } }
                },
                name = "fn",
                typ = {
                  _tag = "types.T.Function",
                  arg_types = {},
                  ret_types = { {
                      _tag = "types.T.Integer"
                    } }
                },
                vars = { {
                    name = "a",
                    typ = {
                      _tag = "types.T.Integer"
                    }
                  }, {
                    name = false,
                    typ = {
                      _tag = "types.T.Boolean"
                    }
                  } }
              } },
            globals = {},
            record_types = {}
          }, res )
    end)
    it('break return',function()
      assert_no_errors({
        exports = { 2 },
        functions = {{
          body = {
            _tag = "ir.Cmd.Nop"
          },
          name = "$init",
          typ = {
            _tag = "types.T.Function",
            arg_types = {},
            ret_types = {}
          },
          vars = {}
        },{
        body = {
          _tag = "ir.Cmd.Seq",
          cmds = { {
              _tag = "ir.Cmd.Loop",
              body = {
                _tag = "ir.Cmd.Break"
              }
            }, {
              _tag = "ir.Cmd.Return",
              srcs = { {
                  _tag = "ir.Value.Integer",
                  value = 17
                } }
            } }
        },
        name = "break_while",
        typ = {
          _tag = "types.T.Function",
          arg_types = {},
          ret_types = { {
              _tag = "types.T.Integer"
            } }
        },
        vars = {}
      }},
      globals = {},
      record_types = {}
    })
    end)
    --TODO: 
    --[[
        while with break
        if with return
        if and else with return
        if without return after
        function call
    --]] 

end)