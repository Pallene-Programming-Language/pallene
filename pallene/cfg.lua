-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local Set = require "pallene.set"

local CFG = {}
--[[
    A control flow graph is a representation of all paths 
    that might be traversed through a program execution. 
    
    The nodes represent commands that use or alter data 
    and the edges represent control instructions.

    In this module, each node is defined by two sets of node indices (from and to)
    and a list of commands. These commands are pointers to nodes in the ir module.

    All the commands of the list are one of the listed in the ir module
    except for the control flow ones (Nop, Seq, Return, Break, Loop, If and For).

    Values aren't nodes.

--]]


--[[
    Graph building uses 3 local functions: 
    new_node, new_edge and build.
    build is called on CFG.new.
--]]

-- creates a new node, should only be called to non-control commands.
local function make_node(self, cmd,current_node)
    table.insert(self,{
        cmd = cmd, --TODO a list of commands
        to={},
        from={}
    })
    local new_node_id = #self
    local new_node = self[new_node_id]
    new_node.from = Set.copy(current_node)
    Set.iforeach(new_node.from,function(_,from)
        Set.insert(self[from].to,new_node_id)
    end)
    return {new_node_id}
end
-- creates a new edge from 'from' to 'to'
local function make_edge(self,to,from)
    if to and from then
        Set.insert(self[from].to,to)
        Set.insert(self[to].from,from)
    end
end

-- builds the graph and calls new_node and new_edge.
-- it receives a node to analyze, the current node list and the current loop.
-- it returns an updated current node list and the current loop.

-- usually, the current_node is a set with a single element, an index, 
-- representing the last node visited or the size of the cfg.
-- but when there is a branch meeting, such after ifs or in before loops,
-- it becomes necessary to join the branches, having a list of current nodes

-- current_loop is modelled as a stack, having a set of indexes as the element.


local function build(self,cmd,current_node,current_loop)
    local tag = cmd._tag
    if     tag == "ir.Cmd.Nop" then
        return current_node,current_loop
    elseif tag == "ir.Cmd.Seq" then
        local new_nodes,new_loop = current_node,current_loop
        for _, c in ipairs(cmd.cmds) do
            new_nodes,new_loop = build(self,c,new_nodes,new_loop)
        end
        assert(new_loop == current_loop, 'unmatched loop in seq (impossible)')
        return new_nodes,new_loop
    elseif tag == "ir.Cmd.Return" then
        local new_node = make_node(self,cmd,current_node,current_loop)
        Set.iforeach(new_node,function(_,node) 
            make_edge(self,"exit", node)

        end)
        return new_node,current_loop
    elseif tag == "ir.Cmd.Break" then
        local loop = current_loop[#current_loop]
        assert(loop,'break outside loop (impossible)')
        Set.iforeach(current_node,function(_,node) 
            Set.iforeach(loop,function(_,loop_node) 
                make_edge(self,loop_node, node)
            end)
        end)
        return current_node,current_loop
    elseif tag == "ir.Cmd.Loop" or tag == "ir.Cmd.For" then
        -- in the case of For:
        -- start,limit,step are ir.Value and 
        -- will be extracted to assignments beforehand
        -- so it is equal to a simple Loop in this context

        -- put a new empty top in the current_loop stack
        table.insert(current_loop, {})
        local new_nodes,new_loop = build(self,cmd.body,current_node,current_loop)
        assert(new_loop == current_loop,'unmatched loop ending (impossible)')
        -- at the end of the loop, gets all indexes at the top 
        -- and points them with what happened before
        -- to the same with what happened during the loop
        local top = current_loop[#current_loop]

        -- the condition is the first node of the body
        -- TODO: remove this hack
        -- maybe return the first node of the scope, not the only the current
        -- maybe propose change in the ir
        local first_node
        if #current_node == 1 then
            if type(current_node[1]) == 'number' then
                first_node =  {current_node[1]+1}
            else
                first_node = current_node
            end
        elseif #current_node == 0 then
            first_node = current_node
        else
            error('impossible?')
        end
        
        Set.iforeach(top,function(_,v) 
            Set.iforeach(first_node,function(_,node)
                make_edge(self,node,v) 
            end)
        end) 
        Set.iforeach(new_nodes,function(_,v) 
            Set.iforeach(first_node,function(_,node)
                make_edge(self,node,v) 
            end)
        end) 
        current_loop[#current_loop] = nil

        

        return first_node,new_loop

    elseif tag == "ir.Cmd.If" then
        -- condition is an ir.Value and 
        -- will be extracted to an assignment instruction beforehand
        local then_nodes, then_loop
        if cmd.then_ then
            then_nodes, then_loop = build(self,cmd.then_,current_node,current_loop)
        else 
            then_nodes, then_loop = {},{}
        end
        local else_nodes, else_loop
        if cmd.else_ then
            else_nodes, else_loop = build(self,cmd.else_,current_node,current_loop)
        else 
            else_nodes, else_loop = {},{}
        end
        assert(then_loop == current_loop,'different loop then at meet (impossible)')
        assert(else_loop == current_loop,'different loop else at meet (impossible)')
        return Set.union(then_nodes,else_nodes), current_loop
    elseif string.match(tag, "^ir%.Cmd%.") then
        return make_node(self,cmd,current_node,current_loop), current_loop
    else
        return current_node,current_loop
    end
end
function CFG.new(code)
    local new = {}
    -- entry and exit nodes
    new.entry = {cmd = false, to={},from={}}
    new.exit = {cmd = false, to={},from={}}
    local last_node
    if code then
        local current_node,_ = build(new,code,{"entry"},{})
        last_node = current_node
    else
        last_node = {'entry'}
    end
    Set.iforeach(last_node,function(_,node) 
        make_edge(new,"exit",node)
    end)
    return new
end



-- traverses the CFG applying the function f to each node.
function CFG.traverse_forward(self,f)
    local visited = {}
    local function go(i)
        assert(self[i], 'failed to retrieve node at index '..i)
        visited[i] = true
        f(self,i)
        Set.iforeach(self[i].to,function(_,v) 
            if not visited[v] then
                go(v)
            end
        end)
    end
    go('entry')
end

-- traverses the CFG backwards applying the function f to each node.
function CFG.traverse_backward(self,f)
    local visited = {}
    local function go(i)
        assert(self[i], 'failed to retrieve node at index '..i)
        visited[i] = true
        f(self,i)
        Set.iforeach(self[i].from,function(_,v) 
            if not visited[v] then
                go(v)
            end
        end)
    end
    go('exit')
end

-- a dead code analysis at CFG level:
-- If a node's from is empty, 
-- then the node isn't reachable.
-- returns a set of localizations of unreachable code in the ret input.
-- if it returns ret[true] as unreachable, 
-- it means that the exit node is unreachable,
-- meaning that maybe there is an inifinite loop in the function.
local function check_unreachable(self, index, ret)
    local node = self[index]
    if node then
        if #node.from == 0 then
            if node.cmd.loc then
                ret[node.cmd.loc] = true
            else
                error('impossible',node._tag)
            end 
        end
    end
end
function CFG.unreachable(self)
    local ret = {}
    CFG.traverse_forward(self,function(cfg,index)
        -- don't check entry/exit nodes
        if type(index) == 'number' then 
            check_unreachable(cfg, index, ret) 
        end
    end)
    if #self.exit.from ~= 0 then
        ret[true] = true
    end
    return ret
end

-- converts the CFG to DOT format, which can be redered with the graphviz utility.
function CFG.to_dot(self)
    local str = ''
    local function append(s) str = str .. '\n' .. s end
    append('digraph cfg {')
    append('entry [label="Entry"];')
    append('exit [label="Exit"];')
    local visited = {}
    CFG.traverse_forward(self,function(cfg_,index)
        local n = cfg_[index]
        if n and not visited[n] then
            visited[n] = true
            if type(index) == 'number' then
                append(index..' [label="'..n.cmd._tag..'"];')
            end
            for _,f in pairs(n.from) do 
                append(f..'->'..index..';')
            end
        end
    end)
    append('}')
    return str
end

return CFG