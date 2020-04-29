-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local Set = {}
function Set.copy(t)
    local ret = {}
    for k,v in ipairs(t) do ret[k] = v end
    return ret
end
function Set.deduplicate(t)
    local hash = {}
    local res = {}
    for _,v in ipairs(t) do
       if not hash[v] then
           res[#res+1] = v
           hash[v] = true
       end
    end
    return res
end
function Set.union(t1, t2)
    local ret = {}
    for _,v in ipairs(t1) do
        table.insert(ret,v)
    end
    for _,v in ipairs(t2) do
        table.insert(ret,v)
    end
    return Set.deduplicate(ret)
end
function Set.difference(t1,t2)
    local ret = {}
    local hash = {}
    for _,v in ipairs(t2) do
       if not hash[v] then
           hash[v] = true
       end
    end
    for _,v in ipairs(t1) do
        if not hash[v] then
            table.insert(ret,v)
        end
    end
    return ret
end
function Set.equal(t1,t2)
    if #t1 ~= #t2 then return false end
    local h1,h2 = {},{}
    for k,v in ipairs(t1) do
       if not h1[v] then
           h1[v] = true
       end
       if not h2[t2[k]] then
           h2[t2[k]] = true
       end
    end
    for k,_ in pairs(h1) do
        if not h2[k] then return false end
    end
    return true
end
function Set.insert(set,element)
    local contains = false
    for _,v in pairs(set) do
        if v == element then contains = true end
    end
    if not contains then
        table.insert(set,element)
    end
end
function Set.iforeach(set,f)
    for k,v in ipairs(set) do
        f(k,v)
    end
end
function Set.foreach(set,f)
    for k,v in pairs(set) do
        f(k,v)
    end
end
return Set