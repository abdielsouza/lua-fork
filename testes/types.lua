print('testing static typing')

local function checkerror (src, msg)
  local f, err = load(src)
  assert(not f and string.find(err, msg, 1, true), err)
end

assert(load([[local a::int = 1
local b::float = 1
local c::str = 'x'
local d::bool = true
local t::tabletype = {}
local x::anytype = 1
x = 'ok']]))()

assert(load([[local f::float = 1
f = 2
f = 3.5]]))()

assert(load([[local u::int|str = 1
u = 'ok'
u = 2]]))()

assert(load([[local gt::tabletype<str, int> = {}
gt = {}]]))()

assert(load([[local box::Box<int> = 1
box = 'anything'
box = {}]]))()

assert(load([[
local id::function(int)->int = function (x::int)::int
  return x
end
local v::int = id(3)
assert(v == 3)
]]))()

assert(load([[
local function run(f::function(int)->int, x::int)::int
  return f(x)
end
local function add1(a::int)::int
  return a + 1
end
local r::int = run(add1, 9)
assert(r == 10)
]]))()

assert(load([[
local noop::function()->unit = function()::unit
  return
end
noop()
]]))()

assert(load([[
local p::tabletype<name:str, age:int> = {}
p.name = 'Lua'
p.age = 31
local n::str = p.name
local a::int = p.age
assert(n == 'Lua' and a == 31)
]]))()

assert(load([[
local i = 1
i = 2
]]))()

assert(load([[
local f = function (x::int)::int
  return x
end
local r::int = f(7)
assert(r == 7)
]]))()

checkerror("local a::int = 'x'", "cannot assign 'str' to 'int' variable 'a'")
checkerror("local a::bool = 1", "cannot assign 'int' to 'bool' variable 'a'")
checkerror("local a::int; a = 'x'", "cannot assign 'str' to 'int' variable 'a'")
checkerror("local a::int, b::str = 1, 2", "cannot assign 'int' to 'str' variable 'b'")
checkerror("global g::int = 'x'", "cannot assign 'str' to 'int' variable 'g'")
checkerror("local function f(a::int) a = 'x' end", "cannot assign 'str' to 'int' variable 'a'")
checkerror("local u::int|str = true", "cannot assign 'bool' to 'int|str' variable 'u'")
checkerror("local gt::tabletype<str, int> = 1", "cannot assign 'int' to 'tabletype' variable 'gt'")
checkerror([[local fn::function(int)->int = function (x::str)::int return 1 end]], "cannot assign")
checkerror([[local function bad()::int return end]], "return type mismatch")
checkerror([[local function run(f::function(int)->int)::int return f('x') end]], "argument 1 type mismatch")
checkerror([[local p::tabletype<name:str> = {}; p.name = 1]], "cannot assign 'int' to 'str' variable 'name'")
checkerror([[local p::tabletype<name:str> = {}; p.age = 1]], "field 'age' is not declared in tabletype")
checkerror([[local i = 1; i = 'x']], "cannot assign 'str' to 'int' variable 'i'")
checkerror([[local f = function (x::int)::int return x end; f = function (s::str)::int return 1 end]], "cannot assign")

print('test passed!')

return true
