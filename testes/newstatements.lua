print('testing new statements: match, with, try-rescue')

local function checkerror (src, msg)
  local f, err = load(src)
  assert(not f and string.find(err, msg, 1, true), err)
end

assert(load([[
local x = 2
local r = 0
match x do
  case 1 then
    r = 10
  case 2 then
    r = 20
  else
    r = 30
end
assert(r == 20)
]]))()

assert(load([[
local out = 0
match 'b' do
  case 'a' then
    out = 1
  case 'b' then
    out = 2
end
assert(out == 2)
]]))()

assert(load([[
local v = 0
with item = 41 do
  v = item + 1
end
assert(v == 42)
]]))()

assert(load([[
local caught = false
try do
  error('boom')
rescue e do
  assert(type(e) == 'string')
  caught = true
end
assert(caught)
]]))()

assert(load([[
local executed = true
try do
  local x = 1 + 1
rescue e do
  executed = false
end
assert(executed)
]]))()

checkerror([[with = 1]], "syntax error")
checkerror([[try do local x = 1 end]], "'rescue' expected")
checkerror([[match 1 do else end]], "'case' expected")

print('test passed!')

return true
