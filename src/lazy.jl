## Free

abstract type Lazy end

struct Free <: AbstractSLProgram
    x::Lazy # must not contain Gen
    gens::Vector{Symbol}
end

Free(x::Lazy) = Free(x, collect(Symbol, slpsyms(maxinput(x))))

function freegens(n::Integer, syms=slpsyms(n))
    syms = collect(syms)
    Any[Free(Input(i), syms) for i=1:n]
end

ngens(f::Free) = length(f.gens)

gens(f::Free) = f.gens

Base.show(io::IO, f::Free) =
    show(IOContext(io, :slp_free_gens => gens(f)), f.x)

evaluate(f::Free, xs) = evaluate(gens(f), f.x, xs)

# check compatibility and return the biggest of the two gens arrays
function gens(x::Free, y::Free)
    if length(gens(y)) < length(gens(x))
        x, y = y, x
    end
    gx, gy = gens(x), gens(y)
    gx == view(gy, eachindex(gx)) || throw(ArgumentError(
        "incompatible symbols"))
    gy
end

# TODO: must they also have the same gens?
Base.:(==)(x::Free, y::Free) = x.x == y.x


### unary/binary ops

+(x::Free, y::Free) = Free(x.x + y.x, gens(x, y))
-(x::Free, y::Free) = Free(x.x - y.x, gens(x, y))
*(x::Free, y::Free) = Free(x.x * y.x, gens(x, y))

-(x::Free) = Free(-x.x, gens(x))
^(x::Free, e::Integer) = Free(x.x^e, gens(x))

Base.literal_pow(::typeof(^), p::Free, ::Val{e}) where {e} = p^e


#### adhoc

+(x::Free, y) = Free(x.x + y, gens(x))
+(x, y::Free) = Free(x + y.x, gens(y))

-(x::Free, y) = Free(x.x - y, gens(x))
-(x, y::Free) = Free(x - y.x, gens(y))

*(x::Free, y) = Free(x.x * y, gens(x))
*(x, y::Free) = Free(x * y.x, gens(y))


## Lazy

gens(l::Lazy) = sort!(unique!(pushgens!(Symbol[], l)::Vector{Symbol}))

Base.:(==)(k::Lazy, l::Lazy) = false

Lazy(x::Lazy) = x
Lazy(x::AbstractSLProgram) = compile(Lazy, x)
Lazy(x) = Const(x)

evaluate(l::Lazy, xs) = evaluate(gens(l), l, xs)
# TODO: remove the 3-arg evaluate methods?


### Const

struct Const{T} <: Lazy
    c::T

    # TODO: this is a hack, delete ASAP
    Const{T}(x::AbstractSLProgram) where {T} = new{T}(x)
    Const(x) = new{typeof(x)}(x)
end

Const(x::AbstractSLProgram) = Const{typeof(x)}(x)


Base.show(io::IO, c::Const) = print(io, c.c)

pushgens!(gs, c::Const) = gs
constantstype(l::Const{T}) where {T} = T

Base.:(==)(k::Const, l::Const) = k.c == l.c

evaluate(gs, c::Const, xs) = c.c

maxinput(c::Const) = 0


### Input

struct Input <: Lazy
    n::Int
end

function Base.show(io::IO, i::Input)
    syms = io[:slp_free_gens]
    print(io, syms[i.n])
end

evaluate(gs, i::Input, xs) = xs[i.n]

maxinput(i::Input) = i.n

Base.:(==)(i::Input, j::Input) = i.n == j.n


### Gen

struct Gen <: Lazy
    g::Symbol
end

Base.show(io::IO, g::Gen) = print(io, g.g)

pushgens!(gs, g::Gen) =
    if findfirst(==(g.g), gs) === nothing
        push!(gs, g.g)
    else
        gs
    end

constantstype(l::Gen) = Union{}

Base.:(==)(k::Gen, l::Gen) = k.g == l.g

evaluate(gs, g::Gen, xs) = xs[findfirst(==(g.g), gs)]

maxinput(g::Gen) = throw(ArgumentError("logic error: Gen not allowed in Free"))


### Plus

struct Plus <: Lazy
    xs::Vector{Lazy}
end

Plus(xs::Lazy...) = Plus(collect(Lazy, xs))

function Base.show(io::IO, p::Plus)
    print(io, '(')
    join(io, p.xs, " + ")
    print(io, ')')
end

pushgens!(gs, p::Plus) = foldl(pushgens!, p.xs, init=gs)

constantstype(p::Plus) =
    mapreduce(constantstype, typejoin, p.xs, init=Union{})

Base.:(==)(k::Plus, l::Plus) = k.xs == l.xs

evaluate(gs, p::Plus, xs) = mapreduce(q -> evaluate(gs, q, xs), +, p.xs)

maxinput(p::Plus) = mapreduce(maxinput, max, p.xs)


### Minus

struct Minus <: Lazy
    p::Lazy
    q::Lazy
end

Base.show(io::IO, p::Minus) = print(io, '(', p.p, " - ", p.q, ')')

pushgens!(gs, l::Minus) = pushgens!(pushgens!(gs, l.p), l.q)

constantstype(m::Minus) = typejoin(constantstype(m.p), constantstype(m.q))

Base.:(==)(k::Minus, l::Minus) = k.p == l.p && k.q == l.q

evaluate(gs, p::Minus, xs) = evaluate(gs, p.p, xs) - evaluate(gs, p.q, xs)

maxinput(m::Minus) = max(maxinput(m.p), maxinput(m.q))


### UniMinus

struct UniMinus <: Lazy
    p::Lazy
end

Base.show(io::IO, p::UniMinus) = print(io, "(-", p.p, ')')

pushgens!(gs, l::UniMinus) = pushgens!(gs, l.p)

constantstype(p::UniMinus) = constantstype(p.p)

Base.:(==)(k::UniMinus, l::UniMinus) = k.p == l.p

evaluate(gs, p::UniMinus, xs) = -evaluate(gs, p.p, xs)

maxinput(p::UniMinus) = maxinput(p.p)


### Times

struct Times <: Lazy
    xs::Vector{Lazy}
end

Times(xs::Lazy...) = Times(collect(Lazy, xs))

function Base.show(io::IO, p::Times)
    print(io, '(')
    join(io, p.xs)
    print(io, ')')
end

pushgens!(gs, p::Times) = foldl(pushgens!, p.xs, init=gs)

constantstype(p::Times) =
    mapreduce(constantstype, typejoin, p.xs, init=Union{})

Base.:(==)(k::Times, l::Times) = k.xs == l.xs

evaluate(gs, p::Times, xs) = mapreduce(q -> evaluate(gs, q, xs), *, p.xs)

maxinput(p::Times) = mapreduce(maxinput, max, p.xs)


### Exp

struct Exp <: Lazy
    p::Lazy
    e::Int
end

Base.show(io::IO, p::Exp) = print(io, p.p, '^', p.e)

pushgens!(gs, l::Exp) = pushgens!(gs, l.p)

constantstype(p::Exp) = constantstype(p.p)

Base.:(==)(k::Exp, l::Exp) = k.p == l.p && k.e == l.e

Base.literal_pow(::typeof(^), p::Lazy, ::Val{e}) where {e} = Exp(p, e)

evaluate(gs, p::Exp, xs) = evaluate(gs, p.p, xs)^p.e

maxinput(e::Exp) = maxinput(e.p)


### Decision

struct Decision <: Lazy
    ps::Vector{Tuple{Lazy,Int}}
end

test(p::Lazy, n) = Decision(Tuple{Lazy,Int}[(p, n)])

Base.show(io::IO, d::Decision) =
    join(io, ("test($p, $n)" for (p, n) in d.ps), " & ")

constantstype(l::Decision) =
    mapreduce(constantstype∘first, typejoin, l.ps, init=Union{})

pushgens!(gs, l::Decision) =
    foldl((gs, d) -> pushgens!(gs, first(d)), l.ps, init=gs)

function Base.:(&)(p::Decision, q::Decision)
    d = Decision(copy(p.ps))
    append!(d.ps, q.ps)
    d
end

Base.:(==)(p::Decision, q::Decision) = p.ps == q.ps

function evaluate(gs, p::Decision, xs)
    (d, i), rest = Iterators.peel(p.ps) # p.ps should never be empty
    res = test(evaluate(gs, d, xs), i)
    res === false && return false
    for (d, i) in rest
        r = test(evaluate(gs, d, xs), i)
        r === false && return false
        res &= r
    end
    res
end

maxinput(p::Decision) = mapreduce(x -> maxinput(x[1]), max, p.ps)


### binary ops

#### +

+(x::Lazy, y::Lazy) = Plus(x, y)

function +(x::Plus, y::Lazy)
    p = Plus(copy(x.xs))
    push!(p.xs, y)
    p
end

function +(x::Lazy, y::Plus)
    p = Plus(copy(y.xs))
    pushfirst!(p.xs, x)
    p
end

function +(x::Plus, y::Plus)
    p = Plus(copy(x.xs))
    append!(p.xs, y.xs)
    p
end


#### -

-(p::Lazy, q::Lazy) = Minus(p, q)
-(p::Lazy) = UniMinus(p)


#### *

*(x::Lazy, y::Lazy) = Times(x, y)

function *(x::Times, y::Lazy)
    p = Times(copy(x.xs))
    push!(p.xs, y)
    p
end

function *(x::Lazy, y::Times)
    p = Times(copy(y.xs))
    pushfirst!(p.xs, x)
    p
end

function *(x::Times, y::Times)
    p = Times(copy(x.xs))
    append!(p.xs, y.xs)
    p
end


#### ^

^(x::Lazy, e::Integer) = Exp(x, Int(e))


### adhoc binary ops

*(x, y::Lazy) = Const(x) * y
*(x::Lazy, y) = x * Const(y)

+(x, y::Lazy) = Const(x) + y
+(x::Lazy, y) = x + Const(y)

-(x, y::Lazy) = Const(x) - y
-(x::Lazy, y) = x - Const(y)


## compile to SLProgram

# TODO: this is legacy, only for tests
SLProgram(l::Lazy) = compile(SLProgram, l)
SLProgram{T}(l::Lazy) where {T} = compile(SLProgram{T}, l)

compile(::Type{SLProgram}, l::Lazy) = compile(SLProgram{constantstype(l)}, l)

function compile(::Type{SLProgram{T}}, l::Lazy, gs=gens(l)) where T
    p = SLProgram{T}()
    i = pushlazy!(p, l, gs)
    pushfinalize!(p, i)
end

pushlazy!(p::SLProgram, l::Const, gs) = pushconst!(p, l.c)

pushlazy!(p::SLProgram, l::Gen, gs) = input(findfirst(==(l.g), gs))

function pushlazy!(p, l::Union{Plus,Times}, gs)
    # TODO: handle isempty(p.xs) ?
    op = l isa Plus ? plus : times
    x, xs = Iterators.peel(l.xs)
    i = pushlazy!(p, x, gs)
    for x in xs
        j = pushlazy!(p, x, gs)
        i = pushop!(p, op, i, j)
    end
    i
end

function pushlazy!(p, l::Minus, gs)
    i = pushlazy!(p, l.p, gs)
    j = pushlazy!(p, l.q, gs)
    pushop!(p, minus, i, j)
end

pushlazy!(p, l::UniMinus, gs) = pushop!(p, uniminus, pushlazy!(p, l.p, gs))

pushlazy!(p, l::Exp, gs) =
    pushop!(p, exponentiate, pushlazy!(p, l.p, gs), intarg(l.e))

function pushlazy!(p, l::Decision, gs)
    local k
    for (x, i) in l.ps
        d = pushlazy!(p, x, gs)
        k = pushop!(p, decision, d, pushint!(p, i))
    end
    k
end
