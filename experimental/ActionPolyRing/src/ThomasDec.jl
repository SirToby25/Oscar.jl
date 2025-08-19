@doc"""
    initial(p::ActionPolyRingElem)

Return the initial of the polynomial `p`, i.e. the leading coefficient of `p` regarded as a univariate polynomial in its leader.
"""
function initial(apre::ActionPolyRingElem)
  if is_constant(apre)
    return apre
  end
  return divexact(leading_term(apre), leader(apre)^degree(apre, leader(apre)); check = true)
end

@doc raw"""
    leader(p::ActionPolyRingElem)

Return the leader of the polynomial `p`, that is the largest variable with respect to the ranking of `parent(p)`. If `p` is constant, an error is raised.
"""
function leader(apre::ActionPolyRingElem)
  @req !is_constant(apre) "A constant polynomial has no leader"
  if is_univariate(apre)
    return vars(apre)[1]
  end
  return max(vars(apre)...)
end

@doc raw"""
    resultant(f::ActionPolyRingElem, g::ActionPolyRingElem, v::ActionPolyRingElem)

Return the resultant of `f` and `g` regarded as univariate polynomial in the jet variable `v`. The jet variable can also be specified its jet index or its position in `gens(parent(f))`.
"""
function resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, var::ActionPolyRingElem{T}) where {T}
  check_parent(apre1, apre2) && check_parent(apre1, var)
  __update_internals!(var)
  @req is_gen(var) "Not a variable"
  return resultant(apre1, apre2, __vtj(parent(var))[var])
end

function resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, i::Int, idx::Vector{Int}) where {T}
  check_parent(apre1, apre2)
  __update_internals!(apre1), __update_internals!(apre2)
  apr = parent(apre1)
  @req __is_valid_jet(apr, i, idx) "Invalid jet variable"
  jtv = __jtv(apr)
  if haskey(jtv, (i, idx))
    return apr(tmp_resultant(data(apre1), data(apre2), data(jtv[(i, idx)])))
  end
  if is_zero(apre1) || is_zero(apre2)
    return zero(apr)
  end
  return one(apr)
end

resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, jet_idx::Tuple{Int,Vector{Int}}) where {T} = resultant(apre1, apre2, jet_idx...)

resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, i::Int) where {T} = resultant(apre1, apre2, gen(parent(apre1), i))

#TODO: Remove once resultant is released in Hecke
function tmp_resultant(f::UniversalPolyRingElem, g::UniversalPolyRingElem, x::UniversalPolyRingElem)
  check_parent(f, g) && check_parent(f, x)
  up = parent(x)
  @req is_gen(x) "Not a variable in the universal polynomial ring"
  res = resultant(data(f), data(g), findfirst(==(x), gens(up)))
  return up(collect(coefficients(res)), collect(exponents(res)))
end

function derivative(apre::ActionPolyRingElem{T}, var::ActionPolyRingElem{T}) where {T}
  check_parent(apre, var)
  __update_internals!(var)
  @req is_gen(var) "Not a variable"
  return derivative(apre, __vtj(parent(var))[var])
end

function derivative(apre::ActionPolyRingElem, i::Int, idx::Vector{Int})
  __update_internals!(apre)
  apr = parent(apre)
  @req __is_valid_jet(apr, i, idx) "Invalid jet variable"
  jtv = __jtv(apr)
  if haskey(jtv, (i, idx))
    return apr(derivative(data(apre), data(jtv[(i, idx)])))
  end
  return zero(apr)
end

derivative(apre::ActionPolyRingElem, jet_idx::Tuple{Int,Vector{Int}}) = derivative(apre, jet_idx...)

derivative(apre::ActionPolyRingElem, i::Int) = derivative(apre, gen(parent(apre), i))

@doc raw"""
    discriminant(p::ActionPolyRingElem)

Return the discriminant of `p`.
"""
function discriminant(p::ActionPolyRingElem)
  ld = leader(p)
  d = degree(p, ld)
  resul = resultant(p, derivative(p, ld), ld)
  return (-1)^(divexact(d*(d-1), 2)) * divexact(resul, initial(p))
end
