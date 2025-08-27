###############################################################################
#
#  Discriminant and its required methods
#
###############################################################################

@doc raw"""
    resultant(f::ActionPolyRingElem, g::ActionPolyRingElem, v::ActionPolyRingElem)

Return the resultant of `f` and `g` regarded as univariate polynomial in the jet variable `v`. The jet variable can also be specified its jet index or its position in `gens(parent(f))`.
"""
function resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, var::ActionPolyRingElem{T}) where {T}
  check_parent(apre1, apre2) && check_parent(apre1, var)
  @req is_gen(var) "Not a variable"
  return resultant(apre1, apre2, __vtj(parent(var))[var])
end

function resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, i::Int, idx::Vector{Int}) where {T}
  check_parent(apre1, apre2)
  apr = parent(apre1)
  @req __is_valid_jet(apr, i, idx) "Invalid jet variable"
  jtv = __jtv(apr)
  if haskey(jtv, (i, idx))
    return apr(resultant(data(apre1), data(apre2), data(jtv[(i, idx)])))
  end
  if is_zero(apre1) || is_zero(apre2)
    return zero(apr)
  end
  return one(apr)
end

resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, jet_idx::Tuple{Int,Vector{Int}}) where {T} = resultant(apre1, apre2, jet_idx...)

resultant(apre1::ActionPolyRingElem{T}, apre2::ActionPolyRingElem{T}, i::Int) where {T} = resultant(apre1, apre2, gen(parent(apre1), i))

@doc raw"""
    discriminant(p::ActionPolyRingElem)

Return the discriminant of `p`.
"""
function discriminant(p::ActionPolyRingElem)
  ld = leader(p)
  d = degree(p, ld)
  resul = resultant(p, derivative(p, ld), ld)
  return (-1)^(divexact(d * (d - 1), 2)) * divexact(resul, initial(p))
end

