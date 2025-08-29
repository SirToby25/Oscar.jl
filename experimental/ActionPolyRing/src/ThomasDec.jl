###############################################################################
#
#  Discriminant and its required methods
#
###############################################################################

@doc raw"""
    resultant(f::ActionPolyRingElem, g::ActionPolyRingElem, v::ActionPolyRingElem)

Return the resultant of `f` and `g` regarded as univariate polynomial in the jet variable `v`. The jet variable can also be specified its jet index or its position in `gens(parent(f))`.
"""
function resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, var::ActionPolyRingElem)
  check_parent(r1, r2) && check_parent(r1, var)
  @req is_gen(var) "Not a variable"
  return resultant(r1, r2, __vtj(parent(var))[var])
end

function resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, i::Int, idx::Vector{Int})
  check_parent(r1, r2)
  S = parent(r1)
  @req __is_valid_jet(S, i, idx) "Invalid jet variable"
  jtv = __jtv(S)
  if haskey(jtv, (i, idx))
    return S(resultant(data(r1), data(r2), data(jtv[(i, idx)])))
  end
  if is_zero(r1) || is_zero(r2)
    return zero(S)
  end
  return one(S)
end

resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, jet_idx::Tuple{Int,Vector{Int}}) = resultant(r1, r2, jet_idx...)

resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, i::Int) = resultant(r1, r2, gen(parent(r1), i))

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

###############################################################################
#
#  Discriminant and its required methods
#
###############################################################################

function univariate_coefficients(r::ActionPolyRingElem, var::ActionPolyRingElem)
  check_parent(r, var)
  @req is_gen(var) "Not a variable"
  return univariate_coefficients(r, __vtj(parent(var))[var])
end
  
function univariate_coefficients(r::ActionPolyRingElem, i, idx::Vector{Int})
  d = degree(r, i, idx)
  if d == 0
    return [r]
  end
  S = parent(r)
  jtv = __jtv(S)
  var = jtv[(i, idx)]
  v_idx = var_index(var)
  return
end

univariate_coefficients(r::ActionPolyRingElem, jet_idx::Tuple{Int, Vector{Int}}) = univariate_coefficients(r, jet_idx...)

univariate_coefficients(r::ActionPolyRingElem, i::Int) = univariate_coefficients(r, gen(parent(r), i))

function initial(apre::ActionPolyRingElem)
  if is_constant(apre)
    return apre
  end
  res = parent(apre)()
  ld = leader(apre)
  ld_ind = var_index(ld)
  d = degree(apre, ld_ind)
  for (t,e) in zip(terms(apre), exponents(apre))
    if e[ld_ind] < d
      break
    end
    res += remove(t, ld)[2] 
  end
  return res
end

###############################################################################
#
#  Pseudo reduction
#
###############################################################################

function is_reduced(r::ActionPolyRingElem, g::ActionPolyRingElem)
  check_parent(r, g)
  @req !is_constant(g) "Cannot reduce with respect to a constant polynomial"
  if is_constant(r)
    return true
  end
  ld = leader(g)
  return degree(r, ld) < degree(g, ld)
end

function is_reduced(r::ActionPolyRingElem, G::Vector{ActionPolyRingElem})
  for g in G
    is_reduced(r, g) || return false
  end
  for c in univariate_coefficients(r)
    for g in G
      is_reduced(c, g) || return false
    end
  end
  return true
end

function reduce(r::ActionPolyRingElem, G::Vector{ActionPolyRingElem})
  all(g -> check_parent(r,g), G) 
  res = r
  b = one(dpr)
  if !is_constant(res)
    
  end
  return (res, b)
end

