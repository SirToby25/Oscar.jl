###############################################################################
#
#  Discriminant and its required methods
#
###############################################################################

function resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, var::ActionPolyRingElem)
  check_parent(r1, r2) && check_parent(r1, var)
  @req is_gen(var) "Not a jet variable"
  return resultant(r1, r2, __vtj(parent(var))[var])
end

@doc raw"""
    resultant(f::ActionPolyRingElem, g::ActionPolyRingElem, i::Int, jet::Vector{Int})

Return the resultant of `f` and `g` regarded as univariate polynomials in the jet variable specified by `i` and
`jet`. This method allows all versions described in [Specifying jet variables](@ref specifying_jet_variables).
"""
function resultant(r1::ActionPolyRingElem, r2::ActionPolyRingElem, i::Int, jet::Vector{Int})
  check_parent(r1, r2)
  S = parent(r1)
  @req __is_valid_jet(S, i, jet) "Invalid jet variable"
  jtv = __jtv(S)
  if haskey(jtv, (i, jet))
    return S(resultant(data(r1), data(r2), data(jtv[(i, jet)])))
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
  if is_constant(p)
    return zero(parent(p))
  end

  ld = leader(p)
  
  if degree(p, ld) % 4 in [0,1]
    return divexact(resultant(p, derivative(p, ld), ld), initial(p))
  end
  
  return -divexact(resultant(p, derivative(p, ld), ld), initial(p))
end

###############################################################################
#
#  Univariate coefficients 
#
###############################################################################

function univariate_coefficients(r::ActionPolyRingElem, var::ActionPolyRingElem)
  check_parent(r, var)
  @req is_gen(var) "Not a jet variable"
  return univariate_coefficients(r, __vtj(parent(var))[var])
end
  
@doc raw"""
    univariate_coefficients(p::ActionPolyRingElem, i::Int, jet::Vector{Int}) 

Return the coefficient vector of `p` regarded as a univariate polynomial in the jet variable specified by `i` and
`jet`, leading with the constant coefficient. This method allows all versions described in
[Specifying jet variables](@ref specifying_jet_variables).
"""
function univariate_coefficients(r::ActionPolyRingElem, i::Int, jet::Vector{Int})
  d = degree(r, i, jet)
  if d == 0
    return [r]
  end
  res = [zero(r) for _ in 1:d+1]
  var = __jtv(parent(r))[(i, jet)]
  v_idx = var_index(var)
  for (t, e) in zip(terms(r), exponents(r)) 
    @inbounds res[e[v_idx] + 1] += remove(t, var)[2]
  end
  return res
end

univariate_coefficients(r::ActionPolyRingElem, jet_idx::Tuple{Int, Vector{Int}}) = univariate_coefficients(r, jet_idx...)
univariate_coefficients(r::ActionPolyRingElem, i::Int) = univariate_coefficients(r, gen(parent(r), i))

###############################################################################
#
#  Evaluation
#
###############################################################################

# We let UnivPoly handle the calculations, so we need to permute argument vectors
function __permute_vals(S::ActionPolyRing, A::Vector{T}) where {T}
  perm = invperm(__perm_for_sort(S))
  n = nvars(S)
  m = length(A) 
  m > n && error("Too many values")
  return vcat(A, [zero(T) for _ in 1:(n - m)])[perm]
end

# Full substitutions with zero padding
evaluate(a::ActionPolyRingElem{T}, A::Vector{T}) where {T <: RingElement} = evaluate(data(a), __permute_vals(parent(a), A))
evaluate(a::ActionPolyRingElem{T}, A::Vector{V}) where {T <: RingElement, V <: Union{Integer, Rational, AbstractFloat}} = evaluate(data(a), __permute_vals(parent(a), A))
evaluate(a::ActionPolyRingElem{T}, A::Vector{V}) where {T <: RingElement, V <: RingElement} = evaluate(data(a), __permute_vals(parent(a), A))

(a::ActionPolyRingElem{T})() where {T <: RingElement} = evaluate(a, T[])
(a::ActionPolyRingElem{T})(vals::T...) where {T <: RingElement} = evaluate(a, collect(vals))
(a::ActionPolyRingElem{T})(val::V, vals::V...) where {T <: RingElement, V <: Union{Integer, Rational, AbstractFloat}} = evaluate(a, [val, vals...])
(a::ActionPolyRingElem{T})(vals::Union{NCRingElem, RingElement}...) where {T <: RingElement} = evaluate(a, collect(vals))

# Partial substitutions
function evaluate(a::ActionPolyRingElem{T}, vars::Vector{Int}, vals::Vector{V}) where {T <: RingElement, V <: RingElement}
    S = parent(a)
  per = __perm_for_sort(S)
  return S(evaluate(data(a), map(x -> per[x], vars), vals))
end

evaluate(a::PolyT, vars::Vector{PolyT}, vals::Vector{V}) where {PolyT <: ActionPolyRingElem, V <: RingElement} = parent(a)(evaluate(a, [var_index(x) for x in vars], vals))

###############################################################################
#
#  Pseudo reduction
#
###############################################################################

@doc raw"""
    is_reduced(r::ActionPolyRingElem, g::ActionPolyRingElem)

Return true if the polynomial `r` is reduced with respect to `g`. This means that either `r` is constant or the degree of `r` is strictly smaller than the degree of `g`, regarding both polynomials as univariate in the leader of `g`.
"""
function is_reduced(r::PolyT, g::PolyT) where {PolyT <: ActionPolyRingElem}
  check_parent(r, g)
  @req !is_constant(g) "Cannot reduce with respect to a constant polynomial"
  if is_constant(r)
    return true
  end
  ld = leader(g)
  return degree(r, ld) < degree(g, ld)
end

@doc raw"""
    is_reduced(r::ActionPolyRingElem, G::Vector{ActionPolyRingElem})

Return true if the polynomial `r` is reduced with respect to `G`. This means that either `r` is constant or it is reduced with respect to all elements of `G` and all coefficients of `r` regarded as a univariate polynomial in its leader are reduced with respect to `G`.
"""
function is_reduced(r::PolyT, G::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(g -> !is_constant(g), G) "Cannot reduce with respect to a constant polynomial"
  if is_constant(r)
    return true
  end
  for g in G
    is_reduced(r, g) || return false
  end
  for c in univariate_coefficients(r, leader(r))
    if is_constant(c)
      continue
    end
    for g in G
      is_reduced(c, g) || return false
    end
  end
  return true
end

function reduce(r::PolyT, g::PolyT) where {PolyT <: ActionPolyRingElem}
  check_parent(r, g)
  return __aux_reduce!(deepcopy(r), [g])
end

@doc raw"""
    reduce(r::ActionPolyRingElem, G::Vector{ActionPolyRingElem})

Return an tuple `(r', b)` such that `r'` is reduced with respect to `G` and $b*r$ and $r'$ are in the same residue class $mod G$. If `G` contains only a single element in may be passed as second element without wrapping it into a vector. See also [`is_reduced`](@ref).
"""
function reduce(r::PolyT, G::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  for g in G
    check_parent(r, g)
  end
  return __aux_reduce!(deepcopy(r), G)
end

function __aux_reduce!(r::PolyT, G::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  b = one(parent(r))
  prod1 = zero(r)
  prod2 = zero(r)

  if !is_constant(r)
    # Leader-reduction loop
    while true
      ld_r = leader(r)
      d = degree(r, ld_r)

      g_found = nothing
      for g in G
        if leader(g) == ld_r && degree(r, ld_r) >= degree(g, ld_r)
          g_found = g
          break
        end
      end

      g_found === nothing && break  # No leader reduction possible 

      g = g_found

      # r = initial(g) * r - initial(r) * ld_r^(d - degree(g, ld_r)) * g
      mul!(prod1, initial(g), r)
      mul!(prod2, g, ld_r^(d - degree(g, ld_r)))
      mul!(prod2, prod2, initial(r))
      sub!(r, prod1, prod2)

      # b = initial(g) * b
      mul!(b, initial(g), b)

      if is_constant(r)
        return (r, b)
      end
    end

    # Coefficient-reduction loop 
    ld_r = leader(r)
    for (i, c) in enumerate(univariate_coefficients(r, ld_r))
      if !is_reduced(c, G)
        tmp_r, tmp_b = reduce(c, G)

        # r = tmp_b * r - (tmp_b * c - tmp_r) * ld_r^(i - 1)
        mul!(prod1, tmp_b, r)
        mul!(prod2, tmp_b, c)
        sub!(prod2, prod2, tmp_r)
        mul!(prod2, prod2, ld_r^(i - 1))
        sub!(r, prod1, prod2)

        # b = tmp_b * b
        mul!(b, tmp_b, b)
      end
    end
  end

  return (r, b)
end

