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

