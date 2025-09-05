###############################################################################
#
#  Construction
#
###############################################################################

function algebraic_system(S::PolyT) where {PolyT <: ActionPolyRing}
  return AlgebraicActionPolySystem{PolyT}(S)
end

function algebraic_system(eqs::Vector{PolyT}, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  le = length(eqs)
  li = length(ineqs)
  @req le + li > 0 "An empty algebraic system over the ring S is created using algebraic_system(S)"

  f = le > 0 ? first(eqs) : first(ineqs)
  eqs_and_ineqs = Vector{Tuple{PolyT, Bool}}(undef, le + li)

  @inbounds for i in 1:le
    g = eqs[i]
    check_parent(f, g)
    eqs_and_ineqs[i] = (g, true)
  end
  @inbounds for j in 1:li
    g = ineqs[j]
    check_parent(f, g)
    eqs_and_ineqs[le + j] = (g, false)
  end
  sort!(eqs_and_ineqs; by = x -> (leader(x[1]), degree(x[1], leader(x[1]))), rev = true)
  return AlgebraicActionPolySystem{parent_type(f)}(parent(f), eqs_and_ineqs, findall(x -> x[2], eqs_and_ineqs), findall(x -> !x[2], eqs_and_ineqs))
end

###############################################################################
#
#  Types
#
###############################################################################

parent_type(::Type{AlgebraicActionPolySystem{PolyT}}) where {PolyT <: ActionPolyRing} = PolyT
base_ring(sys::AlgebraicActionPolySystem) = base_ring(parent(sys))
base_ring_type(::Type{AlgebraicActionPolySystem{PolyT}}) where {PolyT <: ActionPolyRing} = base_ring_type(PolyT)

###############################################################################
#
#  Getters and basic manipulation
#
###############################################################################

parent(sys::AlgebraicActionPolySystem) = sys.ring
__eqs_and_ineqs(sys::AlgebraicActionPolySystem{PolyT}) where {PolyT <: ActionPolyRing} = sys.eqs_and_ineqs::Vector{Tuple{elem_type(PolyT), Bool}}
__eq_idxs(sys::AlgebraicActionPolySystem) = sys.eq_idxs
__ineq_idxs(sys::AlgebraicActionPolySystem) = sys.ineq_idxs

equations(sys::AlgebraicActionPolySystem) = [__eqs_and_ineqs(sys)[i][1] for i in __eq_idxs(sys)]
inequations(sys::AlgebraicActionPolySystem) = [__eqs_and_ineqs(sys)[i][1] for i in __ineq_idxs(sys)]

function set_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  __set_helper!(sys, unique!(filter!(!=(0), copy(eqs))), true) 
  return equations(sys)
end

function set_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  __set_helper!(sys, unique!(filter!(ineq -> total_degree(ineq) != 0, copy(ineqs))), false) 
  return inequations(sys)
end

function __set_helper!(sys::AlgebraicActionPolySystem, v::Vector{PolyT}, is_eq::Bool) where {PolyT <: ActionPolyRingElem}
  write_idx = 1
  for read_idx in 1:length(sys.eqs_and_ineqs)
    if xor(is_eq, sys.eqs_and_ineqs[read_idx][2])
      sys.eqs_and_ineqs[write_idx] = sys.eqs_and_ineqs[read_idx]
      write_idx += 1
    end
  end
  resize!(sys.eqs_and_ineqs, write_idx - 1)
  for elt in v
    push!(sys.eqs_and_ineqs, (elt, is_eq))
  end

  sort!(sys.eqs_and_ineqs; by = x -> (leader(x[1]), degree(x[1], leader(x[1]))), rev = true)
  __compute_eq_and_ineq_idxs!(sys)
end

function __compute_eq_and_ineq_idxs!(sys::AlgebraicActionPolySystem)
  sys.eq_idxs = findall(x -> x[2], sys.eqs_and_ineqs)
  sys.ineq_idxs = findall(x -> !x[2], sys.eqs_and_ineqs)
end

###############################################################################
#
#  Equation maintainence
#
###############################################################################

function add_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  __set_helper!(sys, unique!(vcat(equations(sys), filter(!=(0), eqs))), true)
  return equations(sys)
end

function add_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  __set_helper!(sys, unique!(vcat(inequations(sys), filter(ineq -> total_degree(ineq) != 0, ineqs))), false)
  return inequations(sys)
end

function remove_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  filter!(x -> !x[2] || !(x[1] in eqs), sys.eqs_and_ineqs)
  __compute_eq_and_ineq_idxs!(sys)
  return equations(sys)
end

function remove_equations!(sys::AlgebraicActionPolySystem, idxs::Vector{Int})
  deleteat!(sys.eqs_and_ineqs, __eq_idxs(sys)[idxs])
  __compute_eq_and_ineq_idxs!(sys)
  return equations(sys)
end

function remove_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  filter!(x -> x[2] || !(x[1] in ineqs), sys.eqs_and_ineqs)
  __compute_eq_and_ineq_idxs!(sys)
  return inequations(sys)
end

function remove_inequations!(sys::AlgebraicActionPolySystem, idxs::Vector{Int})
  deleteat!(sys.eqs_and_ineqs, __ineq_idxs(sys)[idxs])
  __compute_eq_and_ineq_idxs!(sys)
  return inequations(sys)
end

###############################################################################
#
#  Simple algebraic systems
#
###############################################################################

@doc raw"""
    is_simple(sys::AlgebraicActionPolySystem) -> Bool

Return true if `sys` is simple. An algebraic system is simple, if its solution
set $S$ in the algebraic closure of its base ring is non-empty and
additionally, if the following three conditions are satisfied:
  - The system is triangular, i.e. the leaders of all equations and inequations
    are pairwise distinct
  - The initial of each equation and inequation has no zeros in the projection 
    of $S$ onto the coordinates that correspond to variables that are strictly
    smaller than the leader of the equation or inequation
  - The discriminant of each equation and inequation has no zeros in the projection 
    of $S$ onto the coordinates that correspond to variables that are strictly
    smaller than the leader of the equation or inequation
"""
function is_simple(sys::AlgebraicActionPolySystem)
  eqs = equations(sys)
  ineqs = inequations(sys)
  for eq in eqs
    !is_constant(eq) || return false
  end
  for ineq in ineqs
    !is_constant(ineq) || return false
  end
  !allunique([leader(x[1]) for x in __eqs_and_ineqs(sys)]) || return false

end
