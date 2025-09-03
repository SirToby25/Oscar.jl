###############################################################################
#
#  Construction
#
###############################################################################

function algebraic_system(S::PolyT) where {PolyT <: ActionPolyRing}
  return AlgebraicActionPolySystem{PolyT}(S)
end

function algebraic_system(eqs::Vector{PolyT}, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  if length(eqs) > 0
    f = eqs[1]
  elseif length(ineqs) > 0
    f = ineqs[1]
  else
    @req false "An empty algebraic system over the ring S is created using algebraic_system(S)"
  end
  for g in vcat(eqs, ineqs)
    check_parent(f, g)
  end
  S = parent(f)
  return AlgebraicActionPolySystem{typeof(S)}(S, unique!(filter(!=(0), eqs)), unique!(filter(ineq -> total_degree(ineq) != 0, ineqs)))
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
#  Getters & Setters
#
###############################################################################

parent(sys::AlgebraicActionPolySystem) = sys.ring
equations(sys::AlgebraicActionPolySystem{PolyT}) where {PolyT <: ActionPolyRing} = sys.eqs::Vector{elem_type(PolyT)}
inequations(sys::AlgebraicActionPolySystem{PolyT}) where {PolyT <: ActionPolyRing} = sys.ineqs::Vector{elem_type(PolyT)}

function set_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  sys.eqs = unique!(filter(!=(0), eqs))
end

function set_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  sys.ineqs = unique!(filter(ineq -> total_degree(ineq) != 0, ineqs))
end

###############################################################################
#
#  Adding and removing
#
###############################################################################

function add_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  unique!(vcat!(sys.eqs, filter(!=(0), eqs)))
end

function add_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  unique!(vcat!(sys.ineqs, filter(ineq -> total_degree(ineq) != 0, ineqs)))
end

function remove_equations!(sys::AlgebraicActionPolySystem, eqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(eq -> parent(eq) === parent(sys), eqs) "Wrong parent"
  filter!(eq -> !(eq in eqs), sys.eqs)
end

function remove_inequations!(sys::AlgebraicActionPolySystem, ineqs::Vector{PolyT}) where {PolyT <: ActionPolyRingElem}
  @req all(ineq -> parent(ineq) === parent(sys), ineqs) "Wrong parent"
  filter!(ineq -> !(ineq in ineqs), sys.ineqs)
end

###############################################################################
#
#  Simple algebraic systems
#
###############################################################################

function is_simple(sys::AlgebraicActionPolySystem)
  return false
end
