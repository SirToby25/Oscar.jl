
###############################################################################
#
#  Types for Thomas decompositions
#
###############################################################################

# Represents an algebraic system or a branch in the Thomas decomposition tree
struct __AlgebraicSystem{P <: MPolyRingElem}
  eqs::Vector{P}
  ineqs::Vector{P}
end

# Represents the final output
struct __AlgebraicThomasDecomposition{P <: MPolyRingElem}
  systems::Vector{__AlgebraicSystem{P}}
end

###############################################################################
#
#  Thomas type helpers
#
###############################################################################

# For inplace killing inconsistent systems
function __empty!(sys::__AlgebraicSystem{P}) where {P <: MPolyRingElem}
  sys.eqs = empty!(sys.eqs)
  sys.ineqs = empty!(sys.ineqs)
  return sys
end

###############################################################################
#
#  Main functions
#
###############################################################################

thomas_decomposition(E::AbstractVector{P}, I::AbstractVector{P}) where {P <: MPolyRingElem} = thomas_decomposition(collect(E), collect(I))

function thomas_decomposition(E::Vector{P}, I::Vector{P}) where {P <: MPolyRingElem}
  queue = [__AlgebraicSystem{P}(E, I)]
  finished_systems = __AlgebraicSystem{P}[]

  while !is_empty(queue)
    current_sys = popfirst!(queue)

    is_consistent, current_sys = __is_consistent_after_preprocessing!(current_sys)
    # Preprocessing
    !__is_consistent && continue

    # TODO: Actually split current_sys

    push!(finished_systems, current_sys)
  end

  return __AlgebraicThomasDecomposition(finished_systems)
end

###############################################################################
#
#  Thomas decompositions helpers
#
###############################################################################

# Strips an algebraic system of constant equations and inequations
function __is_consistent_after_preprocessing!(sys::__AlgebraicSystem{P}) where {P <: MPolyRingElem}

  filter(!is_zero, sys.eqs)
  if any(!is_constant(sys.eqs))
    sys = __empty!(sys)
    return (false, sys)
  end

  if any(is_zero(sys.ineqs))
    sys = __empty!(sys)
    return (false, sys)
  end
  filter(!is_constant, sys.ineqs)

  # Further stuff

  return (true, sys)
end
