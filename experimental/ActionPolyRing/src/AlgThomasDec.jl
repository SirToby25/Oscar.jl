
###############################################################################
#
#  Types for Thomas decompositions
#
###############################################################################

# Represents an algebraic system or a branch in the Thomas decomposition tree
struct __AlgebraicSystem{P <: MPolyRingElem}
  equations::Vector{P}
  inequations::Vector{P}
end

# Represents the final output
struct __AlgebraicThomasDecomposition{P <: MPolyRingElem}
  systems::Vector{__AlgebraicSystem{P}}
end

