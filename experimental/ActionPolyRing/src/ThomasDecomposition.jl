
###############################################################################
#
#  Types for Thomas decompositions 
#
###############################################################################

struct __EquationWithMultVars{T <: RingElement, PolyT <: Union{MPolyRingElem{T}, ActionPolyRingElem{T}}, Var} # Represents the cone (p_i, \mu_i) for a single equation
  p::PolyT
  ld::PolyT
  mult_vars::Vector{Var} # For MPolys: Var == Int, for ActionPolys: Var == Vector{Int}
end

struct __ThomasSystem{T <: RingElement, PolyT <: Union{MPolyRingElem{T}, ActionPolyRingElem{T}}, Var}
  eqs_with_mult_vars::Vector{__EquationWithMultVars{T, PolyT, Var}}
  ineqs::Vector{PolyT}
  split_conds::Vector{PolyT} # Only relevant during some splitting algorithms but stored for performance
end

__eqs(S::__ThomasSystem) = [e.p for e in S.eqs_with_mult_vars]
__mult_vars(S::__ThomasSystem) = [e.mult_vars for e in S.eqs_with_mult_vars]
__ineqs(S::__ThomasSystem) = S.ineqs
__split_conds(S::__ThomasSystem) = S.split_conds

#=
struct __ThomasTriple{T <: RingElement, PolyT <: Union{MPolyRingElem{T}, ActionPolyRingElem{T}}, Var}
  L::__ThomasSystem{T, PolyT, Var}
  M::__ThomasSystem{T, PolyT, Var}
  N::__ThomasSystem{T, PolyT, Var}
end

struct __ThomasDecomposition{T <: RingElement, PolyT <: Union{MPolyRingElem{T}, ActionPolyRingElem{T}}, Var}
  simple_systems::Vector{__ThomasSystem{T, PolyT, Var}}
end
=#
