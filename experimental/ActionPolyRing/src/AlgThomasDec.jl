
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
#  IO Methods
#
###############################################################################

function __show_system(io::IO, sys::__AlgebraicSystem)
  if !is_empty(sys)
    if !is_empty(sys.eqs)
      print(io, "\nEquations:     ")
      join(io, sys.eqs, " = 0, ")
      print(io, " = 0")
    end

    if !is_empty(sys.ineqs)
      print(io, "\nInequations:   ")
      join(io, sys.ineqs, " != 0, ")
      print(io, " != 0")
    end
  else
    print(io, "\nEmpty algebraic system")
  end
end

function Base.show(io::IO, ::MIME"text/plain", sys::__AlgebraicSystem)
  io = pretty(io)
  if is_empty(sys)
    print(io, "Empty algebraic system")
  else
    print(io, "Simple algebraic system")
    print(io, Indent())
    __show_system(io, sys)
    print(io, Dedent())
  end
end

function Base.show(io::IO, sys::__AlgebraicSystem)
  io = pretty(io)
  if is_terse(io)
    print(io, "Simple algebraic system")
  else
    print(io, "Simple algebraic system with $(length(sys.eqs)) equations and $(length(sys.ineqs)) inequations")
  end
end

function Base.show(io::IO, ::MIME"text/plain", tdec::__AlgebraicThomasDecomposition)
  io = pretty(io)
  n = length(tdec.systems)

  if n == 0
    print(io, "Empty Thomas decomposition - the algebraic system is inconsistent")
  elseif n == 1 && is_empty(tdec)
    print(io, "Trivial Thomas decomposition")
  else
    print(io, "Thomas decomposition into $n simple algebraic systems:")

    print(io, Indent())
    for (i, sys) in enumerate(tdec.systems)
      if i > 1
        print(io, "\n")
      end

      print(io, "\nSimple branch $i:")

      print(io, Indent())
      __show_system(io, sys)
      print(io, Dedent())
    end
    print(io, Dedent())
  end
end

function Base.show(io::IO, tdec::__AlgebraicThomasDecomposition)
  io = pretty(io)
  if is_terse(io)
    print(io, "Thomas decomposition")
  else
    print(io, "Thomas decomposition into $(length(tdec.systems)) simple algebraic systems")
  end
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

equations(sys::__AlgebraicSystem) = sys.eqs
inequations(sys::__AlgebraicSystem) = sys.ineqs

###############################################################################
#
#  Collection & QoL API
#
###############################################################################

is_empty(sys::__AlgebraicSystem) = is_empty(sys.eqs) && is_empty(sys.ineqs)
is_empty(dec::__AlgebraicThomasDecomposition) = is_empty(dec.systems)

Base.iterate(dec::__AlgebraicThomasDecomposition) = iterate(dec.systems)
Base.iterate(dec::__AlgebraicThomasDecomposition, state) = iterate(dec.systems, state)

Base.length(dec::__AlgebraicThomasDecomposition) = length(dec.systems)
Base.eltype(::Type{__AlgebraicThomasDecomposition{P}}) where {P} = __AlgebraicSystem{P}

getindex(tdec::__AlgebraicThomasDecomposition, i::Int) = getindex(tdec.systems, i)

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
