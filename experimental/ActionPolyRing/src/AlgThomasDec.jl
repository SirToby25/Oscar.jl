
###############################################################################
#
#  Types for Thomas decompositions
#
###############################################################################

# Represents an algebraic system or a branch in the Thomas decomposition tree
struct __AlgebraicSystem{R <: MPolyRing, P <: MPolyRingElem}
  base_ring::R
  eqs::Vector{P}
  ineqs::Vector{P}
end

# Represents the final output
struct __AlgebraicThomasDecomposition{R <: MPolyRing, P <: MPolyRingElem}
  init_sys::__AlgebraicSystem{R, P}
  simple_systems::Vector{__AlgebraicSystem{R, P}}
end

###############################################################################
#
#  Thomas type helpers
#
###############################################################################

### Getters ###
base_ring(sys::__AlgebraicSystem) = sys.base_ring
equations(sys::__AlgebraicSystem) = sys.eqs
inequations(sys::__AlgebraicSystem) = sys.ineqs

initial_system(tdec::__AlgebraicThomasDecomposition) = tdec.init_sys
simple_systems(tdec::__AlgebraicThomasDecomposition) = tdec.simple_systems

### Other helpers ###
base_ring(tdec::__AlgebraicThomasDecomposition) = base_ring(initial_system(tdec))
__equation_ideal(sys::__AlgebraicSystem) = ideal(base_ring(sys), equations(sys))

# For inplace killing inconsistent systems
function __empty!(sys::__AlgebraicSystem)
  empty!(equations(sys))
  empty!(inequations(sys))
  return sys
end

###############################################################################
#
#  IO Methods
#
###############################################################################

function __show_system(io::IO, sys::__AlgebraicSystem)
  if !is_empty(sys)
    if !is_empty(equations(sys))
      print(io, "\nEquations:     ")
      join(io, equations(sys), " = 0, ")
      print(io, " = 0")
    end

    if !is_empty(inequations(sys))
      print(io, "\nInequations:   ")
      join(io, inequations(sys), " != 0, ")
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
    print(io, "Simple algebraic system with $(length(equations(sys))) equations and $(length(inequations(sys))) inequations")
  end
end

function Base.show(io::IO, ::MIME"text/plain", tdec::__AlgebraicThomasDecomposition)
  io = pretty(io)
  n = length(simple_systems(tdec))

  if n == 0
    print(io, "Empty Thomas decomposition - the algebraic system is inconsistent")
  elseif n == 1 && is_empty(tdec)
    print(io, "Trivial Thomas decomposition")
  else
    print(io, "Thomas decomposition into $n simple algebraic systems:")

    print(io, Indent())
    for (i, sys) in enumerate(simple_systems(tdec))
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
    print(io, "Thomas decomposition into $(length(simple_systems(tdec))) simple algebraic systems")
  end
end

###############################################################################
#
#  Collection & QoL API
#
###############################################################################

is_empty(sys::__AlgebraicSystem) = is_empty(equations(sys)) && is_empty(inequations(sys))
is_empty(tdec::__AlgebraicThomasDecomposition) = is_empty(simple_systems(tdec))

Base.iterate(tdec::__AlgebraicThomasDecomposition) = iterate(simple_systems(tdec))
Base.iterate(tdec::__AlgebraicThomasDecomposition, state) = iterate(simple_systems(tdec), state)

Base.length(tdec::__AlgebraicThomasDecomposition) = length(simple_systems(tdec))
Base.eltype(::Type{__AlgebraicThomasDecomposition{R, P}}) where {R <: MPolyRing, P <: MPolyRingElem} = __AlgebraicSystem{R, P}

getindex(tdec::__AlgebraicThomasDecomposition, i::Int) = getindex(simple_systems(tdec), i)

###############################################################################
#
#  Main functions
#
###############################################################################

function thomas_decomposition(R::MPolyRing;
                     eqs::AbstractVector{<:MPolyRingElem}=elem_type(R)[],
                     ineqs::AbstractVector{<:MPolyRingElem}=elem_type(R)[])
  P = elem_type(R)
  E = eqs isa Vector{P} ? eqs : P[eq for eq in eqs]
  I = ineqs isa Vector{P} ? ineqs : P[iq for iq in ineqs]
  return thomas_decomposition(R, E, I)
end

function thomas_decomposition(R::MPolyRing, E::Vector{P}, I::Vector{P}) where {P <: MPolyRingElem}
  init_sys = __AlgebraicSystem{typeof(R), P}(R, E, I)
  queue = [init_sys]
  finished_systems = __AlgebraicSystem{typeof(R), P}[]

  while !is_empty(queue)
    current_sys = popfirst!(queue)

    is_consistent, current_sys = __is_consistent_after_preprocessing!(current_sys)
    # Preprocessing
    !__is_consistent && continue

    # TODO: Actually split current_sys

    push!(finished_systems, current_sys)
  end

  return __AlgebraicThomasDecomposition(init_sys, finished_systems)
end

function generic_simple_system(tdec::__AlgebraicThomasDecomposition; check::Bool=true)
  check && @req is_prime(__equation_ideal(initial_system(tdec))) "The initial system of the Thomas decomposition is not prime"
  return argmin(sys -> length(equations(sys)), tdec)
end

###############################################################################
#
#  Thomas decompositions helpers
#
###############################################################################

function __is_consistent_after_preprocessing!(sys::__AlgebraicSystem)
  # In all comments, let c be a nonzero constant

  filter(!is_zero, equations(sys)) # 0 == 0 is trivially true and can be removed
  if any(is_constant, equations(sys)) || any(is_zero, inequations(sys)) # inconsistent
    return (false, __empty!(sys))
  end
  filter(!is_constant, inequations(sys)) # c != 0 is trivially true and can be removed

  # divide polys by their content
  for arr in (equations(sys), inequations(sys))
    for i in eachindex(arr)
      c = content(arr[i])
      if !is_one(c)
        arr[i] = divexact(arr[i], c)
      end
    end
  end

  # divide lhs by inequations, if possible.
  ineqs_changed = true
  while ineqs_changed
    ineqs_changed = false
    for q in inequations(sys)
      for i in eachindex(inequations(sys))
        inequations(sys)[i] == q && continue
        nu, inequations(sys)[i] = remove(inequations(sys)[i], q)
        if nu > 0
          ineqs_changed = true
          break
        end
      end
      ineqs_changed && break
    end
  end

  # once no inequations simplify each other, we clear out equations
  for q in inequations(sys)
    for i in eachindex(equations(sys))
      _, equations(sys)[i] = remove(equations(sys)[i], q)
    end
  end

  # If the preprocessing leads to an equation c == 0, the system is inconsistent
  any(is_constant, equations(sys)) && return (false, __empty!(sys))
  filter(!is_constant, inequations(sys)) # c != 0 is trivially true and can be removed

  return (true, sys)
end

