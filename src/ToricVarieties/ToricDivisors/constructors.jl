######################
# 1: The Julia type for ToricDivisors
######################

@attributes mutable struct ToricDivisor
           polymake_divisor::Polymake.BigObject
end
export ToricDivisor


function pm_tdivisor(td::ToricDivisor)
    return td.polymake_divisor
end

######################
# 2: Generic constructors
######################

@doc Markdown.doc"""
    ToricDivisor(v::AbstractNormalToricVariety, coeffs::Vector{Int})

Construct the torus invariant divisor on the normal toric variety `v` as linear combination of the torus invariant prime divisors of `v`. The coefficients of thi linear combination are passed as list of integers as first argument.

# Examples
```jldoctest
julia> show(ToricDivisor(toric_projective_space(2), [1,1,2]))
A torus invariant divisor on a normal toric variety
```
"""
function ToricDivisor(v::AbstractNormalToricVariety, coeffs::Vector{Int})
    # check input
    if length(coeffs) != pm_object(v).N_RAYS
        throw(ArgumentError("Number of coefficients needs to match number of prime divisors!"))
    end
    
    # construct the divisor
    ptd = Polymake.fulton.TDivisor(COEFFICIENTS=coeffs)
    Polymake.add(pm_object(v), "DIVISOR", ptd)
    td = ToricDivisor(ptd, Dict())
    
    # set attributes
    set_attribute!(td, :coefficients, coeffs)
    if sum(coeffs) != 1
        set_attribute!(td, :isprime_divisor, false)
    else
        set_attribute!(td, :isprime_divisor, all(y -> (y == 1 || y == 0), coeffs))
    end
    
    # return the result
    return td
end
export ToricDivisor


######################
# 3: Special constructors
######################

@doc Markdown.doc"""
    DivisorOfCharacter(v::AbstractNormalToricVariety, character::Vector{Int})

Construct the torus invariant divisor associated to a character of the normal toric variety `v`.

# Examples
```jldoctest
julia> show(DivisorOfCharacter(toric_projective_space(2), [1,2]))
A torus invariant divisor on a normal toric variety
```
"""
function DivisorOfCharacter(v::AbstractNormalToricVariety, character::Vector{Int})
    if length(character) != rank(character_lattice(v))
        throw(ArgumentError("Character must consist of $(rank(character_lattice(v))) integers!"))
    end
    f = map_from_character_to_principal_divisors(v)
    char = sum(character .* gens(domain(f)))
    coeffs = [Int(x) for x in transpose(f(char).coeff)][:,1]
    return ToricDivisor(v, coeffs)
end
export DivisorOfCharacter


###############################################################################
###############################################################################
### 4: Display
###############################################################################
###############################################################################
function Base.show(io::IO, td::ToricDivisor)
    print(io, "A torus invariant divisor on a normal toric variety")
end
