@doc raw"""
    blow_up(m::NormalToricVariety, I::ToricIdealSheafFromCoxRingIdeal; coordinate_name::String = "e")

Blow up the toric variety along a toric ideal sheaf.

!!! warning
    This function is type unstable. The type of the domain of the output `f` is always a subtype of `AbsCoveredScheme` (meaning that `domain(f) isa AbsCoveredScheme` is always true). Sometimes, the type of the domain will be a toric variety (meaning that `domain(f) isa NormalToricVariety` is true) if the algorithm can successfully detect this. In the future, the detection algorithm may be improved so that this is successful more often.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> x1, x2, x3, x4 = gens(cox_ring(P3))
4-element Vector{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}:
 x1
 x2
 x3
 x4

julia> II = ideal_sheaf(P3, ideal([x1*x2]))
Sheaf of ideals
  on normal toric variety
with restrictions
  1: Ideal (x_1_1*x_2_1)
  2: Ideal (x_2_2)
  3: Ideal (x_1_3)
  4: Ideal (x_1_4*x_2_4)

julia> f = blow_up(P3, II)
Blowup
  of normal toric variety
  in sheaf of ideals with restrictions
    1b: Ideal (x_1_1*x_2_1)
    2b: Ideal (x_2_2)
    3b: Ideal (x_1_3)
    4b: Ideal (x_1_4*x_2_4)
with domain
  scheme over QQ covered with 4 patches
    1a: [x_1_1, x_2_1, x_3_1]   scheme(0)
    2a: [x_1_2, x_2_2, x_3_2]   scheme(0)
    3a: [x_1_3, x_2_3, x_3_3]   scheme(0)
    4a: [x_1_4, x_2_4, x_3_4]   scheme(0)
and exceptional divisor
  effective cartier divisor defined by
    sheaf of ideals with restrictions
      1a: Ideal (x_1_1*x_2_1)
      2a: Ideal (x_2_2)
      3a: Ideal (x_1_3)
      4a: Ideal (x_1_4*x_2_4)
```
"""
function blow_up(m::NormalToricVarietyType, I::ToricIdealSheafFromCoxRingIdeal; coordinate_name::Union{String, Nothing} = nothing)
  coordinate_name = _find_blowup_coordinate_name(m, coordinate_name)
  defining_ideal = ideal_in_cox_ring(I)
  if all(in(gens(base_ring(defining_ideal))), gens(defining_ideal))
    return blow_up(m, defining_ideal; coordinate_name) # Apply toric method
  else
    return blow_up(I) # Reroute to scheme theory
  end
end

function _find_blowup_coordinate_name(m::NormalToricVarietyType, coordinate_name::Union{String, Nothing} = nothing)
  if coordinate_name !== nothing
    @req !(coordinate_name in coordinate_names(m)) "Coordinate name already exists"
    return coordinate_name
  else
    return _find_blowup_coordinate_name(coordinate_names(m))
  end
end

function _find_blowup_coordinate_name(vs::Vector{String})
  i = 1
  coordinate_name = "e"
  while coordinate_name in vs
    coordinate_name = string("e", i)
    i = i+1
  end
  return coordinate_name
end


@doc raw"""
    blow_up(v::NormalToricVariety, new_ray::AbstractVector{<:IntegerUnion}; coordinate_name::String)

Blow up the toric variety by subdividing the fan of the variety with the
provided new ray. This function returns the corresponding morphism.

Note that this ray must be a primitive element in the lattice Z^d, with
d the dimension of the fan. In particular, it is currently impossible to
blow up along a ray which corresponds to a non-Q-Cartier divisor.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional prime divisor. As optional argument one can supply a
custom variable name.

!!! warning
    This function is type unstable. The type of the field `center_unnormalized` is always a subtype of `AbsIdealSheaf` (meaning that `center_unnormalized(f) isa Oscar.AbsIdealSheaf` is always true). Sometimes, the function computes and sets the field `center_unnormalized` for the output `f`, giving it the type `ToricIdealSheafFromCoxRingIdeal` (meaning that `center_unnormalized(f) isa Oscar.ToricIdealSheafFromCoxRingIdeal` is true and `center_unnormalized(f) isa IdealSheaf` is false). If it does not, then calling `center_unnormalized(f)` computes and sets the field `center_unnormalized` and it will have the type `IdealSheaf` (meaning that `center_unnormalized(f) isa Oscar.ToricIdealSheafFromCoxRingIdeal` is false and `center_unnormalized(f) isa IdealSheaf` is true).

# Examples

In the example below `center_unnormalized(f)` has type `ToricIdealSheafFromCoxRingIdeal` and we can access the corresponding ideal in the Cox ring using `Oscar.ideal_in_cox_ring`.

```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> f = blow_up(P3, [0, 2, 3])
Toric blowup morphism

julia> bP3 = domain(f)
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [1 2]
  x3 -> [1 3]
  x4 -> [1 0]
  e -> [0 -1]

julia> typeof(center_unnormalized(f))
Oscar.ToricIdealSheafFromCoxRingIdeal{NormalToricVariety, AbsAffineScheme, Ideal, Map}

julia> Oscar.ideal_in_cox_ring(center_unnormalized(f))
Ideal generated by
  x2^2
  x3^3
```

In the below example, `center_unnormalized(f)` has type `IdealSheaf` and we cannot access the corresponding ideal in the Cox ring.

# Examples
```jldoctest
julia> rs = [1 1; -1 1]
2×2 Matrix{Int64}:
  1  1
 -1  1

julia> max_cones = incidence_matrix([[1, 2]])
1×2 IncidenceMatrix
[1, 2]

julia> v = normal_toric_variety(max_cones, rs)
Normal toric variety

julia> f = blow_up(v, [0, 1])
Toric blowup morphism

julia> center_unnormalized(f)
Sheaf of ideals
  on normal, non-smooth toric variety
with restriction
  1: Ideal (x_3_1, x_2_1, x_1_1)

julia> typeof(center_unnormalized(f))
IdealSheaf{NormalToricVariety, AbsAffineScheme, Ideal, Map}
```
"""
function blow_up(v::NormalToricVarietyType, new_ray::AbstractVector{<:IntegerUnion}; coordinate_name::Union{String, Nothing} = nothing)
  coordinate_name = _find_blowup_coordinate_name(v, coordinate_name)
  new_variety = normal_toric_variety(star_subdivision(v, new_ray))
  if is_smooth(v) == false
    return ToricBlowupMorphism(v, new_variety, coordinate_name, new_ray, new_ray)
  end
  inx = _get_maximal_cones_containing_vector(polyhedral_fan(v), new_ray)
  old_rays = matrix(ZZ, rays(v))
  cone_generators = matrix(ZZ, [old_rays[i,:] for i in 1:nrows(old_rays) if ray_indices(maximal_cones(v))[inx[1], i]])
  powers = solve_non_negative(ZZMatrix, transpose(cone_generators), transpose(matrix(ZZ, [new_ray])))
  if nrows(powers) != 1
    return ToricBlowupMorphism(v, new_variety, coordinate_name, new_ray, new_ray)
  end
  gens_S = gens(cox_ring(v))
  variables = [gens_S[i] for i in 1:nrows(old_rays) if ray_indices(maximal_cones(v))[inx[1], i]]
  list_of_gens = [variables[i]^powers[i] for i in 1:length(powers) if powers[i] != 0]
  center_unnormalized = ideal_sheaf(v, ideal([variables[i]^powers[i] for i in 1:length(powers) if powers[i] != 0]))
  return ToricBlowupMorphism(v, new_variety, coordinate_name, new_ray, new_ray, center_unnormalized)
end

@doc raw"""
    blow_up(v::NormalToricVariety, n::Int; coordinate_name::String = "e")

Blow up the toric variety by subdividing the n-th cone in the list
of *all* cones of the fan of `v`. This cone need not be maximal.
This function returns the corresponding morphism.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional prime divisor. As third optional argument one can supply
a custom variable name.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> f = blow_up(P3, 5)
Toric blowup morphism

julia> bP3 = domain(f)
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [0 1]
  x3 -> [0 1]
  x4 -> [1 0]
  e -> [1 -1]
```
"""
function blow_up(v::NormalToricVarietyType, n::Int; coordinate_name::Union{String, Nothing} = nothing)
  coordinate_name = _find_blowup_coordinate_name(v, coordinate_name)
  gens_S = gens(cox_ring(v))
  center_unnormalized = ideal_sheaf(v, ideal([gens_S[i] for i in 1:number_of_rays(v) if cones(v)[n,i]]))
  new_variety = normal_toric_variety(star_subdivision(v, n))
  rays_of_variety = matrix(ZZ, rays(v))
  new_ray = vec(sum([rays_of_variety[i, :] for i in 1:number_of_rays(v) if cones(v)[n, i]]))
  return ToricBlowupMorphism(v, new_variety, coordinate_name, new_ray, new_ray, center_unnormalized)
end


@doc raw"""
    blow_up(v::NormalToricVariety, I::MPolyIdeal; coordinate_name::String = "e")

Blow up the toric variety by subdividing the cone in the list
of *all* cones of the fan of `v` which corresponds to the
provided ideal `I`. Note that this cone need not be maximal.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional prime divisor. As third optional argument one can supply
a custom variable name.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> (x1,x2,x3,x4) = gens(cox_ring(P3))
4-element Vector{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}:
 x1
 x2
 x3
 x4

julia> I = ideal([x2,x3])
Ideal generated by
  x2
  x3

julia> bP3 = domain(blow_up(P3, I))
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [0 1]
  x3 -> [0 1]
  x4 -> [1 0]
  e -> [1 -1]

julia> I2 = ideal([x2 * x3])
Ideal generated by
  x2*x3

julia> b2P3 = blow_up(P3, I2);

julia> codomain(b2P3) === P3
true
```
"""
function blow_up(v::NormalToricVarietyType, I::MPolyIdeal; coordinate_name::Union{String, Nothing} = nothing)
  coordinate_name = _find_blowup_coordinate_name(v, coordinate_name)
  cox = cox_ring(v)
  indices = [findfirst(==(x), gens(cox)) for x in gens(I)]
  if all(!isnothing, indices)
    rs = matrix(ZZ, rays(v))
    new_ray = vec(sum(rs[index, :] for index in indices))
    new_ray = new_ray ./ gcd(new_ray)
    new_variety = normal_toric_variety(star_subdivision(v, new_ray))
    center_unnormalized = ideal_sheaf(v, I)
    return ToricBlowupMorphism(v, new_variety, coordinate_name, new_ray, I, center_unnormalized)
  else
    return _generic_blow_up(v, I)
  end
end

function _generic_blow_up(v::Any, I::Any)
  error("Not yet supported")
end

function _generic_blow_up(v::NormalToricVarietyType, I::MPolyIdeal)
  return blow_up(ideal_sheaf(v, I))
end
