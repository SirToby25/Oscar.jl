@testset "Test Downloading Artifact and elementary properties" begin
  t = literature_model(arxiv_id = "1511.03209")
  fully_resolved_big_model = resolve(t, 1)
  f1 = special_flux_family(fully_resolved_big_model, check = false)
  g1 = random_flux_instance(f1, check = false)
  f2 = special_flux_family(fully_resolved_big_model, not_breaking = true, check = false)
  g2 = random_flux_instance(f2, check = false)
  @test n_rays(ambient_space(t)) == 104
  @test n_rays(ambient_space(fully_resolved_big_model)) == 313
  @test typeof(get_attribute(fully_resolved_big_model, :inter_dict)) == Dict{NTuple{4, Int64}, ZZRingElem}
  @test length(chosen_g4_flux_basis(fully_resolved_big_model)) == 629
  @test is_well_quantized(g1) == true
  @test breaks_non_abelian_gauge_group(g2) == false
  @test size(matrix_integral(f1)) == (629, 224)
  @test size(matrix_rational(f1)) == (629, 127)
  @test size(matrix_integral(f2)) == (629, 1)
  @test size(matrix_rational(f2)) == (629, 127)
end

@testset "Advanced intersection theory and QSM-fluxes" begin
  for k in 1:5000
    qsm_model = try literature_model(arxiv_id = "1903.00009", model_parameters = Dict("k" => k)) catch e continue end
    h22_converter_dict = converter_dict_h22_ambient(qsm_model, check = false)
    coh_ring = cohomology_ring(ambient_space(qsm_model), check = false)
    coh_ring_gens = gens(coh_ring)
    for (key, value) in h22_converter_dict
      obj1 = coh_ring_gens[key[1]] * coh_ring_gens[key[2]]
      obj2 = sum(value[k][1] * coh_ring_gens[value[k][2][1]] * coh_ring_gens[value[k][2][2]] for k in 1:length(value))
      @test obj1 == obj2
    end
    qsm_g4_flux = qsm_flux(qsm_model)
    h22_basis = basis_of_h22_hypersurface_indices(qsm_model, check = false)
    flux_poly_str = string(polynomial(cohomology_class(qsm_g4_flux)))
    ring = base_ring(parent(polynomial(cohomology_class(qsm_g4_flux))))
    flux_poly = Oscar.eval_poly(flux_poly_str, ring)
    coeffs = collect(coefficients(flux_poly))
    raw_exps = collect(exponents(flux_poly))
    massaged_exps = [length(pos) == 1 ? (pos[1], pos[1]) : Tuple(sort(pos)) for pos in (findall(!=(0), mon) for mon in raw_exps)]
    flux_vector = fill(QQ(0), length(h22_basis))
    for (i, exp_pair) in enumerate(massaged_exps)
      idx = findfirst(==(exp_pair), h22_basis)
      flux_vector[idx] = coeffs[i]
    end
    flux_vector = transpose(matrix(QQ, [flux_vector]))
    fg = special_flux_family(qsm_model; not_breaking = true, check = false, algorithm = "special")
    @test ncols(matrix_integral(fg)) == 1
    @test nrows(matrix_integral(fg)) == nrows(matrix_rational(fg))
    @test unique(offset(fg)) == [0]
    M1 = matrix_integral(fg)
    M2 = matrix_rational(fg)
    large_M = hcat(M1, M2)
    @test rank(large_M) == minimum(size(large_M))
    solution = solve(large_M, flux_vector, side = :right)
    @test is_integer(solution[1])
    reconstructed_flux = flux_instance(fg, matrix(ZZ, [[solution[1]]]), solution[2:end,:])
    @test cohomology_class(qsm_g4_flux) == cohomology_class(reconstructed_flux)
  end
end
