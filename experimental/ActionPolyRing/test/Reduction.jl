@testset "all tests - Reduction.jl" verbose = true begin
  @testset "Differential reduction methods" begin
    @testset "Single differential indeterminate" begin
      dpr, u = differential_polynomial_ring(QQ, :u, 2)

      u_x = u[1, 0]
      u_y = u[0, 1]
      u_xy = u[1, 1]
      u_xxy = u[2, 1]

      @testset "separant" begin
        q1 = u_x - u^2
        @test separant(q1) == dpr(1)

        q2 = u_xy^2 + u_x
        @test separant(q2) == 2*u_xy
        @test separant(dpr(5)) == dpr(5)
        @test separant(dpr(0)) == 0
      end

      @testset "pseudorem and pseudodivrem" begin
        p1 = u_x^2 + u
        q1 = u_x - u^2

        @test pseudorem(p1, q1) == u^4 + u
        quot1, rem1 = pseudodivrem(p1, q1)
        @test quot1 == u_x + u^2
        @test rem1 == u^4 + u

        p2 = u_x^2 + u_x
        q2 = u * u_x - 1

        @test pseudorem(p2, q2) == u + 1
        quot2, rem2 = pseudodivrem(p2, q2)
        @test quot2 == u * u_x + u + 1
        @test rem2 == u + 1

        @test pseudorem(p2, q2, u_x) == u + 1
        q3, r3 = pseudodivrem(p2, q2, u_x)
        @test q3 == quot2
        @test r3 == rem2
      end

      @testset "__leader_shift_for_partial_reduction" begin
        foo = Oscar.__leader_shift_for_partial_reduction
        q = u_x - u^2

        p1 = u_xxy + u
        @test foo(p1, q) == [1, 1]

        p2 = u_xy + u
        @test foo(p2, q) == [0, 1]

        p3 = u_y + u
        @test foo(p3, q) === nothing
        @test foo(dpr(5), q) === nothing
      end

      @testset "partially_reduce" begin
        p = u_xxy + u
        q = u_x - u^2

        # Iteration 1: Q1 = apply_action(q, [1,1]) = u_xxy - 2*u_x*u_y - 2*u*u_xy
        # p1 = p - Q1 = 2*u*u_xy + 2*u_x*u_y + u
        # Iteration 2: Q2 = apply_action(q, [0,1]) = u_xy - 2*u*u_y
        # p2 = p1 - 2u*Q2 = 4*u^2*u_y + 2*u_x*u_y + u
        @test partially_reduce(p, q) == 4*u^2*u_y + 2*u_x*u_y + u
        @test partially_reduce(u_y + u, q) == u_y + u

        @test partially_reduce(p, dpr(5)) == zero(p)
        @test_throws ArgumentError partially_reduce(p, dpr(0))
      end

      @testset "reduce" begin
        p = u_xxy + u_x^2 + u
        q = u_x - u^2

        # 1. Partial reduction eliminates u_xxy, leaving:
        # p_pred = 4*u^2*u_y + 2*u_x*u_y + u_x^2 + u
        # 2. Algebraic reduction pseudo-divides out u_x^2 and u_x using (u_x - u^2):
        # p_fullred = 6*u^2*u_y + u^4 + u

        @test reduce(p, q) == 6*u^2*u_y + u^4 + u
        @test reduce(u_y + u, q) == u_y + u

        @test reduce(p, dpr(5)) == zero(p)
        @test_throws ArgumentError reduce(p, dpr(0))
      end
    end
    @testset "Two differential indeterminates" begin
      dpr, (u, v) = differential_polynomial_ring(QQ, [:u, :v], 2)

      u_x = dpr[1, [1, 0]]
      u_y = dpr[1, [0, 1]]
      u_xx = dpr[1, [2, 0]]
      u_xy = dpr[1, [1, 1]]
      u_yy = dpr[1, [0, 2]]
      u_xxy = dpr[1, [2, 1]]

      v_x = dpr[2, [1, 0]]
      v_y = dpr[2, [0, 1]]
      v_xx = dpr[2, [2, 0]]
      v_xy = dpr[2, [1, 1]]

      @testset "separant" begin
        q1 = u_xx + u_x^2
        q2 = u_x^3 + v_x*u_x
        q3 = -2*v_y*v_xx^5 - v_xy^2*v_xx^2 + 2*v_xx
        q4 = dpr(1)
        @test separant(q1) == 1
        @test separant(q2) == 3*u_x^2 + v_x
        @test separant(q3) == -10*v_y*v_xx^4 - 2*v_xy^2*v_xx + 2
        @test separant(q4) == dpr(1)
      end
      @testset "pseudorem and pseudodivrem" begin
        p1 = u_x^2 + v_x
        q1 = u_x - v_y

        @test pseudorem(p1, q1) == v_y^2 + v_x

        quot1, rem1 = pseudodivrem(p1, q1)
        @test quot1 == u_x + v_y
        @test rem1 == v_y^2 + v_x
        quotn1, remn1 = pseudodivrem(p1, q1; naive=true)
        @test quotn1 == quot1
        @test remn1 == remn1

        p2 = v_xx^2 + u_x
        q2 = u_y * v_xx - v_x
        @test pseudorem(p2, q2) == v_x^2 + u_y^2 * u_x
        @test pseudorem(p2, q2; naive=true) == v_x^2 + u_y^2 * u_x

        quot2, rem2 = pseudodivrem(p2, q2)
        @test quot2 == u_y * v_xx + v_x
        @test rem2 == v_x^2 + u_y^2 * u_x
        quotn2, remn2 = pseudodivrem(p2, q2; naive=true)
        @test quotn2 == quot2
        @test remn2 == rem2

        @test pseudorem(p2, q2, v_xx) == v_x^2 + u_y^2 * u_x

        quot2_, rem2_ = pseudodivrem(p2, q2, v_xx)
        @test quot2_ == quot2
        @test rem2_ == rem2

        p3 = u_x * v_x + u_x
        q3 = v_x + 1

        @test pseudorem(p3, q3) == dpr(0)
        quot3, rem3 = pseudodivrem(p3, q3)
        @test quot3 == u_x
        @test rem3 == dpr(0)

        p4 = u_y^2 * v_x + 1
        q4 = u_y * v_x + 1
        @test pseudorem(p4, q4) == 1 - u_y
        @test pseudorem(p4, q4; naive=true) == u_y*(1 - u_y)
        @test pseudodivrem(p4, q4) == (u_y, 1 - u_y)
        @test pseudodivrem(p4, q4; naive=true) == (u_y^2, u_y*(1 - u_y))

        p5 = v_x^3 + 1
        q5 = u_y * v_x^2 + 1
        @test pseudorem(p5, q5) == -v_x + u_y
        @test pseudorem(p5, q5; naive=true) == u_y*(-v_x + u_y)
        @test pseudodivrem(p5, q5) == (v_x, -v_x + u_y)
        @test pseudodivrem(p5, q5; naive=true) == (u_y*v_x, u_y*(-v_x + u_y))

        # Trivial Case 1: Degree of p is strictly less than degree of q
        p_triv1 = v_x
        q_triv1 = v_x^2 + u

        @test pseudorem(p_triv1, q_triv1) == v_x
        qt1, rt1 = pseudodivrem(p_triv1, q_triv1)
        @test qt1 == dpr(0)
        @test rt1 == v_x

        # Trivial Case 2: Dividend is exactly zero
        p_triv2 = dpr(0)
        q_triv2 = u_x + v

        @test pseudorem(p_triv2, q_triv2) == dpr(0)
        qt2, rt2 = pseudodivrem(p_triv2, q_triv2)
        @test qt2 == dpr(0)
        @test rt2 == dpr(0)

        # Trivial Case 3: Divisor is the zero polynomial
        @test_throws DivideError pseudorem(u_x + v, dpr(0))
        @test_throws DivideError pseudodivrem(u_x + v, dpr(0))
        @test_throws DivideError pseudorem(u_x + v, dpr(0), u_x)
        @test_throws DivideError pseudodivrem(u_x + v, dpr(0), u_x)

        @testset "nonzero constants" begin
          R, x = differential_polynomial_ring(ZZ, :x, 1)
          @test pseudorem(x, R(2)) == zero(R)
          @test pseudorem(2*x, R(2)) == zero(R)
          @test pseudodivrem(x, R(2)) == (x, R(0))
          @test pseudodivrem(2*x, R(2)) == (x, R(0))
          @test pseudodivrem(R(6), R(2)) == (3, R(0))
          @test pseudodivrem(R(5), R(2)) == (R(5), R(0))
        end
      end

      @testset "partially_reduce" begin
        p1 = u_xxy + v_x
        q1 = u_x - v^2
        @test partially_reduce(p1, q1) == 2*v_x*v_y + 2*v*v_xy+v_x
        @test partially_reduce(p1, [q1]) == 2*v_x*v_y + 2*v*v_xy+v_x
        @test partially_reduce(p1, [q1, q1]) == 2*v_x*v_y + 2*v*v_xy+v_x
        @test partially_reduce(p1, [q1, dpr(1)]) == zero(p1)
        @test_throws ArgumentError partially_reduce(p1, [q1, dpr(1), dpr(0)])

        p5 = u_x^3 + v_x
        q5 = u_x^2 + v
        @test partially_reduce(p5, q5) == p5
      end

      @testset "reduce" begin
        p2 = u_yy + u_y*v_x + u
        q2 = u_y - v^2
        @test reduce(p2, q2) == v^2*v_x + 2*v*v_y + u

        p3 = u_y + v_x
        q3 = u_x - v_y
        @test reduce(p3, q3) == p3

        p4 = u_x + v_y
        q4 = u_x + v_y
        @test reduce(p4, q4) == dpr(0)

        p5 = u_x^3 + v_x
        q5 = u_x^2 + v
        @test reduce(p5, q5) == v_x - u_x * v
      end
    end # two diff indets
    @testset "reduce wrt a set" begin
      dpr, (u, v) = differential_polynomial_ring(QQ, [:u, :v], 1, index_ordering_name=:deglex)

      q1 = v[1] - u[0]
      q2 = u[1] - v[0]

      p = v[2]

      @test !is_partially_reduced(p, [q1, q2])
      @test !is_reduced(p, [q1, q2])
      @test reduce(p, [q1, q2]) == v[0]
      @test partially_reduce(p, [q1, q2]) == u[1]
      @test is_partially_reduced(v[0], [q1, q2])
      @test is_partially_reduced(u[1], [q1, q2])
      @test is_reduced(v[0], [q1, q2])

      dpr, (u, v) = difference_polynomial_ring(QQ, [:u, :v], 1, index_ordering_name=:deglex)

      q1 = v[1] - u[0]
      q2 = u[1] - v[0]

      p = v[2]

      @test !is_partially_reduced(p, [q1, q2])
      @test !is_reduced(p, [q1, q2])
      @test reduce(p, [q1, q2]) == v[0]
      @test partially_reduce(p, [q1, q2]) == u[1]
      @test is_partially_reduced(v[0], [q1, q2])
      @test is_partially_reduced(u[1], [q1, q2])
      @test is_reduced(v[0], [q1, q2])
    end
  end # Differential reduction methods
  @testset "Difference reduction methods" begin
    @testset "Single shift operator " begin
      dpr, u = difference_polynomial_ring(QQ, :u, 2)

      u_0 = u[0, 0]
      u_x = u[1, 0]
      u_y = u[0, 1]
      u_xx = u[2, 0]
      u_xy = u[1, 1]

      @testset "partially reduce" begin
        q = u_x^2 - u_0

        p1 = u_xx + u_0
        @test is_partially_reduced(p1, q)
        @test partially_reduce(p1, q) == p1

        p2 = u_xx^2 + u_xy
        @test !is_partially_reduced(p2, q)
        @test partially_reduce(p2, q) == u_xy + u_x
        @test is_partially_reduced(u_xy + u_x, q)

        p3 = u_xx^3 + u_0
        @test !is_partially_reduced(p3, q)
        @test partially_reduce(p3, q) == u_xx * u_x + u_0
        @test is_partially_reduced(u_xx * u_x + u_0, q)
      end
      @testset "reduce" begin
        q = u_x^2 - u_0

        p1 = u_x^3 + u_x
        @test !is_reduced(p1, q)
        @test reduce(p1, q) == u_x * u_0 + u_x
        @test is_reduced(u_x * u_0 + u_x, q)

        p2 = u_xx^2 + u_x^2
        @test !is_reduced(p2, q)
        @test reduce(p2, q) == u_x + u_0
        @test is_reduced(u_x + u_0, q)

        q3 = u_y * u_x^2 - dpr(1)
        p3 = u_x^2 + u_0
        @test !is_reduced(p3, q3)
        @test reduce(p3, q3) == u_y * u_0 + dpr(1)
        @test is_reduced(u_y *u_0 + dpr(1), q3)

        p4 = u_xx + u_x + u_0
        @test is_partially_reduced(p4, q)
        @test is_reduced(p4, q)
        @test reduce(p4, q) == p4
      end
    end # single shift operator

    @testset "Two shift operators" begin
      dpr, (u, v) = difference_polynomial_ring(QQ, [:u, :v], 2)

      u_0 = u[0, 0]
      u_x = u[1, 0]
      u_y = u[0, 1]
      u_xx = u[2, 0]

      v_0 = v[0, 0]
      v_x = v[1, 0]
      v_y = v[0, 1]
      v_xy = v[1, 1]

      @testset "partially reduce" begin
        q1 = u_x^2 - v_y
        p1 = u_xx^2 - u_0
        @test !is_partially_reduced(p1, q1)
        @test partially_reduce(p1, q1) == v_xy - u_0
        @test is_partially_reduced(v_xy - u_0, q1)

        q2 = v_0 * u_x^2 - 1
        p2 = u_xx^2
        @test !is_partially_reduced(p2, q2)
        @test partially_reduce(p2, q2) == dpr(1)
        @test is_partially_reduced(dpr(1), q2)
      end
      @testset "reduce" begin
        q1 = u_x^2 - v_y
        p1 = v_x * u_x^3 + v_0
        @test !is_reduced(p1, q1)
        @test reduce(p1, q1) == v_x * u_x * v_y + v_0
        @test is_reduced(v_x * u_x *v_y + v_0, q1)

        q2 = u_x^2 - v_0
        p2 = u_xx^2 + u_x^2
        @test !is_reduced(p2, q2)
        @test reduce(p2, q2) == v_x + v_0
        @test is_reduced(v_x + v_0, q2)

        q3 = v_0 * u_x^2 - u_0
        p3 = u_x^3 + v_x
        @test !is_reduced(p3, q3)
        @test reduce(p3, q3) == u_0 * u_x + v_0 * v_x
        @test is_reduced(u_0 * u_x + v_0 * v_x, q3)

        q4 = u_x^2 - v_y
        p4 = u_xx + v_x * u_x + u_0
        @test is_reduced(p4, q4)
        @test reduce(p4, q4) == p4
      end
    end # two diff indets
  end # Difference reduction methods

  @testset "autoreduction" begin
    @testset "single differential indeterminate and single action map" begin
      dxr, x = difference_polynomial_ring(QQ, :x, 1)

      p1 = x[1] - x[0]^2
      p2 = x[2]^2 - x[0]
      @test !is_autoreduced([p1, p2])
      @test !is_autoreduced([p2, p1])
      @test autoreduce([p1, p2]) == [x[0]^8 - x[0],  x[1] - x[0]^2]
      @test autoreduce([p2, p1]) == [x[0]^8 - x[0],  x[1] - x[0]^2]
      @test is_autoreduced([x[0]^8 - x[0],  x[1] - x[0]^2])
      @test autoreduce([p1, p1]) == [p1]
      @test is_autoreduced([p1])
      @test is_autoreduced([p2])
      @test autoreduce(DifferencePolyRingElem[]) == DifferencePolyRingElem[]
      @test autoreduce(DifferencePolyRingElem[zero(dxr)]) == DifferencePolyRingElem[]
      @test is_autoreduced(DifferencePolyRingElem[])
      @test !is_autoreduced([zero(dxr)])
      @test autoreduce([dxr(0), dxr(0)]) == DifferencePolyRingElem[]
      @test autoreduce([dxr(0), dxr(-1), dxr(2)]) == [dxr(-1)]

      dpr, u = differential_polynomial_ring(QQ, :u, 1)
      q1 = u[1]^2 - u[0]
      q2 = u[2] - u[1]
      @test !is_autoreduced([q1, q2])
      @test !is_autoreduced([q2, q1])
      @test autoreduce([q1, q2]) == [u[0]]
      @test autoreduce([q2, q1]) == [u[0]]
      @test autoreduce([q1, q1]) == [q1]
      @test is_autoreduced([q1])
      @test autoreduce(DifferentialPolyRingElem[]) == DifferentialPolyRingElem[]
      @test autoreduce(DifferencePolyRingElem[zero(dxr)]) == DifferencePolyRingElem[]
      @test is_autoreduced(DifferentialPolyRingElem[])
      @test !is_autoreduced([zero(dxr)])
      @test autoreduce([dpr(0), dpr(0)]) == DifferentialPolyRingElem[]
      @test autoreduce([dpr(0), dpr(-1), dpr(2)]) == [dpr(-1)]
    end
    @testset "two differential indeterminates and two action maps" begin
      dpr, (u, v) = differential_polynomial_ring(QQ, [:u, :v], 2; index_ordering_name=:degrevlex)

      p1 = u[1, 1] - u[0, 0]
      p2 = u[1, 0] - v[1, 0]
      p3 = v[1, 1] - u[0, 0]

      @test !is_autoreduced([p1, p2, p3])
      @test autoreduce([p1, p2, p3]) == [p2, p3]
      @test autoreduce([p3, p2, p1]) == [p2, p3]
      @test autoreduce([p2, p3, p1]) == [p2, p3]
      @test autoreduce([p1, p2]) == [p2, p3]
      @test is_autoreduced([p2, p3])

      p4 = u[1, 1] - u[0, 1]
      p5 = p2
      p6 = v[1, 1] + v[0, 0]

      res = [-(u[0, 1] + v[0, 0]), u[1, 0] - v[1, 0], v[1, 1] + v[0, 0]]

      @test !is_autoreduced([p4, p5, p6])
      @test autoreduce([p4, p5, p6]) == res
      @test autoreduce([p6, p5, p4]) == res
      @test autoreduce([p5, p6, p4]) == res
      @test is_autoreduced(res)
    end
  end

  @testset "unified framework" begin
    __ld = Oscar.__leader
    __ulc = Oscar.__univariate_leading_coefficient
    __init = Oscar.__initial
    __disc = Oscar.__discriminant
    __irl = Oscar.__is_ritt_less

    dpr, (u, v) = differential_polynomial_ring(QQ, [:u, :v], 1)
    conv = Oscar.__algebraic_conversion_data(dpr, [u[1], u, v])
    (x, y, z) = gens(conv.mpr)
    @test u[1] > u > v
    @test conv(u[1]) == x
    @test conv(u) == y
    @test conv(v) == z
    @test x > y > z

    f = u[1]^2*u*v -2*u[1]*v + u^2*v
    @test conv(__ld(f)) == __ld(conv(f))
    @test conv(__ulc(f, v)) == __ulc(conv(f), conv(v))
    @test conv(__init(f)) == __init(conv(f))
    @test conv(__disc(f)) == __disc(conv(f))
    @test !__irl(f, u[1])
    @test !__irl(f, u[1]^2)
    @test __irl(f, u[1]^3)
    @test !__irl(conv(f), conv(u[1]))
    @test !__irl(conv(f), conv(u[1]^2))
    @test __irl(conv(f), conv(u[1]^3))
  end

  @testset "kerber helpers" begin
    @testset "berkowitz_minors" begin
      __berkowitz_minors = Oscar.__berkowitz_minors
      M = QQ[1 2 3; 4 5 6; 7 8 9]
      @test __berkowitz_minors(M) == QQ.([1, -3, 0]) # The rhs is obained as [det(M[1:k, 1:k]) for k in 1:3]

      R, (x1, x2, x3, x4, x5) = polynomial_ring(QQ, [:x1, :x2, :x3, :x4, :x5])

      A = matrix(R, [
        x1 + 2*x2 + 1          x2^2 + x3           x3 + x4 + 2;
        x1*x2 + x3             x2 + 3*x4 + 1       x1 + x5;
        x3 + 2*x5              x1^2 + x4           x4 + 3;
      ]) # Some dense matrix

      expected_minors = [
        # m_1 = det(A[1:1, 1:1])
        x1 + 2*x2 + 1,

        # m_2 = det(A[1:2, 1:2])
        -x1*x2^3 - x1*x2*x3 + x1*x2 + 3*x1*x4 + x1 - x2^2*x3 + 2*x2^2 + 6*x2*x4 + 3*x2 - x3^2 + 3*x4 + 1,

        # m_3 = det(A[1:3, 1:3])
        -x1^4 + x1^3*x2*x3 + x1^3*x2*x4 - x1^3*x5 - x1^3 - 2*x1^2*x2*x5 + x1^2*x3^2 + x1^2*x3*x4 + 2*x1^2*x3 - x1^2*x4
        - x1^2*x5 - x1*x2^3*x4 - 3*x1*x2^3 + x1*x2^2*x3 + 2*x1*x2^2*x5 - 3*x1*x2*x3 + x1*x2*x4^2 + x1*x2*x4 + 3*x1*x2
        + x1*x3^2 + 2*x1*x3*x5 + 3*x1*x4^2 - x1*x4*x5 + 9*x1*x4 + 3*x1 - x2^2*x3*x4 + x2^2*x3*x5 - 3*x2^2*x3 + 2*x2^2*x4
        + 2*x2^2*x5^2 + 6*x2^2 - x2*x3^2 - x2*x3*x4 - 2*x2*x3*x5 - 2*x2*x3 + 6*x2*x4^2 - 4*x2*x4*x5 + 21*x2*x4 - 4*x2*x5
        + 9*x2 - 3*x3^2*x4 + x3^2*x5 - 4*x3^2 - 2*x3*x4^2 - 6*x3*x4*x5 - 5*x3*x4 + 2*x3*x5^2 - 2*x3*x5 - 2*x3 - 6*x4^2*x5
        + 3*x4^2 - 15*x4*x5 + 10*x4 - 4*x5 + 3
      ]
      @test __berkowitz_minors(A) == expected_minors
    end
    @testset "__kerber_S_and_H_matrices" begin # This testset is based on Kerber's 2009 paper
      __kerber_S_matrix = Oscar.__kerber_S_matrix
      # The following example is based on the discussion below Definition 2.5
      R, (x,) = polynomial_ring(QQ, [:x])
      f = 3*x^4 - x^2 + 6*x + 1
      g = 2*x^2 + 2*x + 3

      expected_H = matrix(QQ, [
         0   2   2   3;
         2   2   3   0;
         6  11 -12  -2;
        11 -10 -14  -2
      ])
      H = Oscar.__kerber_H_matrix(f, g, 1)
      @test H == expected_H

      # Now we test some S matrices that are constructed from H, see Definition 4.2
      expected_S_12_H = matrix(QQ, [
        0   2  -2;
        2   3  -2;
        6 -12 -11
      ])
      @test __kerber_S_matrix(H, 1, 2) == expected_S_12_H

      expected_S_22_H = matrix(QQ, [
          2    0   3  -2;
          2   -2   0  -3;
         11   -6  -2  12;
        -10  -11  -2  14
      ])
      @test __kerber_S_matrix(H, 2, 2) == expected_S_22_H

      # Small helper
      function __make_kerber_S(A::MatElem, cols::Vector{Int})
        d = length(cols)
        return matrix(QQ, [sign(cols[c]) * A[r, abs(cols[c])] for r in 1:d, c in 1:d])
      end

      A = matrix(QQ, [10*r + c for r in 1:4, c in 1:4])
      @test __kerber_S_matrix(A, 1, 4) == __make_kerber_S(A, [1])
      @test __kerber_S_matrix(A, 2, 4) == __make_kerber_S(A, [2, -1])
      @test __kerber_S_matrix(A, 3, 4) == __make_kerber_S(A, [3, -1, -2])
      @test __kerber_S_matrix(A, 4, 4) == __make_kerber_S(A, [4, -1, -2, -3])

      # The following test is based on Example 4.6 in Kerber's 2009 paper
      R, _ = polynomial_ring(QQ, :x)
      A = matrix(QQ, [10*r + c for r in 1:9, c in 1:9])
      expected_cols = [3, -1, -2, 9, -4, -5, -6, -7, -8]
      @test __kerber_S_matrix(A, 3, 6) == __make_kerber_S(A, expected_cols)

    end # S and H matrices
  end # kerber helpers
  @testset "subresultant_prs" begin
    # Many variables example
    R, (x, a, b, c, d) = polynomial_ring(QQ, [:x, :a, :b, :c, :d])
    p = x^5 + (a + b)*x^4 + (c - d)*x^3 + (a*c + 1)*x^2 + (b*d)*x + (a + c)
    q = (b + 1)*x^4 + (a - c)*x^3 + (c*d)*x^2 + (a - b)*x + 1
    @test_throws ArgumentError subresultant_prs_ducos(q, p, 1)
    @test_throws ArgumentError subresultant_prs_kerber(q, p, 1)
    sprs_d = subresultant_prs_ducos(p, q, 1)
    sprs_k = subresultant_prs_kerber(p, q, 1)
    @test sprs_d[1] == p
    @test sprs_k[1] == p
    @test sprs_d[2] == q
    @test sprs_d[2] == q
    @test sprs_d[end] == resultant(p, q, 1)
    @test sprs_k[end] == resultant(p, q, 1)
    @test length(sprs_d) == 6
    @test length(sprs_k) == 6
    @test sprs_d == sprs_k

    for i in 2:5
      @test degree(p, i) == degree(q, i)
      sprs_d = subresultant_prs_ducos(p, q, i)
      sprs_k = subresultant_prs_kerber(p, q, i)
      @test length(sprs_d) == 3
      @test length(sprs_k) == 3
      @test sprs_d == sprs_k

      sprs_d_swp = subresultant_prs_ducos(q, p, i)
      sprs_k_swp = subresultant_prs_kerber(q, p, i)

      @test sprs_d_swp[3] == -sprs_d[3]
      @test sprs_k_swp[3] == -sprs_k[3]
      @test sprs_d_swp == sprs_k_swp
    end

    @testset "rational polyring in two vars" begin
      R, (x, y) = polynomial_ring(QQ, [:x, :y])

      p = x^4 + y*x + 1
      q = x^4 + 1
      sprs_d = subresultant_prs_ducos(p, q, 1)
      sprs_k = subresultant_prs_kerber(p, q, 1)
      @test resultant(p, q, 1) == sprs_d[end]
      @test resultant(p, q, 1) == sprs_k[end]
      @test sprs_d !== sprs_k
      @test sprs_d == [p, q, -x*y^3, y^4]
      @test sprs_k == [p, q, -x*y, 0, -x*y^3, y^4]
      for i in 0:2
        @test subresultant_prs(p, q, 1; strategy=i) == sprs_d
        @test subresultant_prs(p, q, 1; strategy=i) == [p for (k, p) in enumerate(sprs_k) if k <= 2 || degree(p, 1) == degree(q, 1) - k + 2]
      end

      @test subresultant_prs_ducos(p, q, 1; min_deg=1) == [p, q, -x*y^3]
      @test subresultant_prs_ducos(p, q, 1; min_deg=2) == [p, q]
      @test subresultant_prs_ducos(p, q, 1; min_deg=3) == [p, q]
      @test subresultant_prs_ducos(p, q, 1; min_deg=5) == [p, q] # no effect on p and q
      @test subresultant_prs_kerber(p, q, 1; s=1) == [p, q, 0, 0, -x*y^3, y^4]
      @test subresultant_prs_kerber(p, q, 1; s=2) == [p, q, 0, 0, -x*y^3, y^4]
      @test subresultant_prs_kerber(p, q, 1; s=3) == [p, q, -x*y, 0, -x*y^3, y^4]

      p = x^4 + y
      q = x^3 + 1
      res_ducos = subresultant_prs_ducos(p, q, 1)
      res_kerber = subresultant_prs(p, q, 1; strategy=2)
      @test res_ducos == res_kerber
      @test [degree(t, 1) for t in res_ducos] == [4, 3, 1, 0]
      raw_kerber = subresultant_prs_kerber(p, q, 1)
      @test degree(raw_kerber[3], 1) != 2 || is_zero(raw_kerber[3])

      # Common factor
      g = x^2 + y
      p = g * (x^2 + 2)
      q = g * (x + y)
      res_ducos = subresultant_prs_ducos(p, q, 1)
      res_kerber = subresultant_prs(p, q, 1; strategy=2)

      @test res_ducos == res_kerber
      @test res_ducos[end] == (y^2 + 2)*g

      @test subresultant_prs_ducos(p, q, 1; min_deg=2) == res_ducos
      @test subresultant_prs_ducos(p, q, 1; min_deg=3) == [p, q]
    end
  end
end # all tests
