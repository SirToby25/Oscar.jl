```@meta
CurrentModule = Oscar
CollapsedDocStrings = true
DocTestSetup = Oscar.doctestsetup()
```

# [Differential polynomial rings](@id differentialpolyring)

A differential polynomial ring over the commutative ring ``R`` is an action polynomial ring ``A`` whose action maps are derivations of ``A``, i.e. ``R``-linear maps that also satisfy the Leibniz-rule.

## Construction

```@docs
differential_polynomial_ring
```

<<<<<<< HEAD
## Action maps
The action maps of a differential polynomial ring over the commutative ring `R` are `R`-linear derivations.

=======
>>>>>>> 7514c7a95d (documentation for APR)
!!! warning
    After calling one of the two following methods, all jet variables that arise within their computation will
    be tracked afterwards.

<<<<<<< HEAD
=======
## Action maps
The action maps of a differential polynomial ring over the commutative ring `R` are `R`-linear derivations.

>>>>>>> 7514c7a95d (documentation for APR)
```@docs
diff_action(p::DifferentialPolyRingElem, i::Int)
diff_action(dpre::DifferencePolyRingElem{T}, d::Vector{Int}) where {T}
```
