## Accomplished

Issue #2478 (Schur-Weyl #2b — assemble polynomial GL_N-rep embedding into a
tensor power) — **partial**: landed the injection part.

* New file `EtingofRepresentationTheory/Chapter5/PolynomialRepEmbedding.lean`:
  - `splitDualBasis` — `V^⊗n ⊗ (V^*)^⊗n ≃ₗ[k] (Fin n → Fin N) → V^⊗n` via
    the standard basis of the dual factor (`Basis.equivFun` +
    `TensorProduct.piScalarRight`).
  - `matrixCoeffPoly` — for a basis `b` and polynomial witnesses `P a c`,
    the row-`a` matrix-coefficient polynomial `Σ_c (b.coord c x) • P a c` as
    a `M →ₗ[k] MvPolynomial` linear map.
  - `matrixCoeffPoly_mem_homogeneous` — homogeneity preservation under
    `k`-linear combination.
  - `eval_matrixCoeffPoly` — at any evaluation `s`, the polynomial recovers
    `b.coord a (T x)` for the encoded endomorphism `T`.
  - `polyTensorRow`, `polyTensorBundle` — bundle the `Fin d` rows through
    `homogeneousPolyToTensor` (#2477) and `splitDualBasis`.
  - **Main result `polynomialRep_embeds_in_tensorPower_inj`**: `∃ m, ∃ φ : M
    →ₗ[k] (Fin m → V^⊗n), Function.Injective φ` for any polynomial GL_N-rep
    `M` whose matrix coefficients are homogeneous of degree `n` in `g_ij`.
* Wired into `EtingofRepresentationTheory/Chapter5.lean`.
* Full `lake build` green; zero new sorries; zero linter warnings on the new
  file.

GL_N-**equivariance** of the embedding is deferred — see follow-up #2527.

## Current frontier

Equivariance of the embedding remains open. The bridge file
`PolynomialTensorBridge.lean` itself defers equivariance of
`homogeneousPolyToTensor`, so the equivariance work is meaningfully separate
from the injection assembly and is a self-contained follow-up.

## Overall project progress

* Schur-Weyl pipeline (sub-issue #2 of `progress/schur-weyl-scoping.md`):
  - #2461 (sub-#1): merged
  - #2462 (sub-#4): merged
  - #2477 (sub-#2a, bridge): merged
  - **#2478 (sub-#2b, embedding): injection-only landed; equivariance →
    #2527**
  - sub-#3 (#2458, identify L_i with SchurModule): blocked on Theorem5_18_1
  - sub-#5 (Schur-functor decomposition): waiting on equivariance from
    #2527.

## Next step

Pod will pick up an unclaimed `feature` issue. The equivariance follow-up
#2527 is the natural continuation, but it can wait — the partial PR provides
useful infrastructure on its own.

## Blockers

None for this turn.
