# References: Orthogonality of characters: inner product equals dim Hom

## External Dependencies

- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.
- **Bilinear forms and inner products: Hermitian inner product on complex vector spaces, orthogonality** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap.BilinForm`, `InnerProductSpace`, `inner`, `Orthogonal`
  Inner products via `InnerProductSpace`. Bilinear forms via `LinearMap.BilinForm`. Complex Hermitian inner product supported via `RCLike` typeclass.
- **Tensor product of vector spaces: construction, universal property, tensor product of linear maps** (undergraduate_prerequisite)
  Mathlib (exact): `TensorProduct`, `TensorProduct.map`, `TensorProduct.mk`
  Full tensor product support. Universal property via `TensorProduct.lift`. Tensor product of maps via `TensorProduct.map`.
- **Dual vector space V* and natural pairing, dual maps (transpose/adjoint of linear maps)** (undergraduate_prerequisite)
  Mathlib (exact): `Module.Dual`, `Module.evalEquiv`, `LinearMap.dualMap`
  `Module.Dual R M` is `M →ₗ[R] R`. `Module.evalEquiv` gives the canonical isomorphism `M ≃ₗ[R] (M*)* ` for reflexive modules. `LinearMap.dualMap` is the transpose/dual map.
- **Characters of representations are class functions; character of a direct sum is sum of characters; character of a tensor product is product of characters** (folklore)
  Mathlib (partial): `FDRep.character`, `Representation`, `FDRep`
  `FDRep.character` gives the character of a finite-dimensional representation. The properties (class function, additivity over direct sums, multiplicativity over tensor products) may need to be proved from the definition, though some are likely available.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 2.1
  External source [other_formal]: MathComp (Coq) — character.v, classfun.v
- **Properties of the trace: tr(AB) = tr(BA), trace of identity is dimension, trace is basis-independent** (folklore)
  Mathlib (exact): `Matrix.trace`, `Matrix.trace_mul_comm`
  `Matrix.trace_mul_comm` gives tr(AB) = tr(BA). Trace of identity equals dimension. Basis independence follows from the linear map trace.
- **Generalized Schur orthogonality relations: orthogonality of matrix coefficients of irreducible representations over compact or finite groups** (folklore)
  Mathlib (missing): `FDRep.character`, `Representation`
  Schur orthogonality relations are NOT proved in Mathlib. The character infrastructure exists (`FDRep.character`) but the orthogonality results (both for matrix coefficients and characters) are absent.
- **Averaging (Reynolds) operator for finite group actions: (1/|G|) Σ_g ρ(g) is the projection onto invariants when char k does not divide |G|** (folklore)
  Mathlib (partial): `Representation`, `IsSemisimpleModule`
  The averaging operator is not explicitly named in Mathlib, but `IsSemisimpleModule` captures its consequence (complete reducibility). Maschke's theorem (semisimplicity of group algebra when char k ∤ |G|) is available via the semisimplicity framework.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 1.3
