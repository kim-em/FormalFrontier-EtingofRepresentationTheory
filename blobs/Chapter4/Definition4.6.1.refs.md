# References: Unitary representation

## Mathlib Coverage (partial)

- `UnitaryGroup`

Mathlib has `UnitaryGroup` and inner product spaces, but a dedicated `UnitaryRepresentation` (representation preserving an inner product) type is not available. Can be modeled using `Representation` plus a compatibility condition with `InnerProductSpace`.

## External Sources (definition gap)

- **[natural_language]** Serre, 'Linear Representations of Finite Groups' — Section 1.3
  Unitary representations for finite groups; averaging inner product construction; detailed proof of complete reducibility via unitarizability
- **[natural_language]** Fulton & Harris, 'Representation Theory: A First Course' — Section 1.1
  Introductory treatment of unitary representations with explicit constructions

## External Dependencies

- **Matrix algebra: matrix multiplication, trace, determinant, similarity, matrix units** (undergraduate_prerequisite)
  Mathlib (exact): `Matrix`, `Matrix.mul`, `Matrix.trace`, `Matrix.det`, `Matrix.StdBasisMatrix`, `Matrix.trace_mul_comm`
  Full matrix algebra. `Matrix.StdBasisMatrix` provides matrix units. `Matrix.trace_mul_comm` gives tr(AB) = tr(BA).
- **Eigenvalues and eigenvectors: characteristic polynomial, eigenspaces, diagonalization** (undergraduate_prerequisite)
  Mathlib (exact): `Module.End.HasEigenvalue`, `Module.End.eigenspace`, `Matrix.charpoly`
  Eigenvalues and eigenspaces well-covered. Characteristic polynomial via `Matrix.charpoly`. Diagonalization results available.
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
