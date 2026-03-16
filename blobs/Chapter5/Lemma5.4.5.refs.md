# References: Roots of unity average: either all equal or sum is zero

## External Dependencies

- **Eigenvalues and eigenvectors: characteristic polynomial, eigenspaces, diagonalization** (undergraduate_prerequisite)
  Mathlib (exact): `Module.End.HasEigenvalue`, `Module.End.eigenspace`, `Matrix.charpoly`
  Eigenvalues and eigenspaces well-covered. Characteristic polynomial via `Matrix.charpoly`. Diagonalization results available.
- **Polynomial rings k[x]: division algorithm, irreducible polynomials, minimal polynomial of a linear operator** (undergraduate_prerequisite)
  Mathlib (exact): `Polynomial`, `Polynomial.IsRoot`, `Polynomial.divByMonic`, `Irreducible`, `minpoly`
  Complete polynomial ring support. Division algorithm, irreducibility, and minimal polynomial of an element all present.
- **Algebraic integers and algebraic number theory basics: algebraic integers form a ring, norm of algebraic integers** (undergraduate_prerequisite)
  Mathlib (exact): `IsIntegral`, `NumberField.RingOfIntegers`, `Algebra.norm`
  `IsIntegral R x` for algebraic elements. `NumberField.RingOfIntegers` for the ring of integers. `Algebra.norm` for the norm map.
- **Complex analysis basics: roots of unity, absolute values of complex numbers, triangle inequality for sums of roots of unity** (undergraduate_prerequisite)
  Mathlib (exact): `IsPrimitiveRoot`, `rootsOfUnity`, `Complex.normSq`, `Complex.instNorm`
  Roots of unity via `IsPrimitiveRoot` and `rootsOfUnity`. Complex absolute value via the norm instance `Complex.instNorm` (using `‖z‖`). Triangle inequality available through the normed field instance.
- **Algebraic conjugates of roots of unity are roots of unity; product of algebraic conjugates of an algebraic integer is a rational integer** (folklore)
  Mathlib (partial): `IsPrimitiveRoot`, `Algebra.norm`, `IsIntegral`
  The individual components exist (roots of unity, algebraic integers, norms). The specific fact that algebraic conjugates of roots of unity are roots of unity may need to be proved from the Galois theory of cyclotomic fields, which is well-developed in Mathlib.
  External source [natural_language]: Washington, 'Introduction to Cyclotomic Fields' — Chapter 1
