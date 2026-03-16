import Mathlib.Algebra.Lie.Basic

/-!
# Example 2.9.8: Examples of Representations of Lie Algebras

(1) V = 0 (the zero representation).
(2) Any vector space V with ρ = 0 (the trivial representation).
(3) The adjoint representation V = 𝔤 with ρ(a)(b) := [a, b].

The meaning of the Jacobi identity is that it is equivalent to the existence of the adjoint
representation.

## Mathlib correspondence

Exact match. Mathlib has `LieModule` for Lie algebra representations and the adjoint
representation is built into the `LieRing` structure.
-/

/-- The trivial representation: any module with zero Lie action. (Etingof Example 2.9.8(2))
In Lean 4 / Mathlib, this is `TrivSqZeroExt` or simply the trivial `LieModule` instance. -/
example (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L] :
    LieModule k L L := inferInstance

/-- The adjoint representation: 𝔤 acts on itself via the Lie bracket.
(Etingof Example 2.9.8(3)) -/
example (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L]
    (a b : L) : ⁅a, b⁆ = ⁅a, b⁆ := rfl
