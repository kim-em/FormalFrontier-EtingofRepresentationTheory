import Mathlib.Algebra.Algebra.Basic

/-!
# Definition 2.2.5: Commutative Algebra

An algebra A is **commutative** if ab = ba for all a, b ∈ A.

## Mathlib correspondence

This is `CommRing A` together with `Algebra k A`.
-/

/-- A commutative algebra over k, in the sense of Etingof Definition 2.2.5.
This is `Algebra k A` with `CommRing A` in Mathlib. -/
abbrev Etingof.CommutativeAlgebra (k : Type*) (A : Type*) [Field k] [CommRing A] :=
  Algebra k A
