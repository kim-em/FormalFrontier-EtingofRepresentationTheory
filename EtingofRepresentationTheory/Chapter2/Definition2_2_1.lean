import Mathlib.Algebra.Algebra.Basic

/-!
# Definition 2.2.1: Associative Algebra

An **associative algebra** over k is a vector space A over k together with a bilinear map
A × A → A, (a, b) ↦ ab, such that (ab)c = a(bc).

## Mathlib correspondence

This is exactly `Algebra k A` with `Ring A`. Mathlib algebras are associative and unital
by default.
-/

/-- An associative algebra over a field k, in the sense of Etingof Definition 2.2.1.
This is `Algebra k A` in Mathlib. -/
abbrev Etingof.AssociativeAlgebra (k : Type*) (A : Type*) [Field k] [Ring A] :=
  Algebra k A
