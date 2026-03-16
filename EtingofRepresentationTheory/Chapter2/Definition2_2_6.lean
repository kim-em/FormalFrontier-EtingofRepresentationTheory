import Mathlib.Algebra.Algebra.Hom

/-!
# Definition 2.2.6: Homomorphism of Algebras

A **homomorphism of algebras** f : A → B is a linear map such that f(xy) = f(x)f(y)
for all x, y ∈ A and f(1) = 1.

## Mathlib correspondence

This is exactly `AlgHom R A B` (notation `A →ₐ[R] B`). `AlgEquiv` for isomorphisms.
-/

/-- A homomorphism of algebras, in the sense of Etingof Definition 2.2.6.
This is `AlgHom k A B` (notation `A →ₐ[k] B`) in Mathlib. -/
abbrev Etingof.AlgebraHom (k : Type*) (A B : Type*) [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] :=
  A →ₐ[k] B
