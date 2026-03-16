import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Definition 7.6.1: Adjoint Functors

Functors F : C → D and G : D → C are **adjoint functors** if for any X ∈ C, Y ∈ D
we have an isomorphism ξ_{XY} : Hom_D(F(X), Y) → Hom_C(X, G(Y)) which is
functorial in X and Y.

F is left adjoint to G and G is right adjoint to F.

## Mathlib correspondence

This is exactly `CategoryTheory.Adjunction`.
-/

/-- An adjunction between functors F and G, in the sense of Etingof Definition 7.6.1.
This is `CategoryTheory.Adjunction` in Mathlib. -/
abbrev Etingof.Adjunction {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D)
    (G : CategoryTheory.Functor D C) := CategoryTheory.Adjunction F G
