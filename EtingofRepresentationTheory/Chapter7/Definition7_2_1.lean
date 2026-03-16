import Mathlib.CategoryTheory.Functor.Basic

/-!
# Definition 7.2.1: Functor

A **functor** F : C → D between categories C and D is:
- A map F : Ob(C) → Ob(D)
- For each X, Y ∈ C, a map F_{X,Y} : Hom(X, Y) → Hom(F(X), F(Y))
which preserves compositions and identity morphisms.

## Mathlib correspondence

This is exactly `CategoryTheory.Functor`.
-/

/-- A functor between categories, in the sense of Etingof Definition 7.2.1.
This is `CategoryTheory.Functor` in Mathlib. -/
abbrev Etingof.Functor (C : Type*) (D : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Category D] := CategoryTheory.Functor C D
