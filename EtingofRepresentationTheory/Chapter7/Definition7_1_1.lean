import Mathlib.CategoryTheory.Category.Basic

/-!
# Definition 7.1.1: Category

A **category** C is defined by:
- A class of objects Ob(C)
- For every pair of objects X, Y, a class Hom_C(X, Y) of morphisms
- For any objects X, Y, Z, a composition map: Hom(Y, Z) × Hom(X, Y) → Hom(X, Z)

With axioms:
1. Composition is associative
2. For each X, there exists a unit morphism 1_X ∈ Hom(X, X)

## Mathlib correspondence

This is exactly `CategoryTheory.Category`. Mathlib categories are universe-polymorphic
and use type classes.
-/

/-- A category in the sense of Etingof Definition 7.1.1.
This is `CategoryTheory.Category` in Mathlib. -/
abbrev Etingof.Category (C : Type*) := CategoryTheory.Category C
