import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Definition 7.7.1: Abelian Category

An **abelian category** is a category (enriched over the category of abelian groups)
which is equivalent to a full subcategory C of the category A-mod of left modules
over a ring A, closed under taking finite direct sums, as well as kernels, cokernels,
and images of morphisms.

## Mathlib correspondence

This is exactly `CategoryTheory.Abelian`. Mathlib's definition is intrinsic (not via
embedding into a module category) but is equivalent by the Freyd-Mitchell embedding theorem.
-/

/-- An abelian category in the sense of Etingof Definition 7.7.1.
This is `CategoryTheory.Abelian` in Mathlib. -/
abbrev Etingof.Abelian (C : Type*) [CategoryTheory.Category C] :=
  CategoryTheory.Abelian C
