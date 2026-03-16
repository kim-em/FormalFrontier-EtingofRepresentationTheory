import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Definition 7.1.4: Full Subcategory

A **full subcategory** of a category C is a category C' whose objects are a subclass
of objects of C, and Hom_{C'}(X, Y) = Hom_C(X, Y).

## Mathlib correspondence

This is exactly `CategoryTheory.FullSubcategory` / `CategoryTheory.InducedCategory`.
A full subcategory is determined by a predicate on objects.
-/

/-- A full subcategory of C determined by a predicate P on objects,
in the sense of Etingof Definition 7.1.4.
This is `CategoryTheory.FullSubcategory` in Mathlib. -/
abbrev Etingof.FullSubcategory (C : Type*) [CategoryTheory.Category C]
    (P : CategoryTheory.ObjectProperty C) := P.FullSubcategory
