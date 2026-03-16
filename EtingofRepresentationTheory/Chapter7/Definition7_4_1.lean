import Mathlib.CategoryTheory.Equivalence

/-!
# Definition 7.4.1: Equivalence of Categories

A functor F : C → D is an **equivalence of categories** if there exists F' : D → C
such that F ∘ F' and F' ∘ F are isomorphic to the identity functors.
F' is called a quasi-inverse to F.

## Mathlib correspondence

This is exactly `CategoryTheory.Equivalence`.
-/

/-- An equivalence of categories, in the sense of Etingof Definition 7.4.1.
This is `CategoryTheory.Equivalence` in Mathlib. -/
abbrev Etingof.Equivalence (C : Type*) (D : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Category D] := CategoryTheory.Equivalence C D
