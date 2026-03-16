import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Definition 7.9.4: Semisimple Abelian Category

An abelian category C is **semisimple** if any short exact sequence in this category
splits, i.e., is isomorphic to a sequence 0 → X → X ⊕ Y → Y → 0 (where the maps
are obvious).

## Mathlib correspondence

Partial match. Mathlib has `CategoryTheory.Abelian` but no dedicated
`IsSemisimple` predicate for abelian categories. For module categories,
`IsSemisimpleRing` implies semisimplicity. This definition captures the concept
with a sorry'd proposition.
-/

/-- An abelian category is semisimple if every short exact sequence splits.
(Etingof Definition 7.9.4)

Mathlib does not have a dedicated `IsSemisimple` class for abelian categories.
This is formalized as a Prop placeholder. -/
def Etingof.IsSemisimpleCategory (C : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] : Prop :=
  sorry
