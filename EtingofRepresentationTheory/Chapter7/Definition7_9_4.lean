import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Definition 7.9.4: Semisimple Abelian Category

An abelian category C is **semisimple** if any short exact sequence in this category
splits, i.e., is isomorphic to a sequence 0 → X → X ⊕ Y → Y → 0 (where the maps
are obvious).

## Mathlib correspondence

Partial match. Mathlib has `CategoryTheory.Abelian` but no dedicated
`IsSemisimple` predicate for abelian categories. For module categories,
`IsSemisimpleRing` implies semisimplicity. This definition captures the concept
directly.
-/

open CategoryTheory

/-- An abelian category is semisimple if every short exact sequence splits.
(Etingof Definition 7.9.4)

Mathlib does not have a dedicated `IsSemisimple` class for abelian categories.
We define it as: for every short complex `S` that is short exact, there exists
a splitting of `S`. -/
def Etingof.IsSemisimpleCategory (C : Type*) [Category C] [Abelian C] : Prop :=
  ∀ (S : ShortComplex C), S.ShortExact → Nonempty S.Splitting
