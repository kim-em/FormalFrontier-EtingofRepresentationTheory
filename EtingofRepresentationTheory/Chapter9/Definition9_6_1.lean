import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple

universe u v

/-!
# Definition 9.6.1: Finite abelian category

A **finite abelian category** over a field k is an abelian category 𝒞 which has enough
projectives, and in which there are finitely many simple objects (up to isomorphism).

The primary example is the category of finite dimensional modules over a finite
dimensional k-algebra.

## Mathlib correspondence

Mathlib has `CategoryTheory.Abelian` for abelian categories and
`CategoryTheory.EnoughProjectives` for the enough projectives condition. The finiteness
condition on simple objects requires a custom predicate: we ask for a `Fintype` on the
type of isomorphism classes of simple objects.
-/

open CategoryTheory

/-- A finite abelian category in the sense of Etingof Definition 9.6.1.
An abelian category with enough projectives and finitely many isomorphism classes of
simple objects.

We encode "finitely many simples up to isomorphism" by requiring a finite type `ι`
indexing the simple objects, such that every simple object is isomorphic to one in the
indexed family. -/
class Etingof.IsFiniteAbelianCategory (C : Type u) [Category.{v} C] extends Abelian C,
    EnoughProjectives C where
  /-- An index type for the simple objects. -/
  ι : Type
  /-- The index type is finite. -/
  [finι : Fintype ι]
  /-- A representative simple object for each index. -/
  simpleObj : ι → C
  /-- Each representative is simple. -/
  simple_simpleObj : ∀ i, Simple (simpleObj i)
  /-- Every simple object is isomorphic to some representative. -/
  iso_of_simple : ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ simpleObj i)
