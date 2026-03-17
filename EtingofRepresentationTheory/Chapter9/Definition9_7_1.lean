import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

universe u v

/-!
# Definition 9.7.1: Morita equivalence

Two finite dimensional algebras A and B are **Morita equivalent** if the categories
A-fmod and B-fmod are equivalent as abelian categories.

## Mathlib correspondence

This can be expressed as `CategoryTheory.Equivalence (ModuleCat R) (ModuleCat S)` in Mathlib,
though the finite-dimensional constraint requires additional bundling.
-/

/-- Morita equivalence of algebras, in the sense of Etingof Definition 9.7.1.
Two algebras A and B are Morita equivalent if their module categories are equivalent.
The book restricts to finite-dimensional modules, but we use the full module category
as Mathlib does not have a standalone finite-dimensional module category. -/
def Etingof.MoritaEquivalent (A : Type u) [Ring A] (B : Type v) [Ring B] : Prop :=
  Nonempty (ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)
