import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Definition 9.4.1: Projective dimension

A module M has a **projective resolution** if there exists an exact sequence
… → P₁ → P₀ → M → 0 where each Pᵢ is projective.

The **projective dimension** pd(M) of M is the length of the shortest finite projective
resolution of M. If no finite projective resolution exists, pd(M) = ∞.

## Mathlib correspondence

Mathlib defines `CategoryTheory.projectiveDimension` for objects in an abelian category,
via vanishing of Ext groups. We specialize this to `ModuleCat R`.
-/

universe u

/-- The projective dimension of a module, in the sense of Etingof Definition 9.4.1.
Defined as `CategoryTheory.projectiveDimension` applied to the corresponding object
of `ModuleCat R`. Returns a value in `WithBot ℕ∞`: `⊥` if M is zero, a natural number
for the finite case, or `⊤` if no finite projective resolution exists. -/
noncomputable def Etingof.projectiveDimension
    (R : Type u) [Ring R] (M : ModuleCat.{u} R) : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension M
