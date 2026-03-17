import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Definition 9.4.3: Homological dimension of a ring

A ring A is said to have (left) **homological dimension** ≤ d if every (left)
A-module has projective dimension ≤ d. The smallest such d is the homological dimension
of A. If no such d exists, the homological dimension is infinite.

## Mathlib correspondence

Not directly in Mathlib. We define `HasHomologicalDimensionLE` as a predicate and
`homologicalDimension` as the infimum, both in terms of
`CategoryTheory.HasProjectiveDimensionLE` on `ModuleCat R`.
-/

universe u

/-- A ring R has homological dimension ≤ d if every R-module has projective dimension ≤ d,
in the sense of Etingof Definition 9.4.3. -/
def Etingof.HasHomologicalDimensionLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (M : ModuleCat.{u} R), CategoryTheory.HasProjectiveDimensionLE M d

/-- The homological dimension of a ring, in the sense of Etingof Definition 9.4.3.
The smallest d such that every module has projective dimension ≤ d, or ⊤ if no such d exists.
Returns a value in `ℕ∞`. -/
noncomputable def Etingof.homologicalDimension (R : Type u) [Ring R] : ℕ∞ :=
  ⨅ (d : ℕ) (_ : Etingof.HasHomologicalDimensionLE R d), (d : ℕ∞)
