import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.JordanHolder

/-!
# Lemma 3.4.2: Existence of Filtration with Irreducible Successive Quotients

Any finite dimensional representation V of an algebra A admits a finite filtration
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V such that the successive quotients Vᵢ/Vᵢ₋₁ are irreducible.

The proof is by induction on dim(V): pick an irreducible subrepresentation V₁ ⊂ V,
apply the induction hypothesis to V/V₁.
-/

/-- Every finite dimensional representation admits a composition series (filtration with
irreducible successive quotients). Etingof Lemma 3.4.2. -/
theorem Etingof.exists_composition_series (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (s : CompositionSeries (Submodule A V)), s.head = ⊥ ∧ s.last = ⊤ := by
  sorry
