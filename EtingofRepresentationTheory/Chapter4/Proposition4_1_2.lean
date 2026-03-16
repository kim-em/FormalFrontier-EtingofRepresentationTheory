import Mathlib

/-!
# Proposition 4.1.2: Converse of Maschke's Theorem

If k[G] is semisimple, then char(k) does not divide |G|.

The proof considers the decomposition k[G] = k ⊕ ⊕ᵢ₌₂ʳ End(Vᵢ), the augmentation map
ε : k[G] → k sending each g to 1, and the element Λ = Σ_g g ∈ k[G]. By Schur's lemma,
Λ acts by zero on all non-trivial irreducible representations, so ε(Λ) = |G| · 1_k.
If |G| = 0 in k, then Λ is a non-zero element annihilating all irreducible representations,
contradicting semisimplicity.

## Mathlib correspondence

This is the converse direction of Maschke's theorem. The semisimplicity condition
is `IsSemisimpleRing (MonoidAlgebra k G)`.
-/

/-- Converse of Maschke's theorem: if k[G] is semisimple then char(k) does not
divide |G|. (Etingof Proposition 4.1.2) -/
theorem Etingof.Proposition4_1_2
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    [DecidableEq G]
    (h : IsSemisimpleRing (MonoidAlgebra k G)) :
    IsUnit ((Fintype.card G : k)) := by
  sorry
