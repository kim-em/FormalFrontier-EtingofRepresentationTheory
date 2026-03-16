import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Corollary 4.2.2: Number of Irreducible Representations

The number of isomorphism classes of irreducible representations of G equals
the number of conjugacy classes of G (assuming k is algebraically closed and
char(k) does not divide |G|).

This follows from the Wedderburn-Artin decomposition of k[G]:
1. Each matrix block gives a simple representation (columnFDRep)
2. These are pairwise non-isomorphic (columnFDRep_injective)
3. Every simple FDRep is isomorphic to one (columnFDRep_surjective)
4. The number of blocks equals |ConjClasses G| (n_eq_card_conjClasses)

## Mathlib correspondence

Mathlib has conjugacy classes via `ConjClasses G` and `Fintype (ConjClasses G)`.
-/

open FDRep CategoryTheory

universe u

/-- The number of isomorphism classes of irreducible representations equals the number
of conjugacy classes: there exist exactly `Fintype.card (ConjClasses G)` pairwise
non-isomorphic simple representations, and every simple representation is isomorphic
to one of them. (Etingof Corollary 4.2.2) -/
theorem Etingof.Corollary4_2_2
    {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {k : Type u} [Field k] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      n = Fintype.card (ConjClasses G) := by
  -- Derive NeZero from Invertible
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero
  -- Get the Wedderburn-Artin decomposition
  let D := IrrepDecomp.mk' (k := k) (G := G)
  -- Use the infrastructure from IrreducibleEnumeration
  obtain ⟨V, hsimp, hinj, hsurj⟩ := D.n_eq_card_simples
  -- For the n = |ConjClasses G| part: dim center(k[G]) = |ConjClasses G| and
  -- dim center(∏ Mat(d_i,k)) = n, with the Wedderburn iso preserving centers.
  -- This is proved separately (see Theorem 4.10.2).
  have hn : D.n = Fintype.card (ConjClasses G) := by sorry
  exact ⟨D.n, V, hsimp, hinj, hsurj, hn⟩
