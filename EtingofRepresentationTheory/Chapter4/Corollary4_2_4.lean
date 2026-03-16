import Mathlib

/-!
# Corollary 4.2.4: Representations Determined by Characters

If k has characteristic 0, any finite dimensional representation of G is determined
by its character: χ_V = χ_W implies V ≅ W.
-/

open FDRep CategoryTheory CategoryTheory.Limits Module

/-- Equal characters ⟹ equal Hom-space dimensions from any S. -/
private lemma hom_finrank_eq_of_char_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W)
    (S : FDRep ℂ G) :
    finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W) := by
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1 := scalar_product_char_eq_finrank_equivariant S V
  have h2 := scalar_product_char_eq_finrank_equivariant S W
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

/-- Equal characters imply equal dimension. -/
private lemma finrank_eq_of_char_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    finrank ℂ V = finrank ℂ W := by
  have h1 := FDRep.char_one V
  have h2 := FDRep.char_one W
  have h3 := congr_fun h 1
  exact_mod_cast h1.symm.trans (h3.trans h2)

/-- In a semisimple category (FDRep ℂ G), objects with equal Hom-space dimensions
from every object are isomorphic. This is the categorical core: it uses semisimplicity
(Maschke) and Schur's lemma to match simple constituents. -/
private lemma iso_of_hom_finrank_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : ∀ S : FDRep ℂ G, finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) :
    Nonempty (V ≅ W) := by
  by_cases hV : IsZero V
  · -- V is zero. Show W is also zero.
    have hWV : Subsingleton (W ⟶ V) := ⟨fun f g => hV.eq_of_tgt f g⟩
    have h1 : finrank ℂ (W ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
    have h2 : finrank ℂ (W ⟶ W) = 0 := by rw [← h W]; exact h1
    have hWW : Subsingleton (W ⟶ W) := (Module.finrank_zero_iff.mp h2)
    have hW : IsZero W := by
      rw [IsZero.iff_id_eq_zero]
      exact Subsingleton.eq_zero _
    exact ⟨hV.iso hW⟩
  · -- V is nonzero. Use semisimplicity to extract a simple summand.
    sorry

/-- In characteristic 0, representations are determined by their characters.
(Etingof Corollary 4.2.4) -/
theorem Etingof.Corollary4_2_4
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    Nonempty (V ≅ W) :=
  iso_of_hom_finrank_eq V W (hom_finrank_eq_of_char_eq V W h)
