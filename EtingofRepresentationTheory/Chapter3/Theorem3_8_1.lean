import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.SupIndep
import Mathlib.Order.ModularLattice

/-!
# Theorem 3.8.1: Krull-Schmidt Theorem

Any finite dimensional representation of A can be uniquely (up to isomorphism and the
order of summands) decomposed into a direct sum of indecomposable representations.

The existence of such a decomposition is clear. Uniqueness is proved by induction on dim V,
using Lemma 3.8.2 (endomorphisms of indecomposable representations are either isomorphisms
or nilpotent).
-/

/-- A module is indecomposable if it cannot be decomposed as a nontrivial direct sum
of two submodules. This matches the formulation used in Lemma 3.8.2. -/
def Etingof.IsIndecomposable (A : Type*) (W : Type*) [Ring A] [AddCommGroup W] [Module A W] :
    Prop :=
  ¬ ∃ (M N : Submodule A W), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥

/-- Auxiliary lemma for Krull-Schmidt existence: every A-submodule of V admits an
indecomposable decomposition. Proved by induction on k-dimension. -/
private lemma krull_schmidt_existence_aux (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    (d : ℕ) (S : Submodule A V) (hd : Module.finrank k (S.restrictScalars k) ≤ d) :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, W i ≤ S) ∧
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      (⨆ i, W i) = S ∧ iSupIndep W := by
  induction d generalizing S with
  | zero =>
    have hfin : Module.finrank k (S.restrictScalars k) = 0 := Nat.le_zero.mp hd
    have hS_bot : S.restrictScalars k = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hS : S = ⊥ := by rwa [Submodule.restrictScalars_eq_bot_iff] at hS_bot
    subst hS
    exact ⟨0, Fin.elim0, nofun, nofun, by simp, iSupIndep_subsingleton _⟩
  | succ d ih =>
    by_cases hIndec : Etingof.IsIndecomposable A S
    · exact ⟨1, fun _ => S, fun _ => le_refl S, fun _ => hIndec,
        by simp, iSupIndep_subsingleton _⟩
    · -- S is decomposable
      unfold Etingof.IsIndecomposable at hIndec
      push_neg at hIndec
      obtain ⟨M', N', hM'ne, hN'ne, hSup', hInf'⟩ := hIndec
      -- Map from submodules of ↥S to submodules of V
      set M := Submodule.map S.subtype M' with hM_def
      set N := Submodule.map S.subtype N' with hN_def
      -- Basic properties
      have hML : M ≤ S := Submodule.map_subtype_le S M'
      have hNL : N ≤ S := Submodule.map_subtype_le S N'
      have hMN_sup : M ⊔ N = S := by
        rw [hM_def, hN_def, ← Submodule.map_sup, hSup',
          Submodule.map_top, Submodule.range_subtype]
      have hMN_disj : Disjoint M N := by
        rw [disjoint_iff, hM_def, hN_def,
          ← Submodule.map_inf S.subtype S.injective_subtype,
          hInf', Submodule.map_bot]
      -- M' ≠ ⊤ and N' ≠ ⊤
      have hM'_ne_top : M' ≠ ⊤ := by
        intro h; rw [h, top_inf_eq] at hInf'; exact hN'ne hInf'
      have hN'_ne_top : N' ≠ ⊤ := by
        intro h; rw [h, inf_top_eq] at hInf'; exact hM'ne hInf'
      -- M < S
      have hM_lt_S : M < S := by
        refine lt_of_le_of_ne hML fun heq => hN'ne ?_
        have hN_le_M : N ≤ M := by rw [heq]; exact hMN_sup ▸ le_sup_right
        have hN_bot : N = ⊥ := eq_bot_iff.mpr (hMN_disj hN_le_M le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hN_bot.trans (Submodule.map_bot _).symm)
      -- N < S
      have hN_lt_S : N < S := by
        refine lt_of_le_of_ne hNL fun heq => hM'ne ?_
        have hM_le_N : M ≤ N := by rw [heq]; exact hMN_sup ▸ le_sup_left
        have hM_bot : M = ⊥ := eq_bot_iff.mpr (hMN_disj.symm hM_le_N le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hM_bot.trans (Submodule.map_bot _).symm)
      -- Finrank bounds
      have hM_finrank : Module.finrank k (M.restrictScalars k) ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt
          ((Submodule.restrictScalars_lt (S := k)).mpr hM_lt_S)
        omega
      have hN_finrank : Module.finrank k (N.restrictScalars k) ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt
          ((Submodule.restrictScalars_lt (S := k)).mpr hN_lt_S)
        omega
      -- Apply IH
      obtain ⟨nM, WM, hWM_le, hWM_indec, hWM_sup, hWM_ind⟩ := ih M hM_finrank
      obtain ⟨nN, WN, hWN_le, hWN_indec, hWN_sup, hWN_ind⟩ := ih N hN_finrank
      -- Combine via Sum.elim
      set W' : Fin nM ⊕ Fin nN → Submodule A V := Sum.elim WM WN with hW'_def
      have hW'_le : ∀ i, W' i ≤ S := by
        intro i; cases i with
        | inl j => exact le_trans (hWM_le j) hML
        | inr j => exact le_trans (hWN_le j) hNL
      have hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i) := by
        intro i; cases i with
        | inl j => exact hWM_indec j
        | inr j => exact hWN_indec j
      have hW'_sup : (⨆ i, W' i) = S := by
        simp only [W', iSup_sum, Sum.elim_inl, Sum.elim_inr, hWM_sup, hWN_sup, hMN_sup]
      have hW'_ind : iSupIndep W' := by
        intro i
        cases i with
        | inl j =>
          -- Need: Disjoint (WM j) (⨆ i ≠ Sum.inl j, W' i)
          -- Bound: complement ≤ (⨆ j' ≠ j, WM j') ⊔ N
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' =>
              exact le_sup_of_le_left
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inl h)) le_rfl))
            | inr j' => exact le_sup_of_le_right (le_iSup WN j')
          -- Key facts
          have hWM_j_le_M : WM j ≤ M := hWM_le j
          have hrest_le_M : (⨆ j', ⨆ (_ : j' ≠ j), WM j') ≤ M :=
            iSup₂_le fun j' _ => hWM_le j'
          have hN_eq : ⨆ j', WN j' = N := hWN_sup
          -- WM j ⊓ comp ≤ WM j ⊓ ((⨆ j' ≠ j, WM j') ⊔ N)
          --   ≤ M ⊓ ((⨆ j' ≠ j, WM j') ⊔ N)
          --   = (⨆ j' ≠ j, WM j') ⊔ (M ⊓ N)   [modular law, since rest ≤ M]
          --   = (⨆ j' ≠ j, WM j') ⊔ ⊥ = (⨆ j' ≠ j, WM j')
          -- Then WM j ⊓ comp ≤ WM j ⊓ (⨆ j' ≠ j, WM j') = ⊥
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
            calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
                ≤ WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ N) := by rw [hN_eq]
              _ ≤ M ⊓ (N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j')) := by
                  rw [sup_comm]; exact inf_le_inf_right _ hWM_j_le_M
              _ = M ⊓ N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                  (inf_sup_assoc_of_le N hrest_le_M).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WM j') := by
                  rw [disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
              ≤ WM j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWM_ind j)
        | inr j =>
          -- Symmetric to inl case: WN j ≤ N, complement ≤ M ⊔ (⨆ j' ≠ j, WN j')
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' => exact le_sup_of_le_left (le_iSup WM j')
            | inr j' =>
              exact le_sup_of_le_right
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inr h)) le_rfl))
          have hWN_j_le_N : WN j ≤ N := hWN_le j
          have hrest_le_N : (⨆ j', ⨆ (_ : j' ≠ j), WN j') ≤ N :=
            iSup₂_le fun j' _ => hWN_le j'
          have hM_eq : ⨆ j', WM j' = M := hWM_sup
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
            calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
                ≤ WN j ⊓ ((⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WN j ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) := by rw [hM_eq]
              _ ≤ N ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_right _ hWN_j_le_N
              _ = N ⊓ M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                  (inf_sup_assoc_of_le M hrest_le_N).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
                  rw [inf_comm, disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
              ≤ WN j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWN_ind j)
      -- Convert to Fin indexing
      refine ⟨nM + nN, W' ∘ finSumFinEquiv.symm, ?_, ?_, ?_, ?_⟩
      · intro i
        have : W' (finSumFinEquiv.symm i) ≤ S := hW'_le (finSumFinEquiv.symm i)
        exact this
      · intro i
        have : Etingof.IsIndecomposable A (W' (finSumFinEquiv.symm i)) :=
          hW'_indec (finSumFinEquiv.symm i)
        exact this
      · rw [show (⨆ i, (W' ∘ finSumFinEquiv.symm) i) = ⨆ i, W' i from
          finSumFinEquiv.symm.surjective.iSup_comp W', hW'_sup]
      · exact hW'_ind.comp finSumFinEquiv.symm.injective

/-- Existence part of Krull-Schmidt: any finite dimensional representation admits an
internal direct sum decomposition into indecomposable submodules.
Etingof Theorem 3.8.1 (existence). -/
theorem Etingof.krull_schmidt_existence (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      iSup W = ⊤ ∧ iSupIndep W := by
  obtain ⟨n, W, _, hindec, hsup, hind⟩ := krull_schmidt_existence_aux k A V
    (Module.finrank k V) ⊤ (by simp [Submodule.restrictScalars_top])
  exact ⟨n, W, hindec, hsup, hind⟩

/-- Uniqueness part of Krull-Schmidt: any two decompositions into indecomposable
direct summands have the same number of summands, and the summands can be matched
up to isomorphism after reindexing.
Etingof Theorem 3.8.1 (uniqueness). -/
theorem Etingof.krull_schmidt_uniqueness (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, Etingof.IsIndecomposable A (W i))
    (hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i))
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) := by
  sorry
