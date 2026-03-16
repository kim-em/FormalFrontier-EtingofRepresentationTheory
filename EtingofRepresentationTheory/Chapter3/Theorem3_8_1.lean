import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.SupIndep
import Mathlib.Order.ModularLattice
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Decomposition
import EtingofRepresentationTheory.Chapter3.Lemma3_8_2

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

/-- Key step for Krull-Schmidt uniqueness: given an indecomposable direct summand W₀ in one
decomposition, find a matching indecomposable summand W'_{j₀} in another decomposition
that is isomorphic to W₀ via the projection map.

The proof uses Lemma 3.8.2: the projection from V onto W₀ restricts to endomorphisms of W₀
that sum to the identity. Since W₀ is indecomposable, by 3.8.2(ii) not all can be nilpotent,
so by 3.8.2(i) at least one is an isomorphism. -/
private lemma krull_schmidt_find_iso_summand (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, Etingof.IsIndecomposable A (W i))
    (hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥)
    (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W')
    (hn_pos : 0 < n) (hm_pos : 0 < m) :
    ∃ j : Fin m, Nonempty ((W ⟨0, hn_pos⟩) ≃ₗ[A] (W' j)) ∧
      IsCompl (W' j) (⨆ i, ⨆ (_ : i ≠ (⟨0, hn_pos⟩ : Fin n)), W i) := by
  set i₀ : Fin n := ⟨0, hn_pos⟩
  -- Build internal direct sum structures
  have hIntW : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).mpr ⟨hW_ind, hW_sup⟩
  have hIntW' : DirectSum.IsInternal W' :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W').mpr ⟨hW'_ind, hW'_sup⟩
  -- Get the decomposition equivalences
  set eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hIntW with eW_def
  set eW' := LinearEquiv.ofBijective (DirectSum.coeLinearMap W') hIntW' with eW'_def
  -- Define projection V → W i₀ using the first decomposition
  set π₀ : V →ₗ[A] ↥(W i₀) := (DirectSum.component A (Fin n) (fun i => ↥(W i)) i₀).comp eW.symm.toLinearMap
  -- Define projection V → W' j using the second decomposition
  set π' : ∀ j : Fin m, V →ₗ[A] ↥(W' j) :=
    fun j => (DirectSum.component A (Fin m) (fun j => ↥(W' j)) j).comp eW'.symm.toLinearMap
  -- For each j, define the endomorphism f_j : W i₀ → W i₀
  -- f_j = π₀ ∘ (W' j).subtype ∘ π'_j ∘ (W i₀).subtype
  set f : Fin m → Module.End A ↥(W i₀) :=
    fun j => (π₀.comp ((W' j).subtype.comp ((π' j).comp (W i₀).subtype)))
  -- Key claim: ∑ j, f j = id on W i₀
  -- Proof: π₀ ∘ ι₀ = id (projection-section), ∑ j, ι'_j ∘ π'_j = id_V (reconstruction)
  have hπ₀_ι₀ : π₀.comp (W i₀).subtype = LinearMap.id := by
    ext ⟨y, hy⟩
    simp only [π₀, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply]
    exact congrArg Subtype.val (hIntW.ofBijective_coeLinearMap_same ⟨y, hy⟩)
  have hrecon : ∀ v : V, ∑ j : Fin m, ((W' j).subtype ((π' j) v) : V) = v := by
    intro v
    -- π' j v = component j (eW'.symm v) = (eW'.symm v) j
    have hπ'_eq : ∀ j, π' j v = (eW'.symm v) j := fun j => rfl
    simp_rw [hπ'_eq]
    -- Now need: ∑ j, ι_j ((eW'.symm v) j) = v
    suffices h : ∀ (d : DirectSum (Fin m) (fun j => ↥(W' j))),
        (∑ j : Fin m, ((W' j).subtype (d j) : V)) = (DirectSum.coeLinearMap W') d by
      rw [h]; exact eW'.apply_symm_apply v
    intro d
    induction d using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [DirectSum.coeLinearMap_of]
      rw [Finset.sum_eq_single i]
      · simp [DirectSum.of_eq_same]
      · intro j _ hji; simp [DirectSum.of_eq_of_ne _ _ _ hji]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    | add x y hx hy =>
      simp only [map_add]
      simp_rw [show ∀ j : Fin m, (x + y) j = x j + y j from fun j => rfl,
        map_add, Finset.sum_add_distrib, hx, hy]
  have hf_sum : ∑ j, f j = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    -- Goal: ∑ j, π₀(ι'_j(π'_j(ι₀ ⟨x,hx⟩))) = ⟨x, hx⟩
    -- Factor out π₀ from the sum
    have h1 : (∑ j : Fin m, π₀ ((W' j).subtype ((π' j) ((W i₀).subtype ⟨x, hx⟩)))) =
        π₀ (∑ j : Fin m, ((W' j).subtype ((π' j) x) : V)) := by
      rw [map_sum]; rfl
    rw [h1, hrecon x]
    have := LinearMap.congr_fun hπ₀_ι₀ ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    exact congrArg Subtype.val this
  -- W i₀ is indecomposable and nontrivial
  have hW0_indec := hW_indec i₀
  have hW0_ne := hW_ne i₀
  -- Finite-dimensionality for submodules
  haveI : FiniteDimensional k ↥(W i₀) :=
    Module.Finite.of_injective ((W i₀).subtype.restrictScalars k) Subtype.val_injective
  -- Since ∑ f_j = id and id is not nilpotent (W i₀ ≠ 0), not all f_j are nilpotent
  have hW0_nontrivial : Nontrivial ↥(W i₀) :=
    Submodule.nontrivial_iff_ne_bot.mpr (hW_ne i₀)
  have hid_not_nilp : ¬ IsNilpotent (LinearMap.id : Module.End A ↥(W i₀)) := by
    rintro ⟨p, hp⟩
    simp at hp
    -- hp : LinearMap.id = 0
    obtain ⟨a, b, hab⟩ := hW0_nontrivial
    have h1 := LinearMap.congr_fun hp a
    have h2 := LinearMap.congr_fun hp b
    simp at h1 h2
    exact hab (h1.trans h2.symm)
  -- By Lemma 3.8.2(ii), not all f j are nilpotent
  have hf_not_all_nilp : ¬ ∀ j, IsNilpotent (f j) := by
    intro hall
    have := Etingof.sum_nilpotent_endo_indecomposable k A ↥(W i₀) hW0_indec f hall
    rw [hf_sum] at this
    exact hid_not_nilp this
  -- So there exists j₀ with f j₀ not nilpotent
  push_neg at hf_not_all_nilp
  obtain ⟨j₀, hj₀⟩ := hf_not_all_nilp
  -- By Lemma 3.8.2(i), f j₀ is bijective
  have hj₀_bij : Function.Bijective (f j₀) := by
    have := Etingof.endo_indecomposable_iso_or_nilpotent k A ↥(W i₀) hW0_indec (f j₀)
    tauto
  -- f j₀ = α ∘ β where α : W' j₀ → W i₀ and β : W i₀ → W' j₀
  set α : ↥(W' j₀) →ₗ[A] ↥(W i₀) := π₀.comp (W' j₀).subtype
  set β : ↥(W i₀) →ₗ[A] ↥(W' j₀) := (π' j₀).comp (W i₀).subtype
  have hf_eq : f j₀ = α.comp β := rfl
  -- Consider φ = β ∘ α : W' j₀ → W' j₀ (endomorphism of indecomposable W' j₀)
  set φ : Module.End A ↥(W' j₀) := β.comp α
  -- φ is not nilpotent: if (β ∘ α)^p = 0 then (α ∘ β)^(p+1) = α ∘ (β ∘ α)^p ∘ β = 0,
  -- contradicting f j₀ bijective
  have hφ_not_nilp : ¬ IsNilpotent φ := by
    intro ⟨p, hp⟩
    -- Key identity: (α ∘ β)^n ∘ α = α ∘ (β ∘ α)^n  (by induction)
    have key : ∀ (q : ℕ) (y : ↥(W' j₀)),
        ((α.comp β) ^ q) (α y) = α (((β.comp α) ^ q) y) := by
      intro q; induction q with
      | zero => intro y; simp
      | succ q ih =>
        intro y
        -- (α∘β)^(q+1)(α y) = (α∘β)^q((α∘β)(α y)) = (α∘β)^q(α(β(α y)))
        -- = α((β∘α)^q(β(α y))) = α((β∘α)^(q+1) y)
        simp only [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
        exact ih (β (α y))
    have hf_pow : (f j₀) ^ (p + 1) = 0 := by
      rw [hf_eq]
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.zero_apply, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
      rw [key p (β x), show ((β.comp α) ^ p) (β x) = 0 from LinearMap.congr_fun hp (β x)]
      simp
    have hf_unit : IsUnit (f j₀) := (Module.End.isUnit_iff _).mpr hj₀_bij
    exact not_isUnit_zero (hf_pow ▸ hf_unit.pow (p + 1))
  -- By Lemma 3.8.2(i), φ is bijective
  have hW'_indec_j₀ := hW'_indec j₀
  haveI : FiniteDimensional k ↥(W' j₀) :=
    Module.Finite.of_injective ((W' j₀).subtype.restrictScalars k) Subtype.val_injective
  have hφ_bij : Function.Bijective φ := by
    have := Etingof.endo_indecomposable_iso_or_nilpotent k A ↥(W' j₀) hW'_indec_j₀ φ
    tauto
  -- φ = β ∘ α bijective implies α injective
  have hα_inj : Function.Injective α := by
    intro a b h; exact hφ_bij.1 (show β (α a) = β (α b) by rw [h])
  -- α surjective from f j₀ = α ∘ β surjective
  have hα_surj : Function.Surjective α := by
    intro y; obtain ⟨x, hx⟩ := hj₀_bij.2 y
    rw [hf_eq] at hx; simp only [LinearMap.comp_apply] at hx
    exact ⟨β x, hx⟩
  set C := ⨆ i, ⨆ (_ : i ≠ i₀), W i
  -- W i₀ and C are complements in V (from the direct sum)
  have hIsCompl_W0_C : IsCompl (W i₀) C := by
    constructor
    · exact hW_ind i₀
    · rw [codisjoint_iff]
      apply top_le_iff.mp
      rw [← hW_sup]
      exact iSup_le fun i => by
        rcases eq_or_ne i i₀ with rfl | h
        · exact le_sup_left
        · exact le_sup_of_le_right (le_biSup _ h)
  -- α : W' j₀ → W i₀ is bijective, so W' j₀ is also a complement of C
  -- Construct projection g : V → W' j₀ with g ∘ subtype = id
  -- g = α⁻¹ ∘ π₀, where α : W' j₀ → W i₀ is the bijection via projection
  set αe := LinearEquiv.ofBijective α ⟨hα_inj, hα_surj⟩
  set g : V →ₗ[A] ↥(W' j₀) := αe.symm.toLinearMap.comp π₀
  have hg_proj : ∀ x : ↥(W' j₀), g ((W' j₀).subtype x) = x := by
    intro x
    show αe.symm (π₀ ↑x) = x
    have : π₀ ↑x = αe x := rfl
    rw [this, αe.symm_apply_apply]
  -- By isCompl_of_proj, IsCompl (W' j₀) (ker g)
  have hIsCompl_g : IsCompl (W' j₀) (LinearMap.ker g) :=
    LinearMap.isCompl_of_proj hg_proj
  -- ker g = C (ker g = ker π₀ since αe.symm is injective, and ker π₀ = C)
  have hker_g_eq_C : LinearMap.ker g = C := by
    -- ker g = ker (αe.symm ∘ π₀) = ker π₀ (since αe.symm is injective)
    have : LinearMap.ker g = LinearMap.ker π₀ := by
      ext v; simp only [g, LinearMap.mem_ker, LinearMap.comp_apply]
      constructor
      · intro h
        have h0 : αe.symm (π₀ v) = αe.symm 0 := by
          rw [map_zero]; exact h
        exact αe.symm.injective h0
      · intro h; simp [h]
    rw [this]
    -- Strategy: show C ≤ ker π₀, then use that both are complements of W i₀
    -- to conclude C = ker π₀
    have hπ₀_proj : IsCompl (W i₀) (LinearMap.ker π₀) :=
      LinearMap.isCompl_of_proj (fun x => LinearMap.congr_fun hπ₀_ι₀ x)
    -- C ≤ ker π₀: for v ∈ C, π₀ v = 0
    -- Use: linearProjOfIsCompl (W i₀) C hIsCompl_W0_C has kernel C
    -- and agrees with π₀ on W i₀ (both = id). Since they're both projections
    -- onto the same submodule with the same fixed point property, they agree.
    -- So ker π₀ = ker (linearProjOfIsCompl) = C.
    -- More directly: π₀ = linearProjOfIsCompl (W i₀) C hIsCompl_W0_C
    -- Both satisfy f ∘ subtype = id, and for projections in complemented spaces,
    -- there's a unique projection with given image and kernel.
    -- Use Submodule.linearProjOfIsCompl_eq_ofBijective or similar...
    -- Actually, let's use the uniqueness: if f, g : V →ₗ P are both
    -- left-inverses of subtype and P ⊕ ker f = V = P ⊕ ker g, then f = g.
    -- Simpler: linearProjOfIsCompl satisfies f ∘ subtype = id and ker f = C.
    -- Our π₀ satisfies π₀ ∘ subtype = id. The unique projection with this
    -- property and range in the given complement is linearProjOfIsCompl.
    -- C ≤ ker π₀: for v ∈ W i (i ≠ i₀), π₀ v = 0
    have hC_le : C ≤ LinearMap.ker π₀ := by
      -- C = ⨆ i ≠ i₀, W i. For v ∈ W i with i ≠ i₀, eW.symm v = DirectSum.of i ⟨v,_⟩
      -- and component i₀ of that is 0.
      apply iSup₂_le
      intro i hi v hv
      rw [LinearMap.mem_ker]
      show (DirectSum.component A (Fin n) (fun i => ↥(W i)) i₀) (eW.symm ((W i).subtype ⟨v, hv⟩)) = 0
      have heq : eW.symm ((W i).subtype ⟨v, hv⟩) = DirectSum.lof A (Fin n) (fun i => ↥(W i)) i ⟨v, hv⟩ := by
        apply eW.injective
        simp only [eW_def, LinearEquiv.ofBijective_apply, LinearEquiv.apply_symm_apply,
          DirectSum.coeLinearMap_of, Submodule.subtype_apply, DirectSum.lof_eq_of]
      rw [heq, DirectSum.component.of, dif_neg hi]
    -- ker π₀ ≤ C: use that ker π₀ ⊔ W i₀ = ⊤ and C ⊔ W i₀ = ⊤ and
    -- C ≤ ker π₀ together with W i₀ ⊓ ker π₀ = ⊥
    -- If C ≤ ker π₀ and both are complements of W i₀, then C = ker π₀
    -- Proof: ker π₀ ≤ C because:
    -- ker π₀ ≤ ker π₀ ⊔ ⊥ = ker π₀ ⊔ (W i₀ ⊓ C) ≤ (by modular law, since W i₀ ≤ W i₀)
    -- = (ker π₀ ⊔ C) ⊓ ... no, use: ker π₀ ≤ ⊤ = W i₀ ⊔ C, so
    -- ker π₀ = ker π₀ ⊓ (W i₀ ⊔ C) = (ker π₀ ⊓ W i₀) ⊔ C (modular law, C ≤ ker π₀)
    -- = ⊥ ⊔ C = C
    apply le_antisymm _ hC_le
    -- ker π₀ ≤ C via modular law:
    -- ker π₀ = ker π₀ ⊓ ⊤ = ker π₀ ⊓ (W i₀ ⊔ C) = C ⊔ (ker π₀ ⊓ W i₀) = C ⊔ ⊥ = C
    intro x hx
    have hx_top : x ∈ W i₀ ⊔ C := hIsCompl_W0_C.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hx_top
    -- x = w + c where w ∈ W i₀, c ∈ C
    -- x ∈ ker π₀ means π₀ x = 0, i.e., π₀ (w + c) = 0
    -- π₀ w = w (since π₀ ∘ subtype = id) and π₀ c = 0 (since c ∈ C ≤ ker π₀)
    -- So w = 0, hence x = c ∈ C
    rw [LinearMap.mem_ker] at hx
    have hπ₀c : π₀ c = 0 := LinearMap.mem_ker.mp (hC_le hc)
    have hπ₀_w : (π₀ w : ↥(W i₀)) = ⟨w, hw⟩ := LinearMap.congr_fun hπ₀_ι₀ ⟨w, hw⟩
    have : π₀ (w + c) = 0 := hx
    rw [map_add, hπ₀c, add_zero] at this
    rw [hπ₀_w] at this
    have hw_zero : w = 0 := congrArg Subtype.val (Subtype.ext_iff.mpr (congrArg Subtype.val this))
    rw [hw_zero, zero_add]
    exact hc
  have hIsCompl_Wj₀_C : IsCompl (W' j₀) C := hker_g_eq_C ▸ hIsCompl_g
  exact ⟨j₀, ⟨αe.symm⟩, hIsCompl_Wj₀_C⟩

/-- Two complements of the same submodule are isomorphic. If M ⊕ C = V = M ⊕ D,
then C ≃ₗ[R] D via the quotient V/M. -/
private lemma isCompl_equiv_of_isCompl {R : Type*} {V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    {M C D : Submodule R V}
    (hMC : IsCompl M C) (hMD : IsCompl M D) :
    Nonempty (C ≃ₗ[R] D) :=
  ⟨(Submodule.quotientEquivOfIsCompl M C hMC).symm.trans
    (Submodule.quotientEquivOfIsCompl M D hMD)⟩

/-- Auxiliary lemma for Krull-Schmidt uniqueness. Proved by induction on k-dimension.
Universally quantifies over the module type so the IH applies to the complement. -/
private lemma krull_schmidt_uniqueness_aux (k : Type*) (A : Type*) [Field k] [Ring A] [Algebra k A]
    (d : ℕ) : ∀ (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V], Module.finrank k V ≤ d →
    ∀ {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V),
    (∀ i, Etingof.IsIndecomposable A (W i)) →
    (∀ i, Etingof.IsIndecomposable A (W' i)) →
    (∀ i, W i ≠ ⊥) → (∀ i, W' i ≠ ⊥) →
    iSup W = ⊤ → iSup W' = ⊤ → iSupIndep W → iSupIndep W' →
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) := by
  induction d with
  | zero =>
    intro V _ _ _ _ _ hd n m W W' _ _ hW_ne hW'_ne hW_sup hW'_sup _ _
    have hV : Module.finrank k V = 0 := Nat.le_zero.mp hd
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hn0 : n = 0 := by
      by_contra h
      exact hW_ne ⟨0, Nat.pos_of_ne_zero h⟩ Submodule.eq_bot_of_subsingleton
    have hm0 : m = 0 := by
      by_contra h
      exact hW'_ne ⟨0, Nat.pos_of_ne_zero h⟩ Submodule.eq_bot_of_subsingleton
    subst hn0; subst hm0
    exact ⟨rfl, ⟨Equiv.refl _, nofun⟩⟩
  | succ d ih =>
    intro V _ _ _ _ _ hd n m W W' hW_indec hW'_indec hW_ne hW'_ne hW_sup hW'_sup hW_ind hW'_ind
    -- Handle n = 0 case
    by_cases hn : n = 0
    · subst hn
      have hm0 : m = 0 := by
        by_contra h
        have h_pos : 0 < m := Nat.pos_of_ne_zero h
        have : W' ⟨0, h_pos⟩ ≤ ⊤ := le_top
        have hV0 : (⊤ : Submodule A V) = ⊥ := by rw [← hW_sup]; simp
        rw [hV0] at this
        exact hW'_ne ⟨0, h_pos⟩ (eq_bot_iff.mpr this)
      subst hm0
      exact ⟨rfl, ⟨Equiv.refl _, nofun⟩⟩
    · -- n > 0 and m > 0
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hm_pos : 0 < m := by
        by_contra h_neg
        push_neg at h_neg
        interval_cases m
        have hV0 : (⊤ : Submodule A V) = ⊥ := by rw [← hW'_sup]; simp
        have h_le : W ⟨0, hn_pos⟩ ≤ ⊤ := le_top
        rw [hV0] at h_le
        exact hW_ne ⟨0, hn_pos⟩ (eq_bot_iff.mpr h_le)
      -- Step 1: Find j₀ such that W 0 ≅ W' j₀
      obtain ⟨j₀, hj₀_iso⟩ := krull_schmidt_find_iso_summand k A V W W'
        hW_indec hW'_indec hW_ne hW'_ne hW_sup hW_ind hW'_sup hW'_ind hn_pos hm_pos
      -- The remaining proof requires:
      -- Step 2: Show complements are isomorphic
      -- Step 3: Transport decompositions to the complement and apply IH
      -- Step 4: Combine the matching for index 0 with the IH matching
      sorry

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
    (hW_ne : ∀ i, W i ≠ ⊥)
    (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) :=
  krull_schmidt_uniqueness_aux k A (Module.finrank k V) V le_rfl
    W W' hW_indec hW'_indec hW_ne hW'_ne hW_sup hW'_sup hW_ind hW'_ind
