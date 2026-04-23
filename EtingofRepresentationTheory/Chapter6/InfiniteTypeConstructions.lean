import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification

/-!
# Infinite Type Constructions for Non-Dynkin Graphs

This file proves that graphs containing cycle subgraphs have infinite representation
type, providing one direction of the contrapositive needed for the forward direction
of Gabriel's theorem (Problem 6.1.5).
-/

open scoped Matrix ComplexOrder
open Finset

namespace Etingof

/-! ## Section 1: Nilpotent shift operator -/

noncomputable def nilpotentShiftMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

noncomputable def nilpotentShiftLin (m : ℕ) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
  Matrix.mulVecLin (nilpotentShiftMatrix m)

private theorem mulVecLin_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix.mulVecLin (M ^ k) = (Matrix.mulVecLin M) ^ k := by
  induction k with
  | zero => ext v; simp [Matrix.mulVecLin_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mulVecLin_mul, ih]
    rfl

private theorem nilpotentShiftMatrix_pow_entry (m n : ℕ) (a b : Fin (m + 1)) :
    (nilpotentShiftMatrix m ^ n) a b = if b.val = a.val + n then 1 else 0 := by
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.add_zero, Matrix.one_apply]
    congr 1; exact propext ⟨fun h => (Fin.val_eq_of_eq h).symm, fun h => Fin.ext h.symm⟩
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hb : b.val = a.val + (n + 1)
    · have hbn : a.val + n < m + 1 := by omega
      rw [show (if b.val = a.val + (n + 1) then (1 : ℂ) else 0) = 1 from if_pos hb]
      rw [Finset.sum_eq_single ⟨a.val + n, hbn⟩]
      · rw [ih]; simp only [ite_true, one_mul, nilpotentShiftMatrix]
        rw [if_pos (by show b.val = (a.val + n) + 1; omega)]
      · intro c _ hc; rw [ih]; split_ifs with h1
        · exfalso; exact hc (Fin.ext h1)
        · ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [show (if b.val = a.val + (n + 1) then (1 : ℂ) else 0) = 0 from if_neg hb]
      apply Finset.sum_eq_zero; intro c _; rw [ih]; split_ifs with h1
      · simp only [one_mul, nilpotentShiftMatrix]; rw [if_neg]; intro hbc; exact hb (by omega)
      · ring

theorem nilpotentShiftLin_nilpotent (m : ℕ) :
    IsNilpotent (nilpotentShiftLin m) := by
  use m + 1
  have hmat : nilpotentShiftMatrix m ^ (m + 1) = 0 := by
    ext i j; rw [nilpotentShiftMatrix_pow_entry, Matrix.zero_apply, if_neg]
    intro h; exact absurd h (by have := j.isLt; omega)
  change (nilpotentShiftLin m) ^ (m + 1) = 0
  rw [nilpotentShiftLin, ← mulVecLin_pow, hmat, Matrix.mulVecLin_zero]

private theorem nilpotentShiftLin_apply (m : ℕ) (v : Fin (m + 1) → ℂ) (i : Fin (m + 1)) :
    nilpotentShiftLin m v i = if h : i.val + 1 < m + 1 then v ⟨i.val + 1, h⟩ else 0 := by
  simp only [nilpotentShiftLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    nilpotentShiftMatrix]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp
    · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hbi; exact hb (Fin.ext (by omega))
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero; intro j _
    simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
    intro hji; exact h (by have := j.isLt; omega)

theorem nilpotentShiftLin_ker_finrank (m : ℕ) :
    Module.finrank ℂ (LinearMap.ker (nilpotentShiftLin m)) = 1 := by
  -- The kernel is {v | v(j) = 0 for j ≥ 1} = span{e₀}
  -- We build a linear equiv ker ≃ ℂ
  have hker_fwd : ∀ v : Fin (m + 1) → ℂ, nilpotentShiftLin m v = 0 →
      ∀ j : Fin (m + 1), 0 < j.val → v j = 0 := by
    intro v hv j hj
    have h1 : nilpotentShiftLin m v ⟨j.val - 1, by omega⟩ = 0 := by
      simp [hv]
    rw [nilpotentShiftLin_apply] at h1
    have h2 : (j.val - 1) + 1 < m + 1 := by omega
    rw [dif_pos h2] at h1
    have h3 : (⟨(j.val - 1) + 1, h2⟩ : Fin (m + 1)) = j := by
      ext; show (j.val - 1) + 1 = j.val; omega
    rwa [h3] at h1
  have hker_bwd : ∀ v : Fin (m + 1) → ℂ,
      (∀ j : Fin (m + 1), 0 < j.val → v j = 0) → nilpotentShiftLin m v = 0 := by
    intro v hv; ext i; simp only [Pi.zero_apply]
    rw [nilpotentShiftLin_apply]
    split_ifs with h
    · exact hv ⟨i.val + 1, h⟩ (by simp)
    · rfl
  suffices h : LinearMap.ker (nilpotentShiftLin m) =
      Submodule.span ℂ {Pi.single (0 : Fin (m + 1)) (1 : ℂ)} by
    rw [h, finrank_span_singleton]
    simp [Pi.single_eq_zero_iff]
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have hvj := hker_fwd v hv
    refine ⟨v 0, funext fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj; simp [Pi.single_apply]
    · have hjz := hvj j (Fin.pos_iff_ne_zero.mpr hj)
      simp [Pi.single_apply, hj, hjz]
  · intro ⟨c, hcv⟩
    apply hker_bwd
    intro j hj
    rw [← hcv]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [if_neg (show j ≠ (0 : Fin (m + 1)) from by intro h; subst h; simp at hj)]

/-! ## Section 2: Nilpotent-invariant complement triviality -/

-- Helper: nilpotent endomorphism on nontrivial space has nontrivial kernel
private theorem ker_ne_bot_of_isNilpotent
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (N : V →ₗ[ℂ] V) (hN : IsNilpotent N) :
    LinearMap.ker N ≠ ⊥ := by
  obtain ⟨k, hk⟩ := hN
  rw [Submodule.ne_bot_iff]
  -- Pick any nonzero v. Since N^k v = 0, find minimal j with N^j v = 0.
  -- Then N^(j-1) v ≠ 0 and N(N^(j-1) v) = 0, so N^(j-1) v ∈ ker N \ {0}.
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  classical
  -- Find the first j ≤ k such that N^j v = 0
  have hNkv : (N ^ k) v = 0 := by rw [hk]; simp
  -- Use strong induction / Nat.find
  have hex : ∃ j, (N ^ j) v = 0 := ⟨k, hNkv⟩
  set j := Nat.find hex with hj_def
  have hj_spec : (N ^ j) v = 0 := Nat.find_spec hex
  have hj_min : ∀ i < j, (N ^ i) v ≠ 0 := fun i hi => Nat.find_min hex hi
  by_cases hj_pos : 0 < j
  · refine ⟨(N ^ (j - 1)) v, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      have hjsucc : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj_pos
      have : (N ^ j) v = 0 := hj_spec
      rw [← hjsucc] at this
      rwa [pow_succ'] at this
    · exact hj_min (j - 1) (Nat.sub_lt hj_pos Nat.one_pos)
  · exfalso; push_neg at hj_pos; interval_cases j; simp at hj_spec; exact hv hj_spec

theorem nilpotent_invariant_compl_trivial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (N : V →ₗ[ℂ] V) (hN : IsNilpotent N)
    (hker : Module.finrank ℂ (LinearMap.ker N) = 1)
    (W₁ W₂ : Submodule ℂ V)
    (hW₁_inv : ∀ x ∈ W₁, N x ∈ W₁)
    (hW₂_inv : ∀ x ∈ W₂, N x ∈ W₂)
    (hcompl : IsCompl W₁ W₂) :
    W₁ = ⊥ ∨ W₂ = ⊥ := by
  -- By contradiction: if both W₁ ≠ ⊥ and W₂ ≠ ⊥, the restriction of N
  -- to each is nilpotent with nontrivial kernel, giving dim(ker N) ≥ 2.
  by_contra h
  push_neg at h
  obtain ⟨hW₁_ne, hW₂_ne⟩ := h
  -- The restrictions are nilpotent
  have hmap₁ : Set.MapsTo N W₁ W₁ := fun x hx => hW₁_inv x hx
  have hmap₂ : Set.MapsTo N W₂ W₂ := fun x hx => hW₂_inv x hx
  have hN₁ := Module.End.isNilpotent.restrict hmap₁ hN
  have hN₂ := Module.End.isNilpotent.restrict hmap₂ hN
  -- Each W_i is nontrivial
  have hnt₁ : Nontrivial W₁ := Submodule.nontrivial_iff_ne_bot.mpr hW₁_ne
  have hnt₂ : Nontrivial W₂ := Submodule.nontrivial_iff_ne_bot.mpr hW₂_ne
  -- Each restriction has nontrivial kernel
  have hker₁ := ker_ne_bot_of_isNilpotent (N.restrict hmap₁) hN₁
  have hker₂ := ker_ne_bot_of_isNilpotent (N.restrict hmap₂) hN₂
  -- Extract nonzero elements in ker(N) ∩ W₁ and ker(N) ∩ W₂
  rw [Submodule.ne_bot_iff] at hker₁ hker₂
  obtain ⟨⟨w₁, hw₁_mem⟩, hw₁_ker, hw₁_ne⟩ := hker₁
  obtain ⟨⟨w₂, hw₂_mem⟩, hw₂_ker, hw₂_ne⟩ := hker₂
  simp only [LinearMap.mem_ker, Submodule.ne_bot_iff] at hw₁_ker hw₂_ker
  -- w₁ and w₂ are in ker(N)
  have hw₁_inker : w₁ ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker]
    have := hw₁_ker
    simp only [LinearMap.restrict_apply, Subtype.ext_iff] at this
    exact this
  have hw₂_inker : w₂ ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker]
    have := hw₂_ker
    simp only [LinearMap.restrict_apply, Subtype.ext_iff] at this
    exact this
  -- w₁ ≠ 0 and w₂ ≠ 0
  have hw₁_ne0 : w₁ ≠ 0 := fun h => hw₁_ne (Subtype.ext h)
  have hw₂_ne0 : w₂ ≠ 0 := fun h => hw₂_ne (Subtype.ext h)
  -- ker(N) has dim 1, so all nonzero elements are scalar multiples of each other.
  -- In particular, w₂ = c • w₁ for some c.
  -- But w₁ ∈ W₁ implies c • w₁ ∈ W₁, so w₂ ∈ W₁ ∩ W₂ = {0}. Contradiction.
  have hw₁_ker_elt : (⟨w₁, hw₁_inker⟩ : ↥(LinearMap.ker N)) ≠ 0 := by
    simp [Subtype.ext_iff]; exact hw₁_ne0
  have hdim1 := (finrank_eq_one_iff_of_nonzero' (⟨w₁, hw₁_inker⟩ : ↥(LinearMap.ker N))
    hw₁_ker_elt).mp hker (⟨w₂, hw₂_inker⟩ : ↥(LinearMap.ker N))
  obtain ⟨c, hc⟩ := hdim1
  have hw₂_eq : w₂ = c • w₁ := by
    have := congr_arg Subtype.val hc
    simpa [Submodule.coe_smul] using this.symm
  have hw₂_in_W₁ : w₂ ∈ W₁ := hw₂_eq ▸ W₁.smul_mem c hw₁_mem
  have hmem : w₂ ∈ W₁ ⊓ W₂ := Submodule.mem_inf.mpr ⟨hw₂_in_W₁, hw₂_mem⟩
  rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hw₂_ne0 hmem

/-! ## Section 3: Cycle quiver definitions and orientation -/

def cycleAdj (k : ℕ) (hk : 3 ≤ k) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if j.val = (i.val + 1) % k ∨ i.val = (j.val + 1) % k then 1 else 0

theorem cycleAdj_symm (k : ℕ) (hk : 3 ≤ k) : (cycleAdj k hk).IsSymm := by
  ext i j; simp only [cycleAdj, Matrix.transpose_apply]; congr 1
  exact propext or_comm

theorem cycleAdj_diag (k : ℕ) (hk : 3 ≤ k) (i : Fin k) :
    cycleAdj k hk i i = 0 := by
  simp only [cycleAdj]; rw [if_neg]; push_neg
  have hi := i.isLt
  constructor <;> intro h
  · -- i.val ≠ (i.val + 1) % k
    have := Nat.mod_lt (i.val + 1) (by omega : 0 < k)
    by_cases hlt : i.val + 1 < k
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have : i.val + 1 = k := by omega
      rw [this, Nat.mod_self] at h; omega
  · -- same goal: i.val ≠ (i.val + 1) % k
    have := Nat.mod_lt (i.val + 1) (by omega : 0 < k)
    by_cases hlt : i.val + 1 < k
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have : i.val + 1 = k := by omega
      rw [this, Nat.mod_self] at h; omega

theorem cycleAdj_01 (k : ℕ) (hk : 3 ≤ k) (i j : Fin k) :
    cycleAdj k hk i j = 0 ∨ cycleAdj k hk i j = 1 := by
  simp only [cycleAdj]; split_ifs <;> simp

/-- The cycle quiver: vertex i has an arrow to vertex (i+1) mod k.
    Uses PLift to wrap the Prop into Type 0, matching Quiver's Hom : V → V → Type v. -/
def cycleQuiver (k : ℕ) (_ : 3 ≤ k) : Quiver (Fin k) where
  Hom i j := PLift (j.val = (i.val + 1) % k)

instance cycleQuiver_subsingleton (k : ℕ) (hk : 3 ≤ k) (a b : Fin k) :
    Subsingleton (@Quiver.Hom (Fin k) (cycleQuiver k hk) a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

theorem cycleOrientation_isOrientationOf (k : ℕ) (hk : 3 ≤ k) :
    @Etingof.IsOrientationOf k (cycleQuiver k hk) (cycleAdj k hk) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows: IsEmpty (PLift (j.val = (i.val+1) % k))
    constructor; intro ⟨hp⟩
    simp only [cycleAdj] at hij
    simp only [hp, true_or, ↓reduceIte] at hij
    exact hij rfl
  · -- Each edge has an arrow in one direction
    simp only [cycleAdj] at hij
    split_ifs at hij with h
    · rcases h with h | h
      · left; exact ⟨⟨h⟩⟩
      · right; exact ⟨⟨h⟩⟩
    · simp at hij
  · -- No two-way arrows: j.val = (i.val+1)%k and i.val = (j.val+1)%k → False
    obtain ⟨⟨h1⟩⟩ := hi
    obtain ⟨⟨h2⟩⟩ := hj
    rw [h1] at h2
    -- h2 : i.val = ((i.val + 1) % k + 1) % k
    have hi_lt := i.isLt
    by_cases hlt : i.val + 1 < k
    · rw [Nat.mod_eq_of_lt hlt] at h2
      by_cases hlt2 : i.val + 2 < k
      · rw [Nat.mod_eq_of_lt hlt2] at h2; omega
      · rw [show i.val + 1 + 1 = k from by omega, Nat.mod_self] at h2; omega
    · rw [show i.val + 1 = k from by omega, Nat.mod_self] at h2
      rw [Nat.mod_eq_of_lt (show 1 < k by omega)] at h2
      omega

/-! ## Section 4: Cycle representation construction -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def cycleRep (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin k) _ (cycleQuiver k hk) := by
  letI := cycleQuiver k hk
  exact { obj := fun _ => Fin (m + 1) → ℂ
          mapLinear := fun {v _} _ =>
            if v.val = k - 1 then nilpotentShiftLin m else LinearMap.id }

/-! ## Section 5: Indecomposability of cycle representations -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRep_isIndecomposable (k : ℕ) (hk : 3 ≤ k) (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin k)
      (cycleQuiver k hk) (cycleRep k hk m) := by
  letI := cycleQuiver k hk
  constructor
  · refine ⟨⟨0, by omega⟩, ?_⟩
    change Nontrivial (Fin (m + 1) → ℂ)
    infer_instance
  · intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- The cycle quiver has arrows v → (v+1)%k. For non-last vertices (v ≠ k-1),
    -- the map is id; for v = k-1, it's nilpotentShiftLin.
    -- Step 1: For non-last arrows (v.val + 1 < k), the map is id.
    -- Invariance under id gives W₁(v) ≤ W₁(v+1).
    have hle_succ : ∀ (W : ∀ v, Submodule ℂ ((cycleRep k hk m).obj v)),
        (∀ {a b : Fin k} (e : @Quiver.Hom _ (cycleQuiver k hk) a b),
          ∀ x ∈ W a, (cycleRep k hk m).mapLinear e x ∈ W b) →
        ∀ (v : Fin k) (hv : v.val + 1 < k), W v ≤ W ⟨v.val + 1, hv⟩ := by
      intro W hW_inv v hv x hx
      have harrow : @Quiver.Hom (Fin k) (cycleQuiver k hk) v
          ⟨v.val + 1, by omega⟩ := ⟨by simp [Nat.mod_eq_of_lt hv]⟩
      have := hW_inv harrow x hx
      simp only [cycleRep] at this
      have hne : v.val ≠ k - 1 := by have := v.isLt; omega
      rw [if_neg hne] at this
      exact this
    -- Chain: W(i) ≤ W(j) for i ≤ j < k
    have hchain_mono : ∀ (W : ∀ v, Submodule ℂ ((cycleRep k hk m).obj v)),
        (∀ {a b : Fin k} (e : @Quiver.Hom _ (cycleQuiver k hk) a b),
          ∀ x ∈ W a, (cycleRep k hk m).mapLinear e x ∈ W b) →
        ∀ (i j : ℕ) (hi : i < k) (hj : j < k), i ≤ j → W ⟨i, hi⟩ ≤ W ⟨j, hj⟩ := by
      intro W hW_inv i j hi hj hij
      induction j with
      | zero => simp at hij; subst hij; exact le_of_eq (by congr 1)
      | succ n ih =>
        rcases Nat.eq_or_lt_of_le hij with rfl | hlt
        · exact le_refl _
        · exact le_trans (ih (by omega) (by omega)) (hle_succ W hW_inv ⟨n, by omega⟩ hj)
    -- In particular: W₁(0) ≤ W₁(k-1) and W₂(0) ≤ W₂(k-1)
    -- Step 2: The shift (arrow k-1 → 0) sends W(k-1) into W(0) ≤ W(k-1).
    -- So the shift preserves W(k-1).
    set last : Fin k := ⟨k - 1, by omega⟩
    have hlast_arrow : @Quiver.Hom (Fin k) (cycleQuiver k hk) last
        ⟨0, by omega⟩ := ⟨by
          show (0 : ℕ) = (k - 1 + 1) % k
          rw [show k - 1 + 1 = k from by omega, Nat.mod_self]⟩
    have hshift₁ : ∀ x ∈ W₁ last, nilpotentShiftLin m x ∈ W₁ last := by
      intro x hx
      have h_in_0 := hW₁_inv hlast_arrow x hx
      simp only [cycleRep, show last.val = k - 1 from rfl, ite_true] at h_in_0
      exact hchain_mono W₁ hW₁_inv 0 (k - 1) (by omega) (by omega) (by omega) h_in_0
    have hshift₂ : ∀ x ∈ W₂ last, nilpotentShiftLin m x ∈ W₂ last := by
      intro x hx
      have h_in_0 := hW₂_inv hlast_arrow x hx
      simp only [cycleRep, show last.val = k - 1 from rfl, ite_true] at h_in_0
      exact hchain_mono W₂ hW₂_inv 0 (k - 1) (by omega) (by omega) (by omega) h_in_0
    -- Step 3: Apply nilpotent_invariant_compl_trivial
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ last) (W₂ last) hshift₁ hshift₂ (hcompl last)
    -- Step 4: If W₁(k-1) = ⊥, then W₁(v) = ⊥ for all v (since W₁(v) ≤ W₁(k-1))
    rcases hresult with h | h
    · left; intro v
      have : W₁ v ≤ W₁ last :=
        hchain_mono W₁ hW₁_inv v.val (k - 1) v.isLt (by omega) (by omega)
      rwa [h, le_bot_iff] at this
    · right; intro v
      have : W₂ v ≤ W₂ last :=
        hchain_mono W₂ hW₂_inv v.val (k - 1) v.isLt (by omega) (by omega)
      rwa [h, le_bot_iff] at this

/-! ## Section 6: Dimension vector and infinite type -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem cycleRep_dimVec (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (v : Fin k) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin k) _
      (cycleQuiver k hk) (cycleRep k hk m) v ≃ₗ[ℂ] (Fin (m + 1) → ℂ)) :=
  ⟨LinearEquiv.refl ℂ _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The cycle graph on k ≥ 3 vertices has infinite representation type. -/
theorem cycle_not_finite_type (k : ℕ) (hk : 3 ≤ k) :
    ¬ Etingof.IsFiniteTypeQuiver k (cycleAdj k hk) := by
  intro hft
  letI := cycleQuiver k hk
  have hfin := @hft ℂ _ inferInstance (cycleQuiver k hk)
    (fun a b => cycleQuiver_subsingleton k hk a b)
    (cycleOrientation_isOrientationOf k hk)
  have hmem : ∀ m : ℕ, (fun (_ : Fin k) => m + 1) ∈
      {d : Fin k → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin k),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨cycleRep k hk m, cycleRep_isIndecomposable k hk m, cycleRep_dimVec k hk m⟩
  have hinj : Function.Injective (fun m : ℕ => (fun (_ : Fin k) => m + 1)) := by
    intro m₁ m₂ h
    have : m₁ + 1 = m₂ + 1 := congr_fun h ⟨0, by omega⟩
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 7: Star graph K_{1,4} (D̃₄) definitions -/

/-- The star graph K_{1,4}: vertex 0 is the center, vertices 1-4 are leaves.
    adj i j = 1 iff exactly one of i,j is 0. -/
def starAdj : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j =>
    if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then 1 else 0

theorem starAdj_symm : starAdj.IsSymm := by
  ext i j; simp only [starAdj, Matrix.transpose_apply]; congr 1
  exact propext ⟨fun h => h.elim (fun ⟨a,b⟩ => Or.inr ⟨b,a⟩) (fun ⟨a,b⟩ => Or.inl ⟨b,a⟩),
                 fun h => h.elim (fun ⟨a,b⟩ => Or.inr ⟨b,a⟩) (fun ⟨a,b⟩ => Or.inl ⟨b,a⟩)⟩

theorem starAdj_diag (i : Fin 5) : starAdj i i = 0 := by
  simp only [starAdj]; rw [if_neg]; push_neg; exact ⟨fun h => h, fun h => h⟩

theorem starAdj_01 (i j : Fin 5) : starAdj i j = 0 ∨ starAdj i j = 1 := by
  simp only [starAdj]; split_ifs <;> simp

/-- The star quiver K_{1,4} with all-sink orientation: arrows from leaves 1,2,3,4 to center 0. -/
def starQuiver : Quiver (Fin 5) where
  Hom i j := PLift (i.val ≠ 0 ∧ j.val = 0)

instance starQuiver_subsingleton (a b : Fin 5) :
    Subsingleton (@Quiver.Hom (Fin 5) starQuiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

theorem starOrientation_isOrientationOf :
    @Etingof.IsOrientationOf 5 starQuiver starAdj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    simp only [starAdj] at hij
    obtain ⟨hi_ne, hj_eq⟩ := hp
    rw [if_pos (Or.inr ⟨hi_ne, hj_eq⟩)] at hij
    exact hij rfl
  · -- Each edge has an arrow in one direction
    simp only [starAdj] at hij
    split_ifs at hij with h
    · rcases h with ⟨hi_eq, hj_ne⟩ | ⟨hi_ne, hj_eq⟩
      · right; exact ⟨⟨hj_ne, hi_eq⟩⟩
      · left; exact ⟨⟨hi_ne, hj_eq⟩⟩
    · simp at hij
  · -- No two-way arrows
    obtain ⟨⟨hi_ne, hj_eq⟩⟩ := hi
    obtain ⟨⟨hj_ne, _⟩⟩ := hj
    exact hj_ne hj_eq

/-! ## Section 8: Star representation construction

The star representation for K_{1,4} uses dimension vector (2(m+1), m+1, m+1, m+1, m+1).
- Center (vertex 0): (Fin (m+1) → ℂ) × (Fin (m+1) → ℂ) ≅ ℂ^{2(m+1)}
- Leaves (vertices 1-4): Fin (m+1) → ℂ ≅ ℂ^{m+1}

Maps (all from leaf to center, all-sink orientation):
- B₁(x) = (x, 0)       — first-component embedding
- B₂(x) = (0, x)       — second-component embedding
- B₃(x) = (x, x)       — diagonal embedding
- B₄(x) = (x, Nx)      — nilpotent-twisted embedding

Indecomposability proof:
1. B₁, B₂ force W(center) = W(leaf₁) × W(leaf₂) by dimension counting
2. B₃ forces W(leaf₁) = W(leaf₂) via intersection dimension analysis
3. B₄ forces N to preserve W(leaf₁), then nilpotent_invariant_compl_trivial applies
-/

-- Embedding maps for the star representation.
-- Each maps ℂ^{m+1} into ℂ^{2(m+1)} ≅ ℂ^{m+1} × ℂ^{m+1}.
-- Indices 0..m = first component, (m+1)..2m+1 = second.

/-- First-component embedding: x ↦ (x, 0). -/
noncomputable def starEmbed1 (m : ℕ) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) where
  toFun x i := if h : i.val < m + 1 then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Second-component embedding: x ↦ (0, x). -/
noncomputable def starEmbed2 (m : ℕ) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) where
  toFun x i := if h : m + 1 ≤ i.val then x ⟨i.val - (m + 1), by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Diagonal embedding: x ↦ (x, x). -/
noncomputable def starEmbedDiag (m : ℕ) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) :=
  starEmbed1 m + starEmbed2 m

/-- Nilpotent-twisted embedding: x ↦ (x, Nx) where N is the nilpotent shift. -/
noncomputable def starEmbedNilp (m : ℕ) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) :=
  starEmbed1 m + (starEmbed2 m).comp (nilpotentShiftLin m)

/-- Select the embedding map based on leaf index. -/
noncomputable def starEmbedding (m : ℕ) (leaf : Fin 5) :
    (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) :=
  match leaf with
  | ⟨1, _⟩ => starEmbed1 m
  | ⟨2, _⟩ => starEmbed2 m
  | ⟨3, _⟩ => starEmbedDiag m
  | ⟨4, _⟩ => starEmbedNilp m
  | _ => 0

-- Match-based map for the star representation, ensuring definitional reduction
-- for specific vertex pairs.
private noncomputable def starRepMap (m : ℕ) (a b : Fin 5) :
    (Fin (if a.val = 0 then 2 * (m + 1) else m + 1) → ℂ) →ₗ[ℂ]
    (Fin (if b.val = 0 then 2 * (m + 1) else m + 1) → ℂ) :=
  match a, b with
  | ⟨1, _⟩, ⟨0, _⟩ => starEmbed1 m
  | ⟨2, _⟩, ⟨0, _⟩ => starEmbed2 m
  | ⟨3, _⟩, ⟨0, _⟩ => starEmbedDiag m
  | ⟨4, _⟩, ⟨0, _⟩ => starEmbedNilp m
  | _, _ => 0

-- The star representation with dimension vector (2(m+1), m+1, m+1, m+1, m+1).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def starRep (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin 5) _ starQuiver := by
  letI := starQuiver
  exact {
    obj := fun v => Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => starRepMap m a b
  }

/-! ## Section 9: Indecomposability of star representations -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
set_option maxHeartbeats 1600000 in
theorem starRep_isIndecomposable (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 5)
      starQuiver (starRep m) := by
  letI := starQuiver
  constructor
  · -- Nontrivial at some vertex (leaf 1 has dim m+1 ≥ 1)
    refine ⟨⟨1, by omega⟩, ?_⟩
    change Nontrivial (Fin (if (1 : Fin 5).val = 0 then _ else m + 1) → ℂ)
    simp only [show (1 : Fin 5).val = 1 from rfl, one_ne_zero, ↓reduceIte]
    infer_instance
  · -- Indecomposability: any complement decomposition is trivial
    -- The proof uses dimension counting on the split center space
    -- and nilpotent_invariant_compl_trivial.
    intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Key disjointness: embed1(x) + embed2(y) = 0 → x = 0 ∧ y = 0
    have embed_sum_zero : ∀ x y : Fin (m + 1) → ℂ,
        starEmbed1 m x + starEmbed2 m y = 0 → x = 0 ∧ y = 0 := by
      intro x y h
      have heval : ∀ j : Fin (2 * (m + 1)),
          starEmbed1 m x j + starEmbed2 m y j = 0 :=
        fun j => by have := congr_fun h j; simpa using this
      constructor <;> ext ⟨i, hi⟩ <;> simp only [Pi.zero_apply]
      · have := heval ⟨i, by omega⟩
        simp only [starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk] at this
        split_ifs at this with h1
        · omega
        · simpa using this
      · have := heval ⟨m + 1 + i, by omega⟩
        simp only [starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk] at this
        split_ifs at this with h1 h2
        · omega
        · omega
        · simp only [zero_add] at this
          have key : (⟨m + 1 + i - (m + 1), by omega⟩ : Fin (m + 1)) = ⟨i, hi⟩ := by
            simp only [Fin.mk.injEq]; omega
          rwa [key] at this
        · omega
    -- Core decomposition: if embed1(x) + embed2(z) ∈ W(center) and both W, W'
    -- have subrepresentation invariance, then x ∈ W(leaf1) and z ∈ W(leaf2).
    have core (W W' : ∀ v, Submodule ℂ ((starRep m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x z : Fin (m + 1) → ℂ)
        (hmem : starEmbed1 m x + starEmbed2 m z ∈ W ⟨0, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ z ∈ W ⟨2, by omega⟩ := by
      -- Decompose x at leaf 1: x = a + b, a ∈ W(1), b ∈ W'(1)
      have htop1 := (hc ⟨1, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop1
      -- Decompose z at leaf 2: z = c + d, c ∈ W(2), d ∈ W'(2)
      have htop2 := (hc ⟨2, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
      obtain ⟨c, hc2, d, hd, hcd⟩ := Submodule.mem_sup.mp htop2
      -- embed1(a) ∈ W(0) and embed2(c) ∈ W(0) via invariance
      have ha0 : starEmbed1 m a ∈ W ⟨0, by omega⟩ :=
        hW (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) a ha
      have hc0 : starEmbed2 m c ∈ W ⟨0, by omega⟩ :=
        hW (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) c hc2
      -- embed1(b) ∈ W'(0) and embed2(d) ∈ W'(0)
      have hb0 : starEmbed1 m b ∈ W' ⟨0, by omega⟩ :=
        hW' (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) b hb
      have hd0 : starEmbed2 m d ∈ W' ⟨0, by omega⟩ :=
        hW' (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩ from ⟨⟨by decide, rfl⟩⟩) d hd
      -- The cross-terms sum to zero via complement at center
      have hsum : starEmbed1 m x + starEmbed2 m z =
          (starEmbed1 m a + starEmbed2 m c) + (starEmbed1 m b + starEmbed2 m d) := by
        rw [← hab, ← hcd]; simp [map_add]; abel
      rw [hsum] at hmem
      have hadd : starEmbed1 m a + starEmbed2 m c ∈ W ⟨0, by omega⟩ :=
        (W ⟨0, by omega⟩).add_mem ha0 hc0
      -- Deduce second summand is in W by subtracting first summand
      have hw'_in_W : starEmbed1 m b + starEmbed2 m d ∈ W ⟨0, by omega⟩ := by
        -- hmem : ac + bd ∈ W,  hadd : ac ∈ W,  so bd = (ac + bd) - ac ∈ W
        have hsmul := (W ⟨0, by omega⟩).smul_mem (-1 : ℂ) hadd
        have hadd2 := (W ⟨0, by omega⟩).add_mem hmem hsmul
        have key : starEmbed1 m a + starEmbed2 m c + (starEmbed1 m b + starEmbed2 m d) +
            (-1 : ℂ) • (starEmbed1 m a + starEmbed2 m c) = starEmbed1 m b + starEmbed2 m d := by
          ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rwa [key] at hadd2
      have hzero : starEmbed1 m b + starEmbed2 m d = 0 := by
        have := Submodule.mem_inf.mpr ⟨hw'_in_W,
          (W' ⟨0, by omega⟩).add_mem hb0 hd0⟩
        rwa [(hc ⟨0, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
      obtain ⟨hb0', hd0'⟩ := embed_sum_zero b d hzero
      exact ⟨hab ▸ by rw [hb0', add_zero]; exact ha,
             hcd ▸ by rw [hd0', add_zero]; exact hc2⟩
    -- Extract leaf containments for W₁ and W₂
    -- Leaf 3 (diagonal embedding): x ∈ W(3) → x ∈ W(1) ∧ x ∈ W(2)
    -- Leaf 4 (nilpotent embedding): x ∈ W(4) → x ∈ W(1) ∧ Nx ∈ W(2)
    have leaf3_sub (W W' : ∀ v, Submodule ℂ ((starRep m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W ⟨3, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨3, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      -- mapLinear for leaf 3 is starEmbedDiag = embed1 + embed2
      change starEmbedDiag m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedDiag, LinearMap.add_apply] at hmem
      exact core W W' hW hW' hc x x hmem
    have leaf4_sub (W W' : ∀ v, Submodule ℂ ((starRep m).obj v))
        (hW : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W a, (starRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W ⟨4, by omega⟩) :
        x ∈ W ⟨1, by omega⟩ ∧ nilpotentShiftLin m x ∈ W ⟨2, by omega⟩ := by
      have hmem := hW (show @Quiver.Hom _ starQuiver ⟨4, by omega⟩ ⟨0, by omega⟩
        from ⟨⟨by decide, rfl⟩⟩) x hx
      change starEmbedNilp m x ∈ W ⟨0, by omega⟩ at hmem
      rw [starEmbedNilp, LinearMap.add_apply, LinearMap.comp_apply] at hmem
      exact core W W' hW hW' hc x (nilpotentShiftLin m x) hmem
    -- Helper: if A ≤ B, A' ≤ B', IsCompl A A', IsCompl B B', then A = B
    have compl_eq_of_le (A B A' B' : Submodule ℂ (Fin (m + 1) → ℂ))
        (hAB : A ≤ B) (hA'B' : A' ≤ B')
        (hcA : IsCompl A A') (hcB : IsCompl B B') : A = B := by
      apply le_antisymm hAB; intro x hx
      have hx_top := hcA.sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx_top
      have ha'_B : a' ∈ B := by
        have h := B.sub_mem hx (hAB ha); rwa [show a + a' - a = a' from by abel] at h
      have : a' ∈ B ⊓ B' := Submodule.mem_inf.mpr ⟨ha'_B, hA'B' ha'⟩
      rw [hcB.inf_eq_bot, Submodule.mem_bot] at this; rwa [this, add_zero]
    -- W₁(3) = W₁(1), W₁(3) = W₁(2), W₁(4) = W₁(1)
    have heq31 : W₁ ⟨3, by omega⟩ = W₁ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).1)
      (hcompl ⟨3, by omega⟩) (hcompl ⟨1, by omega⟩)
    have heq32 : W₁ ⟨3, by omega⟩ = W₁ ⟨2, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).2)
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).2)
      (hcompl ⟨3, by omega⟩) (hcompl ⟨2, by omega⟩)
    have heq41 : W₁ ⟨4, by omega⟩ = W₁ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      (fun x hx => (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx).1)
      (hcompl ⟨4, by omega⟩) (hcompl ⟨1, by omega⟩)
    -- N preserves W₁(1): from B₄, x ∈ W₁(4) = W₁(1) → Nx ∈ W₁(2) = W₁(1)
    have h12 : W₁ ⟨1, by omega⟩ = W₁ ⟨2, by omega⟩ := heq31.symm.trans heq32
    have hN₁ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₁ ⟨1, by omega⟩ → nilpotentShiftLin m x ∈ W₁ ⟨1, by omega⟩ := by
      intro x hx
      have hx4 : x ∈ W₁ ⟨4, by omega⟩ := by rw [heq41]; exact hx
      have h2 := (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx4).2
      exact h12 ▸ h2
    -- Similarly: W₂(3) = W₂(1), etc., and N preserves W₂(1)
    have heq31' : W₂ ⟨3, by omega⟩ = W₂ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).1)
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      ((hcompl ⟨3, by omega⟩).symm) ((hcompl ⟨1, by omega⟩).symm)
    have heq32' : W₂ ⟨3, by omega⟩ = W₂ ⟨2, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf3_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).2)
      (fun x hx => (leaf3_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).2)
      ((hcompl ⟨3, by omega⟩).symm) ((hcompl ⟨2, by omega⟩).symm)
    have heq41' : W₂ ⟨4, by omega⟩ = W₂ ⟨1, by omega⟩ := compl_eq_of_le _ _ _ _
      (fun x hx => (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm) x hx).1)
      (fun x hx => (leaf4_sub W₁ W₂ hW₁_inv hW₂_inv hcompl x hx).1)
      ((hcompl ⟨4, by omega⟩).symm) ((hcompl ⟨1, by omega⟩).symm)
    have h12' : W₂ ⟨1, by omega⟩ = W₂ ⟨2, by omega⟩ := heq31'.symm.trans heq32'
    have hN₂ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₂ ⟨1, by omega⟩ → nilpotentShiftLin m x ∈ W₂ ⟨1, by omega⟩ := by
      intro x hx
      have hx4 : x ∈ W₂ ⟨4, by omega⟩ := by rw [heq41']; exact hx
      have h2 := (leaf4_sub W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm)
        x hx4).2
      exact h12' ▸ h2
    -- Apply nilpotent_invariant_compl_trivial at leaf 1
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩) hN₁ hN₂ (hcompl ⟨1, by omega⟩)
    -- Propagate: if W(1) = ⊥ then all W(v) = ⊥
    -- Center argument: W'(1) = ⊤ → embed(any x) ∈ W'(center) → W'(center) = ⊤ → W(center) = ⊥
    have center_decomp : ∀ w : Fin (2 * (m + 1)) → ℂ,
        w = starEmbed1 m (fun i => w ⟨i.val, by omega⟩) +
            starEmbed2 m (fun i => w ⟨m + 1 + i.val, by omega⟩) := by
      intro w; ext ⟨j, hj⟩
      simp only [Pi.add_apply, starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hjlt : j < m + 1
      · simp only [dif_pos hjlt, show ¬(m + 1 ≤ j) from by omega, dite_false, add_zero]
      · simp only [dif_neg hjlt, show m + 1 ≤ j from by omega, dite_true, zero_add]
        congr 1; ext; simp; omega
    suffices propagate : ∀ (W W' : ∀ v, Submodule ℂ ((starRep m).obj v)),
        (∀ {a b : Fin 5} (e : @Quiver.Hom _ starQuiver a b),
          ∀ x ∈ W' a, (starRep m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W ⟨1, by omega⟩ = W ⟨2, by omega⟩ →
        W ⟨3, by omega⟩ = W ⟨1, by omega⟩ →
        W ⟨4, by omega⟩ = W ⟨1, by omega⟩ →
        W ⟨1, by omega⟩ = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₂_inv hcompl (heq31.symm.trans heq32) heq31 heq41 h
      · right; exact propagate W₂ W₁ hW₁_inv (fun v => (hcompl v).symm)
          (heq31'.symm.trans heq32') heq31' heq41' h
    intro W W' hW'_inv hc h12 h31 h41 hbot v
    fin_cases v
    · -- Center
      show W ⟨0, by omega⟩ = ⊥
      have hW'1_top : W' ⟨1, by omega⟩ = ⊤ := by
        have := (hc ⟨1, by omega⟩).sup_eq_top; rwa [hbot, bot_sup_eq] at this
      have hW'2_top : W' ⟨2, by omega⟩ = ⊤ := by
        have := (hc ⟨2, by omega⟩).sup_eq_top; rwa [← h12, hbot, bot_sup_eq] at this
      -- Any element from leaf 1 or 2 maps into W'(center)
      have h_emb1 : ∀ (x : Fin (m + 1) → ℂ), starEmbed1 m x ∈ W' ⟨0, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ starQuiver ⟨1, by omega⟩ ⟨0, by omega⟩
          from ⟨⟨by decide, rfl⟩⟩) x (hW'1_top ▸ Submodule.mem_top)
      have h_emb2 : ∀ (x : Fin (m + 1) → ℂ), starEmbed2 m x ∈ W' ⟨0, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ starQuiver ⟨2, by omega⟩ ⟨0, by omega⟩
          from ⟨⟨by decide, rfl⟩⟩) x (hW'2_top ▸ Submodule.mem_top)
      -- Every w in center decomposes as embed1 + embed2, both in W'
      rw [eq_bot_iff]; intro (w : Fin (2 * (m + 1)) → ℂ) hw
      have hw' : w ∈ W' ⟨0, by omega⟩ :=
        center_decomp w ▸ (W' ⟨0, by omega⟩).add_mem (h_emb1 _) (h_emb2 _)
      have := Submodule.mem_inf.mpr ⟨hw, hw'⟩
      rwa [(hc ⟨0, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
    · -- v = 1
      exact hbot
    · -- v = 2
      show W ⟨2, by omega⟩ = ⊥; rw [← h12]; exact hbot
    · -- v = 3
      show W ⟨3, by omega⟩ = ⊥; rw [h31]; exact hbot
    · -- v = 4
      show W ⟨4, by omega⟩ = ⊥; rw [h41]; exact hbot


/-! ## Section 10: Dimension vectors and infinite type for star -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem starRep_dimVec (m : ℕ) (v : Fin 5) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin 5) _
      starQuiver (starRep m) v ≃ₗ[ℂ]
      (Fin (if v.val = 0 then 2 * (m + 1) else m + 1) → ℂ)) :=
  ⟨LinearEquiv.refl ℂ _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The star graph K_{1,4} has infinite representation type:
    for each m, there is an indecomposable rep with distinct dim vector. -/
theorem star_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 5 starAdj := by
  intro hft
  letI := starQuiver
  have hfin := @hft ℂ _ inferInstance starQuiver
    (fun a b => starQuiver_subsingleton a b)
    starOrientation_isOrientationOf
  -- The dimension vector for starRep m maps m to
  -- (2(m+1), m+1, m+1, m+1, m+1) which is injective in m
  have hmem : ∀ m : ℕ,
      (fun v : Fin 5 => if v.val = 0 then 2 * (m + 1) else m + 1) ∈
      {d : Fin 5 → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin 5),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨starRep m, starRep_isIndecomposable m, starRep_dimVec m⟩
  have hinj : Function.Injective
      (fun m : ℕ => fun v : Fin 5 =>
        if v.val = 0 then 2 * (m + 1) else m + 1) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    simp only [ite_true] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 11: Subgraph infinite type transfer

Given an embedding φ : Fin m ↪ Fin n and an adjacency matrix adj on Fin n whose
restriction to the image of φ equals adj_sub, we show that infinite representation
type transfers from the subgraph to the full graph.

The proof strategy:
1. Given ¬ IsFiniteTypeQuiver m adj_sub, assume IsFiniteTypeQuiver n adj for contradiction.
2. For any orientation Q_sub of adj_sub, extend it to an orientation Q of adj.
3. Map each Q_sub-indecomposable to a Q-indecomposable via extension by zero.
4. The dim vector injection gives a contradiction with finiteness. -/

section SubgraphTransfer

variable {m n : ℕ}

/-- Predicate for arrows in the extended orientation: either the arrow comes from
    the subgraph orientation, or (for edges not fully in the subgraph) we orient
    by vertex index. -/
def extArrowProp (φ : Fin m ↪ Fin n) (adj : Matrix (Fin n) (Fin n) ℤ)
    (Q_sub : Quiver (Fin m)) (a b : Fin n) : Prop :=
  (∃ i j, φ i = a ∧ φ j = b ∧ Nonempty (@Quiver.Hom _ Q_sub i j)) ∨
  ((a ∉ Set.range φ ∨ b ∉ Set.range φ) ∧ a.val < b.val ∧ adj a b = 1)

/-- Extend a subgraph orientation to the full graph. Within the subgraph, use
    the given orientation. For other edges, orient by vertex index order. -/
def extendOrientation (φ : Fin m ↪ Fin n) (adj : Matrix (Fin n) (Fin n) ℤ)
    (Q_sub : Quiver (Fin m)) : Quiver (Fin n) where
  Hom a b := PLift (extArrowProp φ adj Q_sub a b)

instance extendOrientation_subsingleton (φ : Fin m ↪ Fin n) (adj : Matrix (Fin n) (Fin n) ℤ)
    (Q_sub : Quiver (Fin m)) (a b : Fin n) :
    Subsingleton (@Quiver.Hom _ (extendOrientation φ adj Q_sub) a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private lemma adj_symm_of_isSymm {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hadj_symm : adj.IsSymm) (a b : Fin n) : adj a b = adj b a := by
  have h1 : adj.transpose a b = adj a b := congr_fun (congr_fun hadj_symm a) b
  rw [Matrix.transpose_apply] at h1; exact h1.symm

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem extendOrientation_isOrientationOf (φ : Fin m ↪ Fin n)
    (adj : Matrix (Fin n) (Fin n) ℤ) (adj_sub : Matrix (Fin m) (Fin m) ℤ)
    (hadj_symm : adj.IsSymm)
    (hadj_noloop : ∀ v, adj v v ≠ 1)
    (hembed : ∀ i j, adj_sub i j = adj (φ i) (φ j))
    (Q_sub : Quiver (Fin m))
    (hori : @Etingof.IsOrientationOf m Q_sub adj_sub) :
    @Etingof.IsOrientationOf n (extendOrientation φ adj Q_sub) adj := by
  obtain ⟨hQ_no, hQ_edge, hQ_unique⟩ := hori
  have adj_sym := adj_symm_of_isSymm hadj_symm
  -- Helper: if Q_sub.Hom i j is nonempty then adj (φ i) (φ j) = 1
  have arrow_adj : ∀ i j, Nonempty (@Quiver.Hom _ Q_sub i j) → adj (φ i) (φ j) = 1 := by
    intro i j ⟨e⟩
    by_contra h
    exact (hQ_no i j (by rwa [hembed])).elim e
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b ⟨ha⟩ ⟨hb⟩ => ?_⟩
  · -- Non-edge: no arrow
    constructor; intro ⟨harrow⟩
    rcases harrow with ⟨i, j, rfl, rfl, he⟩ | ⟨_, _, hadj_eq⟩
    · exact hab (arrow_adj i j he)
    · exact hab hadj_eq
  · -- Each edge has an arrow in one direction
    have hab_ne : a ≠ b := fun h => by subst h; exact hadj_noloop a hab
    by_cases ha : a ∈ Set.range φ <;> by_cases hb : b ∈ Set.range φ
    · obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := hb
      rcases hQ_edge i j (by rwa [hembed]) with he | he
      · left; exact ⟨⟨Or.inl ⟨i, j, rfl, rfl, he⟩⟩⟩
      · right; exact ⟨⟨Or.inl ⟨j, i, rfl, rfl, he⟩⟩⟩
    all_goals {
      have hne : a.val ≠ b.val := fun h => hab_ne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · left; exact ⟨⟨Or.inr ⟨by tauto, hlt, hab⟩⟩⟩
      · right; exact ⟨⟨Or.inr ⟨by tauto, hgt, adj_sym a b ▸ hab⟩⟩⟩ }
  · -- No two-way arrows
    rcases ha with ⟨i, j, hi, hj, ⟨eij⟩⟩ | ⟨hrange_ab, hlt_ab, _⟩ <;>
    rcases hb with ⟨i', j', hi', hj', ⟨eji⟩⟩ | ⟨hrange_ba, hlt_ba, _⟩
    · -- Both subgraph: Q_sub arrows both ways
      have h1 : i' = j := φ.injective (hi'.trans hj.symm)
      have h2 : j' = i := φ.injective (hj'.trans hi.symm)
      rw [h1, h2] at eji
      exact hQ_unique i j ⟨eij⟩ ⟨eji⟩
    · -- a→b subgraph, b→a external: both a,b in range (from subgraph arrow), contradicts external
      rcases hrange_ba with hb_nr | ha_nr
      · exact hb_nr ⟨j, hj⟩
      · exact ha_nr ⟨i, hi⟩
    · -- a→b external, b→a subgraph: same contradiction
      rcases hrange_ab with ha_nr | hb_nr
      · exact ha_nr ⟨j', hj'⟩
      · exact hb_nr ⟨i', hi'⟩
    · -- Both external: a < b and b < a
      omega

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- If a principal submatrix of adj has infinite representation type,
    then adj itself has infinite representation type. This is proved by
    extending each subgraph orientation and representation to the full graph. -/
theorem subgraph_infinite_type_transfer (φ : Fin m ↪ Fin n)
    (adj : Matrix (Fin n) (Fin n) ℤ) (adj_sub : Matrix (Fin m) (Fin m) ℤ)
    (hadj_symm : adj.IsSymm)
    (hadj_noloop : ∀ v, adj v v ≠ 1)
    (hembed : ∀ i j, adj_sub i j = adj (φ i) (φ j))
    (h_inf : ¬ Etingof.IsFiniteTypeQuiver m adj_sub) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  intro hft
  apply h_inf
  -- Show IsFiniteTypeQuiver m adj_sub by mapping dim vectors into the finite n-graph set
  intro k _ _ Q_sub hss hori_sub
  -- Extend orientation to full graph
  letI Q_ext := extendOrientation φ adj Q_sub
  have hori_ext := extendOrientation_isOrientationOf φ adj adj_sub hadj_symm hadj_noloop
    hembed Q_sub hori_sub
  have hfin := @hft k _ _ Q_ext (fun a b => extendOrientation_subsingleton φ adj Q_sub a b) hori_ext
  -- Define the dim vector extension: d ↦ d' where d'(φ i) = d(i), d'(v) = 0 if v ∉ range φ
  classical
  let extDV : (Fin m → ℕ) → (Fin n → ℕ) := fun d v =>
    if h : ∃ i, φ i = v then d h.choose else 0
  -- extDV is injective (φ is injective → choose recovers the preimage)
  have h_choose : ∀ i, (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose = i :=
    fun i => φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
  have extDV_apply : ∀ d i, extDV d (φ i) = d i := by
    intro d i; change (if h : ∃ j, φ j = φ i then d h.choose else 0) = d i
    rw [dif_pos ⟨i, rfl⟩, h_choose]
  have hinj : Function.Injective extDV := by
    intro d₁ d₂ h; ext i
    have := congr_fun h (φ i)
    rwa [extDV_apply, extDV_apply] at this
  -- extDV maps the Q_sub dim vector set into the Q_ext dim vector set
  have hmem : ∀ d,
      d ∈ {d : Fin m → ℕ |
        ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} k (Fin m),
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))} →
      extDV d ∈ {d : Fin n → ℕ |
        ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} k (Fin n),
          V.IsIndecomposable ∧
          ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))} := by
    intro d ⟨V, hV_ind, hV_dim⟩
    -- Extract chosen linear equivs for each vertex of V
    let equiv_at : ∀ i : Fin m, V.obj i ≃ₗ[k] (Fin (d i) → k) := fun i => (hV_dim i).some
    -- Helper: cast linear equiv between Fin spaces of equal size
    let finCastEquiv (a b : ℕ) (h : a = b) : (Fin a → k) ≃ₗ[k] (Fin b → k) :=
      LinearEquiv.funCongrLeft k k (Fin.castOrderIso h.symm).toEquiv
    -- Construct the extended representation V' with obj v = Fin (extDV d v) → k
    -- Maps at subgraph edges use V's maps transferred through equivs; external use 0
    let V'mapLinear : ∀ {a b : Fin n},
        @Quiver.Hom _ Q_ext a b → (Fin (extDV d a) → k) →ₗ[k] (Fin (extDV d b) → k) :=
      fun {a b} _ =>
        if h : ∃ i j, φ i = a ∧ φ j = b ∧ Nonempty (@Quiver.Hom _ Q_sub i j) then
          have hi : φ h.choose = a := h.choose_spec.choose_spec.1
          have hj : φ h.choose_spec.choose = b := h.choose_spec.choose_spec.2.1
          have e_sub := h.choose_spec.choose_spec.2.2.some
          let j := h.choose_spec.choose
          let i := h.choose
          (finCastEquiv _ _ ((extDV_apply d j).symm.trans (congrArg (extDV d) hj))).toLinearMap.comp
            ((equiv_at j).toLinearMap.comp
              ((@Etingof.QuiverRepresentation.mapLinear k (Fin m) _
                Q_sub V _ _ e_sub).comp
                ((equiv_at i).symm.toLinearMap.comp
                  (finCastEquiv _ _
                    ((extDV_apply d i).symm.trans
                      (congrArg (extDV d) hi))).symm.toLinearMap)))
        else 0
    refine ⟨⟨fun v => Fin (extDV d v) → k, V'mapLinear⟩, ?_, fun v => ⟨LinearEquiv.refl k _⟩⟩
    -- Indecomposability of V': any complement decomposition restricts to one of V
    -- Define the composite equiv V.obj i ≃ Fin (extDV d (φ i)) → k
    let e_at (i : Fin m) : V.obj i ≃ₗ[k] (Fin (extDV d (φ i)) → k) :=
      (equiv_at i).trans (finCastEquiv (d i) (extDV d (φ i)) (extDV_apply d i).symm)
    constructor
    · -- V' is nonzero: V has a nontrivial vertex
      obtain ⟨⟨v₀, hv₀⟩, _⟩ := hV_ind
      exact ⟨φ v₀, (e_at v₀).toEquiv.symm.nontrivial⟩
    · -- Indecomposability
      intro W₁ W₂ hW₁_inv hW₂_inv hcompl
      -- For v ∉ range φ, extDV d v = 0, so both submodules are ⊥
      have h_ext_zero : ∀ v, v ∉ Set.range φ → extDV d v = 0 := by
        intro v hv; simp only [extDV, dif_neg (show ¬∃ i, φ i = v from fun ⟨i, hi⟩ => hv ⟨i, hi⟩)]
      have h_bot_of_not_range : ∀ v, v ∉ Set.range φ →
          ∀ (S : Submodule k (Fin (extDV d v) → k)), S = ⊥ := by
        intro v hv S
        have hze := h_ext_zero v hv
        have : Subsingleton (Fin (extDV d v) → k) := by
          rw [hze]; infer_instance
        rw [eq_bot_iff]; intro x _; rw [Submodule.mem_bot]
        exact Subsingleton.elim _ _
      -- Pull back W₁, W₂ to V via e_at
      let U₁ (i : Fin m) : Submodule k (V.obj i) := (W₁ (φ i)).comap (e_at i).toLinearMap
      let U₂ (i : Fin m) : Submodule k (V.obj i) := (W₂ (φ i)).comap (e_at i).toLinearMap
      -- Complements transfer through linear equiv
      have hU_compl : ∀ i, IsCompl (U₁ i) (U₂ i) := by
        intro i
        have hc := hcompl (φ i)
        constructor
        · -- Disjoint
          rw [disjoint_iff]
          rw [eq_bot_iff]; intro x hx
          rw [Submodule.mem_inf] at hx
          have h1 : (e_at i) x ∈ W₁ (φ i) := hx.1
          have h2 : (e_at i) x ∈ W₂ (φ i) := hx.2
          have : (e_at i) x ∈ W₁ (φ i) ⊓ W₂ (φ i) := Submodule.mem_inf.mpr ⟨h1, h2⟩
          rw [hc.1.eq_bot] at this
          rw [Submodule.mem_bot]
          have h_ez := (Submodule.mem_bot k).mp this
          exact (e_at i).injective (h_ez.trans (map_zero _).symm)
        · -- Codisjoint
          rw [codisjoint_iff]
          rw [eq_top_iff]; intro x _
          have : (e_at i) x ∈ W₁ (φ i) ⊔ W₂ (φ i) := hc.2.eq_top ▸ Submodule.mem_top
          obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp this
          rw [Submodule.mem_sup]
          refine ⟨(e_at i).symm y₁, ?_, (e_at i).symm y₂, ?_, ?_⟩
          · change (e_at i) ((e_at i).symm y₁) ∈ W₁ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy₁
          · change (e_at i) ((e_at i).symm y₂) ∈ W₂ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy₂
          · apply (e_at i).injective
            rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
            exact hsum
      -- Key: V'mapLinear for subgraph edges = e_at j ∘ V.mapLinear ∘ (e_at i)⁻¹
      -- Construct ext edge from subgraph edge
      have mk_ext_edge : ∀ (i j : Fin m), @Quiver.Hom _ Q_sub i j →
          @Quiver.Hom _ Q_ext (φ i) (φ j) :=
        fun i j e => PLift.up (Or.inl ⟨i, j, rfl, rfl, ⟨e⟩⟩)
      -- Helper: for fresh variables i', j' that can be subst'd
      have V'map_aux : ∀ (i j : Fin m) (e_sub_ij : @Quiver.Hom _ Q_sub i j)
          (i' j' : Fin m) (hi : i' = i) (hj : j' = j)
          (e' : @Quiver.Hom _ Q_sub i' j')
          (x : Fin (extDV d (φ i)) → k),
          (finCastEquiv _ _
            ((extDV_apply d j').symm.trans
              (congrArg (extDV d) (show φ j' = φ j by rw [hj])))).toLinearMap.comp
            ((equiv_at j').toLinearMap.comp
              ((@Etingof.QuiverRepresentation.mapLinear k (Fin m) _ Q_sub V _ _ e').comp
                ((equiv_at i').symm.toLinearMap.comp
                  (finCastEquiv _ _ ((extDV_apply d i').symm.trans
                    (congrArg (extDV d) (show φ i' = φ i by rw [hi])))).symm.toLinearMap))) x =
          (e_at j) (V.mapLinear e_sub_ij ((e_at i).symm x)) := by
        intro i j e_sub_ij i' j' hi hj e' x
        subst hi; subst hj
        have : e' = e_sub_ij := Subsingleton.elim _ _
        subst this
        rfl
      have V'map_compat : ∀ (i j : Fin m) (e_sub_ij : @Quiver.Hom _ Q_sub i j)
          (x : Fin (extDV d (φ i)) → k),
          V'mapLinear (mk_ext_edge i j e_sub_ij) x =
          (e_at j) (V.mapLinear e_sub_ij ((e_at i).symm x)) := by
        intro i j e_sub_ij x
        change V'mapLinear (PLift.up (Or.inl ⟨i, j, rfl, rfl, ⟨e_sub_ij⟩⟩)) x = _
        simp only [V'mapLinear]
        have h_ex : ∃ i' j', φ i' = φ i ∧ φ j' = φ j ∧
            Nonempty (@Quiver.Hom _ Q_sub i' j') := ⟨i, j, rfl, rfl, ⟨e_sub_ij⟩⟩
        rw [dif_pos h_ex]
        exact V'map_aux i j e_sub_ij
          h_ex.choose h_ex.choose_spec.choose
          (φ.injective h_ex.choose_spec.choose_spec.1)
          (φ.injective h_ex.choose_spec.choose_spec.2.1)
          h_ex.choose_spec.choose_spec.2.2.some x
      -- U₁ is V-invariant
      have hU₁_inv : ∀ {a b : Fin m} (e : @Quiver.Hom _ Q_sub a b),
          ∀ x ∈ U₁ a, V.mapLinear e x ∈ U₁ b := by
        intro a b e_ab x hx
        -- hx : (e_at a) x ∈ W₁ (φ a)
        -- Need: (e_at b) (V.mapLinear e_ab x) ∈ W₁ (φ b)
        change (e_at b) (V.mapLinear e_ab x) ∈ W₁ (φ b)
        have h_compat := V'map_compat a b e_ab ((e_at a) x)
        rw [LinearEquiv.symm_apply_apply] at h_compat
        rw [← h_compat]
        exact hW₁_inv (mk_ext_edge a b e_ab) _ hx
      -- U₂ is V-invariant
      have hU₂_inv : ∀ {a b : Fin m} (e : @Quiver.Hom _ Q_sub a b),
          ∀ x ∈ U₂ a, V.mapLinear e x ∈ U₂ b := by
        intro a b e_ab x hx
        change (e_at b) (V.mapLinear e_ab x) ∈ W₂ (φ b)
        have h_compat := V'map_compat a b e_ab ((e_at a) x)
        rw [LinearEquiv.symm_apply_apply] at h_compat
        rw [← h_compat]
        exact hW₂_inv (mk_ext_edge a b e_ab) _ hx
      -- Apply V's indecomposability
      rcases hV_ind.2 U₁ U₂ hU₁_inv hU₂_inv hU_compl with hU₁_bot | hU₂_bot
      · -- U₁ = ⊥ everywhere → W₁ = ⊥ everywhere
        left; intro v
        by_cases hv : v ∈ Set.range φ
        · obtain ⟨i, rfl⟩ := hv
          rw [eq_bot_iff]; intro y hy
          have hU := hU₁_bot i
          have : (e_at i).symm y ∈ U₁ i := by
            change (e_at i) ((e_at i).symm y) ∈ W₁ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy
          rw [hU, Submodule.mem_bot] at this
          rw [Submodule.mem_bot]
          calc y = (e_at i) ((e_at i).symm y) := (LinearEquiv.apply_symm_apply _ _).symm
            _ = (e_at i) 0 := by rw [this]
            _ = 0 := map_zero _
        · exact h_bot_of_not_range v hv (W₁ v)
      · -- U₂ = ⊥ everywhere → W₂ = ⊥ everywhere
        right; intro v
        by_cases hv : v ∈ Set.range φ
        · obtain ⟨i, rfl⟩ := hv
          rw [eq_bot_iff]; intro y hy
          have hU := hU₂_bot i
          have : (e_at i).symm y ∈ U₂ i := by
            change (e_at i) ((e_at i).symm y) ∈ W₂ (φ i)
            rw [LinearEquiv.apply_symm_apply]; exact hy
          rw [hU, Submodule.mem_bot] at this
          rw [Submodule.mem_bot]
          calc y = (e_at i) ((e_at i).symm y) := (LinearEquiv.apply_symm_apply _ _).symm
            _ = (e_at i) 0 := by rw [this]
            _ = 0 := map_zero _
        · exact h_bot_of_not_range v hv (W₂ v)
  -- The Q_sub dim vector set maps injectively into the finite Q_ext dim vector set
  exact (hfin.subset (Set.image_subset_iff.mpr hmem)).of_finite_image hinj.injOn

end SubgraphTransfer

/-! ## Section 12: Star subgraph implies infinite type -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- If a graph has a vertex with 4 pairwise non-adjacent neighbors (a K_{1,4} subgraph),
    then it has infinite representation type. -/
theorem star_subgraph_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hadj_symm : adj.IsSymm)
    (hadj_diag : ∀ v, adj v v = 0)
    (center : Fin n) (leaves : Fin 4 ↪ Fin n)
    (hleaves_ne : ∀ i, leaves i ≠ center)
    (hadj_edge : ∀ i, adj center (leaves i) = 1)
    (hadj_indep : ∀ i j, adj (leaves i) (leaves j) = 0) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  -- Construct embedding φ : Fin 5 ↪ Fin n mapping star K_{1,4} into the graph
  -- φ maps: 0 ↦ center, k+1 ↦ leaves k
  have h_leaf (i : Fin 5) (h : i.val ≠ 0) : i.val - 1 < 4 := by omega
  let φ_fun : Fin 5 → Fin n := fun i =>
    if h : i.val = 0 then center
    else leaves ⟨i.val - 1, h_leaf i h⟩
  have hφ_inj : Function.Injective φ_fun := by
    intro a b hab
    simp only [φ_fun] at hab
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
    · exact Fin.ext (by omega)
    · exfalso; rw [dif_pos ha0, dif_neg hb0] at hab; exact hleaves_ne _ hab.symm
    · exfalso; rw [dif_neg ha0, dif_pos hb0] at hab; exact hleaves_ne _ hab
    · rw [dif_neg ha0, dif_neg hb0] at hab
      have h := congr_arg Fin.val (leaves.injective hab)
      simp at h
      exact Fin.ext (by omega)
  let φ : Fin 5 ↪ Fin n := ⟨φ_fun, hφ_inj⟩
  -- Verify adjacency embedding condition: starAdj i j = adj (φ i) (φ j)
  have hembed : ∀ i j, starAdj i j = adj (φ i) (φ j) := by
    intro i j
    change (if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then (1 : ℤ) else 0) =
      adj (φ_fun i) (φ_fun j)
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · -- center-center
      rw [if_neg (by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> contradiction)]
      simp only [φ_fun, dif_pos hi0, dif_pos hj0]
      exact (hadj_diag center).symm
    · -- center-leaf
      rw [if_pos (Or.inl ⟨hi0, hj0⟩)]
      simp only [φ_fun, dif_pos hi0, dif_neg hj0]
      exact (hadj_edge ⟨j.val - 1, h_leaf j hj0⟩).symm
    · -- leaf-center
      rw [if_pos (Or.inr ⟨hi0, hj0⟩)]
      simp only [φ_fun, dif_neg hi0, dif_pos hj0]
      have := hadj_edge ⟨i.val - 1, h_leaf i hi0⟩
      rw [adj_symm_of_isSymm hadj_symm] at this; exact this.symm
    · -- leaf-leaf
      rw [if_neg (by rintro (⟨h, -⟩ | ⟨-, h⟩) <;> contradiction)]
      simp only [φ_fun, dif_neg hi0, dif_neg hj0]
      exact (hadj_indep ⟨i.val - 1, h_leaf i hi0⟩ ⟨j.val - 1, h_leaf j hj0⟩).symm
  exact subgraph_infinite_type_transfer φ adj starAdj hadj_symm
    (fun v h => by linarith [hadj_diag v]) hembed star_not_finite_type

/-! ## Section 13: Trees with degree ≥ 4 have infinite type -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- A tree (connected simple graph with no triangles) having a vertex of degree ≥ 4
    has infinite representation type. The triangle-free condition ensures neighbors
    of the high-degree vertex form an independent set, giving a K_{1,4} subgraph. -/
theorem tree_degree_ge_4_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hadj_symm : adj.IsSymm)
    (hadj_diag : ∀ v, adj v v = 0)
    -- Triangle-free: no two neighbors of the same vertex are adjacent
    (htri_free : ∀ v w₁ w₂, adj v w₁ = 1 → adj v w₂ = 1 → w₁ ≠ w₂ → adj w₁ w₂ = 0)
    (v : Fin n) (hv : 4 ≤ vertexDegree adj v) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  -- Extract 4 distinct neighbors from the neighbor set of v
  set S := Finset.univ.filter (fun w => adj v w = 1) with hS_def
  -- Get a subset of size 4
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hv
  -- Get an equivalence Fin 4 ≃ T
  have hT_fin : Fintype T := inferInstance
  have hT_card : Fintype.card T = 4 := by
    rwa [Fintype.card_coe]
  let e := (Fintype.equivFinOfCardEq hT_card).symm
  -- Define leaves as the composition
  let leaves_fun : Fin 4 → Fin n := fun i => (e i).val
  have hleaves_inj : Function.Injective leaves_fun := by
    intro a b hab
    exact e.injective (Subtype.val_injective hab)
  let leaves : Fin 4 ↪ Fin n := ⟨leaves_fun, hleaves_inj⟩
  -- Each leaf is a neighbor of v
  have hleaves_adj : ∀ i, adj v (leaves i) = 1 := by
    intro i
    have hmem : (e i).val ∈ S := hTS (e i).property
    exact (Finset.mem_filter.mp hmem).2
  -- Each leaf is distinct from v (since adj v v = 0 ≠ 1)
  have hleaves_ne : ∀ i, leaves i ≠ v := by
    intro i habs
    have := hleaves_adj i
    rw [habs, hadj_diag] at this
    exact one_ne_zero this.symm
  -- Leaves are pairwise non-adjacent (triangle-free)
  have hleaves_indep : ∀ i j, adj (leaves i) (leaves j) = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact hadj_diag (leaves i)
    · exact htri_free v (leaves i) (leaves j) (hleaves_adj i) (hleaves_adj j)
        (by intro h; exact hij (hleaves_inj h))
  exact star_subgraph_not_finite_type adj hadj_symm hadj_diag v leaves hleaves_ne
    hleaves_adj hleaves_indep

/-! ## Section 14: Extended Dynkin graph Ẽ_6 = T_{2,2,2}

The graph T_{2,2,2} has 7 vertices: a center vertex (0) with three arms of length 2.
- Arm 1: 0-1-2
- Arm 2: 0-3-4
- Arm 3: 0-5-6

The orientation sends all arrows toward the center: 2→1→0, 4→3→0, 6→5→0.
-/

/-- Adjacency matrix for Ẽ_6 = T_{2,2,2} (7 vertices, 3 arms of length 2). -/
def etilde6Adj : Matrix (Fin 7) (Fin 7) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 0, 3 | 3, 0 | 3, 4 | 4, 3
  | 0, 5 | 5, 0 | 5, 6 | 6, 5 => 1
  | _, _ => 0

theorem etilde6Adj_symm : etilde6Adj.IsSymm := by
  ext i j; simp only [etilde6Adj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem etilde6Adj_diag (i : Fin 7) : etilde6Adj i i = 0 := by
  fin_cases i <;> simp [etilde6Adj]

theorem etilde6Adj_01 (i j : Fin 7) : etilde6Adj i j = 0 ∨ etilde6Adj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [etilde6Adj]


/-! ## Section 15: Extended Dynkin graph Ẽ_8 = T_{2,3,5}

The graph T_{2,3,5} has 11 vertices: a center vertex (0) with arms of length 2, 3, and 5.
- Arm 1 (length 2): 0-1-2
- Arm 2 (length 3): 0-3-4-5
- Arm 3 (length 5): 0-6-7-8-9-10

The orientation sends all arrows toward the center.
-/

/-- Adjacency matrix for Ẽ_8 = T_{2,3,5} (11 vertices). -/
def etilde8Adj : Matrix (Fin 11) (Fin 11) ℤ := fun i j =>
  match i.val, j.val with
  -- Arm 1: 0-1-2
  | 0, 1 | 1, 0 | 1, 2 | 2, 1
  -- Arm 2: 0-3-4-5
  | 0, 3 | 3, 0 | 3, 4 | 4, 3 | 4, 5 | 5, 4
  -- Arm 3: 0-6-7-8-9-10
  | 0, 6 | 6, 0 | 6, 7 | 7, 6 | 7, 8 | 8, 7 | 8, 9 | 9, 8 | 9, 10 | 10, 9 => 1
  | _, _ => 0

theorem etilde8Adj_symm : etilde8Adj.IsSymm := by
  ext i j; simp only [etilde8Adj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem etilde8Adj_diag (i : Fin 11) : etilde8Adj i i = 0 := by
  fin_cases i <;> simp [etilde8Adj]

theorem etilde8Adj_01 (i j : Fin 11) : etilde8Adj i j = 0 ∨ etilde8Adj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [etilde8Adj]

/-- The Ẽ_8 quiver: all arrows directed toward the center (vertex 0).
Arrows: 2→1, 1→0, 5→4, 4→3, 3→0, 10→9, 9→8, 8→7, 7→6, 6→0. -/
def etilde8Quiver : Quiver (Fin 11) where
  Hom i j := PLift (
    -- Arm 1: 2→1→0
    (i.val = 2 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    -- Arm 2: 5→4→3→0
    (i.val = 5 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 0) ∨
    -- Arm 3: 10→9→8→7→6→0
    (i.val = 10 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 7) ∨
    (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 0))

instance etilde8Quiver_subsingleton (a b : Fin 11) :
    Subsingleton (@Quiver.Hom (Fin 11) etilde8Quiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem etilde8_arrow_implies_edge (i j : Fin 11)
    (hp : (i.val = 2 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
      (i.val = 5 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 0) ∨
      (i.val = 10 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 7) ∨
      (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 0)) :
    etilde8Adj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [etilde8Adj, h1, h2]

-- Ẽ_8 has 11 vertices; fin_cases creates 121 goals
set_option maxHeartbeats 3200000 in
private theorem etilde8_edge_has_arrow (i j : Fin 11) (hij : etilde8Adj i j = 1) :
    Nonempty (@Quiver.Hom (Fin 11) etilde8Quiver i j) ∨
    Nonempty (@Quiver.Hom (Fin 11) etilde8Quiver j i) := by
  fin_cases i <;> fin_cases j <;> simp [etilde8Adj] at hij <;>
    first
    | (left; exact ⟨⟨by decide⟩⟩)
    | (right; exact ⟨⟨by decide⟩⟩)

-- orientation proof delegates to helpers; still needs extra heartbeats for 11-vertex quiver
set_option maxHeartbeats 800000 in
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde8Orientation_isOrientationOf :
    @Etingof.IsOrientationOf 11 etilde8Quiver etilde8Adj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    exact hij (etilde8_arrow_implies_edge i j hp)
  · -- Each edge has an arrow in one direction
    exact etilde8_edge_has_arrow i j hij
  · -- No two-way arrows
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        omega

/-! ## Section 16: Extended Dynkin D̃₅ — definitions

The extended Dynkin diagram D̃₅ has 6 vertices with edges:
  0-2, 1-2, 2-3, 3-4, 3-5
Vertices 2 and 3 have degree 3; the rest have degree 1.

```
0     4
 \   / \
  2-3   5
 /
1
```

The null root is δ = (1,1,2,2,1,1), meaning (2I-adj)δ = 0.
-/

/-- Adjacency matrix for the extended Dynkin diagram D̃₅ on 6 vertices.
    Edges: 0-2, 1-2, 2-3, 3-4, 3-5. -/
def d5tildeAdj : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j =>
    if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
       (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
       (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
       (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
       (i.val = 3 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 3)
    then 1 else 0

theorem d5tildeAdj_symm : d5tildeAdj.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d5tildeAdj]

theorem d5tildeAdj_diag (i : Fin 6) : d5tildeAdj i i = 0 := by
  simp only [d5tildeAdj]; rw [if_neg]; push_neg
  exact ⟨fun h => by omega, fun h => by omega, fun h => by omega,
         fun h => by omega, fun h => by omega, fun h => by omega,
         fun h => by omega, fun h => by omega, fun h => by omega,
         fun h => by omega⟩

theorem d5tildeAdj_01 (i j : Fin 6) : d5tildeAdj i j = 0 ∨ d5tildeAdj i j = 1 := by
  simp only [d5tildeAdj]; split_ifs <;> simp

/-- Orientation for D̃₅: arrows 0→2, 1→2, 2→3, 4→3, 5→3.
    Vertex 3 is a pure sink; vertex 2 receives from 0,1 and sends to 3. -/
def d5tildeQuiver : Quiver (Fin 6) where
  Hom i j := PLift (
    (i.val = 0 ∧ j.val = 2) ∨
    (i.val = 1 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 3) ∨
    (i.val = 4 ∧ j.val = 3) ∨
    (i.val = 5 ∧ j.val = 3))

instance d5tildeQuiver_subsingleton (a b : Fin 6) :
    Subsingleton (@Quiver.Hom (Fin 6) d5tildeQuiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

theorem d5tildeOrientation_isOrientationOf :
    @Etingof.IsOrientationOf 6 d5tildeQuiver d5tildeAdj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    simp only [d5tildeAdj] at hij
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rw [if_pos (by omega)] at hij; exact hij rfl)
  · -- Each edge has an arrow in one direction
    simp only [d5tildeAdj] at hij
    split_ifs at hij with h
    · -- h gives which edge we're on; determine arrow direction
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      -- Edge 0-2: arrow 0→2 (left)
      · left; exact ⟨⟨by omega⟩⟩
      -- Edge 2-0: arrow 0→2 (right)
      · right; exact ⟨⟨by omega⟩⟩
      -- Edge 1-2: arrow 1→2 (left)
      · left; exact ⟨⟨by omega⟩⟩
      -- Edge 2-1: arrow 1→2 (right)
      · right; exact ⟨⟨by omega⟩⟩
      -- Edge 2-3: arrow 2→3 (left)
      · left; exact ⟨⟨by omega⟩⟩
      -- Edge 3-2: arrow 2→3 (right)
      · right; exact ⟨⟨by omega⟩⟩
      -- Edge 3-4: arrow 4→3 (right)
      · right; exact ⟨⟨by omega⟩⟩
      -- Edge 4-3: arrow 4→3 (left)
      · left; exact ⟨⟨by omega⟩⟩
      -- Edge 3-5: arrow 5→3 (right)
      · right; exact ⟨⟨by omega⟩⟩
      -- Edge 5-3: arrow 5→3 (left)
      · left; exact ⟨⟨by omega⟩⟩
    · simp at hij
  · -- No two-way arrows
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
         omega)

/-! ## Section 17: D̃₅ representation construction

For parameter m ∈ ℕ, the representation has dimension vector
  (m+1, m+1, 2(m+1), 2(m+1), m+1, m+1)
following the null root δ = (1,1,2,2,1,1).

Vertex spaces:
- V₀ = V₁ = V₄ = V₅ = ℂ^{m+1}
- V₂ = V₃ = ℂ^{2(m+1)}

Maps (under orientation 0→2, 1→2, 2→3, 4→3, 5→3):
- α: V₀ → V₂ : first-component embedding x ↦ (x, 0)
- β: V₁ → V₂ : second-component embedding x ↦ (0, x)
- γ: V₂ → V₃ : block matrix [[I,I],[I,N]] so (x,y) ↦ (x+y, x+Ny)
- δ: V₄ → V₃ : first-component embedding x ↦ (x, 0)
- ε: V₅ → V₃ : second-component embedding x ↦ (0, x)

Key property: γ is invertible (det = (-1)^{m+1} ≠ 0).

Indecomposability proof sketch:
1. Core argument at V₂: embed1/embed2 split W(2) into W(0) ⊕ W(1) components
2. Core argument at V₃: embed4/embed5 split W(3) into W(4) ⊕ W(5) components
3. γ forces: W(0) ⊆ W(4) ∩ W(5), W(1) ⊆ W(4), N(W(1)) ⊆ W(5)
4. By complement equality: all leaf subspaces W(0) = W(1) = W(4) = W(5)
5. N preserves this common subspace → nilpotent_invariant_compl_trivial
-/

/-- The D̃₅ connecting map γ : ℂ^{2(m+1)} → ℂ^{2(m+1)}.
    Block form [[I,I],[I,N]] where N is the nilpotent shift.
    γ(w)_i = if i < m+1 then w_i + w_{m+1+i}       (first block: x+y)
             else w_{i-(m+1)} + N(y)_{i-(m+1)}       (second block: x+Ny) -/
noncomputable def d5tildeGamma (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) where
  toFun w i :=
    if h : i.val < m + 1 then
      -- First block: (x + y)_i = w_i + w_{m+1+i}
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else
      -- Second block: (x + Ny)_{i-(m+1)}
      let j := i.val - (m + 1)
      w ⟨j, by omega⟩ +
        if h2 : j + 1 < m + 1 then w ⟨m + 1 + j + 1, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-! ## Section 16: Ẽ_6 representation construction

The Ẽ_6 = T_{2,2,2} representation uses dimension vector δ = (3,2,1,2,1,2,1)·(m+1),
where δ is the null root of the Ẽ_6 Cartan matrix.

- Center (vertex 0): ℂ^{3(m+1)} with three blocks A, B, C each ℂ^{m+1}
- Inner vertices (1,3,5): ℂ^{2(m+1)} with two blocks each
- Tips (2,4,6): ℂ^{m+1}

Maps along each arm (tip → inner → center):
- Arm 1 (2→1→0): x ↦ (x,0) ↦ (x,b,0) — embeds into blocks A,B of center
- Arm 2 (4→3→0): x ↦ (x,0) ↦ (x,0,b) — embeds into blocks A,C of center
- Arm 3 (6→5→0): x ↦ (x,Nx) ↦ (Nx,0,x) — nilpotent-twisted, blocks A,C

Arms 1 and 2 both send their tips to block A, coupling tips 2 and 4.
The nilpotent twist in arm 3 forces N-invariance, yielding indecomposability.
-/

/-- Dimension function for Ẽ_6 vertices: center gets 3(m+1), inner vertices 2(m+1), tips m+1. -/
def etilde6Dim (m : ℕ) (v : Fin 7) : ℕ :=
  match v.val with
  | 0 => 3 * (m + 1)
  | 1 | 3 | 5 => 2 * (m + 1)
  | _ => m + 1  -- vertices 2, 4, 6

/-- Embedding from 2-block space into blocks (A,B,_) of 3-block center: (a,b) ↦ (a,b,0). -/
noncomputable def embed2to3_AB (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (3 * (m + 1)) → ℂ) where
  toFun x i := if h : i.val < 2 * (m + 1) then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Dimension of vertex v in the D̃₅ representation:
    vertices 0,1,4,5 get m+1; vertices 2,3 get 2(m+1). -/
def d5tildeDim (m : ℕ) (v : Fin 6) : ℕ :=
  if v.val = 2 ∨ v.val = 3 then 2 * (m + 1) else m + 1

/-- Match-based map for the D̃₅ representation. -/
private noncomputable def d5tildeRepMap (m : ℕ) (a b : Fin 6) :
    (Fin (d5tildeDim m a) → ℂ) →ₗ[ℂ] (Fin (d5tildeDim m b) → ℂ) :=
  match a, b with
  | ⟨0, _⟩, ⟨2, _⟩ => starEmbed1 m  -- α: first-component embed
  | ⟨1, _⟩, ⟨2, _⟩ => starEmbed2 m  -- β: second-component embed
  | ⟨2, _⟩, ⟨3, _⟩ => d5tildeGamma m  -- γ: [[I,I],[I,N]]
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1 m  -- δ: first-component embed
  | ⟨5, _⟩, ⟨3, _⟩ => starEmbed2 m  -- ε: second-component embed
  | _, _ => 0

-- The D̃₅ representation with dimension vector (m+1, m+1, 2(m+1), 2(m+1), m+1, m+1).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def d5tildeRep (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin 6) _ d5tildeQuiver := by
  letI := d5tildeQuiver
  exact {
    obj := fun v => Fin (d5tildeDim m v) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => d5tildeRepMap m a b
  }

/-! ## Section 18: Indecomposability of D̃₅ representations

The proof follows the star (K_{1,4}) indecomposability argument:
1. Core argument at each center: embed1/embed2 split center space into leaf components
2. γ = [[I,I],[I,N]] maps: if (x,y) ∈ W(2), then (x+y, x+Ny) ∈ W(3)
   - Taking y=0: x ∈ W(0) implies x ∈ W(4) and x ∈ W(5)
   - Taking x=0: y ∈ W(1) implies y ∈ W(4) and Ny ∈ W(5)
3. By complement equality (compl_eq_of_le): all leaf subspaces equal
4. N preserves this common subspace → nilpotent_invariant_compl_trivial
5. Propagate: if common leaf subspace = ⊥, both centers = ⊥ via decomposition
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
set_option maxHeartbeats 1600000 in
theorem d5tildeRep_isIndecomposable (m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 6)
      d5tildeQuiver (d5tildeRep m) := by
  letI := d5tildeQuiver
  constructor
  · -- Nontrivial at vertex 0 (dim m+1 ≥ 1)
    refine ⟨⟨0, by omega⟩, ?_⟩
    show Nontrivial (Fin (d5tildeDim m ⟨0, by omega⟩) → ℂ)
    simp only [d5tildeDim]
    infer_instance
  · -- Indecomposability
    intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Key disjointness: embed1(x) + embed2(y) = 0 → x = 0 ∧ y = 0
    have embed_sum_zero : ∀ x y : Fin (m + 1) → ℂ,
        starEmbed1 m x + starEmbed2 m y = 0 → x = 0 ∧ y = 0 := by
      intro x y h
      have heval : ∀ j : Fin (2 * (m + 1)),
          starEmbed1 m x j + starEmbed2 m y j = 0 :=
        fun j => by have := congr_fun h j; simpa using this
      constructor <;> ext ⟨i, hi⟩ <;> simp only [Pi.zero_apply]
      · have := heval ⟨i, by omega⟩
        simp only [starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk] at this
        split_ifs at this with h1
        · omega
        · simpa using this
      · have := heval ⟨m + 1 + i, by omega⟩
        simp only [starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk] at this
        split_ifs at this with h1 h2
        · omega
        · omega
        · simp only [zero_add] at this
          have key : (⟨m + 1 + i - (m + 1), by omega⟩ : Fin (m + 1)) = ⟨i, hi⟩ := by
            simp only [Fin.mk.injEq]; omega
          rwa [key] at this
        · omega
    -- Core decomposition: if embed1(x) + embed2(z) ∈ W(center), then
    -- x ∈ W(left_leaf) and z ∈ W(right_leaf).
    -- We prove this for both centers (vertex 2 with leaves 0,1 and vertex 3 with leaves 4,5).
    have core (W W' : ∀ v, Submodule ℂ ((d5tildeRep m).obj v))
        (hW : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W a, (d5tildeRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W' a, (d5tildeRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x z : Fin (m + 1) → ℂ)
        -- At center vertex 2: if embed1(x) + embed2(z) ∈ W(2), then x ∈ W(0), z ∈ W(1)
        (hmem : starEmbed1 m x + starEmbed2 m z ∈ W ⟨2, by omega⟩) :
        x ∈ W ⟨0, by omega⟩ ∧ z ∈ W ⟨1, by omega⟩ := by
      -- Decompose x at leaf 0: x = a + b, a ∈ W(0), b ∈ W'(0)
      have htop0 := (hc ⟨0, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop0
      -- Decompose z at leaf 1: z = c + d, c ∈ W(1), d ∈ W'(1)
      have htop1 := (hc ⟨1, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
      obtain ⟨c, hc1, d, hd, hcd⟩ := Submodule.mem_sup.mp htop1
      -- embed1(a) ∈ W(2) and embed2(c) ∈ W(2) via invariance
      have ha2 : starEmbed1 m a ∈ W ⟨2, by omega⟩ :=
        hW (show @Quiver.Hom _ d5tildeQuiver ⟨0, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inl ⟨rfl, rfl⟩⟩) a ha
      have hc2 : starEmbed2 m c ∈ W ⟨2, by omega⟩ :=
        hW (show @Quiver.Hom _ d5tildeQuiver ⟨1, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩) c hc1
      -- embed1(b) ∈ W'(2) and embed2(d) ∈ W'(2)
      have hb2 : starEmbed1 m b ∈ W' ⟨2, by omega⟩ :=
        hW' (show @Quiver.Hom _ d5tildeQuiver ⟨0, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inl ⟨rfl, rfl⟩⟩) b hb
      have hd2 : starEmbed2 m d ∈ W' ⟨2, by omega⟩ :=
        hW' (show @Quiver.Hom _ d5tildeQuiver ⟨1, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩) d hd
      -- Cross-terms sum to zero via complement at center
      have hsum : starEmbed1 m x + starEmbed2 m z =
          (starEmbed1 m a + starEmbed2 m c) + (starEmbed1 m b + starEmbed2 m d) := by
        rw [← hab, ← hcd]; simp [map_add]; abel
      rw [hsum] at hmem
      have hadd : starEmbed1 m a + starEmbed2 m c ∈ W ⟨2, by omega⟩ :=
        (W ⟨2, by omega⟩).add_mem ha2 hc2
      have hw'_in_W : starEmbed1 m b + starEmbed2 m d ∈ W ⟨2, by omega⟩ := by
        have hsmul := (W ⟨2, by omega⟩).smul_mem (-1 : ℂ) hadd
        have hadd2 := (W ⟨2, by omega⟩).add_mem hmem hsmul
        have key : starEmbed1 m a + starEmbed2 m c + (starEmbed1 m b + starEmbed2 m d) +
            (-1 : ℂ) • (starEmbed1 m a + starEmbed2 m c) = starEmbed1 m b + starEmbed2 m d := by
          ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rwa [key] at hadd2
      have hzero : starEmbed1 m b + starEmbed2 m d = 0 := by
        have := Submodule.mem_inf.mpr ⟨hw'_in_W,
          (W' ⟨2, by omega⟩).add_mem hb2 hd2⟩
        rwa [(hc ⟨2, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
      obtain ⟨hb0, hd0⟩ := embed_sum_zero b d hzero
      exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
             hcd ▸ by rw [hd0, add_zero]; exact hc1⟩
    -- Same core at vertex 3 (center with leaves 4, 5)
    have core3 (W W' : ∀ v, Submodule ℂ ((d5tildeRep m).obj v))
        (hW : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W a, (d5tildeRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W' a, (d5tildeRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x z : Fin (m + 1) → ℂ)
        (hmem : starEmbed1 m x + starEmbed2 m z ∈ W ⟨3, by omega⟩) :
        x ∈ W ⟨4, by omega⟩ ∧ z ∈ W ⟨5, by omega⟩ := by
      have htop4 := (hc ⟨4, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop4
      have htop5 := (hc ⟨5, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
      obtain ⟨c, hc5, d, hd, hcd⟩ := Submodule.mem_sup.mp htop5
      have ha3 : starEmbed1 m a ∈ W ⟨3, by omega⟩ :=
        hW (show @Quiver.Hom _ d5tildeQuiver ⟨4, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩) a ha
      have hc3 : starEmbed2 m c ∈ W ⟨3, by omega⟩ :=
        hW (show @Quiver.Hom _ d5tildeQuiver ⟨5, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩) c hc5
      have hb3 : starEmbed1 m b ∈ W' ⟨3, by omega⟩ :=
        hW' (show @Quiver.Hom _ d5tildeQuiver ⟨4, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩) b hb
      have hd3 : starEmbed2 m d ∈ W' ⟨3, by omega⟩ :=
        hW' (show @Quiver.Hom _ d5tildeQuiver ⟨5, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩) d hd
      have hsum : starEmbed1 m x + starEmbed2 m z =
          (starEmbed1 m a + starEmbed2 m c) + (starEmbed1 m b + starEmbed2 m d) := by
        rw [← hab, ← hcd]; simp [map_add]; abel
      rw [hsum] at hmem
      have hadd : starEmbed1 m a + starEmbed2 m c ∈ W ⟨3, by omega⟩ :=
        (W ⟨3, by omega⟩).add_mem ha3 hc3
      have hw'_in_W : starEmbed1 m b + starEmbed2 m d ∈ W ⟨3, by omega⟩ := by
        have hsmul := (W ⟨3, by omega⟩).smul_mem (-1 : ℂ) hadd
        have hadd2 := (W ⟨3, by omega⟩).add_mem hmem hsmul
        have key : starEmbed1 m a + starEmbed2 m c + (starEmbed1 m b + starEmbed2 m d) +
            (-1 : ℂ) • (starEmbed1 m a + starEmbed2 m c) = starEmbed1 m b + starEmbed2 m d := by
          ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rwa [key] at hadd2
      have hzero : starEmbed1 m b + starEmbed2 m d = 0 := by
        have := Submodule.mem_inf.mpr ⟨hw'_in_W,
          (W' ⟨3, by omega⟩).add_mem hb3 hd3⟩
        rwa [(hc ⟨3, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
      obtain ⟨hb0, hd0⟩ := embed_sum_zero b d hzero
      exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
             hcd ▸ by rw [hd0, add_zero]; exact hc5⟩
    -- γ-based containments: γ(x,y) = (x+y, x+Ny)
    -- From (x,0) ∈ W(2) with x ∈ W(0): γ(x,0) = embed1(x) + embed2(x) ∈ W(3)
    -- → x ∈ W(4) and x ∈ W(5)
    -- From (0,y) ∈ W(2) with y ∈ W(1): γ(0,y) = embed1(y) + embed2(Ny) ∈ W(3)
    -- → y ∈ W(4) and Ny ∈ W(5)
    -- γ(embed1(x)) = embed1(x) + embed2(x): extensional entry-by-entry computation
    -- γ maps (x,0) ↦ (x+0, x+N·0) = (x, x) = embed1(x) + embed2(x)
    have gamma_from_embed1 : ∀ (x : Fin (m + 1) → ℂ),
        d5tildeGamma m (starEmbed1 m x) = starEmbed1 m x + starEmbed2 m x := by
      intro x; ext i
      show (d5tildeGamma m (starEmbed1 m x)) i =
        (starEmbed1 m x) i + (starEmbed2 m x) i
      simp only [d5tildeGamma, starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases h : i.val < m + 1
      · simp only [dif_pos h, dif_neg (show ¬(m + 1 ≤ i.val) by omega),
            dif_neg (show ¬(m + 1 + i.val < m + 1) by omega), add_zero]
      · push_neg at h
        simp only [dif_neg (show ¬(i.val < m + 1) by omega),
            dif_pos (show m + 1 ≤ i.val by omega),
            dif_pos (show i.val - (m + 1) < m + 1 by omega),
            dif_neg (show ¬(m + 1 ≤ i.val - (m + 1)) by omega), zero_add]
        by_cases h2 : i.val - (m + 1) + 1 < m + 1
        · simp only [dif_pos h2,
            dif_neg (show ¬(m + 1 + (i.val - (m + 1)) + 1 < m + 1) by omega),
            add_zero]
        · simp only [dif_neg h2, add_zero]
    -- γ(embed2(y)) = embed1(y) + embed2(Ny): similar computation
    -- γ maps (0,y) ↦ (0+y, 0+Ny) = (y, Ny) = embed1(y) + embed2(Ny)
    have gamma_from_embed2 : ∀ (y : Fin (m + 1) → ℂ),
        d5tildeGamma m (starEmbed2 m y) =
          starEmbed1 m y + starEmbed2 m (nilpotentShiftLin m y) := by
      intro y
      have aux : ∀ j : Fin (m + 1), nilpotentShiftLin m y j =
          if h : j.val + 1 < m + 1 then y ⟨j.val + 1, h⟩ else 0 :=
        nilpotentShiftLin_apply m y
      ext i
      simp only [d5tildeGamma, starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.add_apply, aux]
      by_cases h : i.val < m + 1
      · simp only [dif_pos h,
            dif_neg (show ¬(m + 1 ≤ i.val) by omega),
            dif_pos (show m + 1 ≤ m + 1 + i.val by omega),
            zero_add, add_zero]
        exact congr_arg y (Fin.ext (by simp))
      · push_neg at h
        simp only [dif_neg (show ¬(i.val < m + 1) by omega),
            dif_pos (show m + 1 ≤ i.val by omega),
            dif_neg (show ¬(m + 1 ≤ i.val - (m + 1)) by omega),
            zero_add]
        by_cases h2 : i.val - (m + 1) + 1 < m + 1
        · simp only [dif_pos h2,
              dif_pos (show m + 1 ≤ m + 1 + (i.val - (m + 1)) + 1 by omega)]
          exact congr_arg y (Fin.ext (by simp; omega))
        · simp only [dif_neg h2]
    -- Gamma containments for W₁
    have gamma_containment
        (W W' : ∀ v, Submodule ℂ ((d5tildeRep m).obj v))
        (hW : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W a, (d5tildeRep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W' a, (d5tildeRep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v)) :
        (∀ x : Fin (m + 1) → ℂ, x ∈ W ⟨0, by omega⟩ → x ∈ W ⟨4, by omega⟩) ∧
        (∀ x : Fin (m + 1) → ℂ, x ∈ W ⟨0, by omega⟩ → x ∈ W ⟨5, by omega⟩) ∧
        (∀ x : Fin (m + 1) → ℂ, x ∈ W ⟨1, by omega⟩ → x ∈ W ⟨4, by omega⟩) ∧
        (∀ x : Fin (m + 1) → ℂ, x ∈ W ⟨1, by omega⟩ →
          nilpotentShiftLin m x ∈ W ⟨5, by omega⟩) := by
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
      · -- x ∈ W(0) → x ∈ W(4): use γ(embed1(x)) = embed1(x) + embed2(x)
        have he1 : starEmbed1 m x ∈ W ⟨2, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨0, by omega⟩ ⟨2, by omega⟩
            from ⟨Or.inl ⟨rfl, rfl⟩⟩) x hx
        have hgamma : d5tildeGamma m (starEmbed1 m x) ∈ W ⟨3, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨2, by omega⟩ ⟨3, by omega⟩
            from ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩) _ he1
        rw [gamma_from_embed1] at hgamma
        exact (core3 W W' hW hW' hc x x hgamma).1
      · -- x ∈ W(0) → x ∈ W(5): same path, second component
        have he1 : starEmbed1 m x ∈ W ⟨2, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨0, by omega⟩ ⟨2, by omega⟩
            from ⟨Or.inl ⟨rfl, rfl⟩⟩) x hx
        have hgamma : d5tildeGamma m (starEmbed1 m x) ∈ W ⟨3, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨2, by omega⟩ ⟨3, by omega⟩
            from ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩) _ he1
        rw [gamma_from_embed1] at hgamma
        exact (core3 W W' hW hW' hc x x hgamma).2
      · -- y ∈ W(1) → y ∈ W(4): use γ(embed2(y)) = embed1(y) + embed2(Ny)
        have he2 : starEmbed2 m y ∈ W ⟨2, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨1, by omega⟩ ⟨2, by omega⟩
            from ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩) y hy
        have hgamma : d5tildeGamma m (starEmbed2 m y) ∈ W ⟨3, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨2, by omega⟩ ⟨3, by omega⟩
            from ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩) _ he2
        rw [gamma_from_embed2] at hgamma
        exact (core3 W W' hW hW' hc y (nilpotentShiftLin m y) hgamma).1
      · -- y ∈ W(1) → Ny ∈ W(5): same path, second component
        have he2 : starEmbed2 m y ∈ W ⟨2, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨1, by omega⟩ ⟨2, by omega⟩
            from ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩) y hy
        have hgamma : d5tildeGamma m (starEmbed2 m y) ∈ W ⟨3, by omega⟩ :=
          hW (show @Quiver.Hom _ d5tildeQuiver ⟨2, by omega⟩ ⟨3, by omega⟩
            from ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩) _ he2
        rw [gamma_from_embed2] at hgamma
        exact (core3 W W' hW hW' hc y (nilpotentShiftLin m y) hgamma).2
    -- Helper: if A ≤ B, A' ≤ B', IsCompl A A', IsCompl B B', then A = B
    have compl_eq_of_le (A B A' B' : Submodule ℂ (Fin (m + 1) → ℂ))
        (hAB : A ≤ B) (hA'B' : A' ≤ B')
        (hcA : IsCompl A A') (hcB : IsCompl B B') : A = B := by
      apply le_antisymm hAB; intro x hx
      have hx_top := hcA.sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx_top
      have ha'_B : a' ∈ B := by
        have h := B.sub_mem hx (hAB ha); rwa [show a + a' - a = a' from by abel] at h
      have : a' ∈ B ⊓ B' := Submodule.mem_inf.mpr ⟨ha'_B, hA'B' ha'⟩
      rw [hcB.inf_eq_bot, Submodule.mem_bot] at this; rwa [this, add_zero]
    -- All leaf subspaces of W₁ are equal
    obtain ⟨h04, h05, h14, hN15⟩ := gamma_containment W₁ W₂ hW₁_inv hW₂_inv hcompl
    obtain ⟨h04', h05', h14', hN15'⟩ := gamma_containment W₂ W₁ hW₂_inv hW₁_inv
      (fun v => (hcompl v).symm)
    have heq04 := compl_eq_of_le _ _ _ _ h04 h04' (hcompl ⟨0, by omega⟩) (hcompl ⟨4, by omega⟩)
    have heq05 := compl_eq_of_le _ _ _ _ h05 h05' (hcompl ⟨0, by omega⟩) (hcompl ⟨5, by omega⟩)
    have heq14 := compl_eq_of_le _ _ _ _ h14 h14' (hcompl ⟨1, by omega⟩) (hcompl ⟨4, by omega⟩)
    have heq01 : W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ := heq04.trans heq14.symm
    -- Same for W₂
    have heq04' := compl_eq_of_le _ _ _ _ h04' h04
      ((hcompl ⟨0, by omega⟩).symm) ((hcompl ⟨4, by omega⟩).symm)
    have heq05' := compl_eq_of_le _ _ _ _ h05' h05
      ((hcompl ⟨0, by omega⟩).symm) ((hcompl ⟨5, by omega⟩).symm)
    have heq14' := compl_eq_of_le _ _ _ _ h14' h14
      ((hcompl ⟨1, by omega⟩).symm) ((hcompl ⟨4, by omega⟩).symm)
    have heq01' : W₂ ⟨0, by omega⟩ = W₂ ⟨1, by omega⟩ := heq04'.trans heq14'.symm
    -- N preserves W₁(0) and W₂(0)
    have hN₁ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₁ ⟨0, by omega⟩ → nilpotentShiftLin m x ∈ W₁ ⟨0, by omega⟩ := by
      intro x hx
      have hx1 : x ∈ W₁ ⟨1, by omega⟩ := heq01 ▸ hx
      exact heq05 ▸ hN15 x hx1
    have hN₂ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₂ ⟨0, by omega⟩ → nilpotentShiftLin m x ∈ W₂ ⟨0, by omega⟩ := by
      intro x hx
      have hx1 : x ∈ W₂ ⟨1, by omega⟩ := heq01' ▸ hx
      exact heq05' ▸ hN15' x hx1
    -- Apply nilpotent_invariant_compl_trivial at vertex 0
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩) hN₁ hN₂ (hcompl ⟨0, by omega⟩)
    -- Propagate: W(0) = ⊥ → all W(v) = ⊥
    have center_decomp : ∀ w : Fin (2 * (m + 1)) → ℂ,
        w = starEmbed1 m (fun i => w ⟨i.val, by omega⟩) +
            starEmbed2 m (fun i => w ⟨m + 1 + i.val, by omega⟩) := by
      intro w; ext ⟨j, hj⟩
      simp only [Pi.add_apply, starEmbed1, starEmbed2, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hjlt : j < m + 1
      · simp only [dif_pos hjlt, show ¬(m + 1 ≤ j) from by omega, dite_false, add_zero]
      · simp only [dif_neg hjlt, show m + 1 ≤ j from by omega, dite_true, zero_add]
        congr 1; ext; simp; omega
    suffices propagate : ∀ (W W' : ∀ v, Submodule ℂ ((d5tildeRep m).obj v)),
        (∀ {a b : Fin 6} (e : @Quiver.Hom _ d5tildeQuiver a b),
          ∀ x ∈ W' a, (d5tildeRep m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W ⟨0, by omega⟩ = W ⟨1, by omega⟩ →
        W ⟨0, by omega⟩ = W ⟨4, by omega⟩ →
        W ⟨0, by omega⟩ = W ⟨5, by omega⟩ →
        W ⟨0, by omega⟩ = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₂_inv hcompl heq01 heq04 heq05 h
      · right; exact propagate W₂ W₁ hW₁_inv (fun v => (hcompl v).symm)
          heq01' heq04' heq05' h
    intro W W' hW'_inv hc h01 h04 h05 hbot v
    fin_cases v
    · exact hbot
    · show W ⟨1, by omega⟩ = ⊥; rw [← h01]; exact hbot
    · -- v = 2 (center)
      show W ⟨2, by omega⟩ = ⊥
      have hW'0_top : W' ⟨0, by omega⟩ = ⊤ := by
        have := (hc ⟨0, by omega⟩).sup_eq_top; rwa [hbot, bot_sup_eq] at this
      have hW'1_top : W' ⟨1, by omega⟩ = ⊤ := by
        have := (hc ⟨1, by omega⟩).sup_eq_top; rwa [← h01, hbot, bot_sup_eq] at this
      have h_emb0 : ∀ (x : Fin (m + 1) → ℂ), starEmbed1 m x ∈ W' ⟨2, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ d5tildeQuiver ⟨0, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inl ⟨rfl, rfl⟩⟩) x (hW'0_top ▸ Submodule.mem_top)
      have h_emb1 : ∀ (x : Fin (m + 1) → ℂ), starEmbed2 m x ∈ W' ⟨2, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ d5tildeQuiver ⟨1, by omega⟩ ⟨2, by omega⟩
          from ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩) x (hW'1_top ▸ Submodule.mem_top)
      rw [eq_bot_iff]; intro (w : Fin (2 * (m + 1)) → ℂ) hw
      have hw' : w ∈ W' ⟨2, by omega⟩ :=
        center_decomp w ▸ (W' ⟨2, by omega⟩).add_mem (h_emb0 _) (h_emb1 _)
      have := Submodule.mem_inf.mpr ⟨hw, hw'⟩
      rwa [(hc ⟨2, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
    · -- v = 3 (center)
      show W ⟨3, by omega⟩ = ⊥
      have hW'4_top : W' ⟨4, by omega⟩ = ⊤ := by
        have := (hc ⟨4, by omega⟩).sup_eq_top; rwa [← h04, hbot, bot_sup_eq] at this
      have hW'5_top : W' ⟨5, by omega⟩ = ⊤ := by
        have := (hc ⟨5, by omega⟩).sup_eq_top; rwa [← h05, hbot, bot_sup_eq] at this
      have h_emb4 : ∀ (x : Fin (m + 1) → ℂ), starEmbed1 m x ∈ W' ⟨3, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ d5tildeQuiver ⟨4, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩) x
          (hW'4_top ▸ Submodule.mem_top)
      have h_emb5 : ∀ (x : Fin (m + 1) → ℂ), starEmbed2 m x ∈ W' ⟨3, by omega⟩ :=
        fun x => hW'_inv (show @Quiver.Hom _ d5tildeQuiver ⟨5, by omega⟩ ⟨3, by omega⟩
          from ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩) x
          (hW'5_top ▸ Submodule.mem_top)
      rw [eq_bot_iff]; intro (w : Fin (2 * (m + 1)) → ℂ) hw
      have hw' : w ∈ W' ⟨3, by omega⟩ :=
        center_decomp w ▸ (W' ⟨3, by omega⟩).add_mem (h_emb4 _) (h_emb5 _)
      have := Submodule.mem_inf.mpr ⟨hw, hw'⟩
      rwa [(hc ⟨3, by omega⟩).inf_eq_bot, Submodule.mem_bot] at this
    · show W ⟨4, by omega⟩ = ⊥; rw [← h04]; exact hbot
    · show W ⟨5, by omega⟩ = ⊥; rw [← h05]; exact hbot

/-! ## Section 19: Dimension vectors and infinite type for D̃₅ -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem d5tildeRep_dimVec (m : ℕ) (v : Fin 6) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin 6) _
      d5tildeQuiver (d5tildeRep m) v ≃ₗ[ℂ]
      (Fin (d5tildeDim m v) → ℂ)) :=
  ⟨LinearEquiv.refl ℂ _⟩

/-- Embedding from 2-block space into blocks (A,_,C) of 3-block center: (a,b) ↦ (a,0,b).
    First component goes to block A (positions 0..m), second to block C (positions 2(m+1)..3(m+1)-1). -/
noncomputable def embed2to3_AC (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (3 * (m + 1)) → ℂ) where
  toFun x i :=
    if h : i.val < m + 1 then
      -- Block A: gets first component of input (positions 0 to m)
      x ⟨i.val, by omega⟩
    else if h2 : 2 * (m + 1) ≤ i.val then
      -- Block C: gets second component of input (positions m+1 to 2(m+1)-1)
      (if h3 : i.val - 2 * (m + 1) < m + 1
       then x ⟨(m + 1) + (i.val - 2 * (m + 1)), by omega⟩ else 0)
    else 0  -- Block B: zero
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Embedding from 2-block space into blocks (C,_,A) of 3-block center: (a,b) ↦ (b,0,a).
    First component of input goes to block C, second goes to block A. -/
noncomputable def embed2to3_CA (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (3 * (m + 1)) → ℂ) where
  toFun x i :=
    if h : i.val < m + 1 then
      -- Block A: gets second component of input (positions m+1 to 2(m+1)-1)
      x ⟨i.val + (m + 1), by omega⟩
    else if h2 : 2 * (m + 1) ≤ i.val then
      -- Block C: gets first component of input (positions 0 to m)
      (if h3 : i.val - 2 * (m + 1) < m + 1 then x ⟨i.val - 2 * (m + 1), by omega⟩ else 0)
    else 0  -- Block B: zero
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The extended Dynkin diagram D̃₅ has infinite representation type:
    for each m, there is an indecomposable rep with distinct dim vector. -/
theorem d5tilde_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 6 d5tildeAdj := by
  intro hft
  letI := d5tildeQuiver
  have hfin := @hft ℂ _ inferInstance d5tildeQuiver
    (fun a b => d5tildeQuiver_subsingleton a b)
    d5tildeOrientation_isOrientationOf
  have hmem : ∀ m : ℕ, (d5tildeDim m) ∈
      {d : Fin 6 → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin 6),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨d5tildeRep m, d5tildeRep_isIndecomposable m, d5tildeRep_dimVec m⟩
  have hinj : Function.Injective d5tildeDim := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    show m₁ = m₂
    -- d5tildeDim m ⟨0, _⟩ = if 0 = 2 ∨ 0 = 3 then 2*(m+1) else m+1 = m+1
    change (if (⟨0, by omega⟩ : Fin 6).val = 2 ∨ (⟨0, by omega⟩ : Fin 6).val = 3
            then 2 * (m₁ + 1) else m₁ + 1) =
           (if (⟨0, by omega⟩ : Fin 6).val = 2 ∨ (⟨0, by omega⟩ : Fin 6).val = 3
            then 2 * (m₂ + 1) else m₂ + 1) at h0
    simp only [Fin.val_mk, show ¬(0 = 2 ∨ 0 = 3) from by omega, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 17a: Parameterized D̃_n infrastructure

For parameter k ∈ ℕ, D̃_{k+5} has k+6 vertices:
  - Vertices 0, 1: leaves of branch point 2
  - Vertices 2, 3, ..., k+3: path (branch points at 2 and k+3)
  - Vertices k+4, k+5: leaves of branch point k+3

Null root δ = (1, 1, 2, 2, ..., 2, 1, 1) with k+2 interior 2's.

For m ∈ ℕ, the representation has dimension vector m·δ + δ:
  - Leaf vertices: dim m+1
  - Interior path vertices: dim 2(m+1)

This generalizes the D̃_5 (k=0) construction above. -/

/-- Edge predicate for D̃_{k+5}: vertices i,j are adjacent iff they form
    a leaf-branch edge or a consecutive path edge. -/
private def dTildeEdgePred (k : ℕ) (i j : Fin (k + 6)) : Prop :=
  -- Leaf edges at first branch point
  (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
  -- Path edges: consecutive vertices on the path 2-3-..-(k+3)
  (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ k + 3) ∨
  -- Leaf edges at second branch point
  (i.val = k + 4 ∧ j.val = k + 3) ∨ (i.val = k + 5 ∧ j.val = k + 3)

private instance (k : ℕ) (i j : Fin (k + 6)) : Decidable (dTildeEdgePred k i j) := by
  unfold dTildeEdgePred; infer_instance

private theorem dTildeEdgePred_irrefl (k : ℕ) (i : Fin (k + 6)) :
    ¬ dTildeEdgePred k i i := by
  simp only [dTildeEdgePred]; push_neg; exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Adjacency matrix for D̃_{k+5}: the extended Dynkin diagram with k+6 vertices,
    two branch points connected by a path of length k+1. -/
def dTildeAdj (k : ℕ) : Matrix (Fin (k + 6)) (Fin (k + 6)) ℤ :=
  fun i j => if dTildeEdgePred k i j ∨ dTildeEdgePred k j i then 1 else 0

theorem dTildeAdj_symm (k : ℕ) : (dTildeAdj k).IsSymm := by
  ext i j; simp only [dTildeAdj, Matrix.transpose_apply]
  simp only [show dTildeEdgePred k j i ∨ dTildeEdgePred k i j ↔
    dTildeEdgePred k i j ∨ dTildeEdgePred k j i from Or.comm]

theorem dTildeAdj_diag (k : ℕ) (i : Fin (k + 6)) : dTildeAdj k i i = 0 := by
  simp only [dTildeAdj, show ¬(dTildeEdgePred k i i ∨ dTildeEdgePred k i i) from by
    push_neg; exact ⟨dTildeEdgePred_irrefl k i, dTildeEdgePred_irrefl k i⟩, ite_false]

theorem dTildeAdj_01 (k : ℕ) (i j : Fin (k + 6)) :
    dTildeAdj k i j = 0 ∨ dTildeAdj k i j = 1 := by
  unfold dTildeAdj; split_ifs <;> simp

/-- Arrow predicate for D̃_{k+5}: orientation 0→2, 1→2, 2→3→...→(k+3), (k+4)→(k+3), (k+5)→(k+3).
    Leaf arrows point inward to branch points; path arrows go left-to-right. -/
private def dTildeArrowPred (k : ℕ) (i j : Fin (k + 6)) : Prop :=
  (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) ∨
  (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ k + 3) ∨
  (i.val = k + 4 ∧ j.val = k + 3) ∨ (i.val = k + 5 ∧ j.val = k + 3)

private instance (k : ℕ) (i j : Fin (k + 6)) : Decidable (dTildeArrowPred k i j) := by
  unfold dTildeArrowPred; infer_instance

/-- Orientation for D̃_{k+5}: 0→2, 1→2, path left-to-right, (k+4)→(k+3), (k+5)→(k+3). -/
def dTildeQuiver (k : ℕ) : Quiver (Fin (k + 6)) where
  Hom i j := PLift (dTildeArrowPred k i j)

instance dTildeQuiver_subsingleton (k : ℕ) (a b : Fin (k + 6)) :
    Subsingleton (@Quiver.Hom (Fin (k + 6)) (dTildeQuiver k) a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The arrow predicate exactly captures one direction of each edge. -/
private theorem dTildeArrowPred_eq_edgePred (k : ℕ) (i j : Fin (k + 6)) :
    dTildeArrowPred k i j ↔ dTildeEdgePred k i j := by
  simp only [dTildeArrowPred, dTildeEdgePred]

private theorem dTildeAdj_eq_one_iff (k : ℕ) (i j : Fin (k + 6)) :
    dTildeAdj k i j = 1 ↔ dTildeEdgePred k i j ∨ dTildeEdgePred k j i := by
  simp only [dTildeAdj]; split_ifs with h <;> simp [h]

theorem dTildeOrientation_isOrientationOf (k : ℕ) :
    @Etingof.IsOrientationOf (k + 6) (dTildeQuiver k) (dTildeAdj k) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    have := (dTildeArrowPred_eq_edgePred k i j).mp hp
    exact hij ((dTildeAdj_eq_one_iff k i j).mpr (Or.inl this))
  · -- Each edge has an arrow in one direction
    rcases (dTildeAdj_eq_one_iff k i j).mp hij with hp | hp
    · left; exact ⟨⟨(dTildeArrowPred_eq_edgePred k i j).mpr hp⟩⟩
    · right; exact ⟨⟨(dTildeArrowPred_eq_edgePred k j i).mpr hp⟩⟩
  · -- No two-way arrows (antisymmetry)
    obtain ⟨⟨hp⟩⟩ := hi; obtain ⟨⟨hq⟩⟩ := hj
    simp only [dTildeArrowPred, dTildeEdgePred] at hp hq
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4, h5⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        omega

/-! ## Section 17a.2: D̃_n representation construction

Dimension vector: leaf vertices (0, 1, k+4, k+5) get m+1;
interior path vertices (2, ..., k+3) get 2(m+1).

Maps (under orientation 0→2, 1→2, 2→3→...→(k+3), (k+4)→(k+3), (k+5)→(k+3)):
- 0→2: starEmbed1 (first-component embedding)
- 1→2: starEmbed2 (second-component embedding)
- 2→3: d5tildeGamma (the [[I,I],[I,N]] coupling map)
- i→(i+1) for i=3,...,k+2: identity (LinearMap.id on ℂ^{2(m+1)})
- (k+4)→(k+3): starEmbed1
- (k+5)→(k+3): starEmbed2
-/

/-- Custom inductive indexing of the D̃_{k+5} vertex type. Each constructor
    corresponds to a structural role (leaf / branch / path-interior),
    mirroring the `Fin (k+6)` positions as:
    - `leftLeaf1` ↔ 0, `leftLeaf2` ↔ 1
    - `branchLeft` ↔ 2
    - `pathMid i` ↔ 3, 4, …, k+2 (for i : Fin k)
    - `branchRight` ↔ k+3
    - `rightLeaf1` ↔ k+4, `rightLeaf2` ↔ k+5
    Pattern matching on a `DTildeVertex k` reduces definitionally, which
    is what makes `dim` (below) unblock the D̃_n indecomposability proof
    at k-dependent positions. -/
inductive DTildeVertex (k : ℕ) where
  | leftLeaf1 : DTildeVertex k
  | leftLeaf2 : DTildeVertex k
  | branchLeft : DTildeVertex k
  | pathMid (i : Fin k) : DTildeVertex k
  | branchRight : DTildeVertex k
  | rightLeaf1 : DTildeVertex k
  | rightLeaf2 : DTildeVertex k
  deriving DecidableEq

/-- Dimension of vertex `v` in the D̃_{k+5} representation with parameter `m`:
    leaves get `m + 1`, interior (branch points and path middle) get
    `2 * (m + 1)`. Reduces by `rfl` on each constructor. -/
def DTildeVertex.dim {k : ℕ} (v : DTildeVertex k) (m : ℕ) : ℕ :=
  match v with
  | .leftLeaf1 | .leftLeaf2 | .rightLeaf1 | .rightLeaf2 => m + 1
  | .branchLeft | .branchRight | .pathMid _ => 2 * (m + 1)

/-- Structural-role to `Fin (k + 6)` index map. -/
def DTildeVertex.toFin {k : ℕ} : DTildeVertex k → Fin (k + 6)
  | .leftLeaf1   => ⟨0, by omega⟩
  | .leftLeaf2   => ⟨1, by omega⟩
  | .branchLeft  => ⟨2, by omega⟩
  | .pathMid i   => ⟨i.val + 3, by omega⟩
  | .branchRight => ⟨k + 3, by omega⟩
  | .rightLeaf1  => ⟨k + 4, by omega⟩
  | .rightLeaf2  => ⟨k + 5, by omega⟩

/-- Inverse of `toFin`: recover the structural constructor from a `Fin (k + 6)` index. -/
def DTildeVertex.ofFin (k : ℕ) (v : Fin (k + 6)) : DTildeVertex k :=
  if h0 : v.val = 0 then .leftLeaf1
  else if h1 : v.val = 1 then .leftLeaf2
  else if h2 : v.val = 2 then .branchLeft
  else if hpm : v.val ≤ k + 2 then .pathMid ⟨v.val - 3, by omega⟩
  else if hbr : v.val = k + 3 then .branchRight
  else if hrl1 : v.val = k + 4 then .rightLeaf1
  else .rightLeaf2

theorem DTildeVertex.toFin_ofFin (k : ℕ) (v : Fin (k + 6)) :
    (DTildeVertex.ofFin k v).toFin = v := by
  unfold DTildeVertex.ofFin
  split_ifs with h0 h1 h2 hpm hbr hrl1 <;>
    apply Fin.ext <;> simp [DTildeVertex.toFin] <;> omega

theorem DTildeVertex.ofFin_toFin (k : ℕ) (v : DTildeVertex k) :
    DTildeVertex.ofFin k v.toFin = v := by
  cases v with
  | leftLeaf1   =>
    show DTildeVertex.ofFin k ⟨0, by omega⟩ = .leftLeaf1
    unfold DTildeVertex.ofFin; rw [dif_pos rfl]
  | leftLeaf2   =>
    show DTildeVertex.ofFin k ⟨1, by omega⟩ = .leftLeaf2
    unfold DTildeVertex.ofFin
    rw [dif_neg (by decide : (1 : ℕ) ≠ 0), dif_pos rfl]
  | branchLeft  =>
    show DTildeVertex.ofFin k ⟨2, by omega⟩ = .branchLeft
    unfold DTildeVertex.ofFin
    rw [dif_neg (by decide : (2 : ℕ) ≠ 0), dif_neg (by decide : (2 : ℕ) ≠ 1),
        dif_pos rfl]
  | pathMid i   =>
    show DTildeVertex.ofFin k ⟨i.val + 3, by omega⟩ = .pathMid i
    unfold DTildeVertex.ofFin
    have hi : i.val < k := i.isLt
    rw [dif_neg (show (⟨i.val + 3, by omega⟩ : Fin (k + 6)).val ≠ 0 by
          show i.val + 3 ≠ 0; omega),
        dif_neg (show (⟨i.val + 3, by omega⟩ : Fin (k + 6)).val ≠ 1 by
          show i.val + 3 ≠ 1; omega),
        dif_neg (show (⟨i.val + 3, by omega⟩ : Fin (k + 6)).val ≠ 2 by
          show i.val + 3 ≠ 2; omega),
        dif_pos (show (⟨i.val + 3, by omega⟩ : Fin (k + 6)).val ≤ k + 2 by
          show i.val + 3 ≤ k + 2; omega)]
    congr 1
  | branchRight =>
    show DTildeVertex.ofFin k ⟨k + 3, by omega⟩ = .branchRight
    unfold DTildeVertex.ofFin
    rw [dif_neg (show k + 3 ≠ 0 by omega),
        dif_neg (show k + 3 ≠ 1 by omega),
        dif_neg (show k + 3 ≠ 2 by omega),
        dif_neg (show ¬ k + 3 ≤ k + 2 by omega),
        dif_pos rfl]
  | rightLeaf1  =>
    show DTildeVertex.ofFin k ⟨k + 4, by omega⟩ = .rightLeaf1
    unfold DTildeVertex.ofFin
    rw [dif_neg (show k + 4 ≠ 0 by omega),
        dif_neg (show k + 4 ≠ 1 by omega),
        dif_neg (show k + 4 ≠ 2 by omega),
        dif_neg (show ¬ k + 4 ≤ k + 2 by omega),
        dif_neg (show k + 4 ≠ k + 3 by omega),
        dif_pos rfl]
  | rightLeaf2  =>
    show DTildeVertex.ofFin k ⟨k + 5, by omega⟩ = .rightLeaf2
    unfold DTildeVertex.ofFin
    rw [dif_neg (show k + 5 ≠ 0 by omega),
        dif_neg (show k + 5 ≠ 1 by omega),
        dif_neg (show k + 5 ≠ 2 by omega),
        dif_neg (show ¬ k + 5 ≤ k + 2 by omega),
        dif_neg (show k + 5 ≠ k + 3 by omega),
        dif_neg (show k + 5 ≠ k + 4 by omega)]

/-- The equivalence between `DTildeVertex k` and `Fin (k + 6)`. -/
def DTildeVertex.equivFin (k : ℕ) : DTildeVertex k ≃ Fin (k + 6) where
  toFun := DTildeVertex.toFin
  invFun := DTildeVertex.ofFin k
  left_inv := DTildeVertex.ofFin_toFin k
  right_inv := DTildeVertex.toFin_ofFin k

instance (k : ℕ) : Fintype (DTildeVertex k) := Fintype.ofEquiv _ (DTildeVertex.equivFin k).symm

/-- Dimension of vertex v in the D̃_{k+5} representation:
    vertices 0,1,k+4,k+5 get m+1; interior vertices 2,...,k+3 get 2(m+1). -/
def dTildeDim (k m : ℕ) (v : Fin (k + 6)) : ℕ :=
  if 2 ≤ v.val ∧ v.val ≤ k + 3 then 2 * (m + 1) else m + 1

/-- Bridge: `dTildeDim` computed via the `DTildeVertex` factorization. -/
theorem dTildeDim_eq_ofFin_dim (k m : ℕ) (v : Fin (k + 6)) :
    dTildeDim k m v = (DTildeVertex.ofFin k v).dim m := by
  unfold dTildeDim DTildeVertex.ofFin
  split_ifs <;> first | rfl | (exfalso; omega)

-- Sanity checks: `.dim m` reduces by `rfl` on each constructor.
example (k m : ℕ) : (DTildeVertex.leftLeaf1  : DTildeVertex k).dim m = m + 1 := rfl
example (k m : ℕ) : (DTildeVertex.leftLeaf2  : DTildeVertex k).dim m = m + 1 := rfl
example (k m : ℕ) : (DTildeVertex.branchLeft : DTildeVertex k).dim m = 2 * (m + 1) := rfl
example (k m : ℕ) (i : Fin k) :
    (DTildeVertex.pathMid i : DTildeVertex k).dim m = 2 * (m + 1) := rfl
example (k m : ℕ) : (DTildeVertex.branchRight : DTildeVertex k).dim m = 2 * (m + 1) := rfl
example (k m : ℕ) : (DTildeVertex.rightLeaf1 : DTildeVertex k).dim m = m + 1 := rfl
example (k m : ℕ) : (DTildeVertex.rightLeaf2 : DTildeVertex k).dim m = m + 1 := rfl

/-- The identity map between identical 2(m+1)-dimensional spaces, cast through
    the dimension function. Used for path edges i→(i+1) where both endpoints
    are interior vertices. -/
private noncomputable def dTildePathId (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) :=
  LinearMap.id

/-- Match-based map for the D̃_{k+5} representation. -/
private noncomputable def dTildeRepMap (k m : ℕ) (a b : Fin (k + 6)) :
    (Fin (dTildeDim k m a) → ℂ) →ₗ[ℂ] (Fin (dTildeDim k m b) → ℂ) :=
  if h : a.val = 0 ∧ b.val = 2 then
    have ha : dTildeDim k m a = m + 1 := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ starEmbed1 m
  else if h : a.val = 1 ∧ b.val = 2 then
    have ha : dTildeDim k m a = m + 1 := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ starEmbed2 m
  else if h : a.val = 2 ∧ b.val = 3 then
    have ha : dTildeDim k m a = 2 * (m + 1) := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ d5tildeGamma m
  else if h : 3 ≤ a.val ∧ a.val + 1 = b.val ∧ b.val ≤ k + 3 then
    have ha : dTildeDim k m a = 2 * (m + 1) := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ dTildePathId m
  else if h : a.val = k + 4 ∧ b.val = k + 3 then
    have ha : dTildeDim k m a = m + 1 := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ starEmbed1 m
  else if h : a.val = k + 5 ∧ b.val = k + 3 then
    have ha : dTildeDim k m a = m + 1 := by simp [dTildeDim]; omega
    have hb : dTildeDim k m b = 2 * (m + 1) := by simp [dTildeDim]; omega
    ha ▸ hb ▸ starEmbed2 m
  else
    0

-- The D̃_{k+5} representation with dimension vector δ·(m+1).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def dTildeRep (k m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin (k + 6)) _ (dTildeQuiver k) := by
  letI := dTildeQuiver k
  exact {
    obj := fun v => Fin (dTildeDim k m v) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => dTildeRepMap k m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem dTildeRep_dimVec (k m : ℕ) (v : Fin (k + 6)) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin (k + 6)) _
      (dTildeQuiver k) (dTildeRep k m) v ≃ₗ[ℂ]
      (Fin (dTildeDim k m v) → ℂ)) :=
  ⟨LinearEquiv.refl ℂ _⟩

/-! ## Section 17a.3: Indecomposability of D̃_n representations

The proof follows the same structure as D̃_5:
1. Core argument at each branch point: embed1/embed2 split W into leaf components
2. Gamma coupling forces containment between leaf subspaces
3. Identity maps along the path propagate containment from branch point 2 to k+3
4. By complement equality, all leaf subspaces are equal
5. Nilpotent invariance gives the final contradiction
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
set_option maxHeartbeats 3200000 in
theorem dTildeRep_isIndecomposable (k m : ℕ) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin (k + 6))
      (dTildeQuiver k) (dTildeRep k m) := by
  letI := dTildeQuiver k
  sorry

/-! ## Section 17a.4: D̃_n has infinite representation type -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem dTilde_not_finite_type (k : ℕ) :
    ¬ Etingof.IsFiniteTypeQuiver (k + 6) (dTildeAdj k) := by
  intro hft
  letI := dTildeQuiver k
  have hfin := @hft ℂ _ inferInstance (dTildeQuiver k)
    (fun a b => dTildeQuiver_subsingleton k a b)
    (dTildeOrientation_isOrientationOf k)
  have hmem : ∀ m : ℕ, (dTildeDim k m) ∈
      {d : Fin (k + 6) → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin (k + 6)),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨dTildeRep k m, dTildeRep_isIndecomposable k m, dTildeRep_dimVec k m⟩
  have hinj : Function.Injective (dTildeDim k) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    have : ¬(2 ≤ (⟨0, by omega⟩ : Fin (k + 6)).val ∧
      (⟨0, by omega⟩ : Fin (k + 6)).val ≤ k + 3) := by simp
    simp only [dTildeDim, this, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-- The null root of D̃_{k+5}: δ = (1,1,2,...,2,1,1) with 2's at interior vertices.
    Useful for downstream proofs: (2I - A)δ = 0 witnesses non-positive-definiteness. -/
def dTildeNullRoot (k : ℕ) : Fin (k + 6) → ℤ :=
  fun v => if 2 ≤ v.val ∧ v.val ≤ k + 3 then 2 else 1

theorem dTildeNullRoot_ne_zero (k : ℕ) : dTildeNullRoot k ≠ 0 := by
  intro h
  have := congr_fun h ⟨0, by omega⟩
  simp [dTildeNullRoot] at this

/-! ## Section 17b: Ẽ₆ with mixed orientation (for indecomposability proof)

The sink orientation (all arrows toward center) makes indecomposability proofs hard
because there's no coupling map between arms. We use a mixed orientation:
  2→1→0, 0→3→4, 6→5→0
This makes vertex 0 receive from arms 1 and 3, and send to arm 2,
creating a D̃₅-like structure with a coupling map 0→3. -/

/-- Ẽ₆ quiver with mixed orientation: 2→1→0→3←4, 6→5→0.
    Vertex 0 receives from inner vertices 1 and 5, sends to inner vertex 3.
    Vertex 3 receives from both 0 (via Γ coupling) and 4 (via embedding).
    All maps are injective, ensuring indecomposability via the D̃₅ pattern. -/
def etilde6v2Quiver : Quiver (Fin 7) where
  Hom i j := PLift (
    (i.val = 2 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 0 ∧ j.val = 3) ∨ (i.val = 4 ∧ j.val = 3) ∨
    (i.val = 6 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 0))

instance etilde6v2Quiver_subsingleton (a b : Fin 7) :
    Subsingleton (@Quiver.Hom (Fin 7) etilde6v2Quiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

set_option maxHeartbeats 1600000 in
-- 49 vertex pairs for orientation compatibility, proved by fin_cases enumeration
theorem etilde6v2Orientation_isOrientationOf :
    @Etingof.IsOrientationOf 7 etilde6v2Quiver etilde6Adj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · -- Non-edges have no arrows
    constructor; intro ⟨hp⟩
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp_all [etilde6Adj]
  · -- Each edge has an arrow in one direction
    fin_cases i <;> fin_cases j <;> simp_all [etilde6Adj, etilde6v2Quiver] <;>
      first | left; exact ⟨⟨by omega⟩⟩ | right; exact ⟨⟨by omega⟩⟩
  · -- No two-way arrows
    obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
         omega)

/-- The coupling map Γ: ℂ^{3(m+1)} → ℂ^{2(m+1)} for Ẽ₆ mixed orientation.
    Γ(a, b, c) = (a + b, a + Nc) where a,b,c are blocks of size (m+1) and N is nilpotent shift.
    This mirrors D̃₅'s γ = [[I,I],[I,N]] but operates on 3 input blocks instead of 2. -/
noncomputable def etilde6v2Gamma (m : ℕ) :
    (Fin (3 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 1)) → ℂ) where
  toFun w i :=
    if h : i.val < m + 1 then
      -- First block of output: a + b = w_i + w_{m+1+i}
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else
      -- Second block of output: a + Nc = w_{i-(m+1)} + N(c)_{i-(m+1)}
      let j := i.val - (m + 1)
      w ⟨j, by omega⟩ +
        (if h2 : j + 1 < m + 1 then w ⟨2 * (m + 1) + j + 1, by omega⟩ else 0)
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- The representation map for Ẽ₆ with mixed orientation. -/
private noncomputable def etilde6v2RepMap (m : ℕ) (a b : Fin 7) :
    (Fin (etilde6Dim m a) → ℂ) →ₗ[ℂ] (Fin (etilde6Dim m b) → ℂ) :=
  match a, b with
  -- Arm 1 (toward center): 2→1→0
  | ⟨2, _⟩, ⟨1, _⟩ => starEmbed1 m      -- x ↦ (x, 0)
  | ⟨1, _⟩, ⟨0, _⟩ => embed2to3_AB m    -- (a,b) ↦ (a, b, 0)
  -- Arm 2 (toward vertex 3): 0→3←4
  | ⟨0, _⟩, ⟨3, _⟩ => etilde6v2Gamma m  -- Γ(a,b,c) = (a+b, a+Nc)
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1 m      -- x ↦ (x, 0)
  -- Arm 3 (toward center): 6→5→0
  | ⟨6, _⟩, ⟨5, _⟩ => starEmbedNilp m   -- x ↦ (x, Nx)
  | ⟨5, _⟩, ⟨0, _⟩ => embed2to3_CA m    -- (a,b) ↦ (b, 0, a)
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def etilde6v2Rep (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin 7) _ etilde6v2Quiver := by
  letI := etilde6v2Quiver
  exact {
    obj := fun v => Fin (etilde6Dim m v) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => etilde6v2RepMap m a b
  }

/-! The indecomposability proof follows the D̃₅ pattern:
1. Vertex 0 (dim 3(m+1)) receives from arms 1 and 3:
   - embed2to3_AB maps from inner 1: (a,b) ↦ (a,b,0), covering blocks A,B
   - embed2to3_CA maps from inner 5: (a,b) ↦ (b,0,a), covering blocks A,C
2. Vertex 3 (dim 2(m+1)) receives from vertex 0 (via Γ) and vertex 4 (via starEmbed1):
   - Γ(a,b,c) = (a+b, a+Nc) couples blocks A,B,C to both blocks of vertex 3
   - starEmbed1 embeds tip 4 into first block of vertex 3
3. From tip 2: x ∈ W(2) → (x,0,0) ∈ W(0) → Γ(x,0,0) = (x,x) ∈ W(3)
   So W(2) ⊆ both blocks of W(3), hence W(2) ⊆ W(4) (both in first block)
4. From tip 6: x ∈ W(6) → (x,Nx) ∈ W(5) → (Nx,0,x) ∈ W(0) → Γ(Nx,0,x) = (Nx, Nx+Nx) ∈ W(3)
   Combined with N-coupling: forces N-invariance of common leaf subspace
5. nilpotent_invariant_compl_trivial concludes -/

-- For now, sorry the indecomposability; we only need the infinite type theorem.
-- NOTE: The hypothesis `1 ≤ m` is required. For `m = 0`, `nilpotentShiftLin 0 = 0`
-- (since `i.val + 1 < 1` is unsatisfiable for `i : Fin 1`), so the nilpotent twist
-- disappears and the representation is provably decomposable. An explicit
-- complementary invariant pair is: W₁(0) = {(a,b,0)}, W₂(0) = {(0,0,c)}, with
-- W₁(1)=W₁(3)=W₁(5)=full, W₁(2)=W₁(4)=full, W₁(6)=0, W₂ the complements.
-- For m ≥ 1, the nilpotent twist `N ≠ 0` breaks this decomposition at vertex 6,
-- forcing the argument through via `nilpotent_invariant_compl_trivial`.
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde6v2Rep_isIndecomposable (m : ℕ) (hm : 1 ≤ m) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 7)
      etilde6v2Quiver (etilde6v2Rep m) := by
  letI := etilde6v2Quiver
  constructor
  · refine ⟨⟨2, by omega⟩, ?_⟩
    change Nontrivial (Fin (etilde6Dim m ⟨2, by omega⟩) → ℂ)
    show Nontrivial (Fin (m + 1) → ℂ)
    infer_instance
  · -- Indecomposability
    intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Edge structure: 2→1→0→3←4, 6→5→0
    -- Maps: 2→1: starEmbed1, 1→0: embed2to3_AB, 0→3: etilde6v2Gamma,
    --       4→3: starEmbed1, 6→5: starEmbedNilp, 5→0: embed2to3_CA
    --
    -- Arrow constructors for each edge
    have hom21 : @Quiver.Hom _ etilde6v2Quiver ⟨2, by omega⟩ ⟨1, by omega⟩ :=
      ⟨Or.inl ⟨rfl, rfl⟩⟩
    have hom10 : @Quiver.Hom _ etilde6v2Quiver ⟨1, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    have hom03 : @Quiver.Hom _ etilde6v2Quiver ⟨0, by omega⟩ ⟨3, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    have hom43 : @Quiver.Hom _ etilde6v2Quiver ⟨4, by omega⟩ ⟨3, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    have hom65 : @Quiver.Hom _ etilde6v2Quiver ⟨6, by omega⟩ ⟨5, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    have hom50 : @Quiver.Hom _ etilde6v2Quiver ⟨5, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩
    -- NOTE: Helper lemmas for leaf containment are pushed into `leaf24_containment`
    -- below (sub-sorry). The key facts used there are:
    -- * Γ(embed2to3_AB(starEmbed1(x))) = (x, x) [diagonal embedding, leaf 2 via arm 1]
    -- * Γ(embed2to3_CA(starEmbedNilp(x))) = (Nx, 2Nx) [leaf 6 via arm 3]
    -- * starEmbed1(y) = (y, 0) directly at vertex 3 [leaf 4]
    -- Helper: if A ≤ B, A' ≤ B', IsCompl A A', IsCompl B B', then A = B
    have compl_eq_of_le (A B A' B' : Submodule ℂ (Fin (m + 1) → ℂ))
        (hAB : A ≤ B) (hA'B' : A' ≤ B')
        (hcA : IsCompl A A') (hcB : IsCompl B B') : A = B := by
      apply le_antisymm hAB; intro x hx
      have hx_top := hcA.sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx_top
      have ha'_B : a' ∈ B := by
        have h := B.sub_mem hx (hAB ha); rwa [show a + a' - a = a' from by abel] at h
      have : a' ∈ B ⊓ B' := Submodule.mem_inf.mpr ⟨ha'_B, hA'B' ha'⟩
      rw [hcB.inf_eq_bot, Submodule.mem_bot] at this; rwa [this, add_zero]
    -- KEY SORRY: W(2) ⊆ W(4) as subspaces of ℂ^{m+1}.
    -- Proof sketch: For x ∈ W(2), (x, x) ∈ W(3). Decompose x = a + b at W(4):
    -- a ∈ W(4), b ∈ W'(4). Then (a, 0) ∈ W(3), (b, 0) ∈ W'(3). The combined
    -- constraints at vertex 3 combined with the leaf-6 (Nz, 2Nz) structure
    -- force b = 0. The key extra ingredient is the m ≥ 1 nilpotent coupling
    -- from leaf 6 making leaf 2 and leaf 4 N-interact.
    have leaf24_containment (W W' : ∀ v, Submodule ℂ ((etilde6v2Rep m).obj v))
        (_hW : ∀ {a b : Fin 7} (e : @Quiver.Hom _ etilde6v2Quiver a b),
          ∀ x ∈ W a, (etilde6v2Rep m).mapLinear e x ∈ W b)
        (_hW' : ∀ {a b : Fin 7} (e : @Quiver.Hom _ etilde6v2Quiver a b),
          ∀ x ∈ W' a, (etilde6v2Rep m).mapLinear e x ∈ W' b)
        (_hc : ∀ v, IsCompl (W v) (W' v)) :
        ∀ x : Fin (m + 1) → ℂ, x ∈ W (2 : Fin 7) → x ∈ W (4 : Fin 7) := by
      sorry
    -- W₁(2) = W₁(4) and W₂(2) = W₂(4) via compl_eq_of_le
    have heq24 : W₁ (2 : Fin 7) = W₁ (4 : Fin 7) := compl_eq_of_le _ _ _ _
      (leaf24_containment W₁ W₂ hW₁_inv hW₂_inv hcompl)
      (leaf24_containment W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm))
      (hcompl (2 : Fin 7)) (hcompl (4 : Fin 7))
    have heq24' : W₂ (2 : Fin 7) = W₂ (4 : Fin 7) := compl_eq_of_le _ _ _ _
      (leaf24_containment W₂ W₁ hW₂_inv hW₁_inv (fun v => (hcompl v).symm))
      (leaf24_containment W₁ W₂ hW₁_inv hW₂_inv hcompl)
      ((hcompl (2 : Fin 7)).symm) ((hcompl (4 : Fin 7)).symm)
    -- KEY SORRY: N-invariance of W₁(2) and W₂(2).
    -- Proof sketch: From leaf 6: z ∈ W(6) → (Nz, 2Nz) ∈ W(3). Combined with
    -- the equality W(2) = W(4) and the (x, x) ∈ W(3) structure from leaf 2,
    -- the nilpotent action propagates through the center and forces N to
    -- preserve the common leaf subspace.
    have hN₁ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₁ (2 : Fin 7) → nilpotentShiftLin m x ∈ W₁ (2 : Fin 7) := by
      sorry
    have hN₂ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₂ (2 : Fin 7) → nilpotentShiftLin m x ∈ W₂ (2 : Fin 7) := by
      sorry
    -- Apply nilpotent_invariant_compl_trivial at vertex 2
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ (2 : Fin 7)) (W₂ (2 : Fin 7)) hN₁ hN₂ (hcompl (2 : Fin 7))
    -- Propagation: W(2) = ⊥ → W(0) = ⊥ → all W(v) = ⊥
    suffices propagate : ∀ (W W' : ∀ v, Submodule ℂ ((etilde6v2Rep m).obj v)),
        (∀ {a b : Fin 7} (e : @Quiver.Hom _ etilde6v2Quiver a b),
          ∀ x ∈ W a, (etilde6v2Rep m).mapLinear e x ∈ W b) →
        (∀ {a b : Fin 7} (e : @Quiver.Hom _ etilde6v2Quiver a b),
          ∀ x ∈ W' a, (etilde6v2Rep m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W (2 : Fin 7) = W (4 : Fin 7) →
        W (2 : Fin 7) = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₁_inv hW₂_inv hcompl heq24 h
      · right; exact propagate W₂ W₁ hW₂_inv hW₁_inv
          (fun v => (hcompl v).symm) heq24' h
    intro W W' hW_inv hW'_inv hc h24 hbot v
    -- KEY SORRY: hbot0 — Show W(0) = ⊥.
    -- Proof sketch: W(2) = W(4) = ⊥, so W'(2) = W'(4) = ⊤.
    -- Via arm chains: starEmbed1(ℂ^{m+1}) ⊆ W'(1), then (ℂ^{m+1}, 0) ⊆ W'(1).
    -- By similar logic for arm 3 (using m ≥ 1 for Nilp injectivity), W(5) = ⊥
    -- is also forced. Then the W'(0) structure fills all blocks via the two
    -- arm embeddings, forcing W(0) = ⊥.
    have hbot0 : W (0 : Fin 7) = ⊥ := by sorry
    -- Propagate from W(0) = ⊥ and W(2) = ⊥ to all vertices via injectivity.
    -- Helper: if an injective arrow e:a→b with W(b) = ⊥, then W(a) = ⊥.
    have prop_inj {a b : Fin 7} (e : @Quiver.Hom _ etilde6v2Quiver a b)
        (hinj : ∀ x : (etilde6v2Rep m).obj a, (etilde6v2Rep m).mapLinear e x = 0 → x = 0)
        (htarget : W b = ⊥) : W a = ⊥ := by
      rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]
      have := hW_inv e x hx; rw [htarget, Submodule.mem_bot] at this
      exact hinj x this
    -- Injectivity of starEmbed1: x ↦ (x, 0)
    have inj_starEmbed1 : ∀ x : Fin (m + 1) → ℂ, starEmbed1 m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [starEmbed1, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj, Pi.zero_apply] at this
      exact this
    -- Injectivity of starEmbedNilp is actually not needed: we propagate W(6)=⊥ differently.
    -- Injectivity of embed2to3_AB: (x, y) ↦ (x, y, 0)
    have inj_embed2to3_AB : ∀ x : Fin (2 * (m + 1)) → ℂ, embed2to3_AB m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embed2to3_AB, LinearMap.coe_mk, AddHom.coe_mk,
        dif_pos (show j < 2 * (m + 1) from hj), Pi.zero_apply] at this
      exact this
    -- Injectivity of embed2to3_CA: (a, b) ↦ (b, 0, a).
    -- Input index j < m+1 (first m+1-block, "a"): output at position 2(m+1)+j (block C).
    -- Input index j ≥ m+1 (second m+1-block, "b"): output at position j-(m+1) (block A).
    have inj_embed2to3_CA : ∀ x : Fin (2 * (m + 1)) → ℂ, embed2to3_CA m x = 0 → x = 0 := by
      intro x h
      funext ⟨j, hj⟩
      show x ⟨j, hj⟩ = 0
      by_cases hjlt : j < m + 1
      · -- Read output position 2(m+1)+j to extract input position j (block C)
        have hc := congr_fun h ⟨2 * (m + 1) + j, by omega⟩
        simp only [embed2to3_CA, LinearMap.coe_mk, AddHom.coe_mk,
          dif_neg (show ¬(2 * (m + 1) + j < m + 1) from by omega),
          dif_pos (show 2 * (m + 1) ≤ 2 * (m + 1) + j from by omega),
          dif_pos (show 2 * (m + 1) + j - 2 * (m + 1) < m + 1 from by omega),
          Pi.zero_apply] at hc
        have heq : (⟨2 * (m + 1) + j - 2 * (m + 1), by omega⟩ : Fin (2 * (m + 1))) =
            ⟨j, hj⟩ := by
          apply Fin.ext
          show 2 * (m + 1) + j - 2 * (m + 1) = j
          omega
        exact heq ▸ hc
      · -- Read output position j-(m+1) to extract input position j (block A)
        push_neg at hjlt
        have hc := congr_fun h ⟨j - (m + 1), by omega⟩
        simp only [embed2to3_CA, LinearMap.coe_mk, AddHom.coe_mk,
          dif_pos (show j - (m + 1) < m + 1 from by omega), Pi.zero_apply] at hc
        have heq : (⟨j - (m + 1) + (m + 1), by omega⟩ : Fin (2 * (m + 1))) =
            ⟨j, hj⟩ := by
          apply Fin.ext
          show j - (m + 1) + (m + 1) = j
          omega
        exact heq ▸ hc
    -- Injectivity of starEmbedNilp: x ↦ (x, Nx). Injective since first block is x.
    have inj_starEmbedNilp : ∀ x : Fin (m + 1) → ℂ, starEmbedNilp m x = 0 → x = 0 := by
      intro x h; ext ⟨i, hi⟩
      have := congr_fun h ⟨i, by omega⟩
      simp only [starEmbedNilp, starEmbed1, starEmbed2, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
        Pi.zero_apply, dif_pos hi,
        dif_neg (show ¬(m + 1 ≤ i) from by omega), add_zero] at this
      exact this
    -- Chain: W(0) = ⊥ → W(1) = ⊥, W(5) = ⊥; W(5) = ⊥ → W(6) = ⊥.
    -- W(2) and W(4) from hypothesis and h24.
    have hbot1 : W (1 : Fin 7) = ⊥ := prop_inj hom10 inj_embed2to3_AB hbot0
    have hbot5 : W (5 : Fin 7) = ⊥ := prop_inj hom50 inj_embed2to3_CA hbot0
    have hbot2 : W (2 : Fin 7) = ⊥ := hbot
    have hbot4 : W (4 : Fin 7) = ⊥ := h24 ▸ hbot
    have hbot6 : W (6 : Fin 7) = ⊥ := prop_inj hom65 inj_starEmbedNilp hbot5
    -- W(3) propagation: Γ is surjective, so W'(0) = ⊤ → W'(3) = ⊤ → W(3) = ⊥.
    -- Proof of surjectivity: given (u, v) ∈ V(3), the preimage (v, u-v, 0) ∈ V(0)
    -- satisfies Γ(v, u-v, 0) = (v + (u-v), v + N·0) = (u, v).
    have hbot3 : W (3 : Fin 7) = ⊥ := by
      -- Step 1: W'(0) = ⊤ from W(0) = ⊥ and the complement structure.
      have hWtop0 : W' (0 : Fin 7) = ⊤ := by
        have := (hc (0 : Fin 7)).sup_eq_top
        rwa [hbot0, bot_sup_eq] at this
      -- Step 2a: surjectivity of Γ on the explicit type.
      -- Preimage of (u, v) (where u = first half of y, v = second half) is (v, u - v, 0).
      have hΓ_surj : ∀ y : Fin (2 * (m + 1)) → ℂ,
          ∃ z : Fin (3 * (m + 1)) → ℂ, etilde6v2Gamma m z = y := by
        intro y
        let z : Fin (3 * (m + 1)) → ℂ := fun i =>
          if h1 : i.val < m + 1 then y ⟨m + 1 + i.val, by omega⟩
          else if h2 : i.val < 2 * (m + 1) then
            y ⟨i.val - (m + 1), by omega⟩ - y ⟨i.val, by omega⟩
          else 0
        -- Three accessors for the three blocks of z.
        have z_a : ∀ (k : ℕ) (hk_bound : k < 3 * (m + 1)) (hk : k < m + 1),
            z ⟨k, hk_bound⟩ = y ⟨m + 1 + k, by omega⟩ := by
          intros k _ hk
          show (if h1 : k < m + 1 then y ⟨m + 1 + k, by omega⟩
              else if h2 : k < 2 * (m + 1) then
                y ⟨k - (m + 1), by omega⟩ - y ⟨k, by omega⟩
              else 0) = y ⟨m + 1 + k, by omega⟩
          rw [dif_pos hk]
        have z_b : ∀ (k : ℕ) (hk_bound : k < 3 * (m + 1))
            (hk1 : ¬ k < m + 1) (hk2 : k < 2 * (m + 1)),
            z ⟨k, hk_bound⟩ = y ⟨k - (m + 1), by omega⟩ - y ⟨k, by omega⟩ := by
          intros k _ hk1 hk2
          show (if h1 : k < m + 1 then y ⟨m + 1 + k, by omega⟩
              else if h2 : k < 2 * (m + 1) then
                y ⟨k - (m + 1), by omega⟩ - y ⟨k, by omega⟩
              else 0) = y ⟨k - (m + 1), by omega⟩ - y ⟨k, by omega⟩
          rw [dif_neg hk1, dif_pos hk2]
        have z_c : ∀ (k : ℕ) (hk_bound : k < 3 * (m + 1))
            (hk1 : ¬ k < m + 1) (hk2 : ¬ k < 2 * (m + 1)),
            z ⟨k, hk_bound⟩ = 0 := by
          intros k _ hk1 hk2
          show (if h1 : k < m + 1 then y ⟨m + 1 + k, by omega⟩
              else if h2 : k < 2 * (m + 1) then
                y ⟨k - (m + 1), by omega⟩ - y ⟨k, by omega⟩
              else 0) = 0
          rw [dif_neg hk1, dif_neg hk2]
        refine ⟨z, ?_⟩
        ext ⟨i, hi⟩
        simp only [etilde6v2Gamma, LinearMap.coe_mk, AddHom.coe_mk]
        by_cases hilt : i < m + 1
        · -- First block of Γ output at index i: z ⟨i⟩ + z ⟨m+1+i⟩.
          rw [dif_pos hilt,
            z_a i (by omega) hilt,
            z_b (m + 1 + i) (by omega) (by omega) (by omega)]
          have h_idx : (⟨m + 1 + i - (m + 1), by omega⟩ : Fin (2 * (m + 1))) =
              ⟨i, hi⟩ := by apply Fin.ext; change m + 1 + i - (m + 1) = i; omega
          rw [h_idx]; ring
        · -- Second block of Γ output at index i (i ≥ m+1).
          push_neg at hilt
          rw [dif_neg (show ¬(i < m + 1) from by omega),
            z_a (i - (m + 1)) (by omega) (by omega)]
          have h_idx : (⟨m + 1 + (i - (m + 1)), by omega⟩ : Fin (2 * (m + 1))) =
              ⟨i, hi⟩ := by
            apply Fin.ext; change m + 1 + (i - (m + 1)) = i; omega
          rw [h_idx]
          split_ifs with h2
          · -- z at index 2(m+1) + (i-(m+1)) + 1 is in c-block, so equals 0.
            rw [z_c (2 * (m + 1) + (i - (m + 1)) + 1) (by omega) (by omega) (by omega)]
            ring
          · ring
      -- Step 2b: W'(3) = ⊤.
      have hWtop3 : W' (3 : Fin 7) = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro y
        obtain ⟨z, hz⟩ := hΓ_surj y
        have hz0 : z ∈ W' (0 : Fin 7) := hWtop0 ▸ Submodule.mem_top
        have hgz : (etilde6v2Rep m).mapLinear hom03 z ∈ W' (3 : Fin 7) :=
          hW'_inv hom03 z hz0
        have heq : (etilde6v2Rep m).mapLinear hom03 z = y := hz
        rw [← heq]; exact hgz
      -- Step 3: W(3) ⊓ W'(3) = ⊥, W'(3) = ⊤ ⇒ W(3) = ⊥.
      have h_inf := (hc (3 : Fin 7)).inf_eq_bot
      rwa [hWtop3, inf_top_eq] at h_inf
    fin_cases v
    · exact hbot0  -- v = 0
    · exact hbot1  -- v = 1
    · exact hbot2  -- v = 2
    · exact hbot3  -- v = 3
    · exact hbot4  -- v = 4
    · exact hbot5  -- v = 5
    · exact hbot6  -- v = 6

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde6v2Rep_dimVec (m : ℕ) (v : Fin 7) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin 7) _
      etilde6v2Quiver (etilde6v2Rep m) v ≃ₗ[ℂ]
      (Fin (etilde6Dim m v) → ℂ)) :=
  ⟨LinearEquiv.refl ℂ _⟩

theorem etilde6_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 7 etilde6Adj := by
  intro hft
  letI := etilde6v2Quiver
  have hfin := @hft ℂ _ inferInstance etilde6v2Quiver
    (fun a b => etilde6v2Quiver_subsingleton a b)
    etilde6v2Orientation_isOrientationOf
  -- We range over `m + 1` (not `m`) because `etilde6v2Rep_isIndecomposable`
  -- requires `1 ≤ m`: the `m = 0` case is provably decomposable.
  -- Shifting gives an infinite family of indecomposables with distinct dim vectors.
  have hmem : ∀ m : ℕ, (fun v : Fin 7 => etilde6Dim (m + 1) v) ∈
      {d : Fin 7 → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin 7),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨etilde6v2Rep (m + 1),
      etilde6v2Rep_isIndecomposable (m + 1) (Nat.succ_le_succ m.zero_le),
      etilde6v2Rep_dimVec (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 7 => etilde6Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    simp only [etilde6Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 17: Ẽ_8 has infinite representation type via subgraph embedding

The graph T_{2,3,5} (our "Ẽ_8") contains T_{2,2,2} (Ẽ_6) as a subgraph.
Embedding: φ maps 0→0, 1→1, 2→2, 3→3, 4→4, 5→6, 6→7.
Arms of Ẽ_6 (lengths 2,2,2) embed into the first two edges of each arm of T_{2,3,5}. -/

/-- Embedding of Ẽ_6 (7 vertices) into Ẽ_8 (11 vertices).
Maps: 0→0, 1→1, 2→2, 3→3, 4→4, 5→6, 6→7. -/
def etilde6_to_etilde8_fun : Fin 7 → Fin 11
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨6, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩

private theorem etilde6_to_etilde8_injective : Function.Injective etilde6_to_etilde8_fun := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [etilde6_to_etilde8_fun]

def etilde6_to_etilde8 : Fin 7 ↪ Fin 11 :=
  ⟨etilde6_to_etilde8_fun, etilde6_to_etilde8_injective⟩

-- Ẽ_6 has 7 vertices; fin_cases creates 49 goals for adjacency compatibility
set_option maxHeartbeats 3200000 in
private theorem etilde6_etilde8_adj_compat :
    ∀ i j : Fin 7, etilde6Adj i j = etilde8Adj (etilde6_to_etilde8 i) (etilde6_to_etilde8 j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [etilde6Adj, etilde8Adj, etilde6_to_etilde8,
    etilde6_to_etilde8_fun]

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The extended Dynkin graph T_{2,3,5} (our "Ẽ_8") has infinite representation type.
This follows because it contains Ẽ_6 = T_{2,2,2} as a subgraph, which itself has
infinite representation type. -/
theorem etilde8_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 11 etilde8Adj :=
  subgraph_infinite_type_transfer etilde6_to_etilde8 etilde8Adj etilde6Adj
    etilde8Adj_symm
    (fun v h => by linarith [etilde8Adj_diag v])
    etilde6_etilde8_adj_compat
    etilde6_not_finite_type

/-! ## Section 19: Ẽ₇ = T_{1,3,3} has infinite representation type

The graph T_{1,3,3} has 8 vertices: center (0) with arms of length 1, 3, 3.
- Arm 1 (length 1): 0-1
- Arm 2 (length 3): 0-2-3-4
- Arm 3 (length 3): 0-5-6-7

The null root is δ = (4, 2, 3, 2, 1, 3, 2, 1).
-/

/-- Adjacency matrix for Ẽ₇ = T_{1,3,3} (8 vertices). -/
def etilde7Adj : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0
  | 0, 2 | 2, 0 | 2, 3 | 3, 2 | 3, 4 | 4, 3
  | 0, 5 | 5, 0 | 5, 6 | 6, 5 | 6, 7 | 7, 6 => 1
  | _, _ => 0

theorem etilde7Adj_symm : etilde7Adj.IsSymm := by
  ext i j; simp only [etilde7Adj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem etilde7Adj_diag (i : Fin 8) : etilde7Adj i i = 0 := by
  fin_cases i <;> simp [etilde7Adj]

theorem etilde7Adj_01 (i j : Fin 8) : etilde7Adj i j = 0 ∨ etilde7Adj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [etilde7Adj]

/-- The Ẽ₇ quiver: all arrows directed toward the center (vertex 0).
Arrows: 1→0, 4→3, 3→2, 2→0, 7→6, 6→5, 5→0. -/
def etilde7Quiver : Quiver (Fin 8) where
  Hom i j := PLift (
    (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 4 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
    (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 0))

instance etilde7Quiver_subsingleton (a b : Fin 8) :
    Subsingleton (@Quiver.Hom (Fin 8) etilde7Quiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem etilde7_arrow_implies_edge (i j : Fin 8)
    (hp : (i.val = 1 ∧ j.val = 0) ∨
      (i.val = 4 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
      (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 0)) :
    etilde7Adj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [etilde7Adj, h1, h2]

-- Ẽ₇ has 8 vertices; fin_cases creates 64 goals for adjacency
set_option maxHeartbeats 1600000 in
private theorem etilde7_edge_has_arrow (i j : Fin 8) (hij : etilde7Adj i j = 1) :
    Nonempty (@Quiver.Hom (Fin 8) etilde7Quiver i j) ∨
    Nonempty (@Quiver.Hom (Fin 8) etilde7Quiver j i) := by
  fin_cases i <;> fin_cases j <;> simp [etilde7Adj] at hij <;>
    first
    | (left; exact ⟨⟨by decide⟩⟩)
    | (right; exact ⟨⟨by decide⟩⟩)

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde7Orientation_isOrientationOf :
    @Etingof.IsOrientationOf 8 etilde7Quiver etilde7Adj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · constructor; intro ⟨hp⟩; exact hij (etilde7_arrow_implies_edge i j hp)
  · exact etilde7_edge_has_arrow i j hij
  · obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        omega

/-- Dimension of vertex v in the Ẽ₇ representation (null root multiples):
    v0: 4(m+1), v1: 2(m+1), v2: 3(m+1), v3: 2(m+1), v4: m+1,
    v5: 3(m+1), v6: 2(m+1), v7: m+1. -/
def etilde7Dim (m : ℕ) (v : Fin 8) : ℕ :=
  match v.val with
  | 0 => 4 * (m + 1)
  | 1 | 3 | 6 => 2 * (m + 1)
  | 2 | 5 => 3 * (m + 1)
  | _ => m + 1  -- vertices 4, 7

/-- Embedding ℂ^{3(m+1)} into first 3 blocks of ℂ^{4(m+1)}: (x,y,z) ↦ (x,y,z,0). -/
noncomputable def embed3to4_ABC (m : ℕ) :
    (Fin (3 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (4 * (m + 1)) → ℂ) where
  toFun x i := if h : i.val < 3 * (m + 1) then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Embedding ℂ^{3(m+1)} into blocks A,C,D of ℂ^{4(m+1)}: (x,y,z) ↦ (x,0,y,z). -/
noncomputable def embed3to4_ACD (m : ℕ) :
    (Fin (3 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (4 * (m + 1)) → ℂ) where
  toFun x i :=
    if h : i.val < m + 1 then
      -- Block A: first component of input
      x ⟨i.val, by omega⟩
    else if h2 : m + 1 ≤ i.val ∧ i.val < 2 * (m + 1) then
      -- Block B: zero
      0
    else if h3 : i.val < 4 * (m + 1) then
      -- Blocks C,D: shift input by -(m+1) to get components 2,3 of input
      x ⟨i.val - (m + 1), by omega⟩
    else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Ẽ₇ arm 1 embedding ℂ^{2(m+1)} into ℂ^{4(m+1)}: (p,q) ↦ (p+q, p, q, Nq).
    Couples all four blocks and introduces nilpotent twist in block D. -/
noncomputable def etilde7Arm1Embed (m : ℕ) :
    (Fin (2 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (4 * (m + 1)) → ℂ) where
  toFun w i :=
    if h : i.val < m + 1 then
      -- Block A: p + q = w_i + w_{m+1+i}
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else if h2 : i.val < 2 * (m + 1) then
      -- Block B: p = w_{i-(m+1)} (first component)
      w ⟨i.val - (m + 1), by omega⟩
    else if h3 : i.val < 3 * (m + 1) then
      -- Block C: q = w_{m+1+(i-2(m+1))} (second component)
      w ⟨m + 1 + (i.val - 2 * (m + 1)), by omega⟩
    else
      -- Block D: Nq = nilpotentShift applied to second component
      let j := i.val - 3 * (m + 1)
      if h4 : j + 1 < m + 1 then w ⟨m + 1 + j + 1, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Match-based map for the Ẽ₇ representation.
    Arm 1: 1→0 via nilpotent-coupled embedding
    Arm 2: 4→3→2→0 via identity chain + first-3-blocks embedding
    Arm 3: 7→6→5→0 via identity chain + blocks-ACD embedding -/
private noncomputable def etilde7RepMap (m : ℕ) (a b : Fin 8) :
    (Fin (etilde7Dim m a) → ℂ) →ₗ[ℂ] (Fin (etilde7Dim m b) → ℂ) :=
  match a, b with
  -- Arm 1: 1→0
  | ⟨1, _⟩, ⟨0, _⟩ => etilde7Arm1Embed m
  -- Arm 2: 4→3→2→0 (chain toward center via first blocks)
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1 m          -- x ↦ (x, 0)
  | ⟨3, _⟩, ⟨2, _⟩ => embed2to3_AB m        -- (x,y) ↦ (x, y, 0)
  | ⟨2, _⟩, ⟨0, _⟩ => embed3to4_ABC m       -- (x,y,z) ↦ (x, y, z, 0)
  -- Arm 3: 7→6→5→0 (chain via blocks A,C,D)
  | ⟨7, _⟩, ⟨6, _⟩ => starEmbed1 m          -- x ↦ (x, 0)
  | ⟨6, _⟩, ⟨5, _⟩ => embed2to3_AB m        -- (x,y) ↦ (x, y, 0)
  | ⟨5, _⟩, ⟨0, _⟩ => embed3to4_ACD m       -- (x,y,z) ↦ (x, 0, y, z)
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def etilde7Rep (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin 8) _ etilde7Quiver := by
  letI := etilde7Quiver
  exact {
    obj := fun v => Fin (etilde7Dim m v) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => etilde7RepMap m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde7Rep_isIndecomposable (m : ℕ) (hm : 1 ≤ m) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 8)
      etilde7Quiver (etilde7Rep m) := by
  letI := etilde7Quiver
  constructor
  · -- Nontrivial at vertex 4 (dim m+1 ≥ 1)
    refine ⟨⟨4, by omega⟩, ?_⟩
    show Nontrivial (Fin (etilde7Dim m ⟨4, by omega⟩) → ℂ)
    simp only [etilde7Dim]
    infer_instance
  · -- Indecomposability
    intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Helper: Quiver.Hom constructors for each arrow
    have hom10 : @Quiver.Hom _ etilde7Quiver ⟨1, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inl ⟨rfl, rfl⟩⟩
    have hom43 : @Quiver.Hom _ etilde7Quiver ⟨4, by omega⟩ ⟨3, by omega⟩ :=
      ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    have hom32 : @Quiver.Hom _ etilde7Quiver ⟨3, by omega⟩ ⟨2, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    have hom20 : @Quiver.Hom _ etilde7Quiver ⟨2, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    have hom76 : @Quiver.Hom _ etilde7Quiver ⟨7, by omega⟩ ⟨6, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    have hom65 : @Quiver.Hom _ etilde7Quiver ⟨6, by omega⟩ ⟨5, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    have hom50 : @Quiver.Hom _ etilde7Quiver ⟨5, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩
    -- Arm chain helpers: push x ∈ W(leaf) to center via invariance
    have arm2_to_center (W : ∀ v, Submodule ℂ ((etilde7Rep m).obj v))
        (hW : ∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W a, (etilde7Rep m).mapLinear e x ∈ W b)
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W (4 : Fin 8)) :
        (etilde7Rep m).mapLinear hom20 ((etilde7Rep m).mapLinear hom32
          ((etilde7Rep m).mapLinear hom43 x)) ∈ W (0 : Fin 8) :=
      hW hom20 _ (hW hom32 _ (hW hom43 x hx))
    have arm3_to_center (W : ∀ v, Submodule ℂ ((etilde7Rep m).obj v))
        (hW : ∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W a, (etilde7Rep m).mapLinear e x ∈ W b)
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W (7 : Fin 8)) :
        (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
          ((etilde7Rep m).mapLinear hom76 x)) ∈ W (0 : Fin 8) :=
      hW hom50 _ (hW hom65 _ (hW hom76 x hx))
    -- Both arm chains produce the same element (x,0,0,0) at the center
    have arms_agree : ∀ x : Fin (m + 1) → ℂ,
        (etilde7Rep m).mapLinear hom20 ((etilde7Rep m).mapLinear hom32
          ((etilde7Rep m).mapLinear hom43 x)) =
        (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
          ((etilde7Rep m).mapLinear hom76 x)) := by
      intro x
      show embed3to4_ABC m (embed2to3_AB m (starEmbed1 m x)) =
           embed3to4_ACD m (embed2to3_AB m (starEmbed1 m x))
      -- Intermediate: embed2to3_AB ∘ starEmbed1 has zero in blocks B, C
      -- so embed3to4_ABC and embed3to4_ACD agree (only block A is nonzero)
      have key : ∀ (j : Fin (3 * (m + 1))),
          ¬ (j.val < m + 1) → embed2to3_AB m (starEmbed1 m x) j = 0 := by
        intro ⟨j, hj⟩ hjlt
        simp only [embed2to3_AB, starEmbed1, LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
      ext ⟨i, hi⟩
      simp only [embed3to4_ABC, embed3to4_ACD, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases h1 : i < m + 1
      · -- Block A: both select the same element from the intermediate space
        rw [dif_pos (show i < 3 * (m + 1) by omega), dif_pos h1]
      · rw [dif_neg h1]
        by_cases h2 : m + 1 ≤ i ∧ i < 2 * (m + 1)
        · -- Block B: ABC gives intermediate[i] = 0, ACD gives 0
          rw [dif_pos (show i < 3 * (m + 1) by omega), dif_pos h2]
          exact key ⟨i, by omega⟩ h1
        · rw [dif_neg h2]
          by_cases h3 : i < 4 * (m + 1)
          · -- Blocks C/D: ACD gives intermediate[i-(m+1)] = 0
            rw [dif_pos h3]
            have hj : ¬ (i - (m + 1) < m + 1) := by omega
            rw [key ⟨i - (m + 1), by omega⟩ hj]
            by_cases h4 : i < 3 * (m + 1)
            · rw [dif_pos h4]; exact key ⟨i, by omega⟩ h1
            · rw [dif_neg h4]
          · omega
    -- Leaf containment: W(4) ≤ W(7) via the center
    -- If x ∈ W(4), arm2 gives E ∈ W(0). Decompose x at W(7): x = a+b.
    -- arm3 gives F ∈ W(0), G ∈ W'(0). arms_agree gives E = F+G.
    -- So G = E-F ∈ W(0), hence G ∈ W(0) ∩ W'(0) = 0, so b = 0.
    have leaf_containment
        (W W' : ∀ v, Submodule ℂ ((etilde7Rep m).obj v))
        (hW : ∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W a, (etilde7Rep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W' a, (etilde7Rep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W (4 : Fin 8)) :
        x ∈ W (7 : Fin 8) := by
      -- Decompose x at vertex 7
      have htop7 := (hc (7 : Fin 8)).sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop7
      -- arm2: x ∈ W(4) → E ∈ W(0)
      have hE := arm2_to_center W hW x hx
      -- arm3: a ∈ W(7) → F ∈ W(0), b ∈ W'(7) → G ∈ W'(0)
      have hF := arm3_to_center W hW a ha
      have hG := arm3_to_center W' hW' b hb
      -- G ∈ W(0): since E and arm3(x) agree, and x = a+b, we can extract G
      have hG_W : (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
          ((etilde7Rep m).mapLinear hom76 b)) ∈ W (0 : Fin 8) := by
        -- arm2(x) = arm3(x) = arm3(a) + arm3(b) = F + G
        have key : (etilde7Rep m).mapLinear hom20 ((etilde7Rep m).mapLinear hom32
            ((etilde7Rep m).mapLinear hom43 x)) =
          (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
            ((etilde7Rep m).mapLinear hom76 a)) +
          (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
            ((etilde7Rep m).mapLinear hom76 b)) := by
          have h1 := arms_agree x
          rw [h1, ← hab, map_add, map_add, map_add]
        -- arm3(b) = arm2(x) - arm3(a), and both are in W(0)
        have hFneg := (W (0 : Fin 8)).smul_mem (-1 : ℂ) hF
        have h := (W (0 : Fin 8)).add_mem hE hFneg
        have h2 : (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
            ((etilde7Rep m).mapLinear hom76 b)) =
          (etilde7Rep m).mapLinear hom20 ((etilde7Rep m).mapLinear hom32
            ((etilde7Rep m).mapLinear hom43 x)) +
          (-1 : ℂ) • (etilde7Rep m).mapLinear hom50 ((etilde7Rep m).mapLinear hom65
            ((etilde7Rep m).mapLinear hom76 a)) := by
          rw [key]; funext i
          show _ = (_ + _ + (-1 : ℂ) * _)
          ring
        rw [h2]; exact h
      -- G ∈ W(0) ∩ W'(0) = {0}
      have hzero := Submodule.mem_inf.mpr ⟨hG_W, hG⟩
      rw [(hc (0 : Fin 8)).inf_eq_bot, Submodule.mem_bot] at hzero
      -- From hzero, extract b = 0 via block A of the center
      have hb_zero : b = 0 := by
        ext ⟨j, hj⟩
        -- Evaluate hzero at position j (block A of center)
        have hj4 : j < 4 * (m + 1) := by omega
        have := congr_fun hzero ⟨j, by show j < etilde7Dim m (0 : Fin 8); simp [etilde7Dim]; omega⟩
        -- This is embed3to4_ACD(embed2to3_AB(starEmbed1(b))) at j = b_j
        show b ⟨j, hj⟩ = 0
        change embed3to4_ACD m (embed2to3_AB m (starEmbed1 m b))
          ⟨j, by show j < etilde7Dim m (0 : Fin 8); simp [etilde7Dim]; omega⟩ = 0 at this
        simp only [embed3to4_ACD, embed2to3_AB, starEmbed1,
          LinearMap.coe_mk, AddHom.coe_mk,
          dif_pos hj, dif_pos (show j < 2 * (m + 1) by omega)] at this
        simpa using this
      rw [hb_zero, add_zero] at hab; rw [← hab]; exact ha
    -- Helper: if A ≤ B, A' ≤ B', IsCompl A A', IsCompl B B', then A = B
    have compl_eq_of_le (A B A' B' : Submodule ℂ (Fin (m + 1) → ℂ))
        (hAB : A ≤ B) (hA'B' : A' ≤ B')
        (hcA : IsCompl A A') (hcB : IsCompl B B') : A = B := by
      apply le_antisymm hAB; intro x hx
      have hx_top := hcA.sup_eq_top ▸ Submodule.mem_top (x := x)
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx_top
      have ha'_B : a' ∈ B := by
        have h := B.sub_mem hx (hAB ha); rwa [show a + a' - a = a' from by abel] at h
      have : a' ∈ B ⊓ B' := Submodule.mem_inf.mpr ⟨ha'_B, hA'B' ha'⟩
      rw [hcB.inf_eq_bot, Submodule.mem_bot] at this; rwa [this, add_zero]
    -- W₁(4) = W₁(7) and W₂(4) = W₂(7)
    have heq47 : W₁ (4 : Fin 8) = W₁ (7 : Fin 8) := compl_eq_of_le _ _ _ _
      (fun x hx => leaf_containment W₁ W₂ hW₁_inv hW₂_inv hcompl x hx)
      (fun x hx => leaf_containment W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx)
      (hcompl (4 : Fin 8)) (hcompl (7 : Fin 8))
    have heq47' : W₂ (4 : Fin 8) = W₂ (7 : Fin 8) := compl_eq_of_le _ _ _ _
      (fun x hx => leaf_containment W₂ W₁ hW₂_inv hW₁_inv
        (fun v => (hcompl v).symm) x hx)
      (fun x hx => leaf_containment W₁ W₂ hW₁_inv hW₂_inv hcompl x hx)
      ((hcompl (4 : Fin 8)).symm) ((hcompl (7 : Fin 8)).symm)
    -- N-invariance of W₁(4) and W₂(4) under nilpotentShiftLin
    -- KEY DIFFICULTY: The nilpotent enters through arm 1 (vertex 1→0),
    -- but leaves 4 and 7 connect only to block A of the center.
    -- The connection from arm1's block D (which carries Nq) to block A
    -- (which carries leaf data) requires a non-trivial argument about
    -- the complement decomposition at the center and intermediate vertices.
    have hN₁ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₁ (4 : Fin 8) → nilpotentShiftLin m x ∈ W₁ (4 : Fin 8) := by
      sorry
    have hN₂ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₂ (4 : Fin 8) → nilpotentShiftLin m x ∈ W₂ (4 : Fin 8) := by
      sorry
    -- Apply nilpotent_invariant_compl_trivial at vertex 4
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ (4 : Fin 8)) (W₂ (4 : Fin 8)) hN₁ hN₂ (hcompl (4 : Fin 8))
    -- Propagation: W(4) = ⊥ → W(0) = ⊥ → all W(v) = ⊥
    -- W(4) = ⊥ → W(7) = ⊥ → W'(4) = ⊤, W'(7) = ⊤
    -- → block A of center filled in W' → ... → W(0) = ⊥
    -- → all arrows injective → all vertices ⊥
    suffices propagate : ∀ (W W' : ∀ v, Submodule ℂ ((etilde7Rep m).obj v)),
        (∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W a, (etilde7Rep m).mapLinear e x ∈ W b) →
        (∀ {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b),
          ∀ x ∈ W' a, (etilde7Rep m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W (4 : Fin 8) = W (7 : Fin 8) →
        W (4 : Fin 8) = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₁_inv hW₂_inv hcompl heq47 h
      · right; exact propagate W₂ W₁ hW₂_inv hW₁_inv
          (fun v => (hcompl v).symm) heq47' h
    intro W W' hW_inv hW'_inv hc h47 hbot v
    -- Strategy: show W(0) = ⊥ using W invariance, the complement condition,
    -- and the nilpotent coupling in arm 1 (requires hm : 1 ≤ m).
    -- Then propagate to all vertices via injectivity of the representation maps.
    -- KEY SORRY: Show W(0) = ⊥.
    -- Proof sketch: W'(4) = ⊤ and W'(7) = ⊤ (from W(4) = W(7) = ⊥).
    -- Pushing through arm chains gives {(x,0,0,0)} ⊂ W'(0).
    -- For m ≥ 1, the arm 1 map (p,q) ↦ (p+q, p, 0, Nq) with nontrivial N
    -- forces W'(0) to span blocks A, B, and D: any element of W(1) mapping
    -- to W(0) must satisfy p+q ∈ block_A_of_W(0) = 0 (since block A ⊂ W'(0)),
    -- which constrains W(1) to {(p,-p)} and forces W'(1) large enough that
    -- its image fills the remaining blocks. For m = 0 (N = 0), this fails:
    -- the representation is genuinely decomposable (see issue #2374).
    have hbot0 : W (0 : Fin 8) = ⊥ := by sorry
    -- Propagate from W(0) = ⊥ to all vertices via injectivity of maps.
    -- Each representation map is a block embedding (hence injective).
    -- Helper: if an injective arrow maps W(source) into W(target) = ⊥, then W(source) = ⊥.
    have prop_inj {a b : Fin 8} (e : @Quiver.Hom _ etilde7Quiver a b)
        (hinj : ∀ x : (etilde7Rep m).obj a, (etilde7Rep m).mapLinear e x = 0 → x = 0)
        (htarget : W b = ⊥) : W a = ⊥ := by
      rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]
      have := hW_inv e x hx; rw [htarget, Submodule.mem_bot] at this
      exact hinj x this
    -- Injectivity of starEmbed1: x ↦ (x, 0) is injective
    have inj_starEmbed1 : ∀ x : Fin (m + 1) → ℂ, starEmbed1 m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [starEmbed1, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj, Pi.zero_apply] at this
      exact this
    -- Injectivity of embed2to3_AB: (x,y) ↦ (x,y,0) is injective
    have inj_embed2to3_AB : ∀ x : Fin (2 * (m + 1)) → ℂ, embed2to3_AB m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embed2to3_AB, LinearMap.coe_mk, AddHom.coe_mk, dif_pos (show j < 2 * (m + 1) from hj),
        Pi.zero_apply] at this
      exact this
    -- Injectivity of embed3to4_ABC: (x,y,z) ↦ (x,y,z,0) is injective
    have inj_embed3to4_ABC : ∀ x : Fin (3 * (m + 1)) → ℂ, embed3to4_ABC m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by show j < 4 * (m + 1); omega⟩
      simp only [embed3to4_ABC, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj, Pi.zero_apply] at this
      exact this
    -- Injectivity of embed3to4_ACD: (x,y,z) ↦ (x,0,y,z) is injective
    have inj_embed3to4_ACD : ∀ x : Fin (3 * (m + 1)) → ℂ, embed3to4_ACD m x = 0 → x = 0 := by
      intro x h; ext ⟨j, hj⟩
      by_cases hjlt : j < m + 1
      · -- Block A: output at position j
        have := congr_fun h ⟨j, by omega⟩
        simp only [embed3to4_ACD, LinearMap.coe_mk, AddHom.coe_mk,
          dif_pos hjlt, Pi.zero_apply] at this
        exact this
      · -- Blocks C,D: output at position j + (m+1)
        have := congr_fun h ⟨j + (m + 1), by omega⟩
        simp only [embed3to4_ACD, LinearMap.coe_mk, AddHom.coe_mk,
          dif_neg (show ¬(j + (m + 1) < m + 1) from by omega),
          dif_neg (show ¬(m + 1 ≤ j + (m + 1) ∧ j + (m + 1) < 2 * (m + 1)) from by omega),
          dif_pos (show j + (m + 1) < 4 * (m + 1) from by omega),
          Nat.add_sub_cancel, Pi.zero_apply] at this
        exact this
    -- Injectivity of etilde7Arm1Embed: (p,q) ↦ (p+q, p, q, Nq) is injective
    have inj_arm1 : ∀ x : Fin (2 * (m + 1)) → ℂ, etilde7Arm1Embed m x = 0 → x = 0 := by
      intro w h; ext ⟨j, hj⟩
      have h0 : ∀ i : Fin (4 * (m + 1)), etilde7Arm1Embed m w i = 0 :=
        fun i => by have := congr_fun h i; simpa using this
      by_cases hjlt : j < m + 1
      · -- First component (p): read from block B (position m+1+j)
        have := h0 ⟨m + 1 + j, by omega⟩
        simp only [etilde7Arm1Embed, LinearMap.coe_mk, AddHom.coe_mk,
          dif_neg (show ¬(m + 1 + j < m + 1) from by omega),
          dif_pos (show m + 1 + j < 2 * (m + 1) from by omega),
          show m + 1 + j - (m + 1) = j from by omega,
          Pi.zero_apply] at this
        exact this
      · -- Second component (q): read from block C (position 2(m+1)+j-(m+1))
        have := h0 ⟨2 * (m + 1) + (j - (m + 1)), by omega⟩
        simp only [etilde7Arm1Embed, LinearMap.coe_mk, AddHom.coe_mk,
          dif_neg (show ¬(2 * (m + 1) + (j - (m + 1)) < m + 1) from by omega),
          dif_neg (show ¬(2 * (m + 1) + (j - (m + 1)) < 2 * (m + 1)) from by omega),
          dif_pos (show 2 * (m + 1) + (j - (m + 1)) < 3 * (m + 1) from by omega),
          show m + 1 + (2 * (m + 1) + (j - (m + 1)) - 2 * (m + 1)) = j from by omega,
          Pi.zero_apply] at this
        exact this
    -- Chain: W(0)=⊥ → W(1)=⊥, W(2)=⊥, W(5)=⊥; then W(2)=⊥ → W(3)=⊥; W(5)=⊥ → W(6)=⊥
    have hbot1 : W (1 : Fin 8) = ⊥ := prop_inj hom10 inj_arm1 hbot0
    have hbot2 : W (2 : Fin 8) = ⊥ := prop_inj hom20 inj_embed3to4_ABC hbot0
    have hbot5 : W (5 : Fin 8) = ⊥ := prop_inj hom50 inj_embed3to4_ACD hbot0
    have hbot3 : W (3 : Fin 8) = ⊥ := by
      have hom32' := hom32
      exact prop_inj hom32' inj_embed2to3_AB hbot2
    have hbot6 : W (6 : Fin 8) = ⊥ := by
      have hom65' := hom65
      exact prop_inj hom65' inj_embed2to3_AB hbot5
    have hbot7 : W (7 : Fin 8) = ⊥ := h47 ▸ hbot
    fin_cases v
    · exact hbot0  -- v = 0
    · exact hbot1  -- v = 1
    · exact hbot2  -- v = 2
    · exact hbot3  -- v = 3
    · exact hbot   -- v = 4
    · exact hbot5  -- v = 5
    · exact hbot6  -- v = 6
    · exact hbot7  -- v = 7

theorem etilde7Rep_dimVec (m : ℕ) (v : Fin 8) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin 8) _ etilde7Quiver
      (etilde7Rep m) v ≃ₗ[ℂ] (Fin (etilde7Dim m v) → ℂ)) :=
  ⟨LinearEquiv.refl _ _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem etilde7_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 8 etilde7Adj := by
  intro hft
  letI := etilde7Quiver
  have hfin := @hft ℂ _ inferInstance etilde7Quiver
    (fun a b => etilde7Quiver_subsingleton a b)
    etilde7Orientation_isOrientationOf
  -- We range over `m + 1` (not `m`) because `etilde7Rep_isIndecomposable`
  -- requires `1 ≤ m`: the `m = 0` case is provably decomposable.
  have hmem : ∀ m : ℕ, (fun v : Fin 8 => etilde7Dim (m + 1) v) ∈
      {d : Fin 8 → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin 8),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨etilde7Rep (m + 1),
      etilde7Rep_isIndecomposable (m + 1) (Nat.succ_le_succ m.zero_le),
      etilde7Rep_dimVec (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 8 => etilde7Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨4, by omega⟩
    simp only [etilde7Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 20: T_{1,2,5} has infinite representation type

The graph T_{1,2,5} has 9 vertices: center (0) with arms of length 1, 2, 5.
- Arm 1 (length 1): 0-1
- Arm 2 (length 2): 0-2-3
- Arm 3 (length 5): 0-4-5-6-7-8

The null root is δ = (6, 3, 4, 2, 5, 4, 3, 2, 1).
-/

/-- Adjacency matrix for T_{1,2,5} (9 vertices). -/
def t125Adj : Matrix (Fin 9) (Fin 9) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0
  | 0, 2 | 2, 0 | 2, 3 | 3, 2
  | 0, 4 | 4, 0 | 4, 5 | 5, 4 | 5, 6 | 6, 5 | 6, 7 | 7, 6 | 7, 8 | 8, 7 => 1
  | _, _ => 0

theorem t125Adj_symm : t125Adj.IsSymm := by
  ext i j; simp only [t125Adj, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem t125Adj_diag (i : Fin 9) : t125Adj i i = 0 := by
  fin_cases i <;> simp [t125Adj]

theorem t125Adj_01 (i j : Fin 9) : t125Adj i j = 0 ∨ t125Adj i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [t125Adj]

/-- The T_{1,2,5} quiver: all arrows directed toward the center (vertex 0).
Arrows: 1→0, 3→2, 2→0, 8→7, 7→6, 6→5, 5→4, 4→0. -/
def t125Quiver : Quiver (Fin 9) where
  Hom i j := PLift (
    (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 3 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
    (i.val = 8 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
    (i.val = 5 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0))

instance t125Quiver_subsingleton (a b : Fin 9) :
    Subsingleton (@Quiver.Hom (Fin 9) t125Quiver a b) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

private theorem t125_arrow_implies_edge (i j : Fin 9)
    (hp : (i.val = 1 ∧ j.val = 0) ∨
      (i.val = 3 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
      (i.val = 8 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
      (i.val = 5 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0)) :
    t125Adj i j = 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [t125Adj, h1, h2]

-- T_{1,2,5} has 9 vertices; fin_cases creates 81 goals for adjacency
set_option maxHeartbeats 3200000 in
private theorem t125_edge_has_arrow (i j : Fin 9) (hij : t125Adj i j = 1) :
    Nonempty (@Quiver.Hom (Fin 9) t125Quiver i j) ∨
    Nonempty (@Quiver.Hom (Fin 9) t125Quiver j i) := by
  fin_cases i <;> fin_cases j <;> simp [t125Adj] at hij <;>
    first
    | (left; exact ⟨⟨by decide⟩⟩)
    | (right; exact ⟨⟨by decide⟩⟩)

-- orientation proof for 9-vertex T_{1,2,5} quiver
set_option maxHeartbeats 800000 in
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem t125Orientation_isOrientationOf :
    @Etingof.IsOrientationOf 9 t125Quiver t125Adj := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
  · constructor; intro ⟨hp⟩; exact hij (t125_arrow_implies_edge i j hp)
  · exact t125_edge_has_arrow i j hij
  · obtain ⟨hp⟩ := hi; obtain ⟨hq⟩ := hj
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        omega

/-- Dimension of vertex v in the T_{1,2,5} representation (null root multiples):
    v0: 6(m+1), v1: 3(m+1), v2: 4(m+1), v3: 2(m+1), v4: 5(m+1),
    v5: 4(m+1), v6: 3(m+1), v7: 2(m+1), v8: m+1. -/
def t125Dim (m : ℕ) (v : Fin 9) : ℕ :=
  match v.val with
  | 0 => 6 * (m + 1)
  | 1 | 6 => 3 * (m + 1)
  | 2 | 5 => 4 * (m + 1)
  | 3 | 7 => 2 * (m + 1)
  | 4 => 5 * (m + 1)
  | _ => m + 1  -- vertex 8

/-- Generic first-blocks embedding: ℂ^{k·(m+1)} ↪ ℂ^{n·(m+1)} for k ≤ n,
    sending x to (x, 0, ..., 0). -/
noncomputable def embedFirstBlocks (m : ℕ) (k n : ℕ) (hkn : k ≤ n) :
    (Fin (k * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (n * (m + 1)) → ℂ) where
  toFun x i := if h : i.val < k * (m + 1) then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Embedding ℂ^{k·(m+1)} into ℂ^{n·(m+1)} skipping block B (positions m+1..2(m+1)-1):
    (x₁,...,xₖ) ↦ (x₁, 0, x₂, ..., xₖ). Block A gets first component, skip B, then C..onwards. -/
noncomputable def embedSkipBlockB (m : ℕ) (k n : ℕ) (hkn : k + 1 ≤ n) (hk : 1 ≤ k) :
    (Fin (k * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (n * (m + 1)) → ℂ) where
  toFun x i :=
    if h : i.val < m + 1 then
      x ⟨i.val, by nlinarith⟩
    else if h2 : i.val < 2 * (m + 1) then
      0  -- Block B: skip
    else if h3 : i.val < (k + 1) * (m + 1) then
      x ⟨i.val - (m + 1), by
        have : (k + 1) * (m + 1) = k * (m + 1) + (m + 1) := by ring
        omega⟩
    else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- T_{1,2,5} arm 1 embedding: ℂ^{3(m+1)} → ℂ^{6(m+1)}.
    (p,q,r) ↦ (p+q+r, p+q, p, q, r, Nr) where p,q,r are blocks of size (m+1).
    Couples all six blocks and introduces nilpotent twist in block F. -/
noncomputable def t125Arm1Embed (m : ℕ) :
    (Fin (3 * (m + 1)) → ℂ) →ₗ[ℂ] (Fin (6 * (m + 1)) → ℂ) where
  toFun w i :=
    if h : i.val < m + 1 then
      -- Block A: p + q + r
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩ +
        w ⟨2 * (m + 1) + i.val, by omega⟩
    else if h2 : i.val < 2 * (m + 1) then
      -- Block B: p + q
      let j := i.val - (m + 1)
      w ⟨j, by omega⟩ + w ⟨m + 1 + j, by omega⟩
    else if h3 : i.val < 3 * (m + 1) then
      -- Block C: p
      let j := i.val - 2 * (m + 1)
      w ⟨j, by omega⟩
    else if h4 : i.val < 4 * (m + 1) then
      -- Block D: q
      w ⟨m + 1 + (i.val - 3 * (m + 1)), by omega⟩
    else if h5 : i.val < 5 * (m + 1) then
      -- Block E: r
      w ⟨2 * (m + 1) + (i.val - 4 * (m + 1)), by omega⟩
    else
      -- Block F: Nr (nilpotent shift of third component r)
      let j := i.val - 5 * (m + 1)
      if h6 : j + 1 < m + 1 then w ⟨2 * (m + 1) + j + 1, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Match-based map for the T_{1,2,5} representation.
    Arm 1: 1→0 via nilpotent-coupled embedding
    Arm 2: 3→2→0 via identity chain + first-4-blocks embedding
    Arm 3: 8→7→6→5→4→0 via identity chain + skip-block-B embedding -/
private noncomputable def t125RepMap (m : ℕ) (a b : Fin 9) :
    (Fin (t125Dim m a) → ℂ) →ₗ[ℂ] (Fin (t125Dim m b) → ℂ) :=
  match a, b with
  -- Arm 1: 1→0
  | ⟨1, _⟩, ⟨0, _⟩ => t125Arm1Embed m
  -- Arm 2: 3→2→0
  | ⟨3, _⟩, ⟨2, _⟩ => embedFirstBlocks m 2 4 (by omega) -- ℂ^{2(m+1)} → ℂ^{4(m+1)}: x ↦ (x,0,0)
  -- Need: ℂ^{4(m+1)} → ℂ^{6(m+1)}: first 4 blocks
  | ⟨2, _⟩, ⟨0, _⟩ => embedFirstBlocks m 4 6 (by omega)
  -- Arm 3: 8→7→6→5→4→0
  | ⟨8, _⟩, ⟨7, _⟩ => starEmbed1 m          -- ℂ^{m+1} → ℂ^{2(m+1)}
  | ⟨7, _⟩, ⟨6, _⟩ => embed2to3_AB m        -- ℂ^{2(m+1)} → ℂ^{3(m+1)}
  | ⟨6, _⟩, ⟨5, _⟩ => embedFirstBlocks m 3 4 (by omega) -- ℂ^{3(m+1)} → ℂ^{4(m+1)}
  | ⟨5, _⟩, ⟨4, _⟩ => embedFirstBlocks m 4 5 (by omega) -- ℂ^{4(m+1)} → ℂ^{5(m+1)}
  | ⟨4, _⟩, ⟨0, _⟩ => embedSkipBlockB m 5 6 (by omega) (by omega) -- ℂ^{5(m+1)} → ℂ^{6(m+1)}: skip B
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
noncomputable def t125Rep (m : ℕ) :
    @Etingof.QuiverRepresentation ℂ (Fin 9) _ t125Quiver := by
  letI := t125Quiver
  exact {
    obj := fun v => Fin (t125Dim m v) → ℂ
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => t125RepMap m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem t125Rep_isIndecomposable (m : ℕ) (hm : 1 ≤ m) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 9)
      t125Quiver (t125Rep m) := by
  letI := t125Quiver
  constructor
  · -- Nontrivial at vertex 8 (dim m+1 ≥ 1)
    refine ⟨⟨8, by omega⟩, ?_⟩
    show Nontrivial (Fin (t125Dim m ⟨8, by omega⟩) → ℂ)
    simp only [t125Dim]
    infer_instance
  · -- Indecomposability
    intro W₁ W₂ hW₁_inv hW₂_inv hcompl
    -- Helper: Quiver.Hom constructors for each arrow
    have hom10 : @Quiver.Hom _ t125Quiver ⟨1, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inl ⟨rfl, rfl⟩⟩
    have hom32 : @Quiver.Hom _ t125Quiver ⟨3, by omega⟩ ⟨2, by omega⟩ :=
      ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    have hom20 : @Quiver.Hom _ t125Quiver ⟨2, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    have hom87 : @Quiver.Hom _ t125Quiver ⟨8, by omega⟩ ⟨7, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    have hom76 : @Quiver.Hom _ t125Quiver ⟨7, by omega⟩ ⟨6, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    have hom65 : @Quiver.Hom _ t125Quiver ⟨6, by omega⟩ ⟨5, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    have hom54 : @Quiver.Hom _ t125Quiver ⟨5, by omega⟩ ⟨4, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩
    have hom40 : @Quiver.Hom _ t125Quiver ⟨4, by omega⟩ ⟨0, by omega⟩ :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))⟩
    -- Arm chain helpers: push x ∈ W(8) to center via arm 3 (8→7→6→5→4→0)
    have arm3_to_center (W : ∀ v, Submodule ℂ ((t125Rep m).obj v))
        (hW : ∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W a, (t125Rep m).mapLinear e x ∈ W b)
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W (8 : Fin 9)) :
        (t125Rep m).mapLinear hom40 ((t125Rep m).mapLinear hom54
          ((t125Rep m).mapLinear hom65 ((t125Rep m).mapLinear hom76
            ((t125Rep m).mapLinear hom87 x)))) ∈ W (0 : Fin 9) :=
      hW hom40 _ (hW hom54 _ (hW hom65 _ (hW hom76 _ (hW hom87 x hx))))
    -- Arm 2 chain from vertex 3 to center (3→2→0)
    have arm2_to_center (W : ∀ v, Submodule ℂ ((t125Rep m).obj v))
        (hW : ∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W a, (t125Rep m).mapLinear e x ∈ W b)
        (y : Fin (2 * (m + 1)) → ℂ) (hy : y ∈ W (3 : Fin 9)) :
        (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 y) ∈ W (0 : Fin 9) :=
      hW hom20 _ (hW hom32 y hy)
    -- Both arm chains produce the same element (x,0,...,0) at the center when
    -- arm 3 starts from x at vertex 8 and arm 2 starts from starEmbed1(x) at vertex 3.
    -- Arm 3: x → (x,0) → (x,0,0) → (x,0,0,0) → (x,0,0,0,0) → (x,0,0,0,0,0)
    -- Arm 2: (x,0) → (x,0,0,0) → (x,0,0,0,0,0)
    -- The embedSkipBlockB at 4→0 skips block B, but since blocks B..E of the
    -- arm 3 intermediate are all 0, the skip has no effect.
    have arms_agree : ∀ x : Fin (m + 1) → ℂ,
        (t125Rep m).mapLinear hom40 ((t125Rep m).mapLinear hom54
          ((t125Rep m).mapLinear hom65 ((t125Rep m).mapLinear hom76
            ((t125Rep m).mapLinear hom87 x)))) =
        (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32
          (starEmbed1 m x)) := by
      intro x
      show embedSkipBlockB m 5 6 (by omega) (by omega)
            (embedFirstBlocks m 4 5 (by omega)
              (embedFirstBlocks m 3 4 (by omega)
                (embed2to3_AB m (starEmbed1 m x)))) =
           embedFirstBlocks m 4 6 (by omega)
            (embedFirstBlocks m 2 4 (by omega) (starEmbed1 m x))
      ext ⟨i, hi⟩
      simp only [embedSkipBlockB, embedFirstBlocks, embed2to3_AB, starEmbed1,
        LinearMap.coe_mk, AddHom.coe_mk] at hi ⊢
      -- Both sides equal: if i < m+1 then x ⟨i, _⟩ else 0
      -- We proceed by case analysis on which block i falls in
      split_ifs <;> first | rfl | (try omega) | (try (exfalso; omega)) | (try congr 1; ext; omega)
    -- Leaf containment: x ∈ W(8) implies starEmbed1(x) ∈ W(3)
    -- Proof: decompose starEmbed1(x) at vertex 3, push both parts through arm 2,
    -- use arms_agree to show the W'(0) component is zero, extract via injectivity.
    have leaf_containment
        (W W' : ∀ v, Submodule ℂ ((t125Rep m).obj v))
        (hW : ∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W a, (t125Rep m).mapLinear e x ∈ W b)
        (hW' : ∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W' a, (t125Rep m).mapLinear e x ∈ W' b)
        (hc : ∀ v, IsCompl (W v) (W' v))
        (x : Fin (m + 1) → ℂ) (hx : x ∈ W (8 : Fin 9)) :
        starEmbed1 m x ∈ W (3 : Fin 9) := by
      -- Decompose starEmbed1(x) at vertex 3
      have htop3 := (hc (3 : Fin 9)).sup_eq_top ▸ Submodule.mem_top (x := starEmbed1 m x)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop3
      -- arm3: x ∈ W(8) → E ∈ W(0)
      have hE := arm3_to_center W hW x hx
      -- arm2: a ∈ W(3) → F ∈ W(0), b ∈ W'(3) → G ∈ W'(0)
      have hF := arm2_to_center W hW a ha
      have hG := arm2_to_center W' hW' b hb
      -- G ∈ W(0): since arm3(x) = arm2(starEmbed1(x)) = arm2(a) + arm2(b) = F + G
      have hG_W : (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 b)
          ∈ W (0 : Fin 9) := by
        have key : (t125Rep m).mapLinear hom40 ((t125Rep m).mapLinear hom54
            ((t125Rep m).mapLinear hom65 ((t125Rep m).mapLinear hom76
              ((t125Rep m).mapLinear hom87 x)))) =
          (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 a) +
          (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 b) := by
          have h1 := arms_agree x
          rw [h1, ← hab, map_add, map_add]
        have h2 : (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 b) =
          (t125Rep m).mapLinear hom40 ((t125Rep m).mapLinear hom54
            ((t125Rep m).mapLinear hom65 ((t125Rep m).mapLinear hom76
              ((t125Rep m).mapLinear hom87 x)))) +
          (-1 : ℂ) • (t125Rep m).mapLinear hom20 ((t125Rep m).mapLinear hom32 a) := by
          rw [key]; funext i; show _ = (_ + _ + (-1 : ℂ) * _); ring
        rw [h2]; exact (W (0 : Fin 9)).add_mem hE ((W (0 : Fin 9)).smul_mem (-1) hF)
      -- G ∈ W(0) ∩ W'(0) = {0}
      have hzero := Submodule.mem_inf.mpr ⟨hG_W, hG⟩
      rw [(hc (0 : Fin 9)).inf_eq_bot, Submodule.mem_bot] at hzero
      -- arm2(b) = 0 and arm2 composition is injective → b = 0
      have hb_zero : b = 0 := by
        -- hzero : embedFirstBlocks 4 6 (embedFirstBlocks 2 4 b) = 0
        -- embedFirstBlocks is injective (first k blocks are identity)
        have h1 : embedFirstBlocks m 2 4 (by omega) b = 0 := by
          change embedFirstBlocks m 4 6 (by omega) (embedFirstBlocks m 2 4 (by omega) b) =
            0 at hzero
          ext ⟨j, hj⟩
          have := congr_fun hzero ⟨j, by show j < t125Dim m (0 : Fin 9); simp [t125Dim]; omega⟩
          simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
            dif_pos (show j < 4 * (m + 1) by omega)] at this
          exact this
        ext ⟨j, hj⟩
        have := congr_fun h1 ⟨j, by show j < 4 * (m + 1); omega⟩
        simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
          dif_pos (show j < 2 * (m + 1) by omega)] at this
        exact this
      rw [hb_zero, add_zero] at hab; rw [← hab]; exact ha
    -- N-invariance of W₁(8) and W₂(8) under nilpotentShiftLin
    -- KEY DIFFICULTY: The nilpotent enters through arm 1 (vertex 1→0 via t125Arm1Embed),
    -- which puts Nr in block F of the center. Leaves 8 and 3 connect to block A of the
    -- center. The coupling from arm1's block F to block A requires analysis of the
    -- complement decomposition at the center and intermediate vertices.
    have hN₁ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₁ (8 : Fin 9) → nilpotentShiftLin m x ∈ W₁ (8 : Fin 9) := by
      sorry
    have hN₂ : ∀ (x : Fin (m + 1) → ℂ),
        x ∈ W₂ (8 : Fin 9) → nilpotentShiftLin m x ∈ W₂ (8 : Fin 9) := by
      sorry
    -- Apply nilpotent_invariant_compl_trivial at vertex 8
    have hresult := nilpotent_invariant_compl_trivial
      (nilpotentShiftLin m) (nilpotentShiftLin_nilpotent m) (nilpotentShiftLin_ker_finrank m)
      (W₁ (8 : Fin 9)) (W₂ (8 : Fin 9)) hN₁ hN₂ (hcompl (8 : Fin 9))
    -- Propagation: W(8) = ⊥ → W(0) = ⊥ → all W(v) = ⊥
    suffices propagate : ∀ (W W' : ∀ v, Submodule ℂ ((t125Rep m).obj v)),
        (∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W a, (t125Rep m).mapLinear e x ∈ W b) →
        (∀ {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b),
          ∀ x ∈ W' a, (t125Rep m).mapLinear e x ∈ W' b) →
        (∀ v, IsCompl (W v) (W' v)) →
        W (8 : Fin 9) = ⊥ → ∀ v, W v = ⊥ by
      rcases hresult with h | h
      · left; exact propagate W₁ W₂ hW₁_inv hW₂_inv hcompl h
      · right; exact propagate W₂ W₁ hW₂_inv hW₁_inv
          (fun v => (hcompl v).symm) h
    intro W W' hW_inv hW'_inv hc hbot8 v
    -- Step 1: W(0) = ⊥
    -- From W(8) = ⊥, W'(8) = ⊤. Pushing through arm chains fills W'(0) with
    -- block A data. The arm 1 nilpotent coupling (m ≥ 1) forces enough of
    -- W'(0) to span that W(0) must be ⊥.
    have hbot0 : W (0 : Fin 9) = ⊥ := by sorry
    -- Step 2: Propagate from W(0) = ⊥ to all vertices via injectivity.
    -- Each arrow a→0 has injective map: if f(W(a)) ⊂ W(0) = ⊥, then W(a) = ⊥.
    -- Helper: propagation via injective map
    have prop_inj {a b : Fin 9} (e : @Quiver.Hom _ t125Quiver a b)
        (hbot_b : W b = ⊥)
        (hinj : Function.Injective ((t125Rep m).mapLinear e)) : W a = ⊥ := by
      rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]
      have h := hW_inv e x hx
      rw [hbot_b, Submodule.mem_bot] at h
      have : (t125Rep m).mapLinear e x = (t125Rep m).mapLinear e 0 := by rw [h, map_zero]
      exact hinj this
    -- Injectivity of each edge map
    -- All maps are block embeddings (first-blocks, skip-block-B, or triangular), hence injective.
    -- The proofs show: if f(x) = f(y), reading the output blocks recovers x = y.
    have inj_10 : Function.Injective ((t125Rep m).mapLinear hom10) := by
      show Function.Injective (t125Arm1Embed m)
      intro x y h
      ext ⟨j, hj⟩
      by_cases hj1 : j < m + 1
      · -- p block: read from Block C (position 2(m+1)+j)
        have h1 := congr_fun h ⟨2 * (m + 1) + j, by omega⟩
        simp only [t125Arm1Embed, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
          dif_neg (show ¬(2 * (m + 1) + j < m + 1) by omega),
          dif_neg (show ¬(2 * (m + 1) + j < 2 * (m + 1)) by omega),
          dif_pos (show 2 * (m + 1) + j < 3 * (m + 1) by omega)] at h1
        convert h1 using 1 <;>
          exact congrArg _ (Fin.ext (by try simp only [Fin.val_mk]; omega))
      · by_cases hj2 : j < 2 * (m + 1)
        · -- q block: read from Block D (position 3(m+1)+(j-(m+1)))
          have h1 := congr_fun h ⟨3 * (m + 1) + (j - (m + 1)), by omega⟩
          simp only [t125Arm1Embed, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
            dif_neg (show ¬(3 * (m + 1) + (j - (m + 1)) < m + 1) by omega),
            dif_neg (show ¬(3 * (m + 1) + (j - (m + 1)) < 2 * (m + 1)) by omega),
            dif_neg (show ¬(3 * (m + 1) + (j - (m + 1)) < 3 * (m + 1)) by omega),
            dif_pos (show 3 * (m + 1) + (j - (m + 1)) < 4 * (m + 1) by omega),
            show m + 1 + (3 * (m + 1) + (j - (m + 1)) - 3 * (m + 1)) = j from by omega] at h1
          exact h1
        · -- r block: read from Block E (position 4(m+1)+(j-2(m+1)))
          have h1 := congr_fun h ⟨4 * (m + 1) + (j - 2 * (m + 1)), by omega⟩
          simp only [t125Arm1Embed, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
            dif_neg (show ¬(4 * (m + 1) + (j - 2 * (m + 1)) < m + 1) by omega),
            dif_neg (show ¬(4 * (m + 1) + (j - 2 * (m + 1)) < 2 * (m + 1)) by omega),
            dif_neg (show ¬(4 * (m + 1) + (j - 2 * (m + 1)) < 3 * (m + 1)) by omega),
            dif_neg (show ¬(4 * (m + 1) + (j - 2 * (m + 1)) < 4 * (m + 1)) by omega),
            dif_pos (show 4 * (m + 1) + (j - 2 * (m + 1)) < 5 * (m + 1) by omega),
            show 2 * (m + 1) + (4 * (m + 1) + (j - 2 * (m + 1)) - 4 * (m + 1)) = j from by omega] at h1
          exact h1
    have inj_32 : Function.Injective ((t125Rep m).mapLinear hom32) := by
      show Function.Injective (embedFirstBlocks m 2 4 (by omega))
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_20 : Function.Injective ((t125Rep m).mapLinear hom20) := by
      show Function.Injective (embedFirstBlocks m 4 6 (by omega))
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_87 : Function.Injective ((t125Rep m).mapLinear hom87) := by
      show Function.Injective (starEmbed1 m)
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [starEmbed1, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_76 : Function.Injective ((t125Rep m).mapLinear hom76) := by
      show Function.Injective (embed2to3_AB m)
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embed2to3_AB, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_65 : Function.Injective ((t125Rep m).mapLinear hom65) := by
      show Function.Injective (embedFirstBlocks m 3 4 (by omega))
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_54 : Function.Injective ((t125Rep m).mapLinear hom54) := by
      show Function.Injective (embedFirstBlocks m 4 5 (by omega))
      intro x y h; ext ⟨j, hj⟩
      have := congr_fun h ⟨j, by omega⟩
      simp only [embedFirstBlocks, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj] at this
      exact this
    have inj_40 : Function.Injective ((t125Rep m).mapLinear hom40) := by
      show Function.Injective (embedSkipBlockB m 5 6 (by omega) (by omega))
      intro x y h
      ext ⟨j, hj⟩
      by_cases hj1 : j < m + 1
      · -- Block A: output[j] = input[j]
        have h1 := congr_fun h ⟨j, by omega⟩
        simp only [embedSkipBlockB, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
          dif_pos (show j < m + 1 from hj1)] at h1
        exact h1
      · -- Blocks B..E: output[j + (m+1)] = input[j] (skip block B)
        have h1 := congr_fun h ⟨j + (m + 1), by omega⟩
        simp only [embedSkipBlockB, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
          dif_neg (show ¬(j + (m + 1) < m + 1) by omega),
          dif_neg (show ¬(j + (m + 1) < 2 * (m + 1)) by omega),
          dif_pos (show j + (m + 1) < (5 + 1) * (m + 1) by ring_nf; omega)] at h1
        convert h1 using 1 <;>
          exact congrArg _ (Fin.ext (by try simp only [Fin.val_mk]; omega))
    -- Chain: W(0)=⊥ → W(1)=⊥ (1→0), W(2)=⊥ (2→0), W(4)=⊥ (4→0)
    --        W(2)=⊥ → W(3)=⊥ (3→2), W(4)=⊥ → W(5)=⊥ (5→4)
    --        W(5)=⊥ → W(6)=⊥ (6→5), W(6)=⊥ → W(7)=⊥ (7→6)
    --        W(7)=⊥ → W(8)=⊥ (8→7)
    have hbot1 := prop_inj hom10 hbot0 inj_10
    have hbot2 := prop_inj hom20 hbot0 inj_20
    have hbot4 := prop_inj hom40 hbot0 inj_40
    have hbot3 := prop_inj hom32 hbot2 inj_32
    have hbot5 := prop_inj hom54 hbot4 inj_54
    have hbot6 := prop_inj hom65 hbot5 inj_65
    have hbot7 := prop_inj hom76 hbot6 inj_76
    have hbot8' := prop_inj hom87 hbot7 inj_87
    fin_cases v <;> assumption

theorem t125Rep_dimVec (m : ℕ) (v : Fin 9) :
    Nonempty (@Etingof.QuiverRepresentation.obj ℂ (Fin 9) _ t125Quiver
      (t125Rep m) v ≃ₗ[ℂ] (Fin (t125Dim m v) → ℂ)) :=
  ⟨LinearEquiv.refl _ _⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
theorem t125_not_finite_type :
    ¬ Etingof.IsFiniteTypeQuiver 9 t125Adj := by
  intro hft
  letI := t125Quiver
  have hfin := @hft ℂ _ inferInstance t125Quiver
    (fun a b => t125Quiver_subsingleton a b)
    t125Orientation_isOrientationOf
  -- We range over `m + 1` (not `m`) because `t125Rep_isIndecomposable`
  -- requires `1 ≤ m`: the `m = 0` case is provably decomposable.
  have hmem : ∀ m : ℕ, (fun v : Fin 9 => t125Dim (m + 1) v) ∈
      {d : Fin 9 → ℕ | ∃ V : Etingof.QuiverRepresentation.{0,0,0,0} ℂ (Fin 9),
        V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[ℂ] (Fin (d v) → ℂ))} := by
    intro m
    exact ⟨t125Rep (m + 1),
      t125Rep_isIndecomposable (m + 1) (Nat.succ_le_succ m.zero_le),
      t125Rep_dimVec (m + 1)⟩
  have hinj : Function.Injective (fun m : ℕ => fun v : Fin 9 => t125Dim (m + 1) v) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨8, by omega⟩
    simp only [t125Dim] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

/-! ## Section 21: Non-ADE graph classification

Every non-ADE connected simple graph on n ≥ 1 vertices has infinite representation type.

The proof proceeds in two steps:
1. **Algebraic reduction**: Use the Dynkin classification theorem to show that a non-ADE
   connected simple graph cannot be a Dynkin diagram, hence its Cartan form is not
   positive definite.
2. **Graph-theoretic classification**: Show that a connected simple graph with
   non-positive-definite Cartan form contains one of the forbidden subgraphs
   (cycle, K_{1,4}, D̃₅, Ẽ₆, Ẽ₇, T_{1,2,5}), each proved to have infinite type.

The representation theory is complete: all forbidden subgraph infinite type proofs
are done (Sections 1-20 above). The remaining sorry is in `not_posdef_infinite_type`,
which encapsulates the graph-theoretic classification.
-/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- A graph containing a triangle (3-cycle) has infinite representation type.
    Uses the fact that cycleAdj 3 is the complete graph on 3 vertices. -/
theorem triangle_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (_h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_ab : adj a b = 1) (h_bc : adj b c = 1) (h_ac : adj a c = 1) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Construct embedding φ : Fin 3 ↪ Fin n mapping 0 ↦ a, 1 ↦ b, 2 ↦ c
  let φ_fun : Fin 3 → Fin n := ![a, b, c]
  have hφ_inj : Function.Injective φ_fun := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [φ_fun, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  let φ : Fin 3 ↪ Fin n := ⟨φ_fun, hφ_inj⟩
  have hembed : ∀ i j, cycleAdj 3 (by omega) i j = adj (φ i) (φ j) := by
    intro i j
    have h_ba := (hsymm.apply a b).trans h_ab
    have h_cb := (hsymm.apply b c).trans h_bc
    have h_ca := (hsymm.apply a c).trans h_ac
    fin_cases i <;> fin_cases j <;> simp [cycleAdj, φ, φ_fun, Matrix.cons_val_zero,
      Matrix.cons_val_one, hdiag, h_ab, h_bc, h_ac, h_ba, h_cb, h_ca]
  exact subgraph_infinite_type_transfer φ adj (cycleAdj 3 (by omega)) hsymm
    (fun v h => by linarith [hdiag v]) hembed (cycle_not_finite_type 3 (by omega))

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- A graph containing a cycle (given as a list of distinct vertices with edges between
    consecutive elements and a closing edge) has infinite representation type.
    Proved by strong induction on cycle length: chordless cycles embed into the abstract
    cycle graph; cycles with chords yield strictly shorter sub-cycles. -/
theorem graph_with_list_cycle_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (cycle : List (Fin n))
    (hlen : 3 ≤ cycle.length)
    (hnodup : cycle.Nodup)
    (hedge : ∀ k, (hk : k + 1 < cycle.length) →
      adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, hk⟩) = 1)
    (hclose : adj (cycle.get ⟨cycle.length - 1, by omega⟩)
                   (cycle.get ⟨0, by omega⟩) = 1) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Strong induction on cycle length, quantified over all cycles of that length
  revert cycle hlen hnodup hedge hclose
  have key : ∀ m, (hm : 3 ≤ m) → ∀ (cyc : List (Fin n)), (hlen : cyc.length = m) → cyc.Nodup →
      (∀ k, (hk : k + 1 < cyc.length) →
        adj (cyc.get ⟨k, by omega⟩) (cyc.get ⟨k + 1, hk⟩) = 1) →
      (adj (cyc.get ⟨cyc.length - 1, by omega⟩) (cyc.get ⟨0, by omega⟩) = 1) →
      ¬ IsFiniteTypeQuiver n adj := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro hm cyc hcyc_len hcyc_nodup hcyc_edge hcyc_close
      -- Check if cycle has a chord: ∃ i j with i < j, j - i ≥ 2, not closing edge, adjacent
      by_cases h_chord :
        ∃ (i j : Fin cyc.length), i.val < j.val ∧ j.val - i.val ≥ 2 ∧
          ¬(i.val = 0 ∧ j.val = cyc.length - 1) ∧
          adj (cyc.get i) (cyc.get j) = 1
      · -- Chord case: extract shorter sub-cycle and apply IH
        obtain ⟨p, q, hpq, hdist, hnot_close, hadj_chord⟩ := h_chord
        -- Extract natural number indices
        have hi : p.val < cyc.length := p.isLt
        have hj : q.val < cyc.length := q.isLt
        have hij : p.val < q.val := hpq
        have hdist2 : q.val - p.val ≥ 2 := hdist
        -- The sub-cycle is cyc[p], cyc[p+1], ..., cyc[q] with closing edge from chord
        set subcyc := (cyc.drop p.val).take (q.val - p.val + 1) with hsubcyc_def
        have hsublen : subcyc.length = q.val - p.val + 1 := by
          simp [hsubcyc_def, List.length_take, List.length_drop]; omega
        have hsublen3 : 3 ≤ q.val - p.val + 1 := by omega
        have hsublt : q.val - p.val + 1 < m := by
          subst hcyc_len; push_neg at hnot_close
          by_cases hp0 : p.val = 0
          · have := hnot_close hp0; omega
          · omega
        -- Sub-cycle elements match original cycle shifted by p
        have hsubget : ∀ (k : ℕ) (hk : k < subcyc.length),
            subcyc.get ⟨k, hk⟩ = cyc.get ⟨p.val + k, by rw [hsublen] at hk; omega⟩ := by
          intro k hk
          simp only [List.get_eq_getElem, hsubcyc_def, List.getElem_take, List.getElem_drop]
        -- Nodup
        have hsub_nodup : subcyc.Nodup :=
          hcyc_nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
        -- Consecutive edges
        have hsub_edge : ∀ k, (hk : k + 1 < subcyc.length) →
            adj (subcyc.get ⟨k, by omega⟩) (subcyc.get ⟨k + 1, hk⟩) = 1 := by
          intro k hk
          rw [hsubget k (by omega), hsubget (k + 1) (by omega)]
          have hik : p.val + k + 1 < cyc.length := by rw [hsublen] at hk; omega
          have : cyc.get ⟨p.val + (k + 1), by omega⟩ = cyc.get ⟨p.val + k + 1, hik⟩ := by
            congr 1
          rw [this]
          exact hcyc_edge (p.val + k) hik
        -- Closing edge: adj(cyc[q], cyc[p]) = 1 (the chord, via symmetry)
        have hsub_close : adj (subcyc.get ⟨subcyc.length - 1, by omega⟩)
            (subcyc.get ⟨0, by omega⟩) = 1 := by
          rw [hsubget _ (by omega), hsubget 0 (by omega)]
          have h1 : cyc.get ⟨p.val + (subcyc.length - 1), by omega⟩ = cyc.get q := by
            congr 1; ext; simp [hsublen]; omega
          have h2 : cyc.get ⟨p.val + 0, by omega⟩ = cyc.get p := by
            congr 1
          rw [h1, h2, hsymm.apply]; exact hadj_chord
        exact ih (q.val - p.val + 1) hsublt hsublen3 subcyc hsublen hsub_nodup hsub_edge
          hsub_close
      · -- Chordless case: embed into cycle graph
        push_neg at h_chord
        -- The embedding φ : Fin m → Fin n sends i to cyc[i]
        let φ_fun : Fin m → Fin n := fun i => cyc.get ⟨i.val, by omega⟩
        have hφ_inj : Function.Injective φ_fun := by
          intro a b hab
          simp only [φ_fun] at hab
          exact Fin.ext (Fin.mk.inj (hcyc_nodup.injective_get hab))
        let φ : Fin m ↪ Fin n := ⟨φ_fun, hφ_inj⟩
        have hembed : ∀ i j, cycleAdj m hm i j = adj (φ i) (φ j) := by
          intro ⟨i, hi⟩ ⟨j, hj⟩
          simp only [cycleAdj, φ, φ_fun]
          split_ifs with h
          · -- Adjacent in cycle → adj = 1
            rcases h with h_fwd | h_bwd
            · -- j = (i + 1) % m
              by_cases him : i + 1 < m
              · rw [Nat.mod_eq_of_lt him] at h_fwd; subst h_fwd
                exact (hcyc_edge i (by omega)).symm
              · have hi_eq : i = m - 1 := by omega
                rw [hi_eq, show m - 1 + 1 = m from by omega, Nat.mod_self] at h_fwd
                subst hi_eq; subst h_fwd
                have := hcyc_close.symm; convert this using 2; all_goals (ext; simp_all)
            · -- i = (j + 1) % m (symmetric case)
              by_cases hjm : j + 1 < m
              · rw [Nat.mod_eq_of_lt hjm] at h_bwd; subst h_bwd
                rw [hsymm.apply]; exact (hcyc_edge j (by omega)).symm
              · have hj_eq : j = m - 1 := by omega
                rw [hj_eq, show m - 1 + 1 = m from by omega, Nat.mod_self] at h_bwd
                subst hj_eq; subst h_bwd
                rw [hsymm.apply]
                have := hcyc_close.symm; convert this using 2; all_goals (ext; simp_all)
          · -- Not adjacent in cycle → adj = 0
            push_neg at h
            by_cases hij : i = j
            · subst hij; exact (hdiag _).symm
            · -- Distinct non-adjacent: no chord → adj = 0
              -- Convert h from modular to direct form
              have h_not_fwd : j ≠ (i + 1) % m := h.1
              have h_not_bwd : i ≠ (j + 1) % m := h.2
              rcases Nat.lt_or_ge i j with h_lt | h_ge
              · -- i < j
                have hdist : j - i ≥ 2 := by
                  by_contra hd; push_neg at hd
                  have hji : j = i + 1 := by omega
                  subst hji; exact h_not_fwd (Nat.mod_eq_of_lt (by omega)).symm
                have hnotclose : i = 0 → j ≠ cyc.length - 1 := by
                  intro hi0; subst hi0
                  intro hjm; rw [hcyc_len] at hjm; subst hjm
                  -- h_not_bwd : 0 ≠ (m-1+1) % m = 0 ≠ 0, contradiction
                  exact h_not_bwd (by rw [show m - 1 + 1 = m from by omega, Nat.mod_self])
                have h_not1 := h_chord ⟨i, by omega⟩ ⟨j, by omega⟩ h_lt hdist hnotclose
                rcases h01 (cyc.get ⟨i, by omega⟩) (cyc.get ⟨j, by omega⟩) with h0 | h1
                · exact h0.symm
                · exact absurd h1 h_not1
              · -- j < i
                have h_lt : j < i := by omega
                have hdist : i - j ≥ 2 := by
                  by_contra hd; push_neg at hd
                  have hij2 : i = j + 1 := by omega
                  subst hij2; exact h_not_bwd (Nat.mod_eq_of_lt (by omega)).symm
                have hnotclose : j = 0 → i ≠ cyc.length - 1 := by
                  intro hj0; subst hj0
                  intro him; rw [hcyc_len] at him; subst him
                  -- h_not_fwd : 0 ≠ (m-1+1) % m = 0 ≠ 0, contradiction
                  exact h_not_fwd (by rw [show m - 1 + 1 = m from by omega, Nat.mod_self])
                have h_not1 := h_chord ⟨j, by omega⟩ ⟨i, by omega⟩ h_lt hdist hnotclose
                rcases h01 (cyc.get ⟨i, by omega⟩) (cyc.get ⟨j, by omega⟩) with h0 | h1
                · exact h0.symm
                · rw [hsymm.apply] at h1; exact absurd h1 h_not1
        exact subgraph_infinite_type_transfer φ adj (cycleAdj m hm) hsymm
          (fun v hv => by linarith [hdiag v]) hembed (cycle_not_finite_type m hm)
  intro cycle hlen hnodup hedge hclose
  exact key cycle.length hlen cycle rfl hnodup hedge hclose

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- A graph with a vertex of degree ≥ 4 has infinite representation type.
    Either 4 neighbors are pairwise non-adjacent (star subgraph), or two neighbors
    are adjacent (triangle/cycle). No triangle-free hypothesis needed. -/
theorem degree_ge_4_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (v : Fin n) (hv : 4 ≤ vertexDegree adj v) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Get 4 distinct neighbors of v
  set S := Finset.univ.filter (fun w => adj v w = 1) with hS_def
  have hS_card : 4 ≤ S.card := hv
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS_card
  have hT_fin : Fintype T := inferInstance
  have hT_card : Fintype.card T = 4 := by rwa [Fintype.card_coe]
  let e := (Fintype.equivFinOfCardEq hT_card).symm
  let neighbors : Fin 4 → Fin n := fun i => (e i).val
  have h_adj : ∀ i, adj v (neighbors i) = 1 := by
    intro i; exact (Finset.mem_filter.mp (hTS (e i).prop)).2
  have h_ne : ∀ i, neighbors i ≠ v := by
    intro i hc; have := h_adj i; rw [← hc, hdiag] at this; exact one_ne_zero this.symm
  have h_inj : Function.Injective neighbors := by
    intro a b hab; exact (e.injective (Subtype.val_injective hab))
  -- Case split: are any two neighbors adjacent?
  by_cases h_indep : ∀ i j, adj (neighbors i) (neighbors j) = 0
  · -- All pairwise non-adjacent: use star_subgraph_not_finite_type
    exact star_subgraph_not_finite_type adj hsymm hdiag v ⟨neighbors, h_inj⟩ h_ne h_adj h_indep
  · -- Two neighbors are adjacent: triangle v - w₁ - w₂
    push_neg at h_indep
    obtain ⟨i, j, h_adj_ij⟩ := h_indep
    have h_nonzero : adj (neighbors i) (neighbors j) ≠ 0 := by intro hc; exact h_adj_ij hc
    have h_one : adj (neighbors i) (neighbors j) = 1 := by
      rcases h01 (neighbors i) (neighbors j) with h | h
      · exact absurd h h_nonzero
      · exact h
    -- We have a triangle: v, neighbors i, neighbors j
    have hij : neighbors i ≠ neighbors j := by
      intro hc; rw [hc, hdiag] at h_one; exact one_ne_zero h_one.symm
    exact triangle_infinite_type adj hsymm hdiag h01 v (neighbors i) (neighbors j)
      (h_ne i).symm hij (h_ne j).symm
      (h_adj i) h_one (h_adj j)

/-! ## Section 21a: Helper lemmas for the degree ≤ 3 classification

These lemmas decompose the proof that a connected simple graph with non-positive-definite
Cartan form has infinite representation type, in the case where all vertices have degree ≤ 3.
-/

/-- A connected simple graph containing a chordless cycle of length k ≥ 3 has infinite type.
    The cycle is given as an injective embedding φ : Fin k ↪ Fin n that exactly preserves
    the cycle adjacency structure. -/
theorem chordless_cycle_infinite_type {n k : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (hk : 3 ≤ k)
    (φ : Fin k ↪ Fin n)
    (hembed : ∀ i j, cycleAdj k hk i j = adj (φ i) (φ j)) :
    ¬ IsFiniteTypeQuiver n adj :=
  subgraph_infinite_type_transfer φ adj (cycleAdj k hk) hsymm
    (fun v h => by linarith [hdiag v]) hembed (cycle_not_finite_type k hk)

/-- Strong induction helper: for a connected acyclic graph with all degrees < 3
    and a designated leaf e, the Cartan form satisfies Q(x) ≥ x(e)² (hence ≥ 0)
    and Q(x) > 0 for all x ≠ 0.

    The proof removes the leaf, applies the IH to the reduced graph, and uses the
    decomposition Q(x) = Q'(x') + 2·x(e)² - 2·x(e)·x(v₁) where v₁ is the unique
    neighbor and Q' is the Cartan form of the reduced graph.
    By the IH, Q'(x') ≥ x'(v₁)², giving Q(x) ≥ x(e)² + (x(e) - x(v₁))² ≥ x(e)². -/
-- Cartan form quadratic form notation for brevity
private abbrev QF {m : ℕ} (adj : Matrix (Fin m) (Fin m) ℤ) (x : Fin m → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj).mulVec x)

set_option maxHeartbeats 800000 in
-- Connected acyclic path graph Cartan form is positive definite (strong induction)
private lemma acyclic_path_posdef_aux : ∀ (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (e : Fin n),
    adj.IsSymm → (∀ i, adj i i = 0) → (∀ i j, adj i j = 0 ∨ adj i j = 1) →
    (∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) →
    (∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1) →
    (∀ v, vertexDegree adj v < 3) →
    vertexDegree adj e ≤ 1 →
    -- Conclusion: Q(x) ≥ x(e)², Q(x) > 0 for x ≠ 0, AND Q(x) > x(e)² for x ≠ 0
    (∀ x : Fin n → ℤ, (x e) ^ 2 ≤ QF adj x) ∧
    (∀ x : Fin n → ℤ, x ≠ 0 → 0 < QF adj x) ∧
    (∀ x : Fin n → ℤ, x ≠ 0 → (x e) ^ 2 < QF adj x) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro adj e hsymm hdiag h01 hconn h_acyclic h_deg he
  -- Base case: n = 1
  match n, adj, e, hsymm, hdiag, h01, hconn, h_acyclic, h_deg, he with
  | 1, adj, e, hsymm, hdiag, h01, _, _, _, _ =>
    -- n = 1: Q(x) = 2·x₀², and e is the only vertex
    have he0 : e = 0 := Subsingleton.elim _ _
    have hQF_gen : ∀ x : Fin 1 → ℤ, QF adj x = 2 * (x 0) ^ 2 := by
      intro x
      unfold QF; simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, Fin.isValue, ite_true, hdiag, sub_zero]
      ring
    refine ⟨?_, ?_, ?_⟩
    · -- Q(x) ≥ (x e)²
      intro x; rw [he0, hQF_gen]; nlinarith [sq_nonneg (x 0)]
    · -- Q(x) > 0 for x ≠ 0
      intro x hx
      rw [hQF_gen]
      have : x 0 ≠ 0 := by
        intro h; apply hx; ext ⟨i, hi⟩; interval_cases i; exact h
      positivity
    · -- Q(x) > (x e)² for x ≠ 0
      intro x hx
      rw [he0, hQF_gen]
      have : x 0 ≠ 0 := by
        intro h; apply hx; ext ⟨i, hi⟩; interval_cases i; exact h
      have h_pos : 0 < (x 0) ^ 2 := by positivity
      nlinarith
  | (k + 2), adj, e, hsymm, hdiag, h01, hconn, h_acyclic, h_deg, he =>
    -- n = k + 2 ≥ 2. e is a leaf with degree ≤ 1.
    -- Since n ≥ 2 and graph is connected, e has exactly degree 1.
    have he_deg1 : vertexDegree adj e = 1 := by
      apply le_antisymm he
      -- Degree ≥ 1: pick j ≠ e, get path, first edge gives a neighbor
      obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2), j ≠ e :=
        ⟨⟨if e.val = 0 then 1 else 0, by split_ifs <;> omega⟩,
         fun h => by simp only [Fin.ext_iff] at h; split_ifs at h <;> omega⟩
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn e j
      have hlen : 2 ≤ path.length := by
        rcases path with _ | ⟨a, _ | ⟨b, _⟩⟩
        · simp at hhead
        · simp only [List.head?, List.getLast?_singleton] at hhead hlast
          exact absurd (Option.some.inj hhead ▸ (Option.some.inj hlast).symm) hj
        · simp
      have hadj_01 := hedges 0 (by omega)
      have hp0 : path.get ⟨0, by omega⟩ = e := by
        rcases path with _ | ⟨a, _⟩
        · simp at hhead
        · exact Option.some.inj hhead
      rw [hp0] at hadj_01
      exact Finset.one_le_card.mpr ⟨path.get ⟨1, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_01⟩⟩
    -- Get unique neighbor v₁
    obtain ⟨v₁, hv₁_mem⟩ :=
      Finset.card_pos.mp (show 0 < vertexDegree adj e by omega)
    have hv₁_adj : adj e v₁ = 1 := (Finset.mem_filter.mp hv₁_mem).2
    have hunique : ∀ w, adj e w = 1 → w = v₁ := by
      intro w hw; by_contra hne
      have : 2 ≤ vertexDegree adj e := by
        change 2 ≤ (Finset.univ.filter (fun j => adj e j = 1)).card
        have hv₁_in : v₁ ∈ Finset.univ.filter (fun j => adj e j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ v₁, hv₁_adj⟩
        have hw_in : w ∈ Finset.univ.filter (fun j => adj e j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
        calc 2 = ({v₁, w} : Finset _).card := by
              rw [Finset.card_pair (fun h => hne (h.symm))]
          _ ≤ _ := Finset.card_le_card (fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
      omega
    have hne : v₁ ≠ e := by intro h; subst h; rw [hdiag] at hv₁_adj; omega
    -- Define reduced graph adj' on Fin (k + 1) by removing e
    set adj' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
      fun i j => adj (e.succAbove i) (e.succAbove j) with hadj'_def
    -- Lift x : Fin (k+2) → ℤ to x' on Fin (k+1) via succAbove
    -- and x_ext : Fin (k+2) → ℤ with x_ext(e) = 0
    -- Key transfer: QF adj' x' = QF adj x_ext (zeroing e)
    -- Then: QF adj x = QF adj x_ext + 2·(x e)² - 2·(x e)·(x v₁)
    -- Establish adj' properties
    have hsymm' : adj'.IsSymm := Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
    have hdiag' : ∀ i, adj' i i = 0 := fun i => hdiag _
    have h01' : ∀ i j, adj' i j = 0 ∨ adj' i j = 1 := fun i j => h01 _ _
    -- Degree bound for adj'
    have h_deg' : ∀ v, vertexDegree adj' v < 3 := by
      intro i; unfold vertexDegree
      calc (Finset.univ.filter (fun j => adj' i j = 1)).card
          ≤ (Finset.univ.filter (fun j : Fin (k + 2) => adj (e.succAbove i) j = 1)).card := by
            have h_image : ((Finset.univ.filter (fun j : Fin (k+1) => adj' i j = 1)).image e.succAbove)
                ⊆ Finset.univ.filter (fun j : Fin (k + 2) => adj (e.succAbove i) j = 1) :=
              fun x hx => by
                simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                obtain ⟨y, hy, rfl⟩ := hx; exact hy
            calc (Finset.univ.filter (fun j : Fin (k+1) => adj' i j = 1)).card
                = ((Finset.univ.filter (fun j : Fin (k+1) => adj' i j = 1)).image e.succAbove).card :=
                  (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
              _ ≤ _ := Finset.card_le_card h_image
        _ < 3 := h_deg _
    -- v₁' : preimage of v₁ under succAbove
    obtain ⟨v₁', hv₁'⟩ := Fin.exists_succAbove_eq hne
    -- v₁' is a leaf in adj'
    have hv₁'_deg : vertexDegree adj' v₁' ≤ 1 := by
      unfold vertexDegree
      have h_image : ((Finset.univ.filter (fun j : Fin (k+1) => adj' v₁' j = 1)).image e.succAbove)
          ⊆ (Finset.univ.filter (fun j : Fin (k + 2) => adj v₁ j = 1)).erase e := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne e y, by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₁' ▸ hy⟩⟩
      have h_card : (Finset.univ.filter (fun j : Fin (k+1) => adj' v₁' j = 1)).card ≤
          ((Finset.univ.filter (fun j : Fin (k + 2) => adj v₁ j = 1)).erase e).card :=
        (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm ▸
          Finset.card_le_card h_image
      have hv₀_mem : e ∈ Finset.univ.filter (fun j : Fin (k + 2) => adj v₁ j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply e v₁ ▸ hv₁_adj⟩
      rw [Finset.card_erase_of_mem hv₀_mem] at h_card
      have := h_deg v₁; unfold vertexDegree at this; omega
    -- Acyclicity of adj': a cycle in adj' maps to a cycle in adj via e.succAbove
    have h_acyclic' : ∀ (cycle : List (Fin (k+1))) (hclen : 3 ≤ cycle.length), cycle.Nodup →
        (∀ m, (h : m + 1 < cycle.length) →
          adj' (cycle.get ⟨m, by omega⟩) (cycle.get ⟨m + 1, h⟩) = 1) →
        adj' (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
          (cycle.get ⟨0, by omega⟩) ≠ 1 := by
      intro cycle hclen hnodup hedges hlast
      -- Map cycle to adj via succAbove
      set cycle' := cycle.map e.succAbove
      have hlen' : cycle'.length = cycle.length := List.length_map ..
      have hget' : ∀ (m : ℕ) (hm : m < cycle'.length),
          cycle'.get ⟨m, hm⟩ = e.succAbove (cycle.get ⟨m, by rw [hlen'] at hm; exact hm⟩) := by
        intro m hm; exact List.getElem_map ..
      apply h_acyclic cycle' (by omega)
      · exact hnodup.map Fin.succAbove_right_injective
      · intro m hm
        rw [hget', hget']
        exact hedges m (by rw [hlen'] at hm; omega)
      · simp only [cycle', List.getLast_map, hget']
        exact hlast
    -- Connectivity of adj': removing a degree-1 vertex preserves connectivity.
    -- Uses SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one.
    -- (Same technique as DynkinForward.lean path_walk_construction)
    have hconn' : ∀ i j : Fin (k+1), ∃ path : List (Fin (k+1)),
        path.head? = some i ∧ path.getLast? = some j ∧
        ∀ m, (h : m + 1 < path.length) →
          adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, h⟩) = 1 := by
      -- Build SimpleGraph from adj
      let G : SimpleGraph (Fin (k + 2)) :=
        { Adj := fun i j => adj i j = 1
          symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
          loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
      haveI : DecidableRel G.Adj :=
        fun i j => show Decidable (adj i j = 1) from inferInstance
      -- G is connected
      have hG_conn : G.Connected := by
        constructor
        intro u v
        obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
        suffices h : ∀ (l : List (Fin (k + 2))) (a b : Fin (k + 2)),
            l.head? = some a → l.getLast? = some b →
            (∀ m, (hm : m + 1 < l.length) →
              adj (l.get ⟨m, by omega⟩) (l.get ⟨m + 1, hm⟩) = 1) →
            G.Reachable a b from h path u v hhead hlast hedges
        intro l; induction l with
        | nil => intro a _ ha; simp at ha
        | cons x t ih =>
          intro a b ha hb hedges'
          simp at ha; subst ha
          cases t with
          | nil => simp at hb; subst hb; exact SimpleGraph.Reachable.refl _
          | cons y s =>
            have hxy : G.Adj x y := hedges' 0 (by simp)
            exact hxy.reachable.trans
              (ih y b (by simp) hb (fun m hm => hedges' (m + 1)
                (by simp only [List.length_cons] at hm ⊢; omega)))
      -- G has degree 1 at e
      have hG_deg : G.degree e = 1 := by
        unfold SimpleGraph.degree
        have heq : G.neighborFinset e = Finset.univ.filter (adj e · = 1) := by
          ext j
          simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨fun h => h, fun h => h⟩
        rw [heq]; unfold vertexDegree at he_deg1; convert he_deg1
      -- Apply Mathlib: removing e preserves connectivity
      have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
      -- Convert: G.induce {e}ᶜ connectivity → adj' connectivity
      intro i j
      have hu_ne : e.succAbove i ≠ e := Fin.succAbove_ne e i
      have hw_ne : e.succAbove j ≠ e := Fin.succAbove_ne e j
      have hu_mem : e.succAbove i ∈ ({e}ᶜ : Set (Fin (k + 2))) :=
        Set.mem_compl_singleton_iff.mpr hu_ne
      have hw_mem : e.succAbove j ∈ ({e}ᶜ : Set (Fin (k + 2))) :=
        Set.mem_compl_singleton_iff.mpr hw_ne
      obtain ⟨walk⟩ := hG'.preconnected ⟨e.succAbove i, hu_mem⟩ ⟨e.succAbove j, hw_mem⟩
      -- Map vertices in {e}ᶜ to Fin (k+1) via succAbove inverse
      let toFink : ↥({e}ᶜ : Set (Fin (k + 2))) → Fin (k + 1) :=
        fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
          (Set.mem_compl_singleton_iff.mp hv)).choose
      have htoFink_spec : ∀ (x : ↥({e}ᶜ : Set (Fin (k + 2)))),
          e.succAbove (toFink x) = x.val :=
        fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
          (Set.mem_compl_singleton_iff.mp hv)).choose_spec
      have htoFink_adj : ∀ (x y : ↥({e}ᶜ : Set (Fin (k + 2)))),
          (G.induce ({e}ᶜ : Set _)).Adj x y →
          adj' (toFink x) (toFink y) = 1 := by
        intro x y hadj_xy
        simp only [hadj'_def, SimpleGraph.induce_adj] at hadj_xy ⊢
        rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
      -- Build path by induction on the walk
      suffices h_walk : ∀ (a b : ↥({e}ᶜ : Set (Fin (k + 2))))
          (w' : (G.induce ({e}ᶜ : Set _)).Walk a b),
        ∃ path : List (Fin (k + 1)),
          path.head? = some (toFink a) ∧
          path.getLast? = some (toFink b) ∧
          ∀ m, (hm : m + 1 < path.length) →
            adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
        obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
        refine ⟨path, ?_, ?_, hedges⟩
        · convert hhead using 2
          exact (Fin.succAbove_right_injective
            (htoFink_spec ⟨e.succAbove i, hu_mem⟩)).symm
        · convert hlast using 2
          exact (Fin.succAbove_right_injective
            (htoFink_spec ⟨e.succAbove j, hw_mem⟩)).symm
      intro a b w'
      induction w' with
      | nil =>
        exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
      | @cons c d _ hadj_edge rest ih =>
        obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
        refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
        · -- getLast?
          cases path_rest with
          | nil => simp at hhead_rest hlast_rest ⊢
          | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
        · -- Consecutive adjacency
          intro m hm
          match m with
          | 0 =>
            simp only [List.get_eq_getElem, List.getElem_cons_zero,
              List.getElem_cons_succ]
            have h0 : 0 < path_rest.length := by
              simp only [List.length_cons] at hm; omega
            have hd_eq : path_rest[0] = toFink d := by
              cases path_rest with
              | nil => simp at h0
              | cons y ys =>
                simp only [List.head?, Option.some.injEq] at hhead_rest
                simp only [List.getElem_cons_zero]
                exact hhead_rest
            rw [hd_eq]
            exact htoFink_adj c d hadj_edge
          | m' + 1 =>
            simp only [List.get_eq_getElem, List.getElem_cons_succ]
            exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)
    -- Apply induction hypothesis to adj'
    have ih_result := ih (k + 1) (by omega) adj' v₁' hsymm' hdiag' h01' hconn' h_acyclic' h_deg' hv₁'_deg
    obtain ⟨ih_lb, ih_pos, ih_strict⟩ := ih_result
    -- adj(e,j) is 1 only at v₁, 0 elsewhere
    have hadj_e : ∀ j, adj e j = if j = v₁ then 1 else 0 := by
      intro j; by_cases hj : j = v₁
      · simp [hj, hv₁_adj]
      · rcases h01 e j with h | h
        · simp [hj, h]
        · exact absurd (hunique j h) hj
    -- General decomposition: QF adj x = QF adj (zero at e) + 2·(x e)² - 2·(x e)·(x v₁)
    have h_decomp_gen : ∀ x : Fin (k+2) → ℤ,
        QF adj x = QF adj (fun i => if i = e then 0 else x i) +
          2 * (x e) ^ 2 - 2 * (x e) * (x v₁) := by
      intro x; set x_ext : Fin (k+2) → ℤ := fun i => if i = e then 0 else x i
      have hx_ext_e : x_ext e = 0 := by simp [x_ext]
      have hx_ext_sa : ∀ i, x_ext (e.succAbove i) = x (e.succAbove i) := by
        intro i; simp [x_ext, Fin.succAbove_ne e i]
      suffices h_diff : QF adj x - QF adj x_ext = 2 * (x e) ^ 2 - 2 * (x e) * (x v₁) by linarith
      simp only [QF, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply]
      rw [Fin.sum_univ_succAbove (f := fun i => x i * _) e,
          Fin.sum_univ_succAbove (f := fun i => x_ext i * _) e]
      simp only [hx_ext_e, zero_mul, zero_add]
      simp_rw [Fin.sum_univ_succAbove (f := fun j => _ * x j) e,
               Fin.sum_univ_succAbove (f := fun j => _ * x_ext j) e]
      simp only [hx_ext_e, mul_zero, add_zero]
      simp_rw [hx_ext_sa]
      simp only [hdiag, sub_zero, Fin.succAbove_ne, ite_false]
      simp_rw [show ∀ i, adj (e.succAbove i) e = adj e (e.succAbove i) from
        fun i => hsymm.apply _ _]
      simp_rw [hadj_e]
      simp_rw [show ∀ i : Fin (k+1), (e.succAbove i = v₁) = (i = v₁') from
        fun i => propext ⟨fun h => Fin.succAbove_right_injective (h.trans hv₁'.symm),
          fun h => h ▸ hv₁'⟩]
      simp only [show ∀ i : Fin (k+1), (e = e.succAbove i) = False from
        fun i => propext ⟨fun h => absurd h.symm (Fin.succAbove_ne e i), False.elim⟩,
        show ∀ i j : Fin (k+1), (e.succAbove i = e.succAbove j) = (i = j) from
        fun i j => propext ⟨fun h => Fin.succAbove_right_injective h, fun h => h ▸ rfl⟩,
        ite_false, ite_true]
      simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one, mul_zero, sub_zero,
        zero_sub, zero_add]
      conv_lhs =>
        rw [show ∀ (p : ℤ) (f g h : Fin (k+1) → ℤ),
            p + ∑ i, f i * (g i + h i) - ∑ i, f i * h i = p + ∑ i, f i * g i from by
          intros; simp only [mul_add, Finset.sum_add_distrib]; ring]
      simp only [apply_ite Neg.neg, neg_zero,
        ite_mul, neg_one_mul, zero_mul, mul_ite, mul_neg, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [show x (e.succAbove v₁') = x v₁ from by rw [hv₁']]
      ring
    refine ⟨?_, ?_, ?_⟩
    · -- Part 1: QF adj x ≥ (x e)² for all x
      intro x
      -- Define x' : Fin (k+1) → ℤ as x restricted via succAbove
      set x' : Fin (k + 1) → ℤ := fun i => x (e.succAbove i) with hx'_def
      -- Define x_ext : Fin (k+2) → ℤ as x with x(e) = 0
      set x_ext : Fin (k + 2) → ℤ := fun i => if i = e then 0 else x i with hx_ext_def
      have hx_ext_e : x_ext e = 0 := by simp [x_ext]
      have hx_ext_sa : ∀ i, x_ext (e.succAbove i) = x (e.succAbove i) := by
        intro i; simp [x_ext, Fin.succAbove_ne e i]
      -- Transfer: QF adj x_ext = QF adj' x'
      have h_transfer : QF adj x_ext = QF adj' x' := by
        simp only [QF, dotProduct, Matrix.mulVec]
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [hx_ext_e, zero_mul, zero_add]
        congr 1; ext i; rw [hx_ext_sa]; congr 1
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [hx_ext_e, mul_zero, zero_add]
        congr 1; ext j; rw [hx_ext_sa]; congr 1
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
          Fin.succAbove_right_inj, smul_eq_mul]
      set a := x e
      set b := x v₁
      have h_decomp : QF adj x = QF adj x_ext + 2 * a ^ 2 - 2 * a * b := h_decomp_gen x
      -- Now combine: QF adj x = QF adj' x' + 2a² - 2ab
      rw [h_decomp, h_transfer]
      -- IH gives: QF adj' x' ≥ (x' v₁')² = b²
      have hb_eq : x' v₁' = b := by show x (e.succAbove v₁') = x v₁; rw [hv₁']
      have ih_bound := ih_lb x'
      rw [hb_eq] at ih_bound
      -- QF adj' x' + 2a² - 2ab ≥ b² + 2a² - 2ab = a² + (a-b)²
      nlinarith [sq_nonneg (a - b)]
    · -- Part 2: QF adj x > 0 for x ≠ 0
      intro x hx
      set x' : Fin (k + 1) → ℤ := fun i => x (e.succAbove i) with hx'_def
      set x_ext : Fin (k + 2) → ℤ := fun i => if i = e then 0 else x i with hx_ext_def
      set a := x e
      set b := x v₁
      -- Same decomposition
      have h_transfer : QF adj x_ext = QF adj' x' := by
        simp only [QF, dotProduct, Matrix.mulVec]
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [show x_ext e = 0 from by simp [x_ext], zero_mul, zero_add]
        congr 1; ext i
        rw [show x_ext (e.succAbove i) = x (e.succAbove i) from by simp [x_ext, Fin.succAbove_ne]]
        congr 1
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [show x_ext e = 0 from by simp [x_ext], mul_zero, zero_add]
        congr 1; ext j
        rw [show x_ext (e.succAbove j) = x (e.succAbove j) from by simp [x_ext, Fin.succAbove_ne]]
        congr 1
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
          Fin.succAbove_right_inj, smul_eq_mul]
      -- Convert h_decomp_gen to use local set variables
      have h_decomp : QF adj x = QF adj x_ext + 2 * a ^ 2 - 2 * a * b := h_decomp_gen x
      have hb_eq : x' v₁' = b := by show x (e.succAbove v₁') = x v₁; rw [hv₁']
      by_cases ha : a = 0
      · -- x(e) = 0: QF adj x = QF adj' x', and x' ≠ 0
        have hx'_ne : x' ≠ 0 := by
          intro h; apply hx; funext i
          by_cases hi : i = e
          · exact hi ▸ ha
          · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
            have : x' j = (0 : Fin (k + 1) → ℤ) j := congr_fun h j
            simp only [x', Pi.zero_apply] at this
            rw [← hj]; exact this
        rw [h_decomp, ha]; simp; rw [h_transfer]; exact ih_pos x' hx'_ne
      · -- x(e) ≠ 0: QF adj x ≥ a² > 0
        have ih_bound := ih_lb x'
        rw [hb_eq] at ih_bound
        rw [h_decomp, h_transfer]
        have ha_pos : 0 < a ^ 2 := by positivity
        nlinarith [sq_nonneg (a - b)]
    · -- Part 3: QF adj x > (x e)² for x ≠ 0
      intro x hx
      set x' : Fin (k + 1) → ℤ := fun i => x (e.succAbove i) with hx'_def
      set x_ext : Fin (k + 2) → ℤ := fun i => if i = e then 0 else x i with hx_ext_def
      set a := x e
      set b := x v₁
      -- Same transfer as above
      have h_transfer : QF adj x_ext = QF adj' x' := by
        simp only [QF, dotProduct, Matrix.mulVec]
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [show x_ext e = 0 from by simp [x_ext], zero_mul, zero_add]
        congr 1; ext i
        rw [show x_ext (e.succAbove i) = x (e.succAbove i) from by simp [x_ext, Fin.succAbove_ne]]
        congr 1
        conv_lhs => rw [Fin.sum_univ_succAbove _ e]
        simp only [show x_ext e = 0 from by simp [x_ext], mul_zero, zero_add]
        congr 1; ext j
        rw [show x_ext (e.succAbove j) = x (e.succAbove j) from by simp [x_ext, Fin.succAbove_ne]]
        congr 1
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
          Fin.succAbove_right_inj, smul_eq_mul]
      have h_decomp : QF adj x = QF adj x_ext + 2 * a ^ 2 - 2 * a * b := h_decomp_gen x
      have hb_eq : x' v₁' = b := by show x (e.succAbove v₁') = x v₁; rw [hv₁']
      by_cases ha : a = 0
      · -- a = 0: Q(x) = Q'(x'), x' ≠ 0, Part 2 gives Q'(x') > 0 = a²
        have hx'_ne : x' ≠ 0 := by
          intro h; apply hx; funext i
          by_cases hi : i = e
          · exact hi ▸ ha
          · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
            have : x' j = (0 : Fin (k + 1) → ℤ) j := congr_fun h j
            simp only [x', Pi.zero_apply] at this
            rw [← hj]; exact this
        show a ^ 2 < QF adj x
        rw [h_decomp, ha, h_transfer]
        have := ih_pos x' hx'_ne
        nlinarith
      · -- a ≠ 0: case on x' = 0 or not
        by_cases hx'_z : x' = 0
        · -- x' = 0: QF adj' x' = 0, b = x v₁ = x'(v₁') = 0
          have hb0 : b = 0 := by
            rw [← hb_eq]; have := congr_fun hx'_z v₁'
            simp only [Pi.zero_apply] at this; exact this
          show a ^ 2 < QF adj x
          rw [h_decomp, h_transfer, hx'_z, hb0]
          have hQF0 : QF adj' (0 : Fin (k + 1) → ℤ) = 0 := by
            simp [QF, dotProduct, Matrix.mulVec]
          rw [hQF0]
          have ha_pos : 0 < a ^ 2 := by positivity
          nlinarith
        · -- x' ≠ 0: use Part 3 (ih_strict) at x', giving Q'(x') > b²
          have ih_bound := ih_strict x' hx'_z
          rw [hb_eq] at ih_bound
          show a ^ 2 < QF adj x
          rw [h_decomp, h_transfer]
          nlinarith [sq_nonneg (a - b)]

/-- A connected acyclic simple graph with all degrees ≤ 2 is a path, hence a Dynkin
    diagram of type A_n, and therefore has positive definite Cartan form. -/
theorem acyclic_deg_le_2_posdef {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 3) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  -- Find a leaf
  have h_has_leaf : ∃ e, vertexDegree adj e ≤ 1 := by
    by_contra h_no_leaf; push_neg at h_no_leaf
    -- All degrees ≥ 2, and all < 3, so all = 2. A 2-regular connected graph has a cycle.
    have hdeg2 : ∀ i, vertexDegree adj i = 2 := by
      intro i; have := h_deg i; have := h_no_leaf i; omega
    -- Build SimpleGraph from adj
    let G : SimpleGraph (Fin n) :=
      { Adj := fun i j => adj i j = 1
        symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
        loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
    haveI : DecidableRel G.Adj :=
      fun i j => show Decidable (adj i j = 1) from inferInstance
    -- G.degree = vertexDegree = 2
    have hG_deg : ∀ v, G.degree v = 2 := by
      intro v
      have : G.degree v = vertexDegree adj v := by
        unfold SimpleGraph.degree vertexDegree
        congr 1
        ext j; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
          Finset.mem_univ, true_and]; exact ⟨fun h => h, fun h => h⟩
      rw [this]; exact hdeg2 v
    -- G is connected
    have hG_conn : G.Connected := by
      haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact SimpleGraph.Connected.mk (fun u v => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
      suffices h : ∀ (l : List (Fin n)) (a b : Fin n),
          l.head? = some a → l.getLast? = some b →
          (∀ m, (hm : m + 1 < l.length) →
            adj (l.get ⟨m, by omega⟩) (l.get ⟨m + 1, hm⟩) = 1) →
          G.Reachable a b from h path u v hhead hlast hedges
      intro l; induction l with
      | nil => intro a _ ha; simp at ha
      | cons x t ih =>
        intro a b ha hb hedges'
        simp at ha; subst ha
        cases t with
        | nil => simp at hb; subst hb; exact SimpleGraph.Reachable.refl _
        | cons y s =>
          have hxy : G.Adj x y := hedges' 0 (by simp)
          exact hxy.reachable.trans
            (ih y b (by simp) hb (fun m hm => hedges' (m + 1)
              (by simp only [List.length_cons] at hm ⊢; omega))))
    -- G is acyclic (from h_acyclic): any Walk cycle → list cycle → contradiction
    have hG_acyclic : G.IsAcyclic := by
      intro v c hc
      have hc_len := hc.three_le_length
      -- Build list cycle from getVert
      set cycle := List.ofFn (fun i : Fin c.length => c.getVert i.val) with hcycle_def
      -- Nodup: from IsCycle.getVert_injOn'
      have hcycle_nodup : cycle.Nodup := by
        rw [List.nodup_ofFn]
        intro ⟨i, hi⟩ ⟨j, hj⟩ hveq; ext
        exact hc.getVert_injOn' (by simp [Set.mem_setOf_eq]; omega)
          (by simp [Set.mem_setOf_eq]; omega) hveq
      -- Consecutive edges
      have hcycle_len : cycle.length = c.length := by rw [hcycle_def, List.length_ofFn]
      -- Helper: cycle[m] = c.getVert m
      have hcycle_get : ∀ m (hm : m < cycle.length),
          cycle[m] = c.getVert m := by
        intro m hm
        change cycle.get ⟨m, hm⟩ = c.getVert m
        simp [hcycle_def]
      have hcycle_edges : ∀ m, (h : m + 1 < cycle.length) →
          adj (cycle.get ⟨m, by omega⟩) (cycle.get ⟨m + 1, h⟩) = 1 := by
        intro m hm
        show adj cycle[m] cycle[m + 1] = 1
        rw [hcycle_get m (by omega), hcycle_get (m + 1) (by omega)]
        exact c.adj_getVert_succ (by rw [← hcycle_len]; omega)
      -- Closing edge: adj (getVert (length-1)) (getVert 0) = 1
      have hcycle_ne_nil : cycle ≠ [] := by
        intro h; simp [h] at hcycle_len; omega
      have hcycle_close : adj (cycle.getLast hcycle_ne_nil)
          (cycle.get ⟨0, by rw [hcycle_len]; omega⟩) = 1 := by
        have hlast : cycle.getLast hcycle_ne_nil = c.getVert (c.length - 1) := by
          rw [List.getLast_eq_getElem]
          rw [hcycle_get _ (by rw [hcycle_len]; omega)]
          congr 1; omega
        have hfirst : cycle.get ⟨0, by rw [hcycle_len]; omega⟩ = c.getVert 0 := by
          show cycle[0] = _; rw [hcycle_get 0 (by rw [hcycle_len]; omega)]
        rw [hlast, hfirst]
        have hadj := c.adj_getVert_succ (show c.length - 1 < c.length by omega)
        rw [show c.length - 1 + 1 = c.length from by omega, c.getVert_length] at hadj
        rw [c.getVert_zero]; exact hadj
      -- Apply h_acyclic: closing edge ≠ 1
      exact h_acyclic cycle (by rw [hcycle_len]; omega) hcycle_nodup hcycle_edges hcycle_close
    -- G.IsTree: connected + acyclic
    have htree : G.IsTree := ⟨hG_conn, hG_acyclic⟩
    -- Edge count contradiction: tree has n-1 edges, but degree sum = 2n → n edges
    have h_edges := htree.card_edgeFinset
    have h_handshake := G.sum_degrees_eq_twice_card_edges
    simp only [hG_deg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h_handshake
    simp only [Fintype.card_fin] at h_edges
    omega
  obtain ⟨e, he⟩ := h_has_leaf
  exact (acyclic_path_posdef_aux n adj e hsymm hdiag h01 hconn h_acyclic h_deg he).2.1

/-- In an acyclic graph (tree), two distinct adjacent vertices have no other common
    neighbors. More precisely, if `adj v a = 1` and `adj v b = 1` with `a ≠ b`, and
    `adj v w = 1` with `w ≠ v`, then in the acyclic graph adj a b = 0 (they cannot
    form a triangle). -/
private theorem acyclic_no_triangle {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v a b : Fin n) (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (ha : adj v a = 1) (hb : adj v b = 1) : adj a b = 0 := by
  -- In a tree, if v is adjacent to both a and b, then a-b is not an edge (would form triangle)
  rcases h01 a b with h | h
  · exact h
  · exfalso
    -- adj_comm: adj i j = adj j i
    have adj_comm := fun i j => hsymm.apply j i
    have hcycle := h_acyclic [a, v, b] (by simp)
      (List.nodup_cons.mpr ⟨by simp [hav, hab],
        List.nodup_cons.mpr ⟨by simp [hbv.symm],
          List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩⟩)
      (by intro k hk; have hk' : k + 1 < 3 := by simpa using hk
          have : k = 0 ∨ k = 1 := by omega
          rcases this with rfl | rfl
          · exact (adj_comm a v).trans ha
          · exact hb)
    exact hcycle ((adj_comm b a).trans h)

/-- In an acyclic graph, vertices at path-distance ≥ 2 are non-adjacent.
    If there's a path v₁ - v₂ - ... - v_k from a to b (through intermediate vertices),
    then adj a b = 0 (would create a cycle). -/
private theorem acyclic_path_nonadj {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (path : List (Fin n)) (hlen : 3 ≤ path.length) (hnodup : path.Nodup)
    (hedges : ∀ k, (h : k + 1 < path.length) →
      adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    adj (path.getLast (List.ne_nil_of_length_pos (by omega)))
      (path.get ⟨0, by omega⟩) = 0 := by
  rcases h01 (path.getLast _) (path.get ⟨0, _⟩) with h | h
  · exact h
  · exact absurd h (h_acyclic path hlen hnodup hedges)

set_option maxHeartbeats 3200000 in
/-- A connected acyclic simple graph with two adjacent degree-3 vertices (and all
    degrees ≤ 3) has infinite representation type, by embedding D̃₅.
    The two branch points plus their 4 other neighbors give 6 vertices forming D̃₅. -/
private theorem adjacent_branches_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ w : Fin n) (hv₀_deg : vertexDegree adj v₀ = 3)
    (hw_deg : vertexDegree adj w = 3) (hvw_adj : adj v₀ w = 1) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- adj_comm: adj i j = adj j i (from symmetry)
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  -- ne_of_adj: adjacent vertices are distinct
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Extract the 3 neighbors of v₀
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have hS₀_card : S₀.card = 3 := hv₀_deg
  have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw_adj⟩
  have hS₀_erase : (S₀.erase w).card = 2 := by
    rw [Finset.card_erase_of_mem hw_mem, hS₀_card]
  obtain ⟨u₁, u₂, hu₁₂, hS₀_eq⟩ := Finset.card_eq_two.mp hS₀_erase
  have hu₁_mem : u₁ ∈ S₀.erase w := hS₀_eq ▸ Finset.mem_insert_self u₁ _
  have hu₂_mem : u₂ ∈ S₀.erase w := hS₀_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self u₂))
  have hu₁_adj : adj v₀ u₁ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁_mem)).2
  have hu₂_adj : adj v₀ u₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂_mem)).2
  have hu₁_ne_w : u₁ ≠ w := Finset.ne_of_mem_erase hu₁_mem
  have hu₂_ne_w : u₂ ≠ w := Finset.ne_of_mem_erase hu₂_mem
  -- Extract the 3 neighbors of w
  set Sw := Finset.univ.filter (fun j => adj w j = 1) with hSw_def
  have hSw_card : Sw.card = 3 := hw_deg
  have hv₀_mem_Sw : v₀ ∈ Sw :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm w v₀).trans hvw_adj⟩
  have hSw_erase : (Sw.erase v₀).card = 2 := by
    rw [Finset.card_erase_of_mem hv₀_mem_Sw, hSw_card]
  obtain ⟨w₁, w₂, hw₁₂, hSw_eq⟩ := Finset.card_eq_two.mp hSw_erase
  have hw₁_mem : w₁ ∈ Sw.erase v₀ := hSw_eq ▸ Finset.mem_insert_self w₁ _
  have hw₂_mem : w₂ ∈ Sw.erase v₀ := hSw_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self w₂))
  have hw₁_adj : adj w w₁ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hw₁_mem)).2
  have hw₂_adj : adj w w₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hw₂_mem)).2
  have hw₁_ne_v₀ : w₁ ≠ v₀ := Finset.ne_of_mem_erase hw₁_mem
  have hw₂_ne_v₀ : w₂ ≠ v₀ := Finset.ne_of_mem_erase hw₂_mem
  -- Key distinctness facts (from adjacency)
  have hv₀_ne_w : v₀ ≠ w := ne_of_adj v₀ w hvw_adj
  have hu₁_ne_v₀ : u₁ ≠ v₀ := (ne_of_adj v₀ u₁ hu₁_adj).symm
  have hu₂_ne_v₀ : u₂ ≠ v₀ := (ne_of_adj v₀ u₂ hu₂_adj).symm
  have hw₁_ne_w : w₁ ≠ w := (ne_of_adj w w₁ hw₁_adj).symm
  have hw₂_ne_w : w₂ ≠ w := (ne_of_adj w w₂ hw₂_adj).symm
  -- Non-edges via acyclic_no_triangle (center has both as neighbors → no triangle)
  -- u₁-u₂: center v₀
  have hu₁u₂ : adj u₁ u₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₂
      hu₁₂ hu₁_ne_v₀ hu₂_ne_v₀ hu₁_adj hu₂_adj
  -- u₁-w: center v₀
  have hu₁_w : adj u₁ w = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ w
      hu₁_ne_w hu₁_ne_v₀ hv₀_ne_w.symm hu₁_adj hvw_adj
  -- u₂-w: center v₀
  have hu₂_w : adj u₂ w = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₂ w
      hu₂_ne_w hu₂_ne_v₀ hv₀_ne_w.symm hu₂_adj hvw_adj
  -- w₁-w₂: center w
  have hw₁w₂ : adj w₁ w₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w w₁ w₂
      hw₁₂ hw₁_ne_w hw₂_ne_w hw₁_adj hw₂_adj
  -- v₀-w₁: center w (need adj w v₀ = 1)
  have hw_v₀ : adj w v₀ = 1 := (adj_comm w v₀).trans hvw_adj
  have hv₀_w₁ : adj v₀ w₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w v₀ w₁
      hw₁_ne_v₀.symm hv₀_ne_w hw₁_ne_w hw_v₀ hw₁_adj
  -- v₀-w₂: center w
  have hv₀_w₂ : adj v₀ w₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w v₀ w₂
      hw₂_ne_v₀.symm hv₀_ne_w hw₂_ne_w hw_v₀ hw₂_adj
  -- u₁ ≠ w₁, etc. (if u₁ = w₁, then adj v₀ w₁ = 1, contradicting hv₀_w₁ = 0)
  have hu₁_ne_w₁ : u₁ ≠ w₁ := by intro h; rw [h] at hu₁_adj; linarith
  have hu₁_ne_w₂ : u₁ ≠ w₂ := by intro h; rw [h] at hu₁_adj; linarith
  have hu₂_ne_w₁ : u₂ ≠ w₁ := by intro h; rw [h] at hu₂_adj; linarith
  have hu₂_ne_w₂ : u₂ ≠ w₂ := by intro h; rw [h] at hu₂_adj; linarith
  -- Flipped edge adjacencies for path proofs
  have hw₁_w : adj w₁ w = 1 := (adj_comm w₁ w).trans hw₁_adj
  have hw₂_w : adj w₂ w = 1 := (adj_comm w₂ w).trans hw₂_adj
  -- Path-distance ≥ 3 non-edges via acyclic_path_nonadj
  -- For path [w_j, w, v₀, u_i]: getLast = u_i, [0] = w_j → adj u_i w_j = 0
  have path_nodup : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
    intro a b c d hab hac had hbc hbd hcd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have path_edges : ∀ (a b c d : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d].length) →
        adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d h₁ h₂ h₃ k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have hu₁_w₁ : adj u₁ w₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₁, w, v₀, u₁] (by simp)
      (path_nodup w₁ w v₀ u₁ hw₁_ne_w hw₁_ne_v₀ hu₁_ne_w₁.symm hv₀_ne_w.symm hu₁_ne_w.symm hu₁_ne_v₀.symm)
      (path_edges w₁ w v₀ u₁ hw₁_w hw_v₀ hu₁_adj)
  have hu₁_w₂ : adj u₁ w₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₂, w, v₀, u₁] (by simp)
      (path_nodup w₂ w v₀ u₁ hw₂_ne_w hw₂_ne_v₀ hu₁_ne_w₂.symm hv₀_ne_w.symm hu₁_ne_w.symm hu₁_ne_v₀.symm)
      (path_edges w₂ w v₀ u₁ hw₂_w hw_v₀ hu₁_adj)
  have hu₂_w₁ : adj u₂ w₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₁, w, v₀, u₂] (by simp)
      (path_nodup w₁ w v₀ u₂ hw₁_ne_w hw₁_ne_v₀
        hu₂_ne_w₁.symm hv₀_ne_w.symm hu₂_ne_w.symm hu₂_ne_v₀.symm)
      (path_edges w₁ w v₀ u₂ hw₁_w hw_v₀ hu₂_adj)
  have hu₂_w₂ : adj u₂ w₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₂, w, v₀, u₂] (by simp)
      (path_nodup w₂ w v₀ u₂ hw₂_ne_w hw₂_ne_v₀
        hu₂_ne_w₂.symm hv₀_ne_w.symm hu₂_ne_w.symm hu₂_ne_v₀.symm)
      (path_edges w₂ w v₀ u₂ hw₂_w hw_v₀ hu₂_adj)
  -- Construct the embedding φ : Fin 6 ↪ Fin n
  -- Map: 0 → u₁, 1 → u₂, 2 → v₀, 3 → w, 4 → w₁, 5 → w₂
  let φ_fun : Fin 6 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => u₁ | ⟨1, _⟩ => u₂ | ⟨2, _⟩ => v₀
    | ⟨3, _⟩ => w  | ⟨4, _⟩ => w₁ | ⟨5, _⟩ => w₂
  -- Injectivity from 15 distinctness facts
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
  let φ : Fin 6 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  -- Adjacency verification: d5tildeAdj i j = adj (φ i) (φ j)
  have hembed : ∀ i j, d5tildeAdj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [d5tildeAdj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag u₁, hdiag u₂, hdiag v₀, hdiag w, hdiag w₁, hdiag w₂,
                adj_comm u₁ v₀, adj_comm u₂ v₀, adj_comm w v₀,
                adj_comm w₁ w, adj_comm w₂ w,
                adj_comm u₁ u₂, adj_comm u₁ w, adj_comm u₂ w,
                adj_comm w₁ w₂, adj_comm v₀ w₁, adj_comm v₀ w₂,
                adj_comm u₁ w₁, adj_comm u₁ w₂, adj_comm u₂ w₁, adj_comm u₂ w₂]
  exact subgraph_infinite_type_transfer φ adj d5tildeAdj hsymm
    (fun v h => by linarith [hdiag v]) hembed d5tilde_not_finite_type

set_option maxHeartbeats 3200000 in
/-- Given 9 vertices forming T(1,2,5) in an acyclic graph, embed and transfer infinite type.
    Vertices: v₀ (center), u₁ (arm1), p₁-p₂ (arm2), q₁-q₂-q₃-q₄-q₅ (arm3).
    Map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅. -/
private theorem embed_t125_in_tree {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ u₁ p₁ p₂ q₁ q₂ q₃ q₄ q₅ : Fin n)
    (hu₁ : adj v₀ u₁ = 1) (hp₁ : adj v₀ p₁ = 1) (hp₂ : adj p₁ p₂ = 1)
    (hq₁ : adj v₀ q₁ = 1) (hq₂ : adj q₁ q₂ = 1)
    (hq₃ : adj q₂ q₃ = 1) (hq₄ : adj q₃ q₄ = 1) (hq₅ : adj q₄ q₅ = 1)
    -- Structural ne facts (from how vertices were extracted as distinct neighbors)
    (hu₁_ne_p₁ : u₁ ≠ p₁) (hu₁_ne_q₁ : u₁ ≠ q₁) (hp₁_ne_q₁ : p₁ ≠ q₁)
    (hp₂_ne_v₀ : p₂ ≠ v₀) (hq₂_ne_v₀ : q₂ ≠ v₀)
    (hq₃_ne_q₁ : q₃ ≠ q₁) (hq₄_ne_q₂ : q₄ ≠ q₂) (hq₅_ne_q₃ : q₅ ≠ q₃) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Same-arm distinctness (from adjacency)
  have hv₀_ne_u₁ := ne_of_adj' v₀ u₁ hu₁
  have hv₀_ne_p₁ := ne_of_adj' v₀ p₁ hp₁
  have hp₁_ne_p₂ := ne_of_adj' p₁ p₂ hp₂
  have hv₀_ne_q₁ := ne_of_adj' v₀ q₁ hq₁
  have hq₁_ne_q₂ := ne_of_adj' q₁ q₂ hq₂
  have hq₂_ne_q₃ := ne_of_adj' q₂ q₃ hq₃
  have hq₃_ne_q₄ := ne_of_adj' q₃ q₄ hq₄
  have hq₄_ne_q₅ := ne_of_adj' q₄ q₅ hq₅
  -- Reversed edges
  have hp₁_v₀ : adj p₁ v₀ = 1 := (adj_comm p₁ v₀).trans hp₁
  have hp₂_p₁ : adj p₂ p₁ = 1 := (adj_comm p₂ p₁).trans hp₂
  have hq₁_v₀ : adj q₁ v₀ = 1 := (adj_comm q₁ v₀).trans hq₁
  have hq₂_q₁ : adj q₂ q₁ = 1 := (adj_comm q₂ q₁).trans hq₂
  have hq₃_q₂ : adj q₃ q₂ = 1 := (adj_comm q₃ q₂).trans hq₃
  have hq₄_q₃ : adj q₄ q₃ = 1 := (adj_comm q₄ q₃).trans hq₄
  have hq₅_q₄ : adj q₅ q₄ = 1 := (adj_comm q₅ q₄).trans hq₅
  -- Distance-2 non-edges (acyclic_no_triangle)
  have hu₁p₁ : adj u₁ p₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ p₁
      hu₁_ne_p₁ hv₀_ne_u₁.symm hv₀_ne_p₁.symm hu₁ hp₁
  have hu₁q₁ : adj u₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ q₁
      hu₁_ne_q₁ hv₀_ne_u₁.symm hv₀_ne_q₁.symm hu₁ hq₁
  have hp₁q₁ : adj p₁ q₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ p₁ q₁
      hp₁_ne_q₁ hv₀_ne_p₁.symm hv₀_ne_q₁.symm hp₁ hq₁
  have hv₀p₂ : adj v₀ p₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic p₁ v₀ p₂
      hp₂_ne_v₀.symm hv₀_ne_p₁ hp₁_ne_p₂.symm hp₁_v₀ hp₂
  have hv₀q₂ : adj v₀ q₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₁ v₀ q₂
      hq₂_ne_v₀.symm hv₀_ne_q₁ hq₁_ne_q₂.symm hq₁_v₀ hq₂
  have hq₁q₃ : adj q₁ q₃ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₂ q₁ q₃
      hq₃_ne_q₁.symm hq₁_ne_q₂ hq₂_ne_q₃.symm hq₂_q₁ hq₃
  have hq₂q₄ : adj q₂ q₄ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₃ q₂ q₄
      hq₄_ne_q₂.symm hq₂_ne_q₃ hq₃_ne_q₄.symm hq₃_q₂ hq₄
  have hq₃q₅ : adj q₃ q₅ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic q₄ q₃ q₅
      hq₅_ne_q₃.symm hq₃_ne_q₄ hq₄_ne_q₅.symm hq₄_q₃ hq₅
  -- Cross-arm ne (level 1)
  have hu₁_ne_p₂ : u₁ ≠ p₂ := by intro h; rw [h] at hu₁; linarith [hv₀p₂]
  have hu₁_ne_q₂ : u₁ ≠ q₂ := by intro h; rw [h] at hu₁; linarith [hv₀q₂]
  have hp₁_ne_q₂ : p₁ ≠ q₂ := by intro h; rw [h] at hp₁; linarith [hv₀q₂]
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₁, hp₁q₁]
  have hv₀_ne_q₃ : v₀ ≠ q₃ := by intro h; rw [← h] at hq₃; linarith [adj_comm q₂ v₀, hv₀q₂]
  have hq₁_ne_q₄ : q₁ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ q₁, hq₁q₃]
  have hq₂_ne_q₅ : q₂ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₂, hq₂q₄]
  -- Path nodup helpers
  have path_nodup4 : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
    intro a b c d hab hac had hbc hbd hcd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have path_nodup5 : ∀ (a b c d e : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e →
      b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      [a, b, c, d, e].Nodup := by
    intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
  have path_nodup6 : ∀ (a b c d e f : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f →
      c ≠ d → c ≠ e → c ≠ f → d ≠ e → d ≠ f → e ≠ f →
      [a, b, c, d, e, f].Nodup := by
    intro a b c d e f hab hac had hae haf hbc hbd hbe hbf
      hcd hce hcf hde hdf hef
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩,
      ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩
  have path_nodup7 : ∀ (a b c d e f g : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g →
      d ≠ e → d ≠ f → d ≠ g → e ≠ f → e ≠ g → f ≠ g →
      [a, b, c, d, e, f, g].Nodup := by
    intro a b c d e f g hab hac had hae haf hag hbc hbd hbe hbf hbg
      hcd hce hcf hcg hde hdf hdg hef heg hfg
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag⟩, ⟨hbc, hbd, hbe, hbf, hbg⟩,
      ⟨hcd, hce, hcf, hcg⟩, ⟨hde, hdf, hdg⟩, ⟨hef, heg⟩, hfg⟩
  have path_nodup8 : ∀ (a b c d e f g h : Fin n),
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g → a ≠ h →
      b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g → b ≠ h →
      c ≠ d → c ≠ e → c ≠ f → c ≠ g → c ≠ h →
      d ≠ e → d ≠ f → d ≠ g → d ≠ h →
      e ≠ f → e ≠ g → e ≠ h → f ≠ g → f ≠ h → g ≠ h →
      [a, b, c, d, e, f, g, h].Nodup := by
    intro a b c d e f g h₀ hab hac had hae haf hag hah hbc hbd hbe hbf hbg hbh
      hcd hce hcf hcg hch hde hdf hdg hdh hef heg heh hfg hfh hgh
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had, hae, haf, hag, hah⟩,
      ⟨hbc, hbd, hbe, hbf, hbg, hbh⟩,
      ⟨hcd, hce, hcf, hcg, hch⟩, ⟨hde, hdf, hdg, hdh⟩,
      ⟨hef, heg, heh⟩, ⟨hfg, hfh⟩, hgh⟩
  -- Path edges helpers
  have path_edges4 : ∀ (a b c d : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d].length) →
        adj ([a, b, c, d].get ⟨k, by omega⟩)
          ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d h₁ h₂ h₃ k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have path_edges5 : ∀ (a b c d e : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
        adj ([a, b, c, d, e].get ⟨k, by omega⟩)
          ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e h₁ h₂ h₃ h₄ k hk
    have : k + 1 < 5 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> assumption
  have path_edges6 : ∀ (a b c d e f : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      adj d e = 1 → adj e f = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f].length) →
        adj ([a, b, c, d, e, f].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f h₁ h₂ h₃ h₄ h₅ k hk
    have : k + 1 < 6 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
  have path_edges7 : ∀ (a b c d e f g : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g].length) →
        adj ([a, b, c, d, e, f, g].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₁ h₂ h₃ h₄ h₅ h₆ k hk
    have : k + 1 < 7 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have path_edges8 : ∀ (a b c d e f g h : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
      adj e f = 1 → adj f g = 1 → adj g h = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g, h].length) →
        adj ([a, b, c, d, e, f, g, h].get ⟨k, by omega⟩)
          ([a, b, c, d, e, f, g, h].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d e f g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ k hk
    have : k + 1 < 8 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Distance-3 non-edges (4-vertex paths)
  have hu₁p₂ : adj u₁ p₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [p₂, p₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hp₁_ne_p₂.symm hp₂_ne_v₀ hu₁_ne_p₂.symm
        hv₀_ne_p₁.symm hu₁_ne_p₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hp₂_p₁ hp₁_v₀ hu₁)
  have hu₁q₂ : adj u₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, u₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm
        hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₂ : adj p₁ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁] (by simp)
      (path_nodup4 _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges4 _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂_ne_q₁ : p₂ ≠ q₁ := by
    intro h; rw [h] at hv₀p₂; linarith [hq₁]
  have hp₂q₁ : adj p₂ q₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₁, v₀, p₁, p₂] (by simp)
      (path_nodup4 _ _ _ _ hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm
        hv₀_ne_p₁ hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges4 _ _ _ _ hq₁_v₀ hp₁ hp₂)
  have hq₁_ne_q₃ : q₁ ≠ q₃ := hq₃_ne_q₁.symm
  have hv₀q₃ : adj v₀ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀] (by simp)
      (path_nodup4 _ _ _ _ hq₂_ne_q₃.symm hq₃_ne_q₁ hv₀_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges4 _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₂_ne_q₄ : q₂ ≠ q₄ := hq₄_ne_q₂.symm
  have hq₁q₄ : adj q₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁] (by simp)
      (path_nodup4 _ _ _ _ hq₃_ne_q₄.symm hq₄_ne_q₂ hq₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₃_ne_q₁ hq₁_ne_q₂.symm)
      (path_edges4 _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  have hq₃_ne_q₅ : q₃ ≠ q₅ := hq₅_ne_q₃.symm
  have hq₂q₅ : adj q₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂] (by simp)
      (path_nodup4 _ _ _ _ hq₄_ne_q₅.symm hq₅_ne_q₃ hq₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₄_ne_q₂ hq₂_ne_q₃.symm)
      (path_edges4 _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂)
  -- Cross-arm ne (level 2)
  have hu₁_ne_q₃ : u₁ ≠ q₃ := by intro h; rw [h] at hu₁; linarith [hv₀q₃]
  have hp₁_ne_q₃ : p₁ ≠ q₃ := by intro h; rw [h] at hp₁; linarith [hv₀q₃]
  have hp₂_ne_q₂ : p₂ ≠ q₂ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₂, hp₁q₂]
  have hv₀_ne_q₄ : v₀ ≠ q₄ := by intro h; rw [← h] at hq₄; linarith [adj_comm q₃ v₀, hv₀q₃]
  have hq₁_ne_q₅ : q₁ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ q₁, hq₁q₄]
  -- Distance-4 non-edges (5-vertex paths)
  have hu₁q₃ : adj u₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₃ : adj p₁ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges5 _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₂ : adj p₂ q₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup5 _ _ _ _ _ hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges5 _ _ _ _ _ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₄ : adj v₀ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup5 _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges5 _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  have hq₁q₅ : adj q₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁] (by simp)
      (path_nodup5 _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hq₂_ne_q₃.symm hq₁_ne_q₃.symm hq₁_ne_q₂.symm)
      (path_edges5 _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁)
  -- Cross-arm ne (level 3)
  have hu₁_ne_q₄ : u₁ ≠ q₄ := by intro h; rw [h] at hu₁; linarith [hv₀q₄]
  have hp₁_ne_q₄ : p₁ ≠ q₄ := by intro h; rw [h] at hp₁; linarith [hv₀q₄]
  have hp₂_ne_q₃ : p₂ ≠ q₃ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₃, hp₁q₃]
  have hv₀_ne_q₅ : v₀ ≠ q₅ := by intro h; rw [← h] at hq₅; linarith [adj_comm q₄ v₀, hv₀q₄]
  -- Distance-5 non-edges (6-vertex paths)
  have hu₁q₄ : adj u₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₄ : adj p₁ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges6 _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₃ : adj p₂ q₃ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges6 _ _ _ _ _ _ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  have hv₀q₅ : adj v₀ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀] (by simp)
      (path_nodup6 _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hq₁_ne_q₂.symm hq₂_ne_v₀ hv₀_ne_q₁.symm)
      (path_edges6 _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀)
  -- Cross-arm ne (level 4)
  have hu₁_ne_q₅ : u₁ ≠ q₅ := by intro h; rw [h] at hu₁; linarith [hv₀q₅]
  have hp₁_ne_q₅ : p₁ ≠ q₅ := by intro h; rw [h] at hp₁; linarith [hv₀q₅]
  have hp₂_ne_q₄ : p₂ ≠ q₄ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₄, hp₁q₄]
  -- Distance-6 non-edges (7-vertex paths)
  have hu₁q₅ : adj u₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, u₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hu₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hu₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hu₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hu₁_ne_q₂.symm hv₀_ne_q₁.symm hu₁_ne_q₁.symm hv₀_ne_u₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hu₁)
  have hp₁q₅ : adj p₁ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hv₀_ne_q₁.symm hp₁_ne_q₁.symm hv₀_ne_p₁)
      (path_edges7 _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁)
  have hp₂q₄ : adj p₂ q₄ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup7 _ _ _ _ _ _ _ hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges7 _ _ _ _ _ _ _ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Cross-arm ne (level 5)
  have hp₂_ne_q₅ : p₂ ≠ q₅ := by intro h; rw [h] at hp₂; linarith [adj_comm p₁ q₅, hp₁q₅]
  -- Distance-7 non-edge (8-vertex path)
  have hp₂q₅ : adj p₂ q₅ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [q₅, q₄, q₃, q₂, q₁, v₀, p₁, p₂] (by simp)
      (path_nodup8 _ _ _ _ _ _ _ _
        hq₄_ne_q₅.symm hq₃_ne_q₅.symm hq₂_ne_q₅.symm hq₁_ne_q₅.symm hv₀_ne_q₅.symm hp₁_ne_q₅.symm hp₂_ne_q₅.symm
        hq₃_ne_q₄.symm hq₂_ne_q₄.symm hq₁_ne_q₄.symm hv₀_ne_q₄.symm hp₁_ne_q₄.symm hp₂_ne_q₄.symm
        hq₂_ne_q₃.symm hq₁_ne_q₃.symm hv₀_ne_q₃.symm hp₁_ne_q₃.symm hp₂_ne_q₃.symm
        hq₁_ne_q₂.symm hq₂_ne_v₀ hp₁_ne_q₂.symm hp₂_ne_q₂.symm
        hv₀_ne_q₁.symm hp₁_ne_q₁.symm hp₂_ne_q₁.symm hv₀_ne_p₁
        hp₂_ne_v₀.symm hp₁_ne_p₂)
      (path_edges8 _ _ _ _ _ _ _ _ hq₅_q₄ hq₄_q₃ hq₃_q₂ hq₂_q₁ hq₁_v₀ hp₁ hp₂)
  -- Construct the embedding φ : Fin 9 ↪ Fin n for T(1,2,5)
  -- Map: 0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅
  let φ_fun : Fin 9 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => p₁
    | ⟨3, _⟩ => p₂  | ⟨4, _⟩ => q₁  | ⟨5, _⟩ => q₂
    | ⟨6, _⟩ => q₃  | ⟨7, _⟩ => q₄  | ⟨8, _⟩ => q₅
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exact absurd hij ‹_›)
      | (exact absurd hij.symm ‹_›)
  let φ : Fin 9 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, t125Adj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t125Adj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag v₀, hdiag u₁, hdiag p₁, hdiag p₂,
        hdiag q₁, hdiag q₂, hdiag q₃, hdiag q₄, hdiag q₅,
        hu₁, hp₁, hp₂, hq₁, hq₂, hq₃, hq₄, hq₅,
        adj_comm v₀ u₁, adj_comm v₀ p₁, adj_comm v₀ p₂,
        adj_comm v₀ q₁, adj_comm v₀ q₂, adj_comm v₀ q₃,
        adj_comm v₀ q₄, adj_comm v₀ q₅,
        adj_comm u₁ p₁, adj_comm u₁ p₂,
        adj_comm u₁ q₁, adj_comm u₁ q₂, adj_comm u₁ q₃,
        adj_comm u₁ q₄, adj_comm u₁ q₅,
        adj_comm p₁ p₂, adj_comm p₁ q₁, adj_comm p₁ q₂,
        adj_comm p₁ q₃, adj_comm p₁ q₄, adj_comm p₁ q₅,
        adj_comm p₂ q₁, adj_comm p₂ q₂, adj_comm p₂ q₃,
        adj_comm p₂ q₄, adj_comm p₂ q₅,
        adj_comm q₁ q₂, adj_comm q₁ q₃, adj_comm q₁ q₄, adj_comm q₁ q₅,
        adj_comm q₂ q₃, adj_comm q₂ q₄, adj_comm q₂ q₅,
        adj_comm q₃ q₄, adj_comm q₃ q₅,
        adj_comm q₄ q₅,
        hu₁p₁, hu₁q₁, hp₁q₁, hv₀p₂, hv₀q₂, hq₁q₃, hq₂q₄, hq₃q₅,
        hu₁p₂, hu₁q₂, hp₁q₂, hp₂q₁, hv₀q₃, hq₁q₄, hq₂q₅,
        hu₁q₃, hp₁q₃, hp₂q₂, hv₀q₄, hq₁q₅,
        hu₁q₄, hp₁q₄, hp₂q₃, hv₀q₅,
        hu₁q₅, hp₁q₅, hp₂q₄,
        hp₂q₅]
  exact subgraph_infinite_type_transfer φ adj t125Adj hsymm
    (fun v h => by linarith [hdiag v]) hembed t125_not_finite_type

/-- Removing a degree-1 vertex from a connected tree preserves list-based connectivity
    in the reduced graph (via succAbove). -/
private lemma connected_remove_leaf {m : ℕ}
    (adj : Matrix (Fin (m+1)) (Fin (m+1)) ℤ)
    (e : Fin (m+1))
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin (m+1), ∃ path : List (Fin (m+1)),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (he_deg : vertexDegree adj e = 1) :
    ∀ i j : Fin m, ∃ path : List (Fin m),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (e.succAbove (path.get ⟨k, by omega⟩))
          (e.succAbove (path.get ⟨k + 1, h⟩)) = 1 := by
  -- Build SimpleGraph from adj
  let G : SimpleGraph (Fin (m + 1)) :=
    { Adj := fun i j => adj i j = 1
      symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
      loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
  haveI : DecidableRel G.Adj :=
    fun i j => show Decidable (adj i j = 1) from inferInstance
  -- G is connected
  have hG_conn : G.Connected := by
    constructor
    intro u v
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
    suffices h : ∀ (l : List (Fin (m + 1))) (a b : Fin (m + 1)),
        l.head? = some a → l.getLast? = some b →
        (∀ k, (hk : k + 1 < l.length) →
          adj (l.get ⟨k, by omega⟩) (l.get ⟨k + 1, hk⟩) = 1) →
        G.Reachable a b from h path u v hhead hlast hedges
    intro l; induction l with
    | nil => intro a _ ha; simp at ha
    | cons x t ih =>
      intro a b ha hb hedges'
      simp at ha; subst ha
      cases t with
      | nil => simp at hb; subst hb; exact SimpleGraph.Reachable.refl _
      | cons y s =>
        have hxy : G.Adj x y := hedges' 0 (by simp)
        exact hxy.reachable.trans
          (ih y b (by simp) hb (fun k hk => hedges' (k + 1)
            (by simp only [List.length_cons] at hk ⊢; omega)))
  -- G has degree 1 at e
  have hG_deg : G.degree e = 1 := by
    unfold SimpleGraph.degree
    have heq : G.neighborFinset e = Finset.univ.filter (adj e · = 1) := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨fun h => h, fun h => h⟩
    rw [heq]; unfold vertexDegree at he_deg; convert he_deg
  -- Apply Mathlib: removing e preserves connectivity
  have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
  -- Convert: G.induce {e}ᶜ connectivity → adj' connectivity
  intro i j
  have hu_ne : e.succAbove i ≠ e := Fin.succAbove_ne e i
  have hw_ne : e.succAbove j ≠ e := Fin.succAbove_ne e j
  have hu_mem : e.succAbove i ∈ ({e}ᶜ : Set (Fin (m + 1))) :=
    Set.mem_compl_singleton_iff.mpr hu_ne
  have hw_mem : e.succAbove j ∈ ({e}ᶜ : Set (Fin (m + 1))) :=
    Set.mem_compl_singleton_iff.mpr hw_ne
  obtain ⟨walk⟩ := hG'.preconnected ⟨e.succAbove i, hu_mem⟩ ⟨e.succAbove j, hw_mem⟩
  -- Map vertices in {e}ᶜ to Fin m via succAbove inverse
  let toFinm : ↥({e}ᶜ : Set (Fin (m + 1))) → Fin m :=
    fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
      (Set.mem_compl_singleton_iff.mp hv)).choose
  have htoFinm_spec : ∀ (x : ↥({e}ᶜ : Set (Fin (m + 1)))),
      e.succAbove (toFinm x) = x.val :=
    fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
      (Set.mem_compl_singleton_iff.mp hv)).choose_spec
  have htoFinm_adj : ∀ (x y : ↥({e}ᶜ : Set (Fin (m + 1)))),
      (G.induce ({e}ᶜ : Set _)).Adj x y →
      adj (e.succAbove (toFinm x)) (e.succAbove (toFinm y)) = 1 := by
    intro x y hadj_xy
    rw [htoFinm_spec x, htoFinm_spec y]; exact hadj_xy
  -- Build path by induction on the walk
  suffices h_walk : ∀ (a b : ↥({e}ᶜ : Set (Fin (m + 1))))
      (w' : (G.induce ({e}ᶜ : Set _)).Walk a b),
    ∃ path : List (Fin m),
      path.head? = some (toFinm a) ∧
      path.getLast? = some (toFinm b) ∧
      ∀ k, (hk : k + 1 < path.length) →
        adj (e.succAbove (path.get ⟨k, by omega⟩))
          (e.succAbove (path.get ⟨k + 1, hk⟩)) = 1 by
    obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
    refine ⟨path, ?_, ?_, hedges⟩
    · convert hhead using 2
      exact (Fin.succAbove_right_injective
        (htoFinm_spec ⟨e.succAbove i, hu_mem⟩)).symm
    · convert hlast using 2
      exact (Fin.succAbove_right_injective
        (htoFinm_spec ⟨e.succAbove j, hw_mem⟩)).symm
  intro a b w'
  induction w' with
  | nil =>
    exact ⟨[toFinm _], rfl, rfl, fun k hk => absurd hk (by simp)⟩
  | @cons c d _ hadj_edge rest ih =>
    obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
    refine ⟨toFinm c :: path_rest, by simp, ?_, ?_⟩
    · -- getLast?
      cases path_rest with
      | nil => simp at hhead_rest hlast_rest ⊢
      | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
    · -- Consecutive adjacency
      intro k hk
      match k with
      | 0 =>
        simp only [List.get_eq_getElem, List.getElem_cons_zero,
          List.getElem_cons_succ]
        have h0 : 0 < path_rest.length := by
          simp only [List.length_cons] at hk; omega
        have hd_eq : path_rest[0] = toFinm d := by
          cases path_rest with
          | nil => simp at h0
          | cons y ys =>
            simp only [List.head?, Option.some.injEq] at hhead_rest
            simp only [List.getElem_cons_zero]
            exact hhead_rest
        rw [hd_eq]
        exact htoFinm_adj c d hadj_edge
      | k' + 1 =>
        simp only [List.get_eq_getElem, List.getElem_cons_succ]
        exact hedges_rest k' (by simp only [List.length_cons] at hk; omega)

set_option maxHeartbeats 1600000 in
/-- In a tree where v₀ has two degree-1 neighbors L1 and L2, the Cartan form is positive definite.
    After removing L1 and L2, v₀ becomes a leaf of the resulting path graph.
    Key identity: Q(x) = Q_path(x_rest) - V² + (V - L - A)² + (L - A)²
    where V = x(v₀), L = x(L1), A = x(L2), and Q_path is the path's Cartan form. -/
private lemma tree_two_leaf_posdef {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ L1 L2 : Fin n)
    (hL1_adj : adj v₀ L1 = 1) (hL1_deg : vertexDegree adj L1 = 1)
    (hL2_adj : adj v₀ L2 = 1) (hL2_deg : vertexDegree adj L2 = 1)
    (hL1L2 : L1 ≠ L2) (hL1_ne_v₀ : L1 ≠ v₀) (hL2_ne_v₀ : L2 ≠ v₀)
    (h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  -- L1 only connects to v₀
  have hL1_unique : ∀ j, adj L1 j = if j = v₀ then 1 else 0 := by
    intro j; by_cases hj : j = v₀
    · simp only [hj, ite_true]; exact (hsymm.apply v₀ L1).trans hL1_adj
    · rcases h01 L1 j with h | h
      · simp [hj, h]
      · exfalso; have : 2 ≤ vertexDegree adj L1 := by
          change 2 ≤ (Finset.univ.filter (fun k => adj L1 k = 1)).card
          have hv₀_in : v₀ ∈ Finset.univ.filter (fun k => adj L1 k = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsymm.apply v₀ L1).trans hL1_adj⟩
          have hj_in : j ∈ Finset.univ.filter (fun k => adj L1 k = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          have hne : v₀ ≠ j := Ne.symm hj
          calc 2 = ({v₀, j} : Finset _).card := by
                    rw [Finset.card_pair hne]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
  -- L2 only connects to v₀
  have hL2_unique : ∀ j, adj L2 j = if j = v₀ then 1 else 0 := by
    intro j; by_cases hj : j = v₀
    · simp only [hj, ite_true]; exact (hsymm.apply v₀ L2).trans hL2_adj
    · rcases h01 L2 j with h | h
      · simp [hj, h]
      · exfalso; have : 2 ≤ vertexDegree adj L2 := by
          change 2 ≤ (Finset.univ.filter (fun k => adj L2 k = 1)).card
          have hv₀_in : v₀ ∈ Finset.univ.filter (fun k => adj L2 k = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsymm.apply v₀ L2).trans hL2_adj⟩
          have hj_in : j ∈ Finset.univ.filter (fun k => adj L2 k = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          have hne : v₀ ≠ j := Ne.symm hj
          calc 2 = ({v₀, j} : Finset _).card := by
                    rw [Finset.card_pair hne]
            _ ≤ _ := Finset.card_le_card (fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption)
        omega
  intro x hx
  -- Set up key variables
  set V := x v₀ with hV_def
  set L := x L1 with hL_def
  set A := x L2 with hA_def
  -- Zero out both leaves
  set x₀₀ : Fin n → ℤ := fun i => if i = L1 ∨ i = L2 then 0 else x i with hx₀₀_def
  have hx₀₀_L1 : x₀₀ L1 = 0 := by simp [x₀₀]
  have hx₀₀_L2 : x₀₀ L2 = 0 := by simp [x₀₀, hL1L2]
  have hx₀₀_v₀ : x₀₀ v₀ = V := by
    show (if v₀ = L1 ∨ v₀ = L2 then 0 else x v₀) = V
    rw [if_neg (by push_neg; exact ⟨Ne.symm hL1_ne_v₀, Ne.symm hL2_ne_v₀⟩)]
  have hx₀₀_else : ∀ i, i ≠ L1 → i ≠ L2 → x₀₀ i = x i := by
    intro i h1 h2; simp [x₀₀, h1, h2]
  -- adj L1 L2 = 0 (L1 is a leaf connected only to v₀, and L2 ≠ v₀)
  have hL1L2_adj : adj L1 L2 = 0 := by
    rcases h01 L1 L2 with h | h; exact h
    have := hL1_unique L2; rw [if_neg hL2_ne_v₀] at this; omega
  have hL2L1_adj : adj L2 L1 = 0 := by
    have := hsymm.apply L1 L2; rw [hL1L2_adj] at this; linarith
  -- adj symmetry helpers
  have h_adj_i_L1 : ∀ i, adj i L1 = if i = v₀ then 1 else 0 := by
    intro i; rw [hsymm.apply]; exact hL1_unique i
  have h_adj_i_L2 : ∀ i, adj i L2 = if i = v₀ then 1 else 0 := by
    intro i; rw [hsymm.apply]; exact hL2_unique i
  -- Step 1: Algebraic decomposition
  -- Q(x) = Q(x₀₀) + 2L² + 2A² - 2LV - 2AV
  have h_decomp : QF adj x = QF adj x₀₀ +
      2 * L ^ 2 + 2 * A ^ 2 - 2 * L * V - 2 * A * V := by
    -- Helper: evaluate sum with two nonzero terms
    have sum_two : ∀ (a b : Fin n) (f : Fin n → ℤ), a ≠ b →
        (∀ i, i ≠ a → i ≠ b → f i = 0) →
        ∑ i : Fin n, f i = f a + f b := by
      intro a b f hab hf
      have hb_mem : b ∈ Finset.univ.erase a :=
        Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)]
      congr 1
      rw [← Finset.add_sum_erase (Finset.univ.erase a) f hb_mem]
      suffices ∑ i ∈ (Finset.univ.erase a).erase b, f i = 0 by linarith
      exact Finset.sum_eq_zero fun i hi => by
        simp only [Finset.mem_erase] at hi; exact hf i hi.2.1 hi.1
    suffices h : QF adj x - QF adj x₀₀ =
        2 * L ^ 2 + 2 * A ^ 2 - 2 * L * V - 2 * A * V by linarith
    simp only [QF, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply]
    rw [← Finset.sum_sub_distrib]
    have haL1v₀ : adj L1 v₀ = 1 := by rw [hsymm.apply]; exact hL1_adj
    have haL2v₀ : adj L2 v₀ = 1 := by rw [hsymm.apply]; exact hL2_adj
    -- Evaluate inner(x, L1) = 2L - V via indicator decomposition
    have inner_x_L1 : ∑ j : Fin n,
        ((2 • if L1 = j then (1 : ℤ) else 0) - adj L1 j) * x j =
        2 * L - V := by
      have hf : ∀ k, ((2 • if L1 = k then (1 : ℤ) else 0) - adj L1 k) * x k =
          (if k = L1 then 2 * L else 0) + (if k = v₀ then -V else 0) := by
        intro k
        by_cases hk1 : k = L1
        · rw [hk1]; simp [hdiag, hL1_ne_v₀, ← hL_def]
        · by_cases hkv : k = v₀
          · rw [hkv]; simp [hL1_ne_v₀, Ne.symm hL1_ne_v₀, haL1v₀, ← hV_def]
          · have := hL1_unique k; rw [if_neg hkv] at this
            simp [Ne.symm hk1, hk1, hkv, this]
      simp_rw [hf, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; ring
    -- Evaluate inner(x, L2) = 2A - V
    have inner_x_L2 : ∑ j : Fin n,
        ((2 • if L2 = j then (1 : ℤ) else 0) - adj L2 j) * x j =
        2 * A - V := by
      have hf : ∀ k, ((2 • if L2 = k then (1 : ℤ) else 0) - adj L2 k) * x k =
          (if k = L2 then 2 * A else 0) + (if k = v₀ then -V else 0) := by
        intro k
        by_cases hk2 : k = L2
        · rw [hk2]; simp [hdiag, hL2_ne_v₀, ← hA_def]
        · by_cases hkv : k = v₀
          · rw [hkv]; simp [hL2_ne_v₀, Ne.symm hL2_ne_v₀, haL2v₀, ← hV_def]
          · have := hL2_unique k; rw [if_neg hkv] at this
            simp [Ne.symm hk2, hk2, hkv, this]
      simp_rw [hf, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; ring
    -- Per-term difference decomposed into three indicator functions
    have hterm : ∀ i : Fin n,
        x i * ∑ j, ((2 • if i = j then (1 : ℤ) else 0) - adj i j) * x j -
        x₀₀ i * ∑ j, ((2 • if i = j then (1 : ℤ) else 0) - adj i j) * x₀₀ j =
        (if i = L1 then 2 * L ^ 2 - L * V else 0) +
        (if i = L2 then 2 * A ^ 2 - A * V else 0) +
        (if i = v₀ then -(V * L) - V * A else 0) := by
      intro i
      by_cases hi1 : i = L1
      · subst hi1
        simp only [hx₀₀_L1, zero_mul, sub_zero, ite_true, hL1L2, hL1_ne_v₀, ite_false]
        rw [inner_x_L1]; ring
      · by_cases hi2 : i = L2
        · subst hi2
          simp only [hx₀₀_L2, zero_mul, sub_zero, hi1, ite_false, ite_true, hL2_ne_v₀]
          rw [inner_x_L2]; ring
        · by_cases hiv : i = v₀
          · rw [hiv]
            simp only [hi1, hi2, ite_false, ite_true, hx₀₀_v₀]
            have hrw1 : V * ∑ j, ((2 • if v₀ = j then (1 : ℤ) else 0) - adj v₀ j) * x j -
                V * ∑ j, ((2 • if v₀ = j then (1 : ℤ) else 0) - adj v₀ j) * x₀₀ j =
                V * ∑ j, ((2 • if v₀ = j then (1 : ℤ) else 0) - adj v₀ j) *
                  (x j - x₀₀ j) := by
              rw [← mul_sub, ← Finset.sum_sub_distrib]; congr 1
              apply Finset.sum_congr rfl; intro k _; ring
            rw [hrw1]
            rw [sum_two L1 L2 _ hL1L2 (by
              intro k hk1 hk2; rw [hx₀₀_else k hk1 hk2]; ring)]
            simp only [Ne.symm hL1_ne_v₀, Ne.symm hL2_ne_v₀, hL1_adj, hL2_adj,
              hx₀₀_L1, hx₀₀_L2, ite_false, ← hL_def, ← hA_def]; ring
          · -- i ≠ L1, L2, v₀: all three indicators are 0
            simp only [hi1, hi2, hiv, ite_false, add_zero]
            rw [← hx₀₀_else i hi1 hi2]
            have hrw2 : x₀₀ i * ∑ j, ((2 • if i = j then (1 : ℤ) else 0) - adj i j) * x j -
                x₀₀ i * ∑ j, ((2 • if i = j then (1 : ℤ) else 0) - adj i j) * x₀₀ j =
                x₀₀ i * ∑ j, ((2 • if i = j then (1 : ℤ) else 0) - adj i j) *
                  (x j - x₀₀ j) := by
              rw [← mul_sub, ← Finset.sum_sub_distrib]; congr 1
              apply Finset.sum_congr rfl; intro k _; ring
            rw [hrw2]
            rw [sum_two L1 L2 _ hL1L2 (by
              intro k hk1 hk2; rw [hx₀₀_else k hk1 hk2]; ring)]
            simp only [hx₀₀_L1, hx₀₀_L2, hi1, hi2, ite_false,
              h_adj_i_L1 i, h_adj_i_L2 i, hiv]; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  -- Step 2: Bound on Q(x₀₀) via reduced path graph
  -- Strategy: Remove L1, L2 via two Fin.succAbove operations to get adj₂ on Fin (n-2).
  -- Since x₀₀(L1) = x₀₀(L2) = 0, QF adj x₀₀ = QF adj₂ x₂ (transfer via
  -- Fin.sum_univ_succAbove). Then adj₂ is a path graph with v₀ as leaf, and
  -- acyclic_path_posdef_aux gives V² ≤ QF adj₂ x₂ and strict when x₂ ≠ 0.
  -- Parts 1 & 2: Obtain both bounds via reduced graph (removing L1 and L2)
  obtain ⟨h_bound, h_strict⟩ :
      V ^ 2 ≤ QF adj x₀₀ ∧ (x₀₀ ≠ 0 → V ^ 2 < QF adj x₀₀) := by
    -- Establish n ≥ 3 from distinctness of L1, L2, v₀
    have hn3 : 3 ≤ n := by
      have h2 : L2 ∉ ({v₀} : Finset (Fin n)) := by
        simp only [Finset.mem_singleton]; exact hL2_ne_v₀
      have h1 : L1 ∉ ({L2, v₀} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hL1L2, hL1_ne_v₀⟩
      calc 3 = ({L1, L2, v₀} : Finset (Fin n)).card := by
            rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
                Finset.card_singleton]
        _ ≤ Finset.univ.card := Finset.card_le_univ _
        _ = n := by simp [Fintype.card_fin]
    -- Rewrite n as k + 3 for succAbove type-checking
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    -- === Step 1: Remove L1, get adj₁ on Fin (k+2) ===
    set adj₁ : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
      fun i j => adj (L1.succAbove i) (L1.succAbove j) with hadj₁_def
    set x₁ : Fin (k + 2) → ℤ := fun i => x₀₀ (L1.succAbove i) with hx₁_def
    -- QF transfer: QF adj x₀₀ = QF adj₁ x₁ (since x₀₀(L1) = 0)
    have h_transfer1 : QF adj x₀₀ = QF adj₁ x₁ := by
      simp only [QF, dotProduct, Matrix.mulVec]
      conv_lhs => rw [Fin.sum_univ_succAbove _ L1]
      simp only [hx₀₀_L1, zero_mul, zero_add]
      apply Finset.sum_congr rfl; intro i _
      change x₀₀ (L1.succAbove i) * _ = x₀₀ (L1.succAbove i) * _
      congr 1
      conv_lhs => rw [Fin.sum_univ_succAbove _ L1]
      simp only [hx₀₀_L1, mul_zero, zero_add]
      apply Finset.sum_congr rfl; intro j _
      change _ * x₀₀ (L1.succAbove j) = _ * x₀₀ (L1.succAbove j)
      congr 1
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj₁_def,
        Fin.succAbove_right_inj, smul_eq_mul]
    -- Find L2 and v₀ in Fin (k+2)
    obtain ⟨L2', hL2'⟩ := Fin.exists_succAbove_eq (Ne.symm hL1L2 : L2 ≠ L1)
    obtain ⟨v₀', hv₀'⟩ := Fin.exists_succAbove_eq (Ne.symm hL1_ne_v₀ : v₀ ≠ L1)
    have hx₁_L2' : x₁ L2' = 0 := by show x₀₀ (L1.succAbove L2') = 0; rw [hL2']; exact hx₀₀_L2
    have hx₁_v₀' : x₁ v₀' = V := by show x₀₀ (L1.succAbove v₀') = V; rw [hv₀']; exact hx₀₀_v₀
    -- Adj₁ properties
    have hsymm₁ : adj₁.IsSymm := Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
    have hdiag₁ : ∀ i, adj₁ i i = 0 := fun i => hdiag _
    have h01₁ : ∀ i j, adj₁ i j = 0 ∨ adj₁ i j = 1 := fun i j => h01 _ _
    -- Connectivity preserved (L1 is degree 1)
    have hconn₁ := connected_remove_leaf adj L1 hsymm hdiag h01 hconn
      (by rw [hL1_deg])
    -- Acyclicity preserved
    have h_acyclic₁ : ∀ (cycle : List (Fin (k+2))) (hclen : 3 ≤ cycle.length), cycle.Nodup →
        (∀ m, (h : m + 1 < cycle.length) →
          adj₁ (cycle.get ⟨m, by omega⟩) (cycle.get ⟨m + 1, h⟩) = 1) →
        adj₁ (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
          (cycle.get ⟨0, by omega⟩) ≠ 1 := by
      intro cycle hclen hnodup hedges hlast
      set cycle' := cycle.map L1.succAbove
      have hlen' : cycle'.length = cycle.length := List.length_map ..
      have hget' : ∀ (p : ℕ) (hp : p < cycle'.length),
          cycle'.get ⟨p, hp⟩ =
          L1.succAbove (cycle.get ⟨p, by rw [hlen'] at hp; exact hp⟩) :=
        fun p hp => List.getElem_map ..
      apply h_acyclic cycle' (by omega)
      · exact hnodup.map Fin.succAbove_right_injective
      · intro m hm; rw [hget', hget']
        exact hedges m (by rw [hlen'] at hm; omega)
      · simp only [cycle', List.getLast_map]; rw [hget']
        exact hlast
    -- L2' has degree 1 in adj₁ (L2 only connects to v₀, so L2' only connects to v₀')
    have hL2'_deg : vertexDegree adj₁ L2' = 1 := by
      unfold vertexDegree
      have hfilt : Finset.univ.filter (fun j => adj₁ L2' j = 1) = {v₀'} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          have hadj_eq : adj L2 (L1.succAbove j) = 1 := by
            change adj (L1.succAbove L2') (L1.succAbove j) = 1 at h; rwa [hL2'] at h
          have h3 : L1.succAbove j = v₀ := by
            have h2 := hL2_unique (L1.succAbove j)
            rw [hadj_eq] at h2
            by_contra h_ne; rw [if_neg h_ne] at h2; exact one_ne_zero h2
          exact Fin.succAbove_right_injective (h3.trans hv₀'.symm)
        · intro hj; rw [hj]
          show adj (L1.succAbove L2') (L1.succAbove v₀') = 1
          rw [hL2', hv₀']; exact (hsymm.apply v₀ L2).trans hL2_adj
      rw [hfilt, Finset.card_singleton]
    -- === Step 2: Remove L2', get adj₂ on Fin (k+1) ===
    set adj₂ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
      fun i j => adj₁ (L2'.succAbove i) (L2'.succAbove j) with hadj₂_def
    set x₂ : Fin (k + 1) → ℤ := fun i => x₁ (L2'.succAbove i) with hx₂_def
    -- QF transfer: QF adj₁ x₁ = QF adj₂ x₂ (since x₁(L2') = 0)
    have h_transfer2 : QF adj₁ x₁ = QF adj₂ x₂ := by
      simp only [QF, dotProduct, Matrix.mulVec]
      conv_lhs => rw [Fin.sum_univ_succAbove _ L2']
      simp only [hx₁_L2', zero_mul, zero_add]
      apply Finset.sum_congr rfl; intro i _
      change x₁ (L2'.succAbove i) * _ = x₁ (L2'.succAbove i) * _
      congr 1
      conv_lhs => rw [Fin.sum_univ_succAbove _ L2']
      simp only [hx₁_L2', mul_zero, zero_add]
      apply Finset.sum_congr rfl; intro j _
      change _ * x₁ (L2'.succAbove j) = _ * x₁ (L2'.succAbove j)
      congr 1
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj₂_def,
        Fin.succAbove_right_inj, smul_eq_mul]
    -- Combined transfer
    have h_transfer : QF adj x₀₀ = QF adj₂ x₂ := by rw [h_transfer1, h_transfer2]
    -- Find v₀ in Fin (k+1)
    have hv₀'_ne_L2' : v₀' ≠ L2' := by
      intro h; rw [h] at hv₀'
      have : L1.succAbove L2' = v₀ := hv₀'
      rw [hL2'] at this; exact hL2_ne_v₀ this
    obtain ⟨v₀'', hv₀''⟩ := Fin.exists_succAbove_eq hv₀'_ne_L2'
    have hx₂_v₀'' : x₂ v₀'' = V := by
      show x₁ (L2'.succAbove v₀'') = V; rw [hv₀'']; exact hx₁_v₀'
    -- Adj₂ properties
    have hsymm₂ : adj₂.IsSymm := Matrix.IsSymm.ext (fun i j => hsymm₁.apply _ _)
    have hdiag₂ : ∀ i, adj₂ i i = 0 := fun i => hdiag₁ _
    have h01₂ : ∀ i j, adj₂ i j = 0 ∨ adj₂ i j = 1 := fun i j => h01₁ _ _
    -- Connectivity preserved (L2' is degree 1)
    have hconn₂ := connected_remove_leaf adj₁ L2' hsymm₁ hdiag₁ h01₁ hconn₁ hL2'_deg
    -- Acyclicity preserved
    have h_acyclic₂ : ∀ (cycle : List (Fin (k+1))) (hclen : 3 ≤ cycle.length), cycle.Nodup →
        (∀ m, (h : m + 1 < cycle.length) →
          adj₂ (cycle.get ⟨m, by omega⟩) (cycle.get ⟨m + 1, h⟩) = 1) →
        adj₂ (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
          (cycle.get ⟨0, by omega⟩) ≠ 1 := by
      intro cycle hclen hnodup hedges hlast
      set cycle' := cycle.map L2'.succAbove
      have hlen' : cycle'.length = cycle.length := List.length_map ..
      have hget' : ∀ (p : ℕ) (hp : p < cycle'.length),
          cycle'.get ⟨p, hp⟩ =
          L2'.succAbove (cycle.get ⟨p, by rw [hlen'] at hp; exact hp⟩) :=
        fun p hp => List.getElem_map ..
      apply h_acyclic₁ cycle' (by omega)
      · exact hnodup.map Fin.succAbove_right_injective
      · intro m hm; rw [hget', hget']
        exact hedges m (by rw [hlen'] at hm; omega)
      · simp only [cycle', List.getLast_map]; rw [hget']
        exact hlast
    -- Degree bound: all vertices in adj₂ have degree < 3
    have h_deg₂ : ∀ v, vertexDegree adj₂ v < 3 := by
      intro v
      unfold vertexDegree
      -- vertexDegree adj₂ v ≤ vertexDegree adj₁ (L2'.succAbove v)
      have h_le : (Finset.univ.filter (fun j => adj₂ v j = 1)).card ≤
          (Finset.univ.filter (fun j => adj₁ (L2'.succAbove v) j = 1)).card := by
        have h_image : ((Finset.univ.filter (fun j : Fin (k+1) => adj₂ v j = 1)).image
            L2'.succAbove) ⊆
            Finset.univ.filter (fun j : Fin (k+2) => adj₁ (L2'.succAbove v) j = 1) :=
          fun x hx => by
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            obtain ⟨y, hy, rfl⟩ := hx; exact hy
        calc _ = ((Finset.univ.filter (fun j : Fin (k+1) => adj₂ v j = 1)).image
              L2'.succAbove).card :=
              (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
          _ ≤ _ := Finset.card_le_card h_image
      -- vertexDegree adj₁ (L2'.succAbove v) ≤ vertexDegree adj (L1.succAbove (L2'.succAbove v))
      have h_le₁ : (Finset.univ.filter (fun j => adj₁ (L2'.succAbove v) j = 1)).card ≤
          (Finset.univ.filter (fun j => adj (L1.succAbove (L2'.succAbove v)) j = 1)).card := by
        have h_image : ((Finset.univ.filter (fun j : Fin (k+2) =>
            adj₁ (L2'.succAbove v) j = 1)).image L1.succAbove) ⊆
            Finset.univ.filter (fun j : Fin (k+3) =>
              adj (L1.succAbove (L2'.succAbove v)) j = 1) :=
          fun x hx => by
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            obtain ⟨y, hy, rfl⟩ := hx; exact hy
        calc _ = ((Finset.univ.filter (fun j : Fin (k+2) =>
                adj₁ (L2'.succAbove v) j = 1)).image L1.succAbove).card :=
              (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
          _ ≤ _ := Finset.card_le_card h_image
      -- The original vertex has degree < 4, plus we can do better for non-v₀ vertices
      have h_orig := h_deg (L1.succAbove (L2'.succAbove v))
      by_cases hv_v₀ : L2'.succAbove v = v₀'
      · -- This vertex maps to v₀: tighten h_le by subtracting L2'
        rw [hv_v₀] at h_le₁ h_le
        rw [hv₀'] at h_le₁
        rw [hv_v₀, hv₀'] at h_orig
        unfold vertexDegree at h_orig
        -- Tighter: adj₂ ≤ adj₁ v₀' - 1 (L2' is neighbor of v₀' but not in succAbove range)
        have h_le_tight : (Finset.univ.filter (fun j => adj₂ v j = 1)).card ≤
            ((Finset.univ.filter (fun j => adj₁ v₀' j = 1)).erase L2').card := by
          have h_image : ((Finset.univ.filter (fun j : Fin (k+1) =>
              adj₂ v j = 1)).image L2'.succAbove) ⊆
              (Finset.univ.filter (fun j : Fin (k+2) => adj₁ v₀' j = 1)).erase L2' :=
            fun x hx => by
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne L2' y, by
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_v₀ ▸ hy⟩⟩
          calc _ = ((Finset.univ.filter (fun j : Fin (k+1) =>
                  adj₂ v j = 1)).image L2'.succAbove).card :=
                (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
            _ ≤ _ := Finset.card_le_card h_image
        have hv₀'_L2' : adj₁ v₀' L2' = 1 := by
          show adj (L1.succAbove v₀') (L1.succAbove L2') = 1
          rw [hv₀', hL2']; exact hL2_adj
        have hL2'_mem : L2' ∈ Finset.univ.filter (fun j => adj₁ v₀' j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀'_L2'⟩
        rw [Finset.card_erase_of_mem hL2'_mem] at h_le_tight
        omega
      · -- This vertex is not v₀: degree ≤ 2 in adj (by h_deg_le2)
        have hne_v₀ : L1.succAbove (L2'.succAbove v) ≠ v₀ := by
          intro h; exact hv_v₀ (Fin.succAbove_right_injective (h.trans hv₀'.symm))
        have := h_deg_le2 _ hne_v₀
        unfold vertexDegree at this h_orig
        omega
    -- v₀'' is a leaf in adj₂ (degree ≤ 1)
    have hv₀''_deg : vertexDegree adj₂ v₀'' ≤ 1 := by
      unfold vertexDegree
      -- vertexDegree adj₂ v₀'' ≤ vertexDegree adj₁ v₀' - 1
      -- (because adj₁ v₀' L2' = 1 and L2' is not in the image of L2'.succAbove)
      have h_le : (Finset.univ.filter (fun j => adj₂ v₀'' j = 1)).card ≤
          ((Finset.univ.filter (fun j => adj₁ v₀' j = 1)).erase L2').card := by
        have h_image : ((Finset.univ.filter (fun j : Fin (k+1) =>
            adj₂ v₀'' j = 1)).image L2'.succAbove) ⊆
            (Finset.univ.filter (fun j : Fin (k+2) => adj₁ v₀' j = 1)).erase L2' :=
          fun x hx => by
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne L2' y, by
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀'' ▸ hy⟩⟩
        calc _ = ((Finset.univ.filter (fun j : Fin (k+1) =>
                adj₂ v₀'' j = 1)).image L2'.succAbove).card :=
              (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
          _ ≤ _ := Finset.card_le_card h_image
      -- adj₁ v₀' L2' = 1 (v₀ is adjacent to L2 in adj, so v₀' adjacent to L2' in adj₁)
      have hv₀'_L2' : adj₁ v₀' L2' = 1 := by
        show adj (L1.succAbove v₀') (L1.succAbove L2') = 1
        rw [hv₀', hL2']; exact hL2_adj
      have hL2'_mem : L2' ∈ Finset.univ.filter (fun j => adj₁ v₀' j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀'_L2'⟩
      rw [Finset.card_erase_of_mem hL2'_mem] at h_le
      -- vertexDegree adj₁ v₀' ≤ vertexDegree adj v₀ - 1 (because L1 is lost)
      have h_le₁ : (Finset.univ.filter (fun j => adj₁ v₀' j = 1)).card ≤
          ((Finset.univ.filter (fun j => adj v₀ j = 1)).erase L1).card := by
        have h_image : ((Finset.univ.filter (fun j : Fin (k+2) =>
            adj₁ v₀' j = 1)).image L1.succAbove) ⊆
            (Finset.univ.filter (fun j : Fin (k+3) => adj v₀ j = 1)).erase L1 :=
          fun x hx => by
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne L1 y, by
              change adj (L1.succAbove v₀') (L1.succAbove y) = 1 at hy
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv₀'] at hy; exact hy⟩⟩
        calc _ = ((Finset.univ.filter (fun j : Fin (k+2) =>
                adj₁ v₀' j = 1)).image L1.succAbove).card :=
              (Finset.card_image_of_injective _ Fin.succAbove_right_injective).symm
          _ ≤ _ := Finset.card_le_card h_image
      have hL1_mem : L1 ∈ Finset.univ.filter (fun j => adj v₀ j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL1_adj⟩
      rw [Finset.card_erase_of_mem hL1_mem] at h_le₁
      have h_v₀_deg := h_deg v₀
      unfold vertexDegree at h_v₀_deg
      omega
    -- Need 1 ≤ k + 1 for acyclic_path_posdef_aux
    have hk1 : 1 ≤ k + 1 := by omega
    -- === Step 3: Apply acyclic_path_posdef_aux ===
    obtain ⟨ih_lb, _, ih_strict⟩ := acyclic_path_posdef_aux (k + 1) adj₂ v₀''
      hsymm₂ hdiag₂ h01₂ hconn₂ h_acyclic₂ h_deg₂ hv₀''_deg
    constructor
    · -- h_bound: V² ≤ QF adj x₀₀
      rw [h_transfer, ← hx₂_v₀'']
      exact ih_lb x₂
    · -- h_strict: x₀₀ ≠ 0 → V² < QF adj x₀₀
      intro hx₀₀_ne
      rw [h_transfer, ← hx₂_v₀'']
      apply ih_strict x₂
      -- Show x₂ ≠ 0 from x₀₀ ≠ 0
      intro hx₂_z; apply hx₀₀_ne; ext i
      by_cases hi1 : i = L1
      · exact hi1 ▸ hx₀₀_L1
      · by_cases hi2 : i = L2
        · exact hi2 ▸ hx₀₀_L2
        · obtain ⟨i₁, hi₁⟩ := Fin.exists_succAbove_eq (show i ≠ L1 from hi1)
          have hi₁_ne : i₁ ≠ L2' := by
            intro h; rw [h, hL2'] at hi₁; exact hi2 hi₁.symm
          obtain ⟨i₂, hi₂⟩ := Fin.exists_succAbove_eq hi₁_ne
          have := congr_fun hx₂_z i₂
          simp only [hx₂_def, hi₂, hx₁_def, hi₁, Pi.zero_apply] at this
          simp only [Pi.zero_apply]; exact this
  -- Step 3: Combine using SoS identity
  -- 2L² + 2A² - 2LV - 2AV = (V-L-A)² + (L-A)² - V²
  -- So Q(x) = Q(x₀₀) - V² + (V-L-A)² + (L-A)²
  by_cases hx₀₀_z : x₀₀ = 0
  · -- All non-{L1, L2} values zero: V = 0
    have hV0 : V = 0 := by
      rw [← hx₀₀_v₀]; exact congr_fun hx₀₀_z v₀
    -- Q(x) = 0 + 2L² + 2A²  (since Q(0) = 0 and V = 0)
    have hQF0 : QF adj x₀₀ = 0 := by rw [hx₀₀_z]; simp [QF, dotProduct, Matrix.mulVec]
    rw [show dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) =
        QF adj x from rfl]
    rw [h_decomp, hQF0, hV0]
    -- Need: 2L² + 2A² > 0, i.e., L ≠ 0 or A ≠ 0
    have hLA : L ≠ 0 ∨ A ≠ 0 := by
      by_contra h; push_neg at h; obtain ⟨hL0, hA0⟩ := h
      apply hx; ext i
      by_cases hi1 : i = L1
      · exact hi1 ▸ hL0
      · by_cases hi2 : i = L2
        · exact hi2 ▸ hA0
        · have := congr_fun hx₀₀_z i; simp [x₀₀, hi1, hi2] at this; exact this
    rcases hLA with hL | hA
    · have : 0 < L ^ 2 := by positivity
      nlinarith [sq_nonneg A]
    · have : 0 < A ^ 2 := by positivity
      nlinarith [sq_nonneg L]
  · -- Some non-leaf vertex nonzero: use strict bound
    have h_strict_bound := h_strict hx₀₀_z
    rw [show dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) =
        QF adj x from rfl]
    rw [h_decomp]
    nlinarith [sq_nonneg (V - L - A), sq_nonneg (L - A)]


-- Helper: if a vertex has degree 1, its sole neighbor is the known one.
private lemma deg1_unique_neighbor {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {v w : Fin n} (hadj : adj v w = 1) (hdeg : vertexDegree adj v = 1) :
    ∀ j, adj v j = 1 → j = w := by
  intro j hj; by_contra hne
  have : 2 ≤ vertexDegree adj v := by
    change 2 ≤ (Finset.univ.filter (fun k => adj v k = 1)).card
    calc 2 = ({w, j} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
      _ ≤ _ := Finset.card_le_card fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rcases hx with rfl | rfl <;> assumption⟩
  omega

-- Helper: if a vertex has degree 2 with two known distinct neighbors, any neighbor is one of them.
private lemma deg2_two_neighbors {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {v w₁ w₂ : Fin n} (h1 : adj v w₁ = 1) (h2 : adj v w₂ = 1) (hne : w₁ ≠ w₂)
    (hdeg : vertexDegree adj v = 2) :
    ∀ j, adj v j = 1 → j = w₁ ∨ j = w₂ := by
  intro j hj; by_contra h; push_neg at h
  have : 3 ≤ vertexDegree adj v := by
    change 3 ≤ (Finset.univ.filter (fun k => adj v k = 1)).card
    calc 3 = ({w₁, w₂, j} : Finset _).card := by
          rw [Finset.card_insert_of_notMem (by simp [hne, h.1.symm]),
              Finset.card_pair h.2.symm]
      _ ≤ _ := Finset.card_le_card fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rcases hx with rfl | rfl | rfl <;> assumption⟩
  omega

-- Helper: if a vertex has degree 3 with three known distinct neighbors, any neighbor is one of them.
private lemma deg3_three_neighbors {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {v w₁ w₂ w₃ : Fin n} (h1 : adj v w₁ = 1) (h2 : adj v w₂ = 1) (h3 : adj v w₃ = 1)
    (hne12 : w₁ ≠ w₂) (hne13 : w₁ ≠ w₃) (hne23 : w₂ ≠ w₃)
    (hdeg : vertexDegree adj v = 3) :
    ∀ j, adj v j = 1 → j = w₁ ∨ j = w₂ ∨ j = w₃ := by
  intro j hj; by_contra h; push_neg at h
  have : 4 ≤ vertexDegree adj v := by
    change 4 ≤ (Finset.univ.filter (fun k => adj v k = 1)).card
    calc 4 = ({w₁, w₂, w₃, j} : Finset _).card := by
          rw [Finset.card_insert_of_notMem (by simp [hne12, hne13, h.1.symm]),
              Finset.card_insert_of_notMem (by simp [hne23, h.2.1.symm]),
              Finset.card_pair h.2.2.symm]
      _ ≤ _ := Finset.card_le_card fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rcases hx with rfl | rfl | rfl | rfl <;> assumption⟩
  omega

-- Helper: a sum of 9 nonneg integer terms = 0 implies each = 0
private lemma e7_arms_zero (Xl A₂ B₂ C₂ A₃ B₃ : ℤ)
    (h : Xl ^ 2 + Xl ^ 2 + A₂ ^ 2 + (A₂ - B₂) ^ 2 +
         (B₂ - C₂) ^ 2 + C₂ ^ 2 + A₃ ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2 = 0) :
    Xl = 0 ∧ A₂ = 0 ∧ B₂ = 0 ∧ C₂ = 0 ∧ A₃ = 0 ∧ B₃ = 0 := by
  have hXl : Xl = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  have hA₂ : A₂ = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  have hC₂ : C₂ = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  have hB₃ : B₃ = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  have hB₂ : B₂ = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  have hA₃ : A₃ = 0 := by
    nlinarith [sq_nonneg Xl, sq_nonneg A₂, sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg A₃,
               sq_nonneg (A₃ - B₃), sq_nonneg B₃]
  exact ⟨hXl, hA₂, hB₂, hC₂, hA₃, hB₃⟩

set_option maxHeartbeats 6400000 in
/-- E₇ tree T(1,3,2) has positive definite Cartan form.
    Given 7 named vertices forming the E₇ tree in a connected acyclic graph,
    the Cartan quadratic form is positive definite. -/
private lemma e7_tree_posdef {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    -- 7 named vertices
    (v₀ L a₂ b₂ c₂ a₃ b₃ : Fin n)
    -- Adjacencies (6 edges of the E₇ tree)
    (hL : adj v₀ L = 1) (ha₂ : adj v₀ a₂ = 1) (ha₃ : adj v₀ a₃ = 1)
    (hb₂ : adj a₂ b₂ = 1) (hc₂ : adj b₂ c₂ = 1)
    (hb₃ : adj a₃ b₃ = 1)
    -- Degrees
    (hv₀_deg : vertexDegree adj v₀ = 3)
    (hL_deg : vertexDegree adj L = 1)
    (ha₂_deg : vertexDegree adj a₂ = 2) (ha₃_deg : vertexDegree adj a₃ = 2)
    (hb₂_deg : vertexDegree adj b₂ = 2)
    (hc₂_deg : vertexDegree adj c₂ = 1)
    (hb₃_deg : vertexDegree adj b₃ = 1) :
    ∀ x : Fin n → ℤ, x ≠ 0 → 0 < QF adj x := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  -- ne_of_adj: adjacent vertices are distinct
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b :=
    fun a b h hab => by rw [hab, hdiag] at h; omega
  -- Step 1: Derive distinctness
  -- Most pairs: degree mismatch (v₀=3, L/c₂/b₃=1, a₂/b₂/a₃=2)
  -- If u = v, their degrees match, contradicting the given degree values.
  have deg_ne : ∀ u v : Fin n, vertexDegree adj u ≠ vertexDegree adj v → u ≠ v :=
    fun _ _ h heq => h (heq ▸ rfl)
  have hv₀_ne_L := deg_ne _ _ (hv₀_deg ▸ hL_deg ▸ (by omega : (3 : ℕ) ≠ 1))
  have hv₀_ne_a₂ := deg_ne _ _ (hv₀_deg ▸ ha₂_deg ▸ (by omega : (3 : ℕ) ≠ 2))
  have hv₀_ne_a₃ := deg_ne _ _ (hv₀_deg ▸ ha₃_deg ▸ (by omega : (3 : ℕ) ≠ 2))
  have hv₀_ne_b₂ := deg_ne _ _ (hv₀_deg ▸ hb₂_deg ▸ (by omega : (3 : ℕ) ≠ 2))
  have hv₀_ne_c₂ := deg_ne _ _ (hv₀_deg ▸ hc₂_deg ▸ (by omega : (3 : ℕ) ≠ 1))
  have hv₀_ne_b₃ := deg_ne _ _ (hv₀_deg ▸ hb₃_deg ▸ (by omega : (3 : ℕ) ≠ 1))
  have hL_ne_a₂ := deg_ne _ _ (hL_deg ▸ ha₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hL_ne_b₂ := deg_ne _ _ (hL_deg ▸ hb₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hL_ne_a₃ := deg_ne _ _ (hL_deg ▸ ha₃_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hc₂_ne_a₂ := deg_ne _ _ (hc₂_deg ▸ ha₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hc₂_ne_b₂ := deg_ne _ _ (hc₂_deg ▸ hb₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hc₂_ne_a₃ := deg_ne _ _ (hc₂_deg ▸ ha₃_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hb₃_ne_a₂ := deg_ne _ _ (hb₃_deg ▸ ha₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hb₃_ne_b₂ := deg_ne _ _ (hb₃_deg ▸ hb₂_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  have hb₃_ne_a₃ := deg_ne _ _ (hb₃_deg ▸ ha₃_deg ▸ (by omega : (1 : ℕ) ≠ 2))
  -- Adjacent pairs (same degree) are distinct
  have ha₂_ne_b₂ := ne_of_adj _ _ hb₂
  have hb₂_ne_c₂ := ne_of_adj _ _ hc₂
  have ha₃_ne_b₃ := ne_of_adj _ _ hb₃
  -- Same-degree, non-adjacent pairs: use deg2_two_neighbors
  -- a₂ ≠ a₃: if equal, a₂'s neighbor b₃ must be v₀ or b₂, both degree contradictions
  have ha₂_ne_a₃ : a₂ ≠ a₃ := by
    intro h
    have ha₂_nbrs := deg2_two_neighbors ((adj_comm a₂ v₀).trans ha₂) hb₂
      hv₀_ne_b₂ ha₂_deg
    rcases ha₂_nbrs b₃ (by rw [← h] at hb₃; exact hb₃) with rfl | rfl
    · exact absurd hb₃_deg (by rw [hv₀_deg]; omega)
    · exact absurd hb₃_deg (by rw [hb₂_deg]; omega)
  -- b₂ ≠ a₃: if equal, b₂'s neighbor v₀ must be a₂ or c₂, both degree contradictions
  have hb₂_ne_a₃ : b₂ ≠ a₃ := by
    intro h
    have hb₂_nbrs := deg2_two_neighbors ((adj_comm b₂ a₂).trans hb₂) hc₂
      hc₂_ne_a₂.symm hb₂_deg
    have : adj b₂ v₀ = 1 := by rw [h]; exact (adj_comm a₃ v₀).trans ha₃
    rcases hb₂_nbrs v₀ this with rfl | rfl
    · exact absurd hv₀_deg (by rw [ha₂_deg]; omega)
    · exact absurd hv₀_deg (by rw [hc₂_deg]; omega)
  -- L ≠ c₂: L's sole neighbor is v₀, c₂'s sole neighbor is b₂; if L=c₂ then v₀=b₂
  have hL_ne_c₂ : L ≠ c₂ := fun h => hv₀_ne_b₂ (by
    have hL_only := deg1_unique_neighbor ((adj_comm L v₀).trans hL) hL_deg
    have hc₂_only := deg1_unique_neighbor ((adj_comm c₂ b₂).trans hc₂) hc₂_deg
    have := hc₂_only v₀ (h ▸ (adj_comm L v₀).trans hL); exact this)
  -- L ≠ b₃: similarly, if L=b₃ then v₀=a₃
  have hL_ne_b₃ : L ≠ b₃ := fun h => hv₀_ne_a₃ (by
    have hL_only := deg1_unique_neighbor ((adj_comm L v₀).trans hL) hL_deg
    have hb₃_only := deg1_unique_neighbor ((adj_comm b₃ a₃).trans hb₃) hb₃_deg
    have := hb₃_only v₀ (h ▸ (adj_comm L v₀).trans hL); exact this)
  -- c₂ ≠ b₃: if c₂=b₃ then b₂=a₃ (sole neighbors), giving b₂ 3 neighbors
  have hc₂_ne_b₃ : c₂ ≠ b₃ := fun h => hb₂_ne_a₃ (by
    have hc₂_only := deg1_unique_neighbor ((adj_comm c₂ b₂).trans hc₂) hc₂_deg
    have hb₃_only := deg1_unique_neighbor ((adj_comm b₃ a₃).trans hb₃) hb₃_deg
    exact hb₃_only b₂ (h ▸ (adj_comm c₂ b₂).trans hc₂))
  -- Step 2: Closed neighborhoods (neighbors of each named vertex are all named)
  have hL_only : ∀ j, adj L j = 1 → j = v₀ :=
    deg1_unique_neighbor ((adj_comm L v₀).trans hL) hL_deg
  have hc₂_only : ∀ j, adj c₂ j = 1 → j = b₂ :=
    deg1_unique_neighbor ((adj_comm c₂ b₂).trans hc₂) hc₂_deg
  have hb₃_only : ∀ j, adj b₃ j = 1 → j = a₃ :=
    deg1_unique_neighbor ((adj_comm b₃ a₃).trans hb₃) hb₃_deg
  have ha₂_only : ∀ j, adj a₂ j = 1 → j = v₀ ∨ j = b₂ :=
    deg2_two_neighbors ((adj_comm a₂ v₀).trans ha₂) hb₂ hv₀_ne_b₂ ha₂_deg
  have hb₂_only : ∀ j, adj b₂ j = 1 → j = a₂ ∨ j = c₂ :=
    deg2_two_neighbors ((adj_comm b₂ a₂).trans hb₂) hc₂ hc₂_ne_a₂.symm hb₂_deg
  have ha₃_only : ∀ j, adj a₃ j = 1 → j = v₀ ∨ j = b₃ :=
    deg2_two_neighbors ((adj_comm a₃ v₀).trans ha₃) hb₃ hv₀_ne_b₃ ha₃_deg
  have hv₀_only : ∀ j, adj v₀ j = 1 → j = L ∨ j = a₂ ∨ j = a₃ :=
    deg3_three_neighbors hL ha₂ ha₃ hL_ne_a₂ hL_ne_a₃ ha₂_ne_a₃ hv₀_deg
  -- Step 3: Every vertex is named (closed neighborhood + connectedness)
  have hnamed : ∀ v : Fin n, adj v L = 1 ∨ adj v a₂ = 1 ∨ adj v b₂ = 1 ∨
      adj v c₂ = 1 ∨ adj v a₃ = 1 ∨ adj v b₃ = 1 ∨ adj v v₀ = 1 ∨ v = v₀ →
      v = v₀ ∨ v = L ∨ v = a₂ ∨ v = b₂ ∨ v = c₂ ∨ v = a₃ ∨ v = b₃ := by
    intro v hv; rcases hv with h | h | h | h | h | h | h | h
    -- adj v L = 1: v is L's neighbor, so v = v₀
    · have := hL_only v ((adj_comm L v).trans h); subst this; left; rfl
    -- adj v a₂ = 1: v = v₀ or v = b₂
    · rcases ha₂_only v ((adj_comm a₂ v).trans h) with rfl | rfl
      · left; rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    -- adj v b₂ = 1: v = a₂ or v = c₂
    · rcases hb₂_only v ((adj_comm b₂ v).trans h) with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    -- adj v c₂ = 1: v = b₂
    · have := hc₂_only v ((adj_comm c₂ v).trans h); subst this
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    -- adj v a₃ = 1: v = v₀ or v = b₃
    · rcases ha₃_only v ((adj_comm a₃ v).trans h) with rfl | rfl
      · left; rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    -- adj v b₃ = 1: v = a₃
    · have := hb₃_only v ((adj_comm b₃ v).trans h); subst this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    -- adj v v₀ = 1: v = L or v = a₂ or v = a₃
    · rcases hv₀_only v ((adj_comm v₀ v).trans h) with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    -- v = v₀
    · left; exact h
  -- Every vertex is named: use connectedness
  have hall : ∀ i : Fin n,
      i = v₀ ∨ i = L ∨ i = a₂ ∨ i = b₂ ∨ i = c₂ ∨ i = a₃ ∨ i = b₃ := by
    intro i
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ i
    -- All path elements are named, by induction on position
    suffices hpath : ∀ k (hk : k < path.length),
        path.get ⟨k, hk⟩ = v₀ ∨ path.get ⟨k, hk⟩ = L ∨
        path.get ⟨k, hk⟩ = a₂ ∨ path.get ⟨k, hk⟩ = b₂ ∨
        path.get ⟨k, hk⟩ = c₂ ∨ path.get ⟨k, hk⟩ = a₃ ∨
        path.get ⟨k, hk⟩ = b₃ by
      -- Extract that i (last element) is named
      rcases path with _ | ⟨p, ps⟩
      · simp at hlast
      · -- last element = i
        have hlt : (p :: ps).length - 1 < (p :: ps).length :=
          Nat.sub_lt (Nat.succ_pos ps.length) Nat.one_pos
        have hlast_get := hpath ((p :: ps).length - 1) hlt
        -- get(length-1) = getLast
        have hget_eq : (p :: ps).get ⟨(p :: ps).length - 1, hlt⟩ =
            (p :: ps).getLast (List.cons_ne_nil _ _) := by
          simp [List.getLast_eq_getElem]
        rw [hget_eq] at hlast_get
        -- getLast = i (from getLast? = some i)
        have hlast_eq : (p :: ps).getLast (List.cons_ne_nil _ _) = i := by
          have h := @List.getLast?_eq_getLast _ (p :: ps) (List.cons_ne_nil _ _)
          rw [h] at hlast; injection hlast
        rwa [hlast_eq] at hlast_get
    intro k hk
    induction k with
    | zero =>
      rcases path with _ | ⟨p, _⟩
      · exact absurd hk (by simp)
      · simp only [List.head?, Option.some.injEq] at hhead
        simp only [List.get]; left; exact hhead
    | succ k ih =>
      have hk' : k < path.length := by omega
      have hprev := ih hk'
      have hedge := hedges k hk
      -- adj(path[k+1], path[k]) = 1 by symmetry
      have hadj : adj (path.get ⟨k + 1, hk⟩)
          (path.get ⟨k, hk'⟩) = 1 := (adj_comm _ _).trans hedge
      apply hnamed
      -- path[k] is named; provide adjacency to hnamed
      rcases hprev with heq | heq | heq | heq | heq | heq | heq
          <;> rw [heq] at hadj
      -- path[k] = v₀: adj(path[k+1], v₀) = 1 → 7th disjunct
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl hadj))))))
      -- path[k] = L: adj(path[k+1], L) = 1 → 1st disjunct
      · exact .inl hadj
      -- path[k] = a₂
      · exact .inr (.inl hadj)
      -- path[k] = b₂
      · exact .inr (.inr (.inl hadj))
      -- path[k] = c₂
      · exact .inr (.inr (.inr (.inl hadj)))
      -- path[k] = a₃
      · exact .inr (.inr (.inr (.inr (.inl hadj))))
      -- path[k] = b₃
      · exact .inr (.inr (.inr (.inr (.inr (.inl hadj)))))
  -- Step 4: n = 7
  have hn7 : n = 7 := by
    have hsurj : Function.Surjective
        (![v₀, L, a₂, b₂, c₂, a₃, b₃] : Fin 7 → Fin n) := by
      intro i; rcases hall i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩,
              ⟨5, rfl⟩, ⟨6, rfl⟩]
    have h_le : n ≤ 7 := by
      have := Fintype.card_le_of_surjective _ hsurj
      simp [Fintype.card_fin] at this; exact this
    have h_ge : 7 ≤ n := by
      -- Use that {v₀, L, a₂, b₂, c₂, a₃, b₃} has 7 elements (all distinct)
      have hcard : ({v₀, L, a₂, b₂, c₂, a₃, b₃} : Finset (Fin n)).card = 7 := by
        rw [Finset.card_insert_of_notMem (by simp [hv₀_ne_L, hv₀_ne_a₂,
            hv₀_ne_b₂, hv₀_ne_c₂, hv₀_ne_a₃, hv₀_ne_b₃]),
          Finset.card_insert_of_notMem (by simp [hL_ne_a₂, hL_ne_b₂,
            hL_ne_c₂, hL_ne_a₃, hL_ne_b₃]),
          Finset.card_insert_of_notMem (by simp [ha₂_ne_b₂, hc₂_ne_a₂.symm,
            ha₂_ne_a₃, hb₃_ne_a₂.symm]),
          Finset.card_insert_of_notMem (by simp [hb₂_ne_c₂, hb₂_ne_a₃,
            hb₃_ne_b₂.symm]),
          Finset.card_insert_of_notMem (by simp [hc₂_ne_a₃, hc₂_ne_b₃]),
          Finset.card_insert_of_notMem (by simp [hb₃_ne_a₃.symm]),
          Finset.card_singleton]
      calc 7 = ({v₀, L, a₂, b₂, c₂, a₃, b₃} : Finset (Fin n)).card := hcard.symm
        _ ≤ Finset.univ.card := Finset.card_le_univ _
        _ = n := Fintype.card_fin n
    omega
  -- Step 5: Prove QF positive definite using sum-of-squares decomposition
  subst hn7
  intro x hx
  -- Non-edge facts: for each non-adjacent pair, adj u w = 0
  -- v₀ non-neighbors: b₂, c₂, b₃ (v₀'s only neighbors are L, a₂, a₃)
  have hv₀b₂ : adj v₀ b₂ = 0 := by
    rcases h01 v₀ b₂ with h | h; exact h
    rcases hv₀_only b₂ h with rfl | rfl | rfl
    exacts [absurd rfl hL_ne_b₂, absurd rfl ha₂_ne_b₂, absurd rfl hb₂_ne_a₃.symm]
  have hv₀c₂ : adj v₀ c₂ = 0 := by
    rcases h01 v₀ c₂ with h | h; exact h
    rcases hv₀_only c₂ h with rfl | rfl | rfl
    exacts [absurd rfl hL_ne_c₂, absurd rfl hc₂_ne_a₂.symm, absurd rfl hc₂_ne_a₃.symm]
  have hv₀b₃ : adj v₀ b₃ = 0 := by
    rcases h01 v₀ b₃ with h | h; exact h
    rcases hv₀_only b₃ h with rfl | rfl | rfl
    exacts [absurd rfl hL_ne_b₃, absurd rfl hb₃_ne_a₂.symm, absurd rfl hb₃_ne_a₃.symm]
  -- L non-neighbors: a₂, b₂, c₂, a₃, b₃ (L's only neighbor is v₀)
  have hLa₂ : adj L a₂ = 0 := by
    rcases h01 L a₂ with h | h; exact h; exact absurd (hL_only a₂ h) hv₀_ne_a₂.symm
  have hLb₂ : adj L b₂ = 0 := by
    rcases h01 L b₂ with h | h; exact h; exact absurd (hL_only b₂ h) hv₀_ne_b₂.symm
  have hLc₂ : adj L c₂ = 0 := by
    rcases h01 L c₂ with h | h; exact h; exact absurd (hL_only c₂ h) hv₀_ne_c₂.symm
  have hLa₃ : adj L a₃ = 0 := by
    rcases h01 L a₃ with h | h; exact h; exact absurd (hL_only a₃ h) hv₀_ne_a₃.symm
  have hLb₃ : adj L b₃ = 0 := by
    rcases h01 L b₃ with h | h; exact h; exact absurd (hL_only b₃ h) hv₀_ne_b₃.symm
  -- a₂ non-neighbors: c₂, a₃, b₃ (a₂'s neighbors are v₀ and b₂)
  have ha₂c₂ : adj a₂ c₂ = 0 := by
    rcases h01 a₂ c₂ with h | h; exact h
    rcases ha₂_only c₂ h with rfl | rfl
    exacts [absurd rfl hv₀_ne_c₂, absurd rfl hb₂_ne_c₂]
  have ha₂a₃ : adj a₂ a₃ = 0 := by
    rcases h01 a₂ a₃ with h | h; exact h
    rcases ha₂_only a₃ h with rfl | rfl
    exacts [absurd rfl hv₀_ne_a₃, absurd rfl hb₂_ne_a₃]
  have ha₂b₃ : adj a₂ b₃ = 0 := by
    rcases h01 a₂ b₃ with h | h; exact h
    rcases ha₂_only b₃ h with rfl | rfl
    exacts [absurd rfl hv₀_ne_b₃, absurd rfl hb₃_ne_b₂.symm]
  -- b₂ non-neighbors: a₃, b₃ (b₂'s neighbors are a₂ and c₂)
  have hb₂a₃ : adj b₂ a₃ = 0 := by
    rcases h01 b₂ a₃ with h | h; exact h
    rcases hb₂_only a₃ h with rfl | rfl
    exacts [absurd rfl ha₂_ne_a₃, absurd rfl hc₂_ne_a₃]
  have hb₂b₃ : adj b₂ b₃ = 0 := by
    rcases h01 b₂ b₃ with h | h; exact h
    rcases hb₂_only b₃ h with rfl | rfl
    exacts [absurd rfl hb₃_ne_a₂.symm, absurd rfl hc₂_ne_b₃]
  -- c₂ non-neighbors: a₃, b₃ (c₂'s only neighbor is b₂)
  have hc₂a₃ : adj c₂ a₃ = 0 := by
    rcases h01 c₂ a₃ with h | h; exact h; exact absurd (hc₂_only a₃ h) hb₂_ne_a₃.symm
  have hc₂b₃ : adj c₂ b₃ = 0 := by
    rcases h01 c₂ b₃ with h | h; exact h; exact absurd (hc₂_only b₃ h) hb₃_ne_b₂
  -- a₃ non-neighbor: (all handled by symmetry below)
  -- Symmetric adj facts (edge reverses and non-edge reverses)
  have hLv₀ : adj L v₀ = 1 := (adj_comm L v₀).trans hL
  have ha₂v₀ : adj a₂ v₀ = 1 := (adj_comm a₂ v₀).trans ha₂
  have ha₃v₀ : adj a₃ v₀ = 1 := (adj_comm a₃ v₀).trans ha₃
  have hb₂a₂' : adj b₂ a₂ = 1 := (adj_comm b₂ a₂).trans hb₂
  have hc₂b₂' : adj c₂ b₂ = 1 := (adj_comm c₂ b₂).trans hc₂
  have hb₃a₃ : adj b₃ a₃ = 1 := (adj_comm b₃ a₃).trans hb₃
  -- Symmetric non-edges
  have ha₂L : adj a₂ L = 0 := (adj_comm a₂ L).trans hLa₂
  have hb₂v₀ : adj b₂ v₀ = 0 := (adj_comm b₂ v₀).trans hv₀b₂
  have hb₂L : adj b₂ L = 0 := (adj_comm b₂ L).trans hLb₂
  have hc₂v₀ : adj c₂ v₀ = 0 := (adj_comm c₂ v₀).trans hv₀c₂
  have hc₂L : adj c₂ L = 0 := (adj_comm c₂ L).trans hLc₂
  have hc₂a₂ : adj c₂ a₂ = 0 := (adj_comm c₂ a₂).trans ha₂c₂
  have ha₃L : adj a₃ L = 0 := (adj_comm a₃ L).trans hLa₃
  have ha₃a₂ : adj a₃ a₂ = 0 := (adj_comm a₃ a₂).trans ha₂a₃
  have ha₃b₂ : adj a₃ b₂ = 0 := (adj_comm a₃ b₂).trans hb₂a₃
  have ha₃c₂ : adj a₃ c₂ = 0 := (adj_comm a₃ c₂).trans hc₂a₃
  have hb₃v₀ : adj b₃ v₀ = 0 := (adj_comm b₃ v₀).trans hv₀b₃
  have hb₃L : adj b₃ L = 0 := (adj_comm b₃ L).trans hLb₃
  have hb₃a₂ : adj b₃ a₂ = 0 := (adj_comm b₃ a₂).trans ha₂b₃
  have hb₃b₂ : adj b₃ b₂ = 0 := (adj_comm b₃ b₂).trans hb₂b₃
  have hb₃c₂ : adj b₃ c₂ = 0 := (adj_comm b₃ c₂).trans hc₂b₃
  -- Finset.univ = {v₀, L, a₂, b₂, c₂, a₃, b₃}
  have huniv : (Finset.univ : Finset (Fin 7)) = {v₀, L, a₂, b₂, c₂, a₃, b₃} := by
    ext w; simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases hall w with h | h | h | h | h | h | h <;> simp [h]
  -- Membership proofs for Finset expansion
  have hv₀_nmem : v₀ ∉ ({L, a₂, b₂, c₂, a₃, b₃} : Finset _) := by
    simp [hv₀_ne_L, hv₀_ne_a₂, hv₀_ne_b₂, hv₀_ne_c₂, hv₀_ne_a₃, hv₀_ne_b₃]
  have hL_nmem : L ∉ ({a₂, b₂, c₂, a₃, b₃} : Finset _) := by
    simp [hL_ne_a₂, hL_ne_b₂, hL_ne_c₂, hL_ne_a₃, hL_ne_b₃]
  have ha₂_nmem : a₂ ∉ ({b₂, c₂, a₃, b₃} : Finset _) := by
    simp [ha₂_ne_b₂, hc₂_ne_a₂.symm, ha₂_ne_a₃, hb₃_ne_a₂.symm]
  have hb₂_nmem : b₂ ∉ ({c₂, a₃, b₃} : Finset _) := by
    simp [hb₂_ne_c₂, hb₂_ne_a₃, hb₃_ne_b₂.symm]
  have hc₂_nmem : c₂ ∉ ({a₃, b₃} : Finset _) := by
    simp [hc₂_ne_a₃, hc₂_ne_b₃]
  have ha₃_nmem : a₃ ∉ ({b₃} : Finset _) := by
    simp [ha₃_ne_b₃]
  -- Expand QF over the 7 named vertices
  have hQF : QF adj x =
      x v₀ * (2 * x v₀ - x L - x a₂ - x a₃) +
      x L * (2 * x L - x v₀) +
      x a₂ * (2 * x a₂ - x v₀ - x b₂) +
      x b₂ * (2 * x b₂ - x a₂ - x c₂) +
      x c₂ * (2 * x c₂ - x b₂) +
      x a₃ * (2 * x a₃ - x v₀ - x b₃) +
      x b₃ * (2 * x b₃ - x a₃) := by
    -- QF = x^T (2I - adj) x, expand double sum over named vertices
    have h_adj_row : ∀ v : Fin 7, ∀ j : Fin 7,
        (2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - adj) v j =
        (if v = j then 2 else 0) - adj v j := by
      intro v j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      split_ifs <;> ring
    unfold QF dotProduct
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [h_adj_row]
    rw [show ∑ i : Fin 7, x i * ∑ j : Fin 7, ((if i = j then 2 else 0) - adj i j) * x j =
        ∑ i ∈ (Finset.univ : Finset (Fin 7)),
          x i * ∑ j ∈ (Finset.univ : Finset (Fin 7)),
            ((if i = j then (2 : ℤ) else 0) - adj i j) * x j from rfl]
    rw [huniv]
    simp only [Finset.sum_insert hv₀_nmem, Finset.sum_insert hL_nmem,
               Finset.sum_insert ha₂_nmem, Finset.sum_insert hb₂_nmem,
               Finset.sum_insert hc₂_nmem, Finset.sum_insert ha₃_nmem,
               Finset.sum_singleton]
    simp only [hdiag, hL, ha₂, ha₃, hb₂, hc₂, hb₃,
               hLv₀, ha₂v₀, ha₃v₀, hb₂a₂', hc₂b₂', hb₃a₃,
               hv₀b₂, hv₀c₂, hv₀b₃, hLa₂, hLb₂, hLc₂, hLa₃, hLb₃,
               ha₂L, ha₂c₂, ha₂a₃, ha₂b₃,
               hb₂v₀, hb₂L, hb₂a₃, hb₂b₃,
               hc₂v₀, hc₂L, hc₂a₂, hc₂a₃, hc₂b₃,
               ha₃L, ha₃a₂, ha₃b₂, ha₃c₂,
               hb₃v₀, hb₃L, hb₃a₂, hb₃b₂, hb₃c₂,
               ite_true, ite_false, eq_self_iff_true,
               hv₀_ne_L, hv₀_ne_a₂, hv₀_ne_b₂, hv₀_ne_c₂, hv₀_ne_a₃, hv₀_ne_b₃,
               hL_ne_a₂, hL_ne_b₂, hL_ne_c₂, hL_ne_a₃, hL_ne_b₃,
               ha₂_ne_b₂, hc₂_ne_a₂, ha₂_ne_a₃, hb₃_ne_a₂,
               hb₂_ne_c₂, hb₂_ne_a₃, hb₃_ne_b₂,
               hc₂_ne_a₃, hc₂_ne_b₃, ha₃_ne_b₃,
               Ne.symm hv₀_ne_L, Ne.symm hv₀_ne_a₂, Ne.symm hv₀_ne_b₂,
               Ne.symm hv₀_ne_c₂, Ne.symm hv₀_ne_a₃, Ne.symm hv₀_ne_b₃,
               Ne.symm hL_ne_a₂, Ne.symm hL_ne_b₂, Ne.symm hL_ne_c₂,
               Ne.symm hL_ne_a₃, Ne.symm hL_ne_b₃,
               Ne.symm ha₂_ne_b₂, hc₂_ne_a₂.symm, Ne.symm ha₂_ne_a₃, hb₃_ne_a₂.symm,
               Ne.symm hb₂_ne_c₂, Ne.symm hb₂_ne_a₃, hb₃_ne_b₂.symm,
               Ne.symm hc₂_ne_a₃, Ne.symm hc₂_ne_b₃, Ne.symm ha₃_ne_b₃]
    ring

  -- Sum-of-squares identity
  set V := x v₀; set Xl := x L; set A₂ := x a₂; set B₂ := x b₂
  set C₂ := x c₂; set A₃ := x a₃; set B₃ := x b₃
  have hQF_poly : V * (2 * V - Xl - A₂ - A₃) + Xl * (2 * Xl - V) +
      A₂ * (2 * A₂ - V - B₂) + B₂ * (2 * B₂ - A₂ - C₂) +
      C₂ * (2 * C₂ - B₂) + A₃ * (2 * A₃ - V - B₃) + B₃ * (2 * B₃ - A₃) =
      (V - Xl) ^ 2 + Xl ^ 2 + (V - A₂) ^ 2 + (A₂ - B₂) ^ 2 +
      (B₂ - C₂) ^ 2 + C₂ ^ 2 + (V - A₃) ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2 - V ^ 2 := by ring
  -- Nonzero condition
  have hvals_ne : ¬(V = 0 ∧ Xl = 0 ∧ A₂ = 0 ∧ B₂ = 0 ∧ C₂ = 0 ∧ A₃ = 0 ∧ B₃ = 0) := by
    intro ⟨hV, hXl, hA₂, hB₂, hC₂, hA₃, hB₃⟩
    apply hx; ext i
    rcases hall i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- Arm bounds (Cauchy-Schwarz: k * sum_of_k_squares ≥ v²)
  have hl_bound : 2 * ((V - Xl) ^ 2 + Xl ^ 2) ≥ V ^ 2 := by
    nlinarith [sq_nonneg (V - 2 * Xl)]
  have ha₂_bound : 4 * ((V - A₂) ^ 2 + (A₂ - B₂) ^ 2 + (B₂ - C₂) ^ 2 + C₂ ^ 2) ≥ V ^ 2 := by
    nlinarith [sq_nonneg ((V - A₂) - (A₂ - B₂)), sq_nonneg ((V - A₂) - (B₂ - C₂)),
               sq_nonneg ((V - A₂) - C₂), sq_nonneg ((A₂ - B₂) - (B₂ - C₂)),
               sq_nonneg ((A₂ - B₂) - C₂), sq_nonneg ((B₂ - C₂) - C₂)]
  have ha₃_bound : 3 * ((V - A₃) ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2) ≥ V ^ 2 := by
    nlinarith [sq_nonneg (V - A₃ - (A₃ - B₃)), sq_nonneg ((V - A₃) - B₃),
               sq_nonneg ((A₃ - B₃) - B₃), sq_nonneg (V - A₃ - B₃),
               sq_nonneg (V - 2 * A₃ + B₃), sq_nonneg ((V - A₃) - 2 * (A₃ - B₃) + B₃)]
  -- QF ≥ 0
  have hQF_nonneg : 0 ≤ QF adj x := by
    rw [hQF, hQF_poly]
    nlinarith [sq_nonneg (V - Xl), sq_nonneg Xl, sq_nonneg (V - A₂), sq_nonneg (A₂ - B₂),
               sq_nonneg (B₂ - C₂), sq_nonneg C₂, sq_nonneg (V - A₃), sq_nonneg (A₃ - B₃),
               sq_nonneg B₃]
  -- QF = 0 → contradiction
  rcases eq_or_lt_of_le hQF_nonneg with heq | hlt
  · exfalso
    have hQF0 : QF adj x = 0 := heq.symm
    have harms0 : (V - Xl) ^ 2 + Xl ^ 2 + (V - A₂) ^ 2 + (A₂ - B₂) ^ 2 +
        (B₂ - C₂) ^ 2 + C₂ ^ 2 + (V - A₃) ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2 - V ^ 2 = 0 := by
      linarith [hQF.trans hQF_poly]
    -- V must be 0
    have hV0 : V = 0 := by
      set Sl := (V - Xl) ^ 2 + Xl ^ 2
      set Sa := (V - A₂) ^ 2 + (A₂ - B₂) ^ 2 + (B₂ - C₂) ^ 2 + C₂ ^ 2
      set Sp := (V - A₃) ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2
      have hSlSaSp : Sl + Sa + Sp = V ^ 2 := by linarith
      have hSl_nn : 0 ≤ Sl := by positivity
      have hSa_nn : 0 ≤ Sa := by positivity
      have hSp_nn : 0 ≤ Sp := by positivity
      nlinarith [sq_nonneg V]
    -- All values are 0
    have harms0' : Xl ^ 2 + Xl ^ 2 + A₂ ^ 2 + (A₂ - B₂) ^ 2 +
        (B₂ - C₂) ^ 2 + C₂ ^ 2 + A₃ ^ 2 + (A₃ - B₃) ^ 2 + B₃ ^ 2 = 0 := by
      have := harms0; rw [hV0] at this
      linarith [sq_nonneg (0 - Xl), sq_nonneg (0 - A₂), sq_nonneg (0 - A₃)]
    obtain ⟨hXl0, hA₂0, hB₂0, hC₂0, hA₃0, hB₃0⟩ := e7_arms_zero Xl A₂ B₂ C₂ A₃ B₃ harms0'
    exact hvals_ne ⟨hV0, hXl0, hA₂0, hB₂0, hC₂0, hA₃0, hB₃0⟩
  · exact hlt


/-- In a connected graph, if a predicate S holds for a vertex v₀ and is closed
    under adjacency (S v ∧ adj v w = 1 → S w), then S holds for all vertices. -/
private lemma connected_closed_set_is_all {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (S : Fin n → Prop)
    (v₀ : Fin n) (hv₀ : S v₀)
    (hclosed : ∀ v w, S v → adj v w = 1 → S w) :
    ∀ w, S w := by
  intro w
  obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ w
  have hne : path ≠ [] := by intro h; rw [h] at hhead; simp at hhead
  have h_all : ∀ k (hk : k < path.length), S (path.get ⟨k, hk⟩) := by
    intro k hk
    induction k with
    | zero =>
      have h0 : path.get ⟨0, hk⟩ = v₀ := by
        rcases path with _ | ⟨a, _⟩
        · exact absurd rfl hne
        · exact Option.some.inj hhead
      rw [h0]; exact hv₀
    | succ k ih =>
      exact hclosed _ _ (ih (by omega)) (hedges k (by omega))
  have hlast_idx : path.length - 1 < path.length := by
    rcases path with _ | ⟨a, _⟩
    · exact absurd rfl hne
    · simp
  have h_last := h_all (path.length - 1) hlast_idx
  have hget_last : path.get ⟨path.length - 1, hlast_idx⟩ = path.getLast hne := by
    rcases path with _ | ⟨a, tl⟩; · exact absurd rfl hne
    · simp [List.getLast_eq_getElem]
  rw [hget_last] at h_last
  have hfinal : path.getLast hne = w := by
    rw [List.getLast?_eq_some_getLast (h := hne)] at hlast
    exact Option.some.inj hlast
  rwa [hfinal] at h_last

-- Cauchy-Schwarz arm bounds for E₈ positive definiteness
private lemma e8_arm_l (v l : ℤ) : 2 * ((v - l)^2 + l^2) ≥ v^2 := by
  nlinarith [sq_nonneg (v - 2*l)]

private lemma e8_arm_p (v p q : ℤ) : 3 * ((v - p)^2 + (p - q)^2 + q^2) ≥ v^2 := by
  nlinarith [sq_nonneg (v - p - (p - q)), sq_nonneg ((v - p) - q),
             sq_nonneg ((p - q) - q), sq_nonneg (v - p - q),
             sq_nonneg (v - 2*p + q), sq_nonneg ((v-p) - 2*(p-q) + q)]


set_option maxHeartbeats 800000 in
private lemma e8_arm_a (v a b c d : ℤ) :
    5 * ((v - a)^2 + (a - b)^2 + (b - c)^2 + (c - d)^2 + d^2) ≥ v^2 := by
  nlinarith [sq_nonneg ((v-a) - (a-b)), sq_nonneg ((a-b) - (b-c)),
             sq_nonneg ((b-c) - (c-d)), sq_nonneg ((c-d) - d),
             sq_nonneg ((v-a) - (b-c)), sq_nonneg ((v-a) - (c-d)),
             sq_nonneg ((v-a) - d), sq_nonneg ((a-b) - (c-d)),
             sq_nonneg ((a-b) - d), sq_nonneg ((b-c) - d),
             sq_nonneg v, sq_nonneg (v-a), sq_nonneg (a-b), sq_nonneg (b-c),
             sq_nonneg (c-d), sq_nonneg d]

-- All 28 pairs distinct, bundled as a structure
private structure E8Distinct {n : ℕ} (v₀ l a b c d p q : Fin n) : Prop where
  ne_v₀l : v₀ ≠ l
  ne_v₀a : v₀ ≠ a
  ne_v₀b : v₀ ≠ b
  ne_v₀c : v₀ ≠ c
  ne_v₀d : v₀ ≠ d
  ne_v₀p : v₀ ≠ p
  ne_v₀q : v₀ ≠ q
  ne_la : l ≠ a
  ne_lb : l ≠ b
  ne_lc : l ≠ c
  ne_ld : l ≠ d
  ne_lp : l ≠ p
  ne_lq : l ≠ q
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_ad : a ≠ d
  ne_ap : a ≠ p
  ne_aq : a ≠ q
  ne_bc : b ≠ c
  ne_bd : b ≠ d
  ne_bp : b ≠ p
  ne_bq : b ≠ q
  ne_cd : c ≠ d
  ne_cp : c ≠ p
  ne_cq : c ≠ q
  ne_dp : d ≠ p
  ne_dq : d ≠ q
  ne_pq : p ≠ q

-- mulVec computation: expand adj row sum over all 8 named vertices
set_option maxHeartbeats 3200000 in
private lemma mulVec_at8 {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (v₀ l a b c d p q : Fin n)
    (hd : E8Distinct v₀ l a b c d p q)
    (huniv : (Finset.univ : Finset (Fin n)) = {v₀, l, a, b, c, d, p, q})
    (v : Fin n)
    (r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : ℤ)
    (hself : adj v v = 0)
    (h₀ : adj v v₀ = r₀) (h₁ : adj v l = r₁) (h₂ : adj v a = r₂) (h₃ : adj v b = r₃)
    (h₄ : adj v c = r₄) (h₅ : adj v d = r₅) (h₆ : adj v p = r₆) (h₇ : adj v q = r₇)
    (hv : v = v₀ ∨ v = l ∨ v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = p ∨ v = q) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x v =
      2 * x v - r₀ * x v₀ - r₁ * x l - r₂ * x a - r₃ * x b -
      r₄ * x c - r₅ * x d - r₆ * x p - r₇ * x q := by
  have h_row : ∀ j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) v j =
      2 * (if v = j then 1 else 0) - adj v j := by
    intro j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [h_row]
  have expand : ∑ j : Fin n, (2 * (if v = j then (1 : ℤ) else 0) - adj v j) * x j =
      ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (2 * (if v = j then (1 : ℤ) else 0) - adj v j) * x j := rfl
  rw [expand, huniv]
  rw [Finset.sum_insert (by simp [hd.ne_v₀l, hd.ne_v₀a, hd.ne_v₀b, hd.ne_v₀c,
                                   hd.ne_v₀d, hd.ne_v₀p, hd.ne_v₀q] :
        v₀ ∉ ({l, a, b, c, d, p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_la, hd.ne_lb, hd.ne_lc, hd.ne_ld,
                                   hd.ne_lp, hd.ne_lq] :
        l ∉ ({a, b, c, d, p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_ab, hd.ne_ac, hd.ne_ad, hd.ne_ap, hd.ne_aq] :
        a ∉ ({b, c, d, p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_bc, hd.ne_bd, hd.ne_bp, hd.ne_bq] :
        b ∉ ({c, d, p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_cd, hd.ne_cp, hd.ne_cq] :
        c ∉ ({d, p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_dp, hd.ne_dq] : d ∉ ({p, q} : Finset _)),
      Finset.sum_insert (by simp [hd.ne_pq] : p ∉ ({q} : Finset _)),
      Finset.sum_singleton]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  have ne_v₀l := hd.ne_v₀l; have ne_v₀a := hd.ne_v₀a; have ne_v₀b := hd.ne_v₀b
  have ne_v₀c := hd.ne_v₀c; have ne_v₀d := hd.ne_v₀d; have ne_v₀p := hd.ne_v₀p
  have ne_v₀q := hd.ne_v₀q
  have ne_la := hd.ne_la; have ne_lb := hd.ne_lb; have ne_lc := hd.ne_lc
  have ne_ld := hd.ne_ld; have ne_lp := hd.ne_lp; have ne_lq := hd.ne_lq
  have ne_ab := hd.ne_ab; have ne_ac := hd.ne_ac; have ne_ad := hd.ne_ad
  have ne_ap := hd.ne_ap; have ne_aq := hd.ne_aq
  have ne_bc := hd.ne_bc; have ne_bd := hd.ne_bd; have ne_bp := hd.ne_bp
  have ne_bq := hd.ne_bq
  have ne_cd := hd.ne_cd; have ne_cp := hd.ne_cp; have ne_cq := hd.ne_cq
  have ne_dp := hd.ne_dp; have ne_dq := hd.ne_dq; have ne_pq := hd.ne_pq
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ite_true, ite_false, Ne.symm ne_v₀l, Ne.symm ne_v₀a, Ne.symm ne_v₀b,
               Ne.symm ne_v₀c, Ne.symm ne_v₀d, Ne.symm ne_v₀p, Ne.symm ne_v₀q,
               ne_v₀l, ne_v₀a, ne_v₀b, ne_v₀c, ne_v₀d, ne_v₀p, ne_v₀q,
               ne_la, ne_lb, ne_lc, ne_ld, ne_lp, ne_lq,
               Ne.symm ne_la, Ne.symm ne_lb, Ne.symm ne_lc, Ne.symm ne_ld,
               Ne.symm ne_lp, Ne.symm ne_lq,
               ne_ab, ne_ac, ne_ad, ne_ap, ne_aq,
               Ne.symm ne_ab, Ne.symm ne_ac, Ne.symm ne_ad, Ne.symm ne_ap, Ne.symm ne_aq,
               ne_bc, ne_bd, ne_bp, ne_bq,
               Ne.symm ne_bc, Ne.symm ne_bd, Ne.symm ne_bp, Ne.symm ne_bq,
               ne_cd, ne_cp, ne_cq,
               Ne.symm ne_cd, Ne.symm ne_cp, Ne.symm ne_cq,
               ne_dp, ne_dq, Ne.symm ne_dp, Ne.symm ne_dq,
               ne_pq, Ne.symm ne_pq,
               hself] <;>
    ring

-- Helper: a sum of 10 nonneg integer terms = 0 implies each = 0
private lemma e8_arms_zero (L A B C D P Q : ℤ)
    (h : L^2 + L^2 + A^2 + (A - B)^2 + (B - C)^2 + (C - D)^2 + D^2 +
         P^2 + (P - Q)^2 + Q^2 = 0) :
    L = 0 ∧ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ P = 0 ∧ Q = 0 := by
  have hL : L = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg (A-B), sq_nonneg (B-C),
                                    sq_nonneg (C-D), sq_nonneg D, sq_nonneg P, sq_nonneg (P-Q),
                                    sq_nonneg Q]
  have hA : A = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg (A-B), sq_nonneg (B-C),
                                    sq_nonneg (C-D), sq_nonneg D, sq_nonneg P, sq_nonneg (P-Q),
                                    sq_nonneg Q]
  have hD : D = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg (A-B), sq_nonneg (B-C),
                                    sq_nonneg (C-D), sq_nonneg D, sq_nonneg P, sq_nonneg (P-Q),
                                    sq_nonneg Q]
  have hQ : Q = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg (A-B), sq_nonneg (B-C),
                                    sq_nonneg (C-D), sq_nonneg D, sq_nonneg P, sq_nonneg (P-Q),
                                    sq_nonneg Q]
  have hB : B = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg B, sq_nonneg (A-B),
                                    sq_nonneg (B-C), sq_nonneg (C-D), sq_nonneg D, sq_nonneg P,
                                    sq_nonneg (P-Q), sq_nonneg Q]
  have hC : C = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg B, sq_nonneg C,
                                    sq_nonneg (A-B), sq_nonneg (B-C), sq_nonneg (C-D), sq_nonneg D,
                                    sq_nonneg P, sq_nonneg (P-Q), sq_nonneg Q]
  have hP : P = 0 := by nlinarith [sq_nonneg L, sq_nonneg A, sq_nonneg (A-B), sq_nonneg (B-C),
                                    sq_nonneg (C-D), sq_nonneg D, sq_nonneg P, sq_nonneg (P-Q),
                                    sq_nonneg Q]
  exact ⟨hL, hA, hB, hC, hD, hP, hQ⟩

set_option maxHeartbeats 3200000 in
/-- E₈ positive definiteness for an abstract graph with 8 named vertices.
    v₀ (center, degree 3), l (leaf), a,b,c,d (arm of length 4), p,q (arm of length 2).
    Edges: v₀-l, v₀-a, a-b, b-c, c-d, v₀-p, p-q. -/
private theorem e8_posdef {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (v₀ l a b c d p q : Fin n)
    (hd : E8Distinct v₀ l a b c d p q)
    (hadj_v₀l : adj v₀ l = 1) (hadj_v₀a : adj v₀ a = 1)
    (hadj_ab : adj a b = 1) (hadj_bc : adj b c = 1) (hadj_cd : adj c d = 1)
    (hadj_v₀p : adj v₀ p = 1) (hadj_pq : adj p q = 1)
    (hv₀_only : ∀ w, adj v₀ w = 1 → w = l ∨ w = a ∨ w = p)
    (hl_only : ∀ w, adj l w = 1 → w = v₀)
    (ha_only : ∀ w, adj a w = 1 → w = v₀ ∨ w = b)
    (hb_only : ∀ w, adj b w = 1 → w = a ∨ w = c)
    (hc_only : ∀ w, adj c w = 1 → w = b ∨ w = d)
    (hd_only : ∀ w, adj d w = 1 → w = c)
    (hp_only : ∀ w, adj p w = 1 → w = v₀ ∨ w = q)
    (hq_only : ∀ w, adj q w = 1 → w = p)
    (h_all_named : ∀ w : Fin n,
      w = v₀ ∨ w = l ∨ w = a ∨ w = b ∨ w = c ∨ w = d ∨ w = p ∨ w = q)
    (x : Fin n → ℤ) (hx : x ≠ 0) :
    0 < QF adj x := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have hadj_lv₀ : adj l v₀ = 1 := (adj_comm l v₀).trans hadj_v₀l
  have hadj_av₀ : adj a v₀ = 1 := (adj_comm a v₀).trans hadj_v₀a
  have hadj_ba : adj b a = 1 := (adj_comm b a).trans hadj_ab
  have hadj_cb : adj c b = 1 := (adj_comm c b).trans hadj_bc
  have hadj_dc : adj d c = 1 := (adj_comm d c).trans hadj_cd
  have hadj_pv₀ : adj p v₀ = 1 := (adj_comm p v₀).trans hadj_v₀p
  have hadj_qp : adj q p = 1 := (adj_comm q p).trans hadj_pq
  have huniv : (Finset.univ : Finset (Fin n)) = {v₀, l, a, b, c, d, p, q} := by
    ext w
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases h_all_named w with h | h | h | h | h | h | h | h <;> simp [h]
  -- Non-edge facts
  have hadj_v₀b : adj v₀ b = 0 := by
    rcases h01 v₀ b with h | h; · exact h
    rcases hv₀_only b h with rfl | rfl | rfl
    · exact (hd.ne_lb rfl).elim
    · exact (hd.ne_ab rfl).elim
    · exact (hd.ne_bp rfl).elim
  have hadj_v₀c : adj v₀ c = 0 := by
    rcases h01 v₀ c with h | h; · exact h
    rcases hv₀_only c h with rfl | rfl | rfl
    · exact (hd.ne_lc rfl).elim
    · exact (hd.ne_ac rfl).elim
    · exact (hd.ne_cp rfl).elim
  have hadj_v₀d : adj v₀ d = 0 := by
    rcases h01 v₀ d with h | h; · exact h
    rcases hv₀_only d h with rfl | rfl | rfl
    · exact (hd.ne_ld rfl).elim
    · exact (hd.ne_ad rfl).elim
    · exact (hd.ne_dp rfl).elim
  have hadj_v₀q : adj v₀ q = 0 := by
    rcases h01 v₀ q with h | h; · exact h
    rcases hv₀_only q h with rfl | rfl | rfl
    · exact (hd.ne_lq rfl).elim
    · exact (hd.ne_aq rfl).elim
    · exact (hd.ne_pq rfl).elim
  have hadj_la : adj l a = 0 := by
    rcases h01 l a with h | h; · exact h
    exact absurd (hl_only a h) (Ne.symm hd.ne_v₀a)
  have hadj_lb : adj l b = 0 := by
    rcases h01 l b with h | h; · exact h
    exact absurd (hl_only b h) (Ne.symm hd.ne_v₀b)
  have hadj_lc : adj l c = 0 := by
    rcases h01 l c with h | h; · exact h
    exact absurd (hl_only c h) (Ne.symm hd.ne_v₀c)
  have hadj_ld : adj l d = 0 := by
    rcases h01 l d with h | h; · exact h
    exact absurd (hl_only d h) (Ne.symm hd.ne_v₀d)
  have hadj_lp : adj l p = 0 := by
    rcases h01 l p with h | h; · exact h
    exact absurd (hl_only p h) (Ne.symm hd.ne_v₀p)
  have hadj_lq : adj l q = 0 := by
    rcases h01 l q with h | h; · exact h
    exact absurd (hl_only q h) (Ne.symm hd.ne_v₀q)
  have hadj_ac : adj a c = 0 := by
    rcases h01 a c with h | h; · exact h
    rcases ha_only c h with rfl | rfl
    · exact (hd.ne_v₀c rfl).elim
    · exact (hd.ne_bc rfl).elim
  have hadj_ad : adj a d = 0 := by
    rcases h01 a d with h | h; · exact h
    rcases ha_only d h with rfl | rfl
    · exact (hd.ne_v₀d rfl).elim
    · exact (hd.ne_bd rfl).elim
  have hadj_ap : adj a p = 0 := by
    rcases h01 a p with h | h; · exact h
    rcases ha_only p h with rfl | rfl
    · exact (hd.ne_v₀p rfl).elim
    · exact (hd.ne_bp rfl).elim
  have hadj_aq : adj a q = 0 := by
    rcases h01 a q with h | h; · exact h
    rcases ha_only q h with rfl | rfl
    · exact (hd.ne_v₀q rfl).elim
    · exact (hd.ne_bq rfl).elim
  have hadj_bd : adj b d = 0 := by
    rcases h01 b d with h | h; · exact h
    rcases hb_only d h with rfl | rfl
    · exact (hd.ne_ad rfl).elim
    · exact (hd.ne_cd rfl).elim
  have hadj_bp : adj b p = 0 := by
    rcases h01 b p with h | h; · exact h
    rcases hb_only p h with rfl | rfl
    · exact (hd.ne_ap rfl).elim
    · exact (hd.ne_cp rfl).elim
  have hadj_bq : adj b q = 0 := by
    rcases h01 b q with h | h; · exact h
    rcases hb_only q h with rfl | rfl
    · exact (hd.ne_aq rfl).elim
    · exact (hd.ne_cq rfl).elim
  have hadj_cp : adj c p = 0 := by
    rcases h01 c p with h | h; · exact h
    rcases hc_only p h with rfl | rfl
    · exact (hd.ne_bp rfl).elim
    · exact (hd.ne_dp rfl).elim
  have hadj_cq : adj c q = 0 := by
    rcases h01 c q with h | h; · exact h
    rcases hc_only q h with rfl | rfl
    · exact (hd.ne_bq rfl).elim
    · exact (hd.ne_dq rfl).elim
  have hadj_dp : adj d p = 0 := by
    rcases h01 d p with h | h; · exact h
    exact absurd (hd_only p h) (Ne.symm hd.ne_cp)
  have hadj_dq : adj d q = 0 := by
    rcases h01 d q with h | h; · exact h
    exact absurd (hd_only q h) (Ne.symm hd.ne_cq)
  have hadj_qv₀ : adj q v₀ = 0 := by
    rcases h01 q v₀ with h | h; · exact h
    exact absurd (hq_only v₀ h) hd.ne_v₀p
  have hadj_ql : adj q l = 0 := by
    rcases h01 q l with h | h; · exact h
    exact absurd (hq_only l h) hd.ne_lp
  have hadj_qa : adj q a = 0 := by
    rcases h01 q a with h | h; · exact h
    exact absurd (hq_only a h) hd.ne_ap
  have hadj_qb : adj q b = 0 := by
    rcases h01 q b with h | h; · exact h
    exact absurd (hq_only b h) hd.ne_bp
  have hadj_qc : adj q c = 0 := by
    rcases h01 q c with h | h; · exact h
    exact absurd (hq_only c h) hd.ne_cp
  have hadj_qd : adj q d = 0 := by
    rcases h01 q d with h | h; · exact h
    exact absurd (hq_only d h) hd.ne_dp
  -- Compute mulVec at each named vertex
  have hmv_v₀ : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x v₀ =
      2 * x v₀ - 0 * x v₀ - 1 * x l - 1 * x a - 0 * x b - 0 * x c - 0 * x d - 1 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv v₀ 0 1 1 0 0 0 1 0
      (hdiag v₀) (hdiag v₀) hadj_v₀l hadj_v₀a hadj_v₀b hadj_v₀c hadj_v₀d hadj_v₀p hadj_v₀q
      (Or.inl rfl)
  have hmv_l : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x l =
      2 * x l - 1 * x v₀ - 0 * x l - 0 * x a - 0 * x b - 0 * x c - 0 * x d - 0 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv l 1 0 0 0 0 0 0 0
      (hdiag l) hadj_lv₀ (hdiag l) hadj_la hadj_lb hadj_lc hadj_ld hadj_lp hadj_lq
      (Or.inr (Or.inl rfl))
  have hmv_a : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x a =
      2 * x a - 1 * x v₀ - 0 * x l - 0 * x a - 1 * x b - 0 * x c - 0 * x d - 0 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv a 1 0 0 1 0 0 0 0
      (hdiag a) hadj_av₀ ((adj_comm a l).trans hadj_la) (hdiag a) hadj_ab hadj_ac hadj_ad hadj_ap hadj_aq
      (Or.inr (Or.inr (Or.inl rfl)))
  have hmv_b : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x b =
      2 * x b - 0 * x v₀ - 0 * x l - 1 * x a - 0 * x b - 1 * x c - 0 * x d - 0 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv b 0 0 1 0 1 0 0 0
      (hdiag b) ((adj_comm b v₀).trans hadj_v₀b) ((adj_comm b l).trans hadj_lb) hadj_ba (hdiag b)
      hadj_bc hadj_bd hadj_bp hadj_bq
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hmv_c : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x c =
      2 * x c - 0 * x v₀ - 0 * x l - 0 * x a - 1 * x b - 0 * x c - 1 * x d - 0 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv c 0 0 0 1 0 1 0 0
      (hdiag c) ((adj_comm c v₀).trans hadj_v₀c) ((adj_comm c l).trans hadj_lc)
      ((adj_comm c a).trans hadj_ac) hadj_cb (hdiag c) hadj_cd hadj_cp hadj_cq
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hmv_d : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x d =
      2 * x d - 0 * x v₀ - 0 * x l - 0 * x a - 0 * x b - 1 * x c - 0 * x d - 0 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv d 0 0 0 0 1 0 0 0
      (hdiag d) ((adj_comm d v₀).trans hadj_v₀d) ((adj_comm d l).trans hadj_ld)
      ((adj_comm d a).trans hadj_ad) ((adj_comm d b).trans hadj_bd) hadj_dc (hdiag d) hadj_dp hadj_dq
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hmv_p : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x p =
      2 * x p - 1 * x v₀ - 0 * x l - 0 * x a - 0 * x b - 0 * x c - 0 * x d - 0 * x p - 1 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv p 1 0 0 0 0 0 0 1
      (hdiag p) hadj_pv₀ ((adj_comm p l).trans hadj_lp) ((adj_comm p a).trans hadj_ap)
      ((adj_comm p b).trans hadj_bp) ((adj_comm p c).trans hadj_cp) ((adj_comm p d).trans hadj_dp)
      (hdiag p) hadj_pq
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hmv_q : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x q =
      2 * x q - 0 * x v₀ - 0 * x l - 0 * x a - 0 * x b - 0 * x c - 0 * x d - 1 * x p - 0 * x q :=
    mulVec_at8 adj x v₀ l a b c d p q hd huniv q 0 0 0 0 0 0 1 0
      (hdiag q) hadj_qv₀ hadj_ql hadj_qa hadj_qb hadj_qc hadj_qd hadj_qp (hdiag q)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  -- Expand QF over the 8 named vertices
  have hQF : QF adj x =
      x v₀ * (2 * x v₀ - x l - x a - x p) +
      x l * (2 * x l - x v₀) +
      x a * (2 * x a - x v₀ - x b) +
      x b * (2 * x b - x a - x c) +
      x c * (2 * x c - x b - x d) +
      x d * (2 * x d - x c) +
      x p * (2 * x p - x v₀ - x q) +
      x q * (2 * x q - x p) := by
    unfold QF dotProduct
    have expand : ∑ i : Fin n, x i * (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x i =
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          x i * (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x i := rfl
    rw [expand, huniv]
    rw [Finset.sum_insert (by simp [hd.ne_v₀l, hd.ne_v₀a, hd.ne_v₀b, hd.ne_v₀c,
                                     hd.ne_v₀d, hd.ne_v₀p, hd.ne_v₀q] :
          v₀ ∉ ({l, a, b, c, d, p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_la, hd.ne_lb, hd.ne_lc, hd.ne_ld,
                                     hd.ne_lp, hd.ne_lq] :
          l ∉ ({a, b, c, d, p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_ab, hd.ne_ac, hd.ne_ad, hd.ne_ap, hd.ne_aq] :
          a ∉ ({b, c, d, p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_bc, hd.ne_bd, hd.ne_bp, hd.ne_bq] :
          b ∉ ({c, d, p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_cd, hd.ne_cp, hd.ne_cq] :
          c ∉ ({d, p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_dp, hd.ne_dq] : d ∉ ({p, q} : Finset _)),
        Finset.sum_insert (by simp [hd.ne_pq] : p ∉ ({q} : Finset _)),
        Finset.sum_singleton]
    rw [hmv_v₀, hmv_l, hmv_a, hmv_b, hmv_c, hmv_d, hmv_p, hmv_q]
    ring
  -- Nonzero condition
  have hvals_ne : ¬(x v₀ = 0 ∧ x l = 0 ∧ x a = 0 ∧ x b = 0 ∧ x c = 0 ∧
      x d = 0 ∧ x p = 0 ∧ x q = 0) := by
    intro ⟨hV, hL, hA, hB, hC, hD, hP, hQ⟩
    apply hx; ext i
    rcases h_all_named i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  set V := x v₀; set L := x l; set A := x a; set B := x b
  set C := x c; set D := x d; set P := x p; set Q := x q
  have hQF_poly : V * (2 * V - L - A - P) +
      L * (2 * L - V) +
      A * (2 * A - V - B) +
      B * (2 * B - A - C) +
      C * (2 * C - B - D) +
      D * (2 * D - C) +
      P * (2 * P - V - Q) +
      Q * (2 * Q - P) =
      (V - L)^2 + L^2 + (V - A)^2 + (A - B)^2 + (B - C)^2 + (C - D)^2 + D^2 +
      (V - P)^2 + (P - Q)^2 + Q^2 - V^2 := by ring
  have hl_bound := e8_arm_l V L
  have ha_bound := e8_arm_a V A B C D
  have hp_bound := e8_arm_p V P Q
  have hQF_nonneg : 0 ≤ QF adj x := by
    rw [hQF, hQF_poly]
    nlinarith [sq_nonneg (V - L), sq_nonneg (V - A), sq_nonneg (A - B),
               sq_nonneg (B - C), sq_nonneg (C - D), sq_nonneg (V - P), sq_nonneg (P - Q),
               sq_nonneg L, sq_nonneg D, sq_nonneg Q]
  rcases eq_or_lt_of_le hQF_nonneg with heq | hlt
  · exfalso
    have hQF0 : QF adj x = 0 := heq.symm
    have harms0 : (V - L)^2 + L^2 + (V - A)^2 + (A - B)^2 + (B - C)^2 + (C - D)^2 + D^2 +
        (V - P)^2 + (P - Q)^2 + Q^2 - V^2 = 0 := by
      linarith [hQF.trans hQF_poly]
    have hV0 : V = 0 := by
      set Sl := (V - L)^2 + L^2
      set Sa := (V - A)^2 + (A - B)^2 + (B - C)^2 + (C - D)^2 + D^2
      set Sp := (V - P)^2 + (P - Q)^2 + Q^2
      have hSlSaSp : Sl + Sa + Sp = V^2 := by linarith
      have hSl_nn : 0 ≤ Sl := by positivity
      have hSa_nn : 0 ≤ Sa := by positivity
      have hSp_nn : 0 ≤ Sp := by positivity
      nlinarith [sq_nonneg V]
    have harms0' : L^2 + L^2 + A^2 + (A - B)^2 + (B - C)^2 + (C - D)^2 + D^2 +
        P^2 + (P - Q)^2 + Q^2 = 0 := by
      have := harms0; rw [hV0] at this
      linarith [sq_nonneg (0 - L), sq_nonneg (0 - A), sq_nonneg (0 - P)]
    obtain ⟨hL0, hA0, hB0, hC0, hD0, hP0, hQ0⟩ := e8_arms_zero L A B C D P Q harms0'
    exact hvals_ne ⟨hV0, hL0, hA0, hB0, hC0, hD0, hP0, hQ0⟩
  · exact hlt

set_option maxHeartbeats 6400000 in
-- T(1,2,2) posdef proof requires large simp for QF expansion over 6 vertices
/-- In a tree with unique degree-3 vertex, if some arm has length 1 (a leaf neighbor),
    and the Cartan form is not positive definite, the tree has infinite representation type.
    Handles T(1,q,r): embeds Ẽ₇ if q,r ≥ 3; T(1,2,5) if q=2, r≥5; ADE contradiction otherwise. -/
private theorem single_branch_leaf_case {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
    (leaf : Fin n) (h_leaf_adj : adj v₀ leaf = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1) :
    ¬ IsFiniteTypeQuiver n adj := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj' : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv; have h3 := h_deg v
    by_contra h; push_neg at h; exact hv (h_unique v (by omega))
  -- Extract a₂, a₃: the other two neighbors of v₀ (besides leaf)
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have h_leaf_mem : leaf ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_leaf_adj⟩
  obtain ⟨a₂, a₃, ha₂₃, hS₀_eq⟩ := Finset.card_eq_two.mp (by
    rw [Finset.card_erase_of_mem h_leaf_mem, (show S₀.card = 3 from hv₀)])
  have ha₂_mem : a₂ ∈ S₀.erase leaf := hS₀_eq ▸ Finset.mem_insert_self a₂ _
  have ha₃_mem : a₃ ∈ S₀.erase leaf := hS₀_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self a₃))
  have ha₂_adj : adj v₀ a₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₂_mem)).2
  have ha₃_adj : adj v₀ a₃ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₃_mem)).2
  have ha₂_ne_leaf : a₂ ≠ leaf := Finset.ne_of_mem_erase ha₂_mem
  have ha₃_ne_leaf : a₃ ≠ leaf := Finset.ne_of_mem_erase ha₃_mem
  have hleaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj' v₀ leaf h_leaf_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj' v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj' v₀ a₃ ha₃_adj).symm
  -- Helper: extract the unique other neighbor of a degree-2 vertex
  -- (given vertex v with degree 2 and known neighbor u, returns the other neighbor w)
  have extract_other := fun (v u : Fin n) (hvu : adj v u = 1)
      (hdeg2 : vertexDegree adj v = 2) =>
    let Sv := Finset.univ.filter (fun j => adj v j = 1)
    have hcard : Sv.card = 2 := hdeg2
    have hu_mem : u ∈ Sv :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu⟩
    Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hu_mem, hcard])
  -- Case split: both a₂ and a₃ have degree 2?
  by_cases h_a2_ext : vertexDegree adj a₂ = 2
  · by_cases h_a3_ext : vertexDegree adj a₃ = 2
    · -- Both arms extend. Extract b₂, b₃.
      obtain ⟨b₂, hb₂_eq⟩ := extract_other a₂ v₀
        ((adj_comm a₂ v₀).trans ha₂_adj) h_a2_ext
      have hb₂_mem : b₂ ∈ (Finset.univ.filter (adj a₂ · = 1)).erase v₀ :=
        hb₂_eq ▸ Finset.mem_singleton_self b₂
      have hb₂_adj : adj a₂ b₂ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₂_mem)).2
      have hb₂_ne_v₀ : b₂ ≠ v₀ := Finset.ne_of_mem_erase hb₂_mem
      obtain ⟨b₃, hb₃_eq⟩ := extract_other a₃ v₀
        ((adj_comm a₃ v₀).trans ha₃_adj) h_a3_ext
      have hb₃_mem : b₃ ∈ (Finset.univ.filter (adj a₃ · = 1)).erase v₀ :=
        hb₃_eq ▸ Finset.mem_singleton_self b₃
      have hb₃_adj : adj a₃ b₃ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₃_mem)).2
      have hb₃_ne_v₀ : b₃ ≠ v₀ := Finset.ne_of_mem_erase hb₃_mem
      -- Degree constraints for b₂, b₃
      have hb₂_deg_ge1 : 1 ≤ vertexDegree adj b₂ :=
        Finset.card_pos.mpr ⟨a₂, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm b₂ a₂).trans hb₂_adj⟩⟩
      have hb₃_deg_ge1 : 1 ≤ vertexDegree adj b₃ :=
        Finset.card_pos.mpr ⟨a₃, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm b₃ a₃).trans hb₃_adj⟩⟩
      by_cases h_b2_ext : vertexDegree adj b₂ = 2
      · by_cases h_b3_ext : vertexDegree adj b₃ = 2
        · -- Both arms ≥ 3: extract c₂, c₃ and embed Ẽ₇ = T(1,3,3)
          obtain ⟨c₂, hc₂_eq⟩ := extract_other b₂ a₂
            ((adj_comm b₂ a₂).trans hb₂_adj) h_b2_ext
          have hc₂_mem : c₂ ∈ (Finset.univ.filter (adj b₂ · = 1)).erase a₂ :=
            hc₂_eq ▸ Finset.mem_singleton_self c₂
          have hc₂_adj : adj b₂ c₂ = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₂_mem)).2
          have hc₂_ne_a₂ : c₂ ≠ a₂ := Finset.ne_of_mem_erase hc₂_mem
          obtain ⟨c₃, hc₃_eq⟩ := extract_other b₃ a₃
            ((adj_comm b₃ a₃).trans hb₃_adj) h_b3_ext
          have hc₃_mem : c₃ ∈ (Finset.univ.filter (adj b₃ · = 1)).erase a₃ :=
            hc₃_eq ▸ Finset.mem_singleton_self c₃
          have hc₃_adj : adj b₃ c₃ = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₃_mem)).2
          have hc₃_ne_a₃ : c₃ ≠ a₃ := Finset.ne_of_mem_erase hc₃_mem
          -- Same-arm distinctness
          have ha₂_ne_b₂ := ne_of_adj' a₂ b₂ hb₂_adj
          have hb₂_ne_c₂ := ne_of_adj' b₂ c₂ hc₂_adj
          have ha₃_ne_b₃ := ne_of_adj' a₃ b₃ hb₃_adj
          have hb₃_ne_c₃ := ne_of_adj' b₃ c₃ hc₃_adj
          -- Reversed edge facts for path proofs
          have hb₂_a₂ : adj b₂ a₂ = 1 := (adj_comm b₂ a₂).trans hb₂_adj
          have ha₂_v₀ : adj a₂ v₀ = 1 := (adj_comm a₂ v₀).trans ha₂_adj
          have hb₃_a₃ : adj b₃ a₃ = 1 := (adj_comm b₃ a₃).trans hb₃_adj
          have ha₃_v₀ : adj a₃ v₀ = 1 := (adj_comm a₃ v₀).trans ha₃_adj
          have hc₂_b₂ : adj c₂ b₂ = 1 := (adj_comm c₂ b₂).trans hc₂_adj
          have hc₃_b₃ : adj c₃ b₃ = 1 := (adj_comm c₃ b₃).trans hc₃_adj
          -- Path helpers (nodup + edges for various lengths)
          have path_nodup4 : ∀ (a b c d : Fin n),
              a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
              [a, b, c, d].Nodup := by
            intro a b c d hab hac had hbc hbd hcd
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
          have path_edges4 : ∀ (a b c d : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d].length) →
                adj ([a, b, c, d].get ⟨k, by omega⟩)
                  ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d h₁ h₂ h₃ k hk
            have : k + 1 < 4 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
            rcases this with rfl | rfl | rfl <;> assumption
          have path_nodup5 : ∀ (a b c d e : Fin n),
              a ≠ b → a ≠ c → a ≠ d → a ≠ e →
              b ≠ c → b ≠ d → b ≠ e →
              c ≠ d → c ≠ e → d ≠ e → [a, b, c, d, e].Nodup := by
            intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
          have path_edges5 : ∀ (a b c d e : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
                adj ([a, b, c, d, e].get ⟨k, by omega⟩)
                  ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d e h₁ h₂ h₃ h₄ k hk
            have : k + 1 < 5 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
            rcases this with rfl | rfl | rfl | rfl <;> assumption
          have path_nodup6 : ∀ (a b c d e f : Fin n),
              a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f →
              b ≠ c → b ≠ d → b ≠ e → b ≠ f →
              c ≠ d → c ≠ e → c ≠ f →
              d ≠ e → d ≠ f → e ≠ f → [a, b, c, d, e, f].Nodup := by
            intro a b c d e f hab hac had hae haf hbc hbd hbe hbf
              hcd hce hcf hde hdf hef
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩,
              ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩
          have path_edges6 : ∀ (a b c d e f : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 →
              adj d e = 1 → adj e f = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d, e, f].length) →
                adj ([a, b, c, d, e, f].get ⟨k, by omega⟩)
                  ([a, b, c, d, e, f].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d e f h₁ h₂ h₃ h₄ h₅ k hk
            have : k + 1 < 6 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
          have path_nodup7 : ∀ (a b c d e f g : Fin n),
              a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ f → a ≠ g →
              b ≠ c → b ≠ d → b ≠ e → b ≠ f → b ≠ g →
              c ≠ d → c ≠ e → c ≠ f → c ≠ g →
              d ≠ e → d ≠ f → d ≠ g →
              e ≠ f → e ≠ g → f ≠ g → [a, b, c, d, e, f, g].Nodup := by
            intro a b c d e f g hab hac had hae haf hag hbc hbd hbe hbf hbg
              hcd hce hcf hcg hde hdf hdg hef heg hfg
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had, hae, haf, hag⟩, ⟨hbc, hbd, hbe, hbf, hbg⟩,
              ⟨hcd, hce, hcf, hcg⟩, ⟨hde, hdf, hdg⟩, ⟨hef, heg⟩, hfg⟩
          have path_edges7 : ∀ (a b c d e f g : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
              adj e f = 1 → adj f g = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d, e, f, g].length) →
                adj ([a, b, c, d, e, f, g].get ⟨k, by omega⟩)
                  ([a, b, c, d, e, f, g].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d e f g h₁ h₂ h₃ h₄ h₅ h₆ k hk
            have : k + 1 < 7 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
          -- Triangle non-edges (distance 2)
          have hleaf_a₂ : adj leaf a₂ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ leaf a₂
              ha₂_ne_leaf.symm hleaf_ne_v₀ ha₂_ne_v₀ h_leaf_adj ha₂_adj
          have hleaf_a₃ : adj leaf a₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ leaf a₃
              ha₃_ne_leaf.symm hleaf_ne_v₀ ha₃_ne_v₀ h_leaf_adj ha₃_adj
          have ha₂a₃ : adj a₂ a₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₂ a₃
              ha₂₃ ha₂_ne_v₀ ha₃_ne_v₀ ha₂_adj ha₃_adj
          have hv₀b₂ : adj v₀ b₂ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic a₂ v₀ b₂
              hb₂_ne_v₀.symm ha₂_ne_v₀.symm ha₂_ne_b₂.symm
              ha₂_v₀ hb₂_adj
          have hv₀b₃ : adj v₀ b₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic a₃ v₀ b₃
              hb₃_ne_v₀.symm ha₃_ne_v₀.symm ha₃_ne_b₃.symm
              ha₃_v₀ hb₃_adj
          have ha₂c₂ : adj a₂ c₂ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic b₂ a₂ c₂
              hc₂_ne_a₂.symm ha₂_ne_b₂ hb₂_ne_c₂.symm
              hb₂_a₂ hc₂_adj
          have ha₃c₃ : adj a₃ c₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic b₃ a₃ c₃
              hc₃_ne_a₃.symm ha₃_ne_b₃ hb₃_ne_c₃.symm
              hb₃_a₃ hc₃_adj
          -- Cross-arm distinctness (level 1: from triangle non-edges)
          have hleaf_ne_b₂ : leaf ≠ b₂ := by
            intro h; rw [← h] at hb₂_adj
            linarith [adj_comm a₂ leaf, hleaf_a₂]
          have hleaf_ne_b₃ : leaf ≠ b₃ := by
            intro h; rw [← h] at hb₃_adj
            linarith [adj_comm a₃ leaf, hleaf_a₃]
          have ha₂_ne_b₃ : a₂ ≠ b₃ := by
            intro h; rw [h] at ha₂_adj; linarith [hv₀b₃]
          have ha₃_ne_b₂ : a₃ ≠ b₂ := by
            intro h; rw [h] at ha₃_adj; linarith [hv₀b₂]
          have hv₀_ne_c₂ : v₀ ≠ c₂ := by
            intro h; rw [← h] at hc₂_adj; linarith [adj_comm b₂ v₀, hv₀b₂]
          have hv₀_ne_c₃ : v₀ ≠ c₃ := by
            intro h; rw [← h] at hc₃_adj; linarith [adj_comm b₃ v₀, hv₀b₃]
          -- Path-3 non-edges (distance 3)
          have hleaf_b₂ : adj leaf b₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [b₂, a₂, v₀, leaf] (by simp)
              (path_nodup4 _ _ _ _ ha₂_ne_b₂.symm hb₂_ne_v₀ hleaf_ne_b₂.symm
                ha₂_ne_v₀ ha₂_ne_leaf hleaf_ne_v₀.symm)
              (path_edges4 _ _ _ _ hb₂_a₂ ha₂_v₀ h_leaf_adj)
          have hleaf_b₃ : adj leaf b₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [b₃, a₃, v₀, leaf] (by simp)
              (path_nodup4 _ _ _ _ ha₃_ne_b₃.symm hb₃_ne_v₀ hleaf_ne_b₃.symm
                ha₃_ne_v₀ ha₃_ne_leaf hleaf_ne_v₀.symm)
              (path_edges4 _ _ _ _ hb₃_a₃ ha₃_v₀ h_leaf_adj)
          have ha₂b₃ : adj a₂ b₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [b₃, a₃, v₀, a₂] (by simp)
              (path_nodup4 _ _ _ _ ha₃_ne_b₃.symm hb₃_ne_v₀ ha₂_ne_b₃.symm
                ha₃_ne_v₀ ha₂₃.symm ha₂_ne_v₀.symm)
              (path_edges4 _ _ _ _ hb₃_a₃ ha₃_v₀ ha₂_adj)
          have ha₃b₂ : adj a₃ b₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [b₂, a₂, v₀, a₃] (by simp)
              (path_nodup4 _ _ _ _ ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
                ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
              (path_edges4 _ _ _ _ hb₂_a₂ ha₂_v₀ ha₃_adj)
          have hv₀c₂ : adj v₀ c₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₂, b₂, a₂, v₀] (by simp)
              (path_nodup4 _ _ _ _ hb₂_ne_c₂.symm hc₂_ne_a₂ hv₀_ne_c₂.symm
                ha₂_ne_b₂.symm hb₂_ne_v₀ ha₂_ne_v₀)
              (path_edges4 _ _ _ _ hc₂_b₂ hb₂_a₂ ha₂_v₀)
          have hv₀c₃ : adj v₀ c₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₃, b₃, a₃, v₀] (by simp)
              (path_nodup4 _ _ _ _ hb₃_ne_c₃.symm hc₃_ne_a₃ hv₀_ne_c₃.symm
                ha₃_ne_b₃.symm hb₃_ne_v₀ ha₃_ne_v₀)
              (path_edges4 _ _ _ _ hc₃_b₃ hb₃_a₃ ha₃_v₀)
          -- Cross-arm distinctness (level 2: from path non-edges)
          have hleaf_ne_c₂ : leaf ≠ c₂ := by
            intro h; rw [h] at h_leaf_adj; linarith [hv₀c₂]
          have hleaf_ne_c₃ : leaf ≠ c₃ := by
            intro h; rw [h] at h_leaf_adj; linarith [hv₀c₃]
          have ha₂_ne_c₃ : a₂ ≠ c₃ := by
            intro h; rw [h] at ha₂_adj; linarith [hv₀c₃]
          have ha₃_ne_c₂ : a₃ ≠ c₂ := by
            intro h; rw [h] at ha₃_adj; linarith [hv₀c₂]
          have hb₂_ne_b₃ : b₂ ≠ b₃ := by
            intro h; rw [← h] at hb₃_adj
            exact h_acyclic [b₂, a₂, v₀, a₃] (by simp)
              (path_nodup4 _ _ _ _ ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
                ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
              (path_edges4 _ _ _ _ hb₂_a₂ ha₂_v₀ ha₃_adj) hb₃_adj
          -- c₂ ≠ c₃ via cycle: [c₂, b₂, a₂, v₀, a₃, b₃] would close
          have hc₂_ne_c₃ : c₂ ≠ c₃ := by
            intro h; rw [← h] at hc₃_adj
            -- hc₃_adj is now adj b₃ c₂ = 1; derive c₂ ≠ b₃
            have hc₂_ne_b₃ : c₂ ≠ b₃ := (ne_of_adj' b₃ c₂ hc₃_adj).symm
            exact h_acyclic [c₂, b₂, a₂, v₀, a₃, b₃] (by simp)
              (path_nodup6 _ _ _ _ _ _ hb₂_ne_c₂.symm hc₂_ne_a₂
                hv₀_ne_c₂.symm ha₃_ne_c₂.symm hc₂_ne_b₃
                ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm hb₂_ne_b₃
                ha₂_ne_v₀ ha₂₃ ha₂_ne_b₃ ha₃_ne_v₀.symm
                hb₃_ne_v₀.symm ha₃_ne_b₃)
              (path_edges6 _ _ _ _ _ _ hc₂_b₂ hb₂_a₂ ha₂_v₀ ha₃_adj hb₃_adj)
              hc₃_adj
          have hb₂_ne_c₃ : b₂ ≠ c₃ := by
            intro h; rw [← h] at hc₃_adj
            -- hc₃_adj is now adj b₃ b₂ = 1
            -- cycle: b₂ - a₂ - v₀ - a₃ - b₃ - b₂
            exact h_acyclic [b₂, a₂, v₀, a₃, b₃] (by simp)
              (path_nodup5 _ _ _ _ _ ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
                hb₂_ne_b₃ ha₂_ne_v₀ ha₂₃ ha₂_ne_b₃
                ha₃_ne_v₀.symm hb₃_ne_v₀.symm ha₃_ne_b₃)
              (path_edges5 _ _ _ _ _ hb₂_a₂ ha₂_v₀ ha₃_adj hb₃_adj)
              hc₃_adj
          have hb₃_ne_c₂ : b₃ ≠ c₂ := by
            intro h; rw [← h] at hc₂_adj
            -- hc₂_adj is now adj b₂ b₃ = 1
            -- cycle: b₃ - a₃ - v₀ - a₂ - b₂ - b₃
            exact h_acyclic [b₃, a₃, v₀, a₂, b₂] (by simp)
              (path_nodup5 _ _ _ _ _ ha₃_ne_b₃.symm hb₃_ne_v₀ ha₂_ne_b₃.symm
                hb₂_ne_b₃.symm ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂
                ha₂_ne_v₀.symm hb₂_ne_v₀.symm ha₂_ne_b₂)
              (path_edges5 _ _ _ _ _ hb₃_a₃ ha₃_v₀ ha₂_adj hb₂_adj)
              hc₂_adj
          -- Remaining non-edges (distance 4+)
          have hleaf_c₂ : adj leaf c₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₂, b₂, a₂, v₀, leaf] (by simp)
              (path_nodup5 _ _ _ _ _ hb₂_ne_c₂.symm hc₂_ne_a₂ hv₀_ne_c₂.symm
                hleaf_ne_c₂.symm ha₂_ne_b₂.symm hb₂_ne_v₀ hleaf_ne_b₂.symm
                ha₂_ne_v₀ ha₂_ne_leaf hleaf_ne_v₀.symm)
              (path_edges5 _ _ _ _ _ hc₂_b₂ hb₂_a₂ ha₂_v₀ h_leaf_adj)
          have hleaf_c₃ : adj leaf c₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₃, b₃, a₃, v₀, leaf] (by simp)
              (path_nodup5 _ _ _ _ _ hb₃_ne_c₃.symm hc₃_ne_a₃ hv₀_ne_c₃.symm
                hleaf_ne_c₃.symm ha₃_ne_b₃.symm hb₃_ne_v₀ hleaf_ne_b₃.symm
                ha₃_ne_v₀ ha₃_ne_leaf hleaf_ne_v₀.symm)
              (path_edges5 _ _ _ _ _ hc₃_b₃ hb₃_a₃ ha₃_v₀ h_leaf_adj)
          have ha₂c₃ : adj a₂ c₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₃, b₃, a₃, v₀, a₂] (by simp)
              (path_nodup5 _ _ _ _ _ hb₃_ne_c₃.symm hc₃_ne_a₃ hv₀_ne_c₃.symm
                ha₂_ne_c₃.symm ha₃_ne_b₃.symm hb₃_ne_v₀ ha₂_ne_b₃.symm
                ha₃_ne_v₀ ha₂₃.symm ha₂_ne_v₀.symm)
              (path_edges5 _ _ _ _ _ hc₃_b₃ hb₃_a₃ ha₃_v₀ ha₂_adj)
          have ha₃c₂ : adj a₃ c₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₂, b₂, a₂, v₀, a₃] (by simp)
              (path_nodup5 _ _ _ _ _ hb₂_ne_c₂.symm hc₂_ne_a₂ hv₀_ne_c₂.symm
                ha₃_ne_c₂.symm ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
                ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
              (path_edges5 _ _ _ _ _ hc₂_b₂ hb₂_a₂ ha₂_v₀ ha₃_adj)
          have hb₂b₃ : adj b₂ b₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [b₃, a₃, v₀, a₂, b₂] (by simp)
              (path_nodup5 _ _ _ _ _ ha₃_ne_b₃.symm hb₃_ne_v₀ ha₂_ne_b₃.symm
                hb₂_ne_b₃.symm ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂
                ha₂_ne_v₀.symm hb₂_ne_v₀.symm ha₂_ne_b₂)
              (path_edges5 _ _ _ _ _ hb₃_a₃ ha₃_v₀ ha₂_adj hb₂_adj)
          have hb₂c₃ : adj b₂ c₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₃, b₃, a₃, v₀, a₂, b₂] (by simp)
              (path_nodup6 _ _ _ _ _ _ hb₃_ne_c₃.symm hc₃_ne_a₃
                hv₀_ne_c₃.symm ha₂_ne_c₃.symm hb₂_ne_c₃.symm
                ha₃_ne_b₃.symm hb₃_ne_v₀ ha₂_ne_b₃.symm
                hb₂_ne_b₃.symm ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂
                ha₂_ne_v₀.symm hb₂_ne_v₀.symm ha₂_ne_b₂)
              (path_edges6 _ _ _ _ _ _
                hc₃_b₃ hb₃_a₃ ha₃_v₀ ha₂_adj hb₂_adj)
          have hb₃c₂ : adj b₃ c₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₂, b₂, a₂, v₀, a₃, b₃] (by simp)
              (path_nodup6 _ _ _ _ _ _ hb₂_ne_c₂.symm hc₂_ne_a₂
                hv₀_ne_c₂.symm ha₃_ne_c₂.symm hb₃_ne_c₂.symm
                ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
                hb₂_ne_b₃ ha₂_ne_v₀ ha₂₃ ha₂_ne_b₃
                ha₃_ne_v₀.symm hb₃_ne_v₀.symm ha₃_ne_b₃)
              (path_edges6 _ _ _ _ _ _
                hc₂_b₂ hb₂_a₂ ha₂_v₀ ha₃_adj hb₃_adj)
          have hc₂c₃ : adj c₂ c₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [c₃, b₃, a₃, v₀, a₂, b₂, c₂] (by simp)
              (path_nodup7 _ _ _ _ _ _ _ hb₃_ne_c₃.symm hc₃_ne_a₃
                hv₀_ne_c₃.symm ha₂_ne_c₃.symm hb₂_ne_c₃.symm
                hc₂_ne_c₃.symm ha₃_ne_b₃.symm hb₃_ne_v₀
                ha₂_ne_b₃.symm hb₂_ne_b₃.symm hb₃_ne_c₂
                ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂ ha₃_ne_c₂
                ha₂_ne_v₀.symm hb₂_ne_v₀.symm hv₀_ne_c₂
                ha₂_ne_b₂ hc₂_ne_a₂.symm hb₂_ne_c₂)
              (path_edges7 _ _ _ _ _ _ _
                hc₃_b₃ hb₃_a₃ ha₃_v₀ ha₂_adj hb₂_adj hc₂_adj)
          -- Construct the embedding φ : Fin 8 ↪ Fin n for Ẽ₇ = T(1,3,3)
          -- Ẽ₇ adjacency: 0-1, 0-2, 2-3, 3-4, 0-5, 5-6, 6-7
          -- Map: 0→v₀, 1→leaf, 2→a₂, 3→b₂, 4→c₂, 5→a₃, 6→b₃, 7→c₃
          let φ_fun : Fin 8 → Fin n := fun i =>
            match i with
            | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => leaf | ⟨2, _⟩ => a₂
            | ⟨3, _⟩ => b₂  | ⟨4, _⟩ => c₂   | ⟨5, _⟩ => a₃
            | ⟨6, _⟩ => b₃  | ⟨7, _⟩ => c₃
          have φ_inj : Function.Injective φ_fun := by
            intro i j hij; simp only [φ_fun] at hij
            fin_cases i <;> fin_cases j <;> first
              | rfl
              | (exact absurd hij ‹_›)
              | (exact absurd hij.symm ‹_›)
          let φ : Fin 8 ↪ Fin n := ⟨φ_fun, φ_inj⟩
          have hembed : ∀ i j, etilde7Adj i j = adj (φ i) (φ j) := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp only [etilde7Adj, φ, φ_fun] <;> norm_num <;>
              linarith [hdiag v₀, hdiag leaf, hdiag a₂, hdiag a₃,
                hdiag b₂, hdiag b₃, hdiag c₂, hdiag c₃,
                h_leaf_adj, ha₂_adj, ha₃_adj,
                hb₂_adj, hb₃_adj, hc₂_adj, hc₃_adj,
                adj_comm v₀ leaf, adj_comm v₀ a₂, adj_comm v₀ a₃,
                adj_comm v₀ b₂, adj_comm v₀ b₃,
                adj_comm v₀ c₂, adj_comm v₀ c₃,
                adj_comm leaf a₂, adj_comm leaf a₃,
                adj_comm leaf b₂, adj_comm leaf b₃,
                adj_comm leaf c₂, adj_comm leaf c₃,
                adj_comm a₂ a₃, adj_comm a₂ b₂, adj_comm a₂ b₃,
                adj_comm a₂ c₂, adj_comm a₂ c₃,
                adj_comm a₃ b₂, adj_comm a₃ b₃,
                adj_comm a₃ c₂, adj_comm a₃ c₃,
                adj_comm b₂ b₃, adj_comm b₂ c₂, adj_comm b₂ c₃,
                adj_comm b₃ c₂, adj_comm b₃ c₃,
                adj_comm c₂ c₃,
                hleaf_a₂, hleaf_a₃, ha₂a₃, hv₀b₂, hv₀b₃,
                ha₂c₂, ha₃c₃,
                hleaf_b₂, hleaf_b₃, ha₂b₃, ha₃b₂,
                hv₀c₂, hv₀c₃,
                hleaf_c₂, hleaf_c₃, ha₂c₃, ha₃c₂, hb₂b₃,
                hb₂c₃, hb₃c₂, hc₂c₃]
          exact subgraph_infinite_type_transfer φ adj etilde7Adj hsymm
            (fun v h => by linarith [hdiag v]) hembed
            etilde7_not_finite_type
        · -- b₃ is leaf (T(1,≥3,2)): arm2 has length ≥ 3, arm3 has length 2.
          -- The tree is T(1,q,2) with q ≥ 3.
          -- ADE types: T(1,3,2)=E₆, T(1,4,2)=E₇, T(1,5,2)=E₈ → positive definite.
          -- If arm2 ≥ 6 (i.e. q ≥ 6): embed T(1,2,5) → infinite type.
          -- Extract c₂ (neighbor of b₂ past a₂), then case split on further extensions.
          have hb₃_deg1 : vertexDegree adj b₃ = 1 := by
            have := h_deg_le2 b₃ hb₃_ne_v₀; omega
          obtain ⟨c₂, hc₂_eq⟩ := extract_other b₂ a₂
            ((adj_comm b₂ a₂).trans hb₂_adj) h_b2_ext
          have hc₂_mem : c₂ ∈ (Finset.univ.filter (adj b₂ · = 1)).erase a₂ :=
            hc₂_eq ▸ Finset.mem_singleton_self c₂
          have hc₂_adj : adj b₂ c₂ = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₂_mem)).2
          have hc₂_ne_a₂ : c₂ ≠ a₂ := Finset.ne_of_mem_erase hc₂_mem
          have hc₂_deg_ge1 : 1 ≤ vertexDegree adj c₂ :=
            Finset.card_pos.mpr ⟨b₂, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (adj_comm c₂ b₂).trans hc₂_adj⟩⟩
          by_cases h_c2_ext : vertexDegree adj c₂ = 2
          · -- arm2 ≥ 4 (c₂ extends): extract d₂, then further split
            obtain ⟨d₂, hd₂_eq⟩ := extract_other c₂ b₂
              ((adj_comm c₂ b₂).trans hc₂_adj) h_c2_ext
            have hd₂_mem : d₂ ∈ (Finset.univ.filter (adj c₂ · = 1)).erase b₂ :=
              hd₂_eq ▸ Finset.mem_singleton_self d₂
            have hd₂_adj : adj c₂ d₂ = 1 :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd₂_mem)).2
            have hd₂_ne_b₂ : d₂ ≠ b₂ := Finset.ne_of_mem_erase hd₂_mem
            have hd₂_deg_ge1 : 1 ≤ vertexDegree adj d₂ :=
              Finset.card_pos.mpr ⟨c₂, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (adj_comm d₂ c₂).trans hd₂_adj⟩⟩
            by_cases h_d2_ext : vertexDegree adj d₂ = 2
            · -- arm2 ≥ 5 (d₂ extends): extract e₂, then further split
              obtain ⟨e₂, he₂_eq⟩ := extract_other d₂ c₂
                ((adj_comm d₂ c₂).trans hd₂_adj) h_d2_ext
              have he₂_mem : e₂ ∈ (Finset.univ.filter (adj d₂ · = 1)).erase c₂ :=
                he₂_eq ▸ Finset.mem_singleton_self e₂
              have he₂_adj : adj d₂ e₂ = 1 :=
                (Finset.mem_filter.mp (Finset.mem_of_mem_erase he₂_mem)).2
              have he₂_ne_c₂ : e₂ ≠ c₂ := Finset.ne_of_mem_erase he₂_mem
              by_cases h_e2_ext : vertexDegree adj e₂ = 2
              · -- arm2 ≥ 6: T(1,≥6,2) contains T(1,5,2) = T(1,2,5) = E₈ extended.
                -- Embed T(1,2,5) using vertices leaf, v₀, a₂, b₂, c₂, d₂, e₂, a₃, b₃.
                -- t125Adj: 0-center, 1-leaf1, 0-2-3, 0-4-5-6-7-8
                -- Map: 0→v₀, 1→leaf, 2→a₂, 3→b₂, 4→a₃, 5→b₃(?), but b₃ is a leaf...
                -- Actually T(1,2,5): arms of length 1,2,5 from center.
                -- We have: leaf(arm1), a₂-b₂(arm2 not quite...), longer arm...
                -- Embed: 0→v₀, 1→leaf, 2→a₃, 3→b₃, 4→a₂, 5→b₂, 6→c₂, 7→d₂, 8→e₂
                -- arm1: leaf (length 1), arm2: a₃-b₃ (length 2), arm3: a₂-b₂-c₂-d₂-e₂ (≥5)
                -- But b₃ has degree 1 (= leaf in this arm), so T(1,2,≥5): embed T(1,2,5).
                exact embed_t125_in_tree adj hsymm hdiag h01 h_acyclic
                  v₀ leaf a₃ b₃ a₂ b₂ c₂ d₂ e₂
                  h_leaf_adj ha₃_adj hb₃_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj he₂_adj
                  ha₃_ne_leaf.symm ha₂_ne_leaf.symm ha₂₃.symm hb₃_ne_v₀ hb₂_ne_v₀
                  hc₂_ne_a₂ hd₂_ne_b₂ he₂_ne_c₂
              · -- e₂ is leaf: arm2 has length exactly 5. T(1,5,2)=T(1,2,5)=Ẽ₈ has infinite type.
                -- The 9 named vertices already form T(1,2,5), so embed them directly.
                exact embed_t125_in_tree adj hsymm hdiag h01 h_acyclic
                  v₀ leaf a₃ b₃ a₂ b₂ c₂ d₂ e₂
                  h_leaf_adj ha₃_adj hb₃_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj he₂_adj
                  ha₃_ne_leaf.symm ha₂_ne_leaf.symm ha₂₃.symm hb₃_ne_v₀ hb₂_ne_v₀
                  hc₂_ne_a₂ hd₂_ne_b₂ he₂_ne_c₂
            · -- d₂ is leaf: arm2 has length exactly 4. T(1,4,2)=T(1,2,4)=E₇ → posdef → contradiction
              exfalso
              apply h_not_posdef
              -- d₂ has degree 1
              have hd₂_ne_v₀ : d₂ ≠ v₀ := by
                intro h
                have hv₀_ne_a₂ : v₀ ≠ a₂ := ne_of_adj' v₀ a₂ ha₂_adj
                have ha₂_ne_b₂ : a₂ ≠ b₂ := ne_of_adj' a₂ b₂ hb₂_adj
                have hb₂_ne_c₂ : b₂ ≠ c₂ := ne_of_adj' b₂ c₂ hc₂_adj
                have hv₀_ne_b₂ : v₀ ≠ b₂ := hb₂_ne_v₀.symm
                have hv₀_ne_c₂ : v₀ ≠ c₂ := by
                  intro heq; rw [h, heq] at hd₂_adj; linarith [hdiag c₂]
                have ha₂_ne_c₂ : a₂ ≠ c₂ := hc₂_ne_a₂.symm
                have h_nonadj : adj c₂ v₀ = 0 := acyclic_path_nonadj adj hsymm h01 h_acyclic
                  [v₀, a₂, b₂, c₂] (by simp)
                  (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
                      exact ⟨⟨hv₀_ne_a₂, hv₀_ne_b₂, hv₀_ne_c₂⟩, ⟨ha₂_ne_b₂, ha₂_ne_c₂⟩, hb₂_ne_c₂⟩)
                  (by intro k hk
                      have : k + 1 < 4 := by simpa using hk
                      have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
                      rcases this with rfl | rfl | rfl
                      · exact ha₂_adj
                      · exact hb₂_adj
                      · exact hc₂_adj)
                have hcv : adj c₂ v₀ = 1 := by rw [← h]; exact hd₂_adj
                linarith [hcv, h_nonadj]
              have hd₂_deg1 : vertexDegree adj d₂ = 1 := by
                have := h_deg_le2 d₂ hd₂_ne_v₀; omega
              -- Establish "only" facts for each named vertex
              have hv₀_only : ∀ w, adj v₀ w = 1 → w = leaf ∨ w = a₂ ∨ w = a₃ := by
                intro w hw
                have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwl : w = leaf; · left; exact hwl
                have hw_mem' : w ∈ S₀.erase leaf := Finset.mem_erase.mpr ⟨hwl, hw_mem⟩
                rw [hS₀_eq] at hw_mem'
                rcases Finset.mem_insert.mp hw_mem' with h | h
                · right; left; exact h
                · right; right; exact Finset.mem_singleton.mp h
              have hleaf_only : ∀ w, adj leaf w = 1 → w = v₀ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj leaf := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj leaf j = 1)).card
                  have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm leaf v₀).trans h_leaf_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({v₀, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have ha₂_only : ∀ w, adj a₂ w = 1 → w = v₀ ∨ w = b₂ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwv : w = v₀; · left; exact hwv
                right
                have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj a₂ j = 1)).erase v₀ :=
                  Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
                rw [hb₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hb₂_only : ∀ w, adj b₂ w = 1 → w = a₂ ∨ w = c₂ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwa : w = a₂; · left; exact hwa
                right
                have ha₂_in : a₂ ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₂ a₂).trans hb₂_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj b₂ j = 1)).erase a₂ :=
                  Finset.mem_erase.mpr ⟨hwa, hw_mem⟩
                rw [hc₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hc₂_only : ∀ w, adj c₂ w = 1 → w = b₂ ∨ w = d₂ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj c₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwb : w = b₂; · left; exact hwb
                right
                have hb₂_in : b₂ ∈ Finset.univ.filter (fun j => adj c₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm c₂ b₂).trans hc₂_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj c₂ j = 1)).erase b₂ :=
                  Finset.mem_erase.mpr ⟨hwb, hw_mem⟩
                rw [hd₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hd₂_only : ∀ w, adj d₂ w = 1 → w = c₂ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj d₂ := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj d₂ j = 1)).card
                  have hc₂_in : c₂ ∈ Finset.univ.filter (fun j => adj d₂ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm d₂ c₂).trans hd₂_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj d₂ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({c₂, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have ha₃_only : ∀ w, adj a₃ w = 1 → w = v₀ ∨ w = b₃ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwv : w = v₀; · left; exact hwv
                right
                have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj a₃ j = 1)).erase v₀ :=
                  Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
                rw [hb₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hb₃_only : ∀ w, adj b₃ w = 1 → w = a₃ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj b₃ := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj b₃ j = 1)).card
                  have ha₃_in : a₃ ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₃ a₃).trans hb₃_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({a₃, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have h_all_named : ∀ w : Fin n,
                  w = v₀ ∨ w = leaf ∨ w = a₂ ∨ w = b₂ ∨ w = c₂ ∨ w = d₂ ∨
                  w = a₃ ∨ w = b₃ := by
                apply connected_closed_set_is_all adj hconn
                  (fun w => w = v₀ ∨ w = leaf ∨ w = a₂ ∨ w = b₂ ∨ w = c₂ ∨ w = d₂ ∨
                    w = a₃ ∨ w = b₃) v₀ (Or.inl rfl)
                intro v w hv hvw
                rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · -- v = v₀: hvw : adj v₀ w = 1
                  rcases hv₀_only w hvw with rfl | rfl | rfl
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                · -- v = leaf: hvw : adj leaf w = 1
                  rcases hleaf_only w hvw with rfl
                  exact Or.inl rfl
                · -- v = a₂: hvw : adj a₂ w = 1
                  rcases ha₂_only w hvw with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                · -- v = b₂: hvw : adj b₂ w = 1
                  rcases hb₂_only w hvw with rfl | rfl
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · -- v = c₂: hvw : adj c₂ w = 1
                  rcases hc₂_only w hvw with rfl | rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                · -- v = d₂: hvw : adj d₂ w = 1
                  rcases hd₂_only w hvw with rfl
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · -- v = a₃: hvw : adj a₃ w = 1
                  rcases ha₃_only w hvw with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
                · -- v = b₃: hvw : adj b₃ w = 1
                  rcases hb₃_only w hvw with rfl
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
              have hb₃_deg1 : vertexDegree adj b₃ = 1 := by
                have := h_deg_le2 b₃ hb₃_ne_v₀; omega
              have hd_e8 : E8Distinct v₀ leaf a₂ b₂ c₂ d₂ a₃ b₃ := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · exact ne_of_adj' v₀ leaf h_leaf_adj
                · exact ne_of_adj' v₀ a₂ ha₂_adj
                · intro h; subst h
                  rcases hb₂_only leaf h_leaf_adj with rfl | rfl
                  · linarith [h_leaf_deg, h_a2_ext]
                  · linarith [h_leaf_deg, h_c2_ext]
                · intro h; subst h
                  rcases hc₂_only a₂ ha₂_adj with rfl | rfl
                  · linarith [hdiag a₂, hb₂_adj]
                  · linarith [h_a2_ext, hd₂_deg1]
                · intro h; subst h; exact absurd rfl hd₂_ne_v₀
                · exact ne_of_adj' v₀ a₃ ha₃_adj
                · intro heq; linarith [hv₀, heq ▸ hb₃_deg1]
                · exact ha₂_ne_leaf.symm
                · intro h; linarith [h_leaf_deg, h ▸ h_b2_ext]
                · intro h; linarith [h_leaf_deg, h ▸ h_c2_ext]
                · intro h; subst h
                  have : c₂ = v₀ := hleaf_only c₂ ((adj_comm leaf c₂).trans hd₂_adj)
                  subst this; linarith [hv₀, h_c2_ext]
                · exact ha₃_ne_leaf.symm
                · intro h; subst h
                  have : a₃ = v₀ := hleaf_only a₃ ((adj_comm leaf a₃).trans hb₃_adj)
                  subst this; linarith [hv₀, h_a3_ext]
                · exact ne_of_adj' a₂ b₂ hb₂_adj
                · intro h; subst h
                  rcases ha₂_only d₂ hd₂_adj with rfl | rfl
                  · linarith [hv₀, hd₂_deg1]
                  · linarith [h_b2_ext, hd₂_deg1]
                · intro h; linarith [h_a2_ext, h ▸ hd₂_deg1]
                · exact ha₂₃
                · intro h; linarith [h_a2_ext, h ▸ hb₃_deg1]
                · exact ne_of_adj' b₂ c₂ hc₂_adj
                · intro h; linarith [h_b2_ext, h ▸ hd₂_deg1]
                · intro h
                  rw [h] at hb₂_only
                  rcases hb₂_only v₀ ((adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
                  · linarith [hv₀, h_a2_ext]
                  · linarith [hv₀, h_c2_ext]
                · intro h; linarith [h_b2_ext, h ▸ hb₃_deg1]
                · exact ne_of_adj' c₂ d₂ hd₂_adj
                · intro h
                  rw [h] at hc₂_only
                  rcases hc₂_only v₀ ((adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
                  · linarith [hv₀, h_b2_ext]
                  · linarith [hv₀, hd₂_deg1]
                · intro h; linarith [h_c2_ext, h ▸ hb₃_deg1]
                · intro h; linarith [hd₂_deg1, h ▸ h_a3_ext]
                · intro h; subst h
                  have ha₃_eq_c₂ := hd₂_only a₃ ((adj_comm d₂ a₃).trans hb₃_adj)
                  rcases hc₂_only v₀ (ha₃_eq_c₂ ▸ (adj_comm a₃ v₀).trans ha₃_adj) with rfl | rfl
                  · linarith [hv₀, h_b2_ext]
                  · linarith [hv₀, hd₂_deg1]
                · exact ne_of_adj' a₃ b₃ hb₃_adj
              intro x hx
              exact e8_posdef adj hsymm hdiag h01 v₀ leaf a₂ b₂ c₂ d₂ a₃ b₃ hd_e8
                h_leaf_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj ha₃_adj hb₃_adj
                hv₀_only hleaf_only ha₂_only hb₂_only hc₂_only hd₂_only
                ha₃_only hb₃_only h_all_named x hx
          · -- c₂ is leaf: arm2 has length exactly 3. T(1,3,2)=T(1,2,3)=E₆ → posdef → contradiction
            exfalso
            apply h_not_posdef
            -- T(1,3,2) = E₇: 7 vertices, posdef by e7_tree_posdef
            have hc₂_ne_v₀ : c₂ ≠ v₀ := by
              intro heq
              have hb₂v₀ : adj v₀ b₂ = 1 := by
                rw [adj_comm]; rw [heq] at hc₂_adj; exact hc₂_adj
              have hv₀_nbrs := deg3_three_neighbors h_leaf_adj ha₂_adj
                ha₃_adj ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hv₀
              rcases hv₀_nbrs b₂ hb₂v₀ with h_eq | h_eq | h_eq
              · -- b₂ = leaf: degree mismatch
                rw [h_eq] at h_b2_ext; omega
              · -- b₂ = a₂: adj a₂ a₂ = 1 contradicts diagonal
                rw [h_eq] at hb₂_adj; have := hdiag a₂; omega
              · -- b₂ = a₃: a₃'s neighbors are v₀ and b₃,
                -- but also a₂
                rw [h_eq] at hb₂_adj
                have ha₃_nbrs := deg2_two_neighbors
                  ((adj_comm a₃ v₀).trans ha₃_adj)
                  hb₃_adj hb₃_ne_v₀.symm h_a3_ext
                rcases ha₃_nbrs a₂
                  ((adj_comm a₃ a₂).trans hb₂_adj) with h' | h'
                · exact ha₂_ne_v₀ h'
                · rw [h'] at h_a2_ext; omega
            have hc₂_deg1 : vertexDegree adj c₂ = 1 := by
              have hle := h_deg_le2 c₂ hc₂_ne_v₀; omega
            exact e7_tree_posdef adj hsymm hdiag h01 hconn h_acyclic
              v₀ leaf a₂ b₂ c₂ a₃ b₃
              h_leaf_adj ha₂_adj ha₃_adj hb₂_adj hc₂_adj hb₃_adj
              hv₀ h_leaf_deg h_a2_ext h_a3_ext h_b2_ext
              hc₂_deg1 hb₃_deg1
      · -- b₂ is leaf (arm2 length = 2): T(1,2,≥q) with q ≥ 2 (arm3 = a₃-b₃-...).
        -- T(1,2,3)=E₆, T(1,2,4)=E₇, T(1,2,5)=E₈ → posdef contradiction; T(1,2,≥6) → embed T(1,2,5).
        have hb₂_deg1 : vertexDegree adj b₂ = 1 := by
          have := h_deg_le2 b₂ hb₂_ne_v₀; omega
        -- Case split on whether b₃ has degree 2 (arm3 extends beyond b₃)
        by_cases h_b3_ext' : vertexDegree adj b₃ = 2
        · obtain ⟨c₃, hc₃_eq⟩ := extract_other b₃ a₃
            ((adj_comm b₃ a₃).trans hb₃_adj) h_b3_ext'
          have hc₃_mem : c₃ ∈ (Finset.univ.filter (adj b₃ · = 1)).erase a₃ :=
            hc₃_eq ▸ Finset.mem_singleton_self c₃
          have hc₃_adj : adj b₃ c₃ = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc₃_mem)).2
          have hc₃_ne_a₃ : c₃ ≠ a₃ := Finset.ne_of_mem_erase hc₃_mem
          have hc₃_deg_ge1 : 1 ≤ vertexDegree adj c₃ :=
            Finset.card_pos.mpr ⟨b₃, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (adj_comm c₃ b₃).trans hc₃_adj⟩⟩
          by_cases h_c3_ext : vertexDegree adj c₃ = 2
          · obtain ⟨d₃, hd₃_eq⟩ := extract_other c₃ b₃
              ((adj_comm c₃ b₃).trans hc₃_adj) h_c3_ext
            have hd₃_mem : d₃ ∈ (Finset.univ.filter (adj c₃ · = 1)).erase b₃ :=
              hd₃_eq ▸ Finset.mem_singleton_self d₃
            have hd₃_adj : adj c₃ d₃ = 1 :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd₃_mem)).2
            have hd₃_ne_b₃ : d₃ ≠ b₃ := Finset.ne_of_mem_erase hd₃_mem
            have hd₃_deg_ge1 : 1 ≤ vertexDegree adj d₃ :=
              Finset.card_pos.mpr ⟨c₃, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (adj_comm d₃ c₃).trans hd₃_adj⟩⟩
            by_cases h_d3_ext : vertexDegree adj d₃ = 2
            · obtain ⟨e₃, he₃_eq⟩ := extract_other d₃ c₃
                ((adj_comm d₃ c₃).trans hd₃_adj) h_d3_ext
              have he₃_mem : e₃ ∈ (Finset.univ.filter (adj d₃ · = 1)).erase c₃ :=
                he₃_eq ▸ Finset.mem_singleton_self e₃
              have he₃_adj : adj d₃ e₃ = 1 :=
                (Finset.mem_filter.mp (Finset.mem_of_mem_erase he₃_mem)).2
              have he₃_ne_c₃ : e₃ ≠ c₃ := Finset.ne_of_mem_erase he₃_mem
              by_cases h_e3_ext : vertexDegree adj e₃ = 2
              · -- arm3 ≥ 6: T(1,2,≥6) contains T(1,2,5). Embed:
                -- 0→v₀, 1→leaf, 2→a₂, 3→b₂, 4→a₃, 5→b₃, 6→c₃, 7→d₃, 8→e₃
                -- T(1,2,5): center(0), arm1=1(1), arm2=2-3(2), arm3=4-5-6-7-8(5)
                exact embed_t125_in_tree adj hsymm hdiag h01 h_acyclic
                  v₀ leaf a₂ b₂ a₃ b₃ c₃ d₃ e₃
                  h_leaf_adj ha₂_adj hb₂_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj he₃_adj
                  ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hb₂_ne_v₀ hb₃_ne_v₀
                  hc₃_ne_a₃ hd₃_ne_b₃ he₃_ne_c₃
              · -- e₃ is leaf: arm3 length = 5. T(1,2,5) = Ẽ₈ has infinite type.
                -- The 9 named vertices already form T(1,2,5), so embed them directly.
                exact embed_t125_in_tree adj hsymm hdiag h01 h_acyclic
                  v₀ leaf a₂ b₂ a₃ b₃ c₃ d₃ e₃
                  h_leaf_adj ha₂_adj hb₂_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj he₃_adj
                  ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hb₂_ne_v₀ hb₃_ne_v₀
                  hc₃_ne_a₃ hd₃_ne_b₃ he₃_ne_c₃
            · -- d₃ is leaf: arm3 length = 4. T(1,2,4) = E₇ → posdef → contradiction
              exfalso; apply h_not_posdef
              -- Mapping: v₀→v₀, l→leaf, a→a₃, b→b₃, c→c₃, d→d₃, p→a₂, q→b₂
              have hd₃_ne_v₀ : d₃ ≠ v₀ := by
                intro h
                have hv₀_ne_a₃ : v₀ ≠ a₃ := ne_of_adj' v₀ a₃ ha₃_adj
                have ha₃_ne_b₃ : a₃ ≠ b₃ := ne_of_adj' a₃ b₃ hb₃_adj
                have hb₃_ne_c₃ : b₃ ≠ c₃ := ne_of_adj' b₃ c₃ hc₃_adj
                have hv₀_ne_c₃ : v₀ ≠ c₃ := by
                  intro heq; rw [h, heq] at hd₃_adj; linarith [hdiag c₃]
                have ha₃_ne_c₃ : a₃ ≠ c₃ := hc₃_ne_a₃.symm
                have h_nonadj : adj c₃ v₀ = 0 := acyclic_path_nonadj adj hsymm h01 h_acyclic
                  [v₀, a₃, b₃, c₃] (by simp)
                  (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
                      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
                      exact ⟨⟨hv₀_ne_a₃, hb₃_ne_v₀.symm, hv₀_ne_c₃⟩, ⟨ha₃_ne_b₃, ha₃_ne_c₃⟩, hb₃_ne_c₃⟩)
                  (by intro k hk
                      have : k + 1 < 4 := by simpa using hk
                      have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
                      rcases this with rfl | rfl | rfl
                      · exact ha₃_adj
                      · exact hb₃_adj
                      · exact hc₃_adj)
                have hcv : adj c₃ v₀ = 1 := by rw [← h]; exact hd₃_adj
                linarith [hcv, h_nonadj]
              have hd₃_deg1 : vertexDegree adj d₃ = 1 := by
                have := h_deg_le2 d₃ hd₃_ne_v₀; omega
              have hv₀_only : ∀ w, adj v₀ w = 1 → w = leaf ∨ w = a₃ ∨ w = a₂ := by
                intro w hw
                have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwl : w = leaf; · left; exact hwl
                have hw_mem' : w ∈ S₀.erase leaf := Finset.mem_erase.mpr ⟨hwl, hw_mem⟩
                rw [hS₀_eq] at hw_mem'
                rcases Finset.mem_insert.mp hw_mem' with h | h
                · right; right; exact h
                · right; left; exact Finset.mem_singleton.mp h
              have hleaf_only : ∀ w, adj leaf w = 1 → w = v₀ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj leaf := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj leaf j = 1)).card
                  have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm leaf v₀).trans h_leaf_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj leaf j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({v₀, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have ha₃_only : ∀ w, adj a₃ w = 1 → w = v₀ ∨ w = b₃ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwv : w = v₀; · left; exact hwv
                right
                have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj a₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj a₃ j = 1)).erase v₀ :=
                  Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
                rw [hb₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hb₃_only : ∀ w, adj b₃ w = 1 → w = a₃ ∨ w = c₃ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwa : w = a₃; · left; exact hwa
                right
                have ha₃_in : a₃ ∈ Finset.univ.filter (fun j => adj b₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₃ a₃).trans hb₃_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj b₃ j = 1)).erase a₃ :=
                  Finset.mem_erase.mpr ⟨hwa, hw_mem⟩
                rw [hc₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hc₃_only : ∀ w, adj c₃ w = 1 → w = b₃ ∨ w = d₃ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj c₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwb : w = b₃; · left; exact hwb
                right
                have hb₃_in : b₃ ∈ Finset.univ.filter (fun j => adj c₃ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm c₃ b₃).trans hc₃_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj c₃ j = 1)).erase b₃ :=
                  Finset.mem_erase.mpr ⟨hwb, hw_mem⟩
                rw [hd₃_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hd₃_only : ∀ w, adj d₃ w = 1 → w = c₃ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj d₃ := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj d₃ j = 1)).card
                  have hc₃_in : c₃ ∈ Finset.univ.filter (fun j => adj d₃ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm d₃ c₃).trans hd₃_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj d₃ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({c₃, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have ha₂_only : ∀ w, adj a₂ w = 1 → w = v₀ ∨ w = b₂ := by
                intro w hw
                have hw_mem : w ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                by_cases hwv : w = v₀; · left; exact hwv
                right
                have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj a₂ j = 1) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩
                have hw' : w ∈ (Finset.univ.filter (fun j => adj a₂ j = 1)).erase v₀ :=
                  Finset.mem_erase.mpr ⟨hwv, hw_mem⟩
                rw [hb₂_eq] at hw'; exact Finset.mem_singleton.mp hw'
              have hb₂_only : ∀ w, adj b₂ w = 1 → w = a₂ := by
                intro w hw; by_contra hne
                have : 2 ≤ vertexDegree adj b₂ := by
                  change 2 ≤ (Finset.univ.filter (fun j => adj b₂ j = 1)).card
                  have ha₂_in : a₂ ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm b₂ a₂).trans hb₂_adj⟩
                  have hw_in : w ∈ Finset.univ.filter (fun j => adj b₂ j = 1) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
                  calc 2 = ({a₂, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne)]
                    _ ≤ _ := Finset.card_le_card (fun x hx => by
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                omega
              have h_all_named : ∀ w : Fin n,
                  w = v₀ ∨ w = leaf ∨ w = a₃ ∨ w = b₃ ∨ w = c₃ ∨ w = d₃ ∨
                  w = a₂ ∨ w = b₂ := by
                apply connected_closed_set_is_all adj hconn
                  (fun w => w = v₀ ∨ w = leaf ∨ w = a₃ ∨ w = b₃ ∨ w = c₃ ∨ w = d₃ ∨
                    w = a₂ ∨ w = b₂) v₀ (Or.inl rfl)
                intro v w hv hvw
                rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · -- v = v₀: hvw : adj v₀ w = 1
                  rcases hv₀_only w hvw with rfl | rfl | rfl
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                · -- v = leaf: hvw : adj leaf w = 1
                  rcases hleaf_only w hvw with rfl
                  exact Or.inl rfl
                · -- v = a₃: hvw : adj a₃ w = 1
                  rcases ha₃_only w hvw with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                · -- v = b₃: hvw : adj b₃ w = 1
                  rcases hb₃_only w hvw with rfl | rfl
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · -- v = c₃: hvw : adj c₃ w = 1
                  rcases hc₃_only w hvw with rfl | rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                · -- v = d₃: hvw : adj d₃ w = 1
                  rcases hd₃_only w hvw with rfl
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · -- v = a₂: hvw : adj a₂ w = 1
                  rcases ha₂_only w hvw with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
                · -- v = b₂: hvw : adj b₂ w = 1
                  rcases hb₂_only w hvw with rfl
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
              -- Construct E8Distinct v₀ leaf a₃ b₃ c₃ d₃ a₂ b₂
              have hd_e8 : E8Distinct v₀ leaf a₃ b₃ c₃ d₃ a₂ b₂ := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                -- ne_v₀l
                · exact ne_of_adj' v₀ leaf h_leaf_adj
                -- ne_v₀a
                · exact ne_of_adj' v₀ a₃ ha₃_adj
                -- ne_v₀b: v₀ ≠ b₃ (degrees 3 vs 2)
                · intro h; linarith [hv₀, h.symm ▸ h_b3_ext']
                -- ne_v₀c: v₀ ≠ c₃ (degrees 3 vs 2)
                · intro h; linarith [hv₀, h.symm ▸ h_c3_ext]
                -- ne_v₀d: v₀ ≠ d₃ (degrees 3 vs 1)
                · intro h; linarith [hv₀, h.symm ▸ hd₃_deg1]
                -- ne_v₀p
                · exact ne_of_adj' v₀ a₂ ha₂_adj
                -- ne_v₀q: v₀ ≠ b₂ (degrees 3 vs 1)
                · intro h; linarith [hv₀, h.symm ▸ hb₂_deg1]
                -- ne_la
                · exact ha₃_ne_leaf.symm
                -- ne_lb: leaf ≠ b₃ (degrees 1 vs 2)
                · intro h; linarith [h_leaf_deg, h ▸ h_b3_ext']
                -- ne_lc: leaf ≠ c₃ (degrees 1 vs 2)
                · intro h; linarith [h_leaf_deg, h ▸ h_c3_ext]
                -- ne_ld: leaf ≠ d₃ (both degree 1; leaf's neighbor is v₀, d₃'s neighbor is c₃)
                · intro h
                  have hadj : adj leaf c₃ = 1 := by rw [h]; exact (adj_comm d₃ c₃).trans hd₃_adj
                  have hc₃v₀ : c₃ = v₀ := hleaf_only c₃ hadj
                  linarith [hv₀, hc₃v₀ ▸ h_c3_ext]
                -- ne_lp
                · exact ha₂_ne_leaf.symm
                -- ne_lq: leaf ≠ b₂ (both degree 1; leaf's neighbor is v₀, b₂'s neighbor is a₂)
                · intro h
                  have hadj : adj leaf a₂ = 1 := by rw [h]; exact (adj_comm b₂ a₂).trans hb₂_adj
                  have ha₂v₀ : a₂ = v₀ := hleaf_only a₂ hadj
                  linarith [hv₀, ha₂v₀ ▸ h_a2_ext]
                -- ne_ab
                · exact ne_of_adj' a₃ b₃ hb₃_adj
                -- ne_ac: a₃ ≠ c₃ (already have hc₃_ne_a₃)
                · exact hc₃_ne_a₃.symm
                -- ne_ad: a₃ ≠ d₃ (degrees 2 vs 1)
                · intro h; linarith [h_a3_ext, h ▸ hd₃_deg1]
                -- ne_ap
                · exact ha₂₃.symm
                -- ne_aq: a₃ ≠ b₂ (degrees 2 vs 1)
                · intro h; linarith [h_a3_ext, h ▸ hb₂_deg1]
                -- ne_bc
                · exact ne_of_adj' b₃ c₃ hc₃_adj
                -- ne_bd: b₃ ≠ d₃ (already have hd₃_ne_b₃)
                · exact hd₃_ne_b₃.symm
                -- ne_bp: b₃ ≠ a₂ (b₃ is internal on arm3, a₂ is on arm2 adjacent to v₀)
                · intro h
                  have hb₃v₀ : adj b₃ v₀ = 1 := (adj_comm b₃ v₀).trans (h.symm ▸ ha₂_adj)
                  rcases hb₃_only v₀ hb₃v₀ with heq | heq
                  · linarith [hdiag a₃, heq ▸ ha₃_adj]
                  · linarith [hv₀, heq.symm ▸ h_c3_ext]
                -- ne_bq: b₃ ≠ b₂ (degrees 2 vs 1)
                · intro h; linarith [h_b3_ext', h ▸ hb₂_deg1]
                -- ne_cd
                · exact ne_of_adj' c₃ d₃ hd₃_adj
                -- ne_cp: c₃ ≠ a₂ (c₃ is adjacent to v₀ would require being on both arms)
                · intro h
                  have hv₀c₃ : adj c₃ v₀ = 1 := by rw [adj_comm, h]; exact ha₂_adj
                  rcases hc₃_only v₀ hv₀c₃ with heq | heq
                  · exact absurd heq hb₃_ne_v₀.symm
                  · linarith [hv₀, heq.symm ▸ hd₃_deg1]
                -- ne_cq: c₃ ≠ b₂ (degrees 2 vs 1)
                · intro h; linarith [h_c3_ext, h ▸ hb₂_deg1]
                -- ne_dp: d₃ ≠ a₂ (degrees 1 vs 2)
                · intro h; linarith [hd₃_deg1, h ▸ h_a2_ext]
                -- ne_dq: d₃ ≠ b₂ (both degree 1; d₃'s neighbor is c₃, b₂'s neighbor is a₂)
                · intro h
                  have ha₂d₃ : adj d₃ a₂ = 1 := by rw [adj_comm, h]; exact hb₂_adj
                  have ha₂c₃ := hd₃_only a₂ ha₂d₃
                  rcases ha₂_only b₃ ((adj_comm a₂ b₃).trans (ha₂c₃.symm ▸ hc₃_adj)) with heq | heq
                  · linarith [h_b3_ext', heq ▸ hv₀]
                  · linarith [h_b3_ext', heq ▸ hb₂_deg1]
                -- ne_pq
                · exact ne_of_adj' a₂ b₂ hb₂_adj
              intro x hx
              exact e8_posdef adj hsymm hdiag h01 v₀ leaf a₃ b₃ c₃ d₃ a₂ b₂ hd_e8
                h_leaf_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj ha₂_adj hb₂_adj
                hv₀_only hleaf_only ha₃_only hb₃_only hc₃_only hd₃_only
                ha₂_only hb₂_only h_all_named x hx
          · -- c₃ is leaf: arm3 length = 3. T(1,2,3) = E₆ → posdef → contradiction
            exfalso; apply h_not_posdef
            -- T(1,2,3) = E₇: 7 vertices (swap arms),
            -- posdef by e7_tree_posdef
            have hc₃_ne_v₀ : c₃ ≠ v₀ := by
              intro heq
              have hb₃v₀ : adj v₀ b₃ = 1 := by
                rw [adj_comm]; rw [heq] at hc₃_adj; exact hc₃_adj
              have hv₀_nbrs := deg3_three_neighbors h_leaf_adj ha₂_adj
                ha₃_adj ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hv₀
              rcases hv₀_nbrs b₃ hb₃v₀ with h_eq | h_eq | h_eq
              · -- b₃ = leaf: degree mismatch
                rw [h_eq] at h_b3_ext'; omega
              · -- b₃ = a₂: a₂'s neighbors are v₀ and b₂,
                -- but also a₃
                rw [h_eq] at hb₃_adj
                have ha₂_nbrs := deg2_two_neighbors
                  ((adj_comm a₂ v₀).trans ha₂_adj)
                  hb₂_adj hb₂_ne_v₀.symm h_a2_ext
                rcases ha₂_nbrs a₃
                  ((adj_comm a₂ a₃).trans hb₃_adj) with h' | h'
                · exact ha₃_ne_v₀ h'
                · rw [h'] at h_a3_ext; omega
              · -- b₃ = a₃: adj a₃ a₃ = 1 contradicts diagonal
                rw [h_eq] at hb₃_adj; have := hdiag a₃; omega
            have hc₃_deg1 : vertexDegree adj c₃ = 1 := by
              have hle := h_deg_le2 c₃ hc₃_ne_v₀; omega
            exact e7_tree_posdef adj hsymm hdiag h01 hconn h_acyclic
              v₀ leaf a₃ b₃ c₃ a₂ b₂
              h_leaf_adj ha₃_adj ha₂_adj hb₃_adj hc₃_adj hb₂_adj
              hv₀ h_leaf_deg h_a3_ext h_a2_ext h_b3_ext'
              hc₃_deg1 hb₂_deg1
        · -- b₃ is also leaf: arm3 length = 2. T(1,2,2) = D₅ → posdef → contradiction
          exfalso; apply h_not_posdef
          -- T(1,2,2) positive definiteness proof
          -- Step 1: Establish b₃ has degree 1
          have hb₃_deg1 : vertexDegree adj b₃ = 1 := by
            have := h_deg_le2 b₃ hb₃_ne_v₀; omega
          -- Step 2: Unique neighbor lists for each vertex
          have hv₀_nbrs : ∀ j, adj v₀ j = 1 →
              j = leaf ∨ j = a₂ ∨ j = a₃ := by
            intro j hj
            by_cases hjl : j = leaf
            · exact Or.inl hjl
            · have : j ∈ S₀.erase leaf :=
                Finset.mem_erase.mpr
                  ⟨hjl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
              rw [hS₀_eq] at this
              rcases Finset.mem_insert.mp this with rfl | hm
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Finset.mem_singleton.mp hm))
          have hleaf_nbrs : ∀ j, adj leaf j = 1 → j = v₀ := by
            intro j hj; by_contra hne
            have : 2 ≤ vertexDegree adj leaf := by
              have h1 : v₀ ∈ Finset.univ.filter (adj leaf · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ v₀,
                  (adj_comm leaf v₀).trans h_leaf_adj⟩
              have h2 : j ∈ Finset.univ.filter (adj leaf · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
              calc 2 = ({v₀, j} : Finset _).card :=
                    (Finset.card_pair (Ne.symm hne)).symm
                _ ≤ _ := Finset.card_le_card fun x hx => by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
            omega
          have ha₂_nbrs : ∀ j, adj a₂ j = 1 → j = v₀ ∨ j = b₂ := by
            intro j hj
            by_cases hjv : j = v₀
            · exact Or.inl hjv
            · right
              have hmem : j ∈ (Finset.univ.filter
                  (adj a₂ · = 1)).erase v₀ :=
                Finset.mem_erase.mpr
                  ⟨hjv, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, hj⟩⟩
              rw [hb₂_eq] at hmem
              exact Finset.mem_singleton.mp hmem
          have hb₂_nbrs : ∀ j, adj b₂ j = 1 → j = a₂ := by
            intro j hj; by_contra hne
            have : 2 ≤ vertexDegree adj b₂ := by
              have h1 : a₂ ∈ Finset.univ.filter (adj b₂ · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ a₂,
                  (adj_comm b₂ a₂).trans hb₂_adj⟩
              have h2 : j ∈ Finset.univ.filter (adj b₂ · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
              calc 2 = ({a₂, j} : Finset _).card :=
                    (Finset.card_pair (Ne.symm hne)).symm
                _ ≤ _ := Finset.card_le_card fun x hx => by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
            omega
          have ha₃_nbrs : ∀ j, adj a₃ j = 1 → j = v₀ ∨ j = b₃ := by
            intro j hj
            by_cases hjv : j = v₀
            · exact Or.inl hjv
            · right
              have hmem : j ∈ (Finset.univ.filter
                  (adj a₃ · = 1)).erase v₀ :=
                Finset.mem_erase.mpr
                  ⟨hjv, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, hj⟩⟩
              rw [hb₃_eq] at hmem
              exact Finset.mem_singleton.mp hmem
          have hb₃_nbrs : ∀ j, adj b₃ j = 1 → j = a₃ := by
            intro j hj; by_contra hne
            have : 2 ≤ vertexDegree adj b₃ := by
              have h1 : a₃ ∈ Finset.univ.filter (adj b₃ · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ a₃,
                  (adj_comm b₃ a₃).trans hb₃_adj⟩
              have h2 : j ∈ Finset.univ.filter (adj b₃ · = 1) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
              calc 2 = ({a₃, j} : Finset _).card :=
                    (Finset.card_pair (Ne.symm hne)).symm
                _ ≤ _ := Finset.card_le_card fun x hx => by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
            omega
          -- Step 3: Named set is closed under adjacency
          have h_closed : ∀ i j,
              (i = v₀ ∨ i = leaf ∨ i = a₂ ∨ i = b₂ ∨
                i = a₃ ∨ i = b₃) →
              adj i j = 1 →
              (j = v₀ ∨ j = leaf ∨ j = a₂ ∨ j = b₂ ∨
                j = a₃ ∨ j = b₃) := by
            intro i j hi hadj
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
            · rcases hv₀_nbrs j hadj with h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
            · exact Or.inl (hleaf_nbrs j hadj)
            · rcases ha₂_nbrs j hadj with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inl (hb₂_nbrs j hadj)))
            · rcases ha₃_nbrs j hadj with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
            · exact .inr (.inr (.inr (.inr (.inl
                (hb₃_nbrs j hadj)))))
          -- Step 4: Every vertex is named
          have h_all_named : ∀ i : Fin n,
              i = v₀ ∨ i = leaf ∨ i = a₂ ∨ i = b₂ ∨
                i = a₃ ∨ i = b₃ := by
            intro i
            obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ i
            have hne : path ≠ [] := by
              intro h; rw [h] at hhead; simp at hhead
            have hpos : 0 < path.length := by
              cases path with
              | nil => exact absurd rfl hne
              | cons _ _ => simp
            have h_elts : ∀ (k : ℕ) (hk : k < path.length),
                path.get ⟨k, hk⟩ = v₀ ∨
                path.get ⟨k, hk⟩ = leaf ∨
                path.get ⟨k, hk⟩ = a₂ ∨
                path.get ⟨k, hk⟩ = b₂ ∨
                path.get ⟨k, hk⟩ = a₃ ∨
                path.get ⟨k, hk⟩ = b₃ := by
              intro k
              induction k with
              | zero =>
                intro hk; left
                cases path with
                | nil => simp at hk
                | cons a _ => exact Option.some.inj hhead
              | succ k ih =>
                intro hk
                exact h_closed _ _
                  (ih (by omega)) (hedges k (by omega))
            have hlast_val : path.getLast hne = i := by
              rw [List.getLast?_eq_some_getLast hne] at hlast
              exact Option.some.inj hlast
            have := h_elts (path.length - 1) (by omega)
            rwa [show path.get ⟨path.length - 1, by omega⟩ =
                path.getLast hne from by
              rw [List.getLast_eq_getElem]; rfl,
              hlast_val] at this
          -- Step 5: Additional distinctness facts
          have ha₂_ne_b₂ := ne_of_adj' a₂ b₂ hb₂_adj
          have ha₃_ne_b₃ := ne_of_adj' a₃ b₃ hb₃_adj
          have hb₂_ne_leaf : b₂ ≠ leaf := by
            intro heq
            have : adj leaf a₂ = 1 :=
              heq ▸ (adj_comm b₂ a₂).trans hb₂_adj
            exact ha₂_ne_v₀ (hleaf_nbrs a₂ this)
          have hb₃_ne_leaf : b₃ ≠ leaf := by
            intro heq
            have : adj leaf a₃ = 1 :=
              heq ▸ (adj_comm b₃ a₃).trans hb₃_adj
            exact ha₃_ne_v₀ (hleaf_nbrs a₃ this)
          have ha₃a₂_zero : adj a₃ a₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic
              [a₂, v₀, a₃]
              (by simp)
              (by simp only [List.nodup_cons, List.mem_cons,
                    List.not_mem_nil, not_or,
                    not_false_eq_true, List.nodup_nil,
                    and_self, and_true]
                  exact ⟨⟨ha₂_ne_v₀, ha₂₃⟩, Ne.symm ha₃_ne_v₀⟩)
              (by intro k hk
                  have hk3 : k + 1 < 3 := by
                    simpa using hk
                  have : k = 0 ∨ k = 1 := by omega
                  rcases this with rfl | rfl
                  · exact (adj_comm a₂ v₀).trans ha₂_adj
                  · exact ha₃_adj)
          have hb₂_ne_a₃ : b₂ ≠ a₃ := by
            intro heq
            have : adj a₃ a₂ = 1 :=
              heq ▸ (adj_comm b₂ a₂).trans hb₂_adj
            linarith [ha₃a₂_zero]
          have ha₂_ne_b₃ : a₂ ≠ b₃ := by
            intro heq
            have : adj a₃ a₂ = 1 := heq ▸ hb₃_adj
            linarith [ha₃a₂_zero]
          have hb₂_ne_b₃ : b₂ ≠ b₃ := by
            intro heq
            have h1 : a₂ ∈ Finset.univ.filter
                (adj b₂ · = 1) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ a₂,
                (adj_comm b₂ a₂).trans hb₂_adj⟩
            have h2 : a₃ ∈ Finset.univ.filter
                (adj b₂ · = 1) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ a₃,
                heq ▸ (adj_comm b₃ a₃).trans hb₃_adj⟩
            have : 2 ≤ vertexDegree adj b₂ :=
              calc 2 = ({a₂, a₃} : Finset _).card :=
                    (Finset.card_pair ha₂₃).symm
                _ ≤ _ := Finset.card_le_card fun x hx => by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
            omega
          -- Step 6: Finset.univ equals the 6 named vertices
          have huniv : (Finset.univ : Finset (Fin n)) =
              {v₀, leaf, a₂, b₂, a₃, b₃} := by
            ext i
            simp only [Finset.mem_univ, true_iff,
              Finset.mem_insert, Finset.mem_singleton]
            rcases h_all_named i with
                rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp
          have h_sum : ∀ f : Fin n → ℤ,
              ∑ i, f i = f v₀ + f leaf + f a₂ +
                f b₂ + f a₃ + f b₃ := by
            intro f
            change Finset.sum Finset.univ f = _
            rw [huniv]
            rw [Finset.sum_insert (show v₀ ∉
                ({leaf, a₂, b₂, a₃, b₃} : Finset _) from by
              simp only [Finset.mem_insert,
                Finset.mem_singleton, not_or]
              exact ⟨Ne.symm hleaf_ne_v₀,
                Ne.symm ha₂_ne_v₀, Ne.symm hb₂_ne_v₀,
                Ne.symm ha₃_ne_v₀, Ne.symm hb₃_ne_v₀⟩)]
            rw [Finset.sum_insert (show leaf ∉
                ({a₂, b₂, a₃, b₃} : Finset _) from by
              simp only [Finset.mem_insert,
                Finset.mem_singleton, not_or]
              exact ⟨Ne.symm ha₂_ne_leaf,
                Ne.symm hb₂_ne_leaf,
                Ne.symm ha₃_ne_leaf,
                Ne.symm hb₃_ne_leaf⟩)]
            rw [Finset.sum_insert (show a₂ ∉
                ({b₂, a₃, b₃} : Finset _) from by
              simp only [Finset.mem_insert,
                Finset.mem_singleton, not_or]
              exact ⟨ha₂_ne_b₂, ha₂₃, ha₂_ne_b₃⟩)]
            rw [Finset.sum_insert (show b₂ ∉
                ({a₃, b₃} : Finset _) from by
              simp only [Finset.mem_insert,
                Finset.mem_singleton, not_or]
              exact ⟨hb₂_ne_a₃, hb₂_ne_b₃⟩)]
            rw [Finset.sum_pair ha₃_ne_b₃]
            ring
          -- Step 7: adj row equations
          have hv₀_adj_eq : ∀ j,
              adj v₀ j =
                if j = leaf ∨ j = a₂ ∨ j = a₃
                then 1 else 0 := by
            intro j; split_ifs with h
            · rcases h with rfl | rfl | rfl
              · exact h_leaf_adj
              · exact ha₂_adj
              · exact ha₃_adj
            · push_neg at h; obtain ⟨h1, h2, h3⟩ := h
              rcases h01 v₀ j with h | h
              · exact h
              · exfalso
                rcases hv₀_nbrs j h with rfl | rfl | rfl
                · exact h1 rfl
                · exact h2 rfl
                · exact h3 rfl
          have hleaf_adj_eq : ∀ j,
              adj leaf j = if j = v₀ then 1 else 0 := by
            intro j; split_ifs with h
            · rw [h]
              exact (hsymm.apply v₀ leaf).trans h_leaf_adj
            · rcases h01 leaf j with h' | h'
              · exact h'
              · exact absurd (hleaf_nbrs j h') h
          have ha₂_adj_eq : ∀ j,
              adj a₂ j =
                if j = v₀ ∨ j = b₂ then 1 else 0 := by
            intro j; split_ifs with h
            · rcases h with hj | hj
              · rw [hj]; exact (hsymm.apply v₀ a₂).trans ha₂_adj
              · rw [hj]; exact hb₂_adj
            · push_neg at h; obtain ⟨h1, h2⟩ := h
              rcases h01 a₂ j with h' | h'
              · exact h'
              · exfalso
                rcases ha₂_nbrs j h' with rfl | rfl
                · exact h1 rfl
                · exact h2 rfl
          have hb₂_adj_eq : ∀ j,
              adj b₂ j = if j = a₂ then 1 else 0 := by
            intro j; split_ifs with h
            · rw [h]
              exact (hsymm.apply a₂ b₂).trans hb₂_adj
            · rcases h01 b₂ j with h' | h'
              · exact h'
              · exact absurd (hb₂_nbrs j h') h
          have ha₃_adj_eq : ∀ j,
              adj a₃ j =
                if j = v₀ ∨ j = b₃ then 1 else 0 := by
            intro j; split_ifs with h
            · rcases h with hj | hj
              · rw [hj]; exact (hsymm.apply v₀ a₃).trans ha₃_adj
              · rw [hj]; exact hb₃_adj
            · push_neg at h; obtain ⟨h1, h2⟩ := h
              rcases h01 a₃ j with h' | h'
              · exact h'
              · exfalso
                rcases ha₃_nbrs j h' with rfl | rfl
                · exact h1 rfl
                · exact h2 rfl
          have hb₃_adj_eq : ∀ j,
              adj b₃ j = if j = a₃ then 1 else 0 := by
            intro j; split_ifs with h
            · rw [h]
              exact (hsymm.apply a₃ b₃).trans hb₃_adj
            · rcases h01 b₃ j with h' | h'
              · exact h'
              · exact absurd (hb₃_nbrs j h') h
          -- Step 8: Expand QF as polynomial
          intro x hx
          set V := x v₀; set L := x leaf; set A₂ := x a₂
          set B₂ := x b₂; set A₃ := x a₃; set B₃ := x b₃
          have h_qf : QF adj x =
              2 * V ^ 2 + 2 * L ^ 2 + 2 * A₂ ^ 2 +
              2 * B₂ ^ 2 + 2 * A₃ ^ 2 + 2 * B₃ ^ 2 -
              2 * V * L - 2 * V * A₂ - 2 * A₂ * B₂ -
              2 * V * A₃ - 2 * A₃ * B₃ := by
            unfold QF
            simp only [dotProduct, Matrix.mulVec, h_sum,
              Matrix.sub_apply, Matrix.smul_apply,
              Matrix.one_apply, hdiag,
              hv₀_adj_eq, hleaf_adj_eq, ha₂_adj_eq,
              hb₂_adj_eq, ha₃_adj_eq, hb₃_adj_eq,
              eq_self_iff_true, ite_true, ite_false,
              hleaf_ne_v₀, Ne.symm hleaf_ne_v₀,
              ha₂_ne_v₀, Ne.symm ha₂_ne_v₀,
              ha₃_ne_v₀, Ne.symm ha₃_ne_v₀,
              hb₂_ne_v₀, Ne.symm hb₂_ne_v₀,
              hb₃_ne_v₀, Ne.symm hb₃_ne_v₀,
              ha₂_ne_leaf, Ne.symm ha₂_ne_leaf,
              ha₃_ne_leaf, Ne.symm ha₃_ne_leaf,
              hb₂_ne_leaf, Ne.symm hb₂_ne_leaf,
              hb₃_ne_leaf, Ne.symm hb₃_ne_leaf,
              ha₂₃, Ne.symm ha₂₃,
              ha₂_ne_b₂, Ne.symm ha₂_ne_b₂,
              ha₂_ne_b₃, Ne.symm ha₂_ne_b₃,
              hb₂_ne_a₃, Ne.symm hb₂_ne_a₃,
              hb₂_ne_b₃, Ne.symm hb₂_ne_b₃,
              ha₃_ne_b₃, Ne.symm ha₃_ne_b₃,
              ite_mul, one_mul, zero_mul,
              true_or, or_true, false_or, or_false,
              mul_one, mul_zero, sub_zero, zero_sub]
            ring
          -- Step 9: SoS positivity from LDL^T decomposition
          rw [show dotProduct x
              ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec
                x) = QF adj x from rfl, h_qf]
          suffices h60 :
              0 < 30 * (2 * V - L - A₂ - A₃) ^ 2 +
              10 * (3 * L - A₂ - A₃) ^ 2 +
              5 * (4 * A₂ - 3 * B₂ - 2 * A₃) ^ 2 +
              3 * (5 * B₂ - 2 * A₃) ^ 2 +
              3 * (4 * A₃ - 5 * B₃) ^ 2 +
              45 * B₃ ^ 2 by nlinarith
          by_contra h_le; push_neg at h_le
          have h_all_zero :
              2 * V - L - A₂ - A₃ = 0 ∧
              3 * L - A₂ - A₃ = 0 ∧
              4 * A₂ - 3 * B₂ - 2 * A₃ = 0 ∧
              5 * B₂ - 2 * A₃ = 0 ∧
              4 * A₃ - 5 * B₃ = 0 ∧ B₃ = 0 := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            nlinarith [sq_nonneg (2 * V - L - A₂ - A₃),
              sq_nonneg (3 * L - A₂ - A₃),
              sq_nonneg (4 * A₂ - 3 * B₂ - 2 * A₃),
              sq_nonneg (5 * B₂ - 2 * A₃),
              sq_nonneg (4 * A₃ - 5 * B₃),
              sq_nonneg B₃]
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_all_zero
          have hB₃ : B₃ = 0 := h6
          have hA₃ : A₃ = 0 := by nlinarith
          have hB₂ : B₂ = 0 := by nlinarith
          have hA₂ : A₂ = 0 := by nlinarith
          have hL : L = 0 := by nlinarith
          have hV : V = 0 := by nlinarith
          apply hx; ext i
          rcases h_all_named i with
              rfl | rfl | rfl | rfl | rfl | rfl <;>
            [exact hV; exact hL; exact hA₂;
             exact hB₂; exact hA₃; exact hB₃]
    · -- a₃ has degree 1 (leaf): T(1,≥2,1) = D-type → positive definite → contradiction
      -- a₂ has degree 2, a₃ has degree 1.
      -- v₀ has three neighbors: leaf (deg 1), a₂ (deg 2), a₃ (deg 1).
      -- The Cartan form of a D-type tree is positive definite.
      -- QF(x) = QF_path(x|path) + (x(v₀) - x(leaf) - x(a₃))² + (x(leaf) - x(a₃))²
      -- where QF_path is the QF of the path leaf-v₀-a₂-...(end) (all degrees ≤ 2 in path).
      -- QF_path ≥ 0, and all three summands = 0 implies x(leaf) = x(a₃) = x(v₀) = 0,
      -- then QF_path = 0 implies all path vertices = 0, hence x = 0.
      have ha₃_deg1 : vertexDegree adj a₃ = 1 := by
        have hle := h_deg_le2 a₃ ha₃_ne_v₀
        have hge : 1 ≤ vertexDegree adj a₃ :=
          Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩⟩
        omega
      exfalso
      apply h_not_posdef
      -- Prove: D-type tree (leaf-v₀-a₂-..., a₃ hanging off v₀) has positive definite Cartan form
      intro x hx
      exact tree_two_leaf_posdef adj hsymm hdiag h01 hconn h_acyclic h_deg v₀ leaf a₃
        h_leaf_adj h_leaf_deg ha₃_adj ha₃_deg1
        ha₃_ne_leaf.symm hleaf_ne_v₀ ha₃_ne_v₀ h_deg_le2 x hx
  · -- a₂ has degree 1 (leaf): T(1,≥1,1) — symmetric to the a₃ leaf case.
    -- v₀ has three neighbors: leaf (deg 1), a₂ (deg 1), a₃ (deg ≤ 2).
    -- The tree is D-type (or has leaf+a₂ both as leaves) → positive definite → contradiction.
    have ha₂_deg1 : vertexDegree adj a₂ = 1 := by
      have hle := h_deg_le2 a₂ ha₂_ne_v₀
      have hge : 1 ≤ vertexDegree adj a₂ :=
        Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩⟩
      omega
    -- The tree has two leaf neighbors of v₀: leaf and a₂.
    -- QF(x) ≥ (x v₀ - x leaf - x a₂)² + (x leaf - x a₂)² + QF_path(x|arm_a₃)
    -- where QF_path ≥ 0, and equality forces x = 0.
    exfalso
    apply h_not_posdef
    exact tree_two_leaf_posdef adj hsymm hdiag h01 hconn h_acyclic h_deg v₀ leaf a₂
      h_leaf_adj h_leaf_deg ha₂_adj ha₂_deg1
      ha₂_ne_leaf.symm hleaf_ne_v₀ ha₂_ne_v₀ h_deg_le2

set_option maxHeartbeats 3200000 in
/-- A connected acyclic simple graph with exactly one degree-3 vertex and non-positive-
    definite Cartan form has infinite representation type.

    The tree is T(p,q,r). Since it's not positive definite, it's not ADE
    (D_n, E_6, E_7, E_8), so (p,q,r) is in one of the forbidden ranges:
    - p ≥ 2: contains Ẽ₆ = T(2,2,2)
    - p = 1, q ≥ 3: contains Ẽ₇ = T(1,3,3)
    - p = 1, q = 2, r ≥ 5: contains T(1,2,5) -/
private theorem single_branch_not_posdef_infinite_type {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)) :
    ¬ IsFiniteTypeQuiver n adj := by
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Non-v₀ vertices have degree ≤ 2
  have h_deg_le2 : ∀ v, v ≠ v₀ → vertexDegree adj v ≤ 2 := by
    intro v hv
    have h3 := h_deg v
    by_contra h
    push_neg at h
    have : vertexDegree adj v = 3 := by omega
    exact hv (h_unique v this)
  -- Extract 3 neighbors of v₀
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have hS₀_card : S₀.card = 3 := hv₀
  -- Extract first neighbor
  have hS₀_nonempty : S₀.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hS₀_card
  obtain ⟨a₁, ha₁_mem⟩ := hS₀_nonempty
  have ha₁_adj : adj v₀ a₁ = 1 := (Finset.mem_filter.mp ha₁_mem).2
  have hS₀_erase1 : (S₀.erase a₁).card = 2 := by
    rw [Finset.card_erase_of_mem ha₁_mem, hS₀_card]
  obtain ⟨a₂, a₃, ha₂₃, hS₀_eq2⟩ := Finset.card_eq_two.mp hS₀_erase1
  have ha₂_mem : a₂ ∈ S₀.erase a₁ := hS₀_eq2 ▸ Finset.mem_insert_self a₂ _
  have ha₃_mem : a₃ ∈ S₀.erase a₁ := hS₀_eq2 ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self a₃))
  have ha₂_adj : adj v₀ a₂ = 1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₂_mem)).2
  have ha₃_adj : adj v₀ a₃ = 1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase ha₃_mem)).2
  have ha₁₂ : a₁ ≠ a₂ := (Finset.ne_of_mem_erase ha₂_mem).symm
  have ha₁₃ : a₁ ≠ a₃ := (Finset.ne_of_mem_erase ha₃_mem).symm
  -- Basic distinctness: neighbors ≠ v₀
  have ha₁_ne_v₀ : a₁ ≠ v₀ := (ne_of_adj v₀ a₁ ha₁_adj).symm
  have ha₂_ne_v₀ : a₂ ≠ v₀ := (ne_of_adj v₀ a₂ ha₂_adj).symm
  have ha₃_ne_v₀ : a₃ ≠ v₀ := (ne_of_adj v₀ a₃ ha₃_adj).symm
  -- Check: do all 3 neighbors have degree ≥ 2?
  -- If any neighbor is a leaf (degree 1), delegate to single_branch_leaf_case
  by_cases h_a1_ext : 2 ≤ vertexDegree adj a₁
  · by_cases h_a2_ext : 2 ≤ vertexDegree adj a₂
    · by_cases h_a3_ext : 2 ≤ vertexDegree adj a₃
      · -- Case: all 3 arms have length ≥ 2 → embed Ẽ₆ = T(2,2,2)
        -- Extract b₁: the other neighbor of a₁ (besides v₀)
        have ha₁_deg : vertexDegree adj a₁ = 2 := by
          have := h_deg_le2 a₁ ha₁_ne_v₀; omega
        set Sa₁ := Finset.univ.filter (fun j => adj a₁ j = 1) with hSa₁_def
        have hSa₁_card : Sa₁.card = 2 := ha₁_deg
        have hv₀_in_Sa₁ : v₀ ∈ Sa₁ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₁ v₀).trans ha₁_adj⟩
        have hSa₁_erase : (Sa₁.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₁, hSa₁_card]
        obtain ⟨b₁, hb₁_eq⟩ := Finset.card_eq_one.mp hSa₁_erase
        have hb₁_mem : b₁ ∈ Sa₁.erase v₀ := hb₁_eq ▸ Finset.mem_singleton_self b₁
        have hb₁_adj : adj a₁ b₁ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₁_mem)).2
        have hb₁_ne_v₀ : b₁ ≠ v₀ := Finset.ne_of_mem_erase hb₁_mem
        -- Extract b₂: the other neighbor of a₂ (besides v₀)
        have ha₂_deg : vertexDegree adj a₂ = 2 := by
          have := h_deg_le2 a₂ ha₂_ne_v₀; omega
        set Sa₂ := Finset.univ.filter (fun j => adj a₂ j = 1) with hSa₂_def
        have hSa₂_card : Sa₂.card = 2 := ha₂_deg
        have hv₀_in_Sa₂ : v₀ ∈ Sa₂ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩
        have hSa₂_erase : (Sa₂.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₂, hSa₂_card]
        obtain ⟨b₂, hb₂_eq⟩ := Finset.card_eq_one.mp hSa₂_erase
        have hb₂_mem : b₂ ∈ Sa₂.erase v₀ := hb₂_eq ▸ Finset.mem_singleton_self b₂
        have hb₂_adj : adj a₂ b₂ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₂_mem)).2
        have hb₂_ne_v₀ : b₂ ≠ v₀ := Finset.ne_of_mem_erase hb₂_mem
        -- Extract b₃: the other neighbor of a₃ (besides v₀)
        have ha₃_deg : vertexDegree adj a₃ = 2 := by
          have := h_deg_le2 a₃ ha₃_ne_v₀; omega
        set Sa₃ := Finset.univ.filter (fun j => adj a₃ j = 1) with hSa₃_def
        have hSa₃_card : Sa₃.card = 2 := ha₃_deg
        have hv₀_in_Sa₃ : v₀ ∈ Sa₃ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩
        have hSa₃_erase : (Sa₃.erase v₀).card = 1 := by
          rw [Finset.card_erase_of_mem hv₀_in_Sa₃, hSa₃_card]
        obtain ⟨b₃, hb₃_eq⟩ := Finset.card_eq_one.mp hSa₃_erase
        have hb₃_mem : b₃ ∈ Sa₃.erase v₀ := hb₃_eq ▸ Finset.mem_singleton_self b₃
        have hb₃_adj : adj a₃ b₃ = 1 :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb₃_mem)).2
        have hb₃_ne_v₀ : b₃ ≠ v₀ := Finset.ne_of_mem_erase hb₃_mem
        -- Non-edges via acyclic_no_triangle (center v₀)
        have ha₁a₂ : adj a₁ a₂ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₁ a₂
            ha₁₂ ha₁_ne_v₀ ha₂_ne_v₀ ha₁_adj ha₂_adj
        have ha₁a₃ : adj a₁ a₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₁ a₃
            ha₁₃ ha₁_ne_v₀ ha₃_ne_v₀ ha₁_adj ha₃_adj
        have ha₂a₃ : adj a₂ a₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic v₀ a₂ a₃
            ha₂₃ ha₂_ne_v₀ ha₃_ne_v₀ ha₂_adj ha₃_adj
        -- Non-edges via acyclic_no_triangle (center aᵢ)
        have hv₀b₁ : adj v₀ b₁ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₁ v₀ b₁
            hb₁_ne_v₀.symm ha₁_ne_v₀.symm (ne_of_adj a₁ b₁ hb₁_adj).symm
            ((adj_comm a₁ v₀).trans ha₁_adj) hb₁_adj
        have hv₀b₂ : adj v₀ b₂ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₂ v₀ b₂
            hb₂_ne_v₀.symm ha₂_ne_v₀.symm (ne_of_adj a₂ b₂ hb₂_adj).symm
            ((adj_comm a₂ v₀).trans ha₂_adj) hb₂_adj
        have hv₀b₃ : adj v₀ b₃ = 0 :=
          acyclic_no_triangle adj hsymm h01 h_acyclic a₃ v₀ b₃
            hb₃_ne_v₀.symm ha₃_ne_v₀.symm (ne_of_adj a₃ b₃ hb₃_adj).symm
            ((adj_comm a₃ v₀).trans ha₃_adj) hb₃_adj
        -- Distinctness: aᵢ ≠ bⱼ (for i ≠ j)
        -- If aᵢ = bⱼ, then adj v₀ bⱼ = adj v₀ aᵢ = 1, contradicting hv₀bⱼ = 0
        have ha₁_ne_b₂ : a₁ ≠ b₂ := by intro h; rw [h] at ha₁_adj; linarith
        have ha₁_ne_b₃ : a₁ ≠ b₃ := by intro h; rw [h] at ha₁_adj; linarith
        have ha₂_ne_b₁ : a₂ ≠ b₁ := by intro h; rw [h] at ha₂_adj; linarith
        have ha₂_ne_b₃ : a₂ ≠ b₃ := by intro h; rw [h] at ha₂_adj; linarith
        have ha₃_ne_b₁ : a₃ ≠ b₁ := by intro h; rw [h] at ha₃_adj; linarith
        have ha₃_ne_b₂ : a₃ ≠ b₂ := by intro h; rw [h] at ha₃_adj; linarith
        -- Distinctness: bᵢ ≠ bⱼ (via 4-cycle acyclicity argument)
        have ha₁_ne_b₁ : a₁ ≠ b₁ := ne_of_adj a₁ b₁ hb₁_adj
        have ha₂_ne_b₂ : a₂ ≠ b₂ := ne_of_adj a₂ b₂ hb₂_adj
        have ha₃_ne_b₃ : a₃ ≠ b₃ := ne_of_adj a₃ b₃ hb₃_adj
        -- Helper: 4-element Nodup and edges
        have nodup4 : ∀ (a b c d : Fin n),
            a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
          intro a b c d hab hac had hbc hbd hcd
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
          exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
        have edges4 : ∀ (a b c d : Fin n),
            adj a b = 1 → adj b c = 1 → adj c d = 1 →
            ∀ k, (hk : k + 1 < [a, b, c, d].length) →
              adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
          intro a b c d h₁ h₂ h₃ k hk
          have : k + 1 < 4 := by simpa using hk
          have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
          rcases this with rfl | rfl | rfl <;> assumption
        -- If b₁ = b₂, then [b₁, a₁, v₀, a₂] is a 4-cycle
        have hb₁_ne_b₂ : b₁ ≠ b₂ := by
          intro h; rw [← h] at hb₂_adj
          exact h_acyclic [b₁, a₁, v₀, a₂] (by simp)
            (nodup4 b₁ a₁ v₀ a₂ ha₁_ne_b₁.symm hb₁_ne_v₀ ha₂_ne_b₁.symm
              ha₁_ne_v₀ ha₁₂ ha₂_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₂ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₂_adj) hb₂_adj
        have hb₁_ne_b₃ : b₁ ≠ b₃ := by
          intro h; rw [← h] at hb₃_adj
          exact h_acyclic [b₁, a₁, v₀, a₃] (by simp)
            (nodup4 b₁ a₁ v₀ a₃ ha₁_ne_b₁.symm hb₁_ne_v₀ ha₃_ne_b₁.symm
              ha₁_ne_v₀ ha₁₃ ha₃_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₃ ((adj_comm b₁ a₁).trans hb₁_adj)
              ((adj_comm a₁ v₀).trans ha₁_adj) ha₃_adj) hb₃_adj
        have hb₂_ne_b₃ : b₂ ≠ b₃ := by
          intro h; rw [← h] at hb₃_adj
          exact h_acyclic [b₂, a₂, v₀, a₃] (by simp)
            (nodup4 b₂ a₂ v₀ a₃ ha₂_ne_b₂.symm hb₂_ne_v₀ ha₃_ne_b₂.symm
              ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₃ ((adj_comm b₂ a₂).trans hb₂_adj)
              ((adj_comm a₂ v₀).trans ha₂_adj) ha₃_adj) hb₃_adj
        -- Non-edges via acyclic_path_nonadj (path length 3)
        -- aᵢ-bⱼ for i ≠ j: path [bⱼ, aⱼ, v₀, aᵢ]
        have ha₁b₂ : adj a₁ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₁] (by simp)
            (nodup4 b₂ a₂ v₀ a₁ (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀ ha₁_ne_b₂.symm ha₂_ne_v₀ ha₁₂.symm ha₁_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₁ ((adj_comm b₂ a₂).trans hb₂_adj) ((adj_comm a₂ v₀).trans ha₂_adj) ha₁_adj)
        have ha₁b₃ : adj a₁ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₁] (by simp)
            (nodup4 b₃ a₃ v₀ a₁ (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₁_ne_b₃.symm ha₃_ne_v₀ ha₁₃.symm ha₁_ne_v₀.symm)
            (edges4 b₃ a₃ v₀ a₁ ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj) ha₁_adj)
        have ha₂b₁ : adj a₂ b₁ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₁, a₁, v₀, a₂] (by simp)
            (nodup4 b₁ a₁ v₀ a₂ (ne_of_adj a₁ b₁ hb₁_adj).symm hb₁_ne_v₀ ha₂_ne_b₁.symm ha₁_ne_v₀ ha₁₂ ha₂_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₂ ((adj_comm b₁ a₁).trans hb₁_adj) ((adj_comm a₁ v₀).trans ha₁_adj) ha₂_adj)
        have ha₂b₃ : adj a₂ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₂] (by simp)
            (nodup4 b₃ a₃ v₀ a₂ (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₂_ne_b₃.symm ha₃_ne_v₀ ha₂₃.symm ha₂_ne_v₀.symm)
            (edges4 b₃ a₃ v₀ a₂ ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj) ha₂_adj)
        have ha₃b₁ : adj a₃ b₁ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₁, a₁, v₀, a₃] (by simp)
            (nodup4 b₁ a₁ v₀ a₃ (ne_of_adj a₁ b₁ hb₁_adj).symm hb₁_ne_v₀ ha₃_ne_b₁.symm ha₁_ne_v₀ ha₁₃ ha₃_ne_v₀.symm)
            (edges4 b₁ a₁ v₀ a₃ ((adj_comm b₁ a₁).trans hb₁_adj) ((adj_comm a₁ v₀).trans ha₁_adj) ha₃_adj)
        have ha₃b₂ : adj a₃ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₃] (by simp)
            (nodup4 b₂ a₂ v₀ a₃ (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀ ha₃_ne_b₂.symm ha₂_ne_v₀ ha₂₃ ha₃_ne_v₀.symm)
            (edges4 b₂ a₂ v₀ a₃ ((adj_comm b₂ a₂).trans hb₂_adj) ((adj_comm a₂ v₀).trans ha₂_adj) ha₃_adj)
        -- Non-edges via acyclic_path_nonadj (path length 4)
        -- bᵢ-bⱼ for i ≠ j: path [bⱼ, aⱼ, v₀, aᵢ, bᵢ]
        have path_nodup5 : ∀ (a b c d e : Fin n),
            a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
            [a, b, c, d, e].Nodup := by
          intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
          exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
        have path_edges5 : ∀ (a b c d e : Fin n),
            adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
            ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
              adj ([a, b, c, d, e].get ⟨k, by omega⟩)
                  ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
          intro a b c d e h₁ h₂ h₃ h₄ k hk
          have : k + 1 < 5 := by simpa using hk
          have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases this with rfl | rfl | rfl | rfl <;> assumption
        have hb₁b₂ : adj b₁ b₂ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₂, a₂, v₀, a₁, b₁] (by simp)
            (path_nodup5 b₂ a₂ v₀ a₁ b₁
              (ne_of_adj a₂ b₂ hb₂_adj).symm hb₂_ne_v₀ ha₁_ne_b₂.symm hb₁_ne_b₂.symm
              ha₂_ne_v₀ ha₁₂.symm ha₂_ne_b₁ ha₁_ne_v₀.symm hb₁_ne_v₀.symm ha₁_ne_b₁)
            (path_edges5 b₂ a₂ v₀ a₁ b₁
              ((adj_comm b₂ a₂).trans hb₂_adj) ((adj_comm a₂ v₀).trans ha₂_adj)
              ha₁_adj hb₁_adj)
        have hb₁b₃ : adj b₁ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₁, b₁] (by simp)
            (path_nodup5 b₃ a₃ v₀ a₁ b₁
              (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₁_ne_b₃.symm hb₁_ne_b₃.symm
              ha₃_ne_v₀ ha₁₃.symm ha₃_ne_b₁ ha₁_ne_v₀.symm hb₁_ne_v₀.symm ha₁_ne_b₁)
            (path_edges5 b₃ a₃ v₀ a₁ b₁
              ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj)
              ha₁_adj hb₁_adj)
        have hb₂b₃ : adj b₂ b₃ = 0 :=
          acyclic_path_nonadj adj hsymm h01 h_acyclic [b₃, a₃, v₀, a₂, b₂] (by simp)
            (path_nodup5 b₃ a₃ v₀ a₂ b₂
              (ne_of_adj a₃ b₃ hb₃_adj).symm hb₃_ne_v₀ ha₂_ne_b₃.symm hb₂_ne_b₃.symm
              ha₃_ne_v₀ ha₂₃.symm ha₃_ne_b₂ ha₂_ne_v₀.symm hb₂_ne_v₀.symm ha₂_ne_b₂)
            (path_edges5 b₃ a₃ v₀ a₂ b₂
              ((adj_comm b₃ a₃).trans hb₃_adj) ((adj_comm a₃ v₀).trans ha₃_adj)
              ha₂_adj hb₂_adj)
        -- Non-edge: a₁-b₁ already an edge (not needed as non-edge)
        -- Now construct the embedding φ : Fin 7 ↪ Fin n for Ẽ₆ = T(2,2,2)
        -- Map: 0 → v₀, 1 → a₁, 2 → b₁, 3 → a₂, 4 → b₂, 5 → a₃, 6 → b₃
        let φ_fun : Fin 7 → Fin n := fun i =>
          match i with
          | ⟨0, _⟩ => v₀ | ⟨1, _⟩ => a₁ | ⟨2, _⟩ => b₁
          | ⟨3, _⟩ => a₂ | ⟨4, _⟩ => b₂ | ⟨5, _⟩ => a₃ | ⟨6, _⟩ => b₃
        have φ_inj : Function.Injective φ_fun := by
          intro i j hij; simp only [φ_fun] at hij
          fin_cases i <;> fin_cases j <;>
            first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
        let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
        -- Adjacency verification: etilde6Adj i j = adj (φ i) (φ j)
        have hembed : ∀ i j, etilde6Adj i j = adj (φ i) (φ j) := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp only [etilde6Adj, φ, φ_fun] <;> norm_num <;>
            linarith [hdiag v₀, hdiag a₁, hdiag a₂, hdiag a₃, hdiag b₁, hdiag b₂, hdiag b₃,
                      ha₁_adj, ha₂_adj, ha₃_adj, hb₁_adj, hb₂_adj, hb₃_adj,
                      adj_comm v₀ a₁, adj_comm v₀ a₂, adj_comm v₀ a₃,
                      adj_comm v₀ b₁, adj_comm v₀ b₂, adj_comm v₀ b₃,
                      adj_comm a₁ a₂, adj_comm a₁ a₃, adj_comm a₂ a₃,
                      adj_comm a₁ b₁, adj_comm a₁ b₂, adj_comm a₁ b₃,
                      adj_comm a₂ b₁, adj_comm a₂ b₂, adj_comm a₂ b₃,
                      adj_comm a₃ b₁, adj_comm a₃ b₂, adj_comm a₃ b₃,
                      adj_comm b₁ b₂, adj_comm b₁ b₃, adj_comm b₂ b₃,
                      ha₁a₂, ha₁a₃, ha₂a₃,
                      hv₀b₁, hv₀b₂, hv₀b₃,
                      ha₁b₂, ha₁b₃, ha₂b₁, ha₂b₃, ha₃b₁, ha₃b₂,
                      hb₁b₂, hb₁b₃, hb₂b₃]
        exact subgraph_infinite_type_transfer φ adj etilde6Adj hsymm
          (fun v h => by linarith [hdiag v]) hembed etilde6_not_finite_type
      · -- a₃ is leaf → delegate to leaf case
        have ha₃_deg1 : vertexDegree adj a₃ = 1 := by
          have := h_deg_le2 a₃ ha₃_ne_v₀
          have : 1 ≤ vertexDegree adj a₃ :=
            Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (adj_comm a₃ v₀).trans ha₃_adj⟩⟩
          omega
        exact single_branch_leaf_case adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
          h_unique h_not_posdef a₃ ha₃_adj ha₃_deg1
    · -- a₂ is leaf → delegate to leaf case
      have ha₂_deg1 : vertexDegree adj a₂ = 1 := by
        have := h_deg_le2 a₂ ha₂_ne_v₀
        have : 1 ≤ vertexDegree adj a₂ :=
          Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (adj_comm a₂ v₀).trans ha₂_adj⟩⟩
        omega
      exact single_branch_leaf_case adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
        h_unique h_not_posdef a₂ ha₂_adj ha₂_deg1
  · -- a₁ is leaf → delegate to leaf case
    have ha₁_deg1 : vertexDegree adj a₁ = 1 := by
      have := h_deg_le2 a₁ ha₁_ne_v₀
      have : 1 ≤ vertexDegree adj a₁ :=
        Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (adj_comm a₁ v₀).trans ha₁_adj⟩⟩
      omega
    exact single_branch_leaf_case adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ hv₀
      h_unique h_not_posdef a₁ ha₁_adj ha₁_deg1

/-- If an injective map φ from a connected acyclic subgraph to an acyclic host graph
    preserves edges, then it preserves ALL adjacencies (edges AND non-edges).

    Proof idea: For non-adjacent i ≠ j in the subgraph, connectivity gives a Nodup path
    from i to j of length ≥ 3. Map via φ to get a Nodup path in the host. If φ(i) and
    φ(j) were adjacent, this path + that edge would form a cycle, contradicting acyclicity. -/
private theorem tree_embed_adj_eq {m n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (adj_sub : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : adj.IsSymm) (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hdiag : ∀ i, adj i i = 0)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_sub_01 : ∀ i j, adj_sub i j = 0 ∨ adj_sub i j = 1)
    (φ : Fin m ↪ Fin n)
    (hedges : ∀ i j, adj_sub i j = 1 → adj (φ i) (φ j) = 1)
    -- For each pair of non-adjacent distinct vertices in the subgraph, there exists
    -- a Nodup path of length ≥ 3 connecting them:
    (h_sub_conn : ∀ i j : Fin m, i ≠ j → adj_sub i j = 0 →
      ∃ path : List (Fin m),
        path.head? = some i ∧ path.getLast? = some j ∧
        path.Nodup ∧ 3 ≤ path.length ∧
        ∀ t, (ht : t + 1 < path.length) →
          adj_sub (path.get ⟨t, by omega⟩) (path.get ⟨t + 1, ht⟩) = 1) :
    ∀ i j, adj_sub i j = adj (φ i) (φ j) := by
  intro i j
  rcases h_sub_01 i j with h | h
  · -- adj_sub i j = 0: need adj (φ i) (φ j) = 0
    rw [h]; symm
    by_cases hij : i = j
    · subst hij; exact hdiag _
    · obtain ⟨path, hhead, hlast, hnodup, hlen, hpath⟩ := h_sub_conn i j hij h
      -- Map path via φ → Nodup host path from φ i to φ j
      set host_path := path.map φ with host_path_def
      have host_len : host_path.length = path.length := List.length_map ..
      have host_nodup : host_path.Nodup := hnodup.map φ.injective
      have host_edges : ∀ t, (ht : t + 1 < host_path.length) →
          adj (host_path.get ⟨t, by omega⟩) (host_path.get ⟨t + 1, ht⟩) = 1 := by
        intro t ht
        have ht' : t + 1 < path.length := by rw [← host_len]; exact ht
        have hget : ∀ (k : ℕ) (hk : k < host_path.length),
            host_path.get ⟨k, hk⟩ = φ (path.get ⟨k, by rw [← host_len]; exact hk⟩) :=
          fun k hk => List.getElem_map ..
        rw [hget, hget]
        exact hedges _ _ (hpath t ht')
      -- Apply acyclic_path_nonadj: adj (last) (first) = 0
      have key := acyclic_path_nonadj adj hsymm h01 h_acyclic host_path
        (by omega) host_nodup host_edges
      -- key : adj (host_path.getLast _) (host_path.get ⟨0, _⟩) = 0
      -- Rewrite host_path getLast and get 0 in terms of φ and path
      have hget0 : host_path.get ⟨0, by omega⟩ = φ (path.get ⟨0, by omega⟩) :=
        List.getElem_map ..
      have hgetL : host_path.getLast (List.ne_nil_of_length_pos (by omega)) =
          φ (path.getLast (List.ne_nil_of_length_pos (by omega))) := by
        simp [host_path_def, List.getLast_map]
      -- Convert path endpoints to i and j
      have hpath_ne : path ≠ [] := List.ne_nil_of_length_pos (by omega)
      have h_first_i : path.get ⟨0, by omega⟩ = i := by
        cases path with
        | nil => exact absurd rfl hpath_ne
        | cons a t => simpa using hhead
      have h_last_j : path.getLast hpath_ne = j := by
        have h := hlast
        rw [List.getLast?_eq_some_getLast hpath_ne] at h
        exact Option.some_injective _ h
      rw [hgetL, hget0, h_last_j, h_first_i] at key
      -- key : adj (φ j) (φ i) = 0. By symmetry: adj (φ i) (φ j) = 0.
      rwa [hsymm.apply (φ i) (φ j)] at key
  · -- adj_sub i j = 1: follows from edge preservation
    rw [h]; exact (hedges i j h).symm

/-- Ascending spine path [⟨a,_⟩, ⟨a+1,_⟩, ..., ⟨b,_⟩] in D̃. -/
private def dTildeSpinePath (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    List (Fin (k + 6)) :=
  List.ofFn (fun i : Fin (b - a + 1) => ⟨a + i.val, by omega⟩)

private lemma dTildeSpinePath_length (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    (dTildeSpinePath k a b ha hb hab).length = b - a + 1 := by
  simp [dTildeSpinePath, List.length_ofFn]

private lemma dTildeSpinePath_ne_nil (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    dTildeSpinePath k a b ha hb hab ≠ [] := by
  intro h; have := congr_arg List.length h
  simp [dTildeSpinePath_length] at this

private lemma dTildeSpinePath_getElem (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b)
    (idx : ℕ) (hidx : idx < (dTildeSpinePath k a b ha hb hab).length) :
    (dTildeSpinePath k a b ha hb hab)[idx] = ⟨a + idx, by
      rw [dTildeSpinePath_length] at hidx; omega⟩ := by
  unfold dTildeSpinePath; rw [List.getElem_ofFn]

private lemma dTildeSpinePath_head (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    (dTildeSpinePath k a b ha hb hab).head? = some ⟨a, by omega⟩ := by
  rw [List.head?_eq_head (dTildeSpinePath_ne_nil k a b ha hb hab)]
  congr 1; rw [← List.getElem_zero (by rw [dTildeSpinePath_length]; omega)]
  simp [dTildeSpinePath_getElem]

private lemma dTildeSpinePath_last (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    (dTildeSpinePath k a b ha hb hab).getLast? = some ⟨b, by omega⟩ := by
  rw [List.getLast?_eq_some_getLast (dTildeSpinePath_ne_nil k a b ha hb hab)]
  congr 1
  have hlen := dTildeSpinePath_length k a b ha hb hab
  rw [List.getLast_eq_getElem]
  rw [dTildeSpinePath_getElem]
  congr 1; omega

private lemma dTildeSpinePath_nodup (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    (dTildeSpinePath k a b ha hb hab).Nodup := by
  simp only [dTildeSpinePath, List.nodup_ofFn]
  intro x y hxy
  ext; simpa using hxy

private lemma dTildeSpinePath_edges (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b) :
    ∀ t, (ht : t + 1 < (dTildeSpinePath k a b ha hb hab).length) →
      dTildeAdj k ((dTildeSpinePath k a b ha hb hab).get ⟨t, by omega⟩)
        ((dTildeSpinePath k a b ha hb hab).get ⟨t + 1, ht⟩) = 1 := by
  intro t ht
  have hlen := dTildeSpinePath_length k a b ha hb hab
  show dTildeAdj k (dTildeSpinePath k a b ha hb hab)[t]
    (dTildeSpinePath k a b ha hb hab)[t + 1] = 1
  rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
  simp only [dTildeAdj]; rw [if_pos]
  left; right; right; left
  simp only [Fin.val_mk]
  refine ⟨by omega, by omega, by omega⟩

private lemma dTildeSpinePath_mem_val (k a b : ℕ) (ha : 2 ≤ a) (hb : b ≤ k + 3) (hab : a ≤ b)
    (v : Fin (k + 6)) (hv : v ∈ dTildeSpinePath k a b ha hb hab) :
    a ≤ v.val ∧ v.val ≤ b := by
  simp only [dTildeSpinePath, List.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  simp only [Fin.val_mk]
  exact ⟨by omega, by omega⟩

/-- A non-Nodup list has two distinct indices with equal elements. -/
private lemma exists_dup_indices {α : Type*} [DecidableEq α] :
    ∀ (l : List α), ¬ l.Nodup →
    ∃ (p q : ℕ) (hp : p < l.length) (hq : q < l.length),
      p < q ∧ l.get ⟨p, hp⟩ = l.get ⟨q, hq⟩ := by
  intro l
  induction l with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons a t ih =>
    intro hnd
    rw [List.nodup_cons] at hnd; push_neg at hnd
    by_cases ha : a ∈ t
    · rw [List.mem_iff_get] at ha
      obtain ⟨⟨q, hq⟩, hq_eq⟩ := ha
      exact ⟨0, q + 1, by simp, by simp; omega, by omega, by
        simp [List.get_cons_zero, List.get_cons_succ, hq_eq.symm]⟩
    · obtain ⟨p, q, hp, hq, hpq, heq⟩ := ih (hnd ha)
      exact ⟨p + 1, q + 1, by simp; omega, by simp; omega, by omega, by
        simp [List.get_cons_succ]; exact heq⟩

/-- Any walk between distinct vertices can be trimmed to a
    Nodup (simple) path with the same endpoints. -/
private theorem walk_to_nodup_path {n : ℕ} {i j : Fin n} (adj : Matrix (Fin n) (Fin n) ℤ)
    (walk : List (Fin n))
    (hhead : walk.head? = some i) (hlast : walk.getLast? = some j)
    (hij : i ≠ j)
    (hedges : ∀ t, (ht : t + 1 < walk.length) →
      adj (walk.get ⟨t, by omega⟩) (walk.get ⟨t + 1, ht⟩) = 1) :
    ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      path.Nodup ∧ 2 ≤ path.length ∧
      ∀ t, (ht : t + 1 < path.length) →
        adj (path.get ⟨t, by omega⟩) (path.get ⟨t + 1, ht⟩) = 1 := by
  -- General statement with universally quantified endpoints, by induction on length.
  -- At each step: if the head appears in the tail, drop to its occurrence and recurse.
  -- If not, recurse on the tail and prepend the head.
  suffices h_gen : ∀ (m : ℕ) (w : List (Fin n)) (a b : Fin n),
      w.length ≤ m → a ≠ b →
      w.head? = some a → w.getLast? = some b →
      (∀ t, (ht : t + 1 < w.length) →
        adj (w.get ⟨t, by omega⟩) (w.get ⟨t + 1, ht⟩) = 1) →
      ∃ path : List (Fin n),
        path.head? = some a ∧ path.getLast? = some b ∧
        path.Nodup ∧ 2 ≤ path.length ∧
        ∀ t, (ht : t + 1 < path.length) →
          adj (path.get ⟨t, by omega⟩) (path.get ⟨t + 1, ht⟩) = 1 by
    exact h_gen walk.length walk i j le_rfl hij hhead hlast hedges
  intro m
  induction m with
  | zero =>
    intro w a b hwm _ hwh
    exact absurd hwh (by cases w <;> simp_all)
  | succ m ih =>
    intro w a b hwm hab hwh hwl hwe
    match w, hwh, hwl with
    | [], hwh, _ => simp at hwh
    | [x], hwh, hwl =>
      simp only [List.head?, List.getLast?_singleton, Option.some.injEq] at hwh hwl
      exact absurd (hwh ▸ hwl ▸ rfl : a = b) hab
    | x :: y :: tl, hwh, hwl =>
      -- x = a from the head
      have hxa : x = a := by simpa using hwh
      have rest_last : (y :: tl).getLast? = some b := by
        rwa [← List.getLast?_cons_cons (a := x)]
      have hxy : adj x y = 1 := by have := hwe 0 (by simp); simpa
      have rest_edges : ∀ t, (ht : t + 1 < (y :: tl).length) →
          adj ((y :: tl).get ⟨t, by omega⟩) ((y :: tl).get ⟨t + 1, ht⟩) = 1 := by
        intro t ht; simpa using hwe (t + 1) (by simp at ht ⊢; omega)
      by_cases hyb : y = b
      · -- y = b, path = [x, y] = [a, b]
        refine ⟨[x, y], ?_, ?_, ?_, ?_, ?_⟩
        · simp [hxa]
        · simp [hyb]
        · simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
            List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true]
          intro h; exact hab (hxa ▸ h ▸ hyb)
        · simp
        · intro t ht; simp at ht
          have ht0 : t = 0 := by omega
          subst ht0; simpa
      · -- y ≠ b, recurse on (y :: tl)
        obtain ⟨P, hPh, hPl, hPnd, hPlen, hPe⟩ :=
          ih (y :: tl) y b (by simp only [List.length_cons] at hwm ⊢; omega) hyb (by simp) rest_last rest_edges
        by_cases ha_in : x ∈ P
        · -- x ∈ P: extract subpath from x to b by dropping prefix
          obtain ⟨⟨q, hq⟩, hq_eq⟩ := List.mem_iff_get.mp ha_in
          have hP_drop_ne : P.drop q ≠ [] := by
            intro h; simp [List.length_drop] at h; omega
          refine ⟨P.drop q, ?_, ?_, ?_, ?_, ?_⟩
          · -- head = x = a
            rw [List.head?_eq_head hP_drop_ne]; congr 1
            have h0 : (P.drop q)[0]'(by simp; omega) = P[q] := by
              simp [List.getElem_drop]
            rw [← List.getElem_zero (h := by simp; omega), h0]
            show P.get ⟨q, hq⟩ = a; rw [hq_eq, hxa]
          · -- last = b
            have hPne : P ≠ [] := by intro h; simp [h] at hPlen
            have : (P.drop q).getLast? = P.getLast? := by
              rw [List.getLast?_eq_some_getLast hP_drop_ne,
                  List.getLast?_eq_some_getLast hPne]; congr 1
              simp [List.getLast_eq_getElem, List.getElem_drop]; congr 1; omega
            rw [this]; exact hPl
          · exact hPnd.sublist (List.drop_sublist q P)
          · -- length ≥ 2
            by_contra hlt; push_neg at hlt
            obtain ⟨v, hv⟩ : ∃ v, P.drop q = [v] := by
              match hm : P.drop q, hP_drop_ne with
              | [v], _ => exact ⟨v, rfl⟩
              | [], h => exact absurd rfl h
              | _ :: _ :: _, _ => rw [hm] at hlt; simp at hlt; omega
            have hva : v = x := by
              have h1 : (P.drop q)[0]'(by simp; omega) = P[q] := by
                simp [List.getElem_drop]
              simp [hv] at h1; exact h1 ▸ hq_eq
            have hvb : v = b := by
              have hPne : P ≠ [] := by intro h; simp [h] at hPlen
              have hPl' : P.getLast hPne = b := by
                rw [List.getLast?_eq_some_getLast hPne] at hPl
                exact Option.some_injective _ hPl
              have : (P.drop q).getLast hP_drop_ne = P.getLast hPne := by
                simp [List.getLast_eq_getElem, List.getElem_drop]; congr 1; omega
              simp [hv] at this; rw [this]; exact hPl'
            exact hab (by rw [← hxa, ← hva, hvb])
          · -- edges
            intro t ht
            have hlen_drop : (P.drop q).length = P.length - q := by simp
            have := hPe (q + t) (by omega)
            show adj (P.drop q)[t] (P.drop q)[t + 1] = 1
            simp only [List.getElem_drop]
            convert this using 2 <;> omega
        · -- x ∉ P: prepend x
          refine ⟨x :: P, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hxa]
          · -- last = b
            cases P with
            | nil => simp at hPlen
            | cons p ps => simp only [List.getLast?_cons_cons]; exact hPl
          · exact List.nodup_cons.mpr ⟨ha_in, hPnd⟩
          · simp; omega
          · -- edges
            intro t ht
            match t with
            | 0 =>
              show adj (x :: P)[0] (x :: P)[1] = 1
              simp only [List.getElem_cons_zero, List.getElem_cons_succ]
              have hP0 : P[0]'(by omega) = y := by
                cases P with
                | nil => simp at hPlen
                | cons p ps => simp only [List.head?, Option.some.injEq] at hPh; simp [hPh]
              rw [hP0]; exact hxy
            | t' + 1 =>
              show adj (x :: P)[t' + 1] (x :: P)[t' + 2] = 1
              simp only [List.getElem_cons_succ]
              exact hPe t' (by simp at ht; omega)

/-- D̃_{k+5} has Nodup paths of length ≥ 3 between any two non-adjacent distinct vertices.
    This follows from D̃ being a tree: the unique path between any pair goes through
    the spine (vertices 2 to k+3), possibly via leaf branch points. -/
private theorem dTilde_nodup_path_between (k : ℕ) (i j : Fin (k + 6))
    (hij : i ≠ j) (h_nonadj : dTildeAdj k i j = 0) :
    ∃ path : List (Fin (k + 6)),
      path.head? = some i ∧ path.getLast? = some j ∧
      path.Nodup ∧ 3 ≤ path.length ∧
      ∀ t, (ht : t + 1 < path.length) →
        dTildeAdj k (path.get ⟨t, by omega⟩) (path.get ⟨t + 1, ht⟩) = 1 := by
  -- Step 1: adjacency helpers
  have adj_edge : ∀ (a b : Fin (k + 6)), dTildeEdgePred k a b → dTildeAdj k a b = 1 := by
    intro a b h; rw [dTildeAdj_eq_one_iff]; exact Or.inl h
  have adj_edge' : ∀ (a b : Fin (k + 6)), dTildeEdgePred k b a → dTildeAdj k a b = 1 := by
    intro a b h; rw [dTildeAdj_eq_one_iff]; exact Or.inr h
  -- Step 2: construct a walk between any two vertices via the spine
  -- Every vertex reaches vertex 2 or k+3, and spine connects them all
  -- We construct a walk, then use walk_to_nodup_path
  suffices h_walk : ∃ walk : List (Fin (k + 6)),
      walk.head? = some i ∧ walk.getLast? = some j ∧
      ∀ t, (ht : t + 1 < walk.length) →
        dTildeAdj k (walk.get ⟨t, by omega⟩) (walk.get ⟨t + 1, ht⟩) = 1 by
    obtain ⟨walk, hwh, hwl, hwe⟩ := h_walk
    obtain ⟨path, hph, hpl, hpnd, hplen, hpe⟩ :=
      walk_to_nodup_path (dTildeAdj k) walk hwh hwl hij hwe
    refine ⟨path, hph, hpl, hpnd, ?_, hpe⟩
    -- Boost length ≥ 2 to ≥ 3: if length = 2, path = [i, j], adj i j = 1, contradiction
    by_contra hlt; push_neg at hlt
    have hlen2 : path.length = 2 := by omega
    have h0 : path.get ⟨0, by omega⟩ = i := by
      cases path with
      | nil => simp at hplen
      | cons a _ => simpa using hph
    have h1 : path.get ⟨1, by omega⟩ = j := by
      match path, hlen2, hpl with
      | [_, b], _, hpl => simpa using hpl
    have := hpe 0 (by omega)
    rw [h0, h1] at this
    rw [this] at h_nonadj; exact one_ne_zero h_nonadj
  -- Step 3: construct the walk by classifying vertices
  -- Spine helpers for edge construction
  have spine_edge (a : ℕ) (ha : 2 ≤ a) (ha' : a + 1 ≤ k + 3) :
      dTildeAdj k ⟨a, by omega⟩ ⟨a + 1, by omega⟩ = 1 :=
    adj_edge _ _ (Or.inr (Or.inr (Or.inl ⟨ha, rfl, ha'⟩)))
  have left_edge (v : Fin (k + 6)) (hv : v.val ≤ 1) :
      dTildeAdj k v ⟨2, by omega⟩ = 1 := by
    rcases show v.val = 0 ∨ v.val = 1 from by omega with h | h
    · exact adj_edge _ _ (Or.inl ⟨h, rfl⟩)
    · exact adj_edge _ _ (Or.inr (Or.inl ⟨h, rfl⟩))
  have right_edge (v : Fin (k + 6)) (hv : k + 4 ≤ v.val) :
      dTildeAdj k v ⟨k + 3, by omega⟩ = 1 := by
    rcases show v.val = k + 4 ∨ v.val = k + 5 from by omega with h | h
    · exact adj_edge _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))))
    · exact adj_edge _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))))
  -- Classify i and j into left leaf (val ≤ 1), spine (2 ≤ val ≤ k+3), right leaf (val ≥ k+4)
  rcases show i.val ≤ 1 ∨ (2 ≤ i.val ∧ i.val ≤ k + 3) ∨ k + 4 ≤ i.val from by omega with
    hi_l | hi_s | hi_r <;>
  rcases show j.val ≤ 1 ∨ (2 ≤ j.val ∧ j.val ≤ k + 3) ∨ k + 4 ≤ j.val from by omega with
    hj_l | hj_s | hj_r
  · -- Case 1: left-left (both val ≤ 1), walk = [i, 2, j]
    exact ⟨[i, ⟨2, by omega⟩, j], by simp, by simp, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      match t, ht with
      | 0, _ => simp only [List.get]; exact left_edge i hi_l
      | 1, _ => simp only [List.get]; rw [(dTildeAdj_symm k).apply]; exact left_edge j hj_l⟩
  · -- Case 2: left-spine, walk = [i] ++ spine(2, j.val)
    have h2j : 2 ≤ j.val := hj_s.1
    refine ⟨i :: dTildeSpinePath k 2 j.val (by omega) hj_s.2 h2j, by simp, ?_, fun t ht => ?_⟩
    · rw [show i :: dTildeSpinePath k 2 j.val (by omega) hj_s.2 h2j =
          [i] ++ dTildeSpinePath k 2 j.val (by omega) hj_s.2 h2j from rfl,
          List.getLast?_append_of_ne_nil _
            (dTildeSpinePath_ne_nil k 2 j.val (by omega) hj_s.2 h2j)]
      convert dTildeSpinePath_last k 2 j.val (by omega) hj_s.2 h2j using 2
    · have hsplen := dTildeSpinePath_length k 2 j.val (by omega) hj_s.2 h2j
      simp only [List.length_cons] at ht
      simp only [List.get_eq_getElem]
      rcases t with _ | t
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ,
                    dTildeSpinePath_getElem]
        convert left_edge i hi_l using 2
      · simp only [List.getElem_cons_succ]
        exact dTildeSpinePath_edges k 2 j.val (by omega) hj_s.2 h2j t
          (by rw [hsplen] at ht ⊢; omega)
  · -- Case 3: left-right, walk = [i] ++ spine(2, k+3) ++ [j]
    set sp := dTildeSpinePath k 2 (k + 3) (by omega) (by omega) (by omega)
    have hsplen : sp.length = k + 3 - 2 + 1 :=
      dTildeSpinePath_length k 2 (k + 3) (by omega) (by omega) (by omega)
    refine ⟨(i :: sp) ++ [j], ?_, ?_, fun t ht => ?_⟩
    · simp -- head? = some i
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil j [])]; simp
    · have hwlen : ((i :: sp) ++ [j]).length = sp.length + 2 := by
        simp [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      rcases t with _ | t
      · -- t = 0: edge from i to sp[0] = ⟨2, _⟩
        have h0 : ((i :: sp) ++ [j]).get ⟨0, by omega⟩ = i := by
          show ((i :: sp) ++ [j])[0] = i; simp
        have h1 : ((i :: sp) ++ [j]).get ⟨1, by rw [hwlen]; rw [hsplen]; omega⟩ =
            ⟨2, by omega⟩ := by
          show ((i :: sp) ++ [j])[1] = ⟨2, by omega⟩
          simp only [List.getElem_append_left (show 1 < (i :: sp).length from by
            simp only [List.length_cons]; rw [hsplen]; omega),
            List.getElem_cons_succ]
          rw [dTildeSpinePath_getElem]
        rw [h0, h1]; exact left_edge i hi_l
      · -- t+1: edges in (i :: sp) ++ [j]
        rw [hwlen] at ht
        by_cases ht' : t + 2 < sp.length + 1
        · -- both indices in (i :: sp), use spine edges
          have h1 : ((i :: sp) ++ [j]).get ⟨t + 1, by omega⟩ =
              sp.get ⟨t, by omega⟩ := by
            show ((i :: sp) ++ [j])[t + 1] = sp[t]
            simp only [List.getElem_append_left (show t + 1 < (i :: sp).length from by
              simp only [List.length_cons]; omega), List.getElem_cons_succ]
          have h2 : ((i :: sp) ++ [j]).get ⟨t + 2, by omega⟩ =
              sp.get ⟨t + 1, by omega⟩ := by
            show ((i :: sp) ++ [j])[t + 2] = sp[t + 1]
            simp only [List.getElem_append_left (show t + 2 < (i :: sp).length from by
              simp only [List.length_cons]; omega), List.getElem_cons_succ]
          rw [h1, h2]
          exact dTildeSpinePath_edges k 2 (k + 3) (by omega) (by omega) (by omega) t
            (by rw [hsplen]; omega)
        · -- last edge: sp[last] = ⟨k+3,_⟩ to j
          have ht'eq : t + 2 = sp.length + 1 := by omega
          have h1 : ((i :: sp) ++ [j]).get ⟨t + 1, by omega⟩ =
              sp.get ⟨t, by omega⟩ := by
            show ((i :: sp) ++ [j])[t + 1] = sp[t]
            simp only [List.getElem_append_left (show t + 1 < (i :: sp).length from by
              simp only [List.length_cons]; omega), List.getElem_cons_succ]
          have h2 : ((i :: sp) ++ [j]).get ⟨t + 2, by omega⟩ = j := by
            show ((i :: sp) ++ [j])[t + 2] = j
            simp only [List.getElem_append_right (show (i :: sp).length ≤ t + 2 from by
              simp only [List.length_cons]; omega), List.length_cons,
              show t + 2 - (sp.length + 1) = 0 from by omega, List.getElem_cons_zero]
          rw [h1, h2, show sp.get ⟨t, _⟩ = sp[t] from rfl, dTildeSpinePath_getElem]
          rw [(dTildeAdj_symm k).apply]
          convert right_edge j hj_r using 2
          ext; simp only [Fin.val_mk]; rw [hsplen] at ht'eq; omega
  · -- Case 4: spine-left, walk = reverse(spine(2, i.val)) ++ [j]
    set sp := dTildeSpinePath k 2 i.val (by omega) hi_s.2 hi_s.1
    have hsplen : sp.length = i.val - 2 + 1 :=
      dTildeSpinePath_length k 2 i.val (by omega) hi_s.2 hi_s.1
    have hne : sp ≠ [] := dTildeSpinePath_ne_nil k 2 i.val (by omega) hi_s.2 hi_s.1
    refine ⟨sp.reverse ++ [j], ?_, by simp [List.getLast?_append_of_ne_nil], fun t ht => ?_⟩
    · -- head? = some i (head of reversed spine is the last of spine = ⟨i.val, _⟩)
      have : (sp.reverse ++ [j]).head? = sp.reverse.head? := by
        have : sp.reverse ≠ [] := by rwa [List.reverse_ne_nil_iff]
        exact List.head?_append_of_ne_nil _ this
      rw [this, List.head?_reverse]
      convert dTildeSpinePath_last k 2 i.val (by omega) hi_s.2 hi_s.1 using 2
    · have hwlen : (sp.reverse ++ [j]).length = sp.length + 1 := by
        simp [List.length_reverse]
      rw [hwlen] at ht
      by_cases ht' : t + 1 < sp.length
      · -- reversed spine edge: both indices in sp.reverse
        have h1 : (sp.reverse ++ [j]).get ⟨t, by omega⟩ =
            sp.get ⟨sp.length - 1 - t, by omega⟩ := by
          show (sp.reverse ++ [j])[t] = sp[sp.length - 1 - t]
          simp only [List.getElem_append_left (show t < sp.reverse.length from by
            rw [List.length_reverse]; omega), List.getElem_reverse]
        have h2 : (sp.reverse ++ [j]).get ⟨t + 1, by omega⟩ =
            sp.get ⟨sp.length - 1 - (t + 1), by omega⟩ := by
          show (sp.reverse ++ [j])[t + 1] = sp[sp.length - 1 - (t + 1)]
          simp only [List.getElem_append_left (show t + 1 < sp.reverse.length from by
            rw [List.length_reverse]; omega), List.getElem_reverse]
        rw [h1, h2]
        rw [show sp.get ⟨sp.length - 1 - t, _⟩ = sp[sp.length - 1 - t] from rfl,
            show sp.get ⟨sp.length - 1 - (t + 1), _⟩ = sp[sp.length - 1 - (t + 1)] from rfl,
            dTildeSpinePath_getElem, dTildeSpinePath_getElem, (dTildeAdj_symm k).apply]
        convert spine_edge (2 + (sp.length - 1 - (t + 1)))
          (by rw [hsplen]; omega) (by rw [hsplen]; omega) using 2
        ext; simp only [Fin.val_mk]; rw [hsplen]; omega
      · -- last edge: spine end (= ⟨2, _⟩) to left leaf j
        have ht'eq : t + 1 = sp.length := by omega
        have h1 : (sp.reverse ++ [j]).get ⟨t, by omega⟩ =
            sp.get ⟨sp.length - 1 - t, by omega⟩ := by
          show (sp.reverse ++ [j])[t] = sp[sp.length - 1 - t]
          simp only [List.getElem_append_left (show t < sp.reverse.length from by
            rw [List.length_reverse]; omega), List.getElem_reverse]
        have h2 : (sp.reverse ++ [j]).get ⟨t + 1, by omega⟩ = j := by
          show (sp.reverse ++ [j])[t + 1] = j
          simp only [List.getElem_append_right (show sp.reverse.length ≤ t + 1 from by
            rw [List.length_reverse]; omega), List.length_reverse,
            show t + 1 - sp.length = 0 from by omega, List.getElem_cons_zero]
        rw [h1, h2, show sp.get ⟨sp.length - 1 - t, _⟩ = sp[sp.length - 1 - t] from rfl,
            dTildeSpinePath_getElem]
        have : (⟨2 + (sp.length - 1 - t), by rw [hsplen]; omega⟩ : Fin (k + 6)) =
            ⟨2, by omega⟩ := by
          ext; simp only [Fin.val_mk]; rw [hsplen]; omega
        rw [this]
        exact adj_edge' _ _ (by
          rcases show j.val = 0 ∨ j.val = 1 from by omega with h | h
          · exact Or.inl ⟨h, rfl⟩
          · exact Or.inr (Or.inl ⟨h, rfl⟩))
  · -- Case 5: spine-spine, ascending or reversed spine path
    rcases show i.val ≤ j.val ∨ j.val < i.val from by omega with hij_le | hij_lt
    · exact ⟨dTildeSpinePath k i.val j.val hi_s.1 hj_s.2 (by omega),
        by convert dTildeSpinePath_head k i.val j.val hi_s.1 hj_s.2 (by omega) using 2,
        by convert dTildeSpinePath_last k i.val j.val hi_s.1 hj_s.2 (by omega) using 2,
        dTildeSpinePath_edges k i.val j.val hi_s.1 hj_s.2 (by omega)⟩
    · set sp := dTildeSpinePath k j.val i.val hj_s.1 hi_s.2 (by omega)
      refine ⟨sp.reverse,
        by rw [List.head?_reverse]; convert dTildeSpinePath_last k j.val i.val hj_s.1 hi_s.2 (by omega) using 2,
        by rw [List.getLast?_reverse]; convert dTildeSpinePath_head k j.val i.val hj_s.1 hi_s.2 (by omega) using 2,
        fun t ht => by
          have hsplen := dTildeSpinePath_length k j.val i.val hj_s.1 hi_s.2 (by omega)
          rw [List.length_reverse] at ht
          show dTildeAdj k sp.reverse[t] sp.reverse[t + 1] = 1
          simp only [List.getElem_reverse]
          rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
          rw [(dTildeAdj_symm k).apply]
          convert spine_edge (j.val + (sp.length - 1 - (t + 1)))
            (by rw [hsplen]; omega) (by rw [hsplen]; omega) using 2
          ext; simp only [Fin.val_mk, hsplen]; omega⟩
  · -- Case 6: spine-right, walk = spine(i.val, k+3) ++ [j]
    set sp := dTildeSpinePath k i.val (k + 3) hi_s.1 (by omega) (by omega)
    have hsplen : sp.length = k + 3 - i.val + 1 :=
      dTildeSpinePath_length k i.val (k+3) hi_s.1 (by omega) (by omega)
    refine ⟨sp ++ [j], ?_, by simp [List.getLast?_append_of_ne_nil], ?_⟩
    · have hne : sp ≠ [] := dTildeSpinePath_ne_nil k i.val (k+3) hi_s.1 (by omega) (by omega)
      have : (sp ++ [j]).head? = sp.head? := List.head?_append_of_ne_nil _ hne
      rw [this]; convert dTildeSpinePath_head k i.val (k+3) hi_s.1 (by omega) (by omega) using 2
    · intro t ht
      have hwlen : (sp ++ [j]).length = sp.length + 1 := by simp
      rw [hwlen] at ht
      by_cases ht' : t + 1 < sp.length
      · -- both indices in sp
        have h1 : (sp ++ [j]).get ⟨t, by omega⟩ = sp.get ⟨t, by omega⟩ := by
          show (sp ++ [j])[t] = sp[t]
          simp only [List.getElem_append_left (show t < sp.length from by omega)]
        have h2 : (sp ++ [j]).get ⟨t + 1, by omega⟩ = sp.get ⟨t + 1, by omega⟩ := by
          show (sp ++ [j])[t + 1] = sp[t + 1]
          simp only [List.getElem_append_left (show t + 1 < sp.length from by omega)]
        rw [h1, h2]
        exact dTildeSpinePath_edges k i.val (k+3) hi_s.1 (by omega) (by omega) t
          (by rw [hsplen]; omega)
      · -- last edge: sp[last] to j
        have ht'eq : t + 1 = sp.length := by omega
        have h1 : (sp ++ [j]).get ⟨t, by omega⟩ = sp.get ⟨t, by omega⟩ := by
          show (sp ++ [j])[t] = sp[t]
          simp only [List.getElem_append_left (show t < sp.length from by omega)]
        have h2 : (sp ++ [j]).get ⟨t + 1, by omega⟩ = j := by
          show (sp ++ [j])[t + 1] = j
          simp only [List.getElem_append_right (show sp.length ≤ t + 1 from by omega),
            show t + 1 - sp.length = 0 from by omega, List.getElem_cons_zero]
        rw [h1, h2, show sp.get ⟨t, _⟩ = sp[t] from rfl, dTildeSpinePath_getElem]
        rw [(dTildeAdj_symm k).apply]
        convert right_edge j hj_r using 2
        ext; simp only [Fin.val_mk]; rw [hsplen] at ht'eq; omega
  · -- Case 7: right-left, walk = [i] ++ reverse(spine(2, k+3)) ++ [j]
    set sp := dTildeSpinePath k 2 (k + 3) (by omega) (by omega) (by omega)
    have hsplen : sp.length = k + 3 - 2 + 1 :=
      dTildeSpinePath_length k 2 (k + 3) (by omega) (by omega) (by omega)
    have hne : sp ≠ [] := dTildeSpinePath_ne_nil k 2 (k + 3) (by omega) (by omega) (by omega)
    refine ⟨(i :: sp.reverse) ++ [j], ?_, ?_, fun t ht => ?_⟩
    · simp -- head? = some i
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil j [])]; simp
    · have hwlen : ((i :: sp.reverse) ++ [j]).length = sp.length + 2 := by
        simp only [List.length_append, List.length_cons, List.length_singleton,
                    List.length_reverse, List.length_nil]
      rcases t with _ | t
      · -- t = 0: edge from i to sp.reverse[0] = ⟨k+3, _⟩
        have h0 : ((i :: sp.reverse) ++ [j]).get ⟨0, by omega⟩ = i := by
          show ((i :: sp.reverse) ++ [j])[0] = i; simp
        have h1 : ((i :: sp.reverse) ++ [j]).get ⟨1, by rw [hwlen]; rw [hsplen]; omega⟩ =
            ⟨k + 3, by omega⟩ := by
          show ((i :: sp.reverse) ++ [j])[1] = ⟨k + 3, by omega⟩
          simp only [List.getElem_append_left (show 1 < (i :: sp.reverse).length from by
            simp only [List.length_cons, List.length_reverse]; omega),
            List.getElem_cons_succ, List.getElem_reverse]
          rw [dTildeSpinePath_getElem]
          congr 1; rw [hsplen]; omega
        rw [h0, h1]; exact right_edge i hi_r
      · -- t+1: edges in (i :: sp.reverse) ++ [j]
        by_cases ht' : t + 2 < sp.length + 1
        · -- both indices in (i :: sp.reverse)
          have h1 : ((i :: sp.reverse) ++ [j]).get ⟨t + 1, by omega⟩ =
              sp.get ⟨sp.length - 1 - t, by omega⟩ := by
            show ((i :: sp.reverse) ++ [j])[t + 1] = sp[sp.length - 1 - t]
            simp only [List.getElem_append_left (show t + 1 < (i :: sp.reverse).length from by
              simp only [List.length_cons, List.length_reverse]; omega),
              List.getElem_cons_succ, List.getElem_reverse]
          have h2 : ((i :: sp.reverse) ++ [j]).get ⟨t + 2, by omega⟩ =
              sp.get ⟨sp.length - 1 - (t + 1), by omega⟩ := by
            show ((i :: sp.reverse) ++ [j])[t + 2] = sp[sp.length - 1 - (t + 1)]
            simp only [List.getElem_append_left (show t + 2 < (i :: sp.reverse).length from by
              simp only [List.length_cons, List.length_reverse]; omega),
              List.getElem_cons_succ, List.getElem_reverse]
          rw [h1, h2,
              show sp.get ⟨sp.length - 1 - t, _⟩ = sp[sp.length - 1 - t] from rfl,
              show sp.get ⟨sp.length - 1 - (t + 1), _⟩ = sp[sp.length - 1 - (t + 1)] from rfl,
              dTildeSpinePath_getElem, dTildeSpinePath_getElem, (dTildeAdj_symm k).apply]
          convert spine_edge (2 + (sp.length - 1 - (t + 1)))
            (by rw [hsplen]; omega) (by rw [hsplen]; omega) using 2
          ext; simp only [Fin.val_mk]; rw [hsplen]; omega
        · -- last edge: ⟨2, _⟩ to left leaf j
          have ht'eq : t + 2 = sp.length + 1 := by omega
          have h1 : ((i :: sp.reverse) ++ [j]).get ⟨t + 1, by omega⟩ =
              sp.get ⟨sp.length - 1 - t, by omega⟩ := by
            show ((i :: sp.reverse) ++ [j])[t + 1] = sp[sp.length - 1 - t]
            simp only [List.getElem_append_left (show t + 1 < (i :: sp.reverse).length from by
              simp only [List.length_cons, List.length_reverse]; omega),
              List.getElem_cons_succ, List.getElem_reverse]
          have h2 : ((i :: sp.reverse) ++ [j]).get ⟨t + 2, by omega⟩ = j := by
            show ((i :: sp.reverse) ++ [j])[t + 2] = j
            simp only [List.getElem_append_right (show (i :: sp.reverse).length ≤ t + 2 from by
              simp only [List.length_cons, List.length_reverse]; omega),
              List.length_cons, List.length_reverse,
              show t + 2 - (sp.length + 1) = 0 from by omega, List.getElem_cons_zero]
          rw [h1, h2, show sp.get ⟨sp.length - 1 - t, _⟩ = sp[sp.length - 1 - t] from rfl,
              dTildeSpinePath_getElem]
          have : (⟨2 + (sp.length - 1 - t), by rw [hsplen]; omega⟩ : Fin (k + 6)) =
              ⟨2, by omega⟩ := by
            ext; simp only [Fin.val_mk]; rw [hsplen]; omega
          rw [this]
          exact adj_edge' _ _ (by
            rcases show j.val = 0 ∨ j.val = 1 from by omega with h | h
            · exact Or.inl ⟨h, rfl⟩
            · exact Or.inr (Or.inl ⟨h, rfl⟩))
  · -- Case 8: right-spine, walk = [i] ++ reverse(spine(j.val, k+3))
    have hjs1 := hj_s.1
    refine ⟨i :: (dTildeSpinePath k j.val (k + 3) hjs1 (by omega) (by omega)).reverse,
      by simp, ?_, fun t ht => ?_⟩
    · -- getLast? = some j (getLast of reversed spine = head of spine = ⟨j.val, _⟩)
      rw [show i :: (dTildeSpinePath k j.val (k + 3) hjs1 (by omega) (by omega)).reverse =
          [i] ++ (dTildeSpinePath k j.val (k + 3) hjs1 (by omega) (by omega)).reverse from rfl,
          List.getLast?_append_of_ne_nil _ (by
            rw [List.reverse_ne_nil_iff]
            exact dTildeSpinePath_ne_nil k j.val (k + 3) hjs1 (by omega) (by omega)),
          List.getLast?_reverse]
      convert dTildeSpinePath_head k j.val (k + 3) hjs1 (by omega) (by omega) using 2
    · set sp := dTildeSpinePath k j.val (k + 3) hjs1 (by omega) (by omega)
      have hsplen : sp.length = k + 3 - j.val + 1 :=
        dTildeSpinePath_length k j.val (k + 3) hjs1 (by omega) (by omega)
      simp only [List.length_cons, List.length_reverse] at ht
      simp only [List.get_eq_getElem]
      rcases t with _ | t
      · -- t = 0: edge from i to sp.reverse[0] = ⟨k+3, _⟩
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_reverse,
                    dTildeSpinePath_getElem]
        convert right_edge i hi_r using 2; ext; simp only [Fin.val_mk]; rw [hsplen]; omega
      · -- t+1: reversed spine edges
        simp only [List.getElem_cons_succ, List.getElem_reverse]
        rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem, (dTildeAdj_symm k).apply]
        convert spine_edge (j.val + (sp.length - 1 - (t + 1)))
          (by rw [hsplen]; omega) (by rw [hsplen]; omega) using 2
        ext; simp only [Fin.val_mk]; rw [hsplen]; omega
  · -- Case 9: right-right (both val ≥ k+4), walk = [i, k+3, j]
    exact ⟨[i, ⟨k + 3, by omega⟩, j], by simp, by simp, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      match t, ht with
      | 0, _ => simp only [List.get]; exact right_edge i hi_r
      | 1, _ => simp only [List.get]; rw [(dTildeAdj_symm k).apply]; exact right_edge j hj_r⟩
  /- -- Old proof attempt with many errors
  have spine_adj
      dTildeAdj k ⟨a, by omega⟩ ⟨a + 1, by omega⟩ = 1 := by
    intro a ha ha'; simp only [dTildeAdj]; rw [if_pos]
    left; right; right; left; exact ⟨ha, rfl, ha'⟩
  have spine_adj' : ∀ (a : ℕ), 2 ≤ a → a + 1 ≤ k + 3 →
      dTildeAdj k ⟨a + 1, by omega⟩ ⟨a, by omega⟩ = 1 := by
    intro a ha ha'
    have := (dTildeAdj_symm k).apply ⟨a + 1, by omega⟩ ⟨a, by omega⟩
    rw [this]; exact spine_adj a ha ha'
  have left_adj : ∀ (v : Fin (k + 6)), v.val ≤ 1 →
      dTildeAdj k v ⟨2, by omega⟩ = 1 := by
    intro v hv; simp only [dTildeAdj]; rw [if_pos]
    rcases show v.val = 0 ∨ v.val = 1 from by omega with h | h
    · left; constructor <;> [exact h; rfl]
    · left; right; left; constructor <;> [exact h; rfl]
  have left_adj' : ∀ (v : Fin (k + 6)), v.val ≤ 1 →
      dTildeAdj k ⟨2, by omega⟩ v = 1 := by
    intro v hv; rw [(dTildeAdj_symm k).apply]; exact left_adj v hv
  have right_adj : ∀ (v : Fin (k + 6)), k + 4 ≤ v.val →
      dTildeAdj k v ⟨k + 3, by omega⟩ = 1 := by
    intro v hv; simp only [dTildeAdj]; rw [if_pos]
    rcases show v.val = k + 4 ∨ v.val = k + 5 from by omega with h | h
    · left; right; right; right; left; constructor <;> [exact h; rfl]
    · left; right; right; right; right; constructor <;> [exact h; rfl]
  have right_adj' : ∀ (v : Fin (k + 6)), k + 4 ≤ v.val →
      dTildeAdj k ⟨k + 3, by omega⟩ v = 1 := by
    intro v hv; rw [(dTildeAdj_symm k).apply]; exact right_adj v hv
  -- Adjacency implies adjacency of values
  have adj_spine_consec : ∀ (a b : Fin (k + 6)), dTildeAdj k a b = 1 →
      (a.val ≤ 1 ∧ b.val = 2) ∨ (b.val ≤ 1 ∧ a.val = 2) ∨
      (2 ≤ a.val ∧ a.val + 1 = b.val ∧ b.val ≤ k + 3) ∨
      (2 ≤ b.val ∧ b.val + 1 = a.val ∧ a.val ≤ k + 3) ∨
      (a.val ≥ k + 4 ∧ b.val = k + 3) ∨ (b.val ≥ k + 4 ∧ a.val = k + 3) := by
    intro a b h
    simp only [dTildeAdj, dTildeEdgePred] at h
    split_ifs at h with hcond
    · rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · exact absurd h (by omega)
  -- Non-adjacency constraint
  have h_not_adj : ¬ (dTildeEdgePred k i j ∨ dTildeEdgePred k j i) := by
    intro h; simp only [dTildeAdj, h, ite_true] at h_nonadj
  -- Classify vertices
  rcases show i.val ≤ 1 ∨ (2 ≤ i.val ∧ i.val ≤ k + 3) ∨ k + 4 ≤ i.val from by omega with
    hi_l | hi_s | hi_r <;>
  rcases show j.val ≤ 1 ∨ (2 ≤ j.val ∧ j.val ≤ k + 3) ∨ k + 4 ≤ j.val from by omega with
    hj_l | hj_s | hj_r
  · -- Both left leaves: path = [i, 2, j]
    refine ⟨[i, ⟨2, by omega⟩, j], by simp, by simp, ?_, by simp, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        List.nodup_nil, and_self, and_true]
      exact ⟨by intro h; have := congr_arg Fin.val h; simp at this; omega,
        by intro h; rcases h with h | h <;> [exact hij h; have := congr_arg Fin.val h; simp at this; omega]⟩
    · intro t ht; simp at ht
      match t with
      | 0 => simp; exact left_adj i hi_l
      | 1 => simp; exact left_adj' j hj_l
  · -- Left leaf + spine j: need j.val ≥ 3 (since i adj to 2 but non-adj to j)
    have hj3 : 3 ≤ j.val := by
      by_contra h; push_neg at h; interval_cases j.val using hj_s.1, h
      · exact absurd (left_adj i hi_l) (by rw [show (⟨2, by omega⟩ : Fin (k + 6)) = j from by ext; omega]; rw [h_nonadj]; exact one_ne_zero)
    -- Path = [i] ++ spine(2, j.val)
    set spine := dTildeSpinePath k 2 j.val (by omega) hj_s.2 (by omega) with hspine_def
    refine ⟨i :: spine, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [List.getLast?_cons_cons (by exact dTildeSpinePath_ne_nil k 2 j.val (by omega) hj_s.2 (by omega))]
      convert dTildeSpinePath_last k 2 j.val (by omega) hj_s.2 (by omega) using 2
      ext; simp
    · rw [List.nodup_cons]
      exact ⟨fun hm => by have := (dTildeSpinePath_mem_val k 2 j.val (by omega) hj_s.2 (by omega) i hm).1; omega,
        dTildeSpinePath_nodup k 2 j.val (by omega) hj_s.2 (by omega)⟩
    · simp [dTildeSpinePath_length]; omega
    · intro t ht
      match t with
      | 0 =>
        show dTildeAdj k i spine[0] = 1
        rw [dTildeSpinePath_getElem]; simp; exact left_adj i hi_l
      | t' + 1 =>
        show dTildeAdj k spine[t'] spine[t' + 1] = 1
        exact dTildeSpinePath_edges k 2 j.val (by omega) hj_s.2 (by omega) t' (by
          simp [dTildeSpinePath_length] at ht ⊢; omega)
  · -- Left leaf + right leaf: path = [i] ++ spine(2, k+3) ++ [j]
    set spine := dTildeSpinePath k 2 (k + 3) (by omega) (by omega) (by omega) with hspine_def
    refine ⟨i :: (spine ++ [j]), ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [List.getLast?_append_of_ne_nil _ (by simp)]
    · rw [List.nodup_cons]; constructor
      · intro hm; rw [List.mem_append] at hm; rcases hm with hm | hm
        · exact absurd (dTildeSpinePath_mem_val k 2 (k+3) (by omega) (by omega) (by omega) i hm).1 (by omega)
        · simp at hm; exact hij (by rw [← hm])
      · rw [List.nodup_append]; refine ⟨dTildeSpinePath_nodup k 2 (k+3) (by omega) (by omega) (by omega),
          List.nodup_singleton j, ?_⟩
        intro v hv; simp at hv ⊢; intro heq; rw [← heq]
        exact absurd (dTildeSpinePath_mem_val k 2 (k+3) (by omega) (by omega) (by omega) v hv).2 (by omega)
    · simp [dTildeSpinePath_length]; omega
    · intro t ht
      have hspine_len := dTildeSpinePath_length k 2 (k+3) (by omega) (by omega) (by omega)
      match t with
      | 0 =>
        show dTildeAdj k i (spine ++ [j])[0] = 1
        rw [List.getElem_append_left (by rw [hspine_len]; omega)]
        rw [dTildeSpinePath_getElem]; simp; exact left_adj i hi_l
      | t' + 1 =>
        show dTildeAdj k (spine ++ [j])[t'] (spine ++ [j])[t' + 1] = 1
        simp at ht
        by_cases ht' : t' + 1 < spine.length
        · rw [List.getElem_append_left (by omega), List.getElem_append_left ht']
          exact dTildeSpinePath_edges k 2 (k+3) (by omega) (by omega) (by omega) t' (by omega)
        · -- t' is last spine index, t'+1 is j
          have ht'eq : t' + 1 = spine.length := by omega
          rw [List.getElem_append_left (by omega)]
          rw [show (spine ++ [j])[t' + 1] = j from by
            rw [List.getElem_append_right (by omega)]; simp [ht'eq]]
          rw [dTildeSpinePath_getElem]; simp [hspine_len] at ht'eq
          have : t' = k + 1 := by omega
          subst this; simp; exact right_adj' j hj_r
  · -- Spine i + left leaf j: need i.val ≥ 3
    have hi3 : 3 ≤ i.val := by
      by_contra h; push_neg at h; interval_cases i.val using hi_s.1, h
      · rw [show i = (⟨2, by omega⟩ : Fin (k + 6)) from by ext; omega] at h_nonadj
        exact absurd (left_adj' j hj_l) (by rw [h_nonadj]; exact one_ne_zero)
    -- Path = spine(j→2→i) reversed: actually spine(2, i.val) reversed ++ [j]
    -- Simpler: path = spine(i.val, 2) descending ++ [j]
    -- Use ascending spine reversed: spine(2, i.val).reverse ++ [j]
    -- Or: construct directly as [i, i-1, ..., 2, j]
    -- Let's use: reverse(spine(2, i.val)) ++ [j]
    set spine := dTildeSpinePath k 2 i.val (by omega) hi_s.2 (by omega) with hspine_def
    set path := spine.reverse ++ [j] with hpath_def
    refine ⟨path, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpath_def, List.head?_append (by simp [List.length_reverse]; rw [dTildeSpinePath_length]; omega)]
      rw [List.head?_reverse]
      convert dTildeSpinePath_last k 2 i.val (by omega) hi_s.2 (by omega) using 2
      ext; simp
    · simp [hpath_def, List.getLast?_append_of_ne_nil _ (by simp)]
    · rw [hpath_def, List.nodup_append]
      refine ⟨(dTildeSpinePath_nodup k 2 i.val (by omega) hi_s.2 (by omega)).reverse,
        List.nodup_singleton j, ?_⟩
      intro v hv; simp at hv ⊢; intro heq; rw [← heq]
      rw [List.mem_reverse] at hv
      exact absurd (dTildeSpinePath_mem_val k 2 i.val (by omega) hi_s.2 (by omega) v hv).1 (by omega)
    · simp [hpath_def, dTildeSpinePath_length]; omega
    · intro t ht
      rw [hpath_def] at ht ⊢
      have hspine_len := dTildeSpinePath_length k 2 i.val (by omega) hi_s.2 (by omega)
      have hrev_len : spine.reverse.length = spine.length := List.length_reverse _
      by_cases ht' : t + 1 < spine.reverse.length
      · -- Both in reversed spine
        show dTildeAdj k (spine.reverse ++ [j])[t] (spine.reverse ++ [j])[t + 1] = 1
        rw [List.getElem_append_left (by omega), List.getElem_append_left ht']
        -- spine.reverse[t] = spine[spine.length - 1 - t]
        simp only [List.getElem_reverse]
        rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
        -- Elements: ⟨2 + (len - 1 - t), _⟩ and ⟨2 + (len - 1 - (t + 1)), _⟩
        -- = ⟨2 + len - 1 - t, _⟩ and ⟨2 + len - 2 - t, _⟩
        -- This is adj (a+1) a where a = 2 + len - 2 - t
        exact spine_adj' (2 + (spine.length - 1 - (t + 1))) (by omega) (by omega)
      · -- t is last of reversed spine, t+1 is j
        have ht'eq : t + 1 = spine.reverse.length := by omega
        show dTildeAdj k (spine.reverse ++ [j])[t] (spine.reverse ++ [j])[t + 1] = 1
        rw [List.getElem_append_left (by omega)]
        rw [show (spine.reverse ++ [j])[t + 1] = j from by
          rw [List.getElem_append_right (by omega)]; simp [ht'eq]]
        simp only [List.getElem_reverse]
        rw [dTildeSpinePath_getElem]; simp [hspine_len, hrev_len] at ht'eq
        have : spine.length - 1 - t = 0 := by omega
        simp [this]; exact left_adj' j hj_l
  · -- Both spine: path along spine
    -- Non-adjacency means |i.val - j.val| ≥ 2
    have hdist : (i.val < j.val ∧ i.val + 1 < j.val) ∨ (j.val < i.val ∧ j.val + 1 < i.val) := by
      rcases show i.val < j.val ∨ j.val < i.val from by
        rcases Nat.lt_or_ge i.val j.val with h | h
        · left; exact h
        · right; exact lt_of_le_of_ne h (by intro h; exact hij (by ext; exact h)) with h | h
      · left; refine ⟨h, ?_⟩; by_contra hc; push_neg at hc
        have : i.val + 1 = j.val := by omega
        exact h_not_adj (Or.inl (Or.inr (Or.inr (Or.inl ⟨hi_s.1, this, by omega⟩))))
      · right; refine ⟨h, ?_⟩; by_contra hc; push_neg at hc
        have : j.val + 1 = i.val := by omega
        exact h_not_adj (Or.inr (Or.inr (Or.inl ⟨hj_s.1, this, by omega⟩)))
    rcases hdist with ⟨hij_lt, hij_gap⟩ | ⟨hji_lt, hji_gap⟩
    · -- i.val < j.val, ascending
      set spine := dTildeSpinePath k i.val j.val hi_s.1 hj_s.2 (by omega) with hspine_def
      refine ⟨spine, ?_, ?_, ?_, ?_, ?_⟩
      · convert dTildeSpinePath_head k i.val j.val hi_s.1 hj_s.2 (by omega) using 2; ext; simp
      · convert dTildeSpinePath_last k i.val j.val hi_s.1 hj_s.2 (by omega) using 2; ext; simp
      · exact dTildeSpinePath_nodup k i.val j.val hi_s.1 hj_s.2 (by omega)
      · rw [dTildeSpinePath_length]; omega
      · exact dTildeSpinePath_edges k i.val j.val hi_s.1 hj_s.2 (by omega)
    · -- j.val < i.val, descending: use reversed ascending spine
      set spine := dTildeSpinePath k j.val i.val hj_s.1 hi_s.2 (by omega) with hspine_def
      refine ⟨spine.reverse, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.head?_reverse]
        convert dTildeSpinePath_last k j.val i.val hj_s.1 hi_s.2 (by omega) using 2; ext; simp
      · rw [List.getLast?_reverse]
        convert dTildeSpinePath_head k j.val i.val hj_s.1 hi_s.2 (by omega) using 2; ext; simp
      · exact (dTildeSpinePath_nodup k j.val i.val hj_s.1 hi_s.2 (by omega)).reverse
      · rw [List.length_reverse, dTildeSpinePath_length]; omega
      · intro t ht
        rw [List.length_reverse] at ht
        show dTildeAdj k spine.reverse[t] spine.reverse[t + 1] = 1
        simp only [List.getElem_reverse]
        rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
        exact spine_adj' (j.val + (spine.length - 1 - (t + 1))) (by rw [dTildeSpinePath_length]; omega) (by rw [dTildeSpinePath_length]; omega)
  · -- Spine i + right leaf j: need i.val ≤ k + 2
    have hik2 : i.val ≤ k + 2 := by
      by_contra h; push_neg at h; have : i.val = k + 3 := by omega
      rw [show i = (⟨k + 3, by omega⟩ : Fin (k + 6)) from by ext; omega] at h_nonadj
      exact absurd (right_adj' j hj_r) (by rw [show dTildeAdj k ⟨k + 3, _⟩ j = dTildeAdj k i j from by
        congr 1; ext; omega]; rw [h_nonadj]; exact one_ne_zero)
    -- Path = spine(i.val, k+3) ++ [j]
    set spine := dTildeSpinePath k i.val (k + 3) hi_s.1 (by omega) (by omega) with hspine_def
    refine ⟨spine ++ [j], ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_append (by rw [dTildeSpinePath_length]; omega)]
      convert dTildeSpinePath_head k i.val (k+3) hi_s.1 (by omega) (by omega) using 2; ext; simp
    · simp [List.getLast?_append_of_ne_nil _ (by simp)]
    · rw [List.nodup_append]
      refine ⟨dTildeSpinePath_nodup k i.val (k+3) hi_s.1 (by omega) (by omega),
        List.nodup_singleton j, ?_⟩
      intro v hv; simp at hv ⊢; intro heq; rw [← heq]
      exact absurd (dTildeSpinePath_mem_val k i.val (k+3) hi_s.1 (by omega) (by omega) v hv).2 (by omega)
    · simp [dTildeSpinePath_length]; omega
    · intro t ht
      have hspine_len := dTildeSpinePath_length k i.val (k+3) hi_s.1 (by omega) (by omega)
      by_cases ht' : t + 1 < spine.length
      · rw [List.getElem_append_left (by omega), List.getElem_append_left ht']
        exact dTildeSpinePath_edges k i.val (k+3) hi_s.1 (by omega) (by omega) t (by omega)
      · have ht'eq : t + 1 = spine.length := by omega
        rw [List.getElem_append_left (by omega)]
        rw [show (spine ++ [j])[t + 1] = j from by
          rw [List.getElem_append_right (by omega)]; simp [ht'eq]]
        rw [dTildeSpinePath_getElem]; simp [hspine_len] at ht'eq
        have : t = k + 3 - i.val := by omega
        subst this; simp; exact right_adj' j hj_r
  · -- Right leaf + left leaf: path = [i] ++ spine(k+3, 2).reverse ++ [j]
    -- = [i] ++ reverse(spine(2, k+3)) ++ [j]
    set spine := dTildeSpinePath k 2 (k + 3) (by omega) (by omega) (by omega) with hspine_def
    set path := [i] ++ spine.reverse ++ [j] with hpath_def
    refine ⟨path, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpath_def]
    · simp [hpath_def, List.getLast?_append_of_ne_nil _ (by simp)]
    · rw [hpath_def]
      simp only [List.nodup_cons, List.nodup_append, List.nodup_singleton]
      refine ⟨?_, (dTildeSpinePath_nodup k 2 (k+3) (by omega) (by omega) (by omega)).reverse,
        ?_, ?_⟩
      · intro hm; rw [List.mem_append] at hm; rcases hm with hm | hm
        · rw [List.mem_reverse] at hm
          exact absurd (dTildeSpinePath_mem_val k 2 (k+3) (by omega) (by omega) (by omega) i hm).2 (by omega)
        · simp at hm; exact hij (by rw [← hm])
      · intro v hv; simp at hv ⊢; intro heq; rw [← heq]
        rw [List.mem_reverse] at hv
        exact absurd (dTildeSpinePath_mem_val k 2 (k+3) (by omega) (by omega) (by omega) v hv).1 (by omega)
      · simp; intro v hv heq
        rw [← heq, List.mem_reverse] at hv
        exact absurd (dTildeSpinePath_mem_val k 2 (k+3) (by omega) (by omega) (by omega) v hv).2 (by omega)
    · simp [hpath_def, dTildeSpinePath_length, List.length_reverse]; omega
    · intro t ht
      rw [hpath_def] at ht ⊢
      have hspine_len := dTildeSpinePath_length k 2 (k+3) (by omega) (by omega) (by omega)
      have hrev_len : spine.reverse.length = spine.length := List.length_reverse _
      show dTildeAdj k (([i] ++ spine.reverse ++ [j]).get ⟨t, by omega⟩)
        (([i] ++ spine.reverse ++ [j]).get ⟨t + 1, by omega⟩) = 1
      match t with
      | 0 =>
        simp; show dTildeAdj k i (spine.reverse ++ [j])[0] = 1
        rw [List.getElem_append_left (by rw [hrev_len]; rw [hspine_len]; omega)]
        simp only [List.getElem_reverse]; rw [dTildeSpinePath_getElem]
        simp [hspine_len]; exact right_adj i hi_r
      | t' + 1 =>
        simp
        show dTildeAdj k (spine.reverse ++ [j])[t'] (spine.reverse ++ [j])[t' + 1] = 1
        simp at ht
        by_cases ht'' : t' + 1 < spine.reverse.length
        · rw [List.getElem_append_left (by omega), List.getElem_append_left ht'']
          simp only [List.getElem_reverse]; rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
          exact spine_adj (2 + (spine.length - 1 - (t' + 1))) (by omega) (by rw [hspine_len]; omega)
        · have ht'eq : t' + 1 = spine.reverse.length := by omega
          rw [List.getElem_append_left (by omega)]
          rw [show (spine.reverse ++ [j])[t' + 1] = j from by
            rw [List.getElem_append_right (by omega)]; simp [ht'eq]]
          simp only [List.getElem_reverse]; rw [dTildeSpinePath_getElem]
          simp [hspine_len, hrev_len] at ht'eq
          have : spine.length - 1 - t' = 0 := by omega
          simp [this]; exact left_adj j hj_l
  · -- Right leaf + spine j: need j.val ≤ k + 2
    have hjk2 : j.val ≤ k + 2 := by
      by_contra h; push_neg at h; have : j.val = k + 3 := by omega
      rw [show j = (⟨k + 3, by omega⟩ : Fin (k + 6)) from by ext; omega] at h_nonadj
      exact absurd (right_adj i hi_r) (by rw [h_nonadj]; exact one_ne_zero)
    -- Path = [i] ++ reverse(spine(j.val, k+3))
    set spine := dTildeSpinePath k j.val (k + 3) hj_s.1 (by omega) (by omega) with hspine_def
    set path := i :: spine.reverse with hpath_def
    refine ⟨path, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpath_def]
    · rw [hpath_def, show (i :: spine.reverse).getLast? = spine.reverse.getLast? from by
        cases spine.reverse with | nil => simp [List.length_reverse, dTildeSpinePath_length] at * | cons a t => rfl]
      rw [List.getLast?_reverse]
      convert dTildeSpinePath_head k j.val (k+3) hj_s.1 (by omega) (by omega) using 2; ext; simp
    · rw [hpath_def, List.nodup_cons]
      exact ⟨fun hm => by rw [List.mem_reverse] at hm
        exact absurd (dTildeSpinePath_mem_val k j.val (k+3) hj_s.1 (by omega) (by omega) i hm).2 (by omega),
        (dTildeSpinePath_nodup k j.val (k+3) hj_s.1 (by omega) (by omega)).reverse⟩
    · simp [hpath_def, dTildeSpinePath_length, List.length_reverse]; omega
    · intro t ht
      rw [hpath_def] at ht ⊢
      have hspine_len := dTildeSpinePath_length k j.val (k+3) hj_s.1 (by omega) (by omega)
      match t with
      | 0 =>
        show dTildeAdj k i spine.reverse[0] = 1
        simp only [List.getElem_reverse]; rw [dTildeSpinePath_getElem]
        simp [hspine_len]; exact right_adj i hi_r
      | t' + 1 =>
        show dTildeAdj k spine.reverse[t'] spine.reverse[t' + 1] = 1
        simp only [List.getElem_reverse]; rw [dTildeSpinePath_getElem, dTildeSpinePath_getElem]
        exact spine_adj (j.val + (spine.length - 1 - (t' + 1))) (by omega) (by
          rw [hspine_len]; simp at ht; omega)
  · -- Both right leaves: path = [i, k+3, j]
    refine ⟨[i, ⟨k + 3, by omega⟩, j], by simp, by simp, ?_, by simp, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        List.nodup_nil, and_self, and_true]
      exact ⟨by intro h; have := congr_arg Fin.val h; simp at this; omega,
        by intro h; rcases h with h | h <;> [exact hij h; have := congr_arg Fin.val h; simp at this; omega]⟩
    · intro t ht; simp at ht
      match t with
      | 0 => simp; exact right_adj i hi_r
      | 1 => simp; exact right_adj' j hj_r
  -/

-- Ẽ₆ embedding requires 49-pair adjacency verification via fin_cases + linarith
set_option maxHeartbeats 6400000 in
/-- A connected acyclic simple graph with ≥ 2 non-adjacent degree-3 vertices, all
    degrees ≤ 3, and non-positive-definite Cartan form has infinite representation type.

    Such a graph is a tree with multiple branch points, forming an extended Dynkin D̃_n
    structure or containing one as a subgraph. The proof constructs a forbidden subgraph
    embedding (Ẽ₆, Ẽ₇, T(1,2,5) from branch points with long arms) or reduces to the
    D̃_n infinite type result for the "caterpillar" case H(1,1,d,1,1). -/
private theorem non_adjacent_branches_infinite_type {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ w : Fin n) (hv₀ : vertexDegree adj v₀ = 3) (hw : vertexDegree adj w = 3)
    (hne : w ≠ v₀) (h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Case 1: If some pair of branch points is adjacent somewhere, use that directly
  by_cases h_adj_exists : ∃ x y, adj x y = 1 ∧ vertexDegree adj x = 3 ∧ vertexDegree adj y = 3
  · obtain ⟨x, y, hxy, hx, hy⟩ := h_adj_exists
    exact adjacent_branches_infinite_type adj hsymm hdiag h01 h_acyclic x y hx hy hxy
  · -- Case 2: All branch points are pairwise non-adjacent
    push_neg at h_adj_exists
    -- Setup: convenience lemmas
    have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
    have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
      rw [hab, hdiag] at h; exact one_ne_zero h.symm
    -- Extract v₀'s 3 neighbors
    set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
    have hS₀_card : S₀.card = 3 := hv₀
    -- Get a first neighbor u₃
    have hS₀_ne : S₀.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hS₀_card
    obtain ⟨u₃, hu₃_mem⟩ := hS₀_ne
    have hu₃_adj : adj v₀ u₃ = 1 := (Finset.mem_filter.mp hu₃_mem).2
    -- Get the other two neighbors u₁, u₂
    have hS₀_erase : (S₀.erase u₃).card = 2 := by
      rw [Finset.card_erase_of_mem hu₃_mem, hS₀_card]
    obtain ⟨u₁, u₂, hu₁₂, hS₀_eq⟩ := Finset.card_eq_two.mp hS₀_erase
    have hu₁_mem : u₁ ∈ S₀.erase u₃ := hS₀_eq ▸ Finset.mem_insert_self u₁ _
    have hu₂_mem : u₂ ∈ S₀.erase u₃ := hS₀_eq ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self u₂))
    have hu₁_adj : adj v₀ u₁ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁_mem)).2
    have hu₂_adj : adj v₀ u₂ = 1 :=
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂_mem)).2
    have hu₁_ne_u₃ : u₁ ≠ u₃ := Finset.ne_of_mem_erase hu₁_mem
    have hu₂_ne_u₃ : u₂ ≠ u₃ := Finset.ne_of_mem_erase hu₂_mem
    -- All neighbors have degree < 3
    have hu₁_deg : vertexDegree adj u₁ < 3 := h_no_adj_branch u₁ hu₁_adj
    have hu₂_deg : vertexDegree adj u₂ < 3 := h_no_adj_branch u₂ hu₂_adj
    have hu₃_deg : vertexDegree adj u₃ < 3 := h_no_adj_branch u₃ hu₃_adj
    -- Neighbors ≠ v₀
    have hu₁_ne_v₀ : u₁ ≠ v₀ := (ne_of_adj v₀ u₁ hu₁_adj).symm
    have hu₂_ne_v₀ : u₂ ≠ v₀ := (ne_of_adj v₀ u₂ hu₂_adj).symm
    have hu₃_ne_v₀ : u₃ ≠ v₀ := (ne_of_adj v₀ u₃ hu₃_adj).symm
    -- Reverse adjacencies
    have hu₁_v₀ : adj u₁ v₀ = 1 := (adj_comm u₁ v₀).trans hu₁_adj
    have hu₂_v₀ : adj u₂ v₀ = 1 := (adj_comm u₂ v₀).trans hu₂_adj
    have hu₃_v₀ : adj u₃ v₀ = 1 := (adj_comm u₃ v₀).trans hu₃_adj
    -- Degree ≥ 1 for all neighbors (they're adjacent to v₀)
    have hu₁_deg_ge : 1 ≤ vertexDegree adj u₁ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁_v₀⟩⟩
    have hu₂_deg_ge : 1 ≤ vertexDegree adj u₂ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₂_v₀⟩⟩
    have hu₃_deg_ge : 1 ≤ vertexDegree adj u₃ :=
      Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₃_v₀⟩⟩
    -- Helper: the three leaf-cases (u₁ leaf, u₂ leaf, u₃ leaf) are symmetric. We
    -- extract a uniform `leaf_case` helper that handles all three.
    --
    -- Proof strategy (SORRY — see issue for subgraph embedding details):
    -- v₀ has a leaf neighbor `leaf`. The other two neighbors of v₀ have degree ≤ 2.
    -- Since w ≠ v₀ is a degree-3 branch point (non-adjacent to v₀), the unique path
    -- from v₀ to w passes through exactly one of v₀'s non-leaf neighbors (call it
    -- the "chain-side" neighbor). The path v₀ = p₀, p₁, ..., p_k = w has internal
    -- vertices of degree exactly 2 (bounded above by h_no_adj_branch applied to
    -- neighbors of branch points, and below by path structure).
    --
    -- Then we case-split on:
    --   (a) degree of the non-chain non-leaf neighbor of v₀
    --   (b) degrees of w's two non-chain neighbors
    --   (c) path length k from v₀ to w
    -- and embed one of the following forbidden subgraphs based on structure:
    --   - D̃_{k+3} (when v₀ has 2 leaves AND w has 2 leaves)
    --   - Ẽ₇ = T(1,3,3)  (when arms extend appropriately)
    --   - T(1,2,5)       (when long arm at w beyond chain length)
    -- Subgraph transfer via `subgraph_infinite_type_transfer`.
    have leaf_case : ∀ leaf : Fin n, adj v₀ leaf = 1 → vertexDegree adj leaf = 1 →
        ¬ IsFiniteTypeQuiver n adj := fun leaf h_leaf_adj h_leaf_deg => by
      -- v₀ and w are not adjacent (no adjacent degree-3 pair exists)
      have h_v₀w_nonadj : adj v₀ w ≠ 1 := by
        intro hadj
        have := h_adj_exists v₀ w hadj
        simp [hv₀, hw] at this
      -- Get a Nodup path from v₀ to w (via hconn + walk trimming).
      -- path = [v₀, c₁, ..., c_{d-1}, w] with length ≥ 3 (since non-adjacent)
      obtain ⟨chain, hchain_head, hchain_last, hchain_nodup, hchain_len, hchain_edges⟩ :
        ∃ chain : List (Fin n), chain.head? = some v₀ ∧ chain.getLast? = some w ∧
          chain.Nodup ∧ 3 ≤ chain.length ∧
          ∀ t, (ht : t + 1 < chain.length) →
            adj (chain.get ⟨t, by omega⟩) (chain.get ⟨t + 1, ht⟩) = 1 := by
        -- Get walk from hconn, trim to Nodup
        obtain ⟨walk, hwh, hwl, hwe⟩ := hconn v₀ w
        obtain ⟨spath, hsh, hsl, hsd, hslen, hse⟩ :=
          walk_to_nodup_path adj walk hwh hwl hne.symm hwe
        -- Nodup path length ≥ 3 since v₀ and w are non-adjacent
        refine ⟨spath, hsh, hsl, hsd, ?_, hse⟩
        by_contra hlt; push_neg at hlt
        have hlen2 : spath.length = 2 := by omega
        -- spath = [v₀, w], so adj v₀ w = 1, contradicting non-adjacency
        have h01 := hse 0 (by omega)
        have hfirst : spath.get ⟨0, by omega⟩ = v₀ := by
          cases spath with
          | nil => simp at hlen2
          | cons a _ => simpa using hsh
        have hsecond : spath.get ⟨1, by omega⟩ = w := by
          cases spath with
          | nil => simp at hlen2
          | cons a t =>
            cases t with
            | nil => simp at hlen2
            | cons b u =>
              cases u with
              | nil => simpa using hsl
              | cons _ _ => simp [List.length] at hlen2
        rw [hfirst, hsecond] at h01
        exact h_v₀w_nonadj h01
      -- chain[0] = v₀, chain[last] = w
      have hchain_ne : chain ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hchain_first : chain.get ⟨0, by omega⟩ = v₀ := by
        cases chain with
        | nil => exact absurd rfl hchain_ne
        | cons a t => simpa using hchain_head
      have hchain_last' : chain.getLast hchain_ne = w := by
        rw [List.getLast?_eq_some_getLast hchain_ne] at hchain_last
        exact Option.some_injective _ hchain_last
      -- chain[1] is adjacent to v₀ and distinct from it
      have hc1_adj : adj v₀ (chain.get ⟨1, by omega⟩) = 1 := by
        rw [← hchain_first]; exact hchain_edges 0 (by omega)
      -- leaf ≠ chain[1] (leaf has degree 1, but chain[1] connects to chain[2] and v₀)
      have hleaf_ne_c1 : leaf ≠ chain.get ⟨1, by omega⟩ := by
        intro heq
        -- leaf has degree 1, its only neighbor is v₀
        -- But chain[1] is also adjacent to chain[2] (if chain has length ≥ 3)
        -- chain[2] ≠ v₀ (Nodup)
        have hc1c2_adj : adj (chain.get ⟨1, by omega⟩) (chain.get ⟨2, by omega⟩) = 1 :=
          hchain_edges 1 (by omega)
        have hc2_ne_v₀ : chain.get ⟨2, by omega⟩ ≠ v₀ := by
          rw [← hchain_first]; intro h
          exact absurd ((hchain_nodup.get_inj_iff).mp h) (by simp)
        -- So chain[1] = leaf has at least 2 neighbors: v₀ and chain[2]
        have : 2 ≤ vertexDegree adj leaf := by
          rw [heq]; unfold vertexDegree
          have hv₀_in : v₀ ∈ Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm _ _).trans hc1_adj⟩
          have hc2_in : chain.get ⟨2, by omega⟩ ∈
              Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1c2_adj⟩
          have hsub : {v₀, chain.get ⟨2, by omega⟩} ⊆
              Finset.univ.filter (fun j => adj (chain.get ⟨1, by omega⟩) j = 1) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hc2_ne_v₀.symm] at this
          exact this
        omega
      -- v₀ has exactly 3 neighbors. leaf and chain[1] are two of them.
      -- The third neighbor is the "side arm" start.
      -- Since v₀ has degree 3 and S₀ lists all neighbors:
      -- leaf ∈ S₀, chain[1] ∈ S₀, and there's a third.
      have hleaf_in_S₀ : leaf ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_leaf_adj⟩
      have hc1_in_S₀ : chain.get ⟨1, by omega⟩ ∈ S₀ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1_adj⟩
      -- Get the third neighbor (side arm)
      have hS₀_remove2 : ((S₀.erase leaf).erase (chain.get ⟨1, by omega⟩)).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hleaf_ne_c1.symm, hc1_in_S₀⟩)]
        rw [Finset.card_erase_of_mem hleaf_in_S₀, hS₀_card]
      obtain ⟨side_arm, hside_eq⟩ := Finset.card_eq_one.mp hS₀_remove2
      have hside_mem : side_arm ∈ (S₀.erase leaf).erase (chain.get ⟨1, by omega⟩) :=
        hside_eq ▸ Finset.mem_singleton_self _
      have hside_adj : adj v₀ side_arm = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hside_mem))).2
      have hside_ne_leaf : side_arm ≠ leaf :=
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hside_mem)
      have hside_ne_c1 : side_arm ≠ chain.get ⟨1, by omega⟩ :=
        Finset.ne_of_mem_erase hside_mem
      -- Extract w's two non-chain neighbors (arm₁, arm₂)
      -- w has degree 3, one neighbor is chain[len-2]
      have hw_get : w = chain.get ⟨chain.length - 1, by omega⟩ := by
        rw [← hchain_last']; simp [List.getLast_eq_getElem]
      have hclast_idx : chain.get ⟨chain.length - 2, by omega⟩ ≠ w := by
        rw [hw_get]; intro h
        exact absurd ((hchain_nodup.get_inj_iff).mp h) (by simp; omega)
      have hw_chain_adj : adj w (chain.get ⟨chain.length - 2, by omega⟩) = 1 := by
        rw [adj_comm, hw_get]
        have := hchain_edges (chain.length - 2) (by omega)
        have h_nat : chain.length - 2 + 1 = chain.length - 1 := by omega
        rw [show chain.get ⟨chain.length - 2 + 1, _⟩ =
              chain.get ⟨chain.length - 1, by omega⟩ from by congr 1; exact Fin.ext h_nat] at this
        exact this
      set Sw := Finset.univ.filter (fun j => adj w j = 1) with hSw_def
      have hSw_card : Sw.card = 3 := hw
      have hpre_in_Sw : chain.get ⟨chain.length - 2, by omega⟩ ∈ Sw :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_chain_adj⟩
      have hSw_erase : (Sw.erase (chain.get ⟨chain.length - 2, by omega⟩)).card = 2 := by
        rw [Finset.card_erase_of_mem hpre_in_Sw, hSw_card]
      obtain ⟨arm₁, arm₂, harm₁₂, hSw_eq⟩ := Finset.card_eq_two.mp hSw_erase
      have harm₁_mem : arm₁ ∈ Sw.erase (chain.get ⟨chain.length - 2, by omega⟩) :=
        hSw_eq ▸ Finset.mem_insert_self arm₁ _
      have harm₂_mem : arm₂ ∈ Sw.erase (chain.get ⟨chain.length - 2, by omega⟩) :=
        hSw_eq ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self arm₂))
      have harm₁_adj : adj w arm₁ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase harm₁_mem)).2
      have harm₂_adj : adj w arm₂ = 1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase harm₂_mem)).2
      have harm₁_ne_pre : arm₁ ≠ chain.get ⟨chain.length - 2, by omega⟩ :=
        Finset.ne_of_mem_erase harm₁_mem
      have harm₂_ne_pre : arm₂ ≠ chain.get ⟨chain.length - 2, by omega⟩ :=
        Finset.ne_of_mem_erase harm₂_mem
      -- Embed D̃_{k+5} where k = chain.length - 2
      -- Spine vertices 2..k+3 map to chain[0..chain.length-1]
      set k := chain.length - 2 with hk_def
      have hk_add : k + 2 = chain.length := by omega
      -- Convenience adjacency facts
      have leaf_adj_v₀ : adj leaf v₀ = 1 := (adj_comm leaf v₀).trans h_leaf_adj
      have side_adj_v₀ : adj side_arm v₀ = 1 := (adj_comm side_arm v₀).trans hside_adj
      have arm₁_adj_w : adj arm₁ w = 1 := (adj_comm arm₁ w).trans harm₁_adj
      have arm₂_adj_w : adj arm₂ w = 1 := (adj_comm arm₂ w).trans harm₂_adj
      have leaf_ne_v₀ : leaf ≠ v₀ := (ne_of_adj v₀ leaf h_leaf_adj).symm
      have side_ne_v₀ : side_arm ≠ v₀ := (ne_of_adj v₀ side_arm hside_adj).symm
      have arm₁_ne_w : arm₁ ≠ w := (ne_of_adj w arm₁ harm₁_adj).symm
      have arm₂_ne_w : arm₂ ≠ w := (ne_of_adj w arm₂ harm₂_adj).symm
      -- chain[last] = w
      have hchain_get_last : chain.get ⟨chain.length - 1, by omega⟩ = w := by
        conv_rhs => rw [← hchain_last']
        simp [List.getLast_eq_getElem]
      -- leaf's only neighbor is v₀
      have leaf_only : ∀ x, adj leaf x = 1 → x = v₀ := by
        intro x hx
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_leaf_deg
        have h1 : v₀ = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, leaf_adj_v₀⟩)
        exact (Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hx⟩)).trans h1.symm
      -- Distinctness: leaf ∉ chain
      have leaf_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
          leaf ≠ chain.get ⟨idx, hidx⟩ := by
        intro idx hidx heq
        by_cases h0 : idx = 0
        · subst h0; rw [hchain_first] at heq; exact leaf_ne_v₀ heq
        · by_cases h1 : idx = 1
          · subst h1; exact hleaf_ne_c1 heq
          · -- idx ≥ 2: chain[idx-1] is a neighbor of leaf = chain[idx], but ≠ v₀
            have hedge : adj (chain.get ⟨idx - 1, by omega⟩)
                (chain.get ⟨idx, hidx⟩) = 1 := by
              have h_nat : idx - 1 + 1 = idx := by omega
              have h := hchain_edges (idx - 1) (by omega)
              rwa [show chain.get ⟨idx - 1 + 1, by omega⟩ =
                chain.get ⟨idx, hidx⟩ from by congr 1; exact Fin.ext h_nat] at h
            rw [← heq] at hedge
            have := leaf_only _ ((adj_comm _ _).trans hedge)
            rw [← hchain_first] at this
            exact absurd ((hchain_nodup.get_inj_iff).mp this) (by simp; omega)
      -- Distinctness: side_arm ∉ chain (uses acyclicity for idx ≥ 2)
      have side_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
          side_arm ≠ chain.get ⟨idx, hidx⟩ := by
        intro idx hidx heq
        by_cases h0 : idx = 0
        · subst h0; rw [hchain_first] at heq; exact side_ne_v₀ heq
        · by_cases h1 : idx = 1
          · subst h1; exact hside_ne_c1 heq
          · -- side_arm = chain[idx] is adjacent to v₀ = chain[0]
            -- chain[0..idx] forms a cycle, contradicting acyclicity
            exfalso
            have h_back : adj (chain.get ⟨idx, hidx⟩) (chain.get ⟨0, by omega⟩) = 1 := by
              rw [← heq, hchain_first]; exact side_adj_v₀
            have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
              (chain.take (idx + 1))
              (by rw [List.length_take_of_le (by omega)]; omega)
              (hchain_nodup.sublist (List.take_sublist _ _))
              (fun t ht => by
                rw [List.length_take_of_le (by omega)] at ht
                have ht1 : t + 1 < chain.length := by omega
                have hgt : (chain.take (idx + 1)).get ⟨t, by
                    rw [List.length_take_of_le (by omega)]; omega⟩ =
                    chain.get ⟨t, by omega⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_take]
                have hgt1 : (chain.take (idx + 1)).get ⟨t + 1, by
                    rw [List.length_take_of_le (by omega)]; exact ht⟩ =
                    chain.get ⟨t + 1, ht1⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_take]
                rw [hgt, hgt1]; exact hchain_edges t ht1)
            have hlast : (chain.take (idx + 1)).getLast
                (List.ne_nil_of_length_pos (by
                  rw [List.length_take_of_le (by omega)]; omega)) =
                chain.get ⟨idx, hidx⟩ := by
              simp only [List.getLast_eq_getElem, List.get_eq_getElem,
                List.length_take_of_le (by omega : idx + 1 ≤ chain.length),
                show idx + 1 - 1 = idx from by omega, List.getElem_take]
            have hfirst : (chain.take (idx + 1)).get ⟨0, by
                rw [List.length_take_of_le (by omega)]; omega⟩ =
                chain.get ⟨0, by omega⟩ := by
              simp only [List.get_eq_getElem, List.getElem_take]
            rw [hlast, hfirst] at h_nonadj
            linarith
      -- Distinctness: arm₁ ∉ chain
      have arm₁_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
          arm₁ ≠ chain.get ⟨idx, hidx⟩ := by
        intro idx hidx heq
        by_cases hlast : idx = chain.length - 1
        · subst hlast; rw [hchain_get_last] at heq; exact arm₁_ne_w heq
        · by_cases hpre : idx = chain.length - 2
          · subst hpre; exact harm₁_ne_pre heq
          · -- arm₁ = chain[idx] is adjacent to w = chain[last]
            -- chain[idx..last] forms a cycle
            exfalso
            have h_back : adj (chain.get ⟨chain.length - 1, by omega⟩)
                (chain.get ⟨idx, hidx⟩) = 1 := by
              rw [hchain_get_last, ← heq]; exact harm₁_adj
            have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
              (chain.drop idx)
              (by rw [List.length_drop]; omega)
              (hchain_nodup.sublist (List.drop_sublist _ _))
              (fun t ht => by
                rw [List.length_drop] at ht
                have ht1 : idx + t + 1 < chain.length := by omega
                have hgt : (chain.drop idx).get ⟨t, by rw [List.length_drop]; omega⟩ =
                    chain.get ⟨idx + t, by omega⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_drop]
                have hgt1 : (chain.drop idx).get ⟨t + 1, by rw [List.length_drop]; exact ht⟩ =
                    chain.get ⟨idx + t + 1, ht1⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_drop]
                  rfl
                rw [hgt, hgt1]; exact hchain_edges (idx + t) (by omega))
            have hlast : (chain.drop idx).getLast
                (List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)) =
                chain.get ⟨chain.length - 1, by omega⟩ := by
              rw [List.getLast_drop, List.getLast_eq_getElem, List.get_eq_getElem]
            have hfirst : (chain.drop idx).get ⟨0, by rw [List.length_drop]; omega⟩ =
                chain.get ⟨idx, hidx⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop, Nat.add_zero]
            rw [hlast, hfirst] at h_nonadj
            linarith
      -- Distinctness: arm₂ ∉ chain
      have arm₂_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
          arm₂ ≠ chain.get ⟨idx, hidx⟩ := by
        intro idx hidx heq
        by_cases hlast : idx = chain.length - 1
        · subst hlast; rw [hchain_get_last] at heq; exact arm₂_ne_w heq
        · by_cases hpre : idx = chain.length - 2
          · subst hpre; exact harm₂_ne_pre heq
          · exfalso
            have h_back : adj (chain.get ⟨chain.length - 1, by omega⟩)
                (chain.get ⟨idx, hidx⟩) = 1 := by
              rw [hchain_get_last, ← heq]; exact harm₂_adj
            have h_nonadj := acyclic_path_nonadj adj hsymm h01 h_acyclic
              (chain.drop idx)
              (by rw [List.length_drop]; omega)
              (hchain_nodup.sublist (List.drop_sublist _ _))
              (fun t ht => by
                rw [List.length_drop] at ht
                have ht1 : idx + t + 1 < chain.length := by omega
                have hgt : (chain.drop idx).get ⟨t, by rw [List.length_drop]; omega⟩ =
                    chain.get ⟨idx + t, by omega⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_drop]
                have hgt1 : (chain.drop idx).get ⟨t + 1, by rw [List.length_drop]; exact ht⟩ =
                    chain.get ⟨idx + t + 1, ht1⟩ := by
                  simp only [List.get_eq_getElem, List.getElem_drop]
                  rfl
                rw [hgt, hgt1]; exact hchain_edges (idx + t) (by omega))
            have hlast : (chain.drop idx).getLast
                (List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)) =
                chain.get ⟨chain.length - 1, by omega⟩ := by
              rw [List.getLast_drop, List.getLast_eq_getElem, List.get_eq_getElem]
            have hfirst : (chain.drop idx).get ⟨0, by rw [List.length_drop]; omega⟩ =
                chain.get ⟨idx, hidx⟩ := by
              simp only [List.get_eq_getElem, List.getElem_drop, Nat.add_zero]
            rw [hlast, hfirst] at h_nonadj
            linarith
      -- Cross-region distinctness: leaf ≠ arm₁, leaf ≠ arm₂
      have hleaf_ne_arm₁ : leaf ≠ arm₁ := by
        intro heq; have := leaf_only w (heq ▸ arm₁_adj_w); exact hne this
      have hleaf_ne_arm₂ : leaf ≠ arm₂ := by
        intro heq; have := leaf_only w (heq ▸ arm₂_adj_w); exact hne this
      -- side_arm ≠ arm₁, side_arm ≠ arm₂ (cycle via chain contradicts acyclicity)
      -- Helper: chain ++ [v] forms a cycle when v is adjacent to both chain[last]=w
      -- and chain[0]=v₀, contradicting acyclicity if v ∉ chain
      have side_arm_ne_arm (arm : Fin n) (harm_adj : adj w arm = 1)
          (harm_ne_chain : ∀ (idx : ℕ) (hidx : idx < chain.length),
            arm ≠ chain.get ⟨idx, hidx⟩) : side_arm ≠ arm := by
        intro heq
        -- chain ++ [side_arm] is a cycle: last→first edge is side_arm→v₀
        apply h_acyclic (chain ++ [side_arm])
          (by simp [List.length]; omega)
        · -- Nodup
          rw [List.nodup_append]
          refine ⟨hchain_nodup, List.nodup_singleton _, ?_⟩
          -- Disjointness: side_arm ∉ chain
          intro x hx1 y hy
          simp only [List.mem_singleton] at hy
          subst hy
          obtain ⟨⟨i, hi⟩, heq'⟩ := List.mem_iff_get.mp hx1
          exact heq' ▸ (side_ne_chain i hi).symm
        · -- Consecutive edges
          intro t ht
          simp only [List.length_append, List.length_singleton] at ht
          by_cases ht' : t + 1 < chain.length
          · -- Internal chain edge
            have hge1 : (chain ++ [side_arm]).get ⟨t, by omega⟩ = chain.get ⟨t, by omega⟩ := by
              simp only [List.get_eq_getElem]; exact List.getElem_append_left (by omega)
            have hge2 : (chain ++ [side_arm]).get ⟨t + 1, by omega⟩ = chain.get ⟨t + 1, ht'⟩ := by
              simp only [List.get_eq_getElem]; exact List.getElem_append_left ht'
            rw [hge1, hge2]; exact hchain_edges t ht'
          · -- Edge chain[last] → side_arm
            have htv : t = chain.length - 1 := by omega
            subst htv
            have hge1 : (chain ++ [side_arm]).get ⟨chain.length - 1, by omega⟩ =
                chain.get ⟨chain.length - 1, by omega⟩ := by
              simp only [List.get_eq_getElem]; exact List.getElem_append_left (by omega)
            have hge2 : (chain ++ [side_arm]).get ⟨chain.length - 1 + 1, by omega⟩ = side_arm := by
              simp only [List.get_eq_getElem]
              rw [List.getElem_append_right (by omega)]; simp [show chain.length - 1 + 1 - chain.length = 0 from by omega]
            rw [hge1, hge2, hchain_get_last, heq]; exact harm_adj
        · -- Back-edge: adj side_arm v₀ = 1, contradiction
          have hlast : (chain ++ [side_arm]).getLast
              (List.ne_nil_of_length_pos (by simp)) = side_arm := by
            rw [List.getLast_append_of_ne_nil (by simp) (by simp)]
            simp
          have hfirst : (chain ++ [side_arm]).get ⟨0, by simp⟩ =
              chain.get ⟨0, by omega⟩ := by
            simp only [List.get_eq_getElem]
            exact List.getElem_append_left (by omega)
          rw [hlast, hfirst, hchain_first]; exact side_adj_v₀
      have hside_ne_arm₁ : side_arm ≠ arm₁ :=
        side_arm_ne_arm arm₁ harm₁_adj arm₁_ne_chain
      have hside_ne_arm₂ : side_arm ≠ arm₂ :=
        side_arm_ne_arm arm₂ harm₂_adj arm₂_ne_chain
      -- Define the embedding φ : Fin (k+6) → Fin n
      let φ_fun : Fin (k + 6) → Fin n := fun ⟨i, _⟩ =>
        if i = 0 then leaf
        else if i = 1 then side_arm
        else if h : i ≤ k + 3 then chain.get ⟨i - 2, by omega⟩
        else if i = k + 4 then arm₁
        else arm₂
      -- Prove φ_fun is injective
      have φ_inj : Function.Injective φ_fun := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ heq
        simp only [Fin.mk.injEq]
        -- Unfold φ_fun let binding
        dsimp only [φ_fun] at heq
        -- Case analysis on regions
        by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;>
        by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;>
        by_cases haS : a ≤ k + 3 <;> by_cases hbS : b ≤ k + 3 <;>
        by_cases ha4 : a = k + 4 <;> by_cases hb4 : b = k + 4
        all_goals (simp only [ha0, hb0, ha1, hb1, haS, hbS, ha4, hb4,
          ite_true, ite_false, dite_true, dite_false, eq_self_iff_true,
          show (1:ℕ) = 0 ↔ False from by decide,
          show (1:ℕ) = 1 ↔ True from by decide,
          show (0:ℕ) = 0 ↔ True from by decide,
          show (k + 4 : ℕ) ≠ 0 from by omega,
          show (k + 4 : ℕ) ≠ 1 from by omega,
          show ¬((k + 4 : ℕ) ≤ k + 3) from by omega,
          show (k + 5 : ℕ) ≠ 0 from by omega,
          show (k + 5 : ℕ) ≠ 1 from by omega,
          show ¬((k + 5 : ℕ) ≤ k + 3) from by omega,
          show (k + 5 : ℕ) ≠ k + 4 from by omega,
          show (k + 3 : ℕ) ≠ 0 from by omega,
          show (k + 3 : ℕ) ≠ 1 from by omega,
          show (k + 3 : ℕ) ≤ k + 3 from by omega] at heq ⊢ <;> try omega)
        -- Remaining cross-region collision cases (try all orientations)
        all_goals first
          | exact absurd heq (leaf_ne_chain _ _)
          | exact absurd heq.symm (leaf_ne_chain _ _)
          | exact absurd heq (side_ne_chain _ _)
          | exact absurd heq.symm (side_ne_chain _ _)
          | exact absurd heq (arm₁_ne_chain _ _)
          | exact absurd heq.symm (arm₁_ne_chain _ _)
          | exact absurd heq (arm₂_ne_chain _ _)
          | exact absurd heq.symm (arm₂_ne_chain _ _)
          | exact absurd heq hleaf_ne_arm₁
          | exact absurd heq.symm hleaf_ne_arm₁
          | exact absurd heq hleaf_ne_arm₂
          | exact absurd heq.symm hleaf_ne_arm₂
          | exact absurd heq hside_ne_arm₁
          | exact absurd heq.symm hside_ne_arm₁
          | exact absurd heq hside_ne_arm₂
          | exact absurd heq.symm hside_ne_arm₂
          | exact absurd heq harm₁₂
          | exact absurd heq.symm harm₁₂
          | exact absurd heq hside_ne_leaf
          | exact absurd heq.symm hside_ne_leaf
          | (have := (hchain_nodup.get_inj_iff).mp heq; simp at this; omega)
      let φ : Fin (k + 6) ↪ Fin n := ⟨φ_fun, φ_inj⟩
      -- Edge preservation: D̃ edges map to host edges
      have hedges : ∀ i j : Fin (k + 6), dTildeAdj k i j = 1 →
          adj (φ i) (φ j) = 1 := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ hab
        rcases (dTildeAdj_eq_one_iff k ⟨a, ha⟩ ⟨b, hb⟩).mp hab with hp | hp <;>
          simp only [dTildeEdgePred] at hp <;>
          rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h12, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        -- Forward edges
        · -- 0→2: leaf → v₀
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h1, h2, ite_true, show (2:ℕ) ≠ 0 from by omega,
            show (2:ℕ) ≠ 1 from by omega, ite_false, show (2:ℕ) ≤ k + 3 from by omega,
            dite_true]
          rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
              hchain_first]
          exact leaf_adj_v₀
        · -- 1→2: side_arm → v₀
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h1, h2, show (1:ℕ) ≠ 0 from by omega, ite_true, ite_false,
            show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
            show (2:ℕ) ≤ k + 3 from by omega, dite_true]
          rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
              hchain_first]
          exact side_adj_v₀
        · -- Spine edge a→b (a+1=b, 2≤a, b≤k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          have ha0 : a ≠ 0 := by omega
          have ha1 : a ≠ 1 := by omega
          have haS : a ≤ k + 3 := by omega
          have hb0 : b ≠ 0 := by omega
          have hb1 : b ≠ 1 := by omega
          simp only [ha0, ha1, haS, hb0, hb1, h2, ite_true, ite_false, dite_true]
          have hb_idx : b - 2 = a - 2 + 1 := by omega
          rw [show chain.get ⟨b - 2, _⟩ = chain.get ⟨a - 2 + 1, by omega⟩ from by
                congr 1; exact Fin.ext hb_idx]
          exact hchain_edges (a - 2) (by omega)
        · -- (k+4)→(k+3): arm₁ → w (h1: a=k+4, h2: b=k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h1, show (k + 4 : ℕ) ≠ 0 from by omega,
            show (k + 4 : ℕ) ≠ 1 from by omega,
            show ¬(k + 4 ≤ k + 3) from by omega, ite_true, ite_false,
            h2, show (k + 3 : ℕ) ≠ 0 from by omega,
            show (k + 3 : ℕ) ≠ 1 from by omega,
            show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true]
          have hb_eq : k + 3 - 2 = chain.length - 1 := by omega
          rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
                congr 1; exact Fin.ext hb_eq,
              hchain_get_last]
          exact arm₁_adj_w
        · -- (k+5)→(k+3): arm₂ → w (h1: a=k+5, h2: b=k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h1, show (k + 5 : ℕ) ≠ 0 from by omega,
            show (k + 5 : ℕ) ≠ 1 from by omega,
            show ¬(k + 5 ≤ k + 3) from by omega,
            show (k + 5 : ℕ) ≠ k + 4 from by omega, ite_true, ite_false,
            h2, show (k + 3 : ℕ) ≠ 0 from by omega,
            show (k + 3 : ℕ) ≠ 1 from by omega,
            show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true]
          have hb_eq : k + 3 - 2 = chain.length - 1 := by omega
          rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
                congr 1; exact Fin.ext hb_eq,
              hchain_get_last]
          exact arm₂_adj_w
        -- Backward edges (symmetric)
        · -- 2→0: v₀ → leaf (h1: b=0, h2: a=2)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h2, h1, ite_true, ite_false,
            show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
            show (2:ℕ) ≤ k + 3 from by omega, dite_true]
          rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
              hchain_first]
          exact (adj_comm v₀ leaf).trans leaf_adj_v₀
        · -- 2→1: v₀ → side_arm (h1: b=1, h2: a=2)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h2, h1, ite_true, ite_false,
            show (2:ℕ) ≠ 0 from by omega, show (2:ℕ) ≠ 1 from by omega,
            show (2:ℕ) ≤ k + 3 from by omega, dite_true,
            show (1:ℕ) ≠ 0 from by omega]
          rw [show chain.get ⟨2 - 2, _⟩ = chain.get ⟨0, by omega⟩ from by congr 1,
              hchain_first]
          exact (adj_comm v₀ side_arm).trans side_adj_v₀
        · -- Spine backward (h1: 2≤b, h12: b+1=a, h2: a≤k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          have hb0 : b ≠ 0 := by omega
          have hb1 : b ≠ 1 := by omega
          have hbS : b ≤ k + 3 := by omega
          have ha0 : a ≠ 0 := by omega
          have ha1 : a ≠ 1 := by omega
          simp only [ha0, ha1, show a ≤ k + 3 from by omega, hb0, hb1, hbS,
            ite_true, ite_false, dite_true]
          rw [adj_comm]
          have ha_idx : a - 2 = b - 2 + 1 := by omega
          rw [show chain.get ⟨a - 2, _⟩ = chain.get ⟨b - 2 + 1, by omega⟩ from by
                congr 1; exact Fin.ext ha_idx]
          exact hchain_edges (b - 2) (by omega)
        · -- (k+3)→(k+4): w → arm₁ (h1: b=k+4, h2: a=k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h2, show (k + 3 : ℕ) ≠ 0 from by omega,
            show (k + 3 : ℕ) ≠ 1 from by omega,
            show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true,
            h1, show (k + 4 : ℕ) ≠ 0 from by omega, show (k + 4 : ℕ) ≠ 1 from by omega,
            show ¬(k + 4 ≤ k + 3) from by omega, ite_true, ite_false]
          have ha2 : k + 3 - 2 = chain.length - 1 := by omega
          rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
                congr 1; exact Fin.ext ha2,
              hchain_get_last]
          exact (adj_comm w arm₁).trans arm₁_adj_w
        · -- (k+3)→(k+5): w → arm₂ (h1: b=k+5, h2: a=k+3)
          show adj (φ_fun ⟨a, ha⟩) (φ_fun ⟨b, hb⟩) = 1
          dsimp only [φ_fun]
          simp only [h2, show (k + 3 : ℕ) ≠ 0 from by omega,
            show (k + 3 : ℕ) ≠ 1 from by omega,
            show (k + 3 : ℕ) ≤ k + 3 from by omega, dite_true,
            h1, show (k + 5 : ℕ) ≠ 0 from by omega, show (k + 5 : ℕ) ≠ 1 from by omega,
            show ¬(k + 5 ≤ k + 3) from by omega,
            show (k + 5 : ℕ) ≠ k + 4 from by omega, ite_true, ite_false]
          have ha2 : k + 3 - 2 = chain.length - 1 := by omega
          rw [show chain.get ⟨k + 3 - 2, _⟩ = chain.get ⟨chain.length - 1, by omega⟩ from by
                congr 1; exact Fin.ext ha2,
              hchain_get_last]
          exact (adj_comm w arm₂).trans arm₂_adj_w
      -- Apply tree_embed_adj_eq for full adjacency equality
      have hembed : ∀ i j, dTildeAdj k i j = adj (φ i) (φ j) :=
        tree_embed_adj_eq adj (dTildeAdj k) hsymm h01 hdiag h_acyclic
          (dTildeAdj_01 k) φ hedges
          (fun i j hij hnadj => dTilde_nodup_path_between k i j hij hnadj)
      -- Transfer infinite type from D̃ to host graph
      exact subgraph_infinite_type_transfer φ adj (dTildeAdj k) hsymm
        (fun v h => by rw [hdiag v] at h; exact absurd h (by omega))
        hembed (dTilde_not_finite_type k)
    by_cases hu₁_leaf : vertexDegree adj u₁ = 1
    · -- u₁ is a leaf. Delegate to leaf_case.
      exact leaf_case u₁ hu₁_adj hu₁_leaf
    · by_cases hu₂_leaf : vertexDegree adj u₂ = 1
      · exact leaf_case u₂ hu₂_adj hu₂_leaf
      · by_cases hu₃_leaf : vertexDegree adj u₃ = 1
        · exact leaf_case u₃ hu₃_adj hu₃_leaf
        · -- All 3 neighbors have degree = 2. Embed Ẽ₆ = T(2,2,2).
          have hu₁_deg2 : vertexDegree adj u₁ = 2 := by omega
          have hu₂_deg2 : vertexDegree adj u₂ = 2 := by omega
          have hu₃_deg2 : vertexDegree adj u₃ = 2 := by omega
          -- Extract each neighbor's other neighbor
          -- u₁'s other neighbor
          set Su₁ := Finset.univ.filter (fun j => adj u₁ j = 1)
          have hSu₁_card : Su₁.card = 2 := hu₁_deg2
          have hv₀_in_Su₁ : v₀ ∈ Su₁ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁_v₀⟩
          obtain ⟨u₁', hu₁'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₁, hSu₁_card])
          have hu₁'_mem : u₁' ∈ Su₁.erase v₀ := hu₁'_eq ▸ Finset.mem_singleton_self u₁'
          have hu₁'_adj : adj u₁ u₁' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁'_mem)).2
          have hu₁'_ne_v₀ : u₁' ≠ v₀ := Finset.ne_of_mem_erase hu₁'_mem
          -- u₁ has EXACTLY neighbors {v₀, u₁'}
          have hu₁_only : ∀ x, adj u₁ x = 1 → x = v₀ ∨ x = u₁' := by
            intro x hx
            have hx_mem : x ∈ Su₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            by_cases hxv : x = v₀; · left; exact hxv
            right; have hx_mem' : x ∈ Su₁.erase v₀ := Finset.mem_erase.mpr ⟨hxv, hx_mem⟩
            rw [hu₁'_eq] at hx_mem'; exact Finset.mem_singleton.mp hx_mem'
          -- u₂'s other neighbor
          set Su₂ := Finset.univ.filter (fun j => adj u₂ j = 1)
          have hSu₂_card : Su₂.card = 2 := hu₂_deg2
          have hv₀_in_Su₂ : v₀ ∈ Su₂ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₂_v₀⟩
          obtain ⟨u₂', hu₂'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₂, hSu₂_card])
          have hu₂'_mem : u₂' ∈ Su₂.erase v₀ := hu₂'_eq ▸ Finset.mem_singleton_self u₂'
          have hu₂'_adj : adj u₂ u₂' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂'_mem)).2
          have hu₂'_ne_v₀ : u₂' ≠ v₀ := Finset.ne_of_mem_erase hu₂'_mem
          have hu₂_only : ∀ x, adj u₂ x = 1 → x = v₀ ∨ x = u₂' := by
            intro x hx
            have hx_mem : x ∈ Su₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            by_cases hxv : x = v₀; · left; exact hxv
            right; have hx_mem' : x ∈ Su₂.erase v₀ := Finset.mem_erase.mpr ⟨hxv, hx_mem⟩
            rw [hu₂'_eq] at hx_mem'; exact Finset.mem_singleton.mp hx_mem'
          -- u₃'s other neighbor
          set Su₃ := Finset.univ.filter (fun j => adj u₃ j = 1)
          have hSu₃_card : Su₃.card = 2 := hu₃_deg2
          have hv₀_in_Su₃ : v₀ ∈ Su₃ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₃_v₀⟩
          obtain ⟨u₃', hu₃'_eq⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hv₀_in_Su₃, hSu₃_card])
          have hu₃'_mem : u₃' ∈ Su₃.erase v₀ := hu₃'_eq ▸ Finset.mem_singleton_self u₃'
          have hu₃'_adj : adj u₃ u₃' = 1 :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₃'_mem)).2
          have hu₃'_ne_v₀ : u₃' ≠ v₀ := Finset.ne_of_mem_erase hu₃'_mem
          have hu₃_only : ∀ x, adj u₃ x = 1 → x = v₀ ∨ x = u₃' := by
            intro x hx
            have hx_mem : x ∈ Su₃ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            by_cases hxv : x = v₀; · left; exact hxv
            right; have hx_mem' : x ∈ Su₃.erase v₀ := Finset.mem_erase.mpr ⟨hxv, hx_mem⟩
            rw [hu₃'_eq] at hx_mem'; exact Finset.mem_singleton.mp hx_mem'
          -- v₀'s ONLY neighbors are u₁, u₂, u₃
          have hv₀_only : ∀ x, adj v₀ x = 1 → x = u₁ ∨ x = u₂ ∨ x = u₃ := by
            intro x hx
            have hx_mem : x ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
            by_cases hxu₃ : x = u₃; · right; right; exact hxu₃
            have hx_mem' : x ∈ S₀.erase u₃ := Finset.mem_erase.mpr ⟨hxu₃, hx_mem⟩
            rw [hS₀_eq] at hx_mem'
            rcases Finset.mem_insert.mp hx_mem' with h | h
            · left; exact h
            · right; left; exact Finset.mem_singleton.mp h
          -- Reverse adjacencies for u_i'
          have hu₁'_u₁ : adj u₁' u₁ = 1 := (adj_comm u₁' u₁).trans hu₁'_adj
          have hu₂'_u₂ : adj u₂' u₂ = 1 := (adj_comm u₂' u₂).trans hu₂'_adj
          have hu₃'_u₃ : adj u₃' u₃ = 1 := (adj_comm u₃' u₃).trans hu₃'_adj
          -- u_i' ≠ u_i (from adjacency)
          have hu₁'_ne_u₁ : u₁' ≠ u₁ := (ne_of_adj u₁ u₁' hu₁'_adj).symm
          have hu₂'_ne_u₂ : u₂' ≠ u₂ := (ne_of_adj u₂ u₂' hu₂'_adj).symm
          have hu₃'_ne_u₃ : u₃' ≠ u₃ := (ne_of_adj u₃ u₃' hu₃'_adj).symm
          -- Non-edges via acyclic_no_triangle: neighbors of same vertex
          -- u₁-u₂: center v₀
          have hu₁u₂ : adj u₁ u₂ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₂
              hu₁₂ hu₁_ne_v₀ hu₂_ne_v₀ hu₁_adj hu₂_adj
          -- u₁-u₃: center v₀
          have hu₁u₃ : adj u₁ u₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₃
              hu₁_ne_u₃ hu₁_ne_v₀ hu₃_ne_v₀ hu₁_adj hu₃_adj
          -- u₂-u₃: center v₀
          have hu₂u₃ : adj u₂ u₃ = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₂ u₃
              hu₂_ne_u₃ hu₂_ne_v₀ hu₃_ne_v₀ hu₂_adj hu₃_adj
          -- v₀-u₁': center u₁ (v₀ and u₁' are both neighbors of u₁)
          have hv₀_u₁' : adj v₀ u₁' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₁ v₀ u₁'
              hu₁'_ne_v₀.symm (ne_of_adj v₀ u₁ hu₁_adj) hu₁'_ne_u₁ hu₁_v₀ hu₁'_adj
          -- v₀-u₂': center u₂
          have hv₀_u₂' : adj v₀ u₂' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₂ v₀ u₂'
              hu₂'_ne_v₀.symm (ne_of_adj v₀ u₂ hu₂_adj) hu₂'_ne_u₂ hu₂_v₀ hu₂'_adj
          -- v₀-u₃': center u₃
          have hv₀_u₃' : adj v₀ u₃' = 0 :=
            acyclic_no_triangle adj hsymm h01 h_acyclic u₃ v₀ u₃'
              hu₃'_ne_v₀.symm (ne_of_adj v₀ u₃ hu₃_adj) hu₃'_ne_u₃ hu₃_v₀ hu₃'_adj
          -- Distinctness: u_i' ≠ u_j (via adj v₀ u_j = 1 but adj v₀ u_i' = 0)
          have hu₁'_ne_u₂ : u₁' ≠ u₂ := by intro h; rw [h] at hv₀_u₁'; linarith
          have hu₁'_ne_u₃ : u₁' ≠ u₃ := by intro h; rw [h] at hv₀_u₁'; linarith
          have hu₂'_ne_u₁ : u₂' ≠ u₁ := by intro h; rw [h] at hv₀_u₂'; linarith
          have hu₂'_ne_u₃ : u₂' ≠ u₃ := by intro h; rw [h] at hv₀_u₂'; linarith
          have hu₃'_ne_u₁ : u₃' ≠ u₁ := by intro h; rw [h] at hv₀_u₃'; linarith
          have hu₃'_ne_u₂ : u₃' ≠ u₂ := by intro h; rw [h] at hv₀_u₃'; linarith
          -- Cross-arm non-adjacency via acyclic_path_nonadj with 4-vertex paths
          -- path [u₂, v₀, u₁, u₁'] → adj u₁' u₂ = 0
          have path_nodup4 : ∀ (a b c d : Fin n),
              a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
            intro a b c d hab hac had hbc hbd hcd
            simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
          have path_edges4 : ∀ (a b c d : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d].length) →
                adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d h₁ h₂ h₃ k hk
            have : k + 1 < 4 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
            rcases this with rfl | rfl | rfl <;> assumption
          -- u₁' not adj u₂: path [u₂, v₀, u₁, u₁']
          have hu₁'_u₂_nonadj : adj u₁' u₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂, v₀, u₁, u₁'] (by simp)
              (path_nodup4 u₂ v₀ u₁ u₁' hu₂_ne_v₀ hu₁₂.symm hu₁'_ne_u₂.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges4 u₂ v₀ u₁ u₁' (adj_comm u₂ v₀ |>.trans hu₂_adj) hu₁_adj hu₁'_adj)
          -- u₁' not adj u₃: path [u₃, v₀, u₁, u₁']
          have hu₁'_u₃_nonadj : adj u₁' u₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃, v₀, u₁, u₁'] (by simp)
              (path_nodup4 u₃ v₀ u₁ u₁' hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁'_ne_u₃.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges4 u₃ v₀ u₁ u₁' (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₁_adj hu₁'_adj)
          -- u₂' not adj u₁: path [u₁, v₀, u₂, u₂']
          have hu₂'_u₁_nonadj : adj u₂' u₁ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₁, v₀, u₂, u₂'] (by simp)
              (path_nodup4 u₁ v₀ u₂ u₂' hu₁_ne_v₀ hu₁₂ hu₂'_ne_u₁.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges4 u₁ v₀ u₂ u₂' (adj_comm u₁ v₀ |>.trans hu₁_adj) hu₂_adj hu₂'_adj)
          -- u₂' not adj u₃: path [u₃, v₀, u₂, u₂']
          have hu₂'_u₃_nonadj : adj u₂' u₃ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃, v₀, u₂, u₂'] (by simp)
              (path_nodup4 u₃ v₀ u₂ u₂' hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂'_ne_u₃.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges4 u₃ v₀ u₂ u₂' (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₂_adj hu₂'_adj)
          -- u₃' not adj u₁: path [u₁, v₀, u₃, u₃']
          have hu₃'_u₁_nonadj : adj u₃' u₁ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₁, v₀, u₃, u₃'] (by simp)
              (path_nodup4 u₁ v₀ u₃ u₃' hu₁_ne_v₀ hu₁_ne_u₃ hu₃'_ne_u₁.symm
                hu₃_ne_v₀.symm hu₃'_ne_v₀.symm hu₃'_ne_u₃.symm)
              (path_edges4 u₁ v₀ u₃ u₃' (adj_comm u₁ v₀ |>.trans hu₁_adj) hu₃_adj hu₃'_adj)
          -- u₃' not adj u₂: path [u₂, v₀, u₃, u₃']
          have hu₃'_u₂_nonadj : adj u₃' u₂ = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂, v₀, u₃, u₃'] (by simp)
              (path_nodup4 u₂ v₀ u₃ u₃' hu₂_ne_v₀ hu₂_ne_u₃ hu₃'_ne_u₂.symm
                hu₃_ne_v₀.symm hu₃'_ne_v₀.symm hu₃'_ne_u₃.symm)
              (path_edges4 u₂ v₀ u₃ u₃' (adj_comm u₂ v₀ |>.trans hu₂_adj) hu₃_adj hu₃'_adj)
          -- Extension vertex non-adjacency via 5-vertex paths
          -- u₁'-u₂': path [u₂', u₂, v₀, u₁, u₁']
          have path_nodup5 : ∀ (a b c d e : Fin n),
              a ≠ b → a ≠ c → a ≠ d → a ≠ e →
              b ≠ c → b ≠ d → b ≠ e →
              c ≠ d → c ≠ e → d ≠ e → [a, b, c, d, e].Nodup := by
            intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde
            simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
              not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
            exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩
          have path_edges5 : ∀ (a b c d e : Fin n),
              adj a b = 1 → adj b c = 1 → adj c d = 1 → adj d e = 1 →
              ∀ k, (hk : k + 1 < [a, b, c, d, e].length) →
                adj ([a, b, c, d, e].get ⟨k, by omega⟩) ([a, b, c, d, e].get ⟨k + 1, hk⟩) = 1 := by
            intro a b c d e h₁ h₂ h₃ h₄ k hk
            have : k + 1 < 5 := by simpa using hk
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
            rcases this with rfl | rfl | rfl | rfl <;> assumption
          -- u₁' ≠ u₂': if equal, then adj u₂ u₁' = adj u₂ u₂' = 1.
          -- By hu₁_only, adj u₁ x = 1 → x = v₀ ∨ x = u₁'. Not directly useful.
          -- Use: if u₁' = u₂', then path [u₁, u₁', u₂, v₀] has u₁'=u₂' adj to u₂ (from hu₂'_adj).
          -- Actually simpler: hu₁'_u₂_nonadj says adj u₁' u₂ = 0.
          -- If u₁' = u₂', then adj u₂ u₂' = 1 → adj u₂ u₁' = 1 → (adj_comm) adj u₁' u₂ = 1.
          -- But hu₁'_u₂_nonadj says adj u₁' u₂ = 0. Contradiction.
          have hu₁'_ne_u₂' : u₁' ≠ u₂' := by
            intro h; rw [h] at hu₁'_u₂_nonadj
            have : adj u₂' u₂ = 1 := hu₂'_u₂
            linarith [adj_comm u₂' u₂]
          -- u₁' ≠ u₃': similarly
          have hu₁'_ne_u₃' : u₁' ≠ u₃' := by
            intro h; rw [h] at hu₁'_u₃_nonadj
            have : adj u₃' u₃ = 1 := hu₃'_u₃
            linarith [adj_comm u₃' u₃]
          -- u₂' ≠ u₃'
          have hu₂'_ne_u₃' : u₂' ≠ u₃' := by
            intro h; rw [h] at hu₂'_u₃_nonadj
            have : adj u₃' u₃ = 1 := hu₃'_u₃
            linarith [adj_comm u₃' u₃]
          -- u₁'-u₂' non-adj: path [u₂', u₂, v₀, u₁, u₁']
          have hu₁'_u₂'_nonadj : adj u₁' u₂' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₂', u₂, v₀, u₁, u₁'] (by simp)
              (path_nodup5 u₂' u₂ v₀ u₁ u₁'
                hu₂'_ne_u₂ hu₂'_ne_v₀ hu₂'_ne_u₁ hu₁'_ne_u₂'.symm
                hu₂_ne_v₀ hu₁₂.symm hu₁'_ne_u₂.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges5 u₂' u₂ v₀ u₁ u₁' hu₂'_u₂
                (adj_comm u₂ v₀ |>.trans hu₂_adj) hu₁_adj hu₁'_adj)
          -- u₁'-u₃' non-adj: path [u₃', u₃, v₀, u₁, u₁']
          have hu₁'_u₃'_nonadj : adj u₁' u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₁, u₁'] (by simp)
              (path_nodup5 u₃' u₃ v₀ u₁ u₁'
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₁ hu₁'_ne_u₃'.symm
                hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁'_ne_u₃.symm
                hu₁_ne_v₀.symm hu₁'_ne_v₀.symm hu₁'_ne_u₁.symm)
              (path_edges5 u₃' u₃ v₀ u₁ u₁' hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₁_adj hu₁'_adj)
          -- u₂'-u₃' non-adj: path [u₃', u₃, v₀, u₂, u₂']
          have hu₂'_u₃'_nonadj : adj u₂' u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₂, u₂'] (by simp)
              (path_nodup5 u₃' u₃ v₀ u₂ u₂'
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₂ hu₂'_ne_u₃'.symm
                hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂'_ne_u₃.symm
                hu₂_ne_v₀.symm hu₂'_ne_v₀.symm hu₂'_ne_u₂.symm)
              (path_edges5 u₃' u₃ v₀ u₂ u₂' hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₂_adj hu₂'_adj)
          -- u₁-u₃' non-adj: use hu₃_only. adj u₃ u₁ = 0 means u₁ is not adj to u₃.
          -- But we need u₁ not adj to u₃'. Use path [u₃', u₃, v₀, u₁].
          have hu₁_u₃'_nonadj : adj u₁ u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₁] (by simp)
              (path_nodup4 u₃' u₃ v₀ u₁
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₁
                hu₃_ne_v₀ hu₁_ne_u₃.symm hu₁_ne_v₀.symm)
              (path_edges4 u₃' u₃ v₀ u₁ hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₁_adj)
          -- u₂-u₁' non-adj: already have hu₁'_u₂_nonadj : adj u₁' u₂ = 0
          -- u₁-u₂' non-adj: already have hu₂'_u₁_nonadj : adj u₂' u₁ = 0
          -- u₂-u₃' non-adj: path [u₃', u₃, v₀, u₂]
          have hu₂_u₃'_nonadj : adj u₂ u₃' = 0 :=
            acyclic_path_nonadj adj hsymm h01 h_acyclic [u₃', u₃, v₀, u₂] (by simp)
              (path_nodup4 u₃' u₃ v₀ u₂
                hu₃'_ne_u₃ hu₃'_ne_v₀ hu₃'_ne_u₂
                hu₃_ne_v₀ hu₂_ne_u₃.symm hu₂_ne_v₀.symm)
              (path_edges4 u₃' u₃ v₀ u₂ hu₃'_u₃
                (adj_comm u₃ v₀ |>.trans hu₃_adj) hu₂_adj)
          -- u₃-u₁' non-adj: already have hu₁'_u₃_nonadj : adj u₁' u₃ = 0
          -- u₃-u₂' non-adj: already have hu₂'_u₃_nonadj : adj u₂' u₃ = 0
          -- Construct the embedding φ : Fin 7 ↪ Fin n
          -- Map: 0 → v₀, 1 → u₁, 2 → u₁', 3 → u₂, 4 → u₂', 5 → u₃, 6 → u₃'
          -- etilde6Adj edges: 0-1, 1-2, 0-3, 3-4, 0-5, 5-6
          let φ_fun : Fin 7 → Fin n := fun i =>
            match i with
            | ⟨0, _⟩ => v₀  | ⟨1, _⟩ => u₁  | ⟨2, _⟩ => u₁'
            | ⟨3, _⟩ => u₂  | ⟨4, _⟩ => u₂' | ⟨5, _⟩ => u₃ | ⟨6, _⟩ => u₃'
          have φ_inj : Function.Injective φ_fun := by
            intro i j hij; simp only [φ_fun] at hij
            fin_cases i <;> fin_cases j <;>
              first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
          let φ : Fin 7 ↪ Fin n := ⟨φ_fun, φ_inj⟩
          -- Adjacency verification: etilde6Adj i j = adj (φ i) (φ j)
          have hembed : ∀ i j, etilde6Adj i j = adj (φ i) (φ j) := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp only [etilde6Adj, φ, φ_fun] <;> norm_num <;>
              linarith [hdiag v₀, hdiag u₁, hdiag u₁', hdiag u₂, hdiag u₂',
                        hdiag u₃, hdiag u₃',
                        adj_comm v₀ u₁, adj_comm v₀ u₂, adj_comm v₀ u₃,
                        adj_comm u₁ u₁', adj_comm u₂ u₂', adj_comm u₃ u₃',
                        adj_comm u₁ u₂, adj_comm u₁ u₃, adj_comm u₂ u₃,
                        adj_comm v₀ u₁', adj_comm v₀ u₂', adj_comm v₀ u₃',
                        adj_comm u₁' u₂, adj_comm u₁' u₃, adj_comm u₂' u₁,
                        adj_comm u₂' u₃, adj_comm u₃' u₁, adj_comm u₃' u₂,
                        adj_comm u₁' u₂', adj_comm u₁' u₃', adj_comm u₂' u₃',
                        adj_comm u₁ u₃', adj_comm u₂ u₃']
          exact subgraph_infinite_type_transfer φ adj etilde6Adj hsymm
            (fun v h => by linarith [hdiag v]) hembed etilde6_not_finite_type

/-- A connected acyclic simple graph with all degrees ≤ 3, at least one degree-3 vertex,
    and non-positive-definite Cartan form has infinite representation type.

    The proof proceeds by case analysis on the branch point structure:
    - **Adjacent branch points**: Embed D̃₅ (6 vertices from 2 adjacent degree-3 vertices
      plus their 4 other neighbors).
    - **Single branch point (T(p,q,r))**: The tree's non-positive-definiteness forces it
      outside ADE, enabling embedding of Ẽ₆, Ẽ₇, or T(1,2,5).
    - **Non-adjacent branch points**: Extended Dynkin D̃_n structure or contains forbidden
      subgraph from a well-chosen branch point. -/
theorem acyclic_branch_not_posdef_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (h_has_branch : ∃ v, vertexDegree adj v = 3)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)) :
    ¬ IsFiniteTypeQuiver n adj := by
  obtain ⟨v₀, hv₀⟩ := h_has_branch
  -- Does v₀ have an adjacent branch point?
  by_cases h_adj_branch : ∃ u, adj v₀ u = 1 ∧ vertexDegree adj u = 3
  · -- Case 1: Adjacent branch points → D̃₅ embedding
    obtain ⟨w, hw_adj, hw_deg⟩ := h_adj_branch
    exact adjacent_branches_infinite_type adj hsymm hdiag h01 h_acyclic v₀ w hv₀ hw_deg hw_adj
  · push_neg at h_adj_branch
    -- All neighbors of v₀ have degree < 3 (so ≤ 2, meaning no adjacent branch)
    have h_no_adj : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3 := by
      intro u hu
      have := h_adj_branch u hu
      have := h_deg u; omega
    -- Is v₀ the only branch point?
    by_cases h_unique : ∀ w, vertexDegree adj w = 3 → w = v₀
    · -- Case 2: Single branch point → T(p,q,r) analysis
      exact single_branch_not_posdef_infinite_type adj hn hsymm hdiag h01 hconn
        h_acyclic h_deg v₀ hv₀ h_unique h_not_posdef
    · -- Case 3: ≥ 2 non-adjacent branch points
      push_neg at h_unique
      obtain ⟨w, hw_deg, hw_ne⟩ := h_unique
      exact non_adjacent_branches_infinite_type adj hn hsymm hdiag h01 hconn
        h_acyclic h_deg v₀ w hv₀ hw_deg hw_ne h_no_adj

/-- A connected simple graph whose Cartan form (2I - adj) is not positive definite
    has infinite representation type.

    This is proved by showing the graph contains one of the forbidden subgraphs:
    - Graphs containing cycles → `cycle_not_finite_type` + subgraph transfer
    - Trees with degree ≥ 4 → `degree_ge_4_infinite_type`
    - Trees with ≥ 2 branch points → D̃₅ subgraph → `d5tilde_not_finite_type`
    - T_{p,q,r} with p ≥ 2 → Ẽ₆ subgraph → `etilde6_not_finite_type`
    - T_{1,q,r} with q ≥ 3 → Ẽ₇ subgraph → `etilde7_not_finite_type`
    - T_{1,2,r} with r ≥ 5 → T_{1,2,5} subgraph → `t125_not_finite_type` -/
theorem not_posdef_infinite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Case 1: ∃ vertex with degree ≥ 4
  by_cases h_deg4 : ∃ v, 4 ≤ vertexDegree adj v
  · obtain ⟨v, hv⟩ := h_deg4
    exact degree_ge_4_infinite_type adj hsymm hdiag h01 v hv
  · push_neg at h_deg4
    -- All degrees ≤ 3.
    -- Define acyclicity predicate
    set HasCycle := ∃ (cycle : List (Fin n)) (_ : 3 ≤ cycle.length),
        cycle.Nodup ∧
        (∀ k, (h : k + 1 < cycle.length) →
          adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) ∧
        adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
          (cycle.get ⟨0, by omega⟩) = 1 with HasCycle_def
    -- Case 2: graph contains a cycle
    by_cases h_cycle : HasCycle
    · obtain ⟨cycle, hlen, hnodup, hedges, hclose⟩ := h_cycle
      have hclose' : adj (cycle.get ⟨cycle.length - 1, by omega⟩)
          (cycle.get ⟨0, by omega⟩) = 1 := by
        rwa [List.getLast_eq_getElem] at hclose
      exact graph_with_list_cycle_infinite_type adj hsymm hdiag h01
        cycle hlen hnodup hedges hclose'
    · -- No cycle: graph is acyclic (a tree since it's connected)
      have h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
          (∀ k, (h : k + 1 < cycle.length) →
            adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
          adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
            (cycle.get ⟨0, by omega⟩) ≠ 1 := by
        intro cycle hclen hnodup hedges hclose
        exact h_cycle ⟨cycle, hclen, hnodup, hedges, hclose⟩
      -- Case 3: all degrees ≤ 2 → path → positive definite → contradiction
      by_cases h_has_branch : ∃ v, vertexDegree adj v = 3
      · exact acyclic_branch_not_posdef_infinite_type adj hn hsymm hdiag h01 hconn
          h_acyclic h_deg4 h_has_branch h_not_posdef
      · -- All degrees ≤ 2
        push_neg at h_has_branch
        have h_deg_lt_3 : ∀ v, vertexDegree adj v < 3 := by
          intro v
          have h3 := h_deg4 v
          have hne3 := h_has_branch v
          omega
        exact absurd (acyclic_deg_le_2_posdef adj hn hsymm hdiag h01 hconn
          h_acyclic h_deg_lt_3) h_not_posdef

/-- Every non-ADE connected simple graph on n ≥ 1 vertices has infinite representation type.

    **Proof strategy**: By the Dynkin classification theorem, a connected simple graph is
    a Dynkin diagram iff it is graph-isomorphic to one of A_n, D_n, E₆, E₇, E₈.
    Since our graph is not ADE, it is not a Dynkin diagram, so its Cartan form is not
    positive definite. Then `not_posdef_infinite_type` gives infinite representation type. -/
theorem non_ade_graph_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_ade : ¬ ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Step 1: ¬ADE → ¬IsDynkinDiagram (by Dynkin classification theorem)
  have h_not_dynkin : ¬ IsDynkinDiagram n adj := by
    intro hD
    exact h_not_ade ((Theorem_Dynkin_classification n adj hn).mp hD)
  -- Step 2: Since we have symmetry, 0-diagonal, 0-1 entries, and connectivity,
  -- the only failing condition of IsDynkinDiagram is positive definiteness.
  have h_not_posdef : ¬ ∀ x : Fin n → ℤ, x ≠ 0 →
      0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
    intro hpos
    exact h_not_dynkin ⟨hsymm, hdiag, h01, hconn, hpos⟩
  -- Step 3: Apply the non-positive-definite → infinite type theorem
  exact not_posdef_infinite_type adj hn hsymm hdiag h01 hconn h_not_posdef

end Etingof
