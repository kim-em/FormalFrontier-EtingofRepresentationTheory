import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_theorem

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
    mapLinear := fun {a b} e => by
      obtain ⟨ha, hb⟩ := e.down
      change (Fin (if a.val = 0 then 2 * (m + 1) else m + 1) → ℂ) →ₗ[ℂ]
           (Fin (if b.val = 0 then 2 * (m + 1) else m + 1) → ℂ)
      rw [if_neg ha, if_pos hb]
      exact starEmbedding m a
  }

/-! ## Section 9: Indecomposability of star representations -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
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
    sorry

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

end Etingof
