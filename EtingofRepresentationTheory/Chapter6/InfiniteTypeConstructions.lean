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

/-- The degree of a vertex in a simple graph given by its adjacency matrix. -/
def vertexDegree (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => adj v w = 1)).card

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
    (v : Fin n) (hv : 4 ≤ vertexDegree n adj v) :
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

end Etingof
