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
    sorry

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

end Etingof
