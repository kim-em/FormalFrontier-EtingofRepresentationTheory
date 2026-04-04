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

theorem nilpotentShiftLin_nilpotent (m : ℕ) :
    IsNilpotent (nilpotentShiftLin m) := by
  sorry

theorem nilpotentShiftLin_ker_finrank (m : ℕ) :
    Module.finrank ℂ (LinearMap.ker (nilpotentShiftLin m)) = 1 := by
  sorry

/-! ## Section 2: Nilpotent-invariant complement triviality -/

theorem nilpotent_invariant_compl_trivial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (N : V →ₗ[ℂ] V) (hN : IsNilpotent N)
    (hker : Module.finrank ℂ (LinearMap.ker N) = 1)
    (W₁ W₂ : Submodule ℂ V)
    (hW₁_inv : ∀ x ∈ W₁, N x ∈ W₁)
    (hW₂_inv : ∀ x ∈ W₂, N x ∈ W₂)
    (hcompl : IsCompl W₁ W₂) :
    W₁ = ⊥ ∨ W₂ = ⊥ := by
  sorry

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
