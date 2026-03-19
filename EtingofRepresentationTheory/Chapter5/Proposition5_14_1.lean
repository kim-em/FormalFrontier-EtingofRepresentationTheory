import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2
import EtingofRepresentationTheory.Chapter5.Definition5_14_2

/-!
# Proposition 5.14.1: Kostka Decomposition

For partitions λ, μ of n:
- Hom_{S_n}(U_λ, V_μ) = 0 if μ < λ (dominance order)
- dim Hom_{S_n}(U_λ, V_λ) = 1

Thus U_λ = ⊕_{μ ≥ λ} K_{μλ} · V_μ where K_{μλ} are the Kostka numbers.

Here U_λ = Ind_{S_{λ₁} × ... × S_{λ_p}}^{S_n} (trivial) is the permutation
module associated to partition λ.

## Mathlib correspondence

Requires Specht modules (Theorem 5.12.2), Young tableaux, and Kostka numbers.
The dominance order on partitions is defined locally as Mathlib does not have it.
The permutation module is defined as the free ℂ-module on left cosets S_n/S_λ.
-/

namespace Etingof

/-! ## Dominance order on partitions -/

/-- The dominance order on partitions of n: μ dominates λ (μ ≥ λ) if for all k,
the sum of the first k parts of μ (in non-increasing order) is at least the sum
of the first k parts of λ. -/
def Nat.Partition.Dominates {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  ∀ k : ℕ, (la.sortedParts.take k).sum ≤ (mu.sortedParts.take k).sum

/-- Strict dominance: μ strictly dominates λ when μ dominates λ and μ ≠ λ. -/
def Nat.Partition.StrictDominates {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  Nat.Partition.Dominates mu la ∧ mu ≠ la

/-! ## Permutation module -/

/-- The permutation module U_λ = ℂ[S_n/S_λ], the free ℂ-module on left cosets of the
Young subgroup (row subgroup) S_λ = S_{λ₁} × ... × S_{λ_p}.
S_n acts by left multiplication on cosets.
(Etingof, Section 5.14) -/
noncomputable abbrev PermutationModule (n : ℕ) (la : Nat.Partition n) :=
  (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) →₀ ℂ

/-- The ℂ[S_n]-module structure on the permutation module U_λ, where σ ∈ S_n acts
by left multiplication on cosets: σ · (gS_λ) = (σg)S_λ, extended linearly. -/
noncomputable instance PermutationModule.instModule (n : ℕ) (la : Nat.Partition n) :
    Module (SymGroupAlgebra n) (PermutationModule n la) :=
  Module.compHom _ (Representation.ofMulAction ℂ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ RowSubgroup n la)).asAlgebraHom.toRingHom

/-! ## Helper lemmas for the proof -/

noncomputable section
set_option linter.style.openClassical false in
open scoped Classical

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q (n : ℕ) (la : Nat.Partition n) := G' n ⧸ RowSubgroup n la

/-- The SMul on PermutationModule unfolds to the representation action. -/
private lemma permMod_smul_eq (n : ℕ) (la : Nat.Partition n)
    (a : SymGroupAlgebra n) (x : PermutationModule n la) :
    a • x = (Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom a x := rfl

/-- A group element acts on a Finsupp basis element by permuting the coset index. -/
private lemma of_smul_single (n : ℕ) (la : Nat.Partition n)
    (g : G' n) (q : Q n la) (c : ℂ) :
    (MonoidAlgebra.of ℂ _ g : SymGroupAlgebra n) • (Finsupp.single q c : PermutationModule n la) =
    Finsupp.single (g • q) c := by
  simp [permMod_smul_eq, Representation.ofMulAction_single]

/-- Elements of the row subgroup fix the identity coset. -/
private lemma rowSubgroup_fixes_identity (n : ℕ) (la : Nat.Partition n)
    (p : G' n) (hp : p ∈ RowSubgroup n la) :
    (p • (QuotientGroup.mk 1 : Q n la)) = QuotientGroup.mk 1 := by
  change QuotientGroup.mk (p * 1) = QuotientGroup.mk 1
  rw [mul_one, QuotientGroup.eq]
  simpa using (RowSubgroup n la).inv_mem hp

/-- The PermutationModule is generated (as a SymGroupAlgebra-module) by the identity coset
basis vector. -/
private lemma permMod_cyclic (n : ℕ) (la : Nat.Partition n) :
    Submodule.span (SymGroupAlgebra n)
      {(Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) : PermutationModule n la)} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
  | single q c =>
    rw [Submodule.mem_span_singleton]
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    refine ⟨Finsupp.single σ c, ?_⟩
    rw [permMod_smul_eq]
    simp [Representation.asAlgebraHom_single, Representation.ofMulAction_single, mul_one,
      show σ • (QuotientGroup.mk 1 : Q n la) = QuotientGroup.mk σ from by
        change QuotientGroup.mk (σ * 1) = QuotientGroup.mk σ; rw [mul_one]]

/-- The RowSymmetrizer of la annihilates any element of SpechtModule mu
when mu does not dominate la. -/
private lemma rowSymmetrizer_annihilates_specht (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ Nat.Partition.Dominates mu la)
    (v : SymGroupAlgebra n) (hv : v ∈ SpechtModule n mu) :
    RowSymmetrizer n la * v = 0 := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hv
  rw [show v = x • YoungSymmetrizer n mu from hx.symm]
  change RowSymmetrizer n la * (x * YoungSymmetrizer n mu) = 0
  simp only [YoungSymmetrizer]
  rw [show RowSymmetrizer n la * (x * (RowSymmetrizer n mu * ColumnAntisymmetrizer n mu)) =
    RowSymmetrizer n la * (x * RowSymmetrizer n mu) * ColumnAntisymmetrizer n mu
    from by simp only [mul_assoc]]
  exact Lemma5_13_2_general n la mu h _

/-! ## Left action of row group on Young symmetrizer -/

/-- Left multiplication by a row group element fixes the Young symmetrizer:
of(p) * c_la = c_la for p in P_la. -/
private lemma of_row_mul_youngSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (p : G' n) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ _ p * YoungSymmetrizer n la = YoungSymmetrizer n la := by
  simp only [YoungSymmetrizer]
  rw [← mul_assoc, of_row_mul_RowSymmetrizer p hp]

/-- The product of(g) * c_la depends only on the coset of g modulo P_la. -/
private lemma of_mul_cla_coset_indep (n : ℕ) (la : Nat.Partition n)
    (g g' : G' n) (h : (QuotientGroup.mk g : Q n la) = QuotientGroup.mk g') :
    MonoidAlgebra.of ℂ (G' n) g * YoungSymmetrizer n la =
    MonoidAlgebra.of ℂ (G' n) g' * YoungSymmetrizer n la := by
  rw [QuotientGroup.eq] at h
  -- h : g⁻¹ * g' ∈ RowSubgroup, need g'⁻¹ * g ∈ RowSubgroup
  have h' : g'⁻¹ * g ∈ RowSubgroup n la := by
    have := (RowSubgroup n la).inv_mem h; simp [mul_inv_rev] at this; exact this
  have hof : MonoidAlgebra.of ℂ (G' n) g =
      MonoidAlgebra.of ℂ (G' n) g' * MonoidAlgebra.of ℂ (G' n) (g'⁻¹ * g) := by
    rw [← (MonoidAlgebra.of ℂ (G' n)).map_mul]; congr 1; group
  rw [hof, mul_assoc, of_row_mul_youngSymmetrizer n la _ h']

/-- Any P_la-fixed element of V_la is a scalar multiple of c_la. -/
private lemma pla_fixed_is_scalar_of_cla (n : ℕ) (la : Nat.Partition n)
    (v : ↥(SpechtModule n la))
    (h_fix : ∀ p ∈ RowSubgroup n la,
      (MonoidAlgebra.of ℂ (G' n) p : SymGroupAlgebra n) • v = v) :
    ∃ c : ℂ, (v : SymGroupAlgebra n) = c • YoungSymmetrizer n la := by
  classical
  have h_fix_val : ∀ p ∈ RowSubgroup n la,
      MonoidAlgebra.of ℂ (G' n) p * (v : SymGroupAlgebra n) = (v : SymGroupAlgebra n) :=
    fun p hp => congrArg Subtype.val (h_fix p hp)
  have h_row_sym : RowSymmetrizer n la * (v : SymGroupAlgebra n) =
      (Fintype.card (RowSubgroup n la) : ℂ) • (v : SymGroupAlgebra n) := by
    simp only [RowSymmetrizer, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => h_fix_val p.val p.prop)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp v.prop
  obtain ⟨ℓ, hℓ⟩ := Etingof.Lemma5_13_1 n la
  have h_sandwich : RowSymmetrizer n la * (v : SymGroupAlgebra n) =
      ℓ (x * RowSymmetrizer n la) • YoungSymmetrizer n la := by
    rw [show (v : SymGroupAlgebra n) = x * YoungSymmetrizer n la from hx.symm]
    simp only [YoungSymmetrizer]
    rw [show RowSymmetrizer n la * (x * (RowSymmetrizer n la * ColumnAntisymmetrizer n la)) =
      RowSymmetrizer n la * (x * RowSymmetrizer n la) * ColumnAntisymmetrizer n la
      from by simp only [mul_assoc]]
    exact hℓ _
  have h_card_ne : (Fintype.card (RowSubgroup n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [h_row_sym] at h_sandwich
  refine ⟨ℓ (x * RowSymmetrizer n la) * (Fintype.card (RowSubgroup n la) : ℂ)⁻¹, ?_⟩
  rw [mul_comm, ← smul_smul, ← h_sandwich, smul_smul, inv_mul_cancel₀ h_card_ne, one_smul]

end

/-! ## Proposition 5.14.1 -/

/-- Hom_{S_n}(U_λ, V_μ) = 0 when λ strictly dominates μ (i.e., μ < λ).
Equivalently, there are no nonzero S_n-equivariant maps from U_λ to V_μ.
(Etingof Proposition 5.14.1, vanishing part) -/
theorem Proposition5_14_1_vanishing
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : Nat.Partition.StrictDominates la mu) :
    ∀ f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n mu), f = 0 := by
  classical
  have h_not_dom : ¬ Nat.Partition.Dominates mu la := by
    intro hmu
    exact hdom.2 (Nat.Partition.Dominates.antisymm hdom.1 hmu)
  intro f
  set e : PermutationModule n la := Finsupp.single (QuotientGroup.mk 1) 1 with he_def
  set v₀ := f e with hv₀_def
  -- f = 0 iff v₀ = 0, because PermutationModule is cyclic generated by e
  suffices hv₀_zero : v₀ = 0 by
    apply LinearMap.ext; intro x
    have hx : x ∈ Submodule.span (SymGroupAlgebra n) {e} :=
      permMod_cyclic n la ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change f (a • e) = 0
    rw [f.map_smul]
    have : f e = (0 : ↥(SpechtModule n mu)) := by rw [← hv₀_def]; exact hv₀_zero
    rw [this, smul_zero]
  -- For p ∈ RowSubgroup, (of p) • v₀ = v₀
  have h_inv : ∀ p ∈ RowSubgroup n la,
      (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) • v₀ = v₀ := by
    intro p hp
    have h_fix : (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) • e = e := by
      rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
    change (MonoidAlgebra.of ℂ _ p) • (f e) = f e
    rw [← f.map_smul, h_fix]
  -- Coerce: (of p) * v₀.val = v₀.val
  have h_inv_val : ∀ p ∈ RowSubgroup n la,
      MonoidAlgebra.of ℂ (G' n) p * (v₀ : SymGroupAlgebra n) = (v₀ : SymGroupAlgebra n) :=
    fun p hp => congrArg Subtype.val (h_inv p hp)
  -- RowSymmetrizer * v₀.val = card • v₀.val
  have h_row_sym : RowSymmetrizer n la * (v₀ : SymGroupAlgebra n) =
      (Fintype.card (RowSubgroup n la) : ℂ) • (v₀ : SymGroupAlgebra n) := by
    simp only [RowSymmetrizer, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => h_inv_val p.val p.prop)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  -- RowSymmetrizer * v₀.val = 0
  have h_annihilate : RowSymmetrizer n la * (v₀ : SymGroupAlgebra n) = 0 :=
    rowSymmetrizer_annihilates_specht n la mu h_not_dom (v₀ : SymGroupAlgebra n) v₀.prop
  -- card • v₀.val = 0 and card ≠ 0, so v₀.val = 0
  have h_card_ne_zero : (Fintype.card (RowSubgroup n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hv₀_val_zero : (v₀ : SymGroupAlgebra n) = 0 := by
    rw [h_row_sym] at h_annihilate
    exact (smul_eq_zero.mp h_annihilate).resolve_left h_card_ne_zero
  exact Subtype.ext hv₀_val_zero

/-- dim Hom_{S_n}(U_λ, V_λ) = 1. The space of S_n-equivariant maps from the
permutation module U_λ to the Specht module V_λ is one-dimensional.
(Etingof Proposition 5.14.1, diagonal part) -/
theorem Proposition5_14_1_diagonal
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la)) = 1 := by
  classical
  set e : PermutationModule n la := Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ)
  set cla : ↥(SpechtModule n la) := ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩
  -- Step 1: Any equivariant map f is determined by f(e)
  have hf_det : ∀ f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la),
      f e = 0 → f = 0 := by
    intro f hfe
    ext x
    have hx : x ∈ Submodule.span (SymGroupAlgebra n) {e} :=
      permMod_cyclic n la ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [f.map_smul, hfe]
  -- Step 2: f(e) is P_la-fixed, hence f(e).val is a scalar multiple of c_la
  have hf_scalar : ∀ f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la),
      ∃ c : ℂ, (f e : SymGroupAlgebra n) = c • YoungSymmetrizer n la := by
    intro f
    apply pla_fixed_is_scalar_of_cla
    intro p hp
    rw [← f.map_smul]; congr 1
    rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
  -- Step 3: Any two maps f, g satisfy g = α • f for some scalar
  -- (both f(e).val and g(e).val are scalar multiples of c_la,
  --  so they differ by a scalar, and since U_la is cyclic, the maps differ by that scalar)
  -- Step 4: Construct a nonzero equivariant map (the canonical map)
  -- and show everything is a scalar multiple
  sorry

end Etingof
