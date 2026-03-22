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

/-- Generalized vanishing: Hom_{S_n}(U_λ, V_μ) = 0 when μ does not dominate λ.
This is strictly more general than `Proposition5_14_1_vanishing` which requires
λ to strictly dominate μ; here we only need ¬(μ dominates λ), which also covers
the case where λ and μ are incomparable in the dominance order. -/
theorem Proposition5_14_1_vanishing_general
    (n : ℕ) (la mu : Nat.Partition n)
    (h_not_dom : ¬ Nat.Partition.Dominates mu la) :
    ∀ f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n mu), f = 0 := by
  classical
  intro f
  set e : PermutationModule n la := Finsupp.single (QuotientGroup.mk 1) 1 with he_def
  set v₀ := f e with hv₀_def
  suffices hv₀_zero : v₀ = 0 by
    apply LinearMap.ext; intro x
    have hx : x ∈ Submodule.span (SymGroupAlgebra n) {e} :=
      permMod_cyclic n la ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change f (a • e) = 0
    rw [f.map_smul]
    have : f e = (0 : ↥(SpechtModule n mu)) := by rw [← hv₀_def]; exact hv₀_zero
    rw [this, smul_zero]
  have h_inv : ∀ p ∈ RowSubgroup n la,
      (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) • v₀ = v₀ := by
    intro p hp
    have h_fix : (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) • e = e := by
      rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
    change (MonoidAlgebra.of ℂ _ p) • (f e) = f e
    rw [← f.map_smul, h_fix]
  have h_inv_val : ∀ p ∈ RowSubgroup n la,
      MonoidAlgebra.of ℂ (G' n) p * (v₀ : SymGroupAlgebra n) = (v₀ : SymGroupAlgebra n) :=
    fun p hp => congrArg Subtype.val (h_inv p hp)
  have h_row_sym : RowSymmetrizer n la * (v₀ : SymGroupAlgebra n) =
      (Fintype.card (RowSubgroup n la) : ℂ) • (v₀ : SymGroupAlgebra n) := by
    simp only [RowSymmetrizer, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => h_inv_val p.val p.prop)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have h_annihilate : RowSymmetrizer n la * (v₀ : SymGroupAlgebra n) = 0 :=
    rowSymmetrizer_annihilates_specht n la mu h_not_dom (v₀ : SymGroupAlgebra n) v₀.prop
  have h_card_ne_zero : (Fintype.card (RowSubgroup n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hv₀_val_zero : (v₀ : SymGroupAlgebra n) = 0 := by
    rw [h_row_sym] at h_annihilate
    exact (smul_eq_zero.mp h_annihilate).resolve_left h_card_ne_zero
  exact Subtype.ext hv₀_val_zero

noncomputable section
set_option linter.style.openClassical false in
open scoped Classical

/-- Left multiplication by a row subgroup element fixes the Young symmetrizer. -/
private lemma row_mul_youngSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (p : G' n) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ _ p * YoungSymmetrizer n la = YoungSymmetrizer n la := by
  simp only [YoungSymmetrizer, ← mul_assoc]
  rw [of_row_mul_RowSymmetrizer p hp]

/-- The Young symmetrizer c_λ is nonzero. -/
private lemma youngSymmetrizer_ne_zero (n : ℕ) (la : Nat.Partition n) :
    YoungSymmetrizer n la ≠ 0 := by
  haveI := Theorem5_12_2_irreducible n la
  intro h
  have hbot : SpechtModule n la = ⊥ := Submodule.span_singleton_eq_bot.mpr h
  exact (isSimpleModule_iff_isAtom.mp ‹_›).1 hbot

/-- of(g) * c_λ ≠ 0 since of(g) is a unit and c_λ ≠ 0. -/
private lemma of_mul_youngSymmetrizer_ne_zero (n : ℕ) (la : Nat.Partition n) (g : G' n) :
    MonoidAlgebra.of ℂ _ g * YoungSymmetrizer n la ≠ 0 := by
  intro h
  apply youngSymmetrizer_ne_zero n la
  have : MonoidAlgebra.of ℂ _ g⁻¹ * (MonoidAlgebra.of ℂ _ g * YoungSymmetrizer n la) =
      YoungSymmetrizer n la := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [h, mul_zero] at this
  exact this.symm

/-- Any row-invariant element of V_λ is a scalar multiple of c_λ. -/
private lemma row_invariant_is_scalar_of_youngSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (v : SymGroupAlgebra n) (hv : v ∈ SpechtModule n la)
    (hinv : ∀ p ∈ RowSubgroup n la,
      MonoidAlgebra.of ℂ (G' n) p * v = v) :
    ∃ c : ℂ, v = c • YoungSymmetrizer n la := by
  classical
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hv
  -- v = x * c_λ (since span is smul-span in the algebra = left multiplication)
  change x • YoungSymmetrizer n la = v at hx
  rw [hx.symm]
  -- Sum of (of p) * v over p ∈ P_λ gives a_λ * v = |P_λ| * v
  have h_sum : RowSymmetrizer n la * (x * YoungSymmetrizer n la) =
      (Fintype.card (RowSubgroup n la) : ℂ) • (x * YoungSymmetrizer n la) := by
    have key : ∀ p : RowSubgroup n la,
        (MonoidAlgebra.of ℂ (G' n) p.val) * (x * YoungSymmetrizer n la) =
         x * YoungSymmetrizer n la := by
      intro p; have h := hinv p.val p.prop; rwa [← hx] at h
    simp only [RowSymmetrizer, Finset.sum_mul, key, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
  -- By Lemma 5.13.1: a_λ * (x * c_λ) = a_λ * x * a_λ * b_λ = ℓ(x * a_λ) • c_λ
  obtain ⟨ℓ, hℓ⟩ := Etingof.Lemma5_13_1 n la
  have h_sandwich : RowSymmetrizer n la * (x * YoungSymmetrizer n la) =
      ℓ (x * RowSymmetrizer n la) • YoungSymmetrizer n la := by
    conv_lhs => rw [YoungSymmetrizer, ← mul_assoc x, ← mul_assoc]
    exact hℓ (x * RowSymmetrizer n la)
  have h_card_ne_zero : (Fintype.card (RowSubgroup n la) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [h_sandwich] at h_sum
  -- h_sum : ℓ(x * a_λ) • c_λ = |P_λ| • (x * c_λ)
  -- Multiply both sides by |P_λ|⁻¹ to isolate x * c_λ
  replace h_sum := congr_arg (fun v => (Fintype.card (RowSubgroup n la) : ℂ)⁻¹ • v) h_sum.symm
  simp only [smul_smul, inv_mul_cancel₀ h_card_ne_zero, one_smul] at h_sum
  -- h_sum : x * c_λ = (|P_λ|⁻¹ * ℓ(x * a_λ)) • c_λ
  exact ⟨_, h_sum⟩

/-- Coset representative equivariance: of(out(σ·q)) * c_λ = of(σ) * of(out q) * c_λ. -/
private lemma coset_rep_equivariance (n : ℕ) (la : Nat.Partition n)
    (σ : G' n) (q : Q n la) :
    MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) * YoungSymmetrizer n la =
    MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) *
      YoungSymmetrizer n la := by
  -- out(σ·q) and σ * out(q) are in the same P_λ-coset
  have h_eq : QuotientGroup.mk (Quotient.out (σ • q)) =
      (QuotientGroup.mk (σ * Quotient.out q) : Q n la) := by
    rw [QuotientGroup.out_eq']
    change σ • q = QuotientGroup.mk (σ * Quotient.out q)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  -- (σ * out q)⁻¹ * out(σ·q) ∈ P_λ
  have hmem := QuotientGroup.eq.mp h_eq
  -- out(σ·q)⁻¹ * (σ * out q) ∈ P_λ (the inverse)
  have hcoset := hmem
  -- of(σ) * of(out q) * c_λ = of(out(σ·q)) * of(p) * c_λ = of(out(σ·q)) * c_λ
  have key : MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) =
      MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
        MonoidAlgebra.of ℂ _ ((Quotient.out (σ • q))⁻¹ * (σ * Quotient.out q)) := by
    rw [← map_mul, ← map_mul]; congr 1; group
  rw [key, mul_assoc, row_mul_youngSymmetrizer n la _ hcoset]

end

noncomputable section
set_option linter.style.openClassical false in
open scoped Classical

/-- Helper: the image function for the canonical map. -/
private abbrev canonicalHom_v (n : ℕ) (la : Nat.Partition n) (q : Q n la) :
    SymGroupAlgebra n :=
  MonoidAlgebra.of ℂ _ (Quotient.out q) * YoungSymmetrizer n la

/-- The ℂ-linear version of the canonical map, using Finsupp.lift. -/
private noncomputable def canonicalHom_ℂ (n : ℕ) (la : Nat.Partition n) :
    PermutationModule n la →ₗ[ℂ] SymGroupAlgebra n :=
  Finsupp.lift (SymGroupAlgebra n) ℂ (Q n la) (canonicalHom_v n la)

/-- The smul_assoc for PermutationModule: (r • a) • x = r • (a • x). -/
private lemma permMod_smul_assoc (n : ℕ) (la : Nat.Partition n)
    (r : ℂ) (a : SymGroupAlgebra n) (x : PermutationModule n la) :
    (r • a) • x = r • (a • x) := by
  change (Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom (r • a) x =
    r • ((Representation.ofMulAction ℂ (G' n) (Q n la)).asAlgebraHom a x)
  simp only [map_smul, LinearMap.smul_apply]

/-- The canonical equivariant map φ : U_λ → V_λ, sending δ_{gP_λ} to of(out(gP_λ)) * c_λ. -/
private noncomputable def canonicalHom (n : ℕ) (la : Nat.Partition n) :
    PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la) where
  toFun x :=
    ⟨canonicalHom_ℂ n la x, by
      simp only [canonicalHom_ℂ, Finsupp.lift_apply]
      apply Submodule.sum_mem; intro q _
      exact Submodule.smul_of_tower_mem (SpechtModule n la) (x q)
        (Submodule.mem_span_singleton.mpr ⟨MonoidAlgebra.of ℂ _ (Quotient.out q), rfl⟩)⟩
  map_add' x y := Subtype.ext (map_add (canonicalHom_ℂ n la) x y)
  map_smul' a x := by
    refine Subtype.ext ?_
    simp only [RingHom.id_apply, SetLike.val_smul]
    change canonicalHom_ℂ n la (a • x) = a • canonicalHom_ℂ n la x
    induction a using MonoidAlgebra.induction_on with
    | hM σ =>
      induction x using Finsupp.induction_linear with
      | zero => simp [smul_zero, map_zero]
      | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, ← smul_add, ← map_add]
      | single q c =>
        rw [of_smul_single]
        have lift_single : ∀ q' c', canonicalHom_ℂ n la (Finsupp.single q' c') =
            c' • canonicalHom_v n la q' := by
          intro q' c'
          simp [canonicalHom_ℂ, Finsupp.lift_apply, Finsupp.sum_single_index]
        rw [lift_single, lift_single]
        change c • canonicalHom_v n la (σ • q) =
          (MonoidAlgebra.of ℂ _ σ) * (c • canonicalHom_v n la q)
        rw [Algebra.mul_smul_comm]
        congr 1
        simp only [canonicalHom_v]
        rw [coset_rep_equivariance n la σ q, mul_assoc]
    | hadd a b ha hb =>
      rw [add_smul, map_add, ha, hb, add_smul]
    | hsmul r a ha =>
      rw [permMod_smul_assoc, map_smul, ha, smul_assoc]

/-- Evaluation of canonicalHom at the identity coset. -/
private lemma canonicalHom_apply_identity (n : ℕ) (la : Nat.Partition n) :
    (canonicalHom n la (Finsupp.single (QuotientGroup.mk 1) 1) : SymGroupAlgebra n) =
      canonicalHom_v n la (QuotientGroup.mk 1) := by
  change canonicalHom_ℂ n la (Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ)) = _
  simp [canonicalHom_ℂ, Finsupp.lift_apply, Finsupp.sum_single_index]

/-- Any equivariant map agrees everywhere if it agrees on the identity coset generator. -/
private lemma equivariant_map_ext_of_agree_on_e (n : ℕ) (la : Nat.Partition n)
    (f g : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la))
    (h : f (Finsupp.single (QuotientGroup.mk 1) 1) =
         g (Finsupp.single (QuotientGroup.mk 1) 1)) : f = g := by
  apply LinearMap.ext; intro x
  have hx : x ∈ Submodule.span (SymGroupAlgebra n)
      {(Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) : PermutationModule n la)} :=
    permMod_cyclic n la ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, map_smul, h]

/-- Row-invariance of f(e) for any equivariant map. -/
private lemma equivariant_map_row_invariant (n : ℕ) (la : Nat.Partition n)
    (f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la)) :
    ∀ p ∈ RowSubgroup n la,
      MonoidAlgebra.of ℂ (G' n) p *
        (f (Finsupp.single (QuotientGroup.mk 1) 1) : SymGroupAlgebra n) =
        (f (Finsupp.single (QuotientGroup.mk 1) 1) : SymGroupAlgebra n) := by
  intro p hp
  have h_fix : (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) •
      (Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) : PermutationModule n la) =
      Finsupp.single (QuotientGroup.mk (1 : G' n)) (1 : ℂ) := by
    rw [of_smul_single, rowSubgroup_fixes_identity n la p hp]
  exact congrArg Subtype.val
    (show (MonoidAlgebra.of ℂ _ p) • f (Finsupp.single (QuotientGroup.mk 1) 1) =
          f (Finsupp.single (QuotientGroup.mk 1) 1) by rw [← f.map_smul, h_fix])

end

/-- dim Hom_{S_n}(U_λ, V_λ) = 1. The space of S_n-equivariant maps from the
permutation module U_λ to the Specht module V_λ is one-dimensional.
(Etingof Proposition 5.14.1, diagonal part) -/
theorem Proposition5_14_1_diagonal
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la)) = 1 := by
  classical
  set φ := canonicalHom n la
  set e : PermutationModule n la := Finsupp.single (QuotientGroup.mk 1) 1
  have hφe_val := canonicalHom_apply_identity n la
  -- φ(e) ≠ 0
  have hφe_ne : φ e ≠ 0 := by
    intro h
    have h_val := congrArg Subtype.val h
    simp only [Submodule.coe_zero] at h_val
    rw [hφe_val, canonicalHom_v] at h_val
    exact of_mul_youngSymmetrizer_ne_zero n la _ h_val
  -- φ(e).val is a scalar multiple of c_λ
  obtain ⟨c₀, hc₀⟩ := row_invariant_is_scalar_of_youngSymmetrizer n la
    (φ e : SymGroupAlgebra n) (φ e).prop (equivariant_map_row_invariant n la φ)
  have hc₀_ne : c₀ ≠ 0 := by
    intro h; rw [h, zero_smul] at hc₀; exact hφe_ne (Subtype.ext hc₀)
  apply finrank_eq_one (R := ℂ) (v := φ)
  · exact fun h => hφe_ne (by rw [h, LinearMap.zero_apply])
  · intro f
    obtain ⟨c₁, hc₁⟩ := row_invariant_is_scalar_of_youngSymmetrizer n la
      (f e : SymGroupAlgebra n) (f e).prop (equivariant_map_row_invariant n la f)
    -- f(e) = (c₁/c₀) • φ(e) as subtypes
    have h_agree : f e = (c₁ / c₀) • φ e := by
      apply Subtype.ext
      change (f e : SymGroupAlgebra n) = (c₁ / c₀) • (φ e : SymGroupAlgebra n)
      rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ c₁ hc₀_ne]
    refine ⟨c₁ / c₀, ?_⟩
    apply equivariant_map_ext_of_agree_on_e
    rw [h_agree, LinearMap.smul_apply]

end Etingof
