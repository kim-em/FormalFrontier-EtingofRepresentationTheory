import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Example 5.19.3: Schur Functors for Special Partitions

If λ = (n), then Lλ = SⁿV (symmetric power).
If λ = (1ⁿ), then Lλ = ∧ⁿV (exterior power).
These are irreducible GL(V)-representations (except ∧ⁿV = 0 when n > dim V).

## Mathlib correspondence

Uses `Mathlib.LinearAlgebra.ExteriorAlgebra` and symmetric powers.
-/

open scoped TensorProduct
open Etingof

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The Sₙ-invariant submodule of V⊗ⁿ: tensors fixed by all permutations.
These are the symmetric tensors, i.e., the subspace where σ · x = x for all σ ∈ Sₙ. -/
noncomputable def Etingof.symInvariants :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap - LinearMap.id)

/-- The Sₙ-antisymmetric submodule of V⊗ⁿ: tensors where σ · x = sign(σ) · x
for all σ ∈ Sₙ. These are the alternating tensors. -/
noncomputable def Etingof.symAntisymmetric :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap -
      ((Equiv.Perm.sign σ : ℤ) : k) • LinearMap.id)

namespace Etingof

section SymHelpers

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]
  {n : ℕ}

private lemma mem_symInvariants_iff (x : TensorPower k V n) :
    x ∈ symInvariants k V n ↔ ∀ σ : Equiv.Perm (Fin n), symGroupAction k V n σ x = x := by
  simp only [symInvariants, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]

private lemma mk_symGroupAction_eq (σ : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    SymmetricPower.mk k (Fin n) V (symGroupAction k V n σ x) =
    SymmetricPower.mk k (Fin n) V x := by
  have : (SymmetricPower.mk k (Fin n) V).comp (symGroupAction k V n σ).toLinearMap =
      SymmetricPower.mk k (Fin n) V := by
    ext f
    simp only [LinearMap.comp_apply, LinearMap.coe_compMultilinearMap, Function.comp_apply,
      LinearEquiv.coe_coe, symGroupAction, PiTensorProduct.reindex_tprod]
    show SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i => f (σ.symm i)) =
      SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)
    change (⨂ₛ[k] i, f (σ.symm i)) = ⨂ₛ[k] i, f i
    exact SymmetricPower.tprod_equiv σ.symm f
  exact LinearMap.congr_fun this x

/-- The symmetrization sum: Σ_σ σ · x (without 1/n! factor). -/
private noncomputable def symSum : TensorPower k V n →ₗ[k] TensorPower k V n :=
  ∑ σ : Equiv.Perm (Fin n), (symGroupAction k V n σ).toLinearMap

private lemma symSum_apply (x : TensorPower k V n) :
    symSum x = ∑ σ : Equiv.Perm (Fin n), symGroupAction k V n σ x := by
  simp [symSum, LinearMap.sum_apply]

private lemma symGroupAction_comp (σ τ : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    symGroupAction k V n τ (symGroupAction k V n σ x) =
    symGroupAction k V n (σ.trans τ) x := by
  -- Prove as linear maps are equal on tprod generators
  have h : ((symGroupAction k V n τ).toLinearMap.comp
      (symGroupAction k V n σ).toLinearMap) =
    (symGroupAction k V n (σ.trans τ)).toLinearMap := by
    ext f
    simp [symGroupAction, PiTensorProduct.reindex_tprod]
  exact LinearMap.congr_fun h x

private lemma symSum_symGroupAction (e : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    symSum (symGroupAction k V n e x) = symSum x := by
  simp only [symSum_apply]
  simp_rw [symGroupAction_comp e _ x]
  -- Now goal: ∑ σ, symGroupAction (e.trans σ) x = ∑ σ, symGroupAction σ x
  -- e.trans σ = σ * e in Perm. As σ varies, so does σ * e (right mult bijection).
  -- Use Equiv.mulRight e as the reindexing
  exact Fintype.sum_equiv (Equiv.mulRight e) _ _
    (fun σ => by simp [Equiv.Perm.mul_def, Equiv.trans])

private lemma mk_comp_symSum :
    (SymmetricPower.mk k (Fin n) V).comp symSum =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.coe_compMultilinearMap,
    Function.comp_apply, symSum_apply]
  rw [map_sum]
  simp only [mk_symGroupAction_eq, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma mk_symSum (x : TensorPower k V n) :
    SymmetricPower.mk k (Fin n) V (symSum x) =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V x :=
  LinearMap.congr_fun mk_comp_symSum x

private lemma symSum_of_mem_symInvariants (x : TensorPower k V n)
    (hx : x ∈ symInvariants k V n) :
    symSum x = (Fintype.card (Equiv.Perm (Fin n)) : k) • x := by
  rw [symSum_apply]
  simp only [(mem_symInvariants_iff x).mp hx, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma symSum_mem_symInvariants (x : TensorPower k V n) :
    symSum x ∈ symInvariants k V n := by
  rw [mem_symInvariants_iff]
  intro τ
  simp only [symSum_apply, map_sum]
  simp_rw [symGroupAction_comp _ τ]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp [Equiv.Perm.mul_def])

private lemma symSum_rel :
    ∀ a b, SymmetricPower.Rel k (Fin n) V a b → symSum a = symSum b := by
  intro a b hab
  cases hab with
  | perm e f =>
    -- tprod(f ∘ e) = reindex(e⁻¹)(tprod f), so use symSum_symGroupAction
    have : PiTensorProduct.tprod k (fun i => f (e i)) =
        symGroupAction k V n e⁻¹ (PiTensorProduct.tprod k f) := by
      simp [symGroupAction, PiTensorProduct.reindex_tprod, Equiv.Perm.inv_def]
    rw [this, symSum_symGroupAction]

private lemma ker_mk_le_ker_symSum :
    LinearMap.ker (SymmetricPower.mk k (Fin n) V) ≤ LinearMap.ker symSum := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  -- Build an AddCon from symSum's kernel
  let c : AddCon (⨂[k] (_ : Fin n), V) := AddCon.ker symSum.toAddMonoidHom
  have hle : addConGen (SymmetricPower.Rel k (Fin n) V) ≤ c :=
    AddCon.addConGen_le (fun a b h => symSum_rel a b h)
  -- mk x = 0 means x ≡ 0 mod addConGen(Rel)
  have hrel : (addConGen (SymmetricPower.Rel k (Fin n) V)) x 0 := by
    have hmk : (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) x =
        (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) 0 := by
      change SymmetricPower.mk k (Fin n) V x = SymmetricPower.mk k (Fin n) V 0
      rw [hx, map_zero]
    exact (AddCon.eq _).mp hmk
  -- c x 0 means symSum x = symSum 0 = 0
  have h := hle hrel
  change symSum x = symSum 0 at h
  rwa [map_zero] at h

private lemma perm_card_eq_factorial :
    (Fintype.card (Equiv.Perm (Fin n)) : k) = (n.factorial : k) := by
  simp [Fintype.card_perm]

end SymHelpers

/-- For the partition λ = (n), the Schur functor L_{(n)} equals SⁿV
(the n-th symmetric power). Specifically, the Sₙ-invariant subspace of
V⊗ⁿ (symmetric tensors, where σ · x = x for all σ) is isomorphic to
the n-th symmetric power Sym[k]^n V.

The GL(V)-action on SⁿV is given by g · (v₁ ⊙ ... ⊙ vₙ) = (gv₁) ⊙ ... ⊙ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Example5_19_3_symmetric
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symInvariants k V n ≃ₗ[k] SymmetricPower k (Fin n) V) := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  let f : ↥(symInvariants k V n) →ₗ[k] SymmetricPower k (Fin n) V :=
    (SymmetricPower.mk k (Fin n) V).comp (symInvariants k V n).subtype
  exact ⟨LinearEquiv.ofBijective f ⟨fun a b hab => by
    ext1
    have hmk : SymmetricPower.mk k (Fin n) V (a.1 - b.1) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    have hmem : a.1 - b.1 ∈ symInvariants k V n := sub_mem a.2 b.2
    have h1 : symSum (a.1 - b.1) = 0 :=
      ker_mk_le_ker_symSum (LinearMap.mem_ker.mpr hmk)
    have h2 : symSum (a.1 - b.1) = (Fintype.card (Equiv.Perm (Fin n)) : k) • (a.1 - b.1) :=
      symSum_of_mem_symInvariants _ hmem
    rw [h2] at h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hcard),
  fun y => by
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) y
    refine ⟨⟨(Fintype.card (Equiv.Perm (Fin n)) : k)⁻¹ • symSum x,
      Submodule.smul_mem _ _ (symSum_mem_symInvariants x)⟩, ?_⟩
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, map_smul,
      mk_symSum, smul_smul, inv_mul_cancel₀ hcard, one_smul, hx]⟩⟩

/-- For the partition λ = (1ⁿ), the Schur functor L_{(1ⁿ)} equals ∧ⁿV
(the n-th exterior power), which is zero when n > dim V.

The Sₙ-antisymmetric subspace of V⊗ⁿ (alternating tensors, where
σ · x = sign(σ) · x for all σ) is isomorphic to the n-th exterior
power ⋀[k]^n V.

The GL(V)-action on ∧ⁿV is given by g · (v₁ ∧ ... ∧ vₙ) = (gv₁) ∧ ... ∧ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Example5_19_3_exterior
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symAntisymmetric k V n ≃ₗ[k] ⋀[k]^n V) := by
  sorry

end Etingof
