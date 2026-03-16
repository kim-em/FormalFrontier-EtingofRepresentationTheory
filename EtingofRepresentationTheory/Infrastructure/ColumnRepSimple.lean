import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Column representations are simple

This file proves that the column vector representations from the Wedderburn-Artin
decomposition are simple objects in `FDRep k G`.
-/

open CategoryTheory Representation

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

namespace IrrepDecomp

variable [NeZero (Nat.card G : k)] (D : IrrepDecomp k G) (i : Fin D.n)

/-- `projRingHom` preserves k-scalar multiplication. -/
private lemma projRingHom_smul (r : k) (α : MonoidAlgebra k G) :
    D.projRingHom i (r • α) = r • D.projRingHom i α := by
  show (Pi.evalRingHom _ i) (D.iso (r • α)) = r • (Pi.evalRingHom _ i) (D.iso α)
  rw [show D.iso (r • α) = r • D.iso α from map_smul D.iso r α]; simp [Pi.evalRingHom_apply, Pi.smul_apply]

/-- For any α ∈ k[G], the action of `projRingHom(α)` preserves a subrepresentation. -/
private lemma projRingHom_mulVec_mem_subrepresentation
    (S : Subrepresentation (D.columnRep i))
    (α : MonoidAlgebra k G) (v : Fin (D.d i) → k) (hv : v ∈ S.toSubmodule) :
    Matrix.mulVec (D.projRingHom i α) v ∈ S.toSubmodule := by
  induction α using MonoidAlgebra.induction_on with
  | hM g =>
    have : (D.columnRep i) g v = Matrix.mulVec (D.projRingHom i (MonoidAlgebra.of k G g)) v := by
      simp [columnRep, projRingHom, MonoidAlgebra.of_apply]
    rw [← this]
    exact S.apply_mem_toSubmodule g hv
  | hadd a b ha hb =>
    rw [map_add, Matrix.add_mulVec]
    exact S.toSubmodule.add_mem ha hb
  | hsmul r a ha =>
    rw [projRingHom_smul, Matrix.smul_mulVec]
    exact S.toSubmodule.smul_mem r ha

/-- Helper: a Subrepresentation gives a Matrix submodule with the same carrier. -/
private def toMatSubmodule (S : Subrepresentation (D.columnRep i)) :
    Submodule (Matrix (Fin (D.d i)) (Fin (D.d i)) k) (Fin (D.d i) → k) where
  carrier := S.toSubmodule.carrier
  add_mem' := S.toSubmodule.add_mem'
  zero_mem' := S.toSubmodule.zero_mem'
  smul_mem' M v hv := by
    rw [Matrix.smul_eq_mulVec]
    obtain ⟨α, rfl⟩ := D.projRingHom_surjective i M
    exact D.projRingHom_mulVec_mem_subrepresentation i S α v hv

/-- The column vector representation is irreducible. -/
instance columnRep_isIrreducible : (D.columnRep i).IsIrreducible := by
  haveI := D.d_pos i
  haveI hSimple : IsSimpleModule (Matrix (Fin (D.d i)) (Fin (D.d i)) k) (Fin (D.d i) → k) :=
    Matrix.instIsSimpleModule (D.d i)
  refine {
    exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩
    eq_bot_or_eq_top := fun S => ?_ }
  · -- ⊥ ≠ ⊤: there exists a nonzero element
    have hmem : Pi.single (0 : Fin (D.d i)) (1 : k) ∈
        (⊤ : Subrepresentation (D.columnRep i)).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    have hne : (0 : Fin (D.d i) → k) ≠ Pi.single (0 : Fin (D.d i)) (1 : k) := by
      intro heq; have := congr_fun heq 0; simp at this
    exact hne (by change Pi.single 0 1 ∈ (⊥ : Submodule k _) at hmem; rw [Submodule.mem_bot] at hmem; exact hmem.symm)
  · -- Every subrepresentation is ⊥ or ⊤
    rcases hSimple.eq_bot_or_eq_top (D.toMatSubmodule i S) with h | h
    · left; apply Subrepresentation.toSubmodule_injective
      apply le_antisymm
      · intro x hx
        have hx' : x ∈ (D.toMatSubmodule i S) := hx
        rw [h] at hx'; rw [Submodule.mem_bot] at hx'
        subst hx'; exact Submodule.zero_mem _
      · exact bot_le
    · right; apply Subrepresentation.toSubmodule_injective
      apply le_antisymm
      · exact le_top
      · intro x _
        show x ∈ (D.toMatSubmodule i S)
        rw [h]; exact Submodule.mem_top

/-- Helper: `ρ g⁻¹ (ρ g v) = v` for a group representation. -/
private lemma columnRep_inv_mul_cancel (g : G) (v : Fin (D.d i) → k) :
    (D.columnRep i) g⁻¹ ((D.columnRep i) g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- Helper: `ρ g (ρ g⁻¹ v) = v` for a group representation. -/
private lemma columnRep_mul_inv_cancel (g : G) (v : Fin (D.d i) → k) :
    (D.columnRep i) g ((D.columnRep i) g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Linear equivalence between linHom invariants and IntertwiningMap. -/
private noncomputable def invariantsEquivIntertwining :
    (Representation.linHom (D.columnRep i) (D.columnRep i)).invariants ≃ₗ[k]
      Representation.IntertwiningMap (D.columnRep i) (D.columnRep i) where
  toFun f := {
    toLinearMap := f.val
    isIntertwining' := fun g v => by
      have hf := f.property g
      rw [Representation.linHom_apply] at hf
      -- hf : ρ g ∘ₗ f.val ∘ₗ ρ g⁻¹ = f.val
      have key := LinearMap.congr_fun hf.symm ((D.columnRep i) g v)
      simp only [LinearMap.comp_apply, D.columnRep_inv_mul_cancel] at key
      exact key }
  invFun f := {
    val := f.toLinearMap
    property := fun g => by
      rw [Representation.linHom_apply]
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      have := f.isIntertwining' g ((D.columnRep i) g⁻¹ v)
      rw [D.columnRep_mul_inv_cancel] at this
      exact this.symm }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- columnFDRep_simple is defined in IrreducibleEnumeration.lean; register as instance here
attribute [instance] IrrepDecomp.columnFDRep_simple

end IrrepDecomp
