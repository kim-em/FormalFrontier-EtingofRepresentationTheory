import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Proposition 5.22.2: Twisting by Determinant

`L_{λ + 1^N} ≅ L_λ ⊗ ∧^N V`, where `1^N = (1, 1, …, 1)`.

The top exterior power `∧^N V` is the one-dimensional determinant representation
of `GL_N(k)`. Tensoring by it shifts every part of the highest weight by 1.
This follows from the inclusion `L_λ ⊗ ∧^N V ⊂ V^{⊗(n+N)}` and the
uniqueness of the component with the given character.

## Mathlib correspondence

Uses the Schur module from `Theorem5_22_1`. The tensor product of `FDRep` objects
uses the monoidal category structure on `FDRep k G`.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- The determinant representation of `GL_N(k)`: the one-dimensional representation
given by `g ↦ det(g)`. This is isomorphic to the top exterior power `∧^N(k^N)` as
a `GL_N`-representation. Not yet in Mathlib. -/
noncomputable def detRep (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
    Matrix.GeneralLinearGroup.det)

/-- The determinant-twisted Schur module representation: `g ↦ det(g) • schurModuleRep(g)`.
This is the representation on the same underlying vector space as `L_λ`, but with the
GL_N action twisted by the determinant character. -/
def detTwistedSchurModuleRep (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (SchurModuleSubmodule k N lam) where
  toFun g := (Matrix.GeneralLinearGroup.det g : k) • schurModuleRep k N lam g
  map_one' := by simp [map_one]
  map_mul' g₁ g₂ := by
    have hdet : (Matrix.GeneralLinearGroup.det (g₁ * g₂) : k) =
      (Matrix.GeneralLinearGroup.det g₁ : k) * (Matrix.GeneralLinearGroup.det g₂ : k) := by
      simp [map_mul]
    have hmul : (schurModuleRep k N lam) (g₁ * g₂) = (schurModuleRep k N lam) g₁ *
      (schurModuleRep k N lam) g₂ := map_mul _ _ _
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hdet, hmul]
    rw [mul_smul]
    simp only [map_smul, Submodule.coe_smul_of_tower]

/-- Key isomorphism: the Schur module `L_{λ+(1,…,1)}` is isomorphic (as a GL_N-representation)
to the determinant-twisted Schur module `det ⊗ L_λ`.

Mathematically: `L_λ ⊗ ∧^N V ⊂ V^{⊗n} ⊗ ∧^N V ⊂ V^{⊗(n+N)}`, and the unique
component of `V^{⊗(n+N)}` with the same character as `L_λ ⊗ ∧^N V` is `L_{λ+(1,…,1)}`.
This is the core mathematical content of Proposition 5.22.2. -/
theorem schurModule_shift_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurModuleRep k N (fun i => lam i + 1)) ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  sorry

/-- The `TensorProduct.rid` intertwines the tensor action `rep(g) ⊗ det(g)·id` with
the determinant-twisted action `det(g) · rep(g)`. -/
theorem tensorRid_comm_detTwist (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap ∘ₗ
      TensorProduct.map (schurModuleRep k N lam g)
        (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
          Matrix.GeneralLinearGroup.det g) =
    (detTwistedSchurModuleRep k N lam g) ∘ₗ
      (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap := by
  apply TensorProduct.ext'
  intro v c
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, detTwistedSchurModuleRep]
  -- LHS: (det(g)·c) • rep(g) v   RHS: det(g) • rep(g) (c • v)
  -- LHS: (↑(lsmul).toRingHom ↑(det g)) c • rep(g) v  = (↑(det g) * c) • rep(g) v
  -- RHS: det(g) • rep(g) (c • v) = det(g) • c • rep(g) v
  change ((↑(Matrix.GeneralLinearGroup.det g) : k) * c) • ((schurModuleRep k N lam) g) v =
    (↑(Matrix.GeneralLinearGroup.det g) : k) • ((schurModuleRep k N lam) g) (c • v)
  rw [map_smul, mul_smul, smul_comm]

/-- The FDRep tensor product `L_λ ⊗ det` is isomorphic to the determinant-twisted
representation. For any 1-dimensional representation `χ`, `M ⊗ χ` is isomorphic
to `M` with the action twisted by `χ`. -/
theorem schurModule_tensor_det_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) :
    Nonempty (SchurModule k N lam ⊗ detRep k N ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  -- The underlying linear iso is TensorProduct.rid: M ⊗ k ≅ M
  refine ⟨Action.mkIso
    ((TensorProduct.rid k (SchurModuleSubmodule k N lam)).toFGModuleCatIso) (fun g => ?_)⟩
  ext : 1
  exact tensorRid_comm_detTwist k N lam g

/-- **Determinant twist**: `L_{λ+(1,…,1)} ≅ L_λ ⊗ ∧^N V` as `GL_N(k)`-representations.

Tensoring with the one-dimensional determinant representation shifts every part
of the highest weight by 1.
(Etingof Proposition 5.22.2) -/
theorem Proposition5_22_2
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (SchurModule k N (fun i => lam i + 1) ≅
      SchurModule k N lam ⊗ detRep k N) := by
  -- Decompose into two steps:
  -- (1) L_{λ+1^N} ≅ det-twisted L_λ  (character argument)
  -- (2) det-twisted L_λ ≅ L_λ ⊗ det  (categorical tensor/twist equivalence)
  obtain ⟨iso₁⟩ := schurModule_shift_iso_detTwist k N lam hlam
  obtain ⟨iso₂⟩ := schurModule_tensor_det_iso_detTwist k N lam
  exact ⟨iso₁ ≪≫ iso₂.symm⟩

end Etingof
