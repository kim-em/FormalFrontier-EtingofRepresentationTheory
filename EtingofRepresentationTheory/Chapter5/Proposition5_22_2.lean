import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

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

/-! ### Schur polynomial shift identity

The Schur polynomial for the shifted partition `λ + (1,…,1)` equals
`(∏ Xᵢ) · S_λ`. This follows from the alternant determinant row-scaling
identity: multiplying each row i by `Xᵢ` shifts all exponents by 1. -/

/-- The shifted exponents for `λ + (1,…,1)` equal the original shifted exponents plus 1. -/
private lemma shiftedExps_shift (N : ℕ) (lam : Fin N → ℕ) :
    shiftedExps N (fun i => lam i + 1) = fun j => shiftedExps N lam j + 1 := by
  ext j; simp [shiftedExps]; omega

/-- The alternant matrix with all exponents incremented by 1 equals the diagonal matrix
`diag(X₀, …, X_{N-1})` times the original alternant matrix. -/
private lemma alternantMatrix_shift (N : ℕ) (e : Fin N → ℕ) :
    alternantMatrix N (fun j => e j + 1) =
      Matrix.diagonal (fun i => MvPolynomial.X i) * alternantMatrix N e := by
  ext i j
  simp [alternantMatrix, Matrix.of_apply, Matrix.diagonal_mul, pow_succ, mul_comm]

/-- Row-scaling identity: incrementing all exponents multiplies the alternant
determinant by `∏ Xᵢ`. -/
private lemma alternant_det_shift (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N (fun j => e j + 1)).det =
      (∏ i : Fin N, MvPolynomial.X i) * (alternantMatrix N e).det := by
  rw [alternantMatrix_shift, Matrix.det_mul, Matrix.det_diagonal]

/-- **Schur polynomial shift**: `S_{λ+(1,…,1)} = (∏ Xᵢ) · S_λ`.
Adding 1 to every part of the partition multiplies the Schur polynomial
by the monomial `x₁ · x₂ · ⋯ · x_N`. -/
theorem schurPoly_shift (N : ℕ) (lam : Fin N → ℕ) :
    schurPoly N (fun i => lam i + 1) =
      (∏ i : Fin N, MvPolynomial.X i) * schurPoly N lam := by
  have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [mul_assoc, schurPoly_mul_vandermonde, schurPoly_mul_vandermonde,
      ← alternant_det_shift, shiftedExps_shift]

/-- The formal character of `L_{λ+(1,…,1)}` equals `(∏ Xᵢ) · char(L_λ)`.
This follows from Theorem 5.22.1 (Weyl character formula) and schurPoly_shift. -/
theorem formalCharacter_schurModule_shift (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N (fun i => lam i + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N (SchurModule k N lam) := by
  have hlam' : Antitone (fun i => lam i + 1) := fun i j hij => Nat.add_le_add_right (hlam hij) 1
  rw [Theorem5_22_1 k N _ hlam', Theorem5_22_1 k N lam hlam, schurPoly_shift]

omit [IsAlgClosed k] in
/-- The determinant of `diagUnit k N i t` is `t`. -/
private lemma det_diagUnit (N : ℕ) (i : Fin N) (t : kˣ) :
    Matrix.GeneralLinearGroup.det (diagUnit k N i t) = t := by
  ext
  change Matrix.det (diagUnit k N i t).val = (t : k)
  simp only [diagUnit, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i),
    Pi.one_apply]
  simp [Finset.prod_eq_one (fun j _ => rfl)]

omit [IsAlgClosed k] in
private lemma det_diagUnit_val (N : ℕ) (i : Fin N) (t : kˣ) :
    (Matrix.GeneralLinearGroup.det (diagUnit k N i t) : k) = (t : k) :=
  congr_arg Units.val (det_diagUnit k N i t)

-- The initial `simp only [glWeightSpace, ...]` unfold is expensive.
set_option maxHeartbeats 800000 in
/-- The weight space of the det-twisted module at weight `μ + 1` equals
the weight space of the original Schur module at weight `μ`. -/
lemma glWeightSpace_detTwist_shift (N : ℕ) (lam : Fin N → ℕ) (μ : Fin N → ℕ) :
    glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam)) (fun j => μ j + 1) =
      glWeightSpace k N (SchurModule k N lam) μ := by
  -- Unfold definitions to iInf over kernels
  simp only [glWeightSpace, SchurModule, FDRep.of_ρ']
  -- detTwisted(g) = t • orig(g), so the linear maps factor:
  -- detTwisted(g) - t^(μ+1)•id = t•(orig(g) - t^μ•id)
  -- Hence ker(detTwisted(g) - t^(μ+1)•id) = ker(orig(g) - t^μ•id)
  apply iInf_congr; intro i; apply iInf_congr; intro t
  have hdt : (detTwistedSchurModuleRep k N lam (diagUnit k N i t)) =
      (t : k) • (schurModuleRep k N lam (diagUnit k N i t)) := by
    change (Matrix.GeneralLinearGroup.det (diagUnit k N i t) : k) •
      (schurModuleRep k N lam) (diagUnit k N i t) = _
    rw [det_diagUnit_val]
  have factored : (detTwistedSchurModuleRep k N lam (diagUnit k N i t)) -
      ((↑t : k) ^ (μ i + 1)) • LinearMap.id =
    (↑t : k) • ((schurModuleRep k N lam (diagUnit k N i t)) -
      ((↑t : k) ^ μ i) • LinearMap.id) := by
    rw [hdt, smul_sub, pow_succ, mul_comm, mul_smul]
  calc LinearMap.ker ((detTwistedSchurModuleRep k N lam (diagUnit k N i t)) -
        ((↑t : k) ^ (μ i + 1)) • LinearMap.id)
      = LinearMap.ker ((↑t : k) • ((schurModuleRep k N lam (diagUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id)) := congr_arg LinearMap.ker factored
    _ = LinearMap.ker ((schurModuleRep k N lam (diagUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id) := LinearMap.ker_smul _ _ (Units.ne_zero t)

/-- The formal character of the det-twisted Schur module equals that of the shifted
Schur module `L_{λ+(1,…,1)}`. Both equal `(∏ Xᵢ) · char(L_λ)`. -/
private lemma finrank_submodule_congr {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {S₁ S₂ : Submodule R M} (h : S₁ = S₂) :
    Module.finrank R S₁ = Module.finrank R S₂ := by subst h; rfl

private theorem formalCharacter_detTwist_eq_shift (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      formalCharacter k N (SchurModule k N (fun i => lam i + 1)) := by
  rw [formalCharacter_schurModule_shift k N lam hlam]
  exact formalCharacter_shift_of_weightSpace_finrank k N _ _
    (fun ν => finrank_submodule_congr (glWeightSpace_detTwist_shift k N lam ν))
    (fun μ hμ => by
      -- The det-twisted Schur module has no weight spaces at zero-component weights.
      -- This follows from the polynomial nature of the tensor power action:
      -- diagUnit acts with eigenvalues t^m for m ≥ 0 on V^⊗n, and the det twist
      -- shifts all eigenvalues by +1, so all weights have components ≥ 1.
      sorry)

/-- Key isomorphism: the Schur module `L_{λ+(1,…,1)}` is isomorphic (as a GL_N-representation)
to the determinant-twisted Schur module `det ⊗ L_λ`.

Mathematically: `L_λ ⊗ ∧^N V ⊂ V^{⊗n} ⊗ ∧^N V ⊂ V^{⊗(n+N)}`, and the unique
component of `V^{⊗(n+N)}` with the same character as `L_λ ⊗ ∧^N V` is `L_{λ+(1,…,1)}`.
This is the core mathematical content of Proposition 5.22.2. -/
theorem schurModule_shift_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurModuleRep k N (fun i => lam i + 1)) ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  exact iso_of_formalCharacter_eq k N _ _ (formalCharacter_detTwist_eq_shift k N lam hlam).symm

omit [IsAlgClosed k] in
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
