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

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

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

/-- The standard tensor basis for `(k^N)^{⊗n}`, indexed by `Fin n → Fin N`. -/
private noncomputable abbrev tBasis (N n : ℕ) :=
  (_root_.Basis.piTensorProduct (R := k) (fun _ : Fin n => Pi.basisFun k (Fin N)))

omit [IsAlgClosed k] in
/-- `diagUnit(i, t)` acts on the tensor basis by scalar `t^(count of i in f)`. -/
private lemma glTensorRep_diagUnit_tBasis (N n : ℕ) (i : Fin N) (t : kˣ)
    (f : Fin n → Fin N) :
    (glTensorRep k N n (diagUnit k N i t)) (tBasis (k := k) N n f) =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
        tBasis (k := k) N n f := by
  show PiTensorProduct.map (fun _ => Matrix.mulVecLin (diagUnit k N i t).val)
      (tBasis (k := k) N n f) =
    ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
      tBasis (k := k) N n f
  simp only [tBasis, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
  -- Matrix.mulVecLin(diagUnit) on basis vector = scalar • basis vector
  have haction : ∀ (m : Fin n),
      Matrix.mulVecLin (R := k) (diagUnit k N i t).val (Pi.basisFun k (Fin N) (f m)) =
        (Function.update (1 : Fin N → k) i (t : k)) (f m) •
          Pi.basisFun k (Fin N) (f m) := by
    intro m
    simp only [diagUnit, Matrix.mulVecLin_apply, Pi.basisFun_apply]
    rw [Matrix.mulVec_single]
    ext x
    simp only [mul_one, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
      Function.update_apply, Pi.single_apply, Pi.one_apply]
    by_cases hm : f m = i <;> by_cases hx : x = f m <;> simp_all [Pi.single_apply]
  simp_rw [haction]
  rw [(PiTensorProduct.tprod k).map_smul_univ
    (fun j => (Function.update (1 : Fin N → k) i (t : k)) (f j))
    (fun j => Pi.basisFun k (Fin N) (f j))]
  congr 1
  simp only [Function.update_apply, Pi.one_apply]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

omit [IsAlgClosed k] in
/-- The f-th basis coordinate of `glTensorRep(diagUnit(i,t))` applied to `v` equals
`t^(count f i) * (f-th coordinate of v)`. -/
private lemma repr_glTensorRep_diagUnit (N n : ℕ) (i : Fin N) (t : kˣ)
    (v : TensorPower k (Fin N → k) n) (f : Fin n → Fin N) :
    (tBasis (k := k) N n).repr ((glTensorRep k N n (diagUnit k N i t)) v) f =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) *
        (tBasis (k := k) N n).repr v f := by
  set b := tBasis (k := k) N n
  set c := ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card)
  -- Both sides are linear in v; reduce to basis elements via LinearMap equality
  have h_eq : (Finsupp.lapply f).comp (b.repr.toLinearMap.comp
      (glTensorRep k N n (diagUnit k N i t))) =
      c • ((Finsupp.lapply f).comp b.repr.toLinearMap) := by
    apply b.ext; intro g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.smul_apply,
      smul_eq_mul, Finsupp.lapply_apply]
    rw [glTensorRep_diagUnit_tBasis, map_smul, Finsupp.smul_apply, smul_eq_mul,
      b.repr_self_apply]
    by_cases hgf : g = f <;> simp [hgf, c]
  exact LinearMap.congr_fun h_eq v

private theorem formalCharacter_detTwist_eq_shift (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      formalCharacter k N (SchurModule k N (fun i => lam i + 1)) := by
  rw [formalCharacter_schurModule_shift k N lam hlam]
  exact formalCharacter_shift_of_weightSpace_finrank k N _ _
    (fun ν => finrank_submodule_congr (glWeightSpace_detTwist_shift k N lam ν))
    (fun μ hμ => by
      -- The det-twisted Schur module has no weight spaces at zero-component weights.
      obtain ⟨i₀, hi₀⟩ := hμ
      suffices h : glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam)) μ = ⊥ by
        simp [h]
      rw [Submodule.eq_bot_iff]
      intro v hv
      simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv
      -- For all t: ρ(diagUnit(i₀, t)) v = t^(μ i₀) • v = v  (since μ i₀ = 0)
      have hv_fix : ∀ t : kˣ,
          (FDRep.of (detTwistedSchurModuleRep k N lam)).ρ (diagUnit k N i₀ t) v = v := by
        intro t; have := hv i₀ t; rw [hi₀, pow_zero, one_smul] at this
        exact eq_of_sub_eq_zero this
      -- v is in SchurModuleSubmodule, a subtype of the tensor power
      -- Show (v : TensorPower) = 0 using the tensor basis diagonal action
      set n := ∑ i, lam i
      set b := tBasis (k := k) N n
      -- Extract the underlying tensor power element
      set vt : TensorPower k (Fin N → k) n :=
        (v : SchurModuleSubmodule k N lam).val with hvt_def
      -- It suffices to show all basis coordinates of v (in the tensor power) are zero
      suffices hv_val : vt = 0 by
        exact SetCoe.ext hv_val
      rw [← b.repr.map_eq_zero_iff]
      ext f
      simp only [Finsupp.zero_apply]
      by_contra hcf
      -- The f-th basis coefficient is nonzero; derive contradiction
      set m := (Finset.univ.filter (fun j => f j = i₀)).card
      -- Pick t₀ with t₀^(m+1) ≠ 1 (exists since k is algebraically closed, hence infinite)
      obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne_one k (m + 1) (by omega)
      -- From weight space condition at (i₀, t₀):
      -- detTwistedRep(g) v = det(g) • schurModuleRep(g) v
      -- On the tensor power level: t₀ • glTensorRep(diagUnit(i₀, t₀)) vt = vt
      have hfix_val : (t₀ : k) • (glTensorRep k N n (diagUnit k N i₀ t₀)) vt = vt := by
        have h := congr_arg Subtype.val (hv_fix t₀)
        -- h : ↑(ρ(g) v) = ↑v at the FDRep level
        -- Unfold through: FDRep.of_ρ' → detTwistedSchurModuleRep → smul + restrict → glTensorRep
        simp only [FDRep.of_ρ'] at h
        -- The coercions (smul_apply, restrict_coe_apply, coe_smul) are all rfl,
        -- so h is definitionally: det(g) • glTensorRep(g) vt = vt
        have h2 : (Matrix.GeneralLinearGroup.det (diagUnit k N i₀ t₀) : k) •
            (glTensorRep k N n (diagUnit k N i₀ t₀)) vt = vt := h
        rw [det_diagUnit_val] at h2
        exact h2
      -- Extract f-th basis coordinate: t₀^(m+1) * c_f = c_f
      have hcoord : (t₀ : k) ^ (m + 1) * b.repr vt f = b.repr vt f := by
        have h1 := congr_arg (fun w => b.repr w f) hfix_val
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
        rw [repr_glTensorRep_diagUnit, ← mul_assoc, ← pow_succ'] at h1
        exact h1
      -- (t₀^(m+1) - 1) * c_f = 0, contradicting both ≠ 0
      have h_zero : ((t₀ : k) ^ (m + 1) - 1) * b.repr vt f = 0 := by
        rw [sub_mul, one_mul, hcoord, sub_self]
      exact (mul_eq_zero.mp h_zero).elim (sub_ne_zero.mpr ht₀) hcf)

/-! ### Weight decomposition for Schur modules

The weight spaces of a Schur module form a direct internal decomposition.
This is used to show `finrank(L_λ) = ∑_μ finrank(L_λ)_μ = eval₁(schurPoly)`,
which gives the dimension equality `finrank(L_λ) = finrank(L_{λ+(1,...,1)})`. -/

/-- The Young symmetrizer maps tensor basis elements to weight vectors:
`c_λ(e_f)` has weight `tensorWeight(f)` because `c_λ` commutes with the torus. -/
private lemma youngSym_tBasis_weightVector (N : ℕ) (lam : Fin N → ℕ)
    (f : Fin (∑ i, lam i) → Fin N) (i : Fin N) (t : kˣ) :
    glTensorRep k N (∑ j, lam j) (diagUnit k N i t)
      (youngSymEndomorphism k N lam (tBasis (k := k) N (∑ j, lam j) f)) =
    ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
      youngSymEndomorphism k N lam (tBasis (k := k) N (∑ j, lam j) f) := by
  change (glTensorRep k N (∑ j, lam j) (diagUnit k N i t) ∘ₗ
    youngSymEndomorphism k N lam) (tBasis (k := k) N (∑ j, lam j) f) = _
  rw [glTensor_comm_youngSym k N lam (diagUnit k N i t),
    LinearMap.comp_apply, glTensorRep_diagUnit_tBasis, map_smul]

/-- Weight spaces of the Schur module span the entire module.
Every element of `L_λ = range(c_λ)` is a sum of weight vectors since each
`c_λ(e_f)` lies in the weight space for `tensorWeight(f)` (because `c_λ`
commutes with the torus action). -/
private theorem glWeightSpace_schurModule_iSup_eq_top (N : ℕ) (lam : Fin N → ℕ) :
    ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N (SchurModule k N lam) (fun i => μ i) = ⊤ := by
  -- Proof: v ∈ L_λ ⇒ v = ∑ cₑ · c_λ(eₑ), each c_λ(eₑ) is a weight vector
  -- by youngSym_tBasis_weightVector + glTensor_comm_youngSym
  sorry

/-- Weight spaces for distinct weights are disjoint: if `μ ≠ ν`, then
`glWeightSpace(L, μ) ⊓ glWeightSpace(L, ν) = ⊥`. -/
private theorem glWeightSpace_disjoint (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    {μ ν : Fin N → ℕ} (hne : μ ≠ ν) :
    Disjoint (glWeightSpace k N M μ) (glWeightSpace k N M ν) := by
  rw [Function.ne_iff] at hne; obtain ⟨i₀, hi₀⟩ := hne
  rw [Submodule.disjoint_def]
  intro v hv_μ hv_ν
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv_μ hv_ν
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne k hi₀
  have h1 : M.ρ (diagUnit k N i₀ t₀) v = ((t₀ : k) ^ μ i₀) • v :=
    sub_eq_zero.mp (hv_μ i₀ t₀)
  have h2 : M.ρ (diagUnit k N i₀ t₀) v = ((t₀ : k) ^ ν i₀) • v :=
    sub_eq_zero.mp (hv_ν i₀ t₀)
  have h3 : (((t₀ : k) ^ μ i₀) - ((t₀ : k) ^ ν i₀)) • v = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr (h1.symm.trans h2)
  rw [smul_eq_zero, sub_eq_zero] at h3
  exact h3.resolve_left ht₀

/-- Key isomorphism: the Schur module `L_{λ+(1,…,1)}` is isomorphic (as a GL_N-representation)
to the determinant-twisted Schur module `det ⊗ L_λ`.

Mathematically: `L_λ ⊗ ∧^N V ⊂ V^{⊗n} ⊗ ∧^N V ⊂ V^{⊗(n+N)}`, and the unique
component of `V^{⊗(n+N)}` with the same character as `L_λ ⊗ ∧^N V` is `L_{λ+(1,…,1)}`.
This is the core mathematical content of Proposition 5.22.2. -/
theorem schurModule_shift_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurModuleRep k N (fun i => lam i + 1)) ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  have hlam' : Antitone (fun i => lam i + 1) :=
    fun i j hij => Nat.add_le_add_right (hlam hij) 1
  -- The det-twisted Schur module has the same formal character as the shifted Schur module
  have h_char : formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      schurPoly N (fun i => lam i + 1) := by
    rw [formalCharacter_detTwist_eq_shift k N lam hlam,
        Theorem5_22_1 k N _ hlam']
  -- The det-twisted rep has the same dimension as the shifted Schur module.
  -- Both are polynomial GL_N reps (ℕ-valued weight spaces span everything),
  -- so their dimensions equal the total mass of the Schur polynomial.
  -- Since S_{λ+(1,...,1)} = (∏ Xᵢ) · S_λ and ∏ Xᵢ preserves total mass,
  -- dim L_λ = dim L_{λ+(1,...,1)}.
  have h_dim : Module.finrank k (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      Module.finrank k (SchurModule k N (fun i => lam i + 1)) := by
    sorry
  -- By iso_of_formalCharacter_eq_schurPoly, the det-twisted rep ≅ SchurModule k N (λ+1)
  obtain ⟨iso⟩ := iso_of_formalCharacter_eq_schurPoly k N (fun i => lam i + 1) hlam' _ h_char h_dim
  exact ⟨iso.symm⟩

omit [IsAlgClosed k] [CharZero k] in
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
