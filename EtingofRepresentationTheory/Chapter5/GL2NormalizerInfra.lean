import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues

/-!
# GL₂ Normalizer Infrastructure for Elliptic Subgroup

Infrastructure about the normalizer of K = 𝔽_{q²}× ⊂ GL₂(𝔽_q):
- Frobenius matrix and conjugation action
- Centralizer of non-scalar K-elements
- Normalizer structure N(K) = K ∪ σK, |N| = 2|K|
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

open scoped Matrix

/-- The Frobenius automorphism of 𝔽_{q²}/𝔽_q, represented as an element of GL₂(𝔽_q).
This is the matrix of the map x ↦ x^q with respect to the embedding basis. -/
noncomputable def Etingof.GL2.frobeniusMatrix : GL2 p n := by
  by_cases hn : n = 0
  · exact 1
  · letI := Etingof.algebraGaloisFieldExt p n
    letI := Etingof.scalarTowerGaloisField p n
    haveI := Etingof.finiteDimensionalGaloisFieldExt p n
    haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
    haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
    haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
      Algebra.IsAlgebraic.of_finite _ _
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
    let M := LinearMap.toMatrix b b σ.toLinearMap
    let M_inv := LinearMap.toMatrix b b σ.symm.toLinearMap
    refine ⟨M, M_inv, ?_, ?_⟩
    · -- M * M_inv = 1: toMatrix(σ) * toMatrix(σ⁻¹) = toMatrix(σ ∘ σ⁻¹) = toMatrix(id) = 1
      rw [← LinearMap.toMatrix_mul, show σ.toLinearMap * σ.symm.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]
    · -- M_inv * M = 1
      rw [← LinearMap.toMatrix_mul, show σ.symm.toLinearMap * σ.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]

/-- σ² = id in GL₂ (the Frobenius has order dividing 2 on 𝔽_{q²}/𝔽_q). -/
lemma Etingof.GL2.frobeniusMatrix_sq_eq_one (hn : n ≠ 0) :
    Etingof.GL2.frobeniusMatrix p n ^ 2 = 1 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
  rw [sq]
  apply Units.ext
  -- Unfold frobeniusMatrix to expose the internal basis
  have hval : (Etingof.GL2.frobeniusMatrix p n).val =
      LinearMap.toMatrix b b σ.toLinearMap := by
    change (Etingof.GL2.frobeniusMatrix p n).val = _
    simp only [Etingof.GL2.frobeniusMatrix, dif_neg hn]
    congr; exact Subsingleton.elim _ _
  simp only [Units.val_mul, Units.val_one, hval, ← LinearMap.toMatrix_mul]
  have hσ2 : σ.toLinearMap * σ.toLinearMap = LinearMap.id := by
    ext x
    show σ (σ x) = x
    -- σ(x) = x^q where q = card(F_q), so σ(σ(x)) = x^{q²} = x since |F_{q²}| = q²
    let σ_alg := FiniteField.frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))
    change σ_alg (σ_alg x) = x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    -- Goal: (x ^ q) ^ q = x, beta-reduce and simplify
    simp only [← pow_mul]
    -- x ^ (q * q) = x since card(F_{q²}) = q²
    have hcard : Fintype.card (GaloisField p n) * Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p (2 * n)) := by
      simp only [Fintype.card_eq_nat_card]
      have h1 := @GaloisField.card p _ n hn
      have h2 := @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)
      rw [h1, h2]
      ring
    rw [hcard]
    exact FiniteField.pow_card x
  rw [hσ2, LinearMap.toMatrix_id]

/-- The Frobenius σ⁻¹ = σ (since σ² = 1). -/
lemma Etingof.GL2.frobeniusMatrix_inv_eq_self (hn : n ≠ 0) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ = Etingof.GL2.frobeniusMatrix p n := by
  have h2 := Etingof.GL2.frobeniusMatrix_sq_eq_one p n hn
  rw [sq] at h2
  exact inv_eq_of_mul_eq_one_left h2

/-- The Frobenius matrix conjugates fieldExtEmbed(α) to fieldExtEmbed(α^q). -/
lemma Etingof.GL2.frobeniusMatrix_conj [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (α : (GaloisField p (2 * n))ˣ) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ *
    Etingof.GL2.fieldExtEmbed p n α *
    Etingof.GL2.frobeniusMatrix p n =
    Etingof.GL2.fieldExtEmbed p n
      ⟨(α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       (α⁻¹ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, mul_inv_cancel₀ α.ne_zero],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, inv_mul_cancel₀ α.ne_zero]⟩ := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  -- Note: [Fintype (GaloisField p n)] already from statement; don't duplicate
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  let σ_alg := FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))
  let σ := σ_alg.toLinearEquiv
  rw [Etingof.GL2.frobeniusMatrix_inv_eq_self p n hn]
  apply Units.ext
  have hfrob : (Etingof.GL2.frobeniusMatrix p n).val =
      LinearMap.toMatrix b b σ.toLinearMap := by
    change (Etingof.GL2.frobeniusMatrix p n).val = _
    simp only [Etingof.GL2.frobeniusMatrix, dif_neg hn]
    congr; exact Subsingleton.elim _ _
  have hembed : ∀ (β : (GaloisField p (2 * n))ˣ),
      (Etingof.GL2.fieldExtEmbed p n β).val =
      Algebra.leftMulMatrix b (β : GaloisField p (2 * n)) := by
    intro β
    change (Etingof.GL2.fieldExtEmbed p n β).val = _
    simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]
    congr 1
  simp only [Units.val_mul, hfrob, hembed, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  -- Goal: (σ * Lα * σ)(x) = L_{α^q}(x)
  -- Unfold * on End to composition
  show σ ((Algebra.lmul (GaloisField p n) (GaloisField p (2 * n)) (↑α)) (σ x)) =
    (Algebra.lmul (GaloisField p n) (GaloisField p (2 * n))
      ((↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n))) x
  -- lmul a x = a * x
  show σ ((↑α : GaloisField p (2 * n)) * σ x) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) * x
  -- σ is the Frobenius ring hom: σ(a * b) = σ(a) * σ(b)
  change σ_alg ((↑α : GaloisField p (2 * n)) * σ_alg x) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) * x
  rw [map_mul]
  -- σ²(x) = x
  have hσσ : ∀ y, σ_alg (σ_alg y) = y := by
    intro y
    rw [show (σ_alg : GaloisField p (2 * n) → GaloisField p (2 * n)) = (· ^ Fintype.card (GaloisField p n)) from
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic (GaloisField p n) (GaloisField p (2 * n))]
    simp only [← pow_mul]
    have hcard : Fintype.card (GaloisField p n) * Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p (2 * n)) := by
      simp only [Fintype.card_eq_nat_card]
      rw [@GaloisField.card p _ n hn, @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)]
      ring
    rw [hcard]; exact FiniteField.pow_card y
  rw [hσσ, show (σ_alg (↑α : GaloisField p (2 * n))) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) from
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))) ↑α]

/-- The Frobenius matrix normalizes the elliptic subgroup K. -/
lemma Etingof.GL2.frobeniusMatrix_normalizes [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ * k * Etingof.GL2.frobeniusMatrix p n ∈
    Etingof.GL2.ellipticSubgroup p n := by
  obtain ⟨α, rfl⟩ := hk
  rw [Etingof.GL2.frobeniusMatrix_conj p n hn α]
  exact ⟨_, rfl⟩

/-- The Frobenius matrix squared is in K. -/
lemma Etingof.GL2.frobeniusMatrix_sq_mem (hn : n ≠ 0) :
    Etingof.GL2.frobeniusMatrix p n ^ 2 ∈ Etingof.GL2.ellipticSubgroup p n := by
  rw [Etingof.GL2.frobeniusMatrix_sq_eq_one p n hn]
  exact Subgroup.one_mem _

section Centralizer

/-! ### Centralizer of non-scalar elements of K -/

/-- For non-scalar ζ ∈ K = 𝔽_{q²}× ⊂ GL₂(𝔽_q), the centralizer C_{GL₂}(ζ) equals K.
If g commutes with ζ = embed(α) where α ∉ 𝔽_q, the corresponding linear map φ satisfies
φ(α·x) = α·φ(x). Since {1,α} spans 𝔽_{q²}, we get φ(x) = φ(1)·x, so g ∈ K. -/
lemma Etingof.centralizer_nonscalar_elliptic (hn : n ≠ 0)
    (ζ : GL2 p n) (hζ_mem : ζ ∈ Etingof.GL2.ellipticSubgroup p n)
    (hζ_ns : ¬GL2.IsScalar (p := p) (n := n) ζ)
    (g : GL2 p n) (hcomm : g * ζ = ζ * g) :
    g ∈ Etingof.GL2.ellipticSubgroup p n := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  obtain ⟨α, rfl⟩ := hζ_mem
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  -- fieldExtEmbed α has val = leftMulMatrix b α
  have hembed : ∀ u : (GaloisField p (2 * n))ˣ,
      (Etingof.GL2.fieldExtEmbed p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; change (Etingof.GL2.fieldExtEmbed p n u).val = _
    simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; congr 1
  -- Matrix commutation
  have hcomm_mat : g.val * Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) =
      Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) * g.val := by
    have := congr_arg (fun u : GL2 p n => u.val) hcomm
    simp only [Units.val_mul] at this; rwa [hembed] at this
  -- The linear map φ corresponding to g
  set φ : GaloisField p (2 * n) →ₗ[GaloisField p n] GaloisField p (2 * n) :=
    Matrix.toLinAlgEquiv b g.val with hφ_def
  -- φ commutes with left multiplication by α: φ(α * x) = α * φ(x)
  have hφα : ∀ x, φ ((↑α : GaloisField p (2 * n)) * x) =
      (↑α : GaloisField p (2 * n)) * φ x := by
    intro x
    -- toLinAlgEquiv b (leftMulMatrix b a) = lmul a, so applied to y gives a * y
    have hlm : ∀ y, Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b (↑α : GaloisField p (2 * n))) y =
        (↑α : GaloisField p (2 * n)) * y := by
      intro y
      -- leftMulMatrix b x = toMatrix b b (lmul x) by definition
      -- toLinAlgEquiv b = toLin b b (definitionally)
      -- toLin b b (toMatrix b b f) = f by Matrix.toLin_toMatrix
      show Matrix.toLin b b (LinearMap.toMatrix b b ((Algebra.lmul _ _) ↑α)) y = _
      rw [Matrix.toLin_toMatrix]
    -- From hcomm_mat, apply toLinAlgEquiv (an AlgEquiv, so preserves *) to both sides
    have heq := congr_arg (Matrix.toLinAlgEquiv b) hcomm_mat
    simp only [map_mul] at heq
    -- heq : φ * Lα = Lα * φ, apply to x
    have := congr_fun (congr_arg DFunLike.coe heq) x
    change φ (Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b ↑α) x) =
      Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b ↑α) (φ x) at this
    rw [hlm, hlm] at this; exact this
  -- α not in the base field (from non-scalar hypothesis)
  have hα_not_base : (↑α : GaloisField p (2 * n)) ∉
      Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
    intro ⟨c, hc⟩
    apply hζ_ns; rw [GL2.isScalar_iff]
    have hscalar : Algebra.leftMulMatrix b (↑α : GaloisField p (2 * n)) =
        (algebraMap (GaloisField p n) (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
      rw [← hc]; exact (Algebra.leftMulMatrix b).commutes c
    rw [hembed α, hscalar, Matrix.algebraMap_eq_diagonal]
    exact ⟨Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
           Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
           by simp [Matrix.diagonal_apply_eq]⟩
  -- {1, α} linearly independent over F_q
  have hli : LinearIndependent (GaloisField p n) ![1, (↑α : GaloisField p (2 * n))] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_fin_const] at hf
    intro i; fin_cases i
    · -- f 0 = 0: if f 1 ≠ 0 then α ∈ range(algebraMap), contradiction
      by_contra h0
      have hf1 : f 1 ≠ 0 := by
        intro hf1; rw [hf1, zero_smul, add_zero, smul_eq_zero] at hf
        exact h0 (hf.resolve_right one_ne_zero)
      apply hα_not_base
      refine ⟨(f 1)⁻¹ * (-f 0), ?_⟩
      have h1 := eq_neg_of_add_eq_zero_right hf
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have hne : algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1) ≠ 0 := by
        intro he; exact hf1 ((algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
          (he.trans (map_zero _).symm))
      calc algebraMap _ _ ((f 1)⁻¹ * (-f 0))
          = (algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1))⁻¹ *
            algebraMap _ _ (-f 0) := by rw [map_mul, map_inv₀]
        _ = (algebraMap _ (GaloisField p (2 * n)) (f 1))⁻¹ *
            -(algebraMap _ _ (f 0)) := by rw [map_neg]
        _ = (algebraMap _ _ (f 1))⁻¹ *
            (algebraMap _ _ (f 1) * ↑α) := by rw [h1]
        _ = ↑α := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    · -- f 1 = 0: same argument
      by_contra hf1
      apply hα_not_base
      refine ⟨(f 1)⁻¹ * (-f 0), ?_⟩
      have h1 := eq_neg_of_add_eq_zero_right hf
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have hne : algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1) ≠ 0 := by
        intro he; exact hf1 ((algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
          (he.trans (map_zero _).symm))
      calc algebraMap _ _ ((f 1)⁻¹ * (-f 0))
          = (algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1))⁻¹ *
            algebraMap _ _ (-f 0) := by rw [map_mul, map_inv₀]
        _ = (algebraMap _ (GaloisField p (2 * n)) (f 1))⁻¹ *
            -(algebraMap _ _ (f 0)) := by rw [map_neg]
        _ = (algebraMap _ _ (f 1))⁻¹ *
            (algebraMap _ _ (f 1) * ↑α) := by rw [h1]
        _ = ↑α := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  -- {1, α} spans since finrank = 2 and we have 2 independent vectors
  have hspan : Submodule.span (GaloisField p n) (Set.range ![1, (↑α : GaloisField p (2 * n))]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Etingof.finrank_galoisField_ext p n hn])
  -- φ(x) = φ(1) * x for all x
  have hφ_eq : ∀ x, φ x = φ 1 * x := by
    intro x
    have hx_mem : x ∈ (⊤ : Submodule (GaloisField p n) (GaloisField p (2 * n))) := trivial
    rw [← hspan] at hx_mem
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_mem
    obtain ⟨c, hcx⟩ := hx_mem
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_fin_const] at hcx
    rw [← hcx, map_add, map_smul, map_smul]
    have hφα1 : φ (↑α : GaloisField p (2 * n)) = (↑α : GaloisField p (2 * n)) * φ 1 := by
      have := hφα 1; rwa [mul_one] at this
    rw [hφα1]; simp only [Algebra.smul_def]; ring
  -- g.val = leftMulMatrix b (φ 1)
  have hg_eq : g.val = Algebra.leftMulMatrix b (φ 1) := by
    have hg_mat : g.val = LinearMap.toMatrixAlgEquiv b φ := by
      rw [hφ_def]; exact (LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b g.val).symm
    rw [hg_mat]; congr 1
    exact LinearMap.ext fun x => by
      show φ x = (Algebra.lmul (GaloisField p n) (GaloisField p (2 * n))) (φ 1) x
      change φ x = φ 1 * x; exact hφ_eq x
  -- φ 1 ≠ 0 (g is invertible)
  have hφ1_ne : φ 1 ≠ 0 := by
    intro h
    have hg_zero : g.val = 0 := by rw [hg_eq, h, map_zero]
    have h1 := congr_arg Units.val (mul_inv_cancel g)
    simp only [Units.val_mul, Units.val_one, hg_zero, zero_mul] at h1
    exact zero_ne_one h1
  -- Conclude: g = fieldExtEmbed(Units.mk0 (φ 1) hφ1_ne)
  exact ⟨Units.mk0 (φ 1) hφ1_ne, by
    apply Units.ext; simp only [hembed, Units.val_mk0, hg_eq]⟩

end Centralizer

section Normalizer

/-! ### Normalizer of K in GL₂ -/

/-- The normalizer of K in GL₂(𝔽_q): the set of elements that normalize K. -/
def Etingof.GL2.isInNormalizer (g : GL2 p n) : Prop :=
  ∀ k ∈ Etingof.GL2.ellipticSubgroup p n,
    g⁻¹ * k * g ∈ Etingof.GL2.ellipticSubgroup p n

/-- Elements of K are in the normalizer (K is abelian, so conjugation is trivial). -/
lemma Etingof.GL2.ellipticSubgroup_mem_normalizer
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n k := by
  intro k' hk'
  obtain ⟨α, rfl⟩ := hk
  obtain ⟨β, rfl⟩ := hk'
  change (Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
    Etingof.GL2.fieldExtEmbed p n β *
    Etingof.GL2.fieldExtEmbed p n α ∈ _
  rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  exact ⟨β, rfl⟩

/-- The Frobenius matrix is in the normalizer of K. -/
lemma Etingof.GL2.frobeniusMatrix_mem_normalizer [Fintype (GaloisField p n)] (hn : n ≠ 0) :
    Etingof.GL2.isInNormalizer p n (Etingof.GL2.frobeniusMatrix p n) :=
  fun k hk => Etingof.GL2.frobeniusMatrix_normalizes p n hn k hk

/-- The normalizer of K contains K and the Frobenius coset σK. -/
lemma Etingof.GL2.normalizer_contains_frobeniusCoset [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n (Etingof.GL2.frobeniusMatrix p n * k) := by
  intro k' hk'
  have : (Etingof.GL2.frobeniusMatrix p n * k)⁻¹ * k' *
    (Etingof.GL2.frobeniusMatrix p n * k) =
    k⁻¹ * ((Etingof.GL2.frobeniusMatrix p n)⁻¹ * k' *
      Etingof.GL2.frobeniusMatrix p n) * k := by group
  rw [this]
  exact Etingof.GL2.ellipticSubgroup_mem_normalizer p n k hk _
    (Etingof.GL2.frobeniusMatrix_normalizes p n hn k' hk')

/-- For non-scalar k ∈ K, if z⁻¹kz ∈ K then z normalizes K. -/
lemma Etingof.GL2.conj_mem_implies_normalizer (hn : n ≠ 0)
    (hp2 : p ≠ 2)
    (k : GL2 p n) (hk_mem : k ∈ Etingof.GL2.ellipticSubgroup p n)
    (hk_ns : ¬GL2.IsScalar (p := p) (n := n) k)
    (z : GL2 p n) (hz : z⁻¹ * k * z ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n z := by
  sorry

/-- The cardinality of the normalizer: |N_{GL₂}(K)| = 2|K|. -/
lemma Etingof.GL2.normalizer_card (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GL2 p n)] [Fintype (Etingof.GL2.ellipticSubgroup p n)]
    [DecidablePred (Etingof.GL2.isInNormalizer p n)] :
    (Finset.univ.filter (fun g : GL2 p n =>
      Etingof.GL2.isInNormalizer p n g)).card =
    2 * Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) := by
  sorry

end Normalizer
