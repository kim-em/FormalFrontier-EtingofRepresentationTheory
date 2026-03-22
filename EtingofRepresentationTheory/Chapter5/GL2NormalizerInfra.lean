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
      rw [Matrix.toLin_toMatrix]; rfl
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
    ext i j
    rw [hg_mat, LinearMap.toMatrixAlgEquiv_apply,
        Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    congr 2; exact hφ_eq (b j)
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

/-- Scalar matrices commute with everything, so conjugation preserves non-scalarity. -/
private lemma GL2.isScalar_of_conj_isScalar (z g : GL2 p n)
    (h : GL2.IsScalar (p := p) (n := n) (z⁻¹ * g * z)) :
    GL2.IsScalar (p := p) (n := n) g := by
  rw [GL2.isScalar_iff] at h ⊢
  obtain ⟨h01, h10, h00_eq_h11⟩ := h
  -- z⁻¹gz = cI where c = (z⁻¹gz)₀₀. So g = z(cI)z⁻¹ = c(zz⁻¹) = cI.
  set c := (z⁻¹ * g * z).val 0 0
  have hscalar : (z⁻¹ * g * z).val = c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [c, h01, h10, h00_eq_h11]
  -- g = z * (z⁻¹gz) * z⁻¹
  have hrecover : g = z * (z⁻¹ * g * z) * z⁻¹ := by group
  have hg_val : g.val = c • 1 := by
    have := congr_arg Units.val hrecover
    simp only [Units.val_mul] at this
    rw [this]
    -- Goal: z.val * (z⁻¹.val * g.val * z.val) * z⁻¹.val = c • 1
    -- Replace z⁻¹.val * g.val * z.val with (z⁻¹ * g * z).val
    conv_lhs => rw [show (z⁻¹).val * g.val * z.val = (z⁻¹ * g * z).val from by
      simp [Units.val_mul]]
    rw [hscalar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have hzz : z.val * (z⁻¹).val = 1 :=
      show (z * z⁻¹).val = (1 : GL2 p n).val from congr_arg Units.val (mul_inv_cancel z)
    rw [hzz]
  constructor
  · have := congr_fun (congr_fun hg_val 0) 1; simp at this; exact this
  constructor
  · have := congr_fun (congr_fun hg_val 1) 0; simp at this; exact this
  · have h0 := congr_fun (congr_fun hg_val 0) 0
    have h1 := congr_fun (congr_fun hg_val 1) 1
    simp at h0 h1; rw [h0, h1]

/-- For non-scalar k ∈ K, if z⁻¹kz ∈ K then z normalizes K. -/
lemma Etingof.GL2.conj_mem_implies_normalizer (hn : n ≠ 0)
    (hp2 : p ≠ 2)
    (k : GL2 p n) (hk_mem : k ∈ Etingof.GL2.ellipticSubgroup p n)
    (hk_ns : ¬GL2.IsScalar (p := p) (n := n) k)
    (z : GL2 p n) (hz : z⁻¹ * k * z ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n z := by
  intro k' hk'
  -- z⁻¹k'z commutes with z⁻¹kz (since K is abelian and z⁻¹kz ∈ K)
  have hcomm : z⁻¹ * k' * z * (z⁻¹ * k * z) = z⁻¹ * k * z * (z⁻¹ * k' * z) := by
    -- k and k' commute (both in K, which is abelian)
    obtain ⟨α, rfl⟩ := hk_mem
    obtain ⟨β, rfl⟩ := hk'
    -- Both sides simplify using z * z⁻¹ = 1 in the middle
    have : z⁻¹ * Etingof.GL2.fieldExtEmbed p n β * z *
      (z⁻¹ * Etingof.GL2.fieldExtEmbed p n α * z) =
      z⁻¹ * (Etingof.GL2.fieldExtEmbed p n β *
      Etingof.GL2.fieldExtEmbed p n α) * z := by group
    have : z⁻¹ * Etingof.GL2.fieldExtEmbed p n α * z *
      (z⁻¹ * Etingof.GL2.fieldExtEmbed p n β * z) =
      z⁻¹ * (Etingof.GL2.fieldExtEmbed p n α *
      Etingof.GL2.fieldExtEmbed p n β) * z := by group
    rw [show z⁻¹ * Etingof.GL2.fieldExtEmbed p n β * z *
      (z⁻¹ * Etingof.GL2.fieldExtEmbed p n α * z) =
      z⁻¹ * (Etingof.GL2.fieldExtEmbed p n β *
      Etingof.GL2.fieldExtEmbed p n α) * z from by group,
      show z⁻¹ * Etingof.GL2.fieldExtEmbed p n α * z *
      (z⁻¹ * Etingof.GL2.fieldExtEmbed p n β * z) =
      z⁻¹ * (Etingof.GL2.fieldExtEmbed p n α *
      Etingof.GL2.fieldExtEmbed p n β) * z from by group,
      ← map_mul, ← map_mul, mul_comm β α]
  -- z⁻¹kz is non-scalar (since k is non-scalar)
  have hns : ¬GL2.IsScalar (p := p) (n := n) (z⁻¹ * k * z) :=
    fun h => hk_ns (GL2.isScalar_of_conj_isScalar p n z k h)
  -- By centralizer_nonscalar_elliptic, z⁻¹k'z ∈ K
  exact Etingof.centralizer_nonscalar_elliptic p n hn
    (z⁻¹ * k * z) hz hns (z⁻¹ * k' * z) hcomm

/-- The Frobenius matrix is not in K = 𝔽_{q²}×. If it were, then conjugation
by σ would be trivial on K, meaning α^q = α for all α ∈ 𝔽_{q²}×, which
contradicts [𝔽_{q²} : 𝔽_q] = 2. -/
private lemma Etingof.GL2.frobeniusMatrix_not_in_elliptic (hn : n ≠ 0)
    [Fintype (GaloisField p n)] :
    Etingof.GL2.frobeniusMatrix p n ∉ Etingof.GL2.ellipticSubgroup p n := by
  intro ⟨α, hα⟩
  -- If σ = embed(α), then for any β: σ⁻¹ embed(β) σ = embed(β^q)
  -- But also σ⁻¹ embed(β) σ = α⁻¹ β α (in K, which is commutative) = β
  -- So embed(β^q) = embed(β) for all β
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- fieldExtEmbed is injective
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  have hembed : ∀ (w : (GaloisField p (2 * n))ˣ),
      (Etingof.GL2.fieldExtEmbed p n w).val =
      Algebra.leftMulMatrix b (w : GaloisField p (2 * n)) := by
    intro w; simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; congr 1
  have hembed_inj : Function.Injective (Etingof.GL2.fieldExtEmbed p n) := by
    intro u v huv
    have hval : (Etingof.GL2.fieldExtEmbed p n u).val =
        (Etingof.GL2.fieldExtEmbed p n v).val := congr_arg Units.val huv
    rw [hembed u, hembed v] at hval
    exact Units.ext (Algebra.leftMulMatrix_injective b hval)
  -- For any β: σ⁻¹ embed(β) σ = embed(β^q) (by frobeniusMatrix_conj)
  -- But σ = embed(α), so σ⁻¹ embed(β) σ = embed(β) by commutativity of K
  -- Hence β^q = β
  have htriv : ∀ β : (GaloisField p (2 * n))ˣ,
      (β : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) = β := by
    intro β
    have hconj := Etingof.GL2.frobeniusMatrix_conj p n hn β
    rw [← hα] at hconj
    have hcomm : (Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
      Etingof.GL2.fieldExtEmbed p n β *
      Etingof.GL2.fieldExtEmbed p n α = Etingof.GL2.fieldExtEmbed p n β := by
      rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
    rw [hcomm] at hconj
    have := hembed_inj hconj
    simp only [Units.ext_iff] at this
    exact this.symm
  -- Convert to units: β^q = β as units
  have h_unit_eq : ∀ β : (GaloisField p (2 * n))ˣ,
      β ^ Fintype.card (GaloisField p n) = β := by
    intro β
    exact Units.val_injective (by rw [Units.val_pow_eq_pow_val]; exact htriv β)
  -- Every unit satisfies β^{q-1} = 1
  have h_pow_one : ∀ β : (GaloisField p (2 * n))ˣ,
      β ^ (Fintype.card (GaloisField p n) - 1) = 1 := by
    intro β
    have heq := h_unit_eq β
    rw [show Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p n) - 1 + 1 from
      (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm, pow_succ] at heq
    exact mul_right_cancel (by rw [one_mul]; exact heq)
  -- By forall_pow_eq_one_iff: q²-1 ∣ q-1
  have hdvd : Fintype.card (GaloisField p (2 * n)) - 1 ∣
      Fintype.card (GaloisField p n) - 1 :=
    (FiniteField.forall_pow_eq_one_iff
      (K := GaloisField p (2 * n)) (Fintype.card (GaloisField p n) - 1)).mp h_pow_one
  -- p^{2n} - 1 > p^n - 1, contradicting divisibility
  have hq := @GaloisField.card p _ n hn
  have hq2 := @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)
  simp only [Fintype.card_eq_nat_card] at hdvd
  rw [hq, hq2] at hdvd
  have hpn_ge : p ^ n ≥ 2 := by
    calc p ^ n ≥ 2 ^ n := Nat.pow_le_pow_left (Nat.Prime.two_le hp.out) n
      _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 := by norm_num
  have h2n : p ^ (2 * n) = p ^ n * p ^ n := by rw [two_mul, pow_add]
  have hgt : p ^ (2 * n) > p ^ n := by nlinarith
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- In F_{q²}/F_q, there exists a unit α whose embedding is non-scalar (i.e., α ∉ F_q). -/
private lemma Etingof.GL2.exists_nonscalar_elliptic (hn : n ≠ 0) :
    ∃ α : (GaloisField p (2 * n))ˣ,
      ¬GL2.IsScalar (p := p) (n := n) (Etingof.GL2.fieldExtEmbed p n α) := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  -- If all units had scalar embedding, then all of F_{q²} would be in range(algebraMap),
  -- making finrank = 1, contradicting finrank = 2
  by_contra h
  push_neg at h -- h : ∀ α, GL2.IsScalar (embed α)
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  have hembed : ∀ (u : (GaloisField p (2 * n))ˣ),
      (Etingof.GL2.fieldExtEmbed p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; congr 1
  -- Every nonzero x ∈ F_{q²} is in range(algebraMap)
  have h_all_in_range : ∀ x : GaloisField p (2 * n),
      x ∈ Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    · -- x ≠ 0, so x is a unit
      let α : (GaloisField p (2 * n))ˣ := Units.mk0 x hx
      have hscalar := h α
      rw [GL2.isScalar_iff] at hscalar
      -- IsScalar means leftMulMatrix is a scalar matrix
      -- So leftMulMatrix b x = diagonal (fun _ => c) for some c
      have hmat := hembed α
      -- The off-diagonal of leftMulMatrix b x is 0 and diagonals are equal
      -- This means x acts as scalar multiplication, so x = algebraMap c
      have h01 : (Algebra.leftMulMatrix b x) 0 1 = 0 := by
        have := hscalar.1; rwa [hembed] at this
      have h10 : (Algebra.leftMulMatrix b x) 1 0 = 0 := by
        have := hscalar.2.1; rwa [hembed] at this
      have h_diag : (Algebra.leftMulMatrix b x) 0 0 =
          (Algebra.leftMulMatrix b x) 1 1 := by
        have := hscalar.2.2; rwa [hembed] at this
      -- leftMulMatrix b x = diagonal (fun _ => c) where c = entry (0,0)
      set c := (Algebra.leftMulMatrix b x) 0 0
      have hmat_eq : Algebra.leftMulMatrix b x =
          (algebraMap (GaloisField p n)
            (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
        rw [Matrix.algebraMap_eq_diagonal]
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [c, h01, h10, h_diag, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
      -- leftMulMatrix is injective
      have := Algebra.leftMulMatrix_injective b
        (show Algebra.leftMulMatrix b x =
          Algebra.leftMulMatrix b (algebraMap (GaloisField p n) _ c) by
          rw [hmat_eq, (Algebra.leftMulMatrix b).commutes c])
      exact ⟨c, this.symm⟩
  -- algebraMap is surjective → finrank = 1
  have hsurj : Function.Surjective
      (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
    fun x => h_all_in_range x
  have : Module.finrank (GaloisField p n) (GaloisField p (2 * n)) ≤ 1 :=
    finrank_le_one (1 : GaloisField p (2 * n)) (fun w => by
      obtain ⟨c, hc⟩ := hsurj w
      exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)
  have := Etingof.finrank_galoisField_ext p n hn
  omega

/-- An element α is a root of the charpoly of its left multiplication matrix
(Cayley-Hamilton through the algebra embedding). -/
private lemma Etingof.GL2.isRoot_charpoly_leftMulMatrix (hn : n ≠ 0)
    (α : GaloisField p (2 * n)) :
    letI := Etingof.algebraGaloisFieldExt p n
    letI := Etingof.scalarTowerGaloisField p n
    haveI := Etingof.finiteDimensionalGaloisFieldExt p n
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    Polynomial.aeval α (Algebra.leftMulMatrix b α).charpoly = 0 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  apply Algebra.leftMulMatrix_injective b
  rw [map_zero, ← Polynomial.aeval_algHom_apply (Algebra.leftMulMatrix b)]
  exact Matrix.aeval_self_charpoly _

/-- Frobenius preserves roots of base-field polynomials. -/
private lemma Etingof.GL2.frobenius_root_of_basefield_poly (hn : n ≠ 0)
    [Fintype (GaloisField p n)]
    (α : GaloisField p (2 * n))
    (P : Polynomial (GaloisField p n))
    (hroot : Polynomial.aeval α P = 0) :
    Polynomial.aeval (α ^ Fintype.card (GaloisField p n)) P = 0 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))
  have hφ_eq : ∀ x : GaloisField p (2 * n),
      φ x = x ^ Fintype.card (GaloisField p n) := by
    intro x; exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) x
  have key : Polynomial.aeval (φ.toAlgHom α) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  convert key using 2

/-- A degree-2 polynomial has at most 2 roots: any root equals one of two known distinct roots. -/
private lemma Etingof.GL2.root_dichotomy_of_deg_two
    {R F : Type*} [Field R] [Field F] [Algebra R F]
    (P : Polynomial R) (hdeg : P.natDegree = 2)
    (a b c : F) (ha : Polynomial.aeval a P = 0) (hb : Polynomial.aeval b P = 0)
    (hc : Polynomial.aeval c P = 0) (hab : a ≠ b) :
    c = a ∨ c = b := by
  -- Map P to F[X]; the mapped polynomial Q has the same degree
  set Q := P.map (algebraMap R F) with hQ_def
  have hdQ : Q.natDegree = 2 := by rw [hQ_def, Polynomial.natDegree_map]; exact hdeg
  have hQ_ne : Q ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdQ; omega
  -- a, b, c are roots of Q
  have ha' : Q.IsRoot a := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact ha
  have hb' : Q.IsRoot b := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hb
  have hc' : Q.IsRoot c := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hc
  -- (X - a) and (X - b) divide Q and are coprime (since a ≠ b)
  have hda : (Polynomial.X - Polynomial.C a) ∣ Q := Polynomial.dvd_iff_isRoot.mpr ha'
  have hdb : (Polynomial.X - Polynomial.C b) ∣ Q := Polynomial.dvd_iff_isRoot.mpr hb'
  have hcop : IsCoprime (Polynomial.X - Polynomial.C a : Polynomial F)
      (Polynomial.X - Polynomial.C b) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  -- So (X - a)(X - b) | Q
  obtain ⟨r, hr⟩ := hcop.mul_dvd hda hdb
  -- r must be a nonzero constant since deg Q = deg (X-a)(X-b) = 2
  have hr_ne : r ≠ 0 := right_ne_zero_of_mul (hr ▸ hQ_ne)
  have hprod_ne : (Polynomial.X - Polynomial.C a) *
      (Polynomial.X - Polynomial.C b : Polynomial F) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero a) (Polynomial.X_sub_C_ne_zero b)
  have hr_deg : r.natDegree = 0 := by
    have hprod_deg : ((Polynomial.X - Polynomial.C a) *
        (Polynomial.X - Polynomial.C b) : Polynomial F).natDegree = 2 := by
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) (Polynomial.X_sub_C_ne_zero b)]
      simp [Polynomial.natDegree_X_sub_C]
    by_contra h
    have : Q.natDegree ≥ 3 := by
      rw [hr, Polynomial.natDegree_mul hprod_ne hr_ne, hprod_deg]; omega
    omega
  -- Evaluate Q at c: (c - a) * (c - b) * r(c) = 0
  have heval : (c - a) * (c - b) * r.eval c = 0 := by
    have := hc'
    rw [Polynomial.IsRoot, hr, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    exact this
  -- r(c) ≠ 0 since r is a nonzero constant
  have hr_eval_ne : r.eval c ≠ 0 := by
    have hk := Polynomial.eq_C_of_natDegree_eq_zero hr_deg
    rw [hk, Polynomial.eval_C]
    intro h; exact hr_ne (by rw [hk, h, map_zero])
  -- So (c - a) * (c - b) = 0, hence c = a or c = b
  have hab0 : (c - a) * (c - b) = 0 := by
    rcases mul_eq_zero.mp heval with h | h
    · exact h
    · exact absurd h hr_eval_ne
  rcases mul_eq_zero.mp hab0 with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

set_option maxHeartbeats 1600000 in
/-- Every element of the normalizer N_{GL₂}(K) is in K or in the Frobenius coset σK. -/
private lemma Etingof.GL2.normalizer_mem_dichotomy (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GaloisField p n)]
    (g : GL2 p n) (hg : Etingof.GL2.isInNormalizer p n g) :
    g ∈ Etingof.GL2.ellipticSubgroup p n ∨
    ∃ α : (GaloisField p (2 * n))ˣ,
      g = Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  have hembed : ∀ (u : (GaloisField p (2 * n))ˣ),
      (Etingof.GL2.fieldExtEmbed p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; congr 1
  -- Step 1: Find a non-scalar element of K
  obtain ⟨α₀, hα₀_ns⟩ := Etingof.GL2.exists_nonscalar_elliptic p n hn
  -- Step 2: g conjugates embed(α₀) into K
  have hconj := hg (Etingof.GL2.fieldExtEmbed p n α₀) ⟨α₀, rfl⟩
  obtain ⟨β, hβ⟩ := hconj
  -- Step 3: charpoly is preserved by conjugation
  set P := (Algebra.leftMulMatrix b (α₀ : GaloisField p (2 * n))).charpoly
  have hcharpoly_eq : (Algebra.leftMulMatrix b (β : GaloisField p (2 * n))).charpoly = P := by
    have hval : Algebra.leftMulMatrix b (β : GaloisField p (2 * n)) =
        g.inv * Algebra.leftMulMatrix b (α₀ : GaloisField p (2 * n)) * g.val := by
      have h1 := hembed β; have h2 := hembed α₀
      rw [← h1, ← h2, hβ]; simp [Units.val_mul]
    rw [hval]
    exact Matrix.charpoly_units_conj' g _
  -- Step 4: α₀ and β are roots of P, and α₀^q is also a root
  have hα₀_root : Polynomial.aeval (α₀ : GaloisField p (2 * n)) P = 0 :=
    Etingof.GL2.isRoot_charpoly_leftMulMatrix p n hn ↑α₀
  have hβ_root : Polynomial.aeval (β : GaloisField p (2 * n)) P = 0 := by
    rw [show P = (Algebra.leftMulMatrix b (β : GaloisField p (2 * n))).charpoly from
      hcharpoly_eq.symm]
    exact Etingof.GL2.isRoot_charpoly_leftMulMatrix p n hn ↑β
  set q := Fintype.card (GaloisField p n)
  have hαq_root : Polynomial.aeval ((α₀ : GaloisField p (2 * n)) ^ q) P = 0 :=
    Etingof.GL2.frobenius_root_of_basefield_poly p n hn ↑α₀ P hα₀_root
  -- Step 5: P has degree 2
  have hdeg : P.natDegree = 2 := by
    change (Algebra.leftMulMatrix b (↑α₀ : GaloisField p (2 * n))).charpoly.natDegree = 2
    rw [Matrix.charpoly_natDegree_eq_dim]; simp [Fintype.card_fin]
  -- Step 6: α₀ ≠ α₀^q (non-scalar ↔ α₀ ∉ F_q)
  have hne : (α₀ : GaloisField p (2 * n)) ≠ (α₀ : GaloisField p (2 * n)) ^ q := by
    -- α₀^q = α₀ would mean α₀ ∈ F_q, making embed(α₀) scalar, contradicting hα₀_ns
    intro heq
    apply hα₀_ns
    -- heq means Frobenius fixes α₀
    let φ := FiniteField.frobeniusAlgEquivOfAlgebraic
        (GaloisField p n) (GaloisField p (2 * n))
    have hφ_fix : φ (↑α₀) = ↑α₀ := by
      rw [show (φ : GaloisField p (2 * n) → GaloisField p (2 * n)) (↑α₀) = (↑α₀) ^ q from
        congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) _]
      exact heq.symm
    -- φ ≠ 1 (extension is non-trivial, degree 2)
    have hφ_ne_one : φ ≠ 1 := by
      intro h
      -- Frobenius powers biject Fin(finrank) → Gal; φ = 1 makes the map constant,
      -- contradicting injectivity when finrank = 2
      have hbij := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (GaloisField p n) (GaloisField p (2 * n))
      rw [Etingof.finrank_galoisField_ext p n hn] at hbij
      exact absurd (hbij.1 (show φ ^ (0 : Fin 2).1 = φ ^ (1 : Fin 2).1 by simp [h]))
        (by decide)
    -- |Gal| = 2 and φ ≠ 1 means every f ∈ Gal is either 1 or φ
    have hcard_gal : Nat.card (GaloisField p (2 * n) ≃ₐ[GaloisField p n]
        GaloisField p (2 * n)) = 2 :=
      (IsGalois.card_aut_eq_finrank (GaloisField p n) (GaloisField p (2 * n))).trans
        (Etingof.finrank_galoisField_ext p n hn)
    have hall_fix : ∀ f : (GaloisField p (2 * n) ≃ₐ[GaloisField p n] GaloisField p (2 * n)),
        f (↑α₀ : GaloisField p (2 * n)) = ↑α₀ := by
      intro f
      -- In a type of card 2, with a distinguished element 1, the only other element is φ
      obtain ⟨y, hy_ne, hy_unique⟩ :=
        (Nat.card_eq_two_iff' (1 : GaloisField p (2 * n) ≃ₐ[GaloisField p n]
          GaloisField p (2 * n))).mp hcard_gal
      by_cases hf : f = 1
      · rw [hf]; simp
      · -- f ≠ 1, so f = y; φ ≠ 1, so φ = y; hence f = φ
        have hfy : f = y := hy_unique f hf
        have hφy : φ = y := hy_unique φ hφ_ne_one
        rw [hfy, ← hφy]; exact hφ_fix
    -- α₀ ∈ range(algebraMap) by Galois theory
    have h_in_range : (↑α₀ : GaloisField p (2 * n)) ∈
        Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := GaloisField p n) (E := GaloisField p (2 * n)) (↑α₀)).mpr hall_fix
    -- α₀ ∈ F_q implies embed(α₀) is scalar
    obtain ⟨c, hc⟩ := h_in_range
    rw [GL2.isScalar_iff]
    have hscalar : Algebra.leftMulMatrix b (↑α₀ : GaloisField p (2 * n)) =
        (algebraMap (GaloisField p n) (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
      rw [← hc]; exact (Algebra.leftMulMatrix b).commutes c
    rw [hembed α₀, hscalar, Matrix.algebraMap_eq_diagonal]
    exact ⟨Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
           Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
           by simp [Matrix.diagonal_apply_eq]⟩
  -- Step 7: β ∈ {α₀, α₀^q} by root dichotomy
  have hβ_dichotomy : (β : GaloisField p (2 * n)) = ↑α₀ ∨
      (β : GaloisField p (2 * n)) = (↑α₀ : GaloisField p (2 * n)) ^ q :=
    Etingof.GL2.root_dichotomy_of_deg_two (F := GaloisField p (2 * n))
      P hdeg (↑α₀) ((↑α₀) ^ q) (↑β) hα₀_root hαq_root hβ_root hne
  -- Step 8: Case split
  rcases hβ_dichotomy with hβ_eq_α | hβ_eq_αq
  · -- Case β = α₀: g commutes with embed(α₀), so g ∈ K by centralizer theorem
    left
    have hβα : β = α₀ := Units.val_injective hβ_eq_α
    rw [hβα] at hβ
    -- hβ : fieldExtEmbed α₀ = g⁻¹ * fieldExtEmbed α₀ * g
    have hcomm : g * Etingof.GL2.fieldExtEmbed p n α₀ =
        Etingof.GL2.fieldExtEmbed p n α₀ * g := by
      -- hβ : fieldExtEmbed α₀ = g⁻¹ * fieldExtEmbed α₀ * g
      calc g * Etingof.GL2.fieldExtEmbed p n α₀
          = g * (g⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * g) :=
            congr_arg (g * ·) hβ
        _ = Etingof.GL2.fieldExtEmbed p n α₀ * g := by group
    exact Etingof.centralizer_nonscalar_elliptic p n hn
      (Etingof.GL2.fieldExtEmbed p n α₀) ⟨α₀, rfl⟩ hα₀_ns g hcomm
  · -- Case β = α₀^q: gσ⁻¹ centralizes embed(α₀), so gσ⁻¹ ∈ K, giving g ∈ σK
    right
    -- embed(β) = g⁻¹ embed(α₀) g = embed(α₀^q) = σ⁻¹ embed(α₀) σ
    -- So (gσ⁻¹)⁻¹ embed(α₀) (gσ⁻¹) = embed(α₀)
    -- i.e., gσ⁻¹ commutes with embed(α₀)
    -- By centralizer theorem, gσ⁻¹ ∈ K
    set σ := Etingof.GL2.frobeniusMatrix p n
    -- β as a unit equals the Frobenius-applied unit
    set α₀q_unit : (GaloisField p (2 * n))ˣ :=
      ⟨(↑α₀ : GaloisField p (2 * n)) ^ q,
       (↑α₀⁻¹ : GaloisField p (2 * n)) ^ q,
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, mul_inv_cancel₀ α₀.ne_zero],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, inv_mul_cancel₀ α₀.ne_zero]⟩
    have hβ_eq_αq_unit : β = α₀q_unit := Units.val_injective hβ_eq_αq
    -- embed(α₀^q) = σ⁻¹ embed(α₀) σ (by frobeniusMatrix_conj)
    have hfrob_conj := Etingof.GL2.frobeniusMatrix_conj p n hn α₀
    -- So g⁻¹ embed(α₀) g = σ⁻¹ embed(α₀) σ
    have hconj_eq : g⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * g =
        σ⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * σ := by
      have hfrob := Etingof.GL2.frobeniusMatrix_conj p n hn α₀
      -- hfrob : frobeniusMatrix⁻¹ * embed(α₀) * frobeniusMatrix = embed(⟨α₀^q, ...⟩)
      calc g⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * g
          = Etingof.GL2.fieldExtEmbed p n β := hβ.symm
        _ = Etingof.GL2.fieldExtEmbed p n α₀q_unit :=
            congr_arg _ hβ_eq_αq_unit
        _ = (Etingof.GL2.frobeniusMatrix p n)⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ *
            Etingof.GL2.frobeniusMatrix p n := by
          convert hfrob.symm using 2; exact Units.ext rfl
    -- Therefore σg⁻¹ commutes with embed(α₀), or equivalently gσ⁻¹ commutes with embed(α₀)
    have hcomm : g * σ⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ =
        Etingof.GL2.fieldExtEmbed p n α₀ * (g * σ⁻¹) := by
      -- From hconj_eq: g⁻¹ embed(α₀) g = σ⁻¹ embed(α₀) σ
      -- Multiply left by g, right by σ⁻¹:
      -- embed(α₀) g σ⁻¹ = g σ⁻¹ embed(α₀)
      have := congr_arg (g * · * σ⁻¹) hconj_eq
      simp only [] at this
      rw [show g * (g⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * g) * σ⁻¹ =
          Etingof.GL2.fieldExtEmbed p n α₀ * (g * σ⁻¹) from by group,
        show g * (σ⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ * σ) * σ⁻¹ =
          g * σ⁻¹ * Etingof.GL2.fieldExtEmbed p n α₀ from by group] at this
      exact this.symm
    -- gσ⁻¹ ∈ K
    have hgσ_inv_mem : g * σ⁻¹ ∈ Etingof.GL2.ellipticSubgroup p n :=
      Etingof.centralizer_nonscalar_elliptic p n hn
        (Etingof.GL2.fieldExtEmbed p n α₀) ⟨α₀, rfl⟩ hα₀_ns (g * σ⁻¹) hcomm
    -- g * σ⁻¹ = embed(γ) for some γ
    obtain ⟨γ, hγ⟩ := hgσ_inv_mem
    -- g = embed(γ) * σ = σ * embed(γ^q) (using σ embed(γ^q) = embed(γ) σ)
    have hg_eq : g = Etingof.GL2.fieldExtEmbed p n γ * σ := by
      calc g = g * σ⁻¹ * σ := by group
        _ = Etingof.GL2.fieldExtEmbed p n γ * σ := by rw [hγ]
    -- embed(γ) * σ = σ * embed(γ^q)
    -- From frobeniusMatrix_conj: σ⁻¹ embed(γ) σ = embed(γ^q)
    -- So embed(γ) = σ embed(γ^q) σ⁻¹, and embed(γ) σ = σ embed(γ^q)
    set γq_unit : (GaloisField p (2 * n))ˣ :=
      ⟨(↑γ : GaloisField p (2 * n)) ^ q,
       (↑γ⁻¹ : GaloisField p (2 * n)) ^ q,
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, mul_inv_cancel₀ γ.ne_zero],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, inv_mul_cancel₀ γ.ne_zero]⟩
    refine ⟨γq_unit, ?_⟩
    rw [hg_eq]
    -- embed(γ) * σ = σ * embed(γ^q)
    have hfrob_γ := Etingof.GL2.frobeniusMatrix_conj p n hn γ
    -- hfrob_γ : σ⁻¹ embed(γ) σ = embed(γ^q)
    -- σ * embed(γ^q) = σ * σ⁻¹ * embed(γ) * σ = embed(γ) * σ ✓
    change Etingof.GL2.fieldExtEmbed p n γ * Etingof.GL2.frobeniusMatrix p n =
      Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n γq_unit
    calc Etingof.GL2.fieldExtEmbed p n γ * Etingof.GL2.frobeniusMatrix p n
        = Etingof.GL2.frobeniusMatrix p n *
          ((Etingof.GL2.frobeniusMatrix p n)⁻¹ * Etingof.GL2.fieldExtEmbed p n γ *
           Etingof.GL2.frobeniusMatrix p n) := by group
      _ = Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n γq_unit := by
          congr 1; convert hfrob_γ using 2; exact Units.ext rfl

/-- The cardinality of the normalizer: |N_{GL₂}(K)| = 2|K|.
  Proof sketch: N(K) = K ∪ σK (by `normalizer_mem_dichotomy`), the union is disjoint
  (since σ ∉ K by `frobeniusMatrix_not_in_elliptic`), and |σK| = |K| by left-multiplication
  bijection. -/
lemma Etingof.GL2.normalizer_card (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GL2 p n)] [Fintype (Etingof.GL2.ellipticSubgroup p n)]
    [DecidablePred (Etingof.GL2.isInNormalizer p n)] :
    (Finset.univ.filter (fun g : GL2 p n =>
      Etingof.GL2.isInNormalizer p n g)).card =
    2 * Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) := by
  sorry

end Normalizer
