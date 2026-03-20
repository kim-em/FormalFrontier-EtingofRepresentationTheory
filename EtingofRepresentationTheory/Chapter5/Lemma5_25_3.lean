import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2ConjugacyClasses

/-!
# Lemma 5.25.3: Complementary Series Character Properties

For the virtual representation χ defined in the construction of
complementary series representations of GL₂(𝔽_q):
- ⟨χ, χ⟩ = 1
- χ(1) = q - 1 > 0

These properties establish that χ is the character of an actual
irreducible representation (of dimension q - 1).

The virtual character is defined as:
  χ = char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
where K ⊂ GL₂(𝔽_q) is the cyclic subgroup of multiplications by
elements of 𝔽_{q²}×, ν : K → ℂ× satisfies ν^q ≠ ν, and α = ν|_{𝔽_q×}.

## Mathlib correspondence

Uses `GaloisField` and character inner product theory.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section FieldExtInfrastructure

open Polynomial

/-- X^(p^n) - X divides X^(p^(2n)) - X in characteristic p.
Proof: (X^(p^n) - X)^(p^n) = X^(p^(2n)) - X^(p^n) by Freshman's dream,
so X^(p^(2n)) - X = (X^(p^n) - X)^(p^n) + (X^(p^n) - X). -/
private lemma Etingof.dvd_X_pow_sub_X :
    (X ^ p ^ n - X : (ZMod p)[X]) ∣ (X ^ p ^ (2 * n) - X : (ZMod p)[X]) := by
  set f := (X ^ p ^ n - X : (ZMod p)[X])
  have key : f ^ p ^ n = X ^ p ^ (2 * n) - X ^ p ^ n := by
    change (X ^ p ^ n - X) ^ p ^ n = X ^ p ^ (2 * n) - X ^ p ^ n
    rw [sub_pow_char_pow (p := p)]
    congr 1
    rw [← pow_mul, ← Nat.pow_add]
    ring_nf
  have decomp : X ^ p ^ (2 * n) - X = f ^ p ^ n + f := by
    rw [key]; ring
  rw [decomp]
  exact dvd_add (dvd_pow_self f (pow_ne_zero n hp.out.pos.ne')) dvd_rfl

/-- X^(p^n) - X splits in GaloisField p (2*n) because it divides X^(p^(2n)) - X
which splits there. -/
private lemma Etingof.splits_X_pow_sub_X :
    Splits (map (algebraMap (ZMod p) (GaloisField p (2 * n))) (X ^ p ^ n - X)) := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.mul_zero, pow_zero, pow_one, sub_self, Polynomial.map_zero]
    exact Polynomial.Splits.zero
  · haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
    have hsplits : Splits (map (algebraMap (ZMod p) (GaloisField p (2 * n)))
        (X ^ p ^ (2 * n) - X)) := by
      have hcard : Nat.card (GaloisField p (2 * n)) = p ^ (2 * n) :=
        GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)
      rw [show p ^ (2 * n) = Fintype.card (GaloisField p (2 * n)) from by
        rw [Nat.card_eq_fintype_card] at hcard; omega]
      exact @FiniteField.splits_X_pow_card_sub_X p hp _ _ _ _
    have hne : (X ^ p ^ (2 * n) - X : (ZMod p)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p)
        (Nat.mul_ne_zero two_ne_zero hn) hp.out.one_lt
    exact hsplits.of_dvd (map_ne_zero hne) (map_dvd _ (Etingof.dvd_X_pow_sub_X p n))

/-- The algebra homomorphism GaloisField p n →ₐ[ZMod p] GaloisField p (2*n)
obtained from IsSplittingField.lift. -/
private noncomputable def Etingof.galoisFieldAlgHom :
    GaloisField p n →ₐ[ZMod p] GaloisField p (2 * n) :=
  IsSplittingField.lift (GaloisField p n) (X ^ p ^ n - X)
    (Etingof.splits_X_pow_sub_X p n)

/-- Algebra instance for GaloisField p (2*n) over GaloisField p n. -/
private noncomputable instance Etingof.algebraGaloisFieldExt :
    Algebra (GaloisField p n) (GaloisField p (2 * n)) :=
  (Etingof.galoisFieldAlgHom p n).toRingHom.toAlgebra

/-- The scalar tower ZMod p → GaloisField p n → GaloisField p (2*n). -/
private noncomputable instance Etingof.scalarTowerGaloisField :
    IsScalarTower (ZMod p) (GaloisField p n) (GaloisField p (2 * n)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change (algebraMap (ZMod p) (GaloisField p (2 * n))) r =
      (Etingof.galoisFieldAlgHom p n).toRingHom
        ((algebraMap (ZMod p) (GaloisField p n)) r)
    exact ((Etingof.galoisFieldAlgHom p n).commutes r).symm

/-- GaloisField p (2*n) is finite-dimensional over GaloisField p n. -/
private noncomputable instance Etingof.finiteDimensionalGaloisFieldExt :
    FiniteDimensional (GaloisField p n) (GaloisField p (2 * n)) := by
  haveI : FiniteDimensional (ZMod p) (GaloisField p (2 * n)) := inferInstance
  exact FiniteDimensional.right (ZMod p) (GaloisField p n) (GaloisField p (2 * n))

/-- The degree of GaloisField p (2*n) over GaloisField p n is 2 (when n > 0). -/
private lemma Etingof.finrank_galoisField_ext (hn : n ≠ 0) :
    Module.finrank (GaloisField p n) (GaloisField p (2 * n)) = 2 := by
  have h1 := GaloisField.finrank p (show n ≠ 0 from hn)
  have h2 := GaloisField.finrank p (show 2 * n ≠ 0 from Nat.mul_ne_zero two_ne_zero hn)
  have htower := Module.finrank_mul_finrank (ZMod p) (GaloisField p n)
    (GaloisField p (2 * n))
  rw [h1, h2] at htower
  -- htower : n * finrank = 2 * n
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  nlinarith

end FieldExtInfrastructure

/-- The embedding of 𝔽_{q²}× into GL₂(𝔽_q) via the left regular representation
on a chosen basis of the degree-2 field extension 𝔽_{q²}/𝔽_q. -/
private noncomputable def Etingof.GL2.fieldExtEmbed :
    (GaloisField p (2 * n))ˣ →* GL2 p n := by
  by_cases hn : n = 0
  · -- Degenerate case: n = 0, both fields have 1 element
    exact 1
  · -- Main case: use left multiplication matrix representation
    letI := Etingof.algebraGaloisFieldExt p n
    letI := Etingof.scalarTowerGaloisField p n
    haveI := Etingof.finiteDimensionalGaloisFieldExt p n
    -- Construct Fin 2-indexed basis via finrank = 2
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    let matRepr := Algebra.leftMulMatrix b
    -- matRepr is an algebra hom: lift to units
    exact
      { toFun := fun u =>
          ⟨matRepr u, matRepr ↑u⁻¹, by
            rw [← map_mul, Units.mul_inv, map_one],
           by rw [← map_mul, Units.inv_mul, map_one]⟩
        map_one' := Units.ext (map_one matRepr)
        map_mul' := fun a b => Units.ext (by simp [map_mul]) }

/-- The cyclic subgroup K ⊂ GL₂(𝔽_q) corresponding to multiplication by
elements of 𝔽_{q²}× (embedded via the basis {1, √ε}). -/
noncomputable def Etingof.GL2.ellipticSubgroup : Subgroup (GL2 p n) :=
  (Etingof.GL2.fieldExtEmbed p n).range

/-- Embedding of scalar matrices 𝔽_q× ↪ K via a ↦ embed(algebraMap a). -/
private noncomputable def Etingof.GL2.scalarToElliptic :
    (GaloisField p n)ˣ →* ↥(Etingof.GL2.ellipticSubgroup p n) := by
  by_cases hn : n = 0
  · exact 1
  · letI := Etingof.algebraGaloisFieldExt p n
    -- Map a : (GaloisField p n)ˣ to algebraMap a : (GaloisField p (2*n))ˣ
    -- then apply fieldExtEmbed
    refine (Etingof.GL2.fieldExtEmbed p n).codRestrict
      (Etingof.GL2.ellipticSubgroup p n) ?_ |>.comp ?_
    · intro x; exact ⟨x, rfl⟩
    · -- Units.map of algebraMap
      exact Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom

/-- Character of W₁, the q-dimensional irreducible complement in V(1,1).
W₁ is the complement of the trivial representation in the permutation representation
on P¹(𝔽_q). Its character equals (number of fixed points on P¹) - 1.

A point [1:t] ∈ P¹ is fixed by matrix M iff M₀₁t² + (M₀₀ - M₁₁)t - M₁₀ = 0.
The point [0:1] is fixed iff M₀₁ = 0. -/
private noncomputable def Etingof.GL2.charW₁
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] : GL2 p n → ℂ :=
  fun g =>
    let M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    -- Count fixed points on the affine chart [1:t]
    let fixedAffine := Finset.univ.filter fun (t : GaloisField p n) =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0
    -- Check if the point at infinity [0:1] is fixed
    let fixedInfty : ℕ := if M 0 1 = 0 then 1 else 0
    ((fixedAffine.card + fixedInfty : ℕ) : ℂ) - 1

/-- Character of the principal series representation V(α, 1) of GL₂(𝔽_q).
V(α, 1) = Ind_B^G(α ⊗ 1) where B is the Borel subgroup (upper triangular matrices).
By Frobenius reciprocity, char(V(α,1))(g) = (1/|B|) ∑_{x : x⁻¹gx ∈ B} α(upper-left of x⁻¹gx). -/
private noncomputable def Etingof.GL2.charVα₁
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ) : GL2 p n → ℂ :=
  fun g =>
    -- Frobenius character formula for induced representation
    -- sum over x ∈ G of (indicator that x⁻¹gx is upper triangular) * α(upper-left entry)
    let borelCard : ℂ := ((Fintype.card (GaloisField p n) - 1) ^ 2 *
      Fintype.card (GaloisField p n) : ℕ)
    borelCard⁻¹ * ∑ x : GL2 p n,
      let conj := (x⁻¹ * g * x : GL2 p n)
      let M := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n))
      if M 1 0 = 0 then
        -- x⁻¹gx is upper triangular; extract upper-left entry as a unit
        if h : M 0 0 ≠ 0 then
          (alpha (Units.mk0 (M 0 0) h) : ℂ)
        else 0
      else 0

open Classical in
/-- The complementary series virtual character of GL₂(𝔽_q), defined as
char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
where ν : K → ℂ× with ν^q ≠ ν and α = ν|_{scalars}. -/
noncomputable def Etingof.GL2.complementarySeriesChar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    GL2 p n → ℂ :=
  let K := Etingof.GL2.ellipticSubgroup p n
  let alpha : (GaloisField p n)ˣ →* ℂˣ := nu.comp (Etingof.GL2.scalarToElliptic p n)
  fun g =>
    -- char(W₁ ⊗ V_{α,1})(g) = char(W₁)(g) · char(V_{α,1})(g)
    Etingof.GL2.charW₁ p n g * Etingof.GL2.charVα₁ p n alpha g
    -- minus char(V_{α,1})(g)
    - Etingof.GL2.charVα₁ p n alpha g
    -- minus char(Ind_K^G ℂ_ν)(g) via Frobenius character formula
    - (Fintype.card ↥K : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ K
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0

/-! ### Character value lemmas on each conjugacy class type

From Discussion 5.25.4, the complementary series virtual character
χ = char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
has the following values:
- Scalar xI: χ(xI) = (q-1)α(x)
- Parabolic [[x,1],[0,x]]: χ = -α(x)
- Hyperbolic diag(x,y), x≠y: χ = 0
- Elliptic ζ ∈ K\F_q×: χ = -(ν(ζ) + ν^q(ζ))
-/

section LeftMulHelper

variable {R' A' ι' : Type*} [CommRing R'] [CommRing A'] [Algebra R' A']
    [Fintype ι'] [DecidableEq ι']

/-- leftMulMatrix of algebraMap r is the scalar matrix r. -/
private lemma Etingof.leftMulMatrix_algebraMap
    (b : Module.Basis ι' R' A') (r : R') :
    Algebra.leftMulMatrix b (algebraMap R' A' r) = Matrix.scalar _ r := by
  ext i j
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Matrix.scalar_apply]
  rw [show (Algebra.lmul R' A') (algebraMap R' A' r) (b j) = r • b j from by
    simp [Algebra.smul_def]]
  simp [Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply, eq_comm]

end LeftMulHelper

/-- For n ≠ 0, fieldExtEmbed of a scalar (algebraMap) element is the scalar matrix. -/
private lemma Etingof.fieldExtEmbed_algebraMap_val (hn : n ≠ 0)
    (a : (GaloisField p n)ˣ) :
    (Etingof.GL2.fieldExtEmbed p n
      (Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom a)).val =
    Matrix.diagonal (fun _ : Fin 2 => (a : GaloisField p n)) := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn, MonoidHom.mk'_apply,
             Units.val_mk, Units.map, MonoidHom.coe_mk, OneHom.coe_mk,
             RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact Etingof.leftMulMatrix_algebraMap _ (a : GaloisField p n)

/-- Scalar matrix g = fieldExtEmbed(algebraMap(g₀₀)) when g is scalar and n ≠ 0. -/
private lemma Etingof.scalar_eq_fieldExtEmbed (hn : n ≠ 0)
    (g : GL2 p n) (h01 : g.val 0 1 = 0) (h10 : g.val 1 0 = 0)
    (h00 : g.val 0 0 = g.val 1 1) (hne : g.val 0 0 ≠ 0) :
    g = Etingof.GL2.fieldExtEmbed p n
      (Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom
        (Units.mk0 (g.val 0 0) hne)) := by
  apply Units.ext
  rw [Etingof.fieldExtEmbed_algebraMap_val p n hn]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, h01, h10, h00]

section CharacterValues

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- On scalar matrices, |χ(xI)|² = (q-1)². Since χ(xI) = (q-1)α(x) and
|α(x)| = 1 (α is a character to ℂˣ, landing on roots of unity). -/
private lemma Etingof.normSq_complementaryChar_scalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (hn : n ≠ 0) :
    Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
  obtain ⟨h01, h10, h00⟩ := hg
  -- Scalar matrices commute with everything: x⁻¹gx = g
  have hcomm : ∀ x : GL2 p n, x⁻¹ * g * x = g := by
    intro x
    have : g * x = x * g := by
      ext i j; simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, mul_comm]
    rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
  -- g₀₀ is nonzero (g is invertible, det = g₀₀²)
  have hg00_ne : g.val 0 0 ≠ 0 := by
    intro h0
    have hdet : Matrix.det g.val = 0 := by
      rw [Matrix.det_fin_two]; simp only [h01, h10, ← h00, h0]; ring
    have hmul : g.val * (g⁻¹ : GL2 p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2 p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  -- The key computation: χ(scalar g) = (q-1) * α(g₀₀)
  -- where α = nu ∘ scalarToElliptic
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  set q : ℂ := (Fintype.card (GaloisField p n) : ℂ)
  -- Factor: χ(g) = (q-1) * c where c is a unit in ℂ
  -- Then |χ|² = (q-1)² * |c|² = (q-1)² since |c| = 1
  set c := (alpha (Units.mk0 (g.val 0 0) hg00_ne) : ℂ) with hc_def
  suffices hval : Etingof.GL2.complementarySeriesChar p n nu g = (q - 1) * c by
    rw [hval]
    -- |c|² = 1 since alpha maps to roots of unity
    have hnorm : c * starRingEnd ℂ c = 1 := by
      rw [Complex.mul_conj]
      have h1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
        (show c ^ Fintype.card (GaloisField p n)ˣ = 1 from by
          rw [hc_def, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one,
              Units.val_one])
        Fintype.card_pos.ne'
      rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_cast]
      congr 1; rw [Complex.normSq_eq_norm_sq, h1, one_pow]
    -- conj(q-1) = q-1 since it's real
    have hreal : starRingEnd ℂ (q - 1) = q - 1 := by
      simp [q, map_sub, map_natCast, map_one]
    rw [map_mul, hreal, sq]
    linear_combination (q - 1) * (q - 1) * hnorm
  -- Now prove: complementarySeriesChar p n nu g = (q - 1) * c
  -- Step 1: Compute charW₁(g) = q
  -- Normalize the GL2.mat coercion to g.val
  change g.val 0 1 = 0 at h01
  change g.val 1 0 = 0 at h10
  change g.val 0 0 = g.val 1 1 at h00
  have hW : Etingof.GL2.charW₁ p n g = q := by
    simp only [Etingof.GL2.charW₁]
    -- All affine points are fixed: 0*t²+0*t-0 = 0
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        g.val 0 1 * t ^ 2 + (g.val 0 0 - g.val 1 1) * t - g.val 1 0 = 0) = Finset.univ := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h01, h10, h00, sub_self]; ring
    rw [hfilt, Finset.card_univ]
    simp only [h01, ite_true]; push_cast; ring
  -- Step 2: Show g ∈ K via scalar_eq_fieldExtEmbed
  have hg_mem : g ∈ Etingof.GL2.ellipticSubgroup p n := by
    rw [Etingof.scalar_eq_fieldExtEmbed p n hn g h01 h10 h00 hg00_ne]
    exact ⟨_, rfl⟩
  -- Step 3: scalarToElliptic(Units.mk0 g₀₀ _) = ⟨g, hg_mem⟩ in K
  have hscalar_K : (Etingof.GL2.scalarToElliptic p n (Units.mk0 (g.val 0 0) hg00_ne) : GL2 p n) = g := by
    -- scalarToElliptic(x).val = fieldExtEmbed(algebraMap(x))
    -- = g by scalar_eq_fieldExtEmbed
    simp only [Etingof.GL2.scalarToElliptic, dif_neg hn,
               MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
    exact (Etingof.scalar_eq_fieldExtEmbed p n hn g h01 h10 h00 hg00_ne).symm
  -- Step 4: nu(⟨g, hg_mem⟩) = alpha(g₀₀ as unit) = c
  have hnu_g : (nu ⟨g, hg_mem⟩).val = c := by
    have key : (⟨g, hg_mem⟩ : ↥(Etingof.GL2.ellipticSubgroup p n)) =
        Etingof.GL2.scalarToElliptic p n (Units.mk0 (g.val 0 0) hg00_ne) := by
      exact Subtype.ext hscalar_K.symm
    rw [key]; rfl
  -- Step 5: Compute charVα₁(alpha, g) using constant sum
  have hV : Etingof.GL2.charVα₁ p n alpha g =
      (((Fintype.card (GaloisField p n) - 1) ^ 2 *
        Fintype.card (GaloisField p n) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (GL2 p n) : ℂ) * c) := by
    unfold Etingof.GL2.charVα₁
    congr 1
    have : ∀ x : GL2 p n,
        (let conj := (x⁻¹ * g * x : GL2 p n);
         let M := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n));
         if M 1 0 = 0 then
           if h : M 0 0 ≠ 0 then (alpha (Units.mk0 (M 0 0) h) : ℂ) else 0
         else 0) = c := by
      intro x; simp only [hcomm x, h10, ite_true]; rw [dif_pos hg00_ne]
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  classical
  -- Step 6: Compute the induced character sum
  have hInd : (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
      ∑ x : GL2 p n,
        (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
         then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
      (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
      ((Fintype.card (GL2 p n) : ℂ) * c) := by
    congr 1
    have : ∀ x : GL2 p n,
        (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
         then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) = c := by
      intro x
      simp only [hcomm x]
      rw [dif_pos hg_mem, hnu_g]
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Step 7: Combine: χ(g) = charW₁ * charVα₁ - charVα₁ - Ind
  show Etingof.GL2.complementarySeriesChar p n nu g = (q - 1) * c
  unfold Etingof.GL2.complementarySeriesChar
  -- Replace charW₁ with q
  rw [hW]
  -- Replace all x⁻¹gx with g inside the sums
  simp_rw [hcomm]
  -- Simplify if/dif conditions for scalar g
  simp only [h10, ite_true, dif_pos hg00_ne, dif_pos hg_mem, hnu_g]
  -- Both sums are now constant: ∑ x, c = |G| * c
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Now prove the arithmetic identity
  -- The goal has the form: q * (B⁻¹ * (G * c)) - B⁻¹ * (G * c) - K_raw⁻¹ * (G * c) = (q-1)*c
  -- where B, G are Fintype.card casts and K_raw is a Fintype.card with a different instance
  -- Use the standalone arithmetic identity
  have hn_ne := hn
  set qq := Fintype.card (GaloisField p n) with hqq_def
  have hq1 : 1 < qq := by
    rw [hqq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    exact Nat.one_lt_pow hn_ne hp.out.one_lt
  have h1 : 1 ≤ qq := by omega
  have h2 : 1 ≤ qq ^ 2 := by nlinarith
  have h3 : qq ≤ qq ^ 2 := by nlinarith
  have hq_ne : (qq : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqm1_ne : (qq : ℂ) - 1 ≠ 0 := by
    intro h; have : (qq : ℕ) = 1 := by exact_mod_cast sub_eq_zero.mp h
    omega
  have hqp1_ne : (qq : ℂ) + 1 ≠ 0 := by
    have : ((qq + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at this; exact this
  -- Convert all Fintype.card casts to Nat.card casts (instance-independent)
  simp only [← Nat.card_eq_fintype_card]
  -- Now goal is in terms of Nat.card, which is instance-independent
  -- Compute cardinalities
  have hG_val : Nat.card (GL2 p n) = (qq ^ 2 - 1) * (qq ^ 2 - qq) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [this, Nat.card_eq_fintype_card]
  have hK_val : Nat.card ↥(Etingof.GL2.ellipticSubgroup p n) = qq ^ 2 - 1 := by
    have hinj : Function.Injective (Etingof.GL2.fieldExtEmbed p n) := by
      intro a b hab
      unfold Etingof.GL2.fieldExtEmbed at hab
      simp only [dif_neg hn_ne] at hab
      have hval := congr_arg (fun g => g.val) hab
      have := RingHom.injective
        (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
        (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn_ne))).toRingHom
      exact Units.ext (this hval)
    change Nat.card ↥(Etingof.GL2.fieldExtEmbed p n).range = _
    rw [show Nat.card ↥(Etingof.GL2.fieldExtEmbed p n).range =
      Nat.card ↥(Set.range (Etingof.GL2.fieldExtEmbed p n)) from by congr 1]
    rw [Nat.card_range_of_injective hinj, Nat.card_units,
        GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn_ne),
        hqq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    -- Goal: p^(2*n) - 1 = (p^n)^2 - 1
    rw [sq, ← pow_add, show n + n = 2 * n from by omega]
  -- Goal: q * charVα₁ ... - charVα₁ ... - K⁻¹ * (G * c) = (q-1) * c
  -- where K, G are Nat.card based.
  -- Substitute charVα₁ using hV (which is Fintype.card based)
  rw [hV]
  -- Now goal has B⁻¹, G (Fintype.card based) and Nat.card terms
  -- Convert everything to Nat.card
  simp only [← Nat.card_eq_fintype_card]
  -- Substitute cardinality values
  rw [hG_val, hK_val]
  -- Unfold the set variable q = (qq : ℂ)
  simp only [show q = (qq : ℂ) from rfl]
  -- Push ℕ casts through subtraction (need side conditions for ℕ subtraction)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  -- Factor qq^2 - 1 = (qq - 1)(qq + 1) so field_simp can use individual nonzero hypotheses
  simp only [show (↑qq : ℂ) ^ 2 - 1 = (↑qq - 1) * (↑qq + 1) from by ring]
  field_simp [hq_ne, hqm1_ne, hqp1_ne]
  ring

-- charW₁_parabolic, parabolic_not_in_elliptic, and normSq_complementaryChar_parabolic
-- are defined later in the file (after disc_conj_eq and algebraMap_disc_fieldExtEmbed)

/-- A quadratic polynomial a*x² + b*x + c over a field of char ≠ 2 with a ≠ 0 and
discriminant b² - 4ac ≠ 0 being a square has exactly 2 roots. -/
private lemma Etingof.quadratic_two_roots
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero (2 : F)]
    (a b c : F) (ha : a ≠ 0) (hdisc_ne : b ^ 2 - 4 * a * c ≠ 0)
    (hdisc_sq : IsSquare (b ^ 2 - 4 * a * c)) :
    (Finset.univ.filter fun x : F => a * x ^ 2 + b * x + c = 0).card = 2 := by
  -- Get the square root of the discriminant
  obtain ⟨s, hs⟩ := hdisc_sq
  -- hs : b ^ 2 - 4 * a * c = s * s (IsSquare gives s * s form)
  have hs' : discrim a b c = s * s := by
    simp only [discrim]; exact hs
  have hs_ne : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hs; exact hdisc_ne hs
  -- The two roots
  set r₁ := (-b + s) / (2 * a)
  set r₂ := (-b - s) / (2 * a)
  -- They are distinct
  have h2a : (2 * a) ≠ (0 : F) := mul_ne_zero (NeZero.ne 2) ha
  have hr_ne : r₁ ≠ r₂ := by
    intro h
    have h1 : (-b + s) / (2 * a) = (-b - s) / (2 * a) := h
    rw [div_eq_div_iff h2a h2a] at h1
    -- h1 : (-b + s) * (2 * a) = (-b - s) * (2 * a)
    have h2 := mul_right_cancel₀ h2a h1
    -- h2 : -b + s = -b - s
    have : 2 * s = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (NeZero.ne 2)
    · exact hs_ne h
  -- The filter equals {r₁, r₂}
  have hfilter : Finset.univ.filter (fun x : F => a * x ^ 2 + b * x + c = 0) = {r₁, r₂} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [show a * x ^ 2 + b * x + c = a * (x * x) + b * x + c by ring]
    rw [quadratic_eq_zero_iff ha hs']
  rw [hfilter, Finset.card_pair hr_ne]

/-- A linear equation a*x + b = 0 with a ≠ 0 has exactly 1 root. -/
private lemma Etingof.linear_one_root
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b : F) (ha : a ≠ 0) :
    (Finset.univ.filter fun x : F => a * x + b = 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨-(a⁻¹ * b), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    -- a*x + b = 0 → a*x = -b → x = -(a⁻¹ * b)
    have hax : a * x = -b := by linear_combination h
    have : x = -(a⁻¹ * b) := by
      have := mul_left_cancel₀ ha (show a * x = a * (-(a⁻¹ * b)) by
        rw [hax]; field_simp)
      exact this
    exact this
  · intro h
    subst h
    field_simp
    ring

private lemma Etingof.charW₁_splitSemisimple
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = 1 := by
  haveI : NeZero (2 : GaloisField p n) := by
    constructor; intro h2; apply hp2
    have h2' : (Nat.cast 2 : GaloisField p n) = 0 := h2
    rw [CharP.cast_eq_zero_iff (GaloisField p n) p 2] at h2'
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  obtain ⟨hdisc_ne, hdisc_sq⟩ := hg
  simp only [GL2.disc_eq] at hdisc_ne hdisc_sq
  by_cases h01 : M 0 1 = 0
  · -- Case M₀₁ = 0: infinity is fixed, affine equation is linear
    have h00_ne_11 : M 0 0 - M 1 1 ≠ 0 := by
      intro h; apply hdisc_ne
      show (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = 0
      rw [h01, h]; ring
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; simp only [h01, zero_mul, zero_add, sub_eq_add_neg]
    rw [hfilt, Etingof.linear_one_root _ _ h00_ne_11]
    simp only [h01, ite_true]
    push_cast; ring
  · -- Case M₀₁ ≠ 0: infinity is not fixed, quadratic has 2 roots
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; show _ - _ = 0 ↔ _ + (-_) = 0; rw [sub_eq_add_neg]
    have hconv : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) =
        (M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) * (M 1 0) := by ring
    have hdisc_ne' : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) ≠ 0 := by
      rw [hconv]; exact hdisc_ne
    have hdisc_sq' : IsSquare ((M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0))) := by
      rw [hconv]; exact hdisc_sq
    rw [hfilt, Etingof.quadratic_two_roots _ _ _ h01 hdisc_ne' hdisc_sq']
    simp only [h01, ite_false, Nat.add_zero]
    push_cast; ring

/-- A quadratic polynomial a*x² + b*x + c with a ≠ 0 and non-square discriminant
has no roots. If it had a root r, then a*x² + b*x + c = a*(x-r)*(x-s) for some s,
so disc = a²*(r-s)², which is a square — contradiction. -/
private lemma Etingof.quadratic_no_roots
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b c : F) (_ha : a ≠ 0) (hdisc : ¬IsSquare (b ^ 2 - 4 * a * c)) :
    (Finset.univ.filter fun x : F => a * x ^ 2 + b * x + c = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hroot
  exact hdisc ⟨2 * a * x + b, by linear_combination -4 * a * hroot⟩

/-- On elliptic elements, charW₁ = -1 (no fixed points on P¹).
An elliptic element has non-square discriminant, so:
- M₀₁ ≠ 0 (otherwise disc = (M₀₀-M₁₁)², always a square)
- The fixed-point quadratic M₀₁t² + (M₀₀-M₁₁)t - M₁₀ = 0 has discriminant = disc(g),
  which is non-square, so it has no roots (by `quadratic_no_roots`)
- The point at infinity [0:1] is not fixed (since M₀₁ ≠ 0)
- Total fixed points = 0, so charW₁ = 0 - 1 = -1. -/
private lemma Etingof.charW₁_elliptic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = -1 := by
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  -- M₀₁ ≠ 0 for elliptic elements (otherwise disc = (M₀₀-M₁₁)², a square)
  have h01 : M 0 1 ≠ 0 := by
    intro h
    apply hg  -- hg : ¬IsSquare (GL2.disc g)
    have hdisc : GL2.disc g = (M 0 0 - M 1 1) ^ 2 := by
      simp only [GL2.disc_eq, show g.val 0 1 = M 0 1 from rfl, h]; ring
    rw [hdisc]; exact IsSquare.sq _
  -- The fixed-point quadratic has disc = GL2.disc(g), which is non-square
  have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
      (Finset.univ.filter fun t : GaloisField p n =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
    congr 1; ext t; show _ - _ = 0 ↔ _ + (-_) = 0; rw [sub_eq_add_neg]
  have hconv : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) =
      (M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) * (M 1 0) := by ring
  have hdisc : ¬IsSquare ((M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0))) := by
    rw [hconv]; exact hg
  rw [hfilt, Etingof.quadratic_no_roots _ _ _ h01 hdisc]
  simp only [h01, ite_false, Nat.add_zero, Nat.cast_zero, zero_sub]

/-- The discriminant is a conjugation invariant: disc(x⁻¹gx) = disc(g).
This follows from disc = tr² - 4·det and both tr and det being similarity invariants. -/
private lemma Etingof.disc_eq_tr_det (M : Matrix (Fin 2) (Fin 2) (GaloisField p n)) :
    (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 =
    (Matrix.trace M) ^ 2 - 4 * Matrix.det M := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

private lemma Etingof.disc_conj_eq (g x : GL2 p n) :
    GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g := by
  -- disc = tr² - 4·det for 2×2 matrices
  simp only [GL2.disc_eq]
  set h := x⁻¹ * g * x
  set G := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set H := (h : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  -- Express disc in terms of trace and det
  rw [Etingof.disc_eq_tr_det (M := H), Etingof.disc_eq_tr_det (M := G)]
  -- trace(h) = trace(g)  and  det(h) = det(g)
  have htr : Matrix.trace H = Matrix.trace G := by
    change Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by
      simp [Units.val_mul]]
    exact Matrix.trace_units_conj' x g.val
  have hdet : Matrix.det H = Matrix.det G := by
    change Matrix.det (x⁻¹ * g * x).val = Matrix.det g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by
      simp [Units.val_mul]]
    exact Matrix.det_units_conj' x g.val
  rw [htr, hdet]

/-- If d ∈ 𝔽_q has a square root s in 𝔽_{q²} with s^q = -s and s ≠ 0 (char ≠ 2),
then d is not a square in 𝔽_q. -/
private lemma Etingof.not_isSquare_of_antisymmetric_root (hp2 : p ≠ 2) (hn : n ≠ 0)
    (d : GaloisField p n) (s : GaloisField p (2 * n))
    (hd : algebraMap (GaloisField p n) (GaloisField p (2 * n)) d = s ^ 2)
    (hs_ne : s ≠ 0)
    (hs_frob : s ^ (p ^ n : ℕ) = -s) :
    ¬IsSquare d := by
  letI := Etingof.algebraGaloisFieldExt p n
  intro ⟨r, hr⟩
  -- If d = r * r in 𝔽_q, then algebraMap(r * r) = s² in 𝔽_{q²}
  have hrs : (algebraMap (GaloisField p n) (GaloisField p (2 * n)) r) ^ 2 = s ^ 2 := by
    rw [sq, ← map_mul, ← hr]; exact hd
  -- So (alg_map(r))² = s², meaning (alg_map(r) - s)(alg_map(r) + s) = 0
  set r' := algebraMap (GaloisField p n) (GaloisField p (2 * n)) r
  have h_prod : (r' - s) * (r' + s) = 0 := by
    have h1 : r' ^ 2 = s ^ 2 := hrs
    have : (r' - s) * (r' + s) = r' ^ 2 - s ^ 2 := by ring
    rw [this, h1, sub_self]
  -- Key fact: algebraMap(r)^{p^n} = algebraMap(r) since r ∈ 𝔽_{p^n}
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hr_frob : r' ^ (p ^ n : ℕ) = r' := by
    show (algebraMap (GaloisField p n) (GaloisField p (2 * n)) r) ^ (p ^ n : ℕ) = _
    rw [← map_pow]
    congr 1
    have hcard : Fintype.card (GaloisField p n) = p ^ n := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    rw [← hcard]
    exact FiniteField.pow_card r
  -- NeZero (2 : GaloisField p (2*n)) since char = p ≠ 2
  have h2ne : (2 : GaloisField p (2 * n)) ≠ 0 := by
    intro h2; apply hp2
    have h2' : (Nat.cast 2 : GaloisField p (2 * n)) = 0 := h2
    rw [CharP.cast_eq_zero_iff (GaloisField p (2 * n)) p 2] at h2'
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le
  -- p^n is odd since p is an odd prime
  have hodd : Odd (p ^ n) := by
    exact Odd.pow (Nat.Prime.odd_of_ne_two hp.out hp2)
  rcases mul_eq_zero.mp h_prod with h | h
  · -- r' = s (from r' - s = 0)
    have hs_eq : s = r' := (sub_eq_zero.mp h).symm
    -- s^{p^n} = r'^{p^n} = r' = s, but also s^{p^n} = -s
    have hcontra : s = -s := by
      calc s = r' := hs_eq
        _ = r' ^ (p ^ n : ℕ) := hr_frob.symm
        _ = s ^ (p ^ n : ℕ) := by rw [hs_eq]
        _ = -s := hs_frob
    -- So s + s = 0, i.e., 2 * s = 0
    have h2s : (2 : GaloisField p (2 * n)) * s = 0 := by
      have : s - (-s) = 0 := sub_eq_zero.mpr hcontra
      have : 2 * s = 0 := by linear_combination this
      exact this
    exact absurd ((mul_eq_zero.mp h2s).resolve_left h2ne) hs_ne
  · -- r' + s = 0, so s = -r'
    have hs_eq : s = -r' := by
      have : r' = -s := add_eq_zero_iff_eq_neg.mp h
      rw [this]; ring
    have hr'_ne : r' ≠ 0 := by
      intro h0; rw [hs_eq, h0, neg_zero] at hs_ne; exact hs_ne rfl
    -- s^{p^n} = (-r')^{p^n} = -(r'^{p^n}) = -r' (since p^n is odd)
    have h1 : s ^ (p ^ n : ℕ) = -(r' ^ (p ^ n : ℕ)) := by
      rw [hs_eq]; exact hodd.neg_pow r'
    -- But s^{p^n} = -s = -(-r') = r'
    have h2 : s ^ (p ^ n : ℕ) = r' := by rw [hs_frob, hs_eq, neg_neg]
    -- So -r' = r'
    have h3 : -r' = r' := by
      have : -(r' ^ (p ^ n : ℕ)) = r' := by rw [← h1, h2]
      rwa [hr_frob] at this
    -- So 2r' = 0
    have h4 : (2 : GaloisField p (2 * n)) * r' = 0 := by
      have : r' - (-r') = 0 := sub_eq_zero.mpr h3.symm
      linear_combination this
    exact absurd ((mul_eq_zero.mp h4).resolve_left h2ne) hr'_ne

/-- disc(embed(α)) = trace(α)² - 4·norm(α) in the base field.
This connects the matrix discriminant to algebraic trace and norm. -/
private lemma Etingof.disc_fieldExtEmbed (hn : n ≠ 0) (α : (GaloisField p (2 * n))ˣ) :
    letI := Etingof.algebraGaloisFieldExt p n
    GL2.disc (Etingof.GL2.fieldExtEmbed p n α) =
    Algebra.trace (GaloisField p n) (GaloisField p (2 * n)) (α : GaloisField p (2 * n)) ^ 2 -
    4 * Algebra.norm (GaloisField p n) (α : GaloisField p (2 * n)) := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  -- disc = tr² - 4·det via disc_eq_tr_det
  rw [GL2.disc_eq, Etingof.disc_eq_tr_det]
  -- The key: fieldExtEmbed α has matrix = leftMulMatrix b α
  have hval : (Etingof.GL2.fieldExtEmbed p n α).val =
      Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) := by
    show (Etingof.GL2.fieldExtEmbed p n α).val = _
    simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; rfl
  -- Relate matrix trace/det to algebra trace/norm
  congr 1
  · congr 1; rw [hval]; exact (Algebra.trace_eq_matrix_trace b _).symm
  · congr 1; rw [hval]; exact (Algebra.norm_eq_matrix_det b _).symm

/-- The algebraMap of disc(embed(α)) equals (α - α^q)² in the extension field. -/
private lemma Etingof.algebraMap_disc_fieldExtEmbed (hn : n ≠ 0)
    (α : (GaloisField p (2 * n))ˣ) :
    letI := Etingof.algebraGaloisFieldExt p n
    algebraMap (GaloisField p n) (GaloisField p (2 * n))
      (GL2.disc (Etingof.GL2.fieldExtEmbed p n α)) =
    ((α : GaloisField p (2 * n)) -
     (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)) ^ 2 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  rw [Etingof.disc_fieldExtEmbed p n hn α, map_sub, map_mul, map_pow]
  -- Use trace/norm formulas for finite fields
  have hfinrank : Module.finrank (GaloisField p n) (GaloisField p (2 * n)) = 2 :=
    Etingof.finrank_galoisField_ext p n hn
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_norm_eq_prod_pow]
  rw [hfinrank]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, zero_add, pow_zero, pow_one, hcard]
  -- Handle algebraMap 4 = 4 and close by ring
  have h4 : algebraMap (GaloisField p n) (GaloisField p (2 * n)) 4 = 4 := map_ofNat _ 4
  rw [h4]
  ring

/-- Frobenius s^q = -s for s = α - α^q. -/
private lemma Etingof.frob_diff_neg (hn : n ≠ 0) (α : GaloisField p (2 * n)) :
    (α - α ^ (p ^ n : ℕ)) ^ (p ^ n : ℕ) =
    -(α - α ^ (p ^ n : ℕ)) := by
  rw [sub_pow_char_pow (p := p)]
  -- Need α^(q²) = α, i.e. α^(p^(2n)) = α
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  have hcard2 : Fintype.card (GaloisField p (2 * n)) = p ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
  have hfrob2 : α ^ (p ^ (2 * n) : ℕ) = α := by
    rw [← hcard2]; exact FiniteField.pow_card α
  -- (α^q)^q = α^(q²) = α^(p^(2n)) = α
  have : (α ^ (p ^ n : ℕ)) ^ (p ^ n : ℕ) = α := by
    rw [← pow_mul, ← Nat.pow_add, show n + n = 2 * n from by omega]
    exact hfrob2
  rw [this]; ring

private lemma Etingof.ellipticSubgroup_disc (hp2 : p ≠ 2) (k : GL2 p n)
    (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    GL2.disc k = 0 ∨ ¬IsSquare (GL2.disc k) := by
  obtain ⟨α, rfl⟩ := hk
  by_cases hn : n = 0
  · left; simp [GL2.disc_eq, GL2.fieldExtEmbed, hn]
  · letI := Etingof.algebraGaloisFieldExt p n
    set d := GL2.disc (Etingof.GL2.fieldExtEmbed p n α)
    set s := (α : GaloisField p (2 * n)) - (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)
    have hd : algebraMap (GaloisField p n) (GaloisField p (2 * n)) d = s ^ 2 :=
      Etingof.algebraMap_disc_fieldExtEmbed p n hn α
    by_cases hs : s = 0
    · -- α^q = α, disc = 0
      left
      have hinj : Function.Injective
          (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
        (algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
      exact hinj (by rw [hd, hs, sq, mul_zero, map_zero])
    · -- α^q ≠ α, disc is not a square
      right
      have hs_frob : s ^ (p ^ n : ℕ) = -s := Etingof.frob_diff_neg p n hn ↑α
      exact Etingof.not_isSquare_of_antisymmetric_root p n hp2 hn d s hd hs hs_frob

/-- Elements of GF(q²) fixed by the Frobenius x ↦ x^q lie in GF(q) (i.e., the image
of algebraMap). Uses: X^q - X has q roots (= all of GF(q)), degree q, so any root in
GF(q²) must be in the image of GF(q). -/
private lemma Etingof.frob_fixed_mem_range (hn : n ≠ 0)
    (z : GaloisField p (2 * n))
    (hz : z ^ (p ^ n : ℕ) = z) :
    z ∈ Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
  classical
  letI := Etingof.algebraGaloisFieldExt p n
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  -- The set S = {z ∈ GF(q²) | z^q = z} contains range(algebraMap) by FiniteField.pow_card
  -- and |S| ≤ q (roots of degree-q polynomial X^q - X)
  -- while |range(algebraMap)| = q (injective ring hom from size-q field)
  -- So S = range(algebraMap)
  -- Concretely: z ∈ S, and we prove S ⊆ range by showing S = range via cardinality
  set f := algebraMap (GaloisField p n) (GaloisField p (2 * n))
  -- Build the set S as a Finset
  set S := Finset.univ.filter (fun x : GaloisField p (2 * n) => x ^ (Fintype.card (GaloisField p n)) = x)
  -- range(f) ⊆ S: f(a)^q = f(a^q) = f(a) since a^q = a in GF(q)
  have hrange_sub : ∀ a : GaloisField p n, f a ∈ S := by
    intro a; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow f a, FiniteField.pow_card]
  -- |S| ≤ q (polynomial degree bound)
  have hS_card : S.card ≤ Fintype.card (GaloisField p n) := by
    open Polynomial in
    -- S = roots of X^q - X in GF(q²), degree q, so ≤ q roots
    set q' := Fintype.card (GaloisField p n)
    set poly := (X ^ q' - X : (GaloisField p (2 * n))[X])
    -- S ⊆ poly.roots.toFinset
    have hq_lt : 1 < q' := by
      show 1 < Fintype.card (GaloisField p n)
      rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
      exact Nat.one_lt_pow hn hp.out.one_lt
    have hpoly_ne : poly ≠ 0 := by
      intro h
      have := congr_arg natDegree h
      simp only [poly, natDegree_zero] at this
      rw [natDegree_sub_eq_left_of_natDegree_lt] at this
      · rw [natDegree_X_pow] at this; omega
      · rw [natDegree_X_pow, natDegree_X]; omega
    have hS_roots : S ⊆ poly.roots.toFinset := by
      intro x hx; rw [Multiset.mem_toFinset]
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [mem_roots hpoly_ne, IsRoot, eval_sub, eval_pow, eval_X]
      exact sub_eq_zero.mpr hx
    calc S.card ≤ poly.roots.toFinset.card := Finset.card_le_card hS_roots
      _ ≤ poly.roots.card := Multiset.toFinset_card_le _
      _ ≤ poly.natDegree := card_roots' _
      _ = q' := by
          simp only [poly]
          rw [natDegree_sub_eq_left_of_natDegree_lt]
          · exact natDegree_X_pow q'
          · rw [natDegree_X_pow, natDegree_X]; omega
  -- |range(f)| = q
  have hrange_card : (Finset.univ.image f).card = Fintype.card (GaloisField p n) := by
    rw [Finset.card_image_of_injective _ (RingHom.injective f)]
    exact Finset.card_univ
  -- range ⊆ S and |range| = q ≥ |S|, so S = range
  have himage_sub : Finset.univ.image f ⊆ S := by
    intro x hx; rw [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx; exact hrange_sub a
  -- z ∈ S
  have hz_mem : z ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]; exact hz
  -- S ⊆ image since |S| ≤ |image| and image ⊆ S
  have hS_sub : S ⊆ Finset.univ.image f :=
    Finset.eq_of_subset_of_card_le himage_sub (hrange_card ▸ hS_card) ▸ Finset.Subset.refl S
  have hfinal := hS_sub hz_mem
  rw [Finset.mem_image] at hfinal
  obtain ⟨a, _, ha⟩ := hfinal
  exact ⟨a, ha⟩

/-- If z ∈ GF(q²)ˣ satisfies z^q = z, then fieldExtEmbed(z) is a scalar matrix. -/
private lemma Etingof.fieldExtEmbed_scalar_of_frob_fixed (hn : n ≠ 0)
    (z : (GaloisField p (2 * n))ˣ)
    (hz : (z : GaloisField p (2 * n)) ^ (p ^ n : ℕ) = (z : GaloisField p (2 * n))) :
    GL2.IsScalar (p := p) (n := n) (Etingof.GL2.fieldExtEmbed p n z) := by
  letI := Etingof.algebraGaloisFieldExt p n
  obtain ⟨a, ha⟩ := Etingof.frob_fixed_mem_range p n hn (z : GaloisField p (2 * n)) hz
  -- a must be nonzero since z is a unit
  have ha_ne : a ≠ 0 := by
    intro h0; rw [h0, map_zero] at ha; exact Units.ne_zero z ha.symm
  -- z = Units.map algebraMap (Units.mk0 a ha_ne)
  have hz_eq : z = Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom
      (Units.mk0 a ha_ne) := by
    ext; simp [ha]
  -- fieldExtEmbed(algebraMap(a)) is a scalar matrix
  rw [hz_eq]
  have hval := Etingof.fieldExtEmbed_algebraMap_val p n hn (Units.mk0 a ha_ne)
  constructor
  · -- off-diagonal (0,1) = 0
    have h1 : (Etingof.GL2.fieldExtEmbed p n (Units.map (algebraMap (GaloisField p n)
        (GaloisField p (2 * n))).toMonoidHom (Units.mk0 a ha_ne))).val 0 1 = 0 := by
      rw [hval]; simp [Matrix.diagonal_apply]
    exact h1
  constructor
  · -- off-diagonal (1,0) = 0
    have h2 : (Etingof.GL2.fieldExtEmbed p n (Units.map (algebraMap (GaloisField p n)
        (GaloisField p (2 * n))).toMonoidHom (Units.mk0 a ha_ne))).val 1 0 = 0 := by
      rw [hval]; simp [Matrix.diagonal_apply]
    exact h2
  · -- diagonal entries equal
    have h3 : (Etingof.GL2.fieldExtEmbed p n (Units.map (algebraMap (GaloisField p n)
        (GaloisField p (2 * n))).toMonoidHom (Units.mk0 a ha_ne))).val 0 0 =
        (Etingof.GL2.fieldExtEmbed p n (Units.map (algebraMap (GaloisField p n)
        (GaloisField p (2 * n))).toMonoidHom (Units.mk0 a ha_ne))).val 1 1 := by
      rw [hval]; simp [Matrix.diagonal_apply]
    exact h3

/-- IsScalar is preserved under conjugation: if x⁻¹gx is scalar, then g is scalar. -/
private lemma Etingof.isScalar_of_conj_isScalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g x : GL2 p n) (h : GL2.IsScalar (p := p) (n := n) (x⁻¹ * g * x)) :
    GL2.IsScalar (p := p) (n := n) g := by
  obtain ⟨h01, h10, h00⟩ := h
  -- If x⁻¹gx is scalar, then x⁻¹gx commutes with x, so g = x(x⁻¹gx)x⁻¹ = x⁻¹gx
  -- Actually: x⁻¹gx = cI for some c, so g = xcIx⁻¹ = cI
  set k := x⁻¹ * g * x
  -- k commutes with everything since it's scalar
  have hcomm : ∀ y : GL2 p n, k * y = y * k := by
    intro y
    ext i j; simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    change k.val 0 1 = 0 at h01; change k.val 1 0 = 0 at h10
    change k.val 0 0 = k.val 1 1 at h00
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, mul_comm]
  -- g = xkx⁻¹ = k (since k commutes)
  have hgk : g = k := by
    have : x * k * x⁻¹ = g := by
      show x * (x⁻¹ * g * x) * x⁻¹ = g; group
    rw [← this, mul_assoc, hcomm, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hgk]; exact ⟨h01, h10, h00⟩

/-- On parabolic matrices, charW₁ = 0 (exactly 1 fixed point on P¹). -/
private lemma Etingof.charW₁_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = 0 := by
  obtain ⟨hdisc, hns⟩ := hg
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  by_cases h01 : M 0 1 = 0
  · -- Case M₀₁ = 0: disc = (M₀₀ - M₁₁)², so M₀₀ = M₁₁
    have hdiag : M 0 0 = M 1 1 := by
      have hd : GL2.disc g = (M 0 0 - M 1 1) ^ 2 := by
        simp only [GL2.disc_eq]; rw [show g.val 0 1 = M 0 1 from rfl, h01]; ring
      rw [hd] at hdisc
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdisc)
    -- ¬IsScalar with M₀₁ = 0, M₀₀ = M₁₁ implies M₁₀ ≠ 0
    have h10 : M 1 0 ≠ 0 := by
      intro h; exact hns ⟨h01, h, hdiag⟩
    -- Affine equation: 0·t² + 0·t - M₁₀ = 0: no solutions since M₁₀ ≠ 0
    have hempty : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t _
      simp only [h01, hdiag, zero_mul, sub_self, mul_zero, zero_add, sub_eq_zero]
      exact h10 ∘ Eq.symm
    rw [hempty, Finset.card_empty]
    simp [h01]
  · -- Case M₀₁ ≠ 0: quadratic with disc = 0 has exactly 1 root (char ≠ 2)
    haveI : NeZero (2 : GaloisField p n) := by
      constructor; intro h2
      apply hp2
      have : (Nat.cast 2 : GaloisField p n) = 0 := h2
      rw [CharP.cast_eq_zero_iff (GaloisField p n) p 2] at this
      exact Nat.le_antisymm (Nat.le_of_dvd (by omega) this) hp.out.two_le
    have hdisc_eq : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) = 0 := by
      have hd : GL2.disc g = (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 := by
        simp only [GL2.disc_eq]; rfl
      rw [hd] at hdisc; linear_combination hdisc
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; show _ - _ = 0 ↔ _ + (-_) = 0; rw [sub_eq_add_neg]
    -- disc = 0 means b² = 4ac, so the quadratic factors as a(x + b/(2a))²
    -- Unique root r = -(M 0 0 - M 1 1) / (2 * M 0 1)
    set a := M 0 1
    set b := M 0 0 - M 1 1
    set c := -(M 1 0)
    have h2a : (2 : GaloisField p n) * a ≠ 0 := mul_ne_zero (NeZero.ne 2) h01
    set r := -b / (2 * a)
    have hone : (Finset.univ.filter fun t : GaloisField p n =>
        a * t ^ 2 + b * t + c = 0).card = 1 := by
      -- The polynomial factors as a * (t - r)²
      have hfactor : ∀ t : GaloisField p n,
          a * t ^ 2 + b * t + c = a * (t - r) ^ 2 := by
        intro t
        -- c = b²/(4a) from disc = 0
        have h4 : (4 : GaloisField p n) ≠ 0 := by
          have : (4 : GaloisField p n) = 2 * 2 := by norm_num
          rw [this]; exact mul_ne_zero (NeZero.ne 2) (NeZero.ne 2)
        have hc : c = b ^ 2 / (4 * a) := by
          rw [eq_div_iff (mul_ne_zero h4 h01)]
          linear_combination -hdisc_eq
        rw [hc]; show _ = a * (t - -b / (2 * a)) ^ 2
        field_simp [h4, h01]
        ring
      have hfilter : (Finset.univ.filter fun t : GaloisField p n =>
          a * t ^ 2 + b * t + c = 0) = {r} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [hfactor t]
        constructor
        · intro ht
          have := mul_eq_zero.mp ht
          rcases this with ha0 | hsq
          · exact absurd ha0 h01
          · exact eq_of_sub_eq_zero (sq_eq_zero_iff.mp hsq)
        · intro ht; rw [ht, sub_self, sq, mul_zero, mul_zero]
      rw [hfilter, Finset.card_singleton]
    rw [hfilt, hone, if_neg h01]
    simp

/-- No conjugate of a parabolic element lies in the elliptic subgroup K. -/
private lemma Etingof.parabolic_not_in_elliptic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) (hn : n ≠ 0)
    (x : GL2 p n) :
    x⁻¹ * g * x ∉ Etingof.GL2.ellipticSubgroup p n := by
  intro hmem
  -- x⁻¹gx ∈ K = range(fieldExtEmbed), so x⁻¹gx = fieldExtEmbed(z) for some z
  change x⁻¹ * g * x ∈ (Etingof.GL2.fieldExtEmbed p n).range at hmem
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hmem
  -- disc(fieldExtEmbed(z)) = disc(x⁻¹gx) = disc(g) = 0
  have hd0 : GL2.disc (Etingof.GL2.fieldExtEmbed p n z) = 0 := by
    rw [hz, Etingof.disc_conj_eq p n g x]; exact hg.1
  -- algebraMap(disc(embed(z))) = (z - z^q)² = 0 in the extension field
  have hzq : ((z : GaloisField p (2 * n)) - (z : GaloisField p (2 * n)) ^ (p ^ n : ℕ)) ^ 2 = 0 := by
    letI := Etingof.algebraGaloisFieldExt p n
    rw [← Etingof.algebraMap_disc_fieldExtEmbed p n hn z, hd0, map_zero]
  -- z = z^q (in a field, x² = 0 iff x = 0)
  have hzeq : (z : GaloisField p (2 * n)) = (z : GaloisField p (2 * n)) ^ (p ^ n : ℕ) :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp hzq)
  -- z^q = z implies fieldExtEmbed(z) is a scalar matrix
  have hscalar : GL2.IsScalar (p := p) (n := n) (Etingof.GL2.fieldExtEmbed p n z) :=
    Etingof.fieldExtEmbed_scalar_of_frob_fixed p n hn z hzeq.symm
  -- Since x⁻¹gx = fieldExtEmbed(z) is scalar, and IsScalar is conjugation-invariant, g is scalar
  rw [hz] at hscalar
  exact hg.2 (Etingof.isScalar_of_conj_isScalar p n g x hscalar)

/-- For parabolic g with eigenvalue λ (= tr(g)/2), every upper triangular conjugate
has both diagonal entries equal to λ. -/
private lemma Etingof.parabolic_conj_diag_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (g x : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (hut : (x⁻¹ * g * x : GL2 p n).val 1 0 = 0) :
    (x⁻¹ * g * x : GL2 p n).val 0 0 = (x⁻¹ * g * x : GL2 p n).val 1 1 := by
  set k := x⁻¹ * g * x
  set Mk := (k : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  -- disc(k) = disc(g) = 0
  have hdisc_k : GL2.disc k = 0 := by
    rw [Etingof.disc_conj_eq p n g x]; exact hg.1
  -- With Mk 1 0 = 0, disc(k) = (Mk 0 0 - Mk 1 1)²
  have hdisc_sq : GL2.disc k = (Mk 0 0 - Mk 1 1) ^ 2 := by
    simp only [GL2.disc_eq]; change (Mk 0 0 - Mk 1 1) ^ 2 + 4 * Mk 0 1 * Mk 1 0 = _
    rw [hut]; ring
  rw [hdisc_sq] at hdisc_k
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdisc_k)

/-- For parabolic g, the diagonal entry of upper triangular conjugates is nonzero. -/
private lemma Etingof.parabolic_conj_diag_ne_zero
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g x : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (hut : (x⁻¹ * g * x : GL2 p n).val 1 0 = 0)
    (hdiag : (x⁻¹ * g * x : GL2 p n).val 0 0 = (x⁻¹ * g * x : GL2 p n).val 1 1) :
    (x⁻¹ * g * x : GL2 p n).val 0 0 ≠ 0 := by
  intro h0
  -- det(k) = M₀₀ * M₁₁ - M₀₁ * M₁₀ = 0 * 0 - M₀₁ * 0 = 0
  -- But k is invertible, so det ≠ 0
  set k := x⁻¹ * g * x
  have hdet : Matrix.det k.val = 0 := by
    rw [Matrix.det_fin_two]; rw [hut, h0, ← hdiag, h0]; ring
  have hdet_ne : Matrix.det k.val ≠ 0 := by
    have hmul : k.val * (k⁻¹ : GL2 p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congr_arg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h; rw [h, zero_mul] at this; exact one_ne_zero this.symm
  exact hdet_ne hdet

/-- The value of a monoid hom from a finite group to ℂˣ has |z * conj z| = 1. -/
private lemma Etingof.monoidHom_val_mul_conj_eq_one {G : Type*} [Group G] [Fintype G]
    (f : G →* ℂˣ) (g : G) : (f g : ℂ) * starRingEnd ℂ (f g : ℂ) = 1 := by
  have hne : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hmem : f g ∈ rootsOfUnity (Fintype.card G) ℂ := by
    rw [mem_rootsOfUnity]
    have : (f g) ^ Fintype.card G = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    exact this
  haveI : NeZero (Fintype.card G) := ⟨hne⟩
  rw [Complex.mul_conj']
  have hnorm : ‖(f g : ℂ)‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity hmem
  rw [hnorm]; norm_num

/-- On parabolic matrices, |χ|² = 1 (since χ = -charVα₁ and |charVα₁| = 1). -/
private lemma Etingof.normSq_complementaryChar_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (hn : n ≠ 0) :
    Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) = 1 := by
  -- Step 1: charW₁(g) = 0 for parabolic g
  have hW := Etingof.charW₁_parabolic p n hp2 g hg
  -- Step 2: The induced character sum is 0 (no conjugate in K)
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n) with halpha_def
  classical
  have hInd : ∀ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) = 0 := by
    intro x; rw [dif_neg (Etingof.parabolic_not_in_elliptic p n g hg hn x)]
  have hInd_sum : ∑ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) = 0 := by
    exact Finset.sum_eq_zero (fun x _ => hInd x)
  -- Step 3: χ(g) = (charW₁ - 1) * charVα₁ - Ind = -charVα₁
  show Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) = 1
  unfold Etingof.GL2.complementarySeriesChar
  rw [hW, hInd_sum]
  ring_nf
  simp only [map_neg, mul_neg, neg_neg]
  -- Now goal is: charVα₁(g) * conj(charVα₁(g)) = 1
  sorry

/-- On elliptic elements, charVα₁ = 0 (no conjugate is upper triangular).
If x⁻¹gx were upper triangular, its (1,0) entry would be 0, making
disc(x⁻¹gx) = (M₀₀-M₁₁)², a perfect square. But disc(x⁻¹gx) = disc(g)
(conjugation invariant) and disc(g) is non-square (g is elliptic). -/
private lemma Etingof.charVα₁_elliptic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.charVα₁ p n alpha g = 0 := by
  unfold Etingof.GL2.charVα₁
  simp only [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro x _
  -- No conjugate of an elliptic element is upper triangular
  set conj := (x⁻¹ * g * x : GL2 p n)
  set Mc := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  have hM10 : ¬(Mc 1 0 = 0) := by
    intro h10
    apply hg
    -- disc(x⁻¹gx) = (M₀₀-M₁₁)² when M₁₀ = 0
    rw [← Etingof.disc_conj_eq p n g x]
    have hdisc_sq : GL2.disc conj = (Mc 0 0 - Mc 1 1) ^ 2 := by
      simp only [GL2.disc_eq]
      change (Mc 0 0 - Mc 1 1) ^ 2 + 4 * Mc 0 1 * Mc 1 0 = _
      rw [h10]; ring
    rw [hdisc_sq]; exact IsSquare.sq _
  simp only [hM10, ite_false]

private lemma Etingof.induced_char_splitSemisimple_eq_zero
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) := by
  intro x hcontra
  have hdisc_eq : GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g :=
    Etingof.disc_conj_eq p n g x
  have hK := Etingof.ellipticSubgroup_disc p n hp2 (x⁻¹ * g * x) hcontra
  -- g is split semisimple: disc ≠ 0 and IsSquare
  obtain ⟨hdisc_ne, hdisc_sq⟩ := hg
  rw [hdisc_eq] at hK
  rcases hK with hzero | hnsq
  · exact hdisc_ne hzero
  · exact hnsq hdisc_sq

open Classical in
/-- On split semisimple (hyperbolic) matrices, χ = 0.
Proof: χ = (charW₁ - 1) · charVα₁ - induced_term.
For split semisimple g, charW₁ = 1 (2 fixed points on P¹) and the
induced character sum is 0 (no conjugate lies in K). -/
private lemma Etingof.complementaryChar_splitSemisimple_eq_zero
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g = 0 := by
  unfold Etingof.GL2.complementarySeriesChar
  have h1 : Etingof.GL2.charW₁ p n g = 1 := Etingof.charW₁_splitSemisimple p n hp2 g hg
  have h2 : ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) :=
    Etingof.induced_char_splitSemisimple_eq_zero p n hp2 nu g hg
  -- The induced character sum is zero because each term is zero
  have h3 : ∑ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val
       else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    rw [dif_neg (h2 x)]
  rw [h1, h3, mul_zero, one_mul, sub_self, zero_sub, neg_eq_zero]

end CharacterValues

/-- Character orthogonality for finite groups: the sum of a nontrivial
character over all group elements is zero. Applied to ν^{q-1} on F_{q²}×. -/
private lemma Etingof.sum_nontrivial_char_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  -- Standard character orthogonality: ∑_g χ(g) = 0 for nontrivial χ
  -- Choose g₀ with χ(g₀) ≠ 1
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push_neg at h; exact absurd (MonoidHom.ext h) hχ
  -- χ(g₀) * ∑ g, χ(g) = ∑ g, χ(g₀ * g) = ∑ g, χ(g) (by reindexing)
  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h; apply hg₀; exact Units.val_injective h
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
  -- (χ(g₀) - 1) * ∑ χ = 0, with χ(g₀) ≠ 1
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

open Classical in
/-- On elliptic elements, the complementary series character simplifies to
just the negated induced character: χ(g) = -(|K|⁻¹ ∑ x, ν(x⁻¹gx)).
This is because charW₁(g) = -1 and charVα₁(g) = 0 for elliptic g,
so χ(g) = (-1)·0 - 0 - Ind = -Ind. -/
private lemma Etingof.complementarySeriesChar_elliptic_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g =
    -((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) := by
  unfold Etingof.GL2.complementarySeriesChar
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  have hW : Etingof.GL2.charW₁ p n g = -1 := Etingof.charW₁_elliptic p n g hg
  have hV : Etingof.GL2.charVα₁ p n alpha g = 0 := Etingof.charVα₁_elliptic p n alpha g hg
  rw [hW, hV]
  ring

/-- The elliptic contribution to ∑ |χ|² equals q(q-1)³.

The proof decomposes into three steps:

**Step 1 (Conjugacy class decomposition)**: The sum over elliptic elements of
GL₂(𝔽_q) rewrites as (q(q-1)/2) times the sum over non-scalar elements of K.
This uses: (a) χ is a class function (all three components — charW₁, charVα₁,
induced character — are conjugation-invariant), (b) each elliptic conjugacy class
has |G|/|C_G(ζ)| = |G|/|K| = q(q-1) elements, (c) ζ ~ ζ^q identifies pairs.

**Step 2 (Character values on K)**: For non-scalar ζ ∈ K:
- charW₁(ζ) = -1 (0 fixed points on P¹ for elliptic elements)
- charVα₁(ζ) = 0 (no conjugate of elliptic ζ is upper triangular)
- Ind_K^G ℂ_ν(ζ) = ν(ζ) + ν^q(ζ) (Frobenius formula; normalizer N_G(K)/K ≅ Gal(F_{q²}/F_q))
So χ(ζ) = -(ν(ζ) + ν^q(ζ)) and |χ(ζ)|² = 2 + ν^{q-1}(ζ) + ν^{1-q}(ζ).

**Step 3 (Character orthogonality)**: Since ν^q ≠ ν, the character ν^{q-1}
is nontrivial on F_{q²}× ≅ K, so ∑_K ν^{q-1} = 0 (by `sum_nontrivial_char_eq_zero`).
On F_q× ⊂ K, ν^{q-1} = 1 (since x^q = x for x ∈ F_q×), so ∑_{F_q×} ν^{q-1} = q-1.
Therefore ∑_{K\F_q×} ν^{q-1} = -(q-1), and similarly for ν^{1-q}.
Total: 2q(q-1) - 2(q-1) = 2(q-1)². Assembly: q(q-1)/2 · 2(q-1)² = q(q-1)³. -/
private lemma Etingof.elliptic_contribution
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      Etingof.GL2.complementarySeriesChar p n nu g *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
  sorry

/-- Arithmetic identity: contributions from scalar, parabolic, and elliptic conjugacy classes
sum to |GL₂(𝔽_q)|. Specifically:
  (q-1)³ + (q-1)(q²-1) + q(q-1)³ = q(q-1)²(q+1) = (q²-1)(q²-q) -/
private lemma Etingof.innerProduct_arith_identity (q : ℂ) :
    (q - 1) ^ 3 + (q - 1) * (q ^ 2 - 1) + q * (q - 1) ^ 3 =
    (q ^ 2 - 1) * (q ^ 2 - q) := by
  ring

/-- The inner product sum ∑_{g∈G} |χ(g)|² equals |G| = q(q-1)²(q+1).

The proof splits the sum over GL₂(𝔽_q) by conjugacy class type:
- **Scalar matrices** xI (q-1 elements): |χ(xI)|² = (q-1)², total (q-1)³
- **Parabolic matrices** (q-1)(q²-1) elements: |χ|² = 1, total (q-1)(q²-1)
- **Non-scalar semisimple** (split): χ = 0, total 0
- **Elliptic elements**: uses character orthogonality ∑_{F_{q²}×} ν^{q-1}(ζ) = 0
  to get total q(q-1)³

Combined: (q-1)³ + (q-1)(q²-1) + q(q-1)³ = (q-1)²[q-1+q+1+q(q-1)] = (q-1)²q(q+1) = |G|.
-/
private lemma Etingof.innerProduct_sum_eq_card
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    (∑ x : GL2 p n,
      Etingof.GL2.complementarySeriesChar p n nu x *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) : ℂ) =
    (Fintype.card (GL2 p n) : ℂ) := by
  have hn_ne : n ≠ 0 := by omega
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq1 : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    exact Nat.one_lt_pow hn_ne hp.out.one_lt
  -- |GL₂(𝔽_q)| = (q²-1)(q²-q)
  have hG : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
  -- Step 1: Split sum by conjugacy class type
  set χ := Etingof.GL2.complementarySeriesChar p n nu
  set f : GL2 p n → ℂ := fun g => χ g * starRingEnd ℂ (χ g)
  -- Use GL2.sum_split (GL2 and GL2' are definitionally equal)
  have hsplit := GL2.sum_split (p := p) (n := n) f
  rw [hsplit]
  -- Step 2: Compute contribution from each class type
  -- Scalar: each element contributes (q-1)², total = (q-1) * (q-1)² = (q-1)³
  have h_scalar : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsScalar g), f g =
      ((q : ℂ) - 1) ^ 3 := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsScalar (p := p) (n := n) g),
        f g = ((q : ℂ) - 1) ^ 2 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_scalar p n nu g hg.2 hn_ne
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isScalar hn_ne, nsmul_eq_mul]
    have h1 : 1 ≤ q := by omega
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1]; ring
  -- Parabolic: each element contributes 1, total = (q-1)(q²-1)
  have h_parabolic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic g), f g =
      ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - 1) := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic (p := p) (n := n) g),
        f g = 1 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_parabolic p n hp2 nu g hg.2 hn_ne
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isParabolic hn_ne, nsmul_eq_mul,
      mul_one]
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := by nlinarith
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  -- Split semisimple: each element contributes 0
  have h_split : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsSplitSemisimple g), f g = 0 := by
    apply Finset.sum_eq_zero; intro g hg
    rw [Finset.mem_filter] at hg
    have h0 : χ g = 0 := Etingof.complementaryChar_splitSemisimple_eq_zero p n hp2 nu g hg.2
    change χ g * starRingEnd ℂ (χ g) = 0
    rw [h0, map_zero, mul_zero]
  -- Elliptic: total = q(q-1)³
  have h_elliptic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsElliptic g), f g =
      (q : ℂ) * ((q : ℂ) - 1) ^ 3 :=
    Etingof.elliptic_contribution p n nu hn_ne
  -- Combine
  rw [h_scalar, h_parabolic, h_split, h_elliptic, hG]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := by nlinarith
  have h3 : q ≤ q ^ 2 := by nlinarith
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]; ring

/-- **Lemma 5.25.3 (part 1)**: The complementary series virtual character
satisfies ⟨χ, χ⟩ = 1, establishing (via Lemma 5.7.2) that it is the character
of an actual irreducible representation. (Etingof Lemma 5.25.3) -/
theorem Etingof.Lemma5_25_3_innerProduct
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ x : GL2 p n,
        Etingof.GL2.complementarySeriesChar p n nu x *
        starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) = 1 := by
  rw [Etingof.innerProduct_sum_eq_card p n hp2 nu hn]
  simp only [smul_eq_mul]
  have hcard : (Fintype.card (GL2 p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact inv_mul_cancel₀ hcard

/-- **Lemma 5.25.3 (part 2)**: The complementary series virtual character
satisfies χ(1) = q - 1 > 0, confirming it has positive dimension.
(Etingof Lemma 5.25.3) -/
private lemma Etingof.charW₁_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] :
    Etingof.GL2.charW₁ p n 1 =
      (Fintype.card (GaloisField p n) : ℂ) := by
  unfold GL2.charW₁
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  norm_num

private lemma Etingof.dimension_arith_identity
    (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hqp1 : q + 1 ≠ 0) :
    q * (q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q))) -
    q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) -
    (q ^ 2 - 1)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) = q - 1 := by
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [this]; exact mul_ne_zero hq1 hqp1
  have hqm1sq : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  field_simp [hq, hq1, hqp1, hq2m1, hqm1sq]
  ring

theorem Etingof.Lemma5_25_3_dimension
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    Etingof.GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1 ∧
    (0 : ℝ) < (p ^ n : ℝ) - 1 := by
  constructor
  · -- Part 1: χ(1) = q - 1
    -- At g = 1, x⁻¹·1·x = 1 for all x
    have h1x : ∀ x : GL2 p n, x⁻¹ * 1 * x = 1 := by intro x; simp
    -- Unfold and simplify the character at identity
    change GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1
    unfold GL2.complementarySeriesChar GL2.charW₁ GL2.charVα₁
    simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h1x]
    -- Simplify nu at identity: nu(⟨1, _⟩) = nu(1) = 1, scalarToElliptic(1) = 1
    have hnu_sub : ∀ h, nu (⟨1, h⟩ : ↥(GL2.ellipticSubgroup p n)) = 1 :=
      fun h => (congrArg nu (Subtype.ext rfl)).trans (map_one nu)
    simp only [hnu_sub, Units.val_one]
    -- Resolve Fin 2 if-conditions and simplify 0*t²+0*t-0=0
    norm_num
    -- Goal: q * (q⁻¹ * (q-1)²⁻¹ * |G|) - q⁻¹ * (q-1)²⁻¹ * |G| - |K|⁻¹ * |G| = p^n - 1
    -- where q = p^n, |G| = |GL₂(𝔽_q)|, |K| = |𝔽_{q²}×|
    -- Factor out |G|: ((q-1) * q⁻¹ * (q-1)²⁻¹ - q⁻¹ * (q-1)²⁻¹ - |K|⁻¹) * |G|
    -- = ((q-1)/((q-1)²q) - 1/((q-1)²q) - 1/|K|) * |G|
    -- = (1/((q-1)q) - 1/|K|) * |G|  -- since (q-1-1)/((q-1)²q) = ... wait
    -- Actually: (q-1)/(q(q-1)²) = 1/(q(q-1))
    -- And 1/(q(q-1)²) = 1/(q(q-1)²) stays.
    -- So: q/(q(q-1)²) - 1/(q(q-1)²) - 1/(q²-1) = (q-1)/(q(q-1)²) - 1/(q²-1)
    --   = 1/(q(q-1)) - 1/((q-1)(q+1))  = ((q+1) - q) / (q(q-1)(q+1)) = 1/(q(q-1)(q+1))
    -- Then 1/(q(q-1)(q+1)) * q(q-1)²(q+1) = q-1. ✓
    -- This needs |GL₂| = q(q²-1)(q-1) and |K| = q²-1
    -- Convert all Fintype.card to Nat.card to avoid Fintype instance mismatches
    simp only [← Nat.card_eq_fintype_card]
    have hn_ne : n ≠ 0 := by omega
    have hq_val : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn_ne
    have hq1 : 1 < Nat.card (GaloisField p n) := by
      rw [hq_val]; exact Nat.one_lt_pow hn_ne hp.out.one_lt
    -- GL₂ cardinality (card_GL_field uses Fintype.card for q, convert to Nat.card)
    have hG : Nat.card (GL2 p n) =
        (Nat.card (GaloisField p n) ^ 2 - 1) *
        (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
      haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
      have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
      simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
                  ← Nat.card_eq_fintype_card] at this
      exact this
    -- Elliptic subgroup cardinality: |K| = |𝔽_{q²}×| = q² - 1
    have hK : Nat.card ↥(GL2.ellipticSubgroup p n) =
        Nat.card (GaloisField p n) ^ 2 - 1 := by
      -- K = fieldExtEmbed.range
      change Nat.card ↥(GL2.fieldExtEmbed p n).range = _
      -- fieldExtEmbed is injective (leftMulMatrix is injective as AlgHom from a field)
      have hinj : Function.Injective (GL2.fieldExtEmbed p n) := by
        intro a b hab
        unfold GL2.fieldExtEmbed at hab
        simp only [dif_neg hn_ne] at hab
        have hval := congr_arg (fun g => g.val) hab
        have := RingHom.injective
          (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
          (GaloisField p (2 * n)) (finrank_galoisField_ext p n hn_ne))).toRingHom
        exact Units.ext (this hval)
      -- |range| = |domain| since injective
      have : (GL2.fieldExtEmbed p n).range.carrier = Set.range (GL2.fieldExtEmbed p n) :=
        MonoidHom.coe_range _
      rw [show Nat.card ↥(GL2.fieldExtEmbed p n).range =
        Nat.card ↥(Set.range (GL2.fieldExtEmbed p n)) from by
        congr 1]
      rw [Nat.card_range_of_injective hinj]
      -- |𝔽_{q²}ˣ| = |𝔽_{q²}| - 1 = p^(2n) - 1 = (p^n)² - 1 = q² - 1
      rw [Nat.card_units]
      rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn_ne)]
      rw [hq_val]; ring_nf
    -- Substitute q = p^n throughout (now the goal uses Nat.card)
    rw [hq_val] at hG hK ⊢
    -- Substitute G and K cardinalities
    rw [hG, hK]
    -- Now the goal is purely in terms of p, n as ℕ with casts to ℂ
    -- Convert ℕ subtractions and prove with field_simp + ring
    have h1 : 1 ≤ p ^ n := by omega
    have h2 : 1 ≤ (p ^ n) ^ 2 := by nlinarith
    have h3 : p ^ n ≤ (p ^ n) ^ 2 := by nlinarith
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_pow,
               Nat.cast_one]
    -- Now all ℕ casts are gone, everything is in (↑p : ℂ)^n
    -- Nonzero conditions for field_simp
    have hpn_ne : (↑p : ℂ) ^ n ≠ 0 := by
      exact_mod_cast show (p ^ n : ℕ) ≠ 0 by omega
    have hpn1_ne : (↑p : ℂ) ^ n - 1 ≠ 0 := by
      intro h
      have : (p ^ n : ℕ) = 1 := by exact_mod_cast sub_eq_zero.mp h
      omega
    have hpnp1_ne : (↑p : ℂ) ^ n + 1 ≠ 0 := by
      have : (↑(p ^ n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast [Nat.cast_pow] at this; exact this
    -- Apply the standalone arithmetic identity
    exact dimension_arith_identity _ hpn_ne hpn1_ne hpnp1_ne
  · -- Part 2: q - 1 > 0
    have hp_pos := hp.out.pos
    have h1 : 1 < p ^ n := by
      calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hn
        _ = p := pow_one p
        _ ≥ 2 := hp.out.two_le
    have h2 : (1 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast h1
    linarith
