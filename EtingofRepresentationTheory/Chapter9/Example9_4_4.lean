import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Example 9.4.4: Homological dimension of polynomial algebra (Hilbert syzygies)

By the Hilbert syzygies theorem, the homological dimension of k[x₁, …, xₙ] is n
(where k is a field).

## Mathlib correspondence

The Hilbert syzygy theorem is not yet in Mathlib.
-/

universe u

open Etingof CategoryTheory Limits

/-- Over a semisimple ring, every module is projective and hence has projective dimension ≤ 0. -/
theorem hasHomologicalDimensionLE_zero_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R] [Small.{u} R] :
    HasHomologicalDimensionLE R 0 := by
  intro M
  have : Module.Projective R M := Module.projective_of_isSemisimpleRing R M
  have : Projective M := M.projective_of_categoryTheory_projective
  infer_instance

section EquivalencePreservesProjectiveDimension

variable {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {D : Type*} [Category D] [Abelian D]

/-- An equivalence of abelian categories with enough projectives preserves
projective dimension (upper bound). The proof is by induction on n, using
the kernel short exact sequence from a projective presentation. -/
theorem hasProjectiveDimensionLT_of_equivalence (E : C ≌ D) {X : C} :
    ∀ {n : ℕ}, HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT (E.functor.obj X) n := by
  intro n
  induction n generalizing X with
  | zero =>
    intro h
    exact (E.functor.map_isZero
      (isZero_of_hasProjectiveDimensionLT_zero X)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective X := (projective_iff_hasProjectiveDimensionLT_one X).mpr h
      have : Projective (E.functor.obj X) := (E.map_projective_iff X).mpr hproj
      exact (projective_iff_hasProjectiveDimensionLT_one _).mp this
    | succ m =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (m + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (m + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (m + 1) (by omega)) h
      have hEK := ih hK
      have hEP : Projective (E.functor.obj pp.p) := (E.map_projective_iff pp.p).mpr pp.projective
      have hEP_pd : HasProjectiveDimensionLT (E.functor.obj pp.p) (m + 2) :=
        hasProjectiveDimensionLT_of_ge (E.functor.obj pp.p) 1 (m + 2) (by omega)
      exact (hSE.map_of_exact E.functor).hasProjectiveDimensionLT_X₃ (m + 1) hEK hEP_pd

end EquivalencePreservesProjectiveDimension

/-- Ring isomorphisms preserve homological dimension. -/
theorem hasHomologicalDimensionLE_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (d : ℕ) (h : Etingof.HasHomologicalDimensionLE S d) :
    Etingof.HasHomologicalDimensionLE R d := by
  intro M
  -- restrictScalarsEquivalenceOfRingEquiv e : ModuleCat S ≌ ModuleCat R
  -- functor: ModuleCat S ⥤ ModuleCat R, inverse: ModuleCat R ⥤ ModuleCat S
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  -- E.inverse.obj M : ModuleCat S, has pd ≤ d by hypothesis
  have hN : HasProjectiveDimensionLE (E.inverse.obj M) d := h (E.inverse.obj M)
  -- The equivalence preserves projective dimension: E.functor sends it back to ModuleCat R
  have hFN := hasProjectiveDimensionLT_of_equivalence E hN
  -- E.counitIso.app M : (E.inverse ⋙ E.functor).obj M ≅ (𝟭 _).obj M
  -- which is E.functor.obj (E.inverse.obj M) ≅ M
  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _ (E.counitIso.app M) (d + 1) hFN

/-- The polynomial ring extension theorem for global dimension: if every R-module has
projective dimension ≤ d, then every R[x]-module has projective dimension ≤ d + 1.

The proof constructs the standard short exact sequence for any R[x]-module M:
  0 → R[x] ⊗_R M|_R → R[x] ⊗_R M|_R → M → 0
and uses dimension shifting. Neither this SES nor the flat base change theorem
for projective dimension is yet in Mathlib. -/
theorem hasHomologicalDimensionLE_polynomial {R : Type u} [CommRing R] [Small.{u} R] (d : ℕ)
    (h : Etingof.HasHomologicalDimensionLE R d) :
    Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1) := by
  sorry

/-- The Hilbert syzygy theorem (upper bound): every module over k[x₁, …, xₙ] has
projective dimension ≤ n.

This is the hard direction of the Hilbert syzygy theorem. The proof uses the Koszul
resolution or induction on n via the change-of-rings spectral sequence. Neither
the Koszul complex nor the polynomial ring global dimension theorem is currently
in Mathlib. -/
private instance isSemisimpleRing_mvPolynomial_fin_zero (k : Type u) [Field k] :
    IsSemisimpleRing (MvPolynomial (Fin 0) k) :=
  (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv.isSemisimpleRing

theorem mvPolynomial_hasHomologicalDimensionLE (k : Type u) [Field k] :
    ∀ n, HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n
  | 0 => hasHomologicalDimensionLE_zero_of_isSemisimpleRing _
  | n + 1 => by
    -- By induction, MvPolynomial (Fin n) k has homological dimension ≤ n
    have ih := mvPolynomial_hasHomologicalDimensionLE k n
    -- MvPolynomial (Fin (n+1)) k ≃ₐ Polynomial (MvPolynomial (Fin n) k)
    have e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    -- By the polynomial extension theorem, Polynomial (MvPolynomial (Fin n) k)
    -- has homological dimension ≤ n + 1
    have h_poly := hasHomologicalDimensionLE_polynomial n ih
    -- Transfer across the ring isomorphism
    exact hasHomologicalDimensionLE_of_ringEquiv e (n + 1) h_poly

section PolynomialLowerBound

open Polynomial

/-! ### Polynomial ring has positive global dimension

For a nontrivial commutative ring R, the polynomial ring R[x] is not semisimple.
The key argument: the augmentation module R (where x acts as 0) is not projective
over R[x], because any R[x]-linear section of the evaluation-at-0 map would be
killed by x (since x acts as 0 on R), hence zero, contradicting surjectivity. -/

/-- In Polynomial R, multiplication by X is injective (for any ring R). -/
private theorem Polynomial.X_mul_eq_zero {R : Type u} [CommRing R] {p : R[X]} (h : X * p = 0) :
    p = 0 := by
  ext n
  have h1 := congr_arg (Polynomial.coeff · (n + 1)) h
  simp only [coeff_X_mul, coeff_zero] at h1
  exact h1

/-- The polynomial ring over a nontrivial commutative ring has global dimension ≥ 1.
Equivalently, it is not semisimple: the augmentation module is not projective. -/
private theorem not_hasHomologicalDimensionLE_zero_polynomial
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Etingof.HasHomologicalDimensionLE (Polynomial R) 0 := by
  intro hall
  -- The augmentation module: R with R[X]-action where X acts as 0
  let φ : R →ₗ[R] R := 0
  let A := Module.AEval' φ
  let MA := ModuleCat.of (Polynomial R) A
  -- Every R[X]-module has pd ≤ 0, so MA is projective
  have hpd : HasProjectiveDimensionLE MA 0 := hall MA
  have hproj : Projective MA :=
    (projective_iff_hasProjectiveDimensionLT_one MA).mpr hpd
  have hmod : Module.Projective (Polynomial R) A :=
    MA.projective_of_module_projective
  -- The surjection: R[X] → A sending p ↦ p • 1_A
  let one_A : A := Module.AEval'.of φ (1 : R)
  let surj := LinearMap.toSpanSingleton (Polynomial R) A one_A
  have hsurj : Function.Surjective surj := by
    intro a
    refine ⟨Polynomial.C ((Module.AEval'.of φ).symm a), ?_⟩
    simp only [surj, LinearMap.toSpanSingleton_apply]
    rw [Module.AEval.C_smul,
      ← (Module.AEval'.of φ).map_smul, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  -- Get section from projectivity
  obtain ⟨sect, hsect⟩ :=
    Module.projective_lifting_property surj LinearMap.id hsurj
  -- Show sect = 0: X • a = 0 in A (since X acts as 0),
  -- so X * sect(a) = sect(X • a) = 0
  have X_smul_zero : ∀ a : A, (X : R[X]) • a = 0 := by
    intro a
    rw [show a = Module.AEval'.of φ ((Module.AEval'.of φ).symm a) from
      ((Module.AEval'.of φ).apply_symm_apply a).symm,
      Module.AEval'.X_smul_of, LinearMap.zero_apply, map_zero]
  have hzero : ∀ a : A, sect a = 0 := by
    intro a
    apply Polynomial.X_mul_eq_zero
    calc X * sect a
        = sect ((X : R[X]) • a) := (sect.map_smul (X : R[X]) a).symm
      _ = sect 0 := by rw [X_smul_zero]
      _ = 0 := map_zero sect
  -- surj ∘ sect = id, but sect = 0 means every a = 0
  have hall_zero : ∀ a : A, a = 0 := by
    intro a
    have h := LinearMap.ext_iff.mp hsect a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hzero a,
      map_zero] at h
    exact h.symm
  -- But A ≅ R as additive groups, and R is nontrivial
  have : one_A ≠ 0 := by
    intro h
    exact one_ne_zero ((Module.AEval'.of φ).injective
      (h.trans (map_zero (Module.AEval'.of φ)).symm))
  exact this (hall_zero one_A)

/-- For any R-module M, if gldim(R[X]) ≤ d + 1, then pd_R(M) ≤ d.

The proof combines three ingredients, none of which are currently in Mathlib:

1. **SES construction**: For any R-module M, there is a short exact sequence
   0 → R[X] ⊗_R M →^{X·} R[X] ⊗_R M → M₀ → 0
   where M₀ is M with trivial X-action (X acts as 0).

2. **X-action vanishing**: From the contravariant LES of Ext applied to this SES,
   the map f* = precomp with X-multiplication is surjective on Ext^i(R[X]⊗M, Y)
   for i ≥ d+1. By `smul_comp` and `mk₀_id_comp`, f* equals scalar multiplication
   by X on Ext. Taking Y with trivial X-action (X · 𝟙_Y = 0), `smul_eq_comp_mk₀`
   gives f* = 0, hence Ext^i_{R[X]}(R[X]⊗M, Y₀) = 0 for i ≥ d+1.

3. **Shapiro's lemma**: The extension-restriction adjunction
   (`extendRestrictScalarsAdj Polynomial.C`) plus the fact that `extendScalars`
   preserves projective objects (from `preservesProjectiveObjects_of_adjunction` +
   `restrictScalars` preserves epimorphisms) gives:
     Ext^i_{R[X]}(R[X] ⊗_R M, Y₀) ≅ Ext^i_R(M, Y₀|_R)
   Since every R-module Z equals Y₀|_R for Y₀ = Z with trivial action,
   step 2 gives Ext^i_R(M, Z) = 0 for all Z and i ≥ d+1. -/
private theorem pd_le_of_polynomial_gldim (R : Type u) [CommRing R] (d : ℕ)
    (M : ModuleCat.{u} R)
    (h : Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1)) :
    HasProjectiveDimensionLE M d := by
  sorry

/-- If R is a nontrivial commutative ring and HasHomologicalDimensionLE (Polynomial R) (d+1),
then HasHomologicalDimensionLE R d. This is the key inductive step for the lower bound:
gldim(R[x]) ≥ gldim(R) + 1.

See `pd_le_of_polynomial_gldim` for the proof strategy. -/
private theorem hasHomologicalDimensionLE_of_polynomial_succ
    (R : Type u) [CommRing R] [Nontrivial R] (d : ℕ)
    (h : Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1)) :
    Etingof.HasHomologicalDimensionLE R d := by
  intro M
  exact pd_le_of_polynomial_gldim R d M h

end PolynomialLowerBound

/-- The Hilbert syzygy theorem (lower bound): if every module over k[x₁, …, xₙ] has
projective dimension ≤ d, then n ≤ d. Equivalently, the residue field
k = k[x₁,…,xₙ]/(x₁,…,xₙ) has projective dimension exactly n.

The proof is by induction on n, using the ring equivalence
k[x₁,…,x_{n+1}] ≃ k[x₁,…,xₙ][x_{n+1}] and the fact that polynomial extension
increases global dimension by at least 1. -/
theorem mvPolynomial_homologicalDimension_le_iff (k : Type u) [Field k] :
    ∀ n d, HasHomologicalDimensionLE (MvPolynomial (Fin n) k) d → n ≤ d
  | 0, d, _ => Nat.zero_le d
  | n + 1, d, hd => by
    -- Transfer via ring iso: MvPolynomial (Fin (n+1)) k ≃+* Polynomial (MvPolynomial (Fin n) k)
    have e := (MvPolynomial.finSuccEquiv k n).symm.toRingEquiv
    have hpoly : HasHomologicalDimensionLE (Polynomial (MvPolynomial (Fin n) k)) d :=
      hasHomologicalDimensionLE_of_ringEquiv e d hd
    -- Case split on d
    match d with
    | 0 => exact absurd hpoly (not_hasHomologicalDimensionLE_zero_polynomial _)
    | d' + 1 =>
      have hR := hasHomologicalDimensionLE_of_polynomial_succ _ d' hpoly
      have ih := mvPolynomial_homologicalDimension_le_iff k n d' hR
      omega

/-- The Hilbert syzygy theorem: the homological dimension of k[x₁, …, xₙ] is n.
(Etingof Example 9.4.4) -/
theorem Etingof.Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :
    Etingof.homologicalDimension (MvPolynomial (Fin n) k) = n := by
  unfold homologicalDimension
  apply le_antisymm
  · exact iInf₂_le n (mvPolynomial_hasHomologicalDimensionLE k n)
  · apply le_iInf₂
    intro d hd
    exact_mod_cast mvPolynomial_homologicalDimension_le_iff k n d hd
