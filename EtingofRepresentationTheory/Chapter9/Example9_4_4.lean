import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

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

/-- The Hilbert syzygy theorem (lower bound): if every module over k[x₁, …, xₙ] has
projective dimension ≤ d, then n ≤ d. Equivalently, the residue field
k = k[x₁,…,xₙ]/(x₁,…,xₙ) has projective dimension exactly n.

The proof uses the Koszul complex to compute Ext^n(k, k) ≅ k ≠ 0. -/
theorem mvPolynomial_homologicalDimension_le_iff (k : Type u) [Field k] :
    ∀ n d, HasHomologicalDimensionLE (MvPolynomial (Fin n) k) d → n ≤ d
  | 0, d, _ => Nat.zero_le d
  | n + 1, d, hd => by
    -- Need to show Ext^{n+1}(k, k) ≠ 0 where k = R/(x₁,...,x_{n+1}).
    -- This uses the Koszul complex computation. Not yet in Mathlib.
    sorry

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
