import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Shapiro's Lemma for Ext (Subsingleton direction)

For the extension-restriction adjunction `extendScalars f ⊣ restrictScalars f`
where `f : R →+* S` between commutative rings:

1. `restrictScalars f` preserves epimorphisms (it's a forgetful functor)
2. `extendScalars f` preserves projective objects (from 1 + adjunction)
3. If `S` is projective as an `R`-module (e.g. `S = R[X]`), then `restrictScalars f`
   preserves projective objects.
4. Under these conditions, `HasProjectiveDimensionLT` transfers from
   `(extendScalars f).obj M` to `M` via a retraction argument + dimension shifting.

## Application

For the polynomial ring map `Polynomial.C : R →+* R[X]`:
- `R[X]` is free (hence projective) as an `R`-module
- The evaluation-at-0 map provides a retraction of the unit `M → G(F(M))`
- This gives: `HasProjectiveDimensionLT ((extendScalars C).obj M) n → HasProjectiveDimensionLT M n`

Combined with the Ext long exact sequence and X-action vanishing (issue #1868),
this proves the lower bound in the Hilbert syzygy theorem.
-/

universe u

open CategoryTheory Limits

namespace ModuleCat

section PreservesEpimorphisms

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The restriction-of-scalars functor preserves epimorphisms. This is because
an `S`-module epimorphism is surjective as a function, and viewing it as an
`R`-module map doesn't change the underlying function. -/
instance restrictScalars_preservesEpimorphisms :
    (restrictScalars f).PreservesEpimorphisms where
  preserves {X Y} g hg := by
    rw [ModuleCat.epi_iff_surjective] at hg ⊢
    exact hg

/-- The extension-of-scalars functor preserves projective objects,
since it is left adjoint to `restrictScalars f` which preserves epimorphisms. -/
instance extendScalars_preservesProjectiveObjects :
    (extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (extendRestrictScalarsAdj.{u} f)

end PreservesEpimorphisms

section HasProjectiveDimensionLT

open Abelian

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- An exact functor that preserves projective objects preserves `HasProjectiveDimensionLT`.

The proof is by induction on `n`:
- `n = 0`: The functor preserves zero objects (it's exact).
- `n = 1`: The functor preserves projective objects (by hypothesis).
- `n = k + 2`: Use a projective presentation `0 → K → P → X → 0`,
  map it through the functor to get another SES with projective middle term,
  then apply the `hasProjectiveDimensionLT_X₃` dimension shifting lemma. -/
theorem restrictScalars_preservesProjectiveDimensionLT
    [(restrictScalars.{u} f).PreservesProjectiveObjects]
    [(restrictScalars.{u} f).PreservesHomology]
    (X : ModuleCat.{u} S) :
    ∀ (n : ℕ), HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT ((restrictScalars f).obj X) n := by
  intro n
  induction n generalizing X with
  | zero =>
    intro h
    have hX := isZero_of_hasProjectiveDimensionLT_zero X
    exact ((restrictScalars f).map_isZero hX).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective X := (projective_iff_hasProjectiveDimensionLT_one X).mpr h
      have : Projective ((restrictScalars f).obj X) :=
        Functor.PreservesProjectiveObjects.projective_obj hproj
      exact (projective_iff_hasProjectiveDimensionLT_one _).mp this
    | succ k =>
      -- Take projective presentation: 0 → K → P → X → 0
      obtain ⟨pp⟩ := EnoughProjectives.presentation X
      let SC := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      -- K has HasProjectiveDimensionLT (k + 1) by dimension shifting
      have hK : HasProjectiveDimensionLT (kernel pp.f) (k + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (k + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (k + 1) (by omega))
          h
      -- IH: G(K) has HasProjectiveDimensionLT (k + 1)
      have hGK := ih (kernel pp.f) hK
      -- Map the SES through G (exact functor)
      have hGSE : (SC.map (restrictScalars f)).ShortExact :=
        hSE.map_of_exact (restrictScalars f)
      -- G(P) is projective
      have hGP_proj : Projective ((restrictScalars f).obj pp.p) :=
        Functor.PreservesProjectiveObjects.projective_obj pp.projective
      -- Dimension shift: G(X) has HasProjectiveDimensionLT (k + 2)
      exact hGSE.hasProjectiveDimensionLT_X₃ (k + 1) hGK
        (hasProjectiveDimensionLT_of_ge ((restrictScalars f).obj pp.p) 1 (k + 2)
          (by omega))

/-- If `restrictScalars f` preserves projective objects and `M` is a retract of
`(restrictScalars f).obj ((extendScalars f).obj M)`, then projective dimension
transfers: `HasProjectiveDimensionLT ((extendScalars f).obj M) n` implies
`HasProjectiveDimensionLT M n`.

The proof uses:
1. An exact functor preserving projectives preserves `HasProjectiveDimensionLT`
   (by induction on n using dimension shifting)
2. Retracts preserve `HasProjectiveDimensionLT` -/
theorem hasProjectiveDimensionLT_of_extendScalars
    [Small.{u} R] [Small.{u} S]
    [(restrictScalars.{u} f).PreservesProjectiveObjects]
    [(restrictScalars.{u} f).PreservesHomology]
    (M : ModuleCat.{u} R) (n : ℕ)
    (retraction : Retract M ((restrictScalars f).obj ((extendScalars f).obj M)))
    (h : HasProjectiveDimensionLT ((extendScalars f).obj M) n) :
    HasProjectiveDimensionLT M n := by
  have hG := restrictScalars_preservesProjectiveDimensionLT f
    ((extendScalars f).obj M) n h
  exact retraction.hasProjectiveDimensionLT n

end HasProjectiveDimensionLT

section ExtSubsingleton

open Abelian

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/- Shapiro's lemma (Subsingleton direction): For the extension-restriction adjunction
`extendScalars f ⊣ restrictScalars f`, if `Ext` at degree `i` from
`(extendScalars f).obj M` to `N` is subsingleton, then `Ext` at degree `i` from
`M` to `(restrictScalars f).obj N` is also subsingleton.

The hypothesis `(extendScalars f).PreservesHomology` is needed because the proof
maps a projective R-resolution of M to a projective S-resolution of F(M) via
`mapProjectiveResolution`, which requires F to be exact. This is satisfied when
S is flat as an R-module (e.g., S = R[X]).

**Proof approach** (cochain complex isomorphism, cf. Mathlib's `groupCohomology.coindIso`):
1. Take a projective resolution `P` of `M` (via `EnoughProjectives`).
2. `(extendScalars f).mapProjectiveResolution P` is a projective resolution of `F(M)`.
3. The adjunction `extendScalars f ⊣ restrictScalars f` gives degree-wise isos
   `Hom_S(F(P_n), N) ≅ Hom_R(P_n, G(N))` for each `n`.
4. These commute with coboundary maps by naturality of the adjunction, giving a
   cochain complex isomorphism `HomComplex(F(P), N) ≅ HomComplex(P, G(N))`.
5. The cochain complex iso induces an iso on cohomology = `CohomologyClass`, hence
   on `Ext` via `extEquivCohomologyClass`.
6. Subsingleton transfers through the equivalence.
-/

/-- The adjunction homEquiv commutes with precomposition by the functor map.
This is the naturality of `adj.homEquiv` in the first variable. -/
private lemma adj_homEquiv_naturality_left
    {X X' : ModuleCat.{u} R} {Y : ModuleCat.{u} S} (d : X' ⟶ X)
    (g : (extendScalars.{u, u, u} f).obj X ⟶ Y) :
    (extendRestrictScalarsAdj.{u} f).homEquiv X' Y
      ((extendScalars.{u, u, u} f).map d ≫ g) =
    d ≫ (extendRestrictScalarsAdj.{u} f).homEquiv X Y g := by
  simp [Adjunction.homEquiv_naturality_left]

theorem ext_subsingleton_of_extendScalars [Small.{u} R] [Small.{u} S]
    [(extendScalars.{u, u, u} f).PreservesHomology]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (i : ℕ)
    (h : Subsingleton (Ext.{u} ((extendScalars.{u, u, u} f).obj M) N i)) :
    Subsingleton (Ext.{u} M ((restrictScalars.{u} f).obj N) i) := by
  set F := extendScalars.{u, u, u} f
  set G := restrictScalars.{u} f
  set adj := extendRestrictScalarsAdj.{u} f
  letI : EnoughProjectives (ModuleCat.{u} R) := ModuleCat.enoughProjectives.{u}
  letI : EnoughProjectives (ModuleCat.{u} S) := ModuleCat.enoughProjectives.{u}
  -- F is additive (left adjoint of the additive functor G)
  letI : F.Additive := Adjunction.left_adjoint_additive adj
  -- Get a projective resolution of M
  have ⟨P⟩ : Nonempty (ProjectiveResolution M) := (inferInstance : HasProjectiveResolution M).out
  -- FP is a projective S-resolution of F(M)
  let FP : ProjectiveResolution (F.obj M) := F.mapProjectiveResolution P
  constructor
  intro e₁ e₂
  match i with
  | 0 =>
    -- Ext^0 ≅ Hom via addEquiv₀, adjunction transfers subsingleton
    apply Ext.addEquiv₀.injective
    have hHomS : Subsingleton (F.obj M ⟶ N) := by
      constructor; intro a b
      exact Ext.addEquiv₀.symm.injective (h.elim _ _)
    have : Subsingleton (M ⟶ G.obj N) := by
      constructor; intro a b
      exact (adj.homEquiv M N).symm.injective (Subsingleton.elim _ _)
    exact Subsingleton.elim _ _
  | n + 1 =>
    -- For degree n+1: cocycle/coboundary transfer via adjunction
    have hsub : e₁ - e₂ = 0 := by
      obtain ⟨g, hg, hge⟩ := P.extMk_surjective (e₁ - e₂) (n + 2) rfl
      -- Transfer g to the S-side via adjunction inverse
      set g' : FP.complex.X (n + 1) ⟶ N :=
        (adj.homEquiv (P.complex.X (n + 1)) N).symm g with hg'_def
      -- g' is a cocycle for FP: FP.d(n+2, n+1) ≫ g' = 0
      have hg'_cocycle : FP.complex.d (n + 2) (n + 1) ≫ g' = 0 := by
        rw [hg'_def]
        have : FP.complex.d (n + 2) (n + 1) = F.map (P.complex.d (n + 2) (n + 1)) := rfl
        rw [this, ← Adjunction.homEquiv_naturality_left_symm]
        simp [hg]
      -- Form the S-side Ext element; by subsingleton it equals 0
      have he' : FP.extMk g' (n + 2) rfl hg'_cocycle = 0 := h.elim _ _
      rw [FP.extMk_eq_zero_iff g' (n + 2) rfl hg'_cocycle n rfl] at he'
      obtain ⟨φ', hφ'⟩ := he'
      -- Transfer φ' back via adjunction
      set φ := (adj.homEquiv (P.complex.X n) N) φ' with hφ_def
      -- Show P.d(n+1, n) ≫ φ = g (coboundary condition on the R-side)
      have hcoboundary : P.complex.d (n + 1) n ≫ φ = g := by
        rw [hφ_def, ← adj_homEquiv_naturality_left f (P.complex.d (n + 1) n) φ']
        have : F.map (P.complex.d (n + 1) n) = FP.complex.d (n + 1) n := rfl
        rw [this, hφ']
        rw [hg'_def, Equiv.apply_symm_apply]
      rw [← hge, P.extMk_eq_zero_iff g (n + 2) rfl hg n rfl]
      exact ⟨φ, hcoboundary⟩
    exact sub_eq_zero.mp hsub

end ExtSubsingleton

end ModuleCat
