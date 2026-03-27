import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Example 9.4.4: Homological dimension of polynomial algebra (Hilbert syzygies)

By the Hilbert syzygies theorem, the homological dimension of k[x₁, …, xₙ] is n
(where k is a field).

## Mathlib correspondence

The Hilbert syzygy theorem is not yet in Mathlib.

## Proof strategy

We prove two directions:
1. **Upper bound** (`homologicalDimension ≤ n`): Every `MvPolynomial (Fin n) k`-module
   has projective dimension ≤ n. This follows by induction on n using
   `MvPolynomial.finSuccEquiv : MvPolynomial (Fin (n+1)) R ≃ₐ Polynomial (MvPolynomial (Fin n) R)`
   and the theorem `gl.dim R[x] = gl.dim R + 1` for Noetherian R.
2. **Lower bound** (`n ≤ homologicalDimension`): The residue field `k`, viewed as a
   `k[x₁,...,xₙ]`-module via the augmentation map, has projective dimension exactly n.
   This is witnessed by the Koszul resolution showing `Ext^n(k, k) ≠ 0`.
-/

universe u

open CategoryTheory

namespace Etingof

/-- A field has homological dimension 0: every module is projective.
This follows because every module over a division ring is free
(`Module.Free.of_divisionRing`), free modules are projective
(`Module.Projective.of_free`), and projective objects have
`HasProjectiveDimensionLT 1`. -/
theorem field_hasHomologicalDimensionLE_zero (k : Type u) [Field k] :
    HasHomologicalDimensionLE k 0 := by
  intro M
  letI : _root_.Module.Free k M := _root_.Module.Free.of_divisionRing k M
  letI : _root_.Module.Projective k M :=
    _root_.Module.Projective.of_free (R := k) (P := M)
  letI : Projective M := M.projective_of_categoryTheory_projective
  infer_instance

/-- Upper bound: Every `MvPolynomial (Fin n) k`-module has projective dimension ≤ n.

**Proof outline (by induction on n):**
- Base case (n = 0): `MvPolynomial (Fin 0) k ≃+* k` via `isEmptyRingEquiv`.
  Transfer `field_hasHomologicalDimensionLE_zero` across the ring equivalence using
  `restrictScalarsEquivalenceOfRingEquiv`, which preserves Ext groups.
- Inductive step: `MvPolynomial (Fin (n+1)) k ≃ₐ Polynomial (MvPolynomial (Fin n) k)` via
  `finSuccEquiv`. By induction, `MvPolynomial (Fin n) k` has hd ≤ n.
  The key lemma is that for a Noetherian ring R, `gl.dim R[x] ≤ gl.dim R + 1`.
  This uses the short exact sequence `0 → M[x] →(·x) M[x] → M → 0` and dimension shifting. -/
theorem mvPolynomial_hasHomologicalDimensionLE (k : Type u) [Field k] (n : ℕ) :
    HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n := by
  sorry

/-- Lower bound: Not every `MvPolynomial (Fin n) k`-module has projective dimension < n.

**Proof outline:** The residue field `k = k[x₁,...,xₙ]/(x₁,...,xₙ)` has projective
dimension exactly n. This follows from the Koszul complex computation showing
`Ext^n_{k[x₁,...,xₙ]}(k, k) ≅ k ≠ 0`, hence `k` does not have
`HasProjectiveDimensionLT n`. -/
theorem mvPolynomial_not_hasHomologicalDimensionLE_of_lt (k : Type u) [Field k]
    {n d : ℕ} (hd : d < n) :
    ¬ HasHomologicalDimensionLE (MvPolynomial (Fin n) k) d := by
  sorry

/-- The Hilbert syzygy theorem: the homological dimension of k[x₁, …, xₙ] is n.
(Etingof Example 9.4.4) -/
theorem Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :
    homologicalDimension (MvPolynomial (Fin n) k) = n := by
  unfold homologicalDimension
  apply le_antisymm
  · -- Upper bound: ⨅ ... ≤ n
    apply iInf_le_of_le n
    apply iInf_le_of_le (mvPolynomial_hasHomologicalDimensionLE k n)
    exact le_refl _
  · -- Lower bound: n ≤ ⨅ ...
    apply le_iInf₂
    intro d hd
    by_cases h : d < n
    · exact absurd hd (mvPolynomial_not_hasHomologicalDimensionLE_of_lt k h)
    · push_neg at h
      exact_mod_cast h

end Etingof
