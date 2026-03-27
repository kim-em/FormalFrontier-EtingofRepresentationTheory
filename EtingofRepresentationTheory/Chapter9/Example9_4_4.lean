import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Example 9.4.4: Homological dimension of polynomial algebra (Hilbert syzygies)

By the Hilbert syzygies theorem, the homological dimension of k[x₁, …, xₙ] is n
(where k is a field).

## Mathlib correspondence

The Hilbert syzygy theorem is not yet in Mathlib.
-/

universe u

open Etingof CategoryTheory

/-- Over a semisimple ring, every module is projective and hence has projective dimension ≤ 0. -/
theorem hasHomologicalDimensionLE_zero_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R] [Small.{u} R] :
    HasHomologicalDimensionLE R 0 := by
  intro M
  have : Module.Projective R M := Module.projective_of_isSemisimpleRing R M
  have : Projective M := M.projective_of_categoryTheory_projective
  infer_instance

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
    -- The inductive step requires: gl.dim(R[x]) ≤ gl.dim(R) + 1
    -- This uses the exact sequence 0 → R[x] ⊗_R M → R[x] ⊗_R M → M → 0
    -- and is the core of the Hilbert syzygy theorem. Not yet in Mathlib.
    sorry

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
