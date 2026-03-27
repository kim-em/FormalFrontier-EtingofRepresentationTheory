import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Morita.Matrix

/-!
# Basic algebra existence

For a finite-dimensional algebra `A` over an algebraically closed field `k`,
there exists a basic algebra `B` that is Morita equivalent to `A`.

## Construction

1. `A` is Artinian, hence semiprimary: `A / rad(A)` is semisimple and `rad(A)`
   is nilpotent.
2. By Wedderburn–Artin, `A / rad(A) ≅ ∏ₜ Matₙₜ(Dₜ)` where `Dₜ` are division
   rings. Since `k` is algebraically closed, each `Dₜ = k`.
3. Extract one primitive idempotent `ē₁₁` per matrix block in `A / rad(A)`.
4. Lift these orthogonal idempotents to `A` using
   `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` (Corollary 9.1.3).
5. Set `e = ∑ eᵢ` and `B = eAe`. Then `B` is basic (each simple `B`-module
   is 1-dimensional over `k`) and Morita equivalent to `A` (via the
   progenerator `Ae`).

## Decomposition

The proof is decomposed into two helper lemmas:

* `exists_full_idempotent_basic_corner`: Existence of a full idempotent whose
  corner ring is basic. This uses Wedderburn–Artin over algebraically closed
  fields and idempotent lifting.

* `morita_equiv_of_full_idempotent`: The Morita equivalence between `A` and
  the corner ring `eAe` for a full idempotent `e` (one with `AeA = A`). This
  is the deep part of the proof, requiring construction of the functors
  `M ↦ eM` and `N ↦ Ae ⊗_{eAe} N` and verification they form an equivalence.
-/

universe u

namespace Etingof

/-! ## Full idempotent predicate -/

/-- An idempotent `e` in a ring `A` is **full** if the two-sided ideal it
generates is all of `A`, i.e., `AeA = A`. Full idempotents are precisely the
idempotents for which the corner ring `eAe` is Morita equivalent to `A`. -/
def IsFullIdempotent {A : Type*} [Ring A] (e : A) : Prop :=
  IsIdempotentElem e ∧ Ideal.span {a * e * b | (a : A) (b : A)} = ⊤

/-! ## Helper: Existence of full idempotent with basic corner ring

For a finite-dimensional algebra `A` over an algebraically closed field `k`,
there exists a full idempotent `e ∈ A` such that the corner ring `eAe` is basic.

Construction:
- A/Rad(A) is semisimple (Artinian + semiprimary)
- By Wedderburn–Artin: A/Rad(A) ≅ ∏ Mat_{n_i}(k)
- Pick one diagonal idempotent E_{11} per block → complete orthogonal system
- Lift to A via `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`
- Sum of lifted idempotents gives a full idempotent e
- eAe is basic: its simple modules correspond to k-lines (one per block) -/
private lemma exists_full_idempotent_basic_corner
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (e : A) (he : IsFullIdempotent e),
      @IsBasicAlgebra k _ (CornerRing (k := k) e) (CornerRing.instRing he.1)
        (CornerRing.instAlgebra he.1) := by
  sorry

/-! ## Helper: Morita equivalence via full idempotent

For a ring `A` and a full idempotent `e` (i.e., `AeA = A`), `A` and `eAe` are
Morita equivalent. The equivalence is given by the functors:
- `F : A-Mod → eAe-Mod`, `M ↦ eM` (restriction to the e-corner)
- `G : eAe-Mod → A-Mod`, `N ↦ Ae ⊗_{eAe} N` (induction from the corner)

with natural isomorphisms `FG ≅ Id` and `GF ≅ Id`.

The fullness condition `AeA = A` is essential: it ensures `G` is essentially
surjective (every A-module M satisfies AeM = M when AeA = A). -/
private lemma morita_equiv_of_full_idempotent
    {k : Type u} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {e : A} (he : IsFullIdempotent e) :
    @MoritaEquivalent A _ (CornerRing (k := k) e) (CornerRing.instRing he.1) := by
  sorry

/-- **Basic algebra existence**: For a finite-dimensional algebra `A` over an
algebraically closed field `k`, there exists a basic algebra `B` (all simple
modules 1-dimensional) that is Morita equivalent to `A`.

This is the constructive core of Corollary 9.7.3(i). The witness `B` is
a corner ring `eAe` where `e` is a sum of lifted primitive idempotents,
one per isomorphism class of simple `A`-modules. -/
theorem exists_basic_morita_equivalent
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      IsBasicAlgebra k B ∧ MoritaEquivalent A B := by
  obtain ⟨e, he, hbasic⟩ := exists_full_idempotent_basic_corner k A
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he.1
  exact ⟨CornerRing (k := k) e,
    CornerRing.instRing he.1,
    CornerRing.instAlgebra he.1,
    CornerRing.instModuleFinite,
    hbasic,
    morita_equiv_of_full_idempotent he⟩

end Etingof
