import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Basic algebra existence

For a finite-dimensional algebra `A` over an algebraically closed field `k`,
there exists a basic algebra `B` that is Morita equivalent to `A`.

## Construction (sketch)

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

## Status

The theorem is stated with `sorry` pending formalization of:
- Extraction of primitive idempotents from the Wedderburn–Artin decomposition
- Proof that the corner ring is basic
- Proof of Morita equivalence via the progenerator `Ae`
-/

universe u

namespace Etingof

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
  sorry

end Etingof
