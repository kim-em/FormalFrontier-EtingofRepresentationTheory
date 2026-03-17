import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1

/-!
# Theorem 5.22.1: Weyl Character Formula for GL(V)

The character of the irreducible polynomial representation `L_λ` of `GL_N(k)`
with highest weight `λ` equals the Schur polynomial `S_λ(x₁, …, x_N)`.
Consequently, `dim L_λ = S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i)`
(the dimension formula is already captured by Proposition 5.21.2).

When `λ : Fin N → ℕ` (at most `N` parts), `L_λ` is always nonzero.
The vanishing case `L_λ = 0` arises only when the partition has strictly more
parts than `dim V`, which is excluded by our parameterization.

## Mathlib correspondence

Schur polynomials are defined locally in `Proposition5_21_1`.
The Schur module (highest weight representation of GL_N) and its formal
character are not yet in Mathlib; they are defined as opaque placeholders.
-/

open MvPolynomial Finset CategoryTheory

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- The Schur module `L_λ`: the irreducible polynomial representation of `GL_N(k)`
with highest weight `λ = (λ₁ ≥ ⋯ ≥ λ_N ≥ 0)`.

This is the image of the Schur functor `𝕊_λ` applied to `k^N`. Over algebraically
closed fields of characteristic zero, it is the unique irreducible polynomial
representation with the given highest weight. Not yet in Mathlib. -/
noncomputable def SchurModule (N : ℕ) (lam : Fin N → ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) := sorry

/-- The formal character of a finite-dimensional polynomial `GL_N(k)`-representation,
as a polynomial in `N` variables over `ℚ`. The formal character encodes the trace
of the representation evaluated on diagonal matrices `diag(x₁, …, x_N)` as a
polynomial in `x₁, …, x_N`. Not yet in Mathlib. -/
noncomputable def formalCharacter (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    MvPolynomial (Fin N) ℚ := sorry

/-- **Weyl character formula for GL(V)**: the formal character of the Schur module
`L_λ` equals the Schur polynomial `S_λ(x₁, …, x_N)`.

As a corollary, `dim L_λ = S_λ(1, …, 1)`, which by Proposition 5.21.2 equals
`∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i)`.
(Etingof Theorem 5.22.1) -/
theorem Theorem5_22_1
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N lam) = schurPoly N lam := by
  sorry

end Etingof
