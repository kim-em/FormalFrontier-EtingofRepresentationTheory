import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Formal character determines isomorphism class

For polynomial representations of `GL_N(k)` over algebraically closed fields,
the formal character determines the isomorphism class. This is a consequence of
the complete reducibility of polynomial representations (Schur-Weyl duality).

This file provides the formal-character isomorphism theorem and the weight space
shift computation for the determinant twist.

## Mathematical content

The key theorem `iso_of_formalCharacter_eq_schurPoly` states that a `GL_N(k)`-
representation whose formal character equals a Schur polynomial `S_λ` is
isomorphic to the Schur module `L_λ`. The proof requires:
1. Complete reducibility of polynomial `GL_N` representations
2. Uniqueness of irreducible components with a given highest weight

The previous formulation (`iso_of_glWeightSpace_finrank_eq`) was stated for
arbitrary `FDRep k (GL_N k)`, which is false: non-polynomial representations
like `det⁻¹` and `det⁻²` have all `ℕ`-valued weight spaces trivial (so the
equal-dimensions hypothesis holds vacuously) yet are non-isomorphic.
-/

open CategoryTheory MvPolynomial

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

/-- A `GL_N(k)`-representation whose formal character equals a Schur polynomial
`S_λ` is isomorphic to the Schur module `L_λ`.

This follows from complete reducibility of polynomial `GL_N` representations
(Schur-Weyl duality) together with the Weyl character formula (`Theorem5_22_1`),
which shows that distinct Schur modules have distinct characters.

The downstream use is in `schurModule_shift_iso_detTwist` (Proposition 5.22.2),
where both representations involved are polynomial and have character equal
to `schurPoly N (λ + 1^N)`. -/
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam) :
    Nonempty (M ≅ SchurModule k N lam) := by
  sorry

/-- The finsupp with all values equal to 1 on `Fin N`. -/
private def onesFinsupp (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

private theorem onesFinsupp_apply (N : ℕ) (i : Fin N) : onesFinsupp N i = 1 := by
  simp [onesFinsupp]

private theorem onesFinsupp_support (N : ℕ) : (onesFinsupp N).support = Finset.univ := by
  ext i; simp [onesFinsupp]

private theorem prod_X_eq_monomial_ones (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) =
      MvPolynomial.monomial (onesFinsupp N) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial (R := ℚ) (s := onesFinsupp N),
    onesFinsupp_support]
  simp_rw [onesFinsupp_apply, pow_one]

/-- If the weight space dimensions of `M₁` at weight `ν + (1,…,1)` equal those of `M₂` at `ν`
(for all `ν`), and weight spaces of `M₁` at weights with some zero component are trivial,
then the formal character of `M₁` is `(∏ Xᵢ) · char(M₂)`. -/
theorem formalCharacter_shift_of_weightSpace_finrank (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_shift : ∀ ν : Fin N → ℕ,
      Module.finrank k (glWeightSpace k N M₁ (fun i => ν i + 1)) =
        Module.finrank k (glWeightSpace k N M₂ ν))
    (h_vanish : ∀ μ : Fin N → ℕ, (∃ i, μ i = 0) →
      Module.finrank k (glWeightSpace k N M₁ μ) = 0) :
    formalCharacter k N M₁ =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N M₂ := by
  ext μ
  rw [formalCharacter_coeff, prod_X_eq_monomial_ones, coeff_monomial_mul']
  split_ifs with h
  · -- Case: onesFinsupp N ≤ μ, i.e., all μ i ≥ 1
    rw [one_mul, formalCharacter_coeff]
    have hge : ∀ i : Fin N, 1 ≤ μ i := fun i => by
      have := h i; rwa [onesFinsupp_apply] at this
    have key : (fun i => (μ - onesFinsupp N) i + 1) = (⇑μ : Fin N → ℕ) := by
      ext i; simp [Finsupp.tsub_apply, onesFinsupp_apply, Nat.sub_add_cancel (hge i)]
    have := h_shift (fun i => (μ - onesFinsupp N) i)
    rw [key] at this
    exact_mod_cast this
  · -- Case: ¬(onesFinsupp N ≤ μ), i.e., some μ i = 0
    have hexists : ∃ i : Fin N, (μ i : ℕ) = 0 := by
      by_contra hall
      push_neg at hall
      exact h fun i => by rw [onesFinsupp_apply]; exact Nat.one_le_iff_ne_zero.mpr (hall i)
    exact_mod_cast h_vanish (⇑μ) hexists

end Etingof
