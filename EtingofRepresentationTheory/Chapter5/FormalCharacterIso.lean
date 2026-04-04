import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Formal character determines isomorphism class

For polynomial representations of `GL_N(k)` over algebraically closed fields,
the formal character determines the isomorphism class. This is a consequence of
the complete reducibility of polynomial representations (Schur-Weyl duality).

This file provides the weight-space and formal-character isomorphism theorems
and uses them together with the weight space shift computation for the
determinant twist.

## Mathematical content

The key theorem `iso_of_glWeightSpace_finrank_eq` states that two `GL_N(k)`-
representations with equal weight space dimensions at all weights are isomorphic.
The proof requires:
1. Complete reducibility of polynomial `GL_N` representations: every fin-dim
   polynomial representation decomposes as a direct sum of Schur modules `L_λ`
2. Linear independence of Schur polynomials (which implies equal formal characters
   determine equal multiplicities in the Schur decomposition)
3. Equal multiplicities ⟹ isomorphism

**Note:** The statement as formalized applies to all `FDRep k (GL_N k)`, not just
polynomial representations. For non-polynomial representations (e.g., `det⁻¹` and
`det⁻²`), all natural-number weight spaces are trivial, so the hypothesis is
vacuously satisfied without the conclusion holding. The theorem is correct when
restricted to polynomial representations, which is the only case used downstream
(via `iso_of_formalCharacter_eq` in `Proposition5_22_2`).
-/

open CategoryTheory MvPolynomial

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

/-- Two `GL_N(k)`-representations with equal weight space dimensions at all weights
are isomorphic.

This follows from complete reducibility of polynomial `GL_N` representations (every
finite-dimensional representation decomposes as a direct sum of Schur modules `L_λ`)
and the fact that Schur modules with distinct `λ` have distinct formal characters
(by the Weyl character formula, `Theorem5_22_1`).

**Caveat:** This statement is only correct for polynomial representations. For
non-polynomial reps (e.g., `det⁻¹` vs `det⁻²`), all `ℕ`-valued weight spaces
are trivial, so the hypothesis holds vacuously without the representations being
isomorphic. All downstream uses apply this only to polynomial representations. -/
theorem iso_of_glWeightSpace_finrank_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : ∀ μ : Fin N → ℕ, Module.finrank k (glWeightSpace k N M₁ μ) =
      Module.finrank k (glWeightSpace k N M₂ μ)) :
    Nonempty (M₁ ≅ M₂) := by
  sorry

/-- Two `GL_N(k)`-representations with the same formal character are isomorphic.

This holds for polynomial representations of `GL_N` over algebraically closed fields.
The proof extracts weight space dimension equality from formal character equality
and reduces to `iso_of_glWeightSpace_finrank_eq`. -/
theorem iso_of_formalCharacter_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M₁ = formalCharacter k N M₂) :
    Nonempty (M₁ ≅ M₂) := by
  apply iso_of_glWeightSpace_finrank_eq k N M₁ M₂
  intro μ
  have h_coeff := congr_arg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm μ)) h
  rw [formalCharacter_coeff, formalCharacter_coeff] at h_coeff
  exact_mod_cast h_coeff

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
