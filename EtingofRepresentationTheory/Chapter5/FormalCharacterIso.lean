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

/-! ### Schur polynomial injectivity

Distinct antitone partitions have distinct Schur polynomials. The proof uses:
1. `schurPoly_mul_vandermonde`: `S_λ · Δ = det(alt(λ + δ))`
2. `alternant_coeff_kronecker`: the Kronecker delta property of alternant det coefficients
3. Shifted exponents are strictly antitone for antitone partitions
-/

/-- If two strictly antitone exponent sequences give the same alternant determinant,
they are equal. Uses `alternant_coeff_kronecker` (the Kronecker delta property). -/
private theorem alternant_det_injective (N : ℕ) (e₁ e₂ : Fin N → ℕ)
    (he₁ : StrictAnti e₁) (he₂ : StrictAnti e₂)
    (h : (alternantMatrix N e₁).det = (alternantMatrix N e₂).det) :
    e₁ = e₂ := by
  -- coeff_{e₁}(det(alt(e₁))) = 1 by Kronecker delta with e = e' = e₁
  have hc₁ := alternant_coeff_kronecker he₁ he₁
  simp only [ite_true] at hc₁
  -- Since det(alt(e₁)) = det(alt(e₂)), coeff_{e₁}(det(alt(e₂))) = 1
  rw [h, alternant_coeff_kronecker he₂ he₁] at hc₁
  -- So e₂ = e₁ (the if-then-else equals 1 only when the condition holds)
  revert hc₁; split_ifs with heq
  · exact fun _ => heq.symm
  · exact fun h => absurd h one_ne_zero.symm

/-- The shifted exponents `λ + δ` are strictly antitone for antitone `λ`. -/
private theorem shiftedExps_strictAnti' (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    StrictAnti (shiftedExps N lam) := by
  intro i j hij; simp only [shiftedExps]
  exact Nat.add_lt_add_of_le_of_lt (hlam hij.le) (Nat.sub_lt_sub_left (by omega) hij)

/-- Shifted exponents determine the partition. -/
private theorem shiftedExps_injective (N : ℕ) :
    Function.Injective (shiftedExps N) := by
  intro lam₁ lam₂ h
  funext j; exact Nat.add_right_cancel (congr_fun h j)

/-- Schur polynomials are injective on antitone partitions: equal Schur polynomials
imply equal partitions. -/
theorem schurPoly_injective (N : ℕ) (lam₁ lam₂ : Fin N → ℕ)
    (hlam₁ : Antitone lam₁) (hlam₂ : Antitone lam₂)
    (h : schurPoly N lam₁ = schurPoly N lam₂) :
    lam₁ = lam₂ := by
  have h_alt : (alternantMatrix N (shiftedExps N lam₁)).det =
      (alternantMatrix N (shiftedExps N lam₂)).det := by
    have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
    apply mul_right_cancel₀ hΔ
    rw [← schurPoly_mul_vandermonde, ← schurPoly_mul_vandermonde, h]
  exact shiftedExps_injective N
    (alternant_det_injective N _ _ (shiftedExps_strictAnti' N lam₁ hlam₁)
      (shiftedExps_strictAnti' N lam₂ hlam₂) h_alt)

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

/-- A `GL_N(k)`-representation whose formal character equals a Schur polynomial
`S_λ` and whose dimension matches the Schur module is isomorphic to `L_λ`.

The dimension hypothesis `h_dim` is necessary: without it, one could take
`M = L_λ ⊕ det⁻¹`, which has `formalCharacter M = schurPoly N lam` (since
`det⁻¹` has no `ℕ`-valued weight spaces and is invisible to `formalCharacter`),
yet `M ≇ L_λ` due to the dimension mismatch. The hypothesis ensures `M` is
"polynomial" — its `ℕ`-valued weight spaces account for all of `M`.

The proof requires GL_N-equivariant complete reducibility: every polynomial
`GL_N`-representation decomposes into a direct sum of Schur modules. Combined
with `Theorem5_22_1` (Weyl character formula) and `schurPoly_injective`,
this forces `M ≅ L_λ`.

The downstream use is in `schurModule_shift_iso_detTwist` (Proposition 5.22.2),
where both representations are polynomial and have character equal to
`schurPoly N (λ + 1^N)`. -/
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)) :
    Nonempty (M ≅ SchurModule k N lam) := by
  -- Proof outline:
  -- 1. From h + Theorem5_22_1: weight space dims match at every ℕ-valued weight
  -- 2. From h_dim: ℕ-valued weight spaces span M (M is polynomial)
  -- 3. By GL_N-equivariant complete reducibility (Schur-Weyl): M ≅ ⊕ nᵢ · L_μᵢ
  -- 4. Character additivity + schurPoly_injective: nλ = 1, all others = 0
  -- 5. Therefore M ≅ L_λ
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
