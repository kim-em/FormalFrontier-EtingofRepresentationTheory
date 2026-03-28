import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Formal character determines isomorphism class

For polynomial representations of `GL_N(k)` over algebraically closed fields,
the formal character determines the isomorphism class. This is a consequence of
the complete reducibility of polynomial representations (Schur-Weyl duality).

This file provides the sorry'd general theorem and uses it together with the
weight space shift computation for the determinant twist.
-/

open CategoryTheory MvPolynomial

noncomputable section

namespace Etingof

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- Two `GL_N(k)`-representations with the same formal character are isomorphic.

This holds for polynomial representations of `GL_N` over algebraically closed fields.
The proof requires either:
- Complete reducibility (Schur-Weyl duality / Maschke for reductive groups)
- Or a direct argument via highest weight theory

Both approaches need substantial infrastructure not yet available. -/
theorem iso_of_formalCharacter_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M₁ = formalCharacter k N M₂) :
    Nonempty (M₁ ≅ M₂) := by
  sorry

/-- If the weight space dimensions of `M₁` at weight `ν + (1,…,1)` equal those of `M₂` at `ν`
(for all `ν`), then the formal character of `M₁` is `(∏ Xᵢ) · char(M₂)`.

This requires additionally showing that weight spaces of `M₁` at weights with some zero
component are trivial. For the determinant-twisted representation, this follows from the
polynomial nature of the action: the map `t ↦ ρ(diag(…,t,…))(v)` is polynomial in `t`,
so the eigenvalue `t⁻¹` (from the zero-weight condition) cannot occur. -/
theorem formalCharacter_shift_of_weightSpace_finrank (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_shift : ∀ ν : Fin N → ℕ,
      Module.finrank k (glWeightSpace k N M₁ (fun i => ν i + 1)) =
        Module.finrank k (glWeightSpace k N M₂ ν)) :
    formalCharacter k N M₁ =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N M₂ := by
  sorry

end Etingof
