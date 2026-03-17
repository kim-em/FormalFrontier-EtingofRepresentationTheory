import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Corollary 5.12.4: Rational Representation Matrices

All irreducible representations of S_n can be given by matrices with
rational entries. This follows from the Young symmetrizer construction,
which uses only integer coefficients (signs of permutations and sums
over group elements).

## Mathlib correspondence

This is a consequence of the Specht module construction using Young symmetrizers.
-/

namespace Etingof

/-- All irreducible representations of S_n can be realized over ℚ.
(Etingof Corollary 5.12.4)

Every coefficient of the Young symmetrizer c_λ ∈ ℂ[S_n] is an integer: the row
symmetrizer a_λ = Σ_{g ∈ P_λ} g has coefficients in {0, 1}, the column
antisymmetrizer b_λ = Σ_{g ∈ Q_λ} sign(g)·g has coefficients in {-1, 0, 1},
and their product c_λ = a_λ · b_λ has integer coefficients.

Since c_λ ∈ ℤ[S_n] ⊂ ℚ[S_n] ⊂ ℂ[S_n], the Specht module V_λ = ℂ[S_n] · c_λ
admits a ℚ-form V_λ^ℚ = ℚ[S_n] · c_λ, showing that every irreducible representation
of S_n over ℂ can be defined over ℚ. -/
theorem Corollary5_12_4 (n : ℕ) (la : Nat.Partition n) :
    ∃ c_int : MonoidAlgebra ℤ (Equiv.Perm (Fin n)),
      c_int.mapRange (Int.cast) (by simp) = YoungSymmetrizer n la := by
  sorry

end Etingof
