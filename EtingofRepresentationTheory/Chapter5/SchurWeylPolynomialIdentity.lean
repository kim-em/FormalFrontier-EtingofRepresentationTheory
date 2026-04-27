import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Schur-Weyl Polynomial Identity

The closed-form expansion of `(∑ Xᵢ)^n` against the Schur basis,
specialising the Frobenius character formula `Proposition5_21_1_univ`
to the trivial cycle type `(1, 1, …, 1)`.

## Main results

* `trivialCycleType n` — the partition of `n` consisting of `n` parts of size `1`
  (the cycle type of the identity permutation in `Sₙ`).
* `psumPart_trivialCycleType` — `psumPart (Fin N) ℚ (trivialCycleType n) = (∑ Xᵢ)^n`.
* `sum_X_pow_eq_sum_charValue_smul_schurPoly` — the Schur-Weyl polynomial identity:
  `(∑ Xᵢ)^n = ∑_{λ} charValue N λ (trivialCycleType n) • schurPoly N λ.parts`,
  where the sum runs over `λ : BoundedPartition N n`.

The coefficient `charValue N λ (trivialCycleType n)` equals the dimension of the
Specht module `Sₙ`-irrep `Sλ` (Frobenius character at the identity), bridging the
polynomial identity to a Specht-multiplicity statement.
-/

open MvPolynomial Finset

noncomputable section

namespace Etingof

/-- The trivial cycle-type partition: `n` parts each equal to `1`.
This is the cycle type of the identity permutation in `Sₙ`. -/
def trivialCycleType (n : ℕ) : Nat.Partition n where
  parts := Multiset.replicate n 1
  parts_pos hi := by
    rw [Multiset.mem_replicate] at hi; omega
  parts_sum := by
    rw [Multiset.sum_replicate]; simp

/-- The power-sum partition for the trivial cycle type collapses to `(∑ Xᵢ)^n`. -/
theorem psumPart_trivialCycleType (N n : ℕ) :
    MvPolynomial.psumPart (Fin N) ℚ (trivialCycleType n) =
      (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n := by
  unfold MvPolynomial.psumPart
  change (Multiset.map (MvPolynomial.psum (Fin N) ℚ) (Multiset.replicate n 1)).prod = _
  rw [Multiset.map_replicate, Multiset.prod_replicate, MvPolynomial.psum_one]

/-- **Schur-Weyl polynomial identity.**

The `n`-th power of the standard character `∑ᵢ Xᵢ` decomposes as a sum
of Schur polynomials weighted by character values at the identity:

`(∑ᵢ Xᵢ)ⁿ = ∑_{λ ∈ BoundedPartition N n} χ_λ(1) • s_λ(X)`,

where `χ_λ(1) = charValue N λ (trivialCycleType n)` is the Frobenius character
value at the identity (equivalently: the dimension of the Specht module `Sλ`).

This is the polynomial-side ingredient of Schur-Weyl duality (Etingof Theorem
5.18.4): combined with the formal-character identity for `glTensorRep`
(`formalCharacter_glTensorRep_eq_pow`), it yields the multiplicity formula for the
GL_N-irreducible summands of `V^⊗n`. -/
theorem sum_X_pow_eq_sum_charValue_smul_schurPoly (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ lam : BoundedPartition N n,
        charValue N lam (trivialCycleType n) • schurPoly N lam.parts := by
  rw [← psumPart_trivialCycleType N n]
  exact Proposition5_21_1_univ N (trivialCycleType n)

/-! ## Bridge to Specht module dimensions

The character value `charValue N λ (trivialCycleType n)` evaluates the Frobenius
character at the identity, hence equals the dimension of the Specht module `Sλ`.
This bridges the polynomial identity above to a multiplicity statement involving
explicit Specht-module dimensions, as needed by the Schur-Weyl final assembly. -/

/-- The cycle type of the identity permutation in `Sₙ` is the trivial cycle type
(`n` parts of size `1`). -/
theorem fullCycleTypePartition_one (n : ℕ) :
    fullCycleTypePartition (1 : Equiv.Perm (Fin n)) = trivialCycleType n := by
  apply Nat.Partition.ext
  change fullCycleType n 1 = Multiset.replicate n 1
  unfold fullCycleType
  rw [Equiv.Perm.cycleType_one, Equiv.Perm.support_one,
    Finset.card_empty, Nat.sub_zero, zero_add]

/-- The Frobenius character at the identity equals the dimension of the Specht module. -/
theorem spechtModuleCharacter_one (n : ℕ) (la : Nat.Partition n) :
    spechtModuleCharacter n la 1 = (Module.finrank ℂ (SpechtModule n la) : ℂ) := by
  unfold spechtModuleCharacter
  rw [show (spechtModuleAction n la 1) = (1 : Module.End ℂ ↥(SpechtModule n la)) from
        map_one (spechtModuleRep n la),
      LinearMap.trace_one]

/-- **Specht-dimension bridge.** The character value at the trivial cycle type
equals the dimension of the corresponding Specht module (cast to `ℂ`):

`(charValue N λ (trivialCycleType n) : ℂ) = dim_ℂ (Sλ)`.

This is the polynomial-identity counterpart of "trace at identity = dimension". -/
theorem charValue_trivialCycleType_eq_spechtFinrank
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    (charValue N lam (trivialCycleType n) : ℂ) =
      (Module.finrank ℂ
        (SpechtModule n (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℂ) := by
  rw [← fullCycleTypePartition_one n,
      charValue_eq_spechtModuleCharacter N n lam 1,
      spechtModuleCharacter_one]

/-- **Specht-dimension bridge over `ℚ`.** Stronger form of
`charValue_trivialCycleType_eq_spechtFinrank`: the rational character value at
the trivial cycle type already equals the natural-number dimension of the
Specht module (cast to `ℚ`). Obtained from the `ℂ`-form by injectivity of
`Rat.cast : ℚ → ℂ`. -/
theorem charValue_trivialCycleType_eq_spechtFinrank_rat
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      (Module.finrank ℂ
        (SpechtModule n (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) := by
  apply (Rat.cast_injective (α := ℂ))
  rw [Rat.cast_natCast]
  exact charValue_trivialCycleType_eq_spechtFinrank N lam

/-- **Schur-Weyl polynomial identity in dimension form.**

The `n`-th power of the standard character `∑ᵢ Xᵢ` decomposes as a sum of
Schur polynomials weighted by Specht-module dimensions:

`(∑ᵢ Xᵢ)ⁿ = ∑_{λ ∈ BoundedPartition N n} dim_ℂ(Sλ) • s_λ(X)`.

This is the dimension-form combination of `sum_X_pow_eq_sum_charValue_smul_schurPoly`
and `charValue_trivialCycleType_eq_spechtFinrank_rat`, ready for direct use by
the Schur-Weyl L_i final assembly. -/
theorem sum_X_pow_eq_sum_finrank_smul_schurPoly (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ lam : BoundedPartition N n,
        (Module.finrank ℂ (SpechtModule n
          (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) •
        schurPoly N lam.parts := by
  rw [sum_X_pow_eq_sum_charValue_smul_schurPoly]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [charValue_trivialCycleType_eq_spechtFinrank_rat]

end Etingof
