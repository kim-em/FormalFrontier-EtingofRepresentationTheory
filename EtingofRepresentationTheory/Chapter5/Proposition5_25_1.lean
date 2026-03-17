import Mathlib

/-!
# Proposition 5.25.1: Commutator Subgroup of GL₂(𝔽_q)

[G, G] = SL₂(𝔽_q) where G = GL₂(𝔽_q).

The proof shows det(xyx⁻¹y⁻¹) = 1 so [G,G] ⊆ SL₂, then exhibits the
generators of SL₂ as explicit commutators.

## Mathlib correspondence

Uses `GaloisField`, `Matrix.SpecialLinearGroup`, `Matrix.GeneralLinearGroup`.
-/

/-- The commutator subgroup of GL₂(𝔽_q) equals SL₂(𝔽_q).
(Etingof Proposition 5.25.1) -/
theorem Etingof.Proposition5_25_1
    (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n) :
    commutator (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)) =
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField p n)).range := by
  sorry
