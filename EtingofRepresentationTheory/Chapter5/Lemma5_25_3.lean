import Mathlib

/-!
# Lemma 5.25.3: Complementary Series Character Properties

For the virtual representation χ defined in the construction of
complementary series representations of GL₂(𝔽_q):
- ⟨χ, χ⟩ = 1
- χ(1) = q - 1 > 0

These properties establish that χ is the character of an actual
irreducible representation (of dimension q - 1).

## Mathlib correspondence

Uses `GaloisField` and character inner product theory.
-/

/-- The complementary series virtual character satisfies ⟨χ, χ⟩ = 1 and χ(1) > 0,
hence is an actual irreducible character. (Etingof Lemma 5.25.3) -/
theorem Etingof.Lemma5_25_3
    (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n) :
    let q := p ^ n
    -- ⟨χ, χ⟩ = 1 and χ(1) = q - 1 > 0
    (sorry : Prop) := by
  sorry
