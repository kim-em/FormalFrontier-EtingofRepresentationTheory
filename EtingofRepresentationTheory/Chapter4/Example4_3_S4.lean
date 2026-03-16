import Mathlib

/-!
# Example 4.3: Irreducible Representations of S₄

S₄ has order 24 with 5 conjugacy classes:
{e}, {(12),...}, {(123),...}, {(1234),...}, {(12)(34),...}

By the sum-of-squares formula: d₁² + d₂² + d₃² + d₄² + d₅² = 24,
the unique solution is dimensions 1, 1, 2, 3, 3.

The five irreducible representations:
- Trivial representation ℂ₊
- Sign representation ℂ₋
- 2-dimensional: pulled back from S₃ ≅ S₄/V₄ (V₄ = Klein four group)
- 3-dimensional ℂ₊³: rotation group of cube permuting interior diagonals
- 3-dimensional ℂ₋³ = sign ⊗ ℂ₊³ (equivalently, functions on {1,2,3,4} with zero sum)

## Mathlib correspondence

Uses `Equiv.Perm (Fin 4)` for S₄.
-/

/-- S₄ has exactly 5 conjugacy classes. (Etingof Example 4.3) -/
theorem Etingof.Example4_3_S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  native_decide

/-- The sum-of-squares formula for S₄: 1² + 1² + 2² + 3² + 3² = 24 = |S₄|. -/
theorem Etingof.Example4_3_S4_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2 + 3 ^ 2 = Fintype.card (Equiv.Perm (Fin 4)) := by
  decide
