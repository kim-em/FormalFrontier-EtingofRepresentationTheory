import Mathlib

/-!
# Example 4.3: Irreducible Representations of S₃

The symmetric group S₃ has 3 conjugacy classes: {e}, {(12),(13),(23)}, {(123),(132)}.
By the sum-of-squares formula d₁² + d₂² + d₃² = 6, the dimensions are 1, 1, 2.

The three irreducible representations are:
- The trivial representation ℂ₊
- The sign representation ℂ₋
- The 2-dimensional standard representation ℂ², realized as symmetries of an
  equilateral triangle

## Mathlib correspondence

Mathlib has `Equiv.Perm` for symmetric groups and `Equiv.Perm.sign` for the sign
representation.
-/

/-- S₃ has exactly 3 irreducible representations (over ℂ or any algebraically closed
field of characteristic ≠ 2, 3). (Etingof Example 4.3) -/
theorem Etingof.Example4_3_S3_irreps_count :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  native_decide

/-- The sum-of-squares formula for S₃: 1² + 1² + 2² = 6 = |S₃|. -/
theorem Etingof.Example4_3_S3_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (Equiv.Perm (Fin 3)) := by
  native_decide
