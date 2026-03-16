import Mathlib

/-!
# Example 4.3: Irreducible Representations of Q₈

The quaternion group Q₈ = {±1, ±i, ±j, ±k} has 5 conjugacy classes:
{1}, {-1}, {±i}, {±j}, {±k}.

By the sum-of-squares formula d₁² + d₂² + d₃² + d₄² + d₅² = 8,
the dimensions are 1, 1, 1, 1, 2.

The four 1-dimensional representations are pulled back from Q₈/Z(Q₈) ≅ ℤ₂ × ℤ₂.
The 2-dimensional representation uses the Pauli matrices:
- ρ(i) = [[0, 1], [-1, 0]]
- ρ(j) = [[√(-1), 0], [0, -√(-1)]]
- ρ(k) = [[0, -√(-1)], [-√(-1), 0]]

## Mathlib correspondence

Mathlib has `Quaternion` and `QuaternionGroup`. The explicit representation
construction requires matrix algebra over ℂ.
-/

/-- Q₈ has exactly 5 conjugacy classes, hence 5 irreducible representations.
(Etingof Example 4.3) -/
theorem Etingof.Example4_3_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  sorry

/-- The sum-of-squares formula for Q₈: 1² + 1² + 1² + 1² + 2² = 8 = |Q₈|. -/
theorem Etingof.Example4_3_Q8_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (QuaternionGroup 2) := by
  sorry
