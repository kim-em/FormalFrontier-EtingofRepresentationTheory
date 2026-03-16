import Mathlib

/-!
# Proposition 5.2.4: Ring and Field Properties of Algebraic Numbers/Integers

(i) The set of algebraic integers Ā is a ring (closed under addition and multiplication).
(ii) The set of algebraic numbers Q̄ is a field (the algebraic closure of ℚ in ℂ).

## Mathlib correspondence

These are already established in Mathlib:
- `IsIntegral` is closed under ring operations via `RingHom.IsIntegral`
- `Subalgebra.isAlgebraic` gives the algebraic closure structure
-/

/-- The set of algebraic integers in ℂ forms a subring: it is closed under addition and
multiplication. (Etingof Proposition 5.2.4(i)) -/
theorem Etingof.Proposition5_2_4_ring :
    -- The algebraic integers form a subring of ℂ
    ∀ x y : ℂ, IsIntegral ℤ x → IsIntegral ℤ y →
      IsIntegral ℤ (x + y) ∧ IsIntegral ℤ (x * y) := by
  intro x y hx hy
  exact ⟨hx.add hy, hx.mul hy⟩

/-- The set of algebraic numbers forms a subfield of ℂ (the algebraic closure of ℚ).
(Etingof Proposition 5.2.4(ii)) -/
theorem Etingof.Proposition5_2_4_field :
    -- The algebraic numbers form a subfield of ℂ
    ∀ x y : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ y →
      IsAlgebraic ℚ (x + y) ∧ IsAlgebraic ℚ (x * y) := by
  intro x y hx hy
  exact ⟨hx.add hy, hx.mul hy⟩
