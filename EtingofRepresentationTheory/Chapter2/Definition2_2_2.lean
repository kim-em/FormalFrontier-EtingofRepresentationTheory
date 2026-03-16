import Mathlib.Algebra.Algebra.Basic

/-!
# Definition 2.2.2: Unit in an Associative Algebra

A **unit** in an associative algebra A is an element 1 ∈ A such that 1a = a1 = a.

## Mathlib correspondence

Mathlib algebras are unital by default — `Ring A` includes `One A` and the unit laws.
The unit element is `(1 : A)`.
-/

/-- The unit in an associative algebra, in the sense of Etingof Definition 2.2.2.
In Mathlib, this is built into `Ring A` via `One A` and `MulOneClass`. -/
example (A : Type*) [Ring A] : (1 : A) = 1 := rfl
