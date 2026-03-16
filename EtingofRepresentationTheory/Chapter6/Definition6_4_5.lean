import Mathlib

/-!
# Definition 6.4.5: Simple Roots

The vectors αᵢ = (0, …, 1, …, 0) (with 1 in the i-th position) are called
**simple roots**. The αᵢ naturally form a basis of the lattice ℤⁿ.

## Mathlib correspondence

Mathlib's `RootPairing` has simple roots via indexing. The book's definition is
the standard basis vectors of ℤⁿ, which are `Pi.single i 1` in Mathlib.
-/

/-- The i-th simple root αᵢ is the standard basis vector eᵢ ∈ ℤⁿ.
(Etingof Definition 6.4.5) -/
def Etingof.simpleRoot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  Pi.single i 1
