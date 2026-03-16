import Mathlib

/-!
# Definition 6.4.3: Root

A **root** with respect to a certain positive inner product is a shortest (with respect
to this inner product) nonzero vector in ℤⁿ.

For the inner product B (from the Cartan matrix), a root is a nonzero vector x ∈ ℤⁿ
such that B(x, x) = 2.

## Mathlib correspondence

Mathlib has `RootPairing` which formalizes root systems abstractly. The book's
definition of roots via the quadratic form is more elementary. Since B(x,x) is
always even (Lemma 6.4.2) and positive definite, the minimum nonzero value is 2.
-/

/-- A root of a Dynkin diagram is a nonzero vector x ∈ ℤⁿ such that B(x, x) = 2,
where B is the Cartan inner product. Equivalently, xᵀ(2·Id - adj)x = 2.
(Etingof Definition 6.4.3) -/
def Etingof.IsRoot (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  x ≠ 0 ∧ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2
