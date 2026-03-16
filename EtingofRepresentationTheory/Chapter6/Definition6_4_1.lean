import Mathlib

/-!
# Definition 6.4.1: Cartan Matrix and Inner Product

The **Cartan matrix** of a graph Γ with adjacency matrix R is defined as A = 2·Id - R.

On the lattice ℤⁿ (or the space ℝⁿ) we then define an inner product
  B(x, y) = xᵀ A y
corresponding to the graph Γ.

## Mathlib correspondence

Mathlib has `CoxeterMatrix` from which Cartan matrices can be derived. The specific
construction from an adjacency matrix needs custom scaffolding. The bilinear form
infrastructure (`BilinForm`, `Matrix.toBilin`) is available.
-/

/-- The Cartan matrix of a graph Γ with n vertices is A = 2·Id - R, where R is the
adjacency matrix. The associated bilinear form is B(x, y) = xᵀ A y.
(Etingof Definition 6.4.1) -/
def Etingof.cartanMatrix (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj
