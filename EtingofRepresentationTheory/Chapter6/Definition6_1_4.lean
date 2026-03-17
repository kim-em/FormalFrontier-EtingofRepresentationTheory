import Mathlib

/-!
# Definition 6.1.4: Dynkin Diagram

Γ is said to be a **Dynkin diagram** if the quadratic form on ℝⁿ with matrix A
(the adjacency-based matrix 2·Id - R) is positive definite.

## Mathlib correspondence

Mathlib has `CoxeterMatrix` and `CoxeterSystem` for Coxeter-Dynkin data. The specific
classification of positive-definite graphs as Dynkin diagrams would need custom work.
The quadratic form infrastructure (`QuadraticForm`, `QuadraticMap.PosDef`) is available.

## Formalization note

A Dynkin diagram is a finite connected graph whose associated quadratic form is positive
definite. Mathlib's `SimpleGraph` and `QuadraticMap.PosDef` provide the building blocks,
but the full definition connecting graphs to their quadratic forms needs custom scaffolding.
-/

/-- A Dynkin diagram is a finite connected simple graph whose associated quadratic form
(with Cartan matrix A = 2·Id - adjacency matrix) is positive definite.
(Etingof Definition 6.1.4) -/
def Etingof.IsDynkinDiagram (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  -- Symmetric 0-1 adjacency matrix with no loops (simple graph)
  adj.IsSymm ∧
  (∀ i, adj i i = 0) ∧
  (∀ i j, adj i j = 0 ∨ adj i j = 1) ∧
  -- Connected: any two distinct vertices are linked by a path of adjacency edges
  (∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) ∧
  -- Positive-definite Cartan matrix: xᵀ(2·Id - adj)x > 0 for all nonzero x ∈ ℤⁿ
  (∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x))
