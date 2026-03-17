import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Theorem: Classification of Dynkin Diagrams

Γ is a Dynkin diagram if and only if it is one of the following graphs:
- Aₙ (n ≥ 1): a path with n vertices
- Dₙ (n ≥ 4): a path on vertices 0,...,n-2 with an extra edge from vertex n-3 to vertex n-1
- E₆, E₇, E₈: the three exceptional Dynkin diagrams (path with branch at vertex 2)

## Mathlib correspondence

Mathlib has `CoxeterMatrix` with Coxeter-Dynkin data for classical types, but the
classification theorem for positive-definite graphs is not present. The graph theory
and quadratic form infrastructure exists but the classification itself is absent.

## Formalization note

We define `DynkinType` as an inductive type enumerating the five families, together
with their adjacency matrices. The classification theorem states that `IsDynkinDiagram`
(positive-definite Cartan form) is equivalent to being graph-isomorphic to one of these
standard types.
-/

/-- The five families of Dynkin diagrams: A_n (n ≥ 1), D_n (n ≥ 4), E₆, E₇, E₈. -/
inductive Etingof.DynkinType where
  | A (n : ℕ) (hn : 1 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E6
  | E7
  | E8

/-- The number of vertices (rank) of a Dynkin diagram. -/
def Etingof.DynkinType.rank : Etingof.DynkinType → ℕ
  | .A n _ => n
  | .D n _ => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The adjacency matrix of a Dynkin diagram of the given type.

- **A_n**: path graph 0—1—2—⋯—(n-1)
- **D_n**: path 0—1—⋯—(n-2) with branch edge (n-3)—(n-1)
- **E₆**: path 0—1—2—3—4 with branch edge 2—5
- **E₇**: path 0—1—2—3—4—5 with branch edge 2—6
- **E₈**: path 0—1—2—3—4—5—6 with branch edge 2—7 -/
def Etingof.DynkinType.adj : (t : Etingof.DynkinType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A _n _ => fun i j =>
      if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  | .D n _ => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨
          (j.val + 1 = i.val ∧ i.val ≤ n - 2)) ∨
         ((i.val = n - 3 ∧ j.val = n - 1) ∨
          (j.val = n - 3 ∧ i.val = n - 1))
      then 1 else 0
  | .E6 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 4) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 4)) ∨
         ((i.val = 2 ∧ j.val = 5) ∨ (j.val = 2 ∧ i.val = 5))
      then 1 else 0
  | .E7 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 5) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 5)) ∨
         ((i.val = 2 ∧ j.val = 6) ∨ (j.val = 2 ∧ i.val = 6))
      then 1 else 0
  | .E8 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 6) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 6)) ∨
         ((i.val = 2 ∧ j.val = 7) ∨ (j.val = 2 ∧ i.val = 7))
      then 1 else 0

/-- Classification of Dynkin diagrams: a connected graph with positive-definite Cartan form
is a Dynkin diagram if and only if it is isomorphic (as a graph) to one of the standard
types A_n, D_n, E₆, E₇, or E₈.
(Etingof Theorem, Section 6.1) -/
theorem Etingof.Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Etingof.IsDynkinDiagram n adj ↔
    ∃ t : Etingof.DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := sorry
