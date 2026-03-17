import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.
The definition of "finite type" for quivers requires quiver representation theory
infrastructure (indecomposable representations, isomorphism classes) not yet
available in Mathlib.

## Formalization note

The statement uses `IsDynkinDiagram` (Definition 6.1.4) for the combinatorial
condition. The representation-theoretic side (`IsFiniteTypeQuiver`) is defined
as a sorry'd predicate pending development of quiver representation infrastructure.
The hypotheses unpack the connected simple graph conditions.
-/

/-- A quiver on n vertices (with underlying graph given by adjacency matrix adj) is of
finite type if for every algebraically closed field k, the set of isomorphism classes
of indecomposable k-representations of the path algebra kQ is finite.

This is a placeholder definition — the full development requires quiver representation
theory infrastructure not yet present in this project or in Mathlib. -/
def Etingof.IsFiniteTypeQuiver (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop := sorry

/-- Gabriel's theorem: a connected quiver (given by its symmetric adjacency matrix)
is of finite type (finitely many indecomposable representations up to isomorphism)
if and only if its underlying unoriented graph is a Dynkin diagram.
(Etingof Problem 6.1.5 / Theorem 6.5.2) -/
theorem Etingof.Theorem_6_1_5 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    Etingof.IsFiniteTypeQuiver n adj ↔ Etingof.IsDynkinDiagram n adj := sorry
