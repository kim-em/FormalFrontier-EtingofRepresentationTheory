import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.

## Formalization note

The statement uses `IsDynkinDiagram` (Definition 6.1.4) for the combinatorial
condition. `IsFiniteTypeQuiver` is defined using quiver representation isomorphism
and indecomposability, quantified over all orientations and algebraically closed fields.
-/

section QuiverRepresentationIso

variable {k : Type*} [Field k] {n : ℕ} {Q : Quiver (Fin n)}

/-- Two quiver representations are isomorphic if there exist linear isomorphisms at
each vertex that intertwine the edge maps. -/
def Etingof.QuiverRepresentation.AreIsomorphic
    (V W : @Etingof.QuiverRepresentation k (Fin n) _ Q) : Prop :=
  ∃ (e : ∀ v, V.obj v ≃ₗ[k] W.obj v),
    ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.mapLinear f = W.mapLinear f ∘ₗ (e a).toLinearMap

end QuiverRepresentationIso

/-- A quiver on n vertices (with underlying graph given by adjacency matrix adj) is of
**finite type** if for every algebraically closed field k and every orientation Q of
the graph, the set of dimension vectors supporting an indecomposable representation
is finite.

This is equivalent to there being only finitely many isomorphism classes of
indecomposable representations, since for finite type quivers each dimension vector
supports at most one indecomposable (up to isomorphism).
Uses `QuiverRepresentation.IsIndecomposable` from Proposition 6.6.5. -/
def Etingof.IsFiniteTypeQuiver (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (Q : @Quiver.{0} (Fin n)), @Etingof.IsOrientationOf n Q adj →
      Set.Finite
        {d : Fin n → ℕ |
          ∃ (V : @Etingof.QuiverRepresentation k (Fin n) _ Q),
            V.IsIndecomposable ∧ ∀ v, V.obj v = (Fin (d v) → k)}

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
