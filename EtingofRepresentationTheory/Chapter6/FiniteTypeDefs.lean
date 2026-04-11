import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs

/-!
# Finite Type Definitions for Quiver Representations

This file defines `AreIsomorphic` (isomorphism of quiver representations) and
`IsFiniteTypeQuiver` (finite representation type). These are extracted from
`Problem6_1_5_theorem.lean` to break a circular import dependency with
`InfiniteTypeConstructions.lean`.
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
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)],
    @Etingof.IsOrientationOf n Q adj →
      Set.Finite
        {d : Fin n → ℕ |
          ∃ (V : Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n)),
            V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))}
