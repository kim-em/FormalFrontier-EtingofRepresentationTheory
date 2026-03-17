import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_10
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Theorem 2.1.2: Gabriel's Theorem

The finite type property of a quiver Q does not depend on the orientation of edges.
The connected graphs that yield quivers of finite type are given by the Dynkin diagrams:
A_n, D_n, E_6, E_7, E_8.

## Mathlib correspondence

Gap — Gabriel's theorem is not in Mathlib. Only basic quiver infrastructure exists.

## Formalization note

Gabriel's theorem is a deep classification result connecting quiver representations to
Dynkin diagrams. It requires significant infrastructure (root systems, reflection functors,
positive definite quadratic forms on graphs). The statement is formalized; the proof is sorry'd.

We formalize the key supporting concepts:
- `QuiverRepresentationEquiv`: isomorphism of quiver representations
- `QuiverRepresentation.IsIndecomposable`: indecomposability via vertex-wise complements
- `HasFiniteRepresentationType`: finitely many iso classes of f.d. indecomposable reps
- `quiverUndirectedAdj`: the underlying undirected adjacency matrix of a quiver
-/

namespace Etingof

/-! ## Supporting definitions for Gabriel's theorem -/

/-- An equivalence (isomorphism) of quiver representations: a family of linear equivalences
at each vertex that commute with the arrow maps. -/
structure QuiverRepresentationEquiv (k : Type*) (Q : Type*) [CommSemiring k] [Quiver Q]
    (ρ₁ ρ₂ : QuiverRepresentation k Q) where
  /-- A linear equivalence at each vertex -/
  equivAt : ∀ v, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- The equivalences commute with the arrow maps -/
  commutes : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    equivAt w (ρ₁.mapLinear e x) = ρ₂.mapLinear e (equivAt v x)

/-- A quiver representation is nonzero if at least one vertex space is nontrivial. -/
def QuiverRepresentation.IsNonzero {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    (ρ : QuiverRepresentation k Q) : Prop :=
  ∃ v, Nontrivial (ρ.obj v)

/-- A quiver representation over a field is indecomposable if it is nonzero and for any
vertex-wise complementary pair of subrepresentations, one must be trivial everywhere.

A pair (W₁, W₂) of families of submodules is a complementary pair of subrepresentations
if: (1) W₁ v and W₂ v are complementary submodules of ρ.obj v for each vertex v, and
(2) both W₁ and W₂ are stable under the arrow maps. -/
def QuiverRepresentation.IsIndecomposable {k : Type*} {Q : Type*} [Field k] [Quiver Q]
    (ρ : QuiverRepresentation k Q) : Prop :=
  ρ.IsNonzero ∧
  ∀ (W₁ W₂ : ∀ v, Submodule k (ρ.obj v)),
    -- W₁ and W₂ are complementary at each vertex
    (∀ v, IsCompl (W₁ v) (W₂ v)) →
    -- W₁ is a subrepresentation (stable under arrow maps)
    (∀ {v w : Q} (e : v ⟶ w) (x : ρ.obj v), x ∈ W₁ v → ρ.mapLinear e x ∈ W₁ w) →
    -- W₂ is a subrepresentation
    (∀ {v w : Q} (e : v ⟶ w) (x : ρ.obj v), x ∈ W₂ v → ρ.mapLinear e x ∈ W₂ w) →
    -- Then one of them is trivial everywhere
    (∀ v, W₁ v = ⊥) ∨ (∀ v, W₂ v = ⊥)

/-- Quiver representation with all universes pinned to 0 (the natural setting for
finite-dimensional representations over a concrete field on a finite vertex set). -/
abbrev FinQuiverRep (k : Type) [CommSemiring k] (n : ℕ) [Quiver.{0} (Fin n)] :=
  QuiverRepresentation.{0, 0, 0, 0} k (Fin n)

/-- A quiver on `Fin n` over a field k has **finite representation type** if there exist
finitely many finite-dimensional indecomposable representations such that every
finite-dimensional indecomposable representation is isomorphic to one of them. -/
def HasFiniteRepresentationType (k : Type) [Field k] (n : ℕ)
    [Quiver.{0} (Fin n)] : Prop :=
  ∃ (m : ℕ) (reps : Fin m → FinQuiverRep k n),
    -- Each representative is finite-dimensional
    (∀ i, ∀ v, Module.Finite k ((reps i).obj v)) ∧
    -- Each representative is indecomposable
    (∀ i, (reps i).IsIndecomposable) ∧
    -- Every f.d. indecomposable rep is isomorphic to some representative
    (∀ (ρ : FinQuiverRep k n),
      (∀ v, Module.Finite k (ρ.obj v)) →
      ρ.IsIndecomposable →
      ∃ i, Nonempty (QuiverRepresentationEquiv k (Fin n) ρ (reps i)))

/-- The underlying undirected adjacency matrix of a quiver on `Fin n`.
For distinct vertices i ≠ j, the entry is 1 if there exists an arrow between them
in either direction, and 0 otherwise. Diagonal entries are 0. -/
noncomputable def quiverUndirectedAdj (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≠ j ∧ (Nonempty (i ⟶ j) ∨ Nonempty (j ⟶ i)) then 1 else 0

/-- The underlying undirected graph of a quiver on `Fin n` is connected if for any two
vertices there exists a path of undirected adjacency edges between them. -/
def QuiverUndirectedConnected (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] : Prop :=
  ∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      (quiverUndirectedAdj n)
        (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1

/-! ## Gabriel's Theorem -/

/-- **Gabriel's theorem**: A connected quiver on `Fin n` vertices has finite representation
type over an algebraically closed field if and only if its underlying undirected graph
is a Dynkin diagram (i.e., is connected, simple, and has positive definite Cartan matrix,
which forces it to be one of A_n, D_n, E_6, E_7, or E_8).

The forward direction: if Q has finite type, its underlying graph must be Dynkin.
The backward direction: if the underlying graph is Dynkin, Q has finite type regardless
of the orientation of edges.

(Etingof Theorem 2.1.2) -/
theorem Theorem_2_1_2 (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    (hconn : QuiverUndirectedConnected n) :
    HasFiniteRepresentationType k n ↔
      IsDynkinDiagram n (quiverUndirectedAdj n) := by
  sorry

end Etingof
