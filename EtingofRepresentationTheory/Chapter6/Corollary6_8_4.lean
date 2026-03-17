import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1

/-!
# Corollary 6.8.4: Every Positive Root Is Realized

For every positive root α of a Dynkin quiver Q, there exists an indecomposable
representation V with d(V) = α.

The proof constructs V explicitly: apply the sequence s_n, s_{n-1}s_n, … to α
until reaching a simple root αᵢ. Then build V = F⁻_n F⁻_{n-1} ⋯ F⁻_q k_{(i)}
where k_{(i)} is the simple representation at vertex i on the appropriately
reoriented quiver.

This completes Gabriel's theorem: indecomposable representations of Dynkin quivers
are in bijection with positive roots.

## Mathlib correspondence

Requires full reflection functor machinery and the construction of simple
representations. Not in Mathlib.

## Formalization note

The statement says: for any positive root α (w.r.t. the Cartan form of a Dynkin
diagram), there is an indecomposable quiver representation whose dimension
vector equals α. The proof uses Theorem 6.8.1 (iterated reflections reach a
simple root) and the reflection functors (Definitions 6.6.3-6.6.4) to
reconstruct the representation from the simple one.
-/

/-- Every positive root of a Dynkin quiver is the dimension vector of some
indecomposable representation.

Given a Dynkin diagram with adjacency matrix `adj` and a positive root α
(i.e., α ≠ 0, B(α, α) = 2, all coordinates nonneg), there exists an
indecomposable quiver representation ρ over any field k such that
`finrank k (ρ.obj v) = α v` at each vertex v.
(Etingof Corollary 6.8.4) -/
theorem Etingof.Corollary6_8_4
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (α : Fin n → ℤ) (hα : Etingof.IsPositiveRoot n adj α)
    (k : Type*) [Field k]
    {Q : Quiver (Fin n)} :
    ∃ (ρ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) :=
  sorry
