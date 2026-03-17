import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Proposition6_6_6
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1

/-!
# Corollary 6.8.3: Dimension Vector Determines Indecomposable Representation

If V, V' are indecomposable representations of a Dynkin quiver Q with d(V) = d(V'),
then V ≅ V'.

The proof: let i be minimal such that d(V⁽ⁱ⁾) = αₚ. Then d(V'⁽ⁱ⁾) = αₚ too,
so V⁽ⁱ⁾ = V'⁽ⁱ⁾. Both sequences satisfy surjectivity conditions, so applying
inverse functors gives V = V'.

Together with Corollary 6.8.2, this shows there are finitely many indecomposable
representations (one for each positive root).

## Mathlib correspondence

Requires Theorem 6.8.1, reflection functor invertibility (Proposition 6.6.6),
and quiver representation isomorphism. Not in Mathlib.
-/

/-- Indecomposable representations of a Dynkin quiver are determined (up to isomorphism)
by their dimension vectors.

If two indecomposable representations ρ₁, ρ₂ of a quiver on Fin n (with Dynkin
adjacency matrix) have the same dimension at every vertex, then they are isomorphic
as quiver representations.
(Etingof Corollary 6.8.3) -/
theorem Etingof.Corollary6_8_3
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : ρ₁.IsIndecomposable)
    (h₂ : ρ₂.IsIndecomposable)
    (hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v)) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) :=
  sorry
