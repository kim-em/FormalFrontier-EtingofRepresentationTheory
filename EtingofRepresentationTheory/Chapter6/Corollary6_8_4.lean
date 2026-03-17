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

## Current status

The proof is structured as follows:
1. **Reduction to simple root**: By `Theorem6_8_1`, there exist vertices
   `[v₁, ..., vₘ]` and a vertex `p` such that `sᵥₘ ∘ ⋯ ∘ sᵥ₁(α) = αₚ`.
2. **Base case** (α is a simple root): Construct the simple representation
   `k₍ₚ₎` (one-dimensional at `p`, zero elsewhere, all maps zero). This is
   indecomposable with dimension vector `αₚ`.
3. **Inductive step**: Apply inverse reflection functors `F⁻ᵥ₁ ∘ ⋯ ∘ F⁻ᵥₘ`
   to reconstruct a representation with dimension vector `α`.

### Blockers (sorry remaining)

The construction is sorry'd due to several infrastructure gaps:
- **Universe mismatch**: The `QuiverRepresentation` structure's `obj` field
  lives in a universe variable `u₃`, but concrete constructions (e.g.,
  `Fin m → k`) fix it to the universe of `k`. This prevents the simple
  representation construction from type-checking against the existential.
- **Quiver orientation**: Each reflection functor `F⁻ᵢ` changes the quiver
  via `reversedAtVertex`, producing a representation on a different quiver
  type. Chaining `m` reflections requires tracking `m` nested quiver
  orientations.
- **Q unconstrained**: The theorem statement has `{Q : Quiver (Fin n)}`
  without requiring compatibility between `Q` and `adj`. The proof needs
  `Q` to be an orientation of the Dynkin diagram.
- **Prop 6.6.7 source**: The source version of indecomposability preservation
  is sorry'd, needed for each step of the reflection functor chain.
- **Theorem 6.8.1 sorry'd**: The reflection sequence theorem is itself sorry'd.
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
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  -- By Theorem 6.8.1, iterated simple reflections reduce α to a simple root αₚ.
  -- This gives us the sequence of vertices [v₁, ..., vₘ] for the reflection
  -- functor chain.
  obtain ⟨vertices, p, hreduce⟩ := Etingof.Theorem6_8_1 hDynkin α hα.2 hα.1.1 hα.1.2
  -- The proof proceeds by induction on `vertices.length`:
  --
  -- BASE CASE (vertices = []): α = simpleRoot n p.
  --   Construct ρ with obj v = k^(δ_{v,p}) (1-dim at p, 0-dim elsewhere).
  --   All edge maps are zero. This is indecomposable because:
  --   - Nontrivial at p (k is nontrivial)
  --   - Any complementary sub-reps W₁, W₂ satisfy: at v ≠ p, both are ⊥
  --     (zero-dimensional space); at p, the space is 1-dimensional (simple),
  --     so one of W₁ p, W₂ p must be ⊥.
  --
  -- INDUCTIVE STEP (vertices = i :: rest):
  --   Let α' = sᵢ(α). By IH (on quiver reversedAtVertex Q i),
  --   ∃ ρ' indecomposable with dim vector α'.
  --   Apply F⁻ᵢ(ρ') to get ρ on Q with:
  --   - dim vector = sᵢ(α') = sᵢ(sᵢ(α)) = α (reflections are involutions)
  --     [uses Proposition 6.6.8]
  --   - indecomposable [uses Proposition 6.6.7]
  --
  -- SORRY: Construction blocked — see module docstring for details.
  sorry
