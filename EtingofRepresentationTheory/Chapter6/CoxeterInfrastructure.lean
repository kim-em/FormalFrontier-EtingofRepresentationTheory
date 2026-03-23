import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4

/-!
# Coxeter Element Infrastructure: Admissible Orderings

This file provides the infrastructure for iterating reflection functors along
an admissible ordering of quiver vertices, which is the key ingredient for:
- Proving B(d(V), d(V)) = 2 for indecomposable V (Corollary 6.8.2)
- The cons case of `reflectionFunctors_reduce_and_recover` (Corollary 6.8.3)

## Main definitions
- `Etingof.iteratedReversedAtVertices`: Iterated quiver reversal
- `Etingof.IsAdmissibleOrdering`: An ordering of vertices where each is a sink after
  reversing at all previous vertices
- `Etingof.exists_sink_of_dynkin_orientation`: Every Dynkin quiver orientation has a sink
- `Etingof.admissibleOrdering_exists`: Every Dynkin quiver orientation has an admissible
  ordering

## Key insight
For a Dynkin diagram, the Cartan matrix is positive definite, which implies the quiver
is acyclic (a cycle would give B(d,d) = 0). Acyclicity guarantees the existence of sinks,
which enables inductive construction of admissible orderings.

## References
- Etingof, §6.7-6.8: Coxeter element and Gabriel's theorem
-/

open scoped Matrix

namespace Etingof

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

/-! ## Sink existence for Dynkin quiver orientations -/

/-- If there is an arrow a → b in Q, then adj a b = 1.
Contrapositive of the non-edge condition in `IsOrientationOf`. -/
private lemma adj_eq_one_of_arrow
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    {a b : Fin n} (e : @Quiver.Hom (Fin n) Q a b) :
    adj a b = 1 := by
  rcases hDynkin.2.2.1 a b with h0 | h1
  · exfalso; exact (hOrient.1 a b (by omega)).false e
  · exact h1

/-- Every orientation of a Dynkin diagram has at least one sink vertex.

Proof by contradiction: if no sink exists, every vertex has an outgoing edge.
Iterating gives a walk v₀ → v₁ → ... → vₙ of length n+1, which by pigeonhole
must revisit a vertex. This gives a directed cycle, whose characteristic vector
d satisfies B(d,d) ≤ 0, contradicting positive definiteness of the Cartan matrix.

This is the key lemma enabling the construction of admissible orderings. -/
theorem exists_sink_of_dynkin_orientation
    (hDynkin : IsDynkinDiagram n adj) (hn : 0 < n)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj) :
    ∃ i : Fin n, IsSink (Fin n) i := by
  -- Suppose no sink exists
  by_contra h
  push_neg at h
  -- Then every vertex has an outgoing edge
  have hout : ∀ v : Fin n, ∃ w : Fin n, Nonempty (v ⟶ w) := by
    intro v
    have hv := h v
    unfold IsSink at hv
    push_neg at hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw⟩
  -- Pick a successor function
  choose next hnext using hout
  -- KEY ARGUMENT: injection from Fin n ⊕ Fin n into adj-1 pairs
  -- For each v, we have v → next(v), so adj(v, next v) = 1 and adj(next v, v) = 1.
  -- The pairs (v, next v) and (next v, v) give 2n pairs with adj = 1.
  -- No overlap: if (v₁, next v₁) = (next v₂, v₂) then v₁ → v₂ and v₂ → v₁, contradicting orientation.
  -- So Σ adj ≥ 2n, but positive definiteness gives Σ adj < 2n. Contradiction.
  --
  -- Step 1: adj(v, next v) = 1 for all v
  have hadj_out : ∀ v, adj v (next v) = 1 := by
    intro v; exact adj_eq_one_of_arrow hDynkin hOrient (hnext v).some
  -- Step 2: adj(next v, v) = 1 for all v (by symmetry)
  have hadj_in : ∀ v, adj (next v) v = 1 := by
    intro v
    have h1 := hadj_out v
    have hsymm := hDynkin.1
    have : adj (next v) v = adj v (next v) := by
      have := congr_fun (congr_fun hsymm v) (next v)
      simp [Matrix.transpose_apply] at this; exact this
    rw [this]; exact h1
  -- Step 3: No pair (v, next v) equals (next w, w) — would give both directions
  have hno_overlap : ∀ v w : Fin n, (v, next v) ≠ (next w, w) := by
    intro v w heq
    have h1 : v = next w := congr_arg Prod.fst heq
    have h2 : next v = w := congr_arg Prod.snd heq
    -- v → next v = w and w → next w = v, so both v → w and w → v
    have harr1 := hnext v  -- v → next v
    have harr2 := hnext w  -- w → next w
    -- After substitution: v → w and w → v
    apply hOrient.2.2 v w
    · -- v ⟶ w: harr1 gives v ⟶ next v, and h2 : next v = w
      rw [show w = next v from h2.symm]; exact harr1
    · -- w ⟶ v: harr2 gives w ⟶ next w, and h1 : v = next w
      rw [show v = next w from h1]; exact harr2
  -- Step 4: The double sum Σ_i Σ_j adj(i,j) satisfies incompatible bounds.
  -- Upper bound: B(1,1) > 0 means 2n - Σ adj > 0, so Σ adj < 2n.
  -- Lower bound: the 2n distinct pairs {(v, next v)} ∪ {(next v, v)} each with adj = 1
  --   force Σ adj ≥ 2n.
  -- We show: for each v, adj(v, next v) ≤ Σ_j adj(v, j) (single summand of a sum of nonneg terms)
  -- and similarly for adj(next v, v). The non-overlap condition ensures these contribute distinctly.
  --
  -- For now, the counting argument (injection into the double sum) is sorry'd.
  -- The proof structure above (Steps 1-3) is complete and verified.
  sorry

/-- Reversing at a sink makes that vertex a source in the reversed quiver. -/
theorem reversedAtVertex_sink_becomes_source
    {Q : Quiver (Fin n)} (p : Fin n) (hp : @IsSink (Fin n) Q p) :
    @IsSource (Fin n) (@reversedAtVertex (Fin n) _ Q p) p := by
  intro j
  -- In the reversed quiver, an arrow j ⟶ p has type ReversedAtVertexHom(j, p)
  constructor
  intro (e : ReversedAtVertexHom (Fin n) p j p)
  by_cases hj : j = p
  · -- Self-loop: with j = p, the reversed arrow type equals (p ⟶ p)
    have heq : ReversedAtVertexHom (Fin n) p j p = (@Quiver.Hom (Fin n) Q j p) :=
      ReversedAtVertexHom_eq_eq hj rfl
    have e' : @Quiver.Hom (Fin n) Q j p := cast heq e
    exact (hp p).false (hj ▸ e')
  · -- j ≠ p: ReversedAtVertexHom(j, p) = (p ⟶ j) in original Q
    have heq : ReversedAtVertexHom (Fin n) p j p = (@Quiver.Hom (Fin n) Q p j) :=
      ReversedAtVertexHom_ne_eq hj rfl
    exact (hp j).false (cast heq e)

/-! ## Admissible orderings -/

/-- The quiver obtained by iteratively reversing at a sequence of vertices.
`iteratedReversedAtVertices Q [v₁, v₂, ..., vₖ]` reverses first at v₁,
then at v₂ in the new quiver, etc. -/
noncomputable def iteratedReversedAtVertices
    {V : Type*} [DecidableEq V] : (Q : Quiver V) → List V → Quiver V
  | Q, [] => Q
  | Q, v :: vs => iteratedReversedAtVertices (@reversedAtVertex V _ Q v) vs

/-- Reversing at vertices preserves the orientation property, proven for
arbitrary lists (not just permutations).
Each reversal preserves `IsOrientationOf` by `reversedAtVertex_isOrientationOf`. -/
theorem iteratedReversed_isOrientationOf
    (hDynkin : IsDynkinDiagram n adj)
    (Q : Quiver (Fin n)) (hOrient : IsOrientationOf Q adj)
    (vs : List (Fin n)) :
    @IsOrientationOf n (iteratedReversedAtVertices Q vs) adj := by
  induction vs generalizing Q with
  | nil => exact hOrient
  | cons v vs ih =>
    exact ih _ (reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hOrient v)

/-- An admissible ordering of a quiver is a list of ALL vertices such that
each vertex is a sink in the quiver obtained by reversing at all previous
vertices. This guarantees that we can apply F⁺ at each vertex in sequence.

For a quiver on Fin n, the ordering must be a permutation of all vertices. -/
structure IsAdmissibleOrdering (Q : Quiver (Fin n))
    (ordering : List (Fin n)) : Prop where
  /-- The ordering contains every vertex exactly once -/
  perm : ordering.Perm (List.finRange n)
  /-- Each vertex is a sink after reversing at all previous vertices -/
  isSink : ∀ k (hk : k < ordering.length),
    @IsSink (Fin n)
      (iteratedReversedAtVertices Q (ordering.take k))
      (ordering.get ⟨k, hk⟩)

/-- Every Dynkin quiver orientation admits an admissible ordering.

The proof constructs the ordering inductively: at each step, find a sink
(which exists by `exists_sink_of_dynkin_orientation`), add it to the ordering,
and reverse at it. The reversed quiver is still an orientation of the same
Dynkin diagram (by `reversedAtVertex_isOrientationOf`), so the process continues.

Note: the existence of admissible orderings is a standard result for finite
acyclic directed graphs. The Dynkin hypothesis is used only to guarantee
acyclicity (via positive definiteness of the Cartan matrix). -/
theorem admissibleOrdering_exists
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj) :
    ∃ ordering : List (Fin n), IsAdmissibleOrdering Q ordering := by
  sorry

/-! ## Dimension vector tracking through admissible ordering

The key connection: applying one full round of reflection functors along an
admissible ordering transforms the dimension vector by the Coxeter element.

Specifically, if σ = (σ₁, ..., σₙ) is an admissible ordering, then:
  d(F⁺_{σ₁} ... F⁺_{σₙ} V) = s_{σ₁} ... s_{σₙ} d(V) = c · d(V)

where c = s_{σ₁} ... s_{σₙ} is the Coxeter element.

Combined with Lemma 6.7.2 (Coxeter action eventually produces negative entries)
and Proposition 6.6.5 (non-surjective at sink → simple representation), this
gives the representation-level reduction:

For V indecomposable, after finitely many Coxeter rounds, V reduces to a
simple representation α_p. Then B(d(V), d(V)) = B(α_p, α_p) = 2.

This is the content of the book's proof of Theorem 6.8.1 + Corollary 6.8.2. -/

/-- The dimension vector of an indecomposable representation of a Dynkin quiver
satisfies B(d, d) = 2 (not just ≤ 2).

This is proved by the representation-level Coxeter iteration argument:
1. Choose admissible ordering (by `admissibleOrdering_exists`)
2. At each step, either ρ is simple (done) or F⁺(ρ) is indecomposable
3. Dimension vector tracks as Coxeter element action
4. By Lemma 6.7.2, eventually some dim < 0 at integer level
5. But dim = finrank ≥ 0, so must hit simple before that
6. B(d, d) = B(α_p, α_p) = 2 by preservation

This theorem, once fully proved, resolves `indecomposable_titsForm_le_two`
in `Corollary6_8_3.lean`. -/
theorem indecomposable_bilinearForm_eq_two
    (hDynkin : IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    (ρ : @QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((cartanMatrix n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) = 2 := by
  sorry

end Etingof
