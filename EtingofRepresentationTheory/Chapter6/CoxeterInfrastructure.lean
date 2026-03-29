import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import EtingofRepresentationTheory.Chapter6.Corollary6_8_2
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_7
import EtingofRepresentationTheory.Chapter6.Proposition6_6_8

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
  -- adj is nonneg
  have hadj_nonneg : ∀ i j, (0 : ℤ) ≤ adj i j := by
    intro i j; rcases hDynkin.2.2.1 i j with h | h <;> omega
  -- Total sum of adj
  set total := ∑ i : Fin n, ∑ j : Fin n, adj i j
  -- Upper bound: positive definiteness with x = all-ones gives 2n - total > 0
  have hone_ne : (fun (_ : Fin n) => (1 : ℤ)) ≠ 0 := by
    intro heq; have := congr_fun heq ⟨0, hn⟩; simp at this
  have hpos := hDynkin.2.2.2.2 (fun _ => (1 : ℤ)) hone_ne
  -- Expand B(1,1) = 2n - total
  have hexpand : dotProduct (fun _ => (1 : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) =
      2 * (↑n : ℤ) - total := by
    -- Row sum of (2I - adj) is 2 - row sum of adj
    have h_row : ∀ i : Fin n,
        ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j = 2 - ∑ j, adj i j := by
      intro i
      have h2I : ∑ j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = 2 := by
        simp [Matrix.smul_apply, Matrix.one_apply, Finset.mem_univ]
      simp only [Matrix.sub_apply]
      rw [Finset.sum_sub_distrib]
      linarith
    -- dotProduct 1 (M.mulVec 1) = ∑ i, ∑ j, M i j
    have h_dot : dotProduct (fun _ => (1 : ℤ))
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) =
        ∑ i, ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j := by
      simp only [dotProduct, Matrix.mulVec, one_mul, mul_one]
    rw [h_dot]
    -- Now ∑ i, ∑ j, (2I - adj) i j = ∑ i, (2 - ∑ j, adj i j) = 2n - total
    simp_rw [h_row]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, total]
    ring
  have hub : total < 2 * (↑n : ℤ) := by linarith
  -- Lower bound: 2n ≤ total via disjoint pair counting
  -- Define forward and backward pair maps
  have hfwd_inj : Function.Injective (fun v : Fin n => (v, next v)) :=
    fun a b h => (Prod.mk.inj h).1
  have hbwd_inj : Function.Injective (fun v : Fin n => (next v, v)) :=
    fun a b h => (Prod.mk.inj h).2
  -- The forward and backward images are disjoint (by hno_overlap)
  have hdisjoint : Disjoint
      (Finset.univ.image (fun v : Fin n => (v, next v)))
      (Finset.univ.image (fun v : Fin n => (next v, v))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨v, _, hv⟩ := hp1
    obtain ⟨w, _, hw⟩ := hp2
    exact absurd (hv ▸ hw ▸ rfl : (v, next v) = (next w, w)) (hno_overlap v w)
  -- Sum over forward pairs = n
  have h_fwd_sum : ∑ p ∈ Finset.univ.image (fun v : Fin n => (v, next v)),
      adj p.1 p.2 = ↑n := by
    rw [Finset.sum_image (fun a _ b _ h => hfwd_inj h)]
    simp [hadj_out, Finset.sum_const, Finset.card_univ, mul_one]
  -- Sum over backward pairs = n
  have h_bwd_sum : ∑ p ∈ Finset.univ.image (fun v : Fin n => (next v, v)),
      adj p.1 p.2 = ↑n := by
    rw [Finset.sum_image (fun a _ b _ h => hbwd_inj h)]
    simp [hadj_in, Finset.sum_const, Finset.card_univ, mul_one]
  -- Sum over the disjoint union = 2n
  have h_union_sum : ∑ p ∈ (Finset.univ.image (fun v : Fin n => (v, next v)) ∪
      Finset.univ.image (fun v : Fin n => (next v, v))),
      adj p.1 p.2 = 2 * ↑n := by
    rw [Finset.sum_union hdisjoint, h_fwd_sum, h_bwd_sum]; ring
  -- The union is a subset of all pairs, and adj ≥ 0, so total ≥ 2n
  have h_sub : Finset.univ.image (fun v : Fin n => (v, next v)) ∪
      Finset.univ.image (fun v : Fin n => (next v, v)) ⊆
      (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.subset_univ _
  have h_pair_sum : (∑ p : Fin n × Fin n, adj p.fst p.snd) = total := by
    show (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), adj p.fst p.snd) = total
    rw [Finset.univ_product_univ.symm, Finset.sum_product']
  have hlb : 2 * (↑n : ℤ) ≤ total := by
    have := Finset.sum_le_sum_of_subset_of_nonneg h_sub
      (fun p _ _ => hadj_nonneg p.1 p.2)
    linarith [h_union_sum, h_pair_sum]
  -- Contradiction: total < 2n and total ≥ 2n
  linarith

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

/-- Iterated reversal distributes over list append. -/
private lemma iteratedReversed_append
    {V : Type*} [DecidableEq V] (Q : Quiver V) (xs ys : List V) :
    iteratedReversedAtVertices Q (xs ++ ys) =
    iteratedReversedAtVertices (iteratedReversedAtVertices Q xs) ys := by
  induction xs generalizing Q with
  | nil => rfl
  | cons x xs ih => exact ih (@reversedAtVertex V _ Q x)

/-- Edges between vertices not in the reversal list are unchanged. -/
private lemma iteratedReversed_hom_not_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n))
    {a b : Fin n} (ha : a ∉ vs) (hb : b ∉ vs) :
    @Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a b =
    @Quiver.Hom (Fin n) Q a b := by
  induction vs generalizing Q with
  | nil => rfl
  | cons v vs ih =>
    have hav : a ≠ v := fun h => ha (List.mem_cons.mpr (Or.inl h))
    have hbv : b ≠ v := fun h => hb (List.mem_cons.mpr (Or.inl h))
    have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
    have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
    show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q v) vs) a b =
      @Quiver.Hom _ Q a b
    rw [ih _ ha' hb']
    exact ReversedAtVertexHom_ne_ne hav hbv

/-- In any nonempty subset S of vertices of a Dynkin quiver, there exists a vertex
in S with no outgoing Q-edges to S (a "local sink").

This is the subset generalization of `exists_sink_of_dynkin_orientation`. The proof
uses the same positive-definiteness contradiction: if every S-vertex has an S-outgoing
edge, counting forward/backward pairs gives ∑_{S×S} adj ≥ 2|S|, but B(d,d) > 0 for
the S-indicator d gives ∑_{S×S} adj < 2|S|. -/
private theorem exists_local_sink_of_dynkin
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ w ∈ S, @IsEmpty (@Quiver.Hom _ Q v w) := by
  by_contra hall
  push_neg at hall
  -- Every vertex in S has an outgoing edge within S
  have hout : ∀ v ∈ S, ∃ w ∈ S, Nonempty (@Quiver.Hom _ Q v w) := by
    intro v hv; obtain ⟨w, hw, hne⟩ := hall v hv
    exact ⟨w, hw, hne⟩
  -- Choose successor (dependently typed) and lift to total function
  choose next hnext_mem hnext_arr using hout
  set next' : Fin n → Fin n := fun v => if hv : v ∈ S then next v hv else v
  have hnext'_eq : ∀ v (hv : v ∈ S), next' v = next v hv :=
    fun v hv => dif_pos hv
  have hadj_out : ∀ v ∈ S, adj v (next' v) = 1 := by
    intro v hv; rw [hnext'_eq v hv]
    exact adj_eq_one_of_arrow hDynkin hOrient (hnext_arr v hv).some
  have hadj_in : ∀ v ∈ S, adj (next' v) v = 1 := by
    intro v hv; rw [hnext'_eq v hv]
    have hsymm := hDynkin.1
    have : adj (next v hv) v = adj v (next v hv) := by
      have := congr_fun (congr_fun hsymm v) (next v hv)
      simp [Matrix.transpose_apply] at this; exact this
    rw [this]; exact adj_eq_one_of_arrow hDynkin hOrient (hnext_arr v hv).some
  have hnext'_mem : ∀ v ∈ S, next' v ∈ S := by
    intro v hv; rw [hnext'_eq v hv]; exact hnext_mem v hv
  -- Forward and backward pair sets within S are disjoint
  have hno_overlap : ∀ v ∈ S, ∀ w ∈ S, (v, next' v) ≠ (next' w, w) := by
    intro v hv w hw heq
    rw [hnext'_eq v hv, hnext'_eq w hw] at heq
    have h1 : v = next w hw := congr_arg Prod.fst heq
    have h2 : next v hv = w := congr_arg Prod.snd heq
    apply hOrient.2.2 v w
    · rw [show w = next v hv from h2.symm]; exact hnext_arr v hv
    · rw [show v = next w hw from h1]; exact hnext_arr w hw
  -- adj is nonneg
  have hadj_nonneg : ∀ i j, (0 : ℤ) ≤ adj i j := by
    intro i j; rcases hDynkin.2.2.1 i j with h | h <;> omega
  -- Lower bound: counting forward + backward pairs gives sum ≥ 2|S|
  set total_S := ∑ i ∈ S, ∑ j ∈ S, adj i j with htotal_S_def
  -- Forward pairs: {(v, next' v) | v ∈ S}, injective on first component
  have h_fwd_sum : ∑ p ∈ S.image (fun v => (v, next' v)),
      adj p.1 p.2 = ↑S.card := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    rw [show ∑ x ∈ S, adj x (next' x) = ∑ _ ∈ S, (1 : ℤ) from
      Finset.sum_congr rfl (fun x hx => hadj_out x hx)]
    simp
  -- Backward pairs: {(next' v, v) | v ∈ S}, injective on second component
  have h_bwd_sum : ∑ p ∈ S.image (fun v => (next' v, v)),
      adj p.1 p.2 = ↑S.card := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).2)]
    rw [show ∑ x ∈ S, adj (next' x) x = ∑ _ ∈ S, (1 : ℤ) from
      Finset.sum_congr rfl (fun x hx => hadj_in x hx)]
    simp
  have hdisjoint : Disjoint
      (S.image (fun v => (v, next' v)))
      (S.image (fun v => (next' v, v))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨v, hv, hvp⟩ := hp1
    obtain ⟨w, hw, hwp⟩ := hp2
    exact absurd (hvp ▸ hwp ▸ rfl : (v, next' v) = (next' w, w)) (hno_overlap v hv w hw)
  have h_union_sum : ∑ p ∈ (S.image (fun v => (v, next' v)) ∪
      S.image (fun v => (next' v, v))),
      adj p.1 p.2 = 2 * ↑S.card := by
    rw [Finset.sum_union hdisjoint, h_fwd_sum, h_bwd_sum]; ring
  -- Both image sets are subsets of S × S
  have h_sub : S.image (fun v => (v, next' v)) ∪
      S.image (fun v => (next' v, v)) ⊆ S ×ˢ S := by
    apply Finset.union_subset <;> intro p hp <;> rw [Finset.mem_image] at hp <;>
      obtain ⟨v, hv, rfl⟩ := hp <;> simp [hv, hnext'_mem v hv]
  have hlb : 2 * (↑S.card : ℤ) ≤ total_S := by
    have h_prod_sum : ∑ p ∈ S ×ˢ S, adj p.1 p.2 = total_S := by
      rw [htotal_S_def, Finset.sum_product']
    have := Finset.sum_le_sum_of_subset_of_nonneg h_sub
      (fun p _ _ => hadj_nonneg p.1 p.2)
    linarith [h_union_sum, h_prod_sum]
  -- Upper bound: B(d, d) > 0 for S-indicator gives sum < 2|S|
  set d : Fin n → ℤ := fun v => if v ∈ S then 1 else 0 with hd_def
  have hd_ne : d ≠ 0 := by
    intro heq; obtain ⟨v, hv⟩ := hS
    have := congr_fun heq v; simp [hd_def, hv] at this
  have hpos := hDynkin.2.2.2.2 d hd_ne
  -- Expand B(d,d) = 2|S| - total_S
  have hexpand : dotProduct d ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d) =
      2 * ↑S.card - total_S := by
    -- Decompose: (2I - A)d = 2d - Ad, then d·(2d - Ad) = 2d·d - d·(Ad)
    have h_sub : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d =
        2 • d - adj.mulVec d := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h_sub, dotProduct_sub, dotProduct_smul, nsmul_eq_mul]; push_cast
    -- Helper: Finset.univ.filter (· ∈ S) = S
    have hfilter_S : (Finset.univ : Finset (Fin n)).filter (· ∈ S) = S := by ext; simp
    -- d · d = |S| (since d is a 0/1 indicator)
    have hdd : dotProduct d d = ↑S.card := by
      simp only [dotProduct, hd_def]
      rw [show ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) * (if i ∈ S then 1 else 0) =
        ∑ i, if i ∈ S then 1 else 0 from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)]
      simp only [← Finset.sum_filter, hfilter_S, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- d · (A d) = total_S (since d restricts both indices to S)
    have hdad : dotProduct d (adj.mulVec d) = total_S := by
      simp only [dotProduct, Matrix.mulVec, hd_def]
      -- inner sum: ∑ j, adj i j * d(j) = ∑ j ∈ S, adj i j
      have h_inner : ∀ i : Fin n,
          ∑ j, adj i j * (if j ∈ S then (1 : ℤ) else 0) = ∑ j ∈ S, adj i j := by
        intro i
        rw [show ∑ j, adj i j * (if j ∈ S then (1 : ℤ) else 0) =
          ∑ j, if j ∈ S then adj i j else 0 from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)]
        simp only [← Finset.sum_filter, hfilter_S]
      simp_rw [h_inner]
      -- outer sum: ∑ i, d(i) * (∑ j ∈ S, adj i j) = ∑ i ∈ S, ∑ j ∈ S, adj i j
      rw [show ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) * ∑ j ∈ S, adj i j =
        ∑ i, if i ∈ S then ∑ j ∈ S, adj i j else 0 from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)]
      simp only [← Finset.sum_filter, hfilter_S]; rfl
    linarith
  have hub : total_S < 2 * (↑S.card : ℤ) := by linarith
  -- Contradiction: total_S ≥ 2|S| and total_S < 2|S|
  linarith

/-- Edge from a non-participant `a` to a participant `b` in the iterated reversed
quiver equals the reverse-direction edge `b ⟶ a` in the original quiver Q.

When `b = vs[j]`, the reversal at step j flips the edge direction, and all other
reversals leave it unchanged (since `a ∉ vs` and `b` only appears once by nodup). -/
private lemma iteratedReversed_hom_to_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a : Fin n} (ha : a ∉ vs) {b : Fin n} (hb : b ∈ vs) :
    @Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a b =
    @Quiver.Hom (Fin n) Q b a := by
  induction vs generalizing Q with
  | nil => simp at hb
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp hb with rfl | hb_vs
    · -- b = v (head): reversal at b flips the edge (rfl replaced v with b)
      have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ b := fun h => ha (List.mem_cons.mpr (Or.inl h))
      show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q b) vs) a b = _
      rw [iteratedReversed_hom_not_mem _ vs ha' hvs.1]
      exact ReversedAtVertexHom_ne_eq hav rfl
    · -- b ∈ vs (tail): IH handles, reversal at v is transparent
      have ha' : a ∉ vs := fun h => ha (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ v := fun h => ha (List.mem_cons.mpr (Or.inl h))
      have hbv : b ≠ v := by intro h; subst h; exact hvs.1 hb_vs
      show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q v) vs) a b = _
      rw [ih (@reversedAtVertex _ _ Q v) hvs.2 ha' hb_vs]
      exact ReversedAtVertexHom_ne_ne hbv hav

/-- Edge from a participant `a` to a non-participant `b` in the iterated reversed
quiver equals the reverse-direction edge `b ⟶ a` in the original quiver Q.
Symmetric companion of `iteratedReversed_hom_to_mem`. -/
private lemma iteratedReversed_hom_from_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a : Fin n} (ha : a ∈ vs) {b : Fin n} (hb : b ∉ vs) :
    @Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a b =
    @Quiver.Hom (Fin n) Q b a := by
  induction vs generalizing Q with
  | nil => simp at ha
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp ha with rfl | ha_vs
    · -- a = v (head)
      have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
      have hbv : b ≠ a := fun h => hb (List.mem_cons.mpr (Or.inl h))
      show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q a) vs) a b = _
      rw [iteratedReversed_hom_not_mem _ vs hvs.1 hb']
      exact ReversedAtVertexHom_eq_ne rfl hbv
    · -- a ∈ vs (tail)
      have hb' : b ∉ vs := fun h => hb (List.mem_cons.mpr (Or.inr h))
      have hav : a ≠ v := by intro h; subst h; exact hvs.1 ha_vs
      have hbv : b ≠ v := fun h => hb (List.mem_cons.mpr (Or.inl h))
      show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q v) vs) a b = _
      rw [ih (@reversedAtVertex _ _ Q v) hvs.2 ha_vs hb']
      exact ReversedAtVertexHom_ne_ne hbv hav

/-- When both endpoints are in the reversal list, the double reversal returns
to the original Hom type. Each edge gets flipped twice: once when `a` is
processed and once when `b` is processed. -/
private lemma iteratedReversed_hom_both_mem
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    {a b : Fin n} (ha : a ∈ vs) (hb : b ∈ vs) (hab : a ≠ b) :
    @Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a b =
    @Quiver.Hom (Fin n) Q a b := by
  induction vs generalizing Q with
  | nil => simp at ha
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    rcases List.mem_cons.mp ha with rfl | ha_vs
    · -- a = v: a ∉ vs (by nodup), b ∈ vs (since b ≠ a = v, b ∈ v :: vs implies b ∈ vs)
      have ha_not : a ∉ vs := hvs.1
      have hb_vs : b ∈ vs := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd rfl hab
        · exact h
      show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q a) vs) a b = _
      rw [iteratedReversed_hom_to_mem _ vs hvs.2 ha_not hb_vs]
      -- Now: @Hom (reversedAtVertex Q a) b a = @Hom Q a b
      -- b ≠ a, so ReversedAtVertexHom a b a: x=b ≠ i=a, y=a = i → (i ⟶ x) = (a ⟶ b)
      exact ReversedAtVertexHom_ne_eq (Ne.symm hab) rfl
    · rcases List.mem_cons.mp hb with rfl | hb_vs
      · -- b = v: b ∉ vs (by nodup), a ∈ vs
        have hb_not : b ∉ vs := hvs.1
        show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q b) vs) a b = _
        rw [iteratedReversed_hom_from_mem _ vs hvs.2 ha_vs hb_not]
        -- Now: @Hom (reversedAtVertex Q b) b a = @Hom Q a b
        -- a ≠ b, so ReversedAtVertexHom b b a: x=b = i=b, y=a ≠ i → (y ⟶ i) = (a ⟶ b)
        exact ReversedAtVertexHom_eq_ne rfl hab
      · -- Both in vs (tail): use IH
        have hav : a ≠ v := by intro h; subst h; exact hvs.1 ha_vs
        have hbv : b ≠ v := by intro h; subst h; exact hvs.1 hb_vs
        show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q v) vs) a b = _
        rw [ih (@reversedAtVertex _ _ Q v) hvs.2 ha_vs hb_vs]
        exact ReversedAtVertexHom_ne_ne hav hbv

/-- Self-loops are preserved by iterated reversal.
At each reversal step, self-loops are unchanged regardless of the reversal vertex. -/
private lemma iteratedReversed_self_hom
    (Q : Quiver (Fin n)) (vs : List (Fin n)) (hvs : vs.Nodup)
    (a : Fin n) :
    @Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a a =
    @Quiver.Hom (Fin n) Q a a := by
  induction vs generalizing Q with
  | nil => rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    show @Quiver.Hom _ (iteratedReversedAtVertices (@reversedAtVertex _ _ Q v) vs) a a = _
    rw [ih (@reversedAtVertex _ _ Q v) hvs.2]
    by_cases hav : a = v
    · exact ReversedAtVertexHom_eq_eq hav hav
    · exact ReversedAtVertexHom_ne_ne hav hav

/-- **Round-trip lemma**: Reversing at every vertex in a permutation returns the
quiver to its original state. Each edge gets reversed twice (once for each endpoint),
and self-loops are always preserved. -/
private theorem iteratedReversedAtVertices_perm_eq
    (Q : Quiver (Fin n)) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n)) :
    iteratedReversedAtVertices Q σ = Q := by
  have hnodup : σ.Nodup := hσ.nodup_iff.mpr (List.nodup_finRange n)
  have hmem : ∀ v : Fin n, v ∈ σ := fun v => hσ.mem_iff.mpr (List.mem_finRange v)
  ext a b
  by_cases hab : a = b
  · subst hab; exact iteratedReversed_self_hom Q σ hnodup a
  · exact iteratedReversed_hom_both_mem Q σ hnodup (hmem a) (hmem b) hab

/-- A topological sort of a Dynkin quiver exists: a permutation of vertices
where ordering[k] has no Q-outgoing edges to ordering[m] for m ≥ k. -/
private theorem exists_topoSort
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj) :
    ∃ (ordering : List (Fin n)),
      ordering.Perm (List.finRange n) ∧ ordering.Nodup ∧
      ∀ k m (hk : k < ordering.length) (hm : m < ordering.length), k ≤ m →
        @IsEmpty (@Quiver.Hom _ Q (ordering.get ⟨k, hk⟩) (ordering.get ⟨m, hm⟩)) := by
  -- Build by induction with two invariants:
  -- (1) within-acc topological: acc[k] has no Q-edges to acc[m] for k ≤ m
  -- (2) acc-to-remaining: acc[k] has no Q-edges to any vertex in remaining
  suffices h : ∀ (remaining : Finset (Fin n)) (acc : List (Fin n)),
      acc.Nodup → acc.toFinset = Finset.univ \ remaining →
      (∀ k m (hk : k < acc.length) (hm : m < acc.length), k ≤ m →
        @IsEmpty (@Quiver.Hom _ Q (acc.get ⟨k, hk⟩) (acc.get ⟨m, hm⟩))) →
      (∀ k (hk : k < acc.length), ∀ w ∈ remaining,
        @IsEmpty (@Quiver.Hom _ Q (acc.get ⟨k, hk⟩) w)) →
      ∃ (ordering : List (Fin n)),
        ordering.Perm (List.finRange n) ∧ ordering.Nodup ∧
        ∀ k m (hk : k < ordering.length) (hm : m < ordering.length), k ≤ m →
          @IsEmpty (@Quiver.Hom _ Q (ordering.get ⟨k, hk⟩) (ordering.get ⟨m, hm⟩)) by
    exact h Finset.univ [] List.nodup_nil (by simp) (by simp) (by simp)
  intro remaining
  induction remaining using Finset.strongInduction with
  | H remaining ih =>
    intro acc hnodup hacc_set htopo hedge
    by_cases hrem : remaining.Nonempty
    · obtain ⟨v, hv_mem, hv_sink⟩ := exists_local_sink_of_dynkin hDynkin hOrient remaining hrem
      have hv_not_acc : v ∉ acc := by
        intro hv; rw [← List.mem_toFinset] at hv; rw [hacc_set] at hv
        simp at hv; exact hv hv_mem
      -- Local helpers: bridge List.get ↔ getElem for append
      have get_app_l {l₁ l₂ : List (Fin n)} {i : ℕ} (h₁ : i < l₁.length)
          {h₂ : i < (l₁ ++ l₂).length} :
          (l₁ ++ l₂).get ⟨i, h₂⟩ = l₁.get ⟨i, h₁⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left h₁
      have get_app_r {l₁ l₂ : List (Fin n)} {i : ℕ} (h₁ : l₁.length ≤ i)
          {h₂ : i < (l₁ ++ l₂).length} :
          (l₁ ++ l₂).get ⟨i, h₂⟩ = l₂.get ⟨i - l₁.length, by rw [List.length_append] at h₂; omega⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_right h₁
      apply ih (remaining.erase v) (Finset.erase_ssubset hv_mem) (acc ++ [v])
      · exact hnodup.append (List.nodup_singleton v)
          (by simp [List.disjoint_singleton]; exact hv_not_acc)
      · -- (acc ++ [v]).toFinset = Finset.univ \ remaining.erase v
        rw [List.toFinset_append, hacc_set]
        ext w
        simp only [Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert,
          Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
        tauto
      · -- Topological invariant for acc ++ [v]
        intro k m hk hm hkm
        rw [List.length_append, List.length_singleton] at hk hm
        by_cases hk_old : k < acc.length
        · by_cases hm_old : m < acc.length
          · -- Both in old acc
            rw [get_app_l hk_old, get_app_l hm_old]
            exact htopo k m hk_old hm_old hkm
          · -- k in old acc, m indexes v
            have hm_eq : m = acc.length := by omega
            subst hm_eq
            rw [get_app_l hk_old, get_app_r (by omega)]
            simp; exact hedge k hk_old v hv_mem
        · -- k indexes v
          have hk_eq : k = acc.length := by omega
          subst hk_eq
          have hm_eq : m = acc.length := by omega
          subst hm_eq
          rw [get_app_r (by omega)]
          simp; exact hv_sink v hv_mem
      · -- Edge-to-remaining invariant for acc ++ [v] with remaining.erase v
        intro k hk w hw
        rw [List.length_append, List.length_singleton] at hk
        have hw_rem : w ∈ remaining := Finset.mem_of_mem_erase hw
        by_cases hk_old : k < acc.length
        · rw [get_app_l hk_old]; exact hedge k hk_old w hw_rem
        · have hk_eq : k = acc.length := by omega
          subst hk_eq
          rw [get_app_r (by omega)]; simp
          exact hv_sink w hw_rem
    · -- remaining empty: acc is the full ordering
      rw [Finset.not_nonempty_iff_eq_empty] at hrem
      refine ⟨acc, ?_, hnodup, htopo⟩
      rw [List.perm_iff_count]; intro v
      have hv_acc : v ∈ acc := by rw [← List.mem_toFinset, hacc_set]; simp [hrem]
      rw [List.count_eq_one_of_mem hnodup hv_acc,
          List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange v)]

/-- Every Dynkin quiver orientation admits an admissible ordering.

The proof constructs a topological sort of the quiver (sinks first), using
`exists_local_sink_of_dynkin` to iteratively find vertices with no outgoing
edges to the remaining set. This topological sort is then shown to be an
admissible ordering: each vertex σₖ is a sink of the k-th iterated reversed
quiver because its outgoing Q-edges to earlier vertices get flipped by the
corresponding reversals, while edges to later vertices don't exist (by the
topological property). -/
theorem admissibleOrdering_exists
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj) :
    ∃ ordering : List (Fin n), IsAdmissibleOrdering Q ordering := by
  obtain ⟨ordering, hperm, hnodup, htopo⟩ := exists_topoSort hDynkin hOrient
  -- Bridge: List.get for take = List.get for original
  have get_take_eq {j k : ℕ} (hj : j < (ordering.take k).length) :
      (ordering.take k).get ⟨j, hj⟩ = ordering.get ⟨j, by rw [List.length_take] at hj; omega⟩ := by
    simp only [List.get_eq_getElem]; exact List.getElem_take
  -- Helper: ordering.get ⟨k, hk⟩ ∉ ordering.take k (by nodup)
  have get_not_mem_take : ∀ k (hk : k < ordering.length),
      ordering.get ⟨k, hk⟩ ∉ ordering.take k := by
    intro k hk hmem
    obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := List.mem_iff_get.mp hmem
    have hj_lt_k : j < k := by
      have : j < (ordering.take k).length := hj_lt
      rw [List.length_take] at this; exact lt_of_lt_of_le this (min_le_left k ordering.length)
    have hj_lt' : j < ordering.length := by omega
    have : ordering.get ⟨j, hj_lt'⟩ = ordering.get ⟨k, hk⟩ := by
      rw [← get_take_eq hj_lt, hj_eq]
    have hinj := hnodup.injective_get this
    simp only [Fin.mk.injEq] at hinj
    omega
  -- Helper: ordering.get ⟨m, hm⟩ ∈ ordering.take k when m < k
  have get_mem_take : ∀ m k (hm : m < ordering.length) (hmk : m < k),
      ordering.get ⟨m, hm⟩ ∈ ordering.take k := by
    intro m k hm hmk
    rw [List.mem_iff_get]
    have hm_take : m < (ordering.take k).length := by rw [List.length_take]; omega
    exact ⟨⟨m, hm_take⟩, get_take_eq hm_take⟩
  refine ⟨ordering, hperm, fun k hk => ?_⟩
  -- Show ordering[k] is a sink of iteratedReversedAtVertices Q (ordering.take k)
  intro w
  -- Find w's position in ordering (it's a permutation, so w is in it)
  have hw_mem : w ∈ ordering := hperm.mem_iff.mpr (List.mem_finRange w)
  obtain ⟨⟨m, hm⟩, hm_eq⟩ := List.mem_iff_get.mp hw_mem
  -- hm_eq : ordering.get ⟨m, hm⟩ = w; replace w with ordering.get ⟨m, hm⟩
  constructor; intro e; subst hm_eq
  by_cases hkm : k ≤ m
  · -- m ≥ k: both ordering[k] and ordering[m] are NOT in ordering.take k
    have hk_not := get_not_mem_take k hk
    have hm_not : ordering.get ⟨m, hm⟩ ∉ ordering.take k := by
      intro hmem
      obtain ⟨⟨j, hj_lt⟩, hj_eq⟩ := List.mem_iff_get.mp hmem
      have hj_lt_k : j < k := by
        have : j < (ordering.take k).length := hj_lt
        rw [List.length_take] at this; exact lt_of_lt_of_le this (min_le_left k ordering.length)
      have hj_lt' : j < ordering.length := by omega
      have : ordering.get ⟨j, hj_lt'⟩ = ordering.get ⟨m, hm⟩ := by
        rw [← get_take_eq hj_lt, hj_eq]
      have hinj := hnodup.injective_get this
      simp only [Fin.mk.injEq] at hinj
      omega
    have h_eq := iteratedReversed_hom_not_mem Q (ordering.take k) hk_not hm_not
    exact (htopo k m hk hm hkm).false (h_eq ▸ e)
  · -- m < k: ordering[m] IS in ordering.take k, edge gets flipped
    push_neg at hkm
    have hm_in := get_mem_take m k hm hkm
    have hk_not := get_not_mem_take k hk
    have htake_nodup : (ordering.take k).Nodup := hnodup.take
    have h_eq := iteratedReversed_hom_to_mem Q (ordering.take k) htake_nodup hk_not hm_in
    -- Arrow from ordering[k] to ordering[m] in iterated quiver = ordering[m] ⟶ ordering[k] in Q
    have : Nonempty (@Quiver.Hom _ Q (ordering.get ⟨m, hm⟩) (ordering.get ⟨k, hk⟩)) :=
      ⟨h_eq ▸ e⟩
    exact (htopo m k hm hk (by omega)).false this.some

/-! ## Generalized Coxeter element for arbitrary permutations

For any permutation σ of [0, ..., n-1], the product s_{σ₁} ∘ ... ∘ s_{σₙ}
is a Coxeter element. We prove that iterating any Coxeter element on a
nonneg nonzero vector eventually produces negative entries, generalizing
Lemma 6.7.2 to arbitrary orderings. -/

/-- If vertex j doesn't appear in the list, `iteratedSimpleReflection`
leaves coordinate j unchanged. -/
private lemma iteratedSimpleReflection_coord_not_mem
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (v : Fin n → ℤ)
    (j : Fin n) (hj : j ∉ vs) :
    iteratedSimpleReflection n A vs v j = v j := by
  induction vs generalizing v with
  | nil => rfl
  | cons k rest ih =>
    rw [iteratedSimpleReflection_cons]
    have hk : j ≠ k := fun h => hj (by simp [h])
    have hrest : j ∉ rest := fun h => hj (List.mem_cons.mpr (Or.inr h))
    rw [ih _ hrest]
    exact simpleReflection_apply_ne v k j hk

/-- `iteratedSimpleReflection` distributes over list append. -/
private lemma iteratedSimpleReflection_append
    (A : Matrix (Fin n) (Fin n) ℤ) (xs ys : List (Fin n))
    (v : Fin n → ℤ) :
    iteratedSimpleReflection n A (xs ++ ys) v =
    iteratedSimpleReflection n A ys (iteratedSimpleReflection n A xs v) := by
  simp [iteratedSimpleReflection, List.foldl_append]

/-- Iterating `c = iteratedSimpleReflection n A σ` M times equals
`iteratedSimpleReflection` on M concatenated copies of σ. -/
private lemma iteratedSimpleReflection_replicate_eq_iterate
    (A : Matrix (Fin n) (Fin n) ℤ) (σ : List (Fin n)) (v : Fin n → ℤ) (M : ℕ) :
    iteratedSimpleReflection n A ((List.replicate M σ).flatten) v =
    (fun w => iteratedSimpleReflection n A σ w)^[M] v := by
  set c := fun w => iteratedSimpleReflection n A σ w
  induction M generalizing v with
  | zero =>
    simp only [List.replicate_zero, List.flatten_nil, iteratedSimpleReflection,
      List.foldl_nil, Function.iterate_zero, id_eq]
  | succ M ih =>
    have hflat : (List.replicate (M + 1) σ).flatten = σ ++ (List.replicate M σ).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    simp only [hflat, iteratedSimpleReflection_append, ih,
      Function.iterate_succ, Function.comp_apply, c]

/-- `iteratedSimpleReflection` with a full permutation preserves B. -/
private lemma iteratedSimpleReflection_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (vs : List (Fin n))
    (v : Fin n → ℤ) :
    dotProduct (iteratedSimpleReflection n (cartanMatrix n adj) vs v)
      ((cartanMatrix n adj).mulVec
        (iteratedSimpleReflection n (cartanMatrix n adj) vs v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  induction vs generalizing v with
  | nil => rfl
  | cons k rest ih =>
    rw [iteratedSimpleReflection_cons]
    rw [ih]
    exact simpleReflection_preserves_B hDynkin v k

/-- **Key lemma**: A fixed point of any full-permutation Coxeter element
is zero.

If σ is a permutation of all n vertices and s_{σₙ}(...s_{σ₁}(v)...) = v,
then v = 0. The proof uses a forward telescoping argument: since σ is a
permutation, each coordinate σₖ is touched exactly once. The fixed-point
condition forces (A·v)_{σₖ} = 0 for each k, hence A·v = 0, hence v = 0
by positive definiteness. -/
private lemma iteratedSimpleReflection_perm_fixed_zero
    (hDynkin : IsDynkinDiagram n adj)
    (σ : List (Fin n)) (hσ : σ.Perm (List.finRange n))
    (v : Fin n → ℤ)
    (hfixed : iteratedSimpleReflection n (cartanMatrix n adj) σ v = v) :
    v = 0 := by
  set A := cartanMatrix n adj with hA_def
  have hnodup : σ.Nodup := hσ.nodup_iff.mpr (List.nodup_finRange n)
  have hlen : σ.length = n := by
    have := hσ.length_eq; rwa [List.length_finRange] at this
  -- Forward induction: iteratedSimpleReflection (σ.take k) v = v for all k
  suffices hall : ∀ k, k ≤ n →
      iteratedSimpleReflection n A (σ.take k) v = v by
    -- Extract A·v = 0 from the invariant
    suffices hAv : A.mulVec v = 0 by
      by_contra hv
      have hpos := hDynkin.2.2.2.2 v hv
      rw [show A = (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) from rfl]
        at hAv
      rw [hAv, dotProduct_zero] at hpos
      exact lt_irrefl 0 hpos
    ext p
    -- Find p's position in σ
    have hp_mem : p ∈ σ := hσ.mem_iff.mpr (List.mem_finRange p)
    obtain ⟨⟨k, hk_lt⟩, hk_eq⟩ := List.mem_iff_get.mp hp_mem
    -- From hall(k) and hall(k+1):
    -- iteratedSimpleReflection (σ.take (k+1)) v = v
    -- σ.take (k+1) = σ.take k ++ [σ[k]]
    have hk_lt_n : k < n := by rw [← hlen]; exact hk_lt
    have h_take_k := hall k (by omega)
    have h_take_k1 := hall (k + 1) (by omega)
    have htake_split : σ.take (k + 1) = σ.take k ++ [σ[k]] :=
      (List.take_append_getElem hk_lt).symm
    rw [htake_split, iteratedSimpleReflection_append, h_take_k] at h_take_k1
    -- Now: iteratedSimpleReflection [σ[k]] v = v
    -- i.e., simpleReflection σ[k] v = v
    simp only [iteratedSimpleReflection, List.foldl] at h_take_k1
    -- At coordinate σ[k] = p:
    have hp_eq : σ[k] = p := by
      change σ.get ⟨k, hk_lt⟩ = p; exact hk_eq
    have := congr_fun h_take_k1 p
    rw [← hp_eq] at this
    rw [simpleReflection_apply_self
      (cartanMatrix_isSymm hDynkin.1) v σ[k]] at this
    -- this : v σ[k] - (A *ᵥ v) σ[k] = v σ[k], and σ[k] = p
    rw [hp_eq] at this
    simp only [Pi.zero_apply]
    linarith
  intro k hk
  induction k with
  | zero => simp [iteratedSimpleReflection]
  | succ m ih =>
    have hm_le : m ≤ n := by omega
    have him := ih hm_le
    have hm_lt : m < σ.length := by rw [hlen]; omega
    have htake_split : σ.take (m + 1) =
        σ.take m ++ [σ[m]] :=
      (List.take_append_getElem hm_lt).symm
    rw [htake_split, iteratedSimpleReflection_append, him]
    set p : Fin n := σ[m]
    have hp_not_drop : p ∉ σ.drop (m + 1) := by
      intro hmem
      have hp_take : p ∈ σ.take (m + 1) := by
        rw [htake_split]; simp
      have hnd : (σ.take (m + 1) ++ σ.drop (m + 1)).Nodup := by
        rwa [List.take_append_drop]
      exact (List.nodup_append.mp hnd).2.2 p hp_take p hmem rfl
    -- From the full fixed-point and the fact that drop doesn't touch p:
    have hsplit : σ = σ.take (m + 1) ++ σ.drop (m + 1) :=
      (List.take_append_drop (m + 1) σ).symm
    have hfull : iteratedSimpleReflection n A σ v = v := hfixed
    rw [hsplit, iteratedSimpleReflection_append, htake_split,
      iteratedSimpleReflection_append, him] at hfull
    -- hfull: iteratedSimpleReflection (drop(m+1)) (iteratedSimpleReflection [p] v) = v
    -- iteratedSimpleReflection [p] v = simpleReflection n A p v
    have hsingleton : iteratedSimpleReflection n A [p] v = simpleReflection n A p v := by
      simp [iteratedSimpleReflection]
    rw [hsingleton] at hfull
    -- At coordinate p (not in drop):
    have hcoord := congr_fun hfull p
    rw [iteratedSimpleReflection_coord_not_mem A (σ.drop (m + 1))
      (simpleReflection n A p v) p hp_not_drop] at hcoord
    -- hcoord: s_p(v)(p) = v(p)
    rw [simpleReflection_apply_self
      (cartanMatrix_isSymm hDynkin.1) v p] at hcoord
    -- hcoord: v(p) - (A·v)(p) = v(p), so (A·v)(p) = 0
    have hAv_zero : (A.mulVec v) p = 0 := by linarith
    -- s_p(v) = v since (A·v)(p) = 0
    change iteratedSimpleReflection n A [p] v = v
    simp only [iteratedSimpleReflection, List.foldl]
    change v - dotProduct v (A.mulVec (Pi.single p 1)) • Pi.single p 1 = v
    have hcoeff : dotProduct v (A.mulVec (Pi.single p 1)) =
        (A.mulVec v) p := by
      have hAsymm := cartanMatrix_isSymm hDynkin.1
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
        mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show A j p = A p j from
          congr_fun (congr_fun hAsymm p) j]; ring
    rw [hcoeff, hAv_zero, zero_smul, sub_zero]

/-! ## Linearity and additivity of simple reflections -/

/-- Simple reflection is additive: s_i(u + v) = s_i(u) + s_i(v). -/
private lemma simpleReflection_add
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (u v : Fin n → ℤ) :
    simpleReflection n A i (u + v) =
    simpleReflection n A i u + simpleReflection n A i v := by
  unfold simpleReflection rootReflection
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul,
    add_dotProduct]
  ring

/-- Simple reflection maps 0 to 0. -/
private lemma simpleReflection_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    simpleReflection n A i 0 = 0 := by
  ext j
  simp only [simpleReflection, rootReflection, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, Pi.zero_apply, dotProduct, Matrix.mulVec]
  simp

/-- `iteratedSimpleReflection` is additive. -/
private lemma iteratedSimpleReflection_add
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (u v : Fin n → ℤ) :
    iteratedSimpleReflection n A vs (u + v) =
    iteratedSimpleReflection n A vs u + iteratedSimpleReflection n A vs v := by
  induction vs generalizing u v with
  | nil => rfl
  | cons k rest ih =>
    rw [iteratedSimpleReflection_cons, iteratedSimpleReflection_cons,
      iteratedSimpleReflection_cons, simpleReflection_add, ih]

/-- `iteratedSimpleReflection` maps 0 to 0. -/
private lemma iteratedSimpleReflection_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) :
    iteratedSimpleReflection n A vs 0 = 0 := by
  induction vs with
  | nil => rfl
  | cons k rest ih => rw [iteratedSimpleReflection_cons, simpleReflection_zero, ih]

/-- `iteratedSimpleReflection` distributes over finite sums. -/
private lemma iteratedSimpleReflection_sum
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n))
    {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℤ)) :
    iteratedSimpleReflection n A vs (∑ i ∈ s, f i) =
    ∑ i ∈ s, iteratedSimpleReflection n A vs (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [iteratedSimpleReflection_zero]
  | cons a s has ih =>
    rw [Finset.sum_cons, iteratedSimpleReflection_add, ih, Finset.sum_cons]

/-! ## Finiteness of B-level sets

The set of integer vectors with a given bilinear form value is finite
when the Cartan matrix is positive definite (Dynkin case). -/

/-- The set of integer vectors with a given B-value is finite for Dynkin diagrams. -/
private theorem finite_B_level_set
    (hDynkin : IsDynkinDiagram n adj) (K : ℤ) :
    Set.Finite {v : Fin n → ℤ |
      dotProduct v ((cartanMatrix n adj).mulVec v) = K} := by
  set A := cartanMatrix n adj with hA_def
  -- A.mulVec is injective (from positive definiteness)
  have hA_inj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hne
    have hpos := hDynkin.2.2.2.2 (x - y) (sub_ne_zero.mpr hne)
    have hzero : A.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have : dotProduct (x - y) (A.mulVec (x - y)) = 0 := by
      rw [hzero]; simp [dotProduct]
    rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
    linarith
  -- Positive semi-definiteness
  have hB_nonneg : ∀ w : Fin n → ℤ, 0 ≤ dotProduct w (A.mulVec w) := by
    intro w; by_cases hw : w = 0
    · subst hw; simp [dotProduct, Matrix.mulVec]
    · have := hDynkin.2.2.2.2 w hw
      rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at this
      linarith
  have hA_symm := cartanMatrix_isSymm hDynkin.1
  -- B(eᵢ, eᵢ) = 2
  have hBei : ∀ i : Fin n,
      dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2 := by
    intro i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [hA_def, cartanMatrix, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one]
    have := hDynkin.2.1 i; simp_all
  -- Symmetry helpers
  have hB_coord : ∀ (v : Fin n → ℤ) (i : Fin n),
      dotProduct v (A.mulVec (Pi.single i 1)) = A.mulVec v i := by
    intro v i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show A j i = A i j from congr_fun (congr_fun hA_symm i) j]; ring
  have hB_coord' : ∀ (v : Fin n → ℤ) (i : Fin n),
      dotProduct (Pi.single i 1) (A.mulVec v) = A.mulVec v i := by
    intro v i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Key bound: B(v,v) = K implies |(Av)ᵢ| ≤ K + 2
  have hAv_bound : ∀ v : Fin n → ℤ, dotProduct v (A.mulVec v) = K →
      ∀ i, -(K + 2) ≤ A.mulVec v i ∧ A.mulVec v i ≤ K + 2 := by
    intro v hv i
    have hplus := hB_nonneg (v + Pi.single i 1)
    have hminus := hB_nonneg (v - Pi.single i 1)
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add] at hplus
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at hminus
    rw [hv, hBei, hB_coord v i, hB_coord' v i] at hplus hminus
    constructor <;> omega
  -- Inject into finite Icc via A.mulVec
  apply Set.Finite.subset
    ((Set.finite_Icc (fun _ : Fin n => -(K + 2)) (fun _ => K + 2)).preimage
      (Set.InjOn.mono (Set.subset_univ _) (Set.injOn_of_injective hA_inj)))
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def]
  exact ⟨fun i => (hAv_bound v hv i).1, fun i => (hAv_bound v hv i).2⟩

/-! ## Generalized Lemma 6.7.2 for arbitrary permutation Coxeter elements

For any permutation σ of [0..n-1], the Coxeter element c_σ = s_{σ_n}∘...∘s_{σ_1}
satisfies: for nonneg nonzero β, some iterate c_σ^N(β) has a negative entry.

The proof uses: B-preservation → finite orbit → periodic → sum of period is
fixed by c_σ → zero by `iteratedSimpleReflection_perm_fixed_zero` → contradiction
with nonneg nonzero. -/

/-- Iterated application of the σ-Coxeter element preserves B. -/
private lemma iteratedSimpleReflection_iter_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (σ : List (Fin n))
    (v : Fin n → ℤ) (N : ℕ) :
    dotProduct ((fun w => iteratedSimpleReflection n (cartanMatrix n adj) σ w)^[N] v)
      ((cartanMatrix n adj).mulVec
        ((fun w => iteratedSimpleReflection n (cartanMatrix n adj) σ w)^[N] v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [iteratedSimpleReflection_preserves_B hDynkin, ih]

/-- The orbit of any vector under a σ-Coxeter element is finite. -/
private theorem iteratedSimpleReflection_orbit_finite
    (hDynkin : IsDynkinDiagram n adj) (σ : List (Fin n))
    (v : Fin n → ℤ) :
    Set.Finite (Set.range (fun N =>
      (fun w => iteratedSimpleReflection n (cartanMatrix n adj) σ w)^[N] v)) := by
  apply Set.Finite.subset (finite_B_level_set hDynkin
    (dotProduct v ((cartanMatrix n adj).mulVec v)))
  intro w ⟨N, hN⟩
  simp only [Set.mem_setOf_eq]
  rw [← hN, iteratedSimpleReflection_iter_preserves_B hDynkin]

/-- `iteratedSimpleReflection` negates: c(-v) = -c(v). -/
private lemma iteratedSimpleReflection_neg
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (v : Fin n → ℤ) :
    iteratedSimpleReflection n A vs (-v) =
    -iteratedSimpleReflection n A vs v := by
  have h : iteratedSimpleReflection n A vs v +
      iteratedSimpleReflection n A vs (-v) = 0 := by
    rw [← iteratedSimpleReflection_add, add_neg_cancel, iteratedSimpleReflection_zero]
  exact eq_neg_of_add_eq_zero_right h

/-- `iteratedSimpleReflection` distributes over subtraction. -/
private lemma iteratedSimpleReflection_sub
    (A : Matrix (Fin n) (Fin n) ℤ) (vs : List (Fin n)) (u v : Fin n → ℤ) :
    iteratedSimpleReflection n A vs (u - v) =
    iteratedSimpleReflection n A vs u - iteratedSimpleReflection n A vs v := by
  rw [sub_eq_add_neg, iteratedSimpleReflection_add, iteratedSimpleReflection_neg, ← sub_eq_add_neg]

/-- `iteratedSimpleReflection` with a permutation is injective.
Proof: if c(u) = c(v), then c(u-v) = 0, so B(u-v,u-v) = 0, hence u = v. -/
private lemma iteratedSimpleReflection_injective
    (hDynkin : IsDynkinDiagram n adj) (σ : List (Fin n))
    (_hσ : σ.Perm (List.finRange n)) :
    Function.Injective (fun v => iteratedSimpleReflection n (cartanMatrix n adj) σ v) := by
  intro u v huv
  have hlin : iteratedSimpleReflection n (cartanMatrix n adj) σ (u - v) = 0 := by
    rw [iteratedSimpleReflection_sub]
    exact sub_eq_zero.mpr huv
  have hB := iteratedSimpleReflection_preserves_B hDynkin σ (u - v)
  rw [hlin] at hB
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hB
  -- hB : 0 = Σ (u-v)_i * (A(u-v))_i, i.e. B(u-v,u-v) = 0
  by_contra hne
  have hpos := hDynkin.2.2.2.2 (u - v) (sub_ne_zero.mpr hne)
  rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = cartanMatrix n adj from rfl] at hpos
  -- hpos : 0 < dotProduct (u-v) (A *ᵥ (u-v))
  simp only [dotProduct] at hpos
  linarith

/-- The orbit of any vector under a permutation Coxeter element is eventually periodic.
Returns period M > 0 with c^M(v) = v. -/
private theorem iteratedSimpleReflection_periodic
    (hDynkin : IsDynkinDiagram n adj) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n)) (v : Fin n → ℤ) :
    ∃ M : ℕ, 0 < M ∧
      (fun w => iteratedSimpleReflection n (cartanMatrix n adj) σ w)^[M] v = v := by
  set c := fun w => iteratedSimpleReflection n (cartanMatrix n adj) σ w
  have hinj := iteratedSimpleReflection_injective hDynkin σ hσ
  have hfin := iteratedSimpleReflection_orbit_finite hDynkin σ v
  -- Orbit is a finite subset of (Fin n → ℤ), so by pigeonhole
  -- there exist a ≠ b with c^a(v) = c^b(v)
  have hnotinj : ∃ a b, c^[a] v = c^[b] v ∧ a ≠ b := by
    by_contra hall
    push_neg at hall
    -- hall : ∀ a b, c^a(v) = c^b(v) → a = b, i.e. the orbit map is injective
    exact Set.infinite_range_of_injective (fun a b hab => hall a b hab) |>.not_finite hfin
  obtain ⟨a, b, hab, hne⟩ := hnotinj
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨b - a, Nat.sub_pos_of_lt h, ?_⟩
    have hiter : c^[a] (c^[b - a] v) = c^[a] v := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt h)]
      exact hab.symm
    exact Function.Injective.iterate hinj a hiter
  · refine ⟨a - b, Nat.sub_pos_of_lt h, ?_⟩
    have hiter : c^[b] (c^[a - b] v) = c^[b] v := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt h)]
      exact hab
    exact Function.Injective.iterate hinj b hiter

/-- **Generalized Lemma 6.7.2**: For any permutation σ of [0..n-1], a nonneg nonzero
vector eventually gets a negative entry under iteration of the σ-Coxeter element.

Proof: by contradiction. If all iterates are nonneg, the orbit is periodic (by
finiteness). The sum of one period is a fixed point of c_σ, hence zero. But the
sum is nonneg and ≥ β ≠ 0. Contradiction. -/
private theorem generalized_Lemma6_7_2
    (hDynkin : IsDynkinDiagram n adj) (σ : List (Fin n))
    (hσ : σ.Perm (List.finRange n))
    (β : Fin n → ℤ) (hβ_nonneg : ∀ i, 0 ≤ β i) (hβ_nonzero : β ≠ 0) :
    ∃ N : ℕ, ∃ i : Fin n,
      ((fun v => iteratedSimpleReflection n (cartanMatrix n adj) σ v)^[N] β) i < 0 := by
  set c := fun v => iteratedSimpleReflection n (cartanMatrix n adj) σ v
  by_contra h
  push_neg at h
  -- h : ∀ N i, 0 ≤ c^[N](β) i
  -- Step 1: Get periodicity M > 0 with c^M(β) = β
  obtain ⟨M, hM_pos, hM_period⟩ := iteratedSimpleReflection_periodic hDynkin σ hσ β
  -- Step 2: Define S = β + c(β) + ... + c^{M-1}(β)
  set S := ∑ k ∈ Finset.range M, c^[k] β with hS_def
  -- Step 3: S is nonneg
  have hS_nonneg : ∀ i, 0 ≤ S i := by
    intro i; simp only [hS_def, Finset.sum_apply]
    exact Finset.sum_nonneg (fun k _ => h k i)
  -- Step 4: S ≠ 0 (β = c^0(β) is a summand, and all terms are nonneg)
  have hS_nonzero : S ≠ 0 := by
    intro hS_eq
    have hβ_zero : β = 0 := by
      funext i
      have hSi : S i = 0 := congr_fun hS_eq i
      rw [hS_def, Finset.sum_apply] at hSi
      have h_each := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h k i)).mp hSi
      have h0 : c^[0] β i = 0 := h_each 0 (Finset.mem_range.mpr hM_pos)
      simp only [Function.iterate_zero, id_eq] at h0
      exact h0
    exact hβ_nonzero hβ_zero
  -- Step 5: c(S) = S (by linearity + periodicity)
  -- c(S) = c(Σ c^k β) = Σ c^{k+1} β = Σ_{k=1}^{M} c^k β
  --      = Σ_{k=0}^{M-1} c^k β  (since c^M β = β)
  --      = S
  have hcS : c S = S := by
    -- c(S) = Σ c(c^k β) = Σ c^{k+1} β
    change iteratedSimpleReflection n (cartanMatrix n adj) σ S = S
    rw [hS_def, iteratedSimpleReflection_sum]
    -- Each term: c(c^k(β)) = c^{k+1}(β)
    have h_succ : ∀ k, iteratedSimpleReflection n (cartanMatrix n adj) σ (c^[k] β) =
        c^[k + 1] β := by
      intro k; change c (c^[k] β) = c^[k + 1] β
      rw [show k + 1 = k.succ from rfl, Function.iterate_succ', Function.comp_apply]
    simp_rw [h_succ]
    -- Σ_{k∈range M} c^{k+1} β = Σ_{k∈range M} c^k β (using c^M β = β)
    have hsr' := Finset.sum_range_succ' (fun k => c^[k] β) M
    have hsr := Finset.sum_range_succ (fun k => c^[k] β) M
    simp only [Function.iterate_zero, id_eq] at hsr'
    rw [show c^[M] β = β from hM_period] at hsr
    exact add_right_cancel (hsr'.symm.trans hsr)
  -- Step 6: S is a fixed point of c_σ, hence S = 0
  have hS_zero := iteratedSimpleReflection_perm_fixed_zero hDynkin σ hσ S hcS
  -- Step 7: But S ≠ 0. Contradiction.
  exact hS_nonzero hS_zero

/-! ## Dimension vector tracking through admissible ordering

The key connection: applying one full round of reflection functors along an
admissible ordering transforms the dimension vector by the Coxeter element.

Specifically, if σ = (σ₁, ..., σₙ) is an admissible ordering, then:
  d(F⁺_{σ₁} ... F⁺_{σₙ} V) = s_{σ₁} ... s_{σₙ} d(V) = c · d(V)

where c = s_{σ₁} ... s_{σₙ} is the Coxeter element.

Combined with the generalized Lemma 6.7.2 (Coxeter action eventually produces
negative entries) and Proposition 6.6.5 (non-surjective at sink → simple
representation), this gives the representation-level reduction.

This is the content of the book's proof of Theorem 6.8.1 + Corollary 6.8.2. -/

/-! ### Infrastructure: Subsingleton preservation and Fintype derivation

For Dynkin quiver orientations, each Hom type has at most one element (simple graph).
This `Subsingleton` property is preserved by `reversedAtVertex`, enabling `Fintype`
derivation for `ArrowsInto` which is needed by Proposition 6.6.8. -/

/-- `Subsingleton` for Hom types is preserved by `reversedAtVertex`.
Each case of `ReversedAtVertexHom` reduces to an original Hom type. -/
private lemma subsingleton_hom_reversedAtVertex
    [inst : DecidableEq (Fin n)]
    {Q : Quiver (Fin n)} [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (a b : Fin n) :
    Subsingleton (@Quiver.Hom (Fin n) (@reversedAtVertex (Fin n) inst Q p) a b) := by
  constructor
  intro x y
  revert x y
  change ∀ (x y : ReversedAtVertexHom (Fin n) p a b), x = y
  unfold ReversedAtVertexHom
  cases inst a p <;> cases inst b p <;> exact fun x y => Subsingleton.elim x y

/-- `Subsingleton` for Hom types is preserved by `iteratedReversedAtVertices`. -/
private lemma subsingleton_hom_iteratedReversed
    {Q : Quiver (Fin n)} [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (vs : List (Fin n)) (a b : Fin n) :
    Subsingleton (@Quiver.Hom (Fin n) (iteratedReversedAtVertices Q vs) a b) := by
  induction vs generalizing Q with
  | nil => change Subsingleton (@Quiver.Hom (Fin n) Q a b); infer_instance
  | cons v vs ih =>
    change Subsingleton (@Quiver.Hom (Fin n)
      (iteratedReversedAtVertices (@reversedAtVertex (Fin n) _ Q v) vs) a b)
    haveI : ∀ (a b : Fin n), Subsingleton
        (@Quiver.Hom (Fin n) (@reversedAtVertex (Fin n) _ Q v) a b) :=
      fun a b => subsingleton_hom_reversedAtVertex v a b
    exact @ih _ this

/-- Derive `Fintype` for each Hom type from `Subsingleton`, classically. -/
private noncomputable def fintypeHomOfSubsingleton
    {V : Type*} [Quiver V] [∀ (a b : V), Subsingleton (@Quiver.Hom V _ a b)]
    (a b : V) : Fintype (@Quiver.Hom V _ a b) := by
  classical
  exact if h : Nonempty (a ⟶ b)
    then Fintype.ofSubsingleton h.some
    else @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)

/-- Derive `Fintype (ArrowsInto Q i)` from `Subsingleton` Hom types on `Fin n`. -/
private noncomputable def fintypeArrowsIntoOfSubsingleton
    {Q : Quiver (Fin n)} [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (i : Fin n) : Fintype (@ArrowsInto (Fin n) Q i) := by
  haveI : ∀ (a : Fin n), Fintype (@Quiver.Hom (Fin n) Q a i) :=
    fun a => fintypeHomOfSubsingleton a i
  exact Sigma.instFintype

/-- `Module.Free` for the reflected representation at v ≠ i.
At v ≠ i, F⁺ᵢ(ρ).obj v = ρ.obj v, so Free transfers. -/
private lemma reflFunctorPlus_free_ne
    {k₀ : Type*} [Field k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : IsSink Q i)
    (ρ : @QuiverRepresentation k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)]
    (v : Q) (hv : v ≠ i) :
    Module.Free k₀ (@QuiverRepresentation.obj k₀ Q _ (reversedAtVertex Q i)
      (reflectionFunctorPlus Q i hi ρ) v) := by
  exact Module.Free.of_equiv (reflFunctorPlus_equivAt_ne hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
/-- `Module.Free` for the reflected representation at i (ker of linear map over field). -/
private lemma reflFunctorPlus_free_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : IsSink Q i)
    (ρ : @QuiverRepresentation k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (@ArrowsInto Q _ i)] :
    Module.Free k₀ (@QuiverRepresentation.obj k₀ Q _ (reversedAtVertex Q i)
      (reflectionFunctorPlus Q i hi ρ) i) := by
  -- Transport via the linear equivalence F⁺ᵢ(ρ).obj i ≃ₗ ker(sinkMap)
  -- Need AddCommGroup for the direct sum to make Free work for submodules over PIDs
  letI : AddCommGroup (DirectSum (@ArrowsInto Q _ i) (fun a => ρ.obj a.1)) :=
    addCommGroupOfRing (k := k₀)
  exact Module.Free.of_equiv (reflFunctorPlus_equivAt_eq hi ρ).symm

/-- `Module.Finite` for the reflected representation at v ≠ i. -/
private lemma reflFunctorPlus_finite_ne
    {k₀ : Type*} [Field k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : IsSink Q i)
    (ρ : @QuiverRepresentation k₀ Q _ _)
    [∀ v, Module.Finite k₀ (ρ.obj v)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite k₀ (@QuiverRepresentation.obj k₀ Q _ (reversedAtVertex Q i)
      (reflectionFunctorPlus Q i hi ρ) v) := by
  exact Module.Finite.equiv (reflFunctorPlus_equivAt_ne hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
/-- `Module.Finite` for the reflected representation at i. -/
private lemma reflFunctorPlus_finite_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : IsSink Q i)
    (ρ : @QuiverRepresentation k₀ Q _ _)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (@ArrowsInto Q _ i)] :
    Module.Finite k₀ (@QuiverRepresentation.obj k₀ Q _ (reversedAtVertex Q i)
      (reflectionFunctorPlus Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (@ArrowsInto Q _ i) (fun a => ρ.obj a.1)) :=
    addCommGroupOfRing (k := k₀)
  exact Module.Finite.equiv (reflFunctorPlus_equivAt_eq hi ρ).symm

/-! ### Bridge: simpleReflectionDimVector ↔ simpleReflection

For a sink p of an orientation of a Dynkin diagram with Subsingleton Hom types,
the ArrowsInto-indexed sum `Σ_{a : ArrowsInto Q p} d(a.1)` equals the
Cartan-matrix-indexed sum `Σ_j adj(p,j) * d(j)`, because:
- adj(p,j) = 1 iff there exists an arrow j → p (since p is a sink, all adjacent arrows point in)
- Subsingleton ensures at most one arrow per direction
- So the ArrowsInto sum runs over exactly those j with adj(p,j) = 1 -/

/-- At a sink of a Dynkin orientation with Subsingleton Hom types,
`simpleReflectionDimVector` equals `simpleReflection` on the dimension vector. -/
private lemma simpleReflectionDimVector_eq_simpleReflection
    (hDynkin : IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @IsSink (Fin n) Q p)
    (d : Fin n → ℤ) :
    haveI := fintypeArrowsIntoOfSubsingleton (Q := Q) p
    simpleReflectionDimVector (fun (a : @ArrowsInto (Fin n) Q p) => a.1) p d =
    simpleReflection n (cartanMatrix n adj) p d := by
  sorry

/-- **One round of reflection functors along an admissible ordering.**

For an indecomposable representation V with admissible ordering σ, either:
- Some prefix of σ reduces d(V) to a simple root αₚ, or
- After the full round, the Coxeter-transformed dimension vector c_σ(d(V))
  is nonneg and is the dimension vector of an indecomposable representation
  on the same quiver Q (since reversal at all vertices returns Q).

The proof applies Props 6.6.5, 6.6.7, 6.6.8 at each step of the admissible
ordering, threading the type-changing quiver instances. -/
private lemma one_round_or_simpleRoot
    (hDynkin : IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (σ : List (Fin n)) (hσ : IsAdmissibleOrdering Q σ)
    (ρ : @QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable)
    (d : Fin n → ℤ) (hd : d = fun v => (Module.finrank k (ρ.obj v) : ℤ)) :
    (∃ (i : ℕ) (p : Fin n), i ≤ σ.length ∧
      iteratedSimpleReflection n (cartanMatrix n adj) (σ.take i) d = simpleRoot n p)
    ∨
    ((∀ i, 0 ≤ iteratedSimpleReflection n (cartanMatrix n adj) σ d i) ∧
     iteratedSimpleReflection n (cartanMatrix n adj) σ d ≠ 0 ∧
     ∃ (ρ' : @QuiverRepresentation k (Fin n) _ Q)
       (_ : ∀ v, Module.Free k (ρ'.obj v))
       (_ : ∀ v, Module.Finite k (ρ'.obj v)),
       ρ'.IsIndecomposable ∧
       ∀ v, (Module.finrank k (ρ'.obj v) : ℤ) =
         iteratedSimpleReflection n (cartanMatrix n adj) σ d v) := by
  -- The proof proceeds by induction on the admissible ordering σ, tracking an
  -- indecomposable representation on iteratedReversedAtVertices Q (σ.take m).
  -- At each step m, apply Prop 6.6.5 (simple or surjective at sink σ[m]):
  --   - If simple: the dim vector is a simple root → left disjunct
  --   - If surjective: apply F⁺, getting indecomp rep on Q_{m+1} (Prop 6.6.7)
  --     with dim vector = simpleReflection of previous (Prop 6.6.8 + bridge lemma)
  -- At m = σ.length: Q_n = Q by iteratedReversedAtVertices_perm_eq → right disjunct.
  --
  -- Technical blocker: Lean universe constraint. The representation at step m lives on
  -- iteratedReversedAtVertices Q (σ.take m), which is Quiver.{v} (Fin n) at the same
  -- Hom universe v as Q. But the obj types of QuiverRepresentation introduce a separate
  -- universe u_obj, and when the induction state is wrapped in a ∀ or ∃, Lean cannot
  -- unify u_obj across steps. Infrastructure lemmas (Subsingleton preservation, Fintype
  -- derivation, Module.Free/Finite for F⁺, dim vector bridge) are provided above.
  sorry

/-- **Representation-level Theorem 6.8.1**: For an indecomposable representation V
of a Dynkin quiver, there exist simple reflections reducing d(V) to a simple root.

The proof follows the book's argument:
1. Choose an admissible ordering σ = (σ₁, ..., σₙ)
2. Apply `one_round_or_simpleRoot` to get either a simple root or a new indecomp rep
3. By the generalized Lemma 6.7.2, this iteration cannot continue indefinitely
4. Conclusion: some prefix of the iterated ordering reduces d(V) to a simple root -/
private lemma indecomposable_reduces_to_simpleRoot
    (hDynkin : IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      iteratedSimpleReflection n (cartanMatrix n adj) vertices
        (fun v => (Module.finrank k (ρ.obj v) : ℤ)) = simpleRoot n p := by
  obtain ⟨σ, hσ⟩ := admissibleOrdering_exists hDynkin hOrient
  set A := cartanMatrix n adj
  set d := fun v => (Module.finrank k (ρ.obj v) : ℤ) with hd_def
  set c := fun v => iteratedSimpleReflection n A σ v
  -- d is nonneg
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => Int.natCast_nonneg _
  -- d is nonzero (indecomposable → nontrivial at some vertex → finrank > 0)
  have hd_nonzero : d ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ.1
    intro heq
    have h0 : d v = 0 := congr_fun heq v
    simp only [hd_def] at h0
    -- finrank = 0 contradicts Nontrivial (which gives finrank ≥ 1)
    have hfr : Module.finrank k (ρ.obj v) = 0 := by exact_mod_cast h0
    -- Use the same pattern as Proposition6_6_7: upgrade AddCommMonoid to AddCommGroup
    letI : ∀ w, AddCommGroup (ρ.obj w) := fun w => Etingof.addCommGroupOfRing (k := k)
    have hpos := Module.finrank_pos (R := k) (M := ρ.obj v)
    omega
  -- By generalized Lemma 6.7.2: ∃ N i, c^N(d)_i < 0
  have hσ_perm := hσ.perm
  obtain ⟨N, i, hNeg⟩ := generalized_Lemma6_7_2 hDynkin σ hσ_perm d hd_nonneg hd_nonzero
  -- Iterate one_round_or_simpleRoot N times, threading the representation.
  -- Strengthen the induction: at each round M, either found a simple root,
  -- or have an indecomposable representation ρ_M on Q with dim vec = c^M(d).
  suffices ∀ (M : ℕ),
    (∃ (vertices : List (Fin n)) (p : Fin n),
      iteratedSimpleReflection n A vertices d = simpleRoot n p) ∨
    ((∀ j, 0 ≤ c^[M] d j) ∧
     ∃ (ρ_M : @QuiverRepresentation k (Fin n) _ Q),
       (∀ v, Module.Free k (ρ_M.obj v)) ∧
       (∀ v, Module.Finite k (ρ_M.obj v)) ∧
       ρ_M.IsIndecomposable ∧
       (∀ v, (Module.finrank k (ρ_M.obj v) : ℤ) = c^[M] d v)) by
    rcases this N with ⟨vertices, p, hp⟩ | ⟨hNN, _⟩
    · exact ⟨vertices, p, hp⟩
    · exact absurd (hNN i) (not_le.mpr hNeg)
  intro M
  induction M with
  | zero =>
    right
    exact ⟨fun j => by simp only [Function.iterate_zero, id_eq]; exact hd_nonneg j,
           ρ, ‹_›, ‹_›, hρ,
           fun v => by simp only [Function.iterate_zero, id_eq, hd_def]⟩
  | succ M ih =>
    rcases ih with ⟨vertices, p, hp⟩ | ⟨hM_nonneg, ρ_M, hFree_M, hFinite_M, hIndecomp_M, hDimVec_M⟩
    · left; exact ⟨vertices, p, hp⟩
    · -- c^M(d) is nonneg and is the dim vector of indecomp ρ_M on Q.
      -- Apply one_round_or_simpleRoot to ρ_M.
      haveI : ∀ v, Module.Free k (ρ_M.obj v) := hFree_M
      haveI : ∀ v, Module.Finite k (ρ_M.obj v) := hFinite_M
      have hd_M : c^[M] d = fun v => (Module.finrank k (ρ_M.obj v) : ℤ) := by
        ext v; exact (hDimVec_M v).symm
      rcases one_round_or_simpleRoot hDynkin hOrient σ hσ ρ_M hIndecomp_M
        (c^[M] d) hd_M with
        ⟨j, p, hj, hp⟩ | ⟨hnonneg, hnonzero, ρ', hFree', hFinite', hIndecomp', hDimVec'⟩
      · -- Found simple root at prefix j of round M
        left
        -- The full vertex sequence is σ^M ++ σ.take j
        refine ⟨(List.replicate M σ).flatten ++ σ.take j, p, ?_⟩
        rw [iteratedSimpleReflection_append]
        rw [iteratedSimpleReflection_replicate_eq_iterate]
        exact hp
      · -- Full round completed: c^{M+1}(d) is nonneg with indecomp rep ρ'
        right
        refine ⟨fun j => ?_, ρ', hFree', hFinite', hIndecomp', fun v => ?_⟩
        · rw [Function.iterate_succ', Function.comp_apply]; exact hnonneg j
        · rw [Function.iterate_succ', Function.comp_apply]; exact hDimVec' v

/-- The dimension vector of an indecomposable representation of a Dynkin quiver
satisfies B(d, d) = 2 (not just ≤ 2).

The proof uses `indecomposable_reduces_to_simpleRoot` to find reflections reducing d(V) to a
simple root αₚ, then applies `Corollary6_8_2` (bilinear form preservation through
reflections) to conclude B(d(V), d(V)) = B(αₚ, αₚ) = 2.

This theorem resolves `indecomposable_titsForm_le_two` in `Corollary6_8_3.lean`. -/
theorem indecomposable_bilinearForm_eq_two
    (hDynkin : IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((cartanMatrix n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) = 2 := by
  set d := fun v => (Module.finrank k (ρ.obj v) : ℤ) with hd_def
  -- d is nonneg (finranks are nonneg)
  have hd_pos : ∀ v, 0 ≤ d v := fun v => Int.natCast_nonneg _
  -- d is nonzero (V is indecomposable, hence nontrivial at some vertex)
  have hd_nonzero : d ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ.1
    intro heq
    have hv_eq := congr_fun heq v
    simp only [hd_def, Pi.zero_apply, Int.natCast_eq_zero] at hv_eq
    -- finrank = 0 → Subsingleton, contradicting Nontrivial
    letI : AddCommGroup (ρ.obj v) := addCommGroupOfRing (k := k)
    have hsub : Subsingleton (ρ.obj v) := Module.finrank_zero_iff.mp hv_eq
    exact not_nontrivial (ρ.obj v) hv
  -- By rep-level Theorem 6.8.1: reflections reduce d to a simple root
  obtain ⟨vertices, p, hrefl⟩ := indecomposable_reduces_to_simpleRoot hDynkin hOrient ρ hρ
  -- By Corollary 6.8.2: d is a positive root
  have hroot := Corollary6_8_2 hDynkin d hd_pos hd_nonzero ⟨vertices, p, hrefl⟩
  -- Extract B(d, d) = 2 from IsPositiveRoot
  -- IsPositiveRoot = (d ≠ 0 ∧ B(d,d) = 2) ∧ (∀ i, 0 ≤ d i)
  -- where B uses (2 • 1 - adj) = cartanMatrix n adj
  exact hroot.1.2

end Etingof
