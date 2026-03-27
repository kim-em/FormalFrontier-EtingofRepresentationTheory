import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import EtingofRepresentationTheory.Chapter6.Corollary6_8_2
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

/-- **Representation-level Theorem 6.8.1**: For an indecomposable representation V
of a Dynkin quiver, there exist simple reflections reducing d(V) to a simple root.

The proof follows the book's argument:
1. Choose an admissible ordering σ = (σ₁, ..., σₙ)
2. Apply reflection functors F⁺_{σ₁}, F⁺_{σ₂}, ... along the ordering
3. At each step, by Prop 6.6.5: either V^(i) is simple (done) or surjective at σᵢ
4. If surjective, by Prop 6.6.8: d(V^(i+1)) = s_{σᵢ}(d(V^(i)))
5. By Prop 6.6.7: V^(i+1) is indecomposable
6. By Lemma 6.7.2: this cannot continue indefinitely (d would get negative entries)
7. At the first non-surjective step, d(V^(i)) = αₚ for some vertex p

The main technical challenge is the type-changing iteration: each F⁺ changes the
quiver type. This requires threading `Module.Free`/`Module.Finite` instances and
connecting the representation-level iteration to `iteratedSimpleReflection`. -/
private lemma indecomposable_reduces_to_simpleRoot
    (hDynkin : IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)} (hOrient : IsOrientationOf Q adj)
    (ρ : @QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      iteratedSimpleReflection n (cartanMatrix n adj) vertices
        (fun v => (Module.finrank k (ρ.obj v) : ℤ)) = simpleRoot n p := by
  -- Requires type-changing iterated reflection functor along admissible ordering.
  -- Each F⁺_i changes the quiver from Q to reversedAtVertex Q i, requiring
  -- Module.Free/Module.Finite instances to be threaded through the iteration.
  -- The termination argument uses Lemma 6.7.2 (Coxeter action eventually produces
  -- negative entries) combined with the constraint that finrank ≥ 0.
  sorry

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
