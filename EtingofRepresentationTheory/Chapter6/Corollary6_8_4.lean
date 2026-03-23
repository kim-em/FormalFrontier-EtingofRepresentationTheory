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

### Infrastructure built
- **Simple representation construction** (`simpleRepresentation`): Constructs the
  indecomposable representation k₍ₚ₎ at vertex p (1-dim at p, 0 elsewhere, all
  maps zero) for any quiver Q.
- **Base case proved** (`Corollary6_8_4_simpleRoot`): When α = simpleRoot n p,
  the simple representation realizes it.
- **Induction structure**: The main proof reduces via Theorem 6.8.1 to the base
  case plus a reflection functor chain step (sorry'd).

### Remaining blocker
- **Reflection functor chain** (`reflectionFunctorChainStep`): Applying F⁻ᵢ to
  transform a realization on the reversed quiver back to Q. This requires:
  - Iterated quiver reversal tracking
  - Proposition 6.6.7 source case (currently sorry'd)
  - Proposition 6.6.8 source case for dimension vector tracking

### Fixed (issue #1094)
- **Q-adj connection**: Added `IsOrientationOf Q adj` hypothesis linking the
  quiver to the Dynkin diagram's adjacency matrix.
- **Universe polymorphism**: Pinned `obj` universe to match `k` in the
  conclusion's `QuiverRepresentation`.
-/

open scoped Matrix

/-- A quiver `Q` on `Fin n` is an orientation of the undirected graph with adjacency
matrix `adj` if:
- for each edge (`adj i j = 1`), exactly one of `i ⟶ j` or `j ⟶ i` is inhabited;
- for non-edges (`adj i j ≠ 1`), no arrows exist in either direction.

This predicate connects the unoriented graph (encoded by `adj`) to the oriented
quiver `Q`, which is needed for Gabriel's theorem: the positive roots of the
Dynkin diagram correspond to indecomposable representations of any orientation. -/
def Etingof.IsOrientationOf {n : ℕ} (Q : Quiver (Fin n))
    (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  -- Non-edges have no arrows
  (∀ i j : Fin n, adj i j ≠ 1 → IsEmpty (Q.Hom i j)) ∧
  -- Each edge is oriented: exactly one direction
  (∀ i j : Fin n, adj i j = 1 → Nonempty (Q.Hom i j) ∨ Nonempty (Q.Hom j i)) ∧
  (∀ i j : Fin n, Nonempty (Q.Hom i j) → Nonempty (Q.Hom j i) → False)

section SimpleRepresentation

/-- The simple quiver representation at vertex p: assigns `Fin 1 → k` at p,
`Fin 0 → k` at all other vertices, and zero maps on all edges. -/
noncomputable def Etingof.simpleRepresentation
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n)
    {Q : Quiver (Fin n)} :
    @Etingof.QuiverRepresentation k (Fin n) _ Q where
  obj v := Fin (if v = p then 1 else 0) → k
  mapLinear _ := 0

/-- The simple representation at p has `Module.Free k` at every vertex. -/
instance Etingof.simpleRepresentation_free
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Free k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
  Module.Free.pi _ _

/-- The simple representation at p has `Module.Finite k` at every vertex. -/
instance Etingof.simpleRepresentation_finite
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Finite k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
  Module.Finite.pi

private lemma Etingof.simpleRepresentation_finrank
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) =
      if v = p then 1 else 0 := by
  change Module.finrank k (Fin (if v = p then 1 else 0) → k) = _
  split_ifs with h <;> simp_all [Module.finrank_pi_fintype]

private lemma Etingof.simpleRepresentation_finrank_eq_simpleRoot
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    (Etingof.simpleRoot n p v : ℤ) =
      ↑(Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj v)) := by
  rw [Etingof.simpleRepresentation_finrank]
  simp only [Etingof.simpleRoot, Pi.single_apply]
  split_ifs <;> simp_all

set_option maxHeartbeats 400000 in
-- 1-dim space case analysis with finrank API needs extra heartbeats
/-- The simple representation at p is indecomposable: nontrivial at p and
any complementary sub-representations must have one component trivial. -/
private lemma Etingof.simpleRepresentation_indecomposable
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} :
    (Etingof.simpleRepresentation k p (Q := Q)).IsIndecomposable := by
  refine ⟨⟨p, ?_⟩, fun W₁ W₂ _ _ hcompl => ?_⟩
  · -- Nontrivial at p: Fin 1 → k is nontrivial
    change Nontrivial (Fin (if p = p then 1 else 0) → k)
    simp only [ite_true]
    exact Pi.nontrivial
  · -- At vertices v ≠ p, both submodules are ⊥ (zero-dimensional space)
    have hbot : ∀ v, v ≠ p → W₁ v = ⊥ ∧ W₂ v = ⊥ := by
      intro v hv
      have hempty : IsEmpty (Fin (if v = p then 1 else 0)) := by
        simp only [hv, ite_false]; exact Fin.isEmpty
      haveI : Subsingleton ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        show Subsingleton (Fin (if v = p then 1 else 0) → k) from inferInstance
      exact ⟨Submodule.eq_bot_of_subsingleton, Submodule.eq_bot_of_subsingleton⟩
    -- At vertex p, 1-dimensional space: one complement must be ⊥
    have hdim_p : Module.finrank k (Fin (if p = p then 1 else 0) → k) = 1 := by
      simp
    -- In a 1-dim space, any IsCompl pair has one component = ⊥
    have hcompl_p := hcompl p
    -- Use disjointness: W₁ ⊓ W₂ = ⊥, W₁ ⊔ W₂ = ⊤
    -- In a 1-dim space, if both are nonzero then both = ⊤, contradicting disjointness
    have : W₁ p = ⊥ ∨ W₂ p = ⊥ := by
      -- upgrade to AddCommGroup for Submodule API
      letI : ∀ v, AddCommGroup ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        fun v => Etingof.addCommGroupOfField (k := k)
      by_contra h
      push_neg at h
      obtain ⟨h1, h2⟩ := h
      have hr1 := Submodule.one_le_finrank_iff.mpr h1
      have hr2 := Submodule.one_le_finrank_iff.mpr h2
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W₁ p) (W₂ p)
      rw [hcompl_p.sup_eq_top, hcompl_p.inf_eq_bot] at hsum
      rw [finrank_top, finrank_bot] at hsum
      -- finrank of the whole space at p equals 1
      have hdim_p' : Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj p) = 1 :=
        hdim_p
      omega
    rcases this with h | h
    · left; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).1
    · right; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).2

end SimpleRepresentation

universe u in
/-- Base case: when α is a simple root, the simple representation realizes it.
The `obj` universe is fixed to match `k` (uses `Fin m → k` for spaces).
Note: This fixes `QuiverRepresentation.obj` to live in the same universe as `k`. -/
theorem Etingof.Corollary6_8_4_simpleRoot
    {n : ℕ} (p : Fin n)
    (k : Type u) [Field k]
    {Q : Quiver (Fin n)} :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (Etingof.simpleRoot n p v : ℤ) = ↑(Module.finrank k (ρ.obj v)) :=
  ⟨Etingof.simpleRepresentation k p,
   fun v => Etingof.simpleRepresentation_free k p v,
   fun v => Etingof.simpleRepresentation_finite k p v,
   Etingof.simpleRepresentation_indecomposable k p,
   fun v => Etingof.simpleRepresentation_finrank_eq_simpleRoot k p v⟩

universe v_arrow in
private lemma nonempty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    Nonempty X → Nonempty Y :=
  fun hx => match h with | rfl => hx

universe v_arrow in
private lemma isEmpty_of_eq {X Y : Sort v_arrow} (h : X = Y) :
    IsEmpty Y → IsEmpty X :=
  fun hy => match h with | rfl => hy

/-- Reversing all arrows at a vertex preserves the orientation property. -/
lemma Etingof.reversedAtVertex_isOrientationOf
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hadj_symm : adj.IsSymm) (hnoloop : ∀ v, adj v v = 0)
    {Q : Quiver (Fin n)} (hQ : Etingof.IsOrientationOf Q adj) (p : Fin n) :
    Etingof.IsOrientationOf (@Etingof.reversedAtVertex (Fin n) _ Q p) adj := by
  obtain ⟨hQ_nonarrow, hQ_edge, hQ_unique⟩ := hQ
  have adj_symm : ∀ i j, adj i j = adj j i := by
    intro i j
    have := congr_fun (congr_fun hadj_symm j) i
    simp [Matrix.transpose_apply] at this
    exact this
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b ha_arr hb_arr => ?_⟩
  · -- Non-edges: no arrows in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_eq_eq ha hb) (hQ_nonarrow a b hab)
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb)
        (hQ_nonarrow b p fun h => hab (by rw [ha, adj_symm p b]; exact h))
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb)
        (hQ_nonarrow p a fun h => hab (by rw [hb, adj_symm a p]; exact h))
    · exact isEmpty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb) (hQ_nonarrow a b hab)
  · -- Each edge has an arrow in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact absurd (by rw [ha, hb] at hab; rw [hnoloop] at hab; exact hab.symm) one_ne_zero
    · have h_bp : adj b p = 1 := by rw [adj_symm b p, ← ha]; exact hab
      rcases hQ_edge b p h_bp with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq hb ha).symm h
    · have h_pa : adj p a = 1 := by rw [adj_symm p a, ← hb]; exact hab
      rcases hQ_edge p a h_pa with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne hb ha).symm h
    · rcases hQ_edge a b hab with h | h
      · left; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb).symm h
      · right; exact nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne hb ha).symm h
  · -- No two-way arrows in reversed quiver
    by_cases ha : a = p <;> by_cases hb : b = p
    · exact hQ_unique a b
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_eq ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_eq hb ha) hb_arr)
    · exact hQ_unique b p
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq hb ha) hb_arr)
    · exact hQ_unique p a
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_eq ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_eq_ne hb ha) hb_arr)
    · exact hQ_unique a b
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne ha hb) ha_arr)
        (nonempty_of_eq (Etingof.ReversedAtVertexHom_ne_ne hb ha) hb_arr)

universe u in
/-- Every positive root of a Dynkin quiver is the dimension vector of some
indecomposable representation.

Given a Dynkin diagram with adjacency matrix `adj`, an orientation `Q` of that
diagram, and a positive root α (i.e., α ≠ 0, B(α, α) = 2, all coordinates
nonneg), there exists an indecomposable quiver representation ρ over any field k
such that `finrank k (ρ.obj v) = α v` at each vertex v.
(Etingof Corollary 6.8.4) -/
theorem Etingof.Corollary6_8_4
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (α : Fin n → ℤ) (hα : Etingof.IsPositiveRoot n adj α)
    (k : Type u) [Field k]
    {Q : Quiver (Fin n)} (hQ : Etingof.IsOrientationOf Q adj) :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  -- Strong induction on coordinate sum, using exists_good_vertex directly.
  -- This avoids needing the vertex list from Theorem 6.8.1 to export the
  -- "good vertex" property at each step.
  set A := Etingof.cartanMatrix n adj with hA_def
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  suffices h : ∀ (m : ℕ) (α : Fin n → ℤ) (Q : Quiver (Fin n)),
      (∑ j, α j).toNat = m →
      Etingof.IsPositiveRoot n adj α →
      Etingof.IsOrientationOf Q adj →
      ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v))
        (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.IsIndecomposable ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) from
    h _ α Q rfl hα hQ
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro α Q hm hα_pos hQ_orient
    have hα_nonneg := hα_pos.2
    have hα_nonzero := hα_pos.1.1
    have hα_root := hα_pos.1.2
    have hsum_pos := Etingof.sum_pos_of_nonneg_ne_zero α hα_nonneg hα_nonzero
    by_cases hle : ∑ j : Fin n, α j ≤ 1
    · -- Base case: ∑ α = 1, so α is a simple root → use simple representation.
      have hα_sum : ∑ j : Fin n, α j = 1 := by omega
      obtain ⟨p, hp⟩ := Etingof.sum_one_is_simpleRoot α hα_nonneg hα_nonzero hα_sum
      subst hp
      exact Etingof.Corollary6_8_4_simpleRoot p k
    · -- Inductive step: find good vertex, reflect, recurse.
      push_neg at hle
      have hd_sum2 : 2 ≤ ∑ j : Fin n, α j := by omega
      -- Step 1: Find a good vertex i with 0 < (Aα)_i ≤ α_i.
      obtain ⟨i, hi_pos, hi_le⟩ :=
        Etingof.exists_good_vertex hDynkin α hα_nonneg hα_nonzero hα_root hd_sum2
      -- Step 2: α' = s_i(α) is a positive root with strictly smaller coordinate sum.
      set α' := Etingof.simpleReflection n A i α with hα'_def
      have hα'_nonneg : ∀ j, 0 ≤ α' j :=
        Etingof.simpleReflection_nonneg hAsymm α i hα_nonneg hi_le
      have hα'_nonzero : α' ≠ 0 :=
        Etingof.simpleReflection_nonzero hDynkin α i hα_root
      have hα'_B : dotProduct α' (A.mulVec α') = 2 :=
        (Etingof.simpleReflection_preserves_B hDynkin α i).trans hα_root
      have hα'_positive : Etingof.IsPositiveRoot n adj α' :=
        ⟨⟨hα'_nonzero, hα'_B⟩, hα'_nonneg⟩
      have hα'_sum : ∑ j, α' j = (∑ j, α j) - (A.mulVec α) i :=
        Etingof.simpleReflection_sum hAsymm α i
      have hα'_sum_lt : (∑ j, α' j).toNat < m := by
        have h1 : ∑ j, α' j < ∑ j, α j := by linarith
        have h2 : 0 ≤ ∑ j, α' j := Finset.sum_nonneg fun i _ => hα'_nonneg i
        omega
      -- Step 3: The reversed quiver Q' is still an orientation of adj.
      have hQ' : Etingof.IsOrientationOf
          (@Etingof.reversedAtVertex (Fin n) _ Q i) adj :=
        Etingof.reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hQ_orient _
      -- Step 4: By IH, get an indecomposable ρ' on Q' with dimension vector α'.
      obtain ⟨ρ', hfree', hfinite', hindec', hdim'⟩ :=
        ih _ hα'_sum_lt α' (@Etingof.reversedAtVertex (Fin n) _ Q i) rfl hα'_positive hQ'
      -- Step 5: Construct ρ on Q from ρ' on Q' via reflection functor at i.
      -- The full argument requires:
      -- (a) Determine if i is a sink or source in Q' and apply F⁺ᵢ or F⁻ᵢ.
      -- (b) Double reversal: reversedAtVertex (reversedAtVertex Q i) i = Q,
      --     so the result lives on Q.
      -- (c) Proposition 6.6.7: reflection functor preserves indecomposability.
      -- (d) Proposition 6.6.8: d(F±ᵢ(ρ')) = sᵢ(d(ρ')) = sᵢ(α') = α.
      -- These require sorry'd Propositions 6.6.6/6.6.7 and quiver reversal
      -- infrastructure not yet available.
      sorry
