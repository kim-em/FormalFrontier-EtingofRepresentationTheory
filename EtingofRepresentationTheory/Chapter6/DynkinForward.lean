import Mathlib
import EtingofRepresentationTheory.Chapter6.DynkinTypes

namespace Etingof

open Matrix Finset

/-! ## Forward direction infrastructure

The forward direction of the Dynkin classification proceeds by elimination:

1. **No cycles**: A cycle of length k has null vector (1,1,...,1) for the Cartan form.
   Any graph containing a cycle has non-positive-definite Cartan form.

2. **Degree bound**: If a vertex has degree ≥ 4, the vector (2 at vertex, 1 at neighbors,
   0 elsewhere) gives Cartan form ≤ 0. So max degree ≤ 3.

3. **Tree classification**: A connected tree with max degree ≤ 3 is either:
   - A path (all degrees ≤ 2) → isomorphic to A_n
   - Has exactly one vertex of degree 3 with arms (p,q,r) → the arm lengths determine the type

4. **Arm length constraint**: For a branching tree T_{p,q,r}, positive definiteness requires
   1/(p+1) + 1/(q+1) + 1/(r+1) > 1. The solutions with p ≤ q ≤ r are:
   - (1,1,r) → D_{r+3}
   - (1,2,2) → E₆, (1,2,3) → E₇, (1,2,4) → E₈
-/

/-- The degree of vertex i in a 0-1 adjacency matrix. -/
noncomputable def vertexDegree {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => adj i j = 1)).card

/-- The number of edges (counted as half the sum of all adjacency entries) equals
    the sum of entries divided by 2 for a symmetric 0-1 adjacency matrix. -/
noncomputable def edgeCount {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (∑ i : Fin n, vertexDegree adj i) / 2

/-- Subgraph non-positive-definiteness: if a Dynkin diagram contains a subgraph
    (via injection φ) whose Cartan form has a non-trivial non-negative null vector,
    then we get a contradiction.

    The key idea: push forward v via φ to get w on Fin n. Since v ≥ 0 and adj ≥ adj_sub
    on the image, we have B_adj(w,w) ≤ B_sub(v,v) ≤ 0, contradicting positive definiteness. -/
lemma subgraph_contradiction {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj)
    (adj_sub : Matrix (Fin m) (Fin m) ℤ)
    (φ : Fin m ↪ Fin n)
    (hembed : ∀ i j, adj_sub i j ≤ adj (φ i) (φ j))
    (v : Fin m → ℤ) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne : v ≠ 0)
    (hv_null : dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) ≤ 0) :
    False := by
  obtain ⟨_hsymm, _hdiag, h01, _hconn, hpos⟩ := hD
  -- Push forward v to w on Fin n: w(φ(i)) = v(i), w(j) = 0 for j ∉ image(φ)
  -- We use the inverse of φ on its image
  set w : Fin n → ℤ := fun j =>
    if h : ∃ i, φ i = j then v h.choose else 0 with hw_def
  -- w is nonzero since v is nonzero
  have hw_ne : w ≠ 0 := by
    intro h
    apply hv_ne; ext i
    have hw_phi : w (φ i) = 0 := congr_fun h (φ i)
    simp only [w, show (∃ j, φ j = φ i) from ⟨i, rfl⟩, dite_true] at hw_phi
    have heq : (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose = i :=
      φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
    rw [heq] at hw_phi
    exact hw_phi
  -- B_adj(w,w) ≤ B_sub(v,v) ≤ 0
  have hadj_nonneg : ∀ i j, 0 ≤ adj i j := by
    intro i j; rcases h01 i j with h | h <;> omega
  -- First show B_adj(w,w) ≤ B_sub(v,v)
  -- B_adj(w,w) = Σ_{j,k} (2δ_{jk} - adj(j,k))·w(j)·w(k)
  -- Only terms with j,k ∈ image(φ) are nonzero (since w = 0 outside image)
  -- On image(φ): w(φ(i))·w(φ(j)) = v(i)·v(j)
  -- The 2δ terms are the same (φ injective)
  -- The adj terms: adj(φ(i),φ(j)) ≥ adj_sub(i,j) (from hembed + adj_sub 0-1)
  -- Since v(i)·v(j) ≥ 0: -adj(φ(i),φ(j))·v(i)·v(j) ≤ -adj_sub(i,j)·v(i)·v(j)
  -- Therefore B_adj(w,w) ≤ B_sub(v,v)
  -- w(φ(i)) = v(i) for all i
  have hw_phi : ∀ i, w (φ i) = v i := by
    intro i
    simp only [w, show (∃ j, φ j = φ i) from ⟨i, rfl⟩, dite_true]
    congr 1; exact φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
  -- w(j) = 0 for j ∉ image(φ)
  have hw_zero : ∀ j, (∀ i, φ i ≠ j) → w j = 0 := by
    intro j hj; simp only [w, show ¬∃ i, φ i = j from fun ⟨i, hi⟩ => hj i hi, dite_false]
  -- Helper: reindex sums from Fin n to Fin m since w vanishes outside image(φ)
  have sum_reindex : ∀ g : Fin n → ℤ, ∑ a : Fin n, w a * g a = ∑ i : Fin m, v i * g (φ i) := by
    intro g
    -- Split sum into image(φ) and its complement
    set S := Finset.univ.image φ with hS_def
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun a => a ∈ S) (f := fun a => w a * g a)
    rw [← hsplit]
    -- Complement sum is 0 (w vanishes outside image)
    have hcomp : ∑ a ∈ Finset.univ.filter (fun a => a ∉ S), w a * g a = 0 := by
      apply Finset.sum_eq_zero; intro a ha
      have ha' : a ∉ S := (Finset.mem_filter.mp ha).2
      have : w a = 0 := hw_zero a fun i hi =>
        ha' (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [this, zero_mul]
    rw [hcomp, add_zero]
    -- The image sum equals the reindexed sum via Finset.sum_image
    have hfilter_eq : Finset.univ.filter (· ∈ S) = S := by
      ext a; simp [S, Finset.mem_image]
    rw [hfilter_eq]
    rw [Finset.sum_image (fun i _ j _ h => φ.injective h)]
    apply Finset.sum_congr rfl; intro i _
    rw [hw_phi]
  have hle : dotProduct w ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) ≤
      dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) := by
    -- Proof strategy (sum reindexing + term-by-term comparison):
    -- Step 1: Since w vanishes outside image(φ), reindex B_adj(w,w) as:
    --   B_adj(w,w) = Σ_{i,j:Fin m} (2δ_{i,j} - adj(φ i, φ j)) · v(i) · v(j)
    -- (Use sum_reindex twice, once for outer and once for inner sum, plus φ.injective for δ)
    -- Step 2: Compare term-by-term with B_sub(v,v):
    --   Each difference term is (adj_sub(i,j) - adj(φ i, φ j)) · v(i) · v(j) ≤ 0
    --   because v(i)·v(j) ≥ 0 and adj(φ i, φ j) ≥ adj_sub(i,j)
    --   because adj_sub i j ≤ adj (φ i) (φ j) by hembed
    -- Rewrite LHS outer sum via sum_reindex
    simp only [dotProduct]
    rw [sum_reindex (fun a => ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) a)]
    -- Rewrite mulVec at φ i using sum_reindex on inner sum
    have inner : ∀ i : Fin m,
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) (φ i) =
        ∑ j : Fin m, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) (φ j) * v j := by
      intro i
      change ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) b * w b = _
      simp_rw [mul_comm ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) _) (w _)]
      rw [sum_reindex]
      congr 1; ext j; ring
    simp_rw [inner]
    -- Now both sides are double sums over Fin m; compare term-by-term
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hv_nonneg i)
    apply Finset.sum_le_sum; intro j _
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
    apply mul_le_mul_of_nonneg_right _ (hv_nonneg j)
    linarith [hembed i j]
  linarith [hpos w hw_ne]

/-- In a Dynkin diagram, vertex degree is at most 3.
    Proof: if deg(v) ≥ 4, embed the star K_{1,4} (center + 4 leaves) and use
    the null vector (2,1,1,1,1) which gives B = 0 on the star. -/
lemma dynkin_degree_le_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (i : Fin n) : vertexDegree adj i ≤ 3 := by
  by_contra hge; push_neg at hge
  obtain ⟨hsymm, hdiag, h01, _, hpos⟩ := hD
  -- Extract 4 neighbors
  set N := Finset.univ.filter (fun j => adj i j = 1) with hN_def
  have hcard : 4 ≤ N.card := hge
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hi_not_S : i ∉ S := by
    intro hi; have := (Finset.mem_filter.mp (hSsub hi)).2; linarith [hdiag i]
  -- Define x: 2 at center, 1 at 4 neighbors, 0 elsewhere
  set x : Fin n → ℤ := fun j => if j = i then 2 else if j ∈ S then 1 else 0
  have hx_ne : x ≠ 0 := by intro h; have := congr_fun h i; simp [x] at this
  -- Each term x(a)*mulVec(a) ≤ 0, so B(x,x) ≤ 0
  suffices hle : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 by
    linarith [hpos x hx_ne]
  -- Helper: adj(i,b)*x(b) is nonneg for all b
  have adj_x_nonneg : ∀ a b, 0 ≤ adj a b * x b := fun a b =>
    mul_nonneg (by rcases h01 a b with h | h <;> omega)
      (by simp only [x]; split_ifs <;> omega)
  -- Helper: for b ∈ S, adj(i,b)*x(b) = 1
  have adj_x_S : ∀ b, b ∈ S → adj i b * x b = 1 := by
    intro b hb
    have h1 : adj i b = 1 := (Finset.mem_filter.mp (hSsub hb)).2
    have h2 : x b = 1 := by
      have : b ≠ i := fun h => hi_not_S (h ▸ hb)
      simp [x, this, hb]
    rw [h1, h2, mul_one]
  -- Helper: Σ_b adj(i,b)*x(b) ≥ 4
  have sum_i_ge : (4 : ℤ) ≤ ∑ b, adj i b * x b := by
    have hS_sum : ∑ b ∈ S, adj i b * x b = 4 := by
      rw [show (4 : ℤ) = ∑ _b ∈ S, (1 : ℤ) from by simp [hScard]]
      exact Finset.sum_congr rfl (fun b hb => adj_x_S b hb)
    calc (4 : ℤ) = ∑ b ∈ S, adj i b * x b := hS_sum.symm
      _ ≤ ∑ b, adj i b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg i b)
  -- Helper: for a ∈ S, Σ_b adj(a,b)*x(b) ≥ 2 (from adj(a,i)*x(i) = 1*2)
  have sum_a_ge : ∀ a, a ∈ S → (2 : ℤ) ≤ ∑ b, adj a b * x b := by
    intro a ha
    have ha_adj_i : adj a i = 1 := by
      have := (Finset.mem_filter.mp (hSsub ha)).2; exact hsymm.apply i a ▸ this
    have hxi : x i = 2 := by simp [x]
    have : adj a i * x i = 2 := by rw [ha_adj_i, hxi]; ring
    calc (2 : ℤ) = adj a i * x i := this.symm
      _ = ∑ b ∈ ({i} : Finset (Fin n)), adj a b * x b := by simp
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg a b)
  -- Key: mulVec decomposes as 2*x(a) - Σ adj(a,b)*x(b)
  have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) a =
      2 * x a - ∑ b, adj a b * x b := by
    intro a; simp only [mulVec, dotProduct]
    rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * x b =
        ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * x b - adj a b * x b) from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * x b =
        ∑ b, if a = b then 2 * x b else 0 from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.one_apply]; split_ifs <;> simp <;> ring)]
    simp [Finset.sum_ite_eq']
  -- B(x,x) = Σ_a x(a) * ((2I-adj)x)(a), show each term ≤ 0
  apply Finset.sum_nonpos; intro a _
  rw [mulVec_eq]
  by_cases hai : a = i
  · -- a = i: x(i) = 2, Σ adj(i,b)*x(b) ≥ 4
    have hxa : x a = 2 := by simp [x, hai]
    rw [hxa]; linarith [hai ▸ sum_i_ge]
  · by_cases haS : a ∈ S
    · -- a ∈ S: x(a) = 1, Σ adj(a,b)*x(b) ≥ 2
      have hxa : x a = 1 := by
        simp only [x]; rw [if_neg hai, if_pos haS]
      rw [hxa]; linarith [sum_a_ge a haS]
    · -- a ∉ {i}∪S: x(a) = 0
      have : x a = 0 := by simp [x, hai, haS]
      rw [this]; simp

/-- In a Dynkin diagram, any cycle of length ≥ 3 would give a null vector for the Cartan form.
    Therefore Dynkin diagrams have no cycles, hence are trees. -/
lemma dynkin_no_cycle {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (cycle : List (Fin n)) (hlen : 3 ≤ cycle.length)
    (hnodup : cycle.Nodup)
    (hedges : ∀ k, (h : k + 1 < cycle.length) →
      adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1)
    (hclose : adj (cycle.getLast (by intro h; simp [h] at hlen)) (cycle.get ⟨0, by omega⟩) = 1) :
    False := by
  obtain ⟨hsymm, _hdiag, h01, _hconn, hpos⟩ := hD
  -- The all-ones vector on the cycle has B(x,x) = 2k - 2k = 0 (minus extra edges)
  -- where k = cycle.length
  set x : Fin n → ℤ := fun j => if j ∈ cycle then 1 else 0
  have hx_ne : x ≠ 0 := by
    intro h
    have hmem : cycle[0]'(by omega) ∈ cycle := List.getElem_mem ..
    have hval := congr_fun h (cycle[0]'(by omega))
    simp only [x, hmem, ite_true, Pi.zero_apply] at hval
    exact absurd hval one_ne_zero
  -- Use subgraph_contradiction: embed the cycle as a subgraph with null vector (1,...,1)
  set m := cycle.length
  -- Cycle adjacency matrix on Fin m
  let adj_sub : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) ∨
       (i.val = 0 ∧ j.val = m - 1) ∨ (j.val = 0 ∧ i.val = m - 1)
    then 1 else 0
  -- Embedding: cycle positions → graph vertices
  have φ_inj : Function.Injective (fun i : Fin m => cycle.get i) :=
    hnodup.injective_get
  let φ : Fin m ↪ Fin n := ⟨fun i => cycle.get i, φ_inj⟩
  -- Rewrite hclose using get
  have hclose' : adj (cycle.get ⟨m - 1, by omega⟩) (cycle.get ⟨0, by omega⟩) = 1 := by
    convert hclose using 2; symm; exact List.getLast_eq_getElem _
  -- Embedding condition: cycle edges are subgraph edges
  have hembed : ∀ i j, adj_sub i j ≤ adj (φ i) (φ j) := by
    intro i j; simp only [adj_sub, φ]
    split_ifs with h
    · -- adj_sub = 1: show adj(cycle[i], cycle[j]) ≥ 1
      show 1 ≤ adj (cycle.get i) (cycle.get j)
      suffices adj (cycle.get i) (cycle.get j) = 1 by omega
      rcases h with h | h | ⟨hi, hj⟩ | ⟨hj, hi⟩
      · -- i.val + 1 = j.val: consecutive vertices
        have key := hedges i.val (by omega)
        have : cycle.get j = cycle.get (⟨i.val + 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext h.symm)
        rw [this]; exact key
      · -- j.val + 1 = i.val: reverse consecutive
        have key := hedges j.val (by omega)
        have : cycle.get i = cycle.get (⟨j.val + 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext h.symm)
        rw [hsymm.apply, this]; exact key
      · -- i = 0, j = m-1: closing edge (reversed)
        have h1 : cycle.get i = cycle.get (⟨0, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hi)
        have h2 : cycle.get j = cycle.get (⟨m - 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hj)
        rw [hsymm.apply, h1, h2]; exact hclose'
      · -- j = 0, i = m-1: closing edge
        have h1 : cycle.get i = cycle.get (⟨m - 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hi)
        have h2 : cycle.get j = cycle.get (⟨0, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hj)
        rw [h1, h2]; exact hclose'
    · -- adj_sub = 0: trivially 0 ≤ adj(...)
      have : adj (φ i) (φ j) = 0 ∨ adj (φ i) (φ j) = 1 := h01 (φ i) (φ j)
      show 0 ≤ adj (φ i) (φ j)
      rcases this with h | h <;> simp [h]
  -- Null vector: all ones
  let v : Fin m → ℤ := fun _ => 1
  have hv_nonneg : ∀ i, 0 ≤ v i := fun _ => by show (0 : ℤ) ≤ 1; omega
  have hv_ne : v ≠ 0 := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [v] at this
  -- B_sub(v,v) ≤ 0: each vertex has degree 2 in the cycle, so B(1,...,1) = 0
  -- Each vertex in a cycle has exactly 2 neighbors, so B(1,...,1) = Σ(2-2) = 0
  have hdeg2 : ∀ i : Fin m, ∑ j : Fin m, adj_sub i j = 2 := by
    intro i
    -- adj_sub i j = 1 iff j is a cycle-neighbor of i; each vertex has exactly 2 neighbors
    -- The condition (from adj_sub definition) uses i.val and j.val (ℕ comparisons)
    -- After simp [adj_sub], the sum has if-then-else over ℕ conditions
    have h01_sub : ∀ j, adj_sub i j = 0 ∨ adj_sub i j = 1 := by
      intro j; simp only [adj_sub]; split_ifs <;> omega
    -- Convert to cardinality of the neighbor set
    rw [show ∑ j, adj_sub i j = ↑(Finset.univ.filter (fun j : Fin m => adj_sub i j = 1)).card from by
      rw [show ∑ j, adj_sub i j = ∑ j, if adj_sub i j = 1 then (1 : ℤ) else 0 from
        Finset.sum_congr rfl (fun j _ => by rcases h01_sub j with h | h <;> simp [h])]
      push_cast; simp [Finset.sum_boole]]
    -- Show the neighbor set has exactly 2 elements
    -- Define the two neighbors
    set nxt : Fin m := ⟨if i.val + 1 < m then i.val + 1 else 0, by split_ifs <;> omega⟩
    set prv : Fin m := ⟨if i.val = 0 then m - 1 else i.val - 1, by split_ifs <;> omega⟩
    have hne : nxt ≠ prv := by
      simp only [nxt, prv, ne_eq, Fin.ext_iff, Fin.val_mk]; split_ifs <;> omega
    suffices Finset.univ.filter (fun j : Fin m => adj_sub i j = 1) = {nxt, prv} by
      rw [this, Finset.card_pair hne]; norm_cast
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · -- adj_sub i j = 1 → j = nxt ∨ j = prv
      intro h; simp only [adj_sub] at h
      split_ifs at h with hcond
      · rcases hcond with hc | hc | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
        · left; exact Fin.ext (by simp only [nxt, Fin.val_mk]; split_ifs <;> omega)
        · right; exact Fin.ext (by simp only [prv, Fin.val_mk]; split_ifs <;> omega)
        · right; exact Fin.ext (by simp only [prv, Fin.val_mk]; split_ifs <;> omega)
        · left; exact Fin.ext (by simp only [nxt, Fin.val_mk]; split_ifs <;> omega)
      · omega -- h : 0 = 1 contradiction
    · -- j = nxt ∨ j = prv → adj_sub i j = 1
      rintro (hj | hj) <;> subst hj <;> simp only [adj_sub, nxt, prv, Fin.val_mk] <;>
        split_ifs <;> omega
  have hv_null : dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) ≤ 0 := by
    suffices h0 : (2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v = 0 by
      rw [h0]; simp [dotProduct]
    ext i; simp only [mulVec, dotProduct, v, mul_one, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Pi.zero_apply]
    -- Convert nsmul to concrete ℤ values
    simp_rw [show ∀ j : Fin m, (2 : ℕ) • (if i = j then (1 : ℤ) else 0) =
      if i = j then (2 : ℤ) else 0 from fun j => by split_ifs <;> simp]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hdeg2 i]
  exact subgraph_contradiction ⟨hsymm, _hdiag, h01, _hconn, hpos⟩ adj_sub φ hembed v hv_nonneg hv_ne hv_null

/-- For a 0-1 adjacency matrix, the sum of row entries equals the vertex degree. -/
lemma adj_sum_eq_degree {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1) (a : Fin n) :
    ∑ b : Fin n, adj a b = ↑(vertexDegree adj a) := by
  simp only [vertexDegree]
  rw [show ∑ b : Fin n, adj a b =
      ∑ b : Fin n, (if adj a b = 1 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun b _ => by rcases h01 a b with h | h <;> simp [h])]
  simp [Finset.sum_boole]

/-- A Dynkin diagram on n vertices has exactly n-1 edges (it's a tree).
    This follows from no-cycles + connectivity. -/
lemma list_path_reachable {n : ℕ} (G : SimpleGraph (Fin n))
    (path : List (Fin n)) (u v : Fin n)
    (hhead : path.head? = some u) (hlast : path.getLast? = some v)
    (hedges : ∀ k, (h : k + 1 < path.length) →
      G.Adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩)) :
    G.Reachable u v := by
  induction path generalizing u v with
  | nil => exact absurd hhead (by simp)
  | cons a rest ih =>
    have ha : a = u := by simpa using hhead
    cases rest with
    | nil =>
      have hv : a = v := by simpa using hlast
      rw [← ha, hv]
    | cons b rest' =>
      have hadj : G.Adj a b := hedges 0 (by simp)
      rw [← ha]
      exact hadj.reachable.trans <| ih b v (by simp)
        (by simpa [List.getLast?_cons_cons] using hlast)
        (fun k hk => hedges (k + 1) (by simp at hk ⊢; omega))

lemma dynkin_edge_count {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) : edgeCount adj = n - 1 := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  -- Define the SimpleGraph corresponding to the adjacency matrix
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := fun {i j} h => by change adj j i = 1; rw [hsymm.apply i j]; exact h
      loopless := ⟨fun i h => by change adj i i = 1 at h; linarith [hdiag i]⟩ }
  letI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  -- Show G is connected
  have hG_conn : G.Connected := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact ⟨fun u v => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
      exact list_path_reachable G path u v hhead hlast hedges⟩
  -- Upper bound: edgeCount ≤ n - 1 from positive definiteness
  have h_upper : edgeCount adj ≤ n - 1 := by
    -- B(1,...,1) > 0 implies ∑ deg < 2n
    set x : Fin n → ℤ := fun _ => 1
    have hx_ne : x ≠ 0 := by intro h; have := congr_fun h ⟨0, by omega⟩; simp [x] at this
    -- mulVec decomposition (same pattern as dynkin_has_endpoint)
    have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) a =
        2 * x a - ∑ b, adj a b * x b := by
      intro a; simp only [mulVec, dotProduct]
      rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * x b =
          ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * x b - adj a b * x b) from
        Finset.sum_congr rfl (fun b _ => by
          simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)]
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * x b =
          ∑ b, if a = b then 2 * x b else 0 from
        Finset.sum_congr rfl (fun b _ => by
          simp only [Matrix.one_apply]; split_ifs <;> simp <;> ring)]
      simp [Finset.sum_ite_eq']
    -- B(1,...,1) = ∑_a (2 - deg(a))
    have hBpos := hpos x hx_ne
    simp only [dotProduct, show ∀ b, x b = (1 : ℤ) from fun _ => rfl, one_mul,
      mulVec_eq, mul_one] at hBpos
    -- hBpos : 0 < ∑ a, (2 - ∑ b, adj a b)
    -- This means ∑ deg < 2n
    have hsum_lt : ∑ i : Fin n, vertexDegree adj i < 2 * n := by
      have hsum_ineq : (0 : ℤ) < ∑ a : Fin n, (2 - ∑ b, adj a b) := hBpos
      have : (↑(∑ i : Fin n, vertexDegree adj i) : ℤ) < 2 * ↑n := by
        have h1 : ∑ a : Fin n, (2 - ∑ b : Fin n, adj a b) =
            2 * ↑n - ∑ a, ∑ b, adj a b := by
          rw [Finset.sum_sub_distrib]; simp [Finset.card_fin]; ring
        have h2 : (∑ i : Fin n, (vertexDegree adj i : ℤ)) = ∑ i, ∑ j, adj i j := by
          congr 1; ext i; exact (adj_sum_eq_degree h01 i).symm
        push_cast; linarith
      exact_mod_cast this
    unfold edgeCount; omega
  -- Lower bound: n - 1 ≤ edgeCount from connectivity
  have h_lower : n - 1 ≤ edgeCount adj := by
    have h1 := hG_conn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin] at h1
    -- Relate Nat.card G.edgeSet to edgeCount
    have hdeg_eq : ∀ v, G.degree v = vertexDegree adj v := by
      intro v; simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        SimpleGraph.neighborSet, Set.toFinset_setOf]
      congr 1
    have h_sum : ∑ v, G.degree v = ∑ v, vertexDegree adj v := by
      congr 1; ext v; exact hdeg_eq v
    have h_handshake := G.sum_degrees_eq_twice_card_edges
    have h_eq : G.edgeFinset.card = edgeCount adj := by
      unfold edgeCount; rw [← h_sum, h_handshake]; omega
    rw [show Nat.card G.edgeSet = edgeCount adj from by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]; exact h_eq] at h1
    omega
  omega

/-- In a Dynkin diagram with all degrees ≤ 2, there exists a vertex of degree ≤ 1 (endpoint).
    Proof: if all degrees = 2 then the all-ones vector has B(x,x) = 0, contradicting pos-def. -/
lemma dynkin_has_endpoint {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) (hpath : ∀ i, vertexDegree adj i ≤ 2) :
    ∃ v, vertexDegree adj v ≤ 1 := by
  by_contra h; push_neg at h
  obtain ⟨_, hdiag, h01, _, hpos⟩ := hD
  have hdeg2 : ∀ i, vertexDegree adj i = 2 := fun i => le_antisymm (hpath i) (h i)
  set x : Fin n → ℤ := fun _ => 1
  have hx_ne : x ≠ 0 := by intro h; have := congr_fun h ⟨0, by omega⟩; simp [x] at this
  -- B(x,x) = Σ_a (2 - degree(a)) = Σ_a 0 = 0, contradicting hpos > 0
  -- mulVec decomposition: mulVec(a) = 2*x(a) - Σ adj(a,b)*x(b)
  have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) a =
      2 * x a - ∑ b, adj a b * x b := by
    intro a; simp only [mulVec, dotProduct]
    rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * x b =
        ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * x b - adj a b * x b) from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * x b =
        ∑ b, if a = b then 2 * x b else 0 from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.one_apply]; split_ifs <;> simp <;> ring)]
    simp [Finset.sum_ite_eq']
  have hB_le : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos; intro a _
    simp only [show ∀ b, x b = (1 : ℤ) from fun _ => rfl, mul_one, one_mul, mulVec_eq]
    -- Goal: 2 - Σ adj(a,b) ≤ 0, i.e., 2 ≤ Σ adj(a,b)
    linarith [show (2 : ℤ) ≤ ∑ b, adj a b from by
      rw [adj_sum_eq_degree h01 a, hdeg2 a]; norm_cast]
  linarith [hpos x hx_ne]

/-- Given a connected graph with all degrees ≤ 2 and an endpoint v₀,
    construct a walk visiting all n vertices in order. The walk is:
    walk(0) = v₀, walk(k+1) = the unique neighbor of walk(k) not yet visited.
    Returns: an injective walk function, proof it covers all vertices,
    and proof consecutive vertices are adjacent. -/
lemma path_walk_construction {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hpath : ∀ i, vertexDegree adj i ≤ 2) (v₀ : Fin n)
    (hv₀ : vertexDegree adj v₀ ≤ 1) :
    ∃ σ : Fin n ≃ Fin n,
      σ ⟨0, by omega⟩ = v₀ ∧
      (∀ (k : Fin n) (hk : k.val + 1 < n), adj (σ k) (σ ⟨k.val + 1, hk⟩) = 1) ∧
      (∀ i j, adj (σ i) (σ j) = 1 → (i.val + 1 = j.val ∨ j.val + 1 = i.val)) := by
  -- Proof by induction on n, removing the leaf v₀ at each step.
  revert adj hD hn hpath v₀ hv₀
  induction n with
  | zero => intro _ _ hn; omega
  | succ k ih =>
    intro adj hD hn hpath v₀ hv₀
    obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
    -- n = 1: trivial
    by_cases hk0 : k = 0
    · subst hk0
      have huniq : ∀ (a : Fin 1), a = ⟨0, by omega⟩ := fun a => Fin.ext (by omega)
      refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
      · simp [huniq v₀]
      · intro i hk; exact absurd hk (by omega)
      · intro i j hadj_ij
        have hi := huniq i; have hj := huniq j
        rw [hi, hj, hdiag] at hadj_ij; omega
    · -- n = k + 1 ≥ 2
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      -- v₀ has degree exactly 1 (connected + degree ≤ 1 + n ≥ 2)
      have hv₀_deg1 : vertexDegree adj v₀ = 1 := by
        apply le_antisymm hv₀
        -- Degree ≥ 1: pick j ≠ v₀, get path, first edge gives neighbor
        obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), j ≠ v₀ :=
          ⟨⟨if v₀.val = 0 then 1 else 0, by split_ifs <;> omega⟩,
           fun h => by simp only [Fin.ext_iff] at h; split_ifs at h <;> omega⟩
        obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ j
        have hlen : 2 ≤ path.length := by
          rcases path with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp at hhead
          · -- path = [a], so head = some a = some v₀ and last = some a = some j
            simp only [List.head?, List.getLast?_singleton] at hhead hlast
            have ha := Option.some.inj hhead
            have hb := Option.some.inj hlast
            exact absurd (ha ▸ hb.symm) hj
          · simp
        -- Extract first edge
        have hadj_01 := hedges 0 (by omega)
        have hp0 : path.get ⟨0, by omega⟩ = v₀ := by
          rcases path with _ | ⟨a, rest⟩
          · simp at hhead
          · exact Option.some.inj hhead
        rw [hp0] at hadj_01
        change 1 ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card
        exact Finset.one_le_card.mpr ⟨path.get ⟨1, by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_01⟩⟩
      -- Get unique neighbor v₁
      have hv₁_nonempty : (Finset.univ.filter (fun j => adj v₀ j = 1)).Nonempty :=
        Finset.card_pos.mp (by change 0 < vertexDegree adj v₀; omega)
      obtain ⟨v₁, hv₁_mem_filter⟩ := hv₁_nonempty
      have hv₁_adj : adj v₀ v₁ = 1 := (Finset.mem_filter.mp hv₁_mem_filter).2
      have hv₁_unique : ∀ w, adj v₀ w = 1 → w = v₁ := by
        intro w hw
        by_contra hne
        -- Both v₁ and w are distinct neighbors, so degree ≥ 2
        have : 2 ≤ vertexDegree adj v₀ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card
          have hw_mem : w ∈ Finset.univ.filter (fun j => adj v₀ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({v₁, w} : Finset _).card := by
                rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card :=
                Finset.card_le_card (fun x hx => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact hv₁_mem_filter
                  · exact hw_mem)
        omega
      have hv₁_ne : v₁ ≠ v₀ := by
        intro h; subst h; rw [hdiag] at hv₁_adj; omega
      -- Define reduced graph on Fin k by removing v₀
      set adj' : Matrix (Fin k) (Fin k) ℤ :=
        fun i j => adj (v₀.succAbove i) (v₀.succAbove j) with hadj'_def
      -- Reduced graph is a Dynkin diagram
      have hD' : IsDynkinDiagram k adj' := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
        · intro i; exact hdiag _
        · intro i j; exact h01 _ _
        · -- Connectivity: removing a leaf preserves connectivity
          -- Build SimpleGraph from adj
          let G : SimpleGraph (Fin (k + 1)) :=
            { Adj := fun i j => adj i j = 1
              symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
              loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
          haveI : DecidableRel G.Adj :=
            fun i j => show Decidable (adj i j = 1) from inferInstance
          -- G is connected
          have hG_conn : G.Connected := by
            constructor
            · intro u v
              obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
              suffices h : ∀ (l : List (Fin (k + 1))) (a b : Fin (k + 1)),
                  l.head? = some a → l.getLast? = some b →
                  (∀ m, (hm : m + 1 < l.length) →
                    adj (l.get ⟨m, by omega⟩) (l.get ⟨m + 1, hm⟩) = 1) →
                  G.Reachable a b from h path u v hhead hlast hedges
              intro l; induction l with
              | nil => intro a _ ha; simp at ha
              | cons x t ih =>
                intro a b ha hb hedges'
                simp at ha; subst ha
                cases t with
                | nil => simp at hb; subst hb; exact SimpleGraph.Reachable.refl _
                | cons y s =>
                  have hxy : G.Adj x y := hedges' 0 (by simp)
                  exact hxy.reachable.trans
                    (ih y b (by simp) hb (fun m hm => hedges' (m + 1)
                      (by simp only [List.length_cons] at hm ⊢; omega)))
          -- G has degree 1 at v₀
          have hG_deg : G.degree v₀ = 1 := by
            unfold SimpleGraph.degree
            have heq : G.neighborFinset v₀ = Finset.univ.filter (adj v₀ · = 1) := by
              ext j
              simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
                Finset.mem_univ, true_and]
              exact ⟨fun h => h, fun h => h⟩
            rw [heq]; unfold vertexDegree at hv₀_deg1; convert hv₀_deg1
          -- Apply Mathlib: removing v₀ preserves connectivity
          have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
          -- Convert: G.induce {v₀}ᶜ connectivity → adj' connectivity
          intro u w
          have hu_ne : v₀.succAbove u ≠ v₀ := Fin.succAbove_ne v₀ u
          have hw_ne : v₀.succAbove w ≠ v₀ := Fin.succAbove_ne v₀ w
          have hu_mem : v₀.succAbove u ∈ ({v₀}ᶜ : Set (Fin (k + 1))) :=
            Set.mem_compl_singleton_iff.mpr hu_ne
          have hw_mem : v₀.succAbove w ∈ ({v₀}ᶜ : Set (Fin (k + 1))) :=
            Set.mem_compl_singleton_iff.mpr hw_ne
          obtain ⟨walk⟩ := hG'.preconnected ⟨v₀.succAbove u, hu_mem⟩ ⟨v₀.succAbove w, hw_mem⟩
          -- Convert walk to List (Fin k) path by induction on the walk
          -- Helper: map vertex in {v₀}ᶜ to Fin k via succAbove inverse
          let toFink : ↥({v₀}ᶜ : Set (Fin (k + 1))) → Fin k :=
            fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
              (Set.mem_compl_singleton_iff.mp hv)).choose
          have htoFink_spec : ∀ (x : ↥({v₀}ᶜ : Set (Fin (k + 1)))),
              v₀.succAbove (toFink x) = x.val :=
            fun ⟨v, hv⟩ => (Fin.exists_succAbove_eq
              (Set.mem_compl_singleton_iff.mp hv)).choose_spec
          have htoFink_adj : ∀ (x y : ↥({v₀}ᶜ : Set (Fin (k + 1)))),
              (G.induce ({v₀}ᶜ : Set _)).Adj x y →
              adj' (toFink x) (toFink y) = 1 := by
            intro x y hadj_xy
            simp only [hadj'_def, SimpleGraph.induce_adj] at hadj_xy ⊢
            rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
          -- Build path by induction on the walk
          suffices h_walk : ∀ (a b : ↥({v₀}ᶜ : Set (Fin (k+1))))
              (w' : (G.induce ({v₀}ᶜ : Set _)).Walk a b),
            ∃ path : List (Fin k),
              path.head? = some (toFink a) ∧
              path.getLast? = some (toFink b) ∧
              ∀ m, (hm : m + 1 < path.length) →
                adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
            obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
            refine ⟨path, ?_, ?_, hedges⟩
            · convert hhead using 2
              exact (Fin.succAbove_right_injective
                (htoFink_spec ⟨v₀.succAbove u, hu_mem⟩)).symm
            · convert hlast using 2
              exact (Fin.succAbove_right_injective
                (htoFink_spec ⟨v₀.succAbove w, hw_mem⟩)).symm
          intro a b w'
          induction w' with
          | nil =>
            exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
          | @cons c d _ hadj_edge rest ih =>
            obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
            refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
            · -- getLast?
              cases path_rest with
              | nil =>
                simp at hhead_rest hlast_rest ⊢
              | cons y ys =>
                simp only [List.getLast?_cons_cons]
                exact hlast_rest
            · -- Consecutive adjacency
              intro m hm
              match m with
              | 0 =>
                simp only [List.get_eq_getElem, List.getElem_cons_zero,
                  List.getElem_cons_succ]
                -- Goal: adj' (toFink c) path_rest[0] = 1
                -- path_rest is nonempty and path_rest[0] = toFink d
                have h0 : 0 < path_rest.length := by
                  simp only [List.length_cons] at hm; omega
                have hd_eq : path_rest[0] = toFink d := by
                  cases path_rest with
                  | nil => simp at h0
                  | cons y ys =>
                    simp only [List.head?, Option.some.injEq] at hhead_rest
                    simp only [List.getElem_cons_zero]
                    exact hhead_rest
                rw [hd_eq]
                exact htoFink_adj c d hadj_edge
              | m' + 1 =>
                simp only [List.get_eq_getElem, List.getElem_cons_succ]
                exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)
        · -- Positive definiteness: principal submatrix of pos-def
          intro x hx
          set x' : Fin (k + 1) → ℤ := fun a =>
            if h : a = v₀ then 0 else x (Fin.exists_succAbove_eq h).choose
          have hx'_v₀ : x' v₀ = 0 := by simp [x']
          have hx'_sa : ∀ i, x' (v₀.succAbove i) = x i := by
            intro i; simp only [x']
            rw [dif_neg (Fin.succAbove_ne v₀ i)]; congr 1
            exact Fin.succAbove_right_injective
              (Fin.exists_succAbove_eq (Fin.succAbove_ne v₀ i)).choose_spec
          have hx'_ne : x' ≠ 0 := by
            intro heq; apply hx; ext b
            have := congr_fun heq (v₀.succAbove b)
            rw [hx'_sa, Pi.zero_apply] at this; exact this
          have hB_eq : dotProduct x' ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x') =
              dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj').mulVec x) := by
            simp only [dotProduct, mulVec]
            conv_lhs => rw [Fin.sum_univ_succAbove _ v₀]
            simp only [hx'_v₀, zero_mul, zero_add]
            congr 1; ext i; rw [hx'_sa]; congr 1
            conv_lhs => rw [Fin.sum_univ_succAbove _ v₀]
            simp only [hx'_v₀, mul_zero, zero_add]
            congr 1; ext j; rw [hx'_sa]; congr 1
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
              Fin.succAbove_right_inj]
          linarith [hpos x' hx'_ne]
      -- Degree bounds for adj'
      have hpath' : ∀ i, vertexDegree adj' i ≤ 2 := by
        intro i
        -- Degree in subgraph ≤ degree in parent graph (injection via succAbove)
        unfold vertexDegree
        have h_image : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image v₀.succAbove)
            ⊆ Finset.univ.filter (fun j : Fin (k + 1) => adj (v₀.succAbove i) j = 1) := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          obtain ⟨y, hy, rfl⟩ := hx
          exact hy
        have h_card := Finset.card_le_card h_image
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
        have := hpath (v₀.succAbove i)
        unfold vertexDegree at this
        linarith
      -- Find v₁' (preimage of v₁ under succAbove)
      obtain ⟨v₁', hv₁'⟩ := Fin.exists_succAbove_eq hv₁_ne
      -- v₁' is an endpoint in adj' (degree ≤ 1)
      have hv₁'_deg : vertexDegree adj' v₁' ≤ 1 := by
        -- v₁ has degree ≤ 2 in adj. Its neighbor set in adj includes v₀.
        -- Removing v₀ drops one neighbor, so degree in adj' ≤ 1.
        unfold vertexDegree
        -- Image of adj' neighbors under succAbove ⊆ (adj neighbors of v₁) \ {v₀}
        have h_image : ((Finset.univ.filter (fun j : Fin k => adj' v₁' j = 1)).image v₀.succAbove)
            ⊆ (Finset.univ.filter (fun j : Fin (k + 1) => adj v₁ j = 1)).erase v₀ := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne v₀ y, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hv₁']; exact hy
        have h_card := Finset.card_le_card h_image
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
        have hv₀_mem : v₀ ∈ Finset.univ.filter (fun j : Fin (k + 1) => adj v₁ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply v₀ v₁ ▸ hv₁_adj⟩
        rw [Finset.card_erase_of_mem hv₀_mem] at h_card
        have := hpath v₁; unfold vertexDegree at this
        omega
      -- Apply induction hypothesis
      obtain ⟨σ', hσ'0, hσ'_fwd, hσ'_only⟩ := ih hD' (by omega) hpath' v₁' hv₁'_deg
      -- Construct σ : Fin (k+1) ≃ Fin (k+1) from σ' by prepending v₀
      -- σ(0) = v₀, σ(i+1) = v₀.succAbove(σ'(i))
      set f : Fin (k + 1) → Fin (k + 1) :=
        Fin.cons v₀ (v₀.succAbove ∘ σ')
      have hf0 : f (0 : Fin (k + 1)) = v₀ := by simp [f]
      have hf_succ : ∀ i : Fin k, f i.succ = v₀.succAbove (σ' i) := by
        intro i; simp [f]
      have hf_inj : Function.Injective f := by
        intro a b hab
        rcases Fin.eq_zero_or_eq_succ a with ha | ⟨a', rfl⟩
        · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
          · exact ha.trans hb.symm
          · simp only [ha, f, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at hab
            exact absurd hab.symm (Fin.succAbove_ne v₀ _)
        · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
          · simp only [hb, f, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at hab
            exact absurd hab (Fin.succAbove_ne v₀ _)
          · simp only [f, Fin.cons_succ, Function.comp_apply] at hab
            exact congr_arg _ (σ'.injective (Fin.succAbove_right_injective hab))
      set σ : Fin (k + 1) ≃ Fin (k + 1) :=
        Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
      refine ⟨σ, ?_, ?_, ?_⟩
      · -- σ(0) = v₀
        exact hf0
      · -- Consecutive adjacency: adj(σ(m))(σ(m+1)) = 1
        intro m hm
        change adj (f m) (f ⟨m.val + 1, hm⟩) = 1
        rcases Fin.eq_zero_or_eq_succ m with hm0 | ⟨m', rfl⟩
        · -- m = 0: adj(v₀)(succAbove(σ'(0))) = adj(v₀)(v₁)
          subst hm0
          simp only [f, Fin.cons_zero]
          conv_lhs => rw [show (⟨(0 : Fin (k + 1)).val + 1, hm⟩ : Fin (k + 1)) =
            (⟨0, by omega⟩ : Fin k).succ from by ext; simp]
          simp only [Fin.cons_succ, Function.comp_apply, hσ'0, hv₁']
          exact hv₁_adj
        · -- m = m'+1: adj(succAbove(σ'(m')))(succAbove(σ'(m'+1)))
          simp only [f, Fin.cons_succ, Function.comp_apply]
          have hm'_lt : m'.val + 1 < k := by
            have : m'.succ.val = m'.val + 1 := rfl; omega
          have : (⟨m'.succ.val + 1, hm⟩ : Fin (k + 1)) =
              (⟨m'.val + 1, hm'_lt⟩ : Fin k).succ := by exact Fin.ext rfl
          conv_lhs => rw [this]
          simp only [Fin.cons_succ, Function.comp_apply]
          exact hσ'_fwd m' (by omega)
      · -- Non-adjacency: adj(σ(i))(σ(j)) = 1 → i+1=j ∨ j+1=i
        intro i j hadj_ij
        change adj (f i) (f j) = 1 at hadj_ij
        rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', rfl⟩
        · -- i = 0: adj(v₀)(f j) = 1, so f j = v₁
          rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', rfl⟩
          · -- j = 0: adj(v₀)(v₀) = 0 ≠ 1, contradiction
            simp only [hi, hj, f, Fin.cons_zero, hdiag] at hadj_ij
            omega
          · -- j = j'+1: adj(v₀)(succAbove(σ'(j'))) = 1
            simp only [hi, f, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at hadj_ij
            have : v₀.succAbove (σ' j') = v₁ := hv₁_unique _ hadj_ij
            have : σ' j' = v₁' := Fin.succAbove_right_injective (this.trans hv₁'.symm)
            have : j' = ⟨0, by omega⟩ := σ'.injective (this.trans hσ'0.symm)
            left; subst hi; simp [this]
        · rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', rfl⟩
          · -- j = 0: adj(succAbove(σ'(i')))(v₀) = 1
            simp only [hj, f, Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at hadj_ij
            have : v₀.succAbove (σ' i') = v₁ :=
              hv₁_unique _ ((hsymm.apply _ _).trans hadj_ij)
            have : σ' i' = v₁' := Fin.succAbove_right_injective (this.trans hv₁'.symm)
            have : i' = ⟨0, by omega⟩ := σ'.injective (this.trans hσ'0.symm)
            right; subst hj; simp [this]
          · -- Both ≥ 1: use hσ'_only
            simp only [f, Fin.cons_succ, Function.comp_apply] at hadj_ij
            rcases hσ'_only i' j' hadj_ij with h | h
            · left; simp [Fin.val_succ]; omega
            · right; simp [Fin.val_succ]; omega

lemma path_iso_An {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hpath : ∀ i, vertexDegree adj i ≤ 2)
    : ∃ σ : Fin n ≃ Fin n, ∀ i j, adj (σ i) (σ j) = DynkinType.adj (.A n hn) i j := by
  obtain ⟨v₀, hv₀⟩ := dynkin_has_endpoint hD hn hpath
  obtain ⟨σ, _, hσ_fwd, hσ_only⟩ := path_walk_construction hD hn hpath v₀ hv₀
  obtain ⟨hsymm, _, h01, _, _⟩ := hD
  refine ⟨σ, fun i j => ?_⟩
  -- Unfold DynkinType.adj for A_n
  change adj (σ i) (σ j) = if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  -- i j : Fin (DynkinType.A n hn).rank = Fin n definitionally
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  split_ifs with h
  · rcases h with h_fwd | h_bwd
    · have hk : i.val + 1 < n := by linarith
      have heq : j = ⟨i.val + 1, by linarith⟩ := by ext; exact h_fwd.symm
      rw [heq]; exact hσ_fwd i hk
    · have hk : j.val + 1 < n := by linarith
      have heq : i = ⟨j.val + 1, by linarith⟩ := by ext; exact h_bwd.symm
      rw [heq, hsymm.apply]; exact hσ_fwd j hk
  · push_neg at h
    rcases h01 (σ i) (σ j) with h0 | h1
    · exact h0
    · exfalso
      rcases hσ_only i j h1 with h2 | h2
      · exact h.1 h2
      · exact h.2 h2

/-- The reciprocal sum constraint on arm lengths of a Dynkin diagram with a branch vertex:
    the only solutions of 1/(p+1) + 1/(q+1) + 1/(r+1) > 1 with 1 ≤ p ≤ q ≤ r are
    (1,1,r) for r ≥ 1, (1,2,2), (1,2,3), and (1,2,4). -/
lemma arm_length_solutions (p q r : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hrecip : (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1) >
              (p + 1) * (q + 1) * (r + 1)) :
    (p = 1 ∧ q = 1) ∨ (p = 1 ∧ q = 2 ∧ r = 2) ∨
    (p = 1 ∧ q = 2 ∧ r = 3) ∨ (p = 1 ∧ q = 2 ∧ r = 4) := by
  -- Upper bound on p: if p ≥ 2, then p+1 ≥ 3 and q+1 ≥ 3, r+1 ≥ 3,
  -- so 1/(p+1) + 1/(q+1) + 1/(r+1) ≤ 1/3 + 1/3 + 1/3 = 1, contradicting > 1.
  -- Formally: product(p+1)(q+1)(r+1) ≥ sum of pairwise products.
  have hp1 : p = 1 := by
    by_contra hp_ne
    have hp2 : 2 ≤ p := by omega
    have hq2 : 2 ≤ q := le_trans hp2 hpq
    have hr2 : 2 ≤ r := le_trans hq2 hqr
    -- Key: p*q*r ≥ p + q + r + 2 for p,q,r ≥ 2
    have h1 : 2 * (q * r) ≤ p * (q * r) :=
      Nat.mul_le_mul_right _ hp2
    have h2 : 2 * (2 * r) ≤ 2 * (q * r) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hq2)
    have h3 : p + q ≤ 2 * r := by linarith
    -- (p+1)(q+1)(r+1) = pqr + pq + pr + qr + p + q + r + 1
    -- sum = qr + q + r + 1 + pr + p + r + 1 + pq + p + q + 1
    -- diff = pqr - p - q - r - 2 ≥ 4r - p - q - r - 2 = 3r - (p+q) - 2 ≥ r - 2 ≥ 0
    nlinarith
  subst hp1
  -- Now p = 1. Upper bound on q: if q ≥ 3 then 1/2 + 1/4 + 1/(r+1) ≤ 1 (since r ≥ q ≥ 3).
  have hq_le : q ≤ 2 := by
    by_contra hq_big; push_neg at hq_big
    have hq3 : 3 ≤ q := by omega
    have hr3 : 3 ≤ r := le_trans hq3 hqr
    nlinarith
  interval_cases q
  · -- q = 1: any r ≥ 1 works (1/2 + 1/2 + 1/(r+1) > 1 always)
    left; exact ⟨rfl, rfl⟩
  · -- q = 2: 1/2 + 1/3 + 1/(r+1) > 1, so r ≤ 4
    right
    have hr_le : r ≤ 4 := by nlinarith
    interval_cases r
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; exact ⟨rfl, rfl, rfl⟩

end Etingof
