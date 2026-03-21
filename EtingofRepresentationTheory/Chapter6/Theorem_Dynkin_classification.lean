import Mathlib
import EtingofRepresentationTheory.Chapter6.DynkinTypes
import EtingofRepresentationTheory.Chapter6.DynkinForward

namespace Etingof

open Matrix Finset

/-- If two vertices of a Dynkin diagram both have degree 3, they must be the same vertex.
    Proof: if v ≠ w both have degree 3, define x on Fin n by putting 2 on all vertices
    of the unique v-to-w path and 1 on the extra neighbors of v and w (not on the path).
    Then B(x,x) = 0, contradicting positive definiteness. -/
private lemma dynkin_unique_degree_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v w : Fin n)
    (hv : vertexDegree adj v = 3) (hw : vertexDegree adj w = 3) : v = w := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  by_contra hvw
  -- Build SimpleGraph and get a simple path from v to w
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := fun {i j} h => by change adj j i = 1; rw [hsymm.apply i j]; exact h
      loopless := ⟨fun i h => by change adj i i = 1 at h; linarith [hdiag i]⟩ }
  haveI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  haveI : Nonempty (Fin n) := ⟨v⟩
  have hG_conn : G.Connected :=
    ⟨fun u w' => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u w'
      exact list_path_reachable G path u w' hhead hlast hedges⟩
  obtain ⟨walk⟩ := hG_conn.preconnected v w
  set pw := (walk.toPath : G.Walk v w) with hpw_def
  have hpw_path : pw.IsPath := (walk.toPath).property
  set L := pw.length with hL_def
  have hL_pos : 0 < L := by
    rw [Nat.pos_iff_ne_zero]; intro hL0; apply hvw
    have hL0' : pw.length = 0 := by omega
    have h1 := pw.getVert_length
    rw [hL0'] at h1
    rw [← pw.getVert_zero]; exact h1
  -- Support properties
  set supp := pw.support.toFinset with hsupp_def
  have hv_in : v ∈ supp := List.mem_toFinset.mpr pw.start_mem_support
  have hw_in : w ∈ supp := List.mem_toFinset.mpr pw.end_mem_support
  have hgv_in : ∀ m, m ≤ L → pw.getVert m ∈ supp :=
    fun m _ => List.mem_toFinset.mpr (pw.getVert_mem_support m)
  have hgv_adj : ∀ m, m < L → adj (pw.getVert m) (pw.getVert (m + 1)) = 1 :=
    fun m hm => pw.adj_getVert_succ hm
  have hgv_inj : ∀ m₁ m₂, m₁ ≤ L → m₂ ≤ L → pw.getVert m₁ = pw.getVert m₂ →
      m₁ = m₂ :=
    fun m₁ m₂ h₁ h₂ heq => hpw_path.getVert_injOn h₁ h₂ heq
  -- Define x: 2 on path, 1 on non-path neighbors of v/w, 0 else
  set x : Fin n → ℤ := fun i =>
    if i ∈ supp then 2
    else if adj v i = 1 ∨ adj w i = 1 then 1
    else 0 with hx_def
  have hx_ne : x ≠ 0 := by
    intro h; have hv0 := congr_fun h v
    change (if v ∈ supp then 2
      else if adj v v = 1 ∨ adj w v = 1 then 1 else 0) = 0 at hv0
    rw [if_pos hv_in] at hv0; exact absurd hv0 (by omega)
  have hx_nonneg : ∀ i, 0 ≤ x i := fun i => by simp only [x]; split_ifs <;> omega
  have hadj_nonneg : ∀ a b, 0 ≤ adj a b * x b := fun a b =>
    mul_nonneg (by rcases h01 a b with h | h <;> omega) (hx_nonneg b)
  -- mulVec decomposition
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
  have adj_sum_lb : ∀ (a b₁ b₂ : Fin n), b₁ ≠ b₂ →
      adj a b₁ = 1 → adj a b₂ = 1 →
      adj a b₁ * x b₁ + adj a b₂ * x b₂ ≤ ∑ b, adj a b * x b := by
    intro a b₁ b₂ hne hab₁ hab₂
    calc adj a b₁ * x b₁ + adj a b₂ * x b₂ =
        ∑ b ∈ ({b₁, b₂} : Finset _), adj a b * x b := by
          rw [Finset.sum_pair hne]
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg a b)
  have adj_sum_lb1 : ∀ (a b₁ : Fin n),
      adj a b₁ = 1 → adj a b₁ * x b₁ ≤ ∑ b, adj a b * x b := by
    intro a b₁ hab₁
    calc adj a b₁ * x b₁ = ∑ b ∈ ({b₁} : Finset _), adj a b * x b := by simp
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg a b)
  -- adj_sum ≥ 4 for v or w: degree-3 vertex with a known path neighbor
  have v_adj_sum_ge4 : ∀ (p1 : Fin n), adj v p1 = 1 → p1 ∈ supp →
      4 ≤ ∑ b, adj v b * x b := by
    intro p1 hp1_adj hp1_supp
    set N := Finset.univ.filter (fun j => adj v j = 1) with hN_def
    have hN_card : N.card = 3 := by
      simp only [hN_def]; delta vertexDegree at hv; convert hv
    have hp1_N : p1 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1_adj⟩
    have hN_erase : (N.erase p1).card = 2 := by
      rw [Finset.card_erase_of_mem hp1_N]; omega
    have hN_le : ∑ j ∈ N, adj v j * x j ≤ ∑ b, adj v b * x b :=
      Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg v b)
    have hN_sum : ∑ j ∈ N, adj v j * x j = adj v p1 * x p1 +
        ∑ j ∈ N.erase p1, adj v j * x j :=
      (Finset.add_sum_erase N _ hp1_N).symm
    have hxp1 : x p1 = 2 := by
      change (if p1 ∈ supp then 2 else _) = 2
      rw [if_pos hp1_supp]
    -- Each j ∈ N has adj(v,j) = 1, so x(j) ≥ 1
    have hN_min : ∀ j ∈ N.erase p1, 1 ≤ adj v j * x j := by
      intro j hj
      have hadj_j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
      rw [hadj_j, one_mul]
      change 1 ≤ (if j ∈ supp then 2
        else if adj v j = 1 ∨ adj w j = 1 then 1 else 0)
      split_ifs with h1 h2
      · omega
      · omega
      · exact absurd (Or.inl hadj_j) h2
    -- 2 + sum of at least 2 terms each ≥ 1
    have hsum_ge : 2 ≤ ∑ j ∈ N.erase p1, adj v j * x j := by
      calc 2 = ∑ _ ∈ N.erase p1, (1 : ℤ) := by
            rw [Finset.sum_const]; simp [hN_erase]
        _ ≤ ∑ j ∈ N.erase p1, adj v j * x j :=
          Finset.sum_le_sum hN_min
    nlinarith [hp1_adj, hxp1]
  have w_adj_sum_ge4 : ∀ (p1 : Fin n), adj w p1 = 1 → p1 ∈ supp →
      4 ≤ ∑ b, adj w b * x b := by
    intro p1 hp1_adj hp1_supp
    set N := Finset.univ.filter (fun j => adj w j = 1) with hN_def
    have hN_card : N.card = 3 := by
      simp only [hN_def]; delta vertexDegree at hw; convert hw
    have hp1_N : p1 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1_adj⟩
    have hN_erase : (N.erase p1).card = 2 := by
      rw [Finset.card_erase_of_mem hp1_N]; omega
    have hN_le : ∑ j ∈ N, adj w j * x j ≤ ∑ b, adj w b * x b :=
      Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg w b)
    have hN_sum : ∑ j ∈ N, adj w j * x j = adj w p1 * x p1 +
        ∑ j ∈ N.erase p1, adj w j * x j :=
      (Finset.add_sum_erase N _ hp1_N).symm
    have hxp1 : x p1 = 2 := by
      change (if p1 ∈ supp then 2 else _) = 2
      rw [if_pos hp1_supp]
    have hN_min : ∀ j ∈ N.erase p1, 1 ≤ adj w j * x j := by
      intro j hj
      have hadj_j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
      rw [hadj_j, one_mul]
      change 1 ≤ (if j ∈ supp then 2
        else if adj v j = 1 ∨ adj w j = 1 then 1 else 0)
      split_ifs with h1 h2
      · omega
      · omega
      · exact absurd (Or.inr hadj_j) h2
    have hsum_ge : 2 ≤ ∑ j ∈ N.erase p1, adj w j * x j := by
      calc 2 = ∑ _ ∈ N.erase p1, (1 : ℤ) := by
            rw [Finset.sum_const]; simp [hN_erase]
        _ ≤ ∑ j ∈ N.erase p1, adj w j * x j :=
          Finset.sum_le_sum hN_min
    nlinarith [hp1_adj, hxp1]
  -- B(x,x) ≤ 0
  have hB_le : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos; intro a _
    rw [mulVec_eq]
    by_cases ha_S : a ∈ supp
    · -- a is on the path, x a = 2
      have hxa : x a = 2 := by simp [x, ha_S]
      rw [hxa]
      -- Find index of a in the support
      have ha_mem : a ∈ pw.support := List.mem_toFinset.mp ha_S
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp ha_mem
      rw [pw.length_support] at hidx_lt
      have hidx_le : idx ≤ L := by omega
      have ha_gv : pw.getVert idx = a := by
        rw [pw.getVert_eq_support_getElem hidx_le]; exact hidx_eq
      by_cases hidx0 : idx = 0
      · -- a = v (start of path)
        have hav : a = v := by rw [← ha_gv, hidx0, pw.getVert_zero]
        rw [hav]
        have h01 := hgv_adj 0 hL_pos
        rw [pw.getVert_zero] at h01
        nlinarith [v_adj_sum_ge4 (pw.getVert 1) h01 (hgv_in 1 (by omega))]
      · by_cases hidxL : idx = L
        · -- a = w (end of path)
          have haw : a = w := by
            rw [← ha_gv, hidxL]; exact pw.getVert_length
          rw [haw]
          have hp_adj : adj w (pw.getVert (L - 1)) = 1 := by
            have := hgv_adj (L - 1) (by omega)
            rw [show L - 1 + 1 = L from by omega] at this
            rwa [pw.getVert_length, hsymm.apply] at this
          nlinarith [w_adj_sum_ge4 (pw.getVert (L - 1)) hp_adj
            (hgv_in (L - 1) (by omega))]
        · -- Interior path vertex: two distinct path neighbors
          have h0 : 0 < idx := by omega
          have hL' : idx < L := by omega
          have hpred := hgv_adj (idx - 1) (by omega)
          rw [show idx - 1 + 1 = idx from by omega] at hpred
          have hsucc := hgv_adj idx hL'
          rw [ha_gv] at hpred hsucc
          have hpred' : adj a (pw.getVert (idx - 1)) = 1 := by
            rw [hsymm.apply]; exact hpred
          have hne : pw.getVert (idx - 1) ≠ pw.getVert (idx + 1) := by
            intro heq
            exact absurd (hgv_inj (idx - 1) (idx + 1) (by omega)
              (by omega) heq) (by omega)
          have hpred_x : x (pw.getVert (idx - 1)) = 2 := by
            simp [x, hgv_in (idx - 1) (by omega)]
          have hsucc_x : x (pw.getVert (idx + 1)) = 2 := by
            simp [x, hgv_in (idx + 1) (by omega)]
          nlinarith [adj_sum_lb a _ _ hne hpred' hsucc,
            hpred_x, hsucc_x]
    · -- a not on path
      by_cases ha_adj : adj v a = 1 ∨ adj w a = 1
      · have hxa : x a = 1 := by
          simp only [x, if_neg ha_S, if_pos ha_adj]
        rw [hxa]
        rcases ha_adj with hva | hwa
        · have hav : adj a v = 1 := by rw [hsymm.apply]; exact hva
          have hxv : x v = 2 := by simp [hx_def, hv_in]
          nlinarith [adj_sum_lb1 a v hav]
        · have haw : adj a w = 1 := by rw [hsymm.apply]; exact hwa
          have hxw : x w = 2 := by simp [hx_def, hw_in]
          nlinarith [adj_sum_lb1 a w haw]
      · have : x a = 0 := by simp [x, ha_S, ha_adj]
        rw [this]; simp
  linarith [hpos x hx_ne]

/-- In a Dynkin diagram with a degree-3 branch vertex v, at least one of v's
    neighbors is a leaf (degree 1). Proof: if all 3 neighbors had degree ≥ 2,
    the graph would contain T_{2,2,2} as a subgraph, whose Cartan form has
    the null vector (3,2,2,2,1,1,1), contradicting positive definiteness. -/
private lemma branch_has_leaf_neighbor {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (v : Fin n) (hv : vertexDegree adj v = 3) :
    ∃ u, adj v u = 1 ∧ vertexDegree adj u = 1 := by
  obtain ⟨hsymm, hdiag, h01, _, hpos⟩ := hD
  -- By contradiction: if every neighbor of v has degree ≥ 2
  by_contra h; push_neg at h
  -- Every neighbor u of v has vertexDegree ≠ 1, so degree ≥ 2 (it's ≥ 1 since adj v u = 1)
  have h_nbr_deg : ∀ u, adj v u = 1 → 2 ≤ vertexDegree adj u := by
    intro u hu
    have h1 : 1 ≤ vertexDegree adj u := by
      change 1 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
      exact Finset.one_le_card.mpr ⟨v, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩⟩
    have h_ne1 : vertexDegree adj u ≠ 1 := h u hu
    omega
  -- Extract 3 neighbors of v
  set N := Finset.univ.filter (fun j => adj v j = 1) with hN_def
  have hN_card : N.card = 3 := hv
  -- Get 3 distinct neighbors
  obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hcover⟩ :=
    Finset.card_eq_three.mp hN_card
  have hn₁_adj : adj v n₁ = 1 := by
    have : n₁ ∈ N := hcover ▸ Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2
  have hn₂_adj : adj v n₂ = 1 := by
    have : n₂ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _))
    exact (Finset.mem_filter.mp this).2
  have hn₃_adj : adj v n₃ = 1 := by
    have : n₃ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))
    exact (Finset.mem_filter.mp this).2
  -- Each neighbor has degree ≥ 2, so has another neighbor besides v
  have get_second_nbr : ∀ u, adj v u = 1 → u ≠ v →
      ∃ w, adj u w = 1 ∧ w ≠ v ∧ w ≠ u := by
    intro u hu hu_ne
    have hdeg : 2 ≤ vertexDegree adj u := h_nbr_deg u hu
    -- u has ≥ 2 neighbors, one is v, so there's another
    have : 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card := hdeg
    have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩
    -- After removing v, still ≥ 1 neighbor
    have h_erase := Finset.card_erase_of_mem hv_mem
    have : 1 ≤ ((Finset.univ.filter (fun j => adj u j = 1)).erase v).card := by omega
    obtain ⟨w, hw_mem⟩ := Finset.one_le_card.mp this
    have hw := Finset.mem_erase.mp hw_mem
    have hw_ne_u : w ≠ u := by
      intro heq; subst heq
      have := (Finset.mem_filter.mp hw.2).2
      rw [hdiag] at this; omega
    exact ⟨w, (Finset.mem_filter.mp hw.2).2, hw.1, hw_ne_u⟩
  -- v ≠ nᵢ for each i
  have hv_ne1 : n₁ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₁_adj; omega
  have hv_ne2 : n₂ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₂_adj; omega
  have hv_ne3 : n₃ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₃_adj; omega
  obtain ⟨a₁, ha₁_adj, ha₁_nv, ha₁_nn⟩ := get_second_nbr n₁ hn₁_adj hv_ne1
  obtain ⟨a₂, ha₂_adj, ha₂_nv, ha₂_nn⟩ := get_second_nbr n₂ hn₂_adj hv_ne2
  obtain ⟨a₃, ha₃_adj, ha₃_nv, ha₃_nn⟩ := get_second_nbr n₃ hn₃_adj hv_ne3
  -- Now embed T_{2,2,2} = {v, n₁, n₂, n₃, a₁, a₂, a₃} as a subgraph
  -- Null vector: v→3, nᵢ→2, aᵢ→1. B = 2(9+4+4+4+1+1+1) - 2(3·2·3+2·1·3) =
  -- 2·24 - 2(18+6) = 48 - 48 = 0.
  -- Actually: let's put weights directly on Fin n.
  -- x(v)=3, x(nᵢ)=2, x(aᵢ)=1, x(else)=0.
  -- Then for each nonzero vertex i, 2xᵢ = Σⱼ aᵢⱼ xⱼ:
  --   v: 2·3=6 = x(n₁)+x(n₂)+x(n₃) = 2+2+2 = 6 ✓
  --   nᵢ: 2·2=4 = x(v)+x(aᵢ) = 3+1 = 4 ✓ (needs nᵢ adj to only v and aᵢ among nonzero)
  --   aᵢ: 2·1=2 = x(nᵢ) = 2 ✓ (needs aᵢ adj to only nᵢ among nonzero)
  -- Wait, nᵢ might also be adjacent to other nonzero vertices (e.g., n₁ adj n₂).
  -- In a tree, nᵢ~nⱼ would create a triangle v-nᵢ-nⱼ-v, which is a cycle!
  -- So no nᵢ~nⱼ edges in a tree. Similarly aᵢ can't be adjacent to v or nⱼ (j≠i).
  -- But we haven't formally proved "no cycles" for these specific vertices.
  -- Instead, use a direct computation showing B(x,x) ≤ 0.
  set x : Fin n → ℤ := fun a =>
    if a = v then 3
    else if a = n₁ ∨ a = n₂ ∨ a = n₃ then 2
    else if a = a₁ ∨ a = a₂ ∨ a = a₃ then 1
    else 0 with hx_def
  have hx_ne : x ≠ 0 := by
    intro h; have := congr_fun h v; simp [x] at this
  -- Show B(x,x) ≤ 0 by decomposing the sum
  have hB_le : dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) ≤ 0 := by
    -- B(x,x) = Σᵢ xᵢ · (2xᵢ - Σⱼ aᵢⱼ·xⱼ)
    -- For each nonzero xᵢ, show 2xᵢ ≤ Σⱼ aᵢⱼ·xⱼ
    -- Since xᵢ ≥ 0 for all i, each term xᵢ·(2xᵢ - Σⱼ) ≤ 0
    -- B(x,x) = Σᵢ xᵢ · (2xᵢ - Σⱼ aᵢⱼ·xⱼ)
    -- For each i with xᵢ > 0: 2xᵢ ≤ Σⱼ aᵢⱼ·xⱼ, so the term is ≤ 0.
    -- For i with xᵢ = 0: term is 0. Hence B(x,x) ≤ 0.
    have hx_nonneg : ∀ i, 0 ≤ x i := by
      intro i; simp only [x]; split_ifs <;> omega
    have hadj_x_nn : ∀ i j, 0 ≤ adj i j * x j := by
      intro i j; rcases h01 i j with h | h <;> simp [h, hx_nonneg j]
    -- Adjacency symmetry: reverse edge facts
    have ha_n1v : adj n₁ v = 1 := by rw [hsymm.apply v n₁]; exact hn₁_adj
    have ha_n2v : adj n₂ v = 1 := by rw [hsymm.apply v n₂]; exact hn₂_adj
    have ha_n3v : adj n₃ v = 1 := by rw [hsymm.apply v n₃]; exact hn₃_adj
    have ha_a1n1 : adj a₁ n₁ = 1 := by rw [hsymm.apply n₁ a₁]; exact ha₁_adj
    have ha_a2n2 : adj a₂ n₂ = 1 := by rw [hsymm.apply n₂ a₂]; exact ha₂_adj
    have ha_a3n3 : adj a₃ n₃ = 1 := by rw [hsymm.apply n₃ a₃]; exact ha₃_adj
    -- x values for specific vertices
    have hxv : x v = 3 := by simp [x]
    have hxn1 : x n₁ = 2 := by
      show (if n₁ = v then 3 else if n₁ = n₁ ∨ n₁ = n₂ ∨ n₁ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne1, if_pos (Or.inl rfl)]
    have hxn2 : x n₂ = 2 := by
      show (if n₂ = v then 3 else if n₂ = n₁ ∨ n₂ = n₂ ∨ n₂ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne2, if_pos (Or.inr (Or.inl rfl))]
    have hxn3 : x n₃ = 2 := by
      show (if n₃ = v then 3 else if n₃ = n₁ ∨ n₃ = n₂ ∨ n₃ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne3, if_pos (Or.inr (Or.inr rfl))]
    -- Key: for each i, 2*x(i) ≤ Σⱼ adj(i,j)*x(j)
    suffices h_bound : ∀ i : Fin n, 2 * x i ≤ ∑ j : Fin n, adj i j * x j by
      -- Derive B(x,x) ≤ 0 from h_bound
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply]
      apply Finset.sum_nonpos
      intro i _
      apply mul_nonpos_of_nonneg_of_nonpos (hx_nonneg i)
      -- 2 • and (2 : ℤ) * are definitionally equal, so use * form directly
      show ∑ j : Fin n, ((2 : ℤ) * (if i = j then 1 else 0) - adj i j) * x j ≤ 0
      have : ∑ j : Fin n, ((2 : ℤ) * (if i = j then (1 : ℤ) else 0) - adj i j) * x j =
          2 * x i - ∑ j : Fin n, adj i j * x j := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
          (fun j _ hji => by rw [if_neg (Ne.symm hji)])]
        simp
      linarith [this, h_bound i]
    -- Prove the bound for each vertex type
    intro i
    by_cases hxi : x i = 0
    · simp [hxi]; exact Finset.sum_nonneg (fun j _ => hadj_x_nn i j)
    · have hi_cases : i = v ∨ (i = n₁ ∨ i = n₂ ∨ i = n₃) ∨
          (i = a₁ ∨ i = a₂ ∨ i = a₃) := by
        simp only [x] at hxi; split_ifs at hxi <;> simp_all
      -- Use Finset.sum_le_sum_of_subset_of_nonneg to extract subset sums
      rcases hi_cases with hi | (hi | hi | hi) | (hi | hi | hi) <;> rw [hi]
      · -- v: {n₁,n₂,n₃} contributes ≥ 6 = 2*3
        have hS : ({n₁, n₂, n₃} : Finset _).sum (fun j => adj v j * x j) ≤
            ∑ j : Fin n, adj v j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn v j)
        have hS_eq : ({n₁, n₂, n₃} : Finset _).sum (fun j => adj v j * x j) = 6 := by
          have hm1 : n₁ ∉ ({n₂, n₃} : Finset _) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hne12, hne13⟩
          rw [Finset.sum_insert hm1, Finset.sum_pair hne23,
              hn₁_adj, hn₂_adj, hn₃_adj, hxn1, hxn2, hxn3]; norm_num
        rw [hxv]; linarith
      · -- n₁: {v, a₁} contributes ≥ 4 = 2*2
        have hS_le : ({v, a₁} : Finset _).sum (fun j => adj n₁ j * x j) ≤
            ∑ j : Fin n, adj n₁ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₁ j)
        have hS_ge : ({v, a₁} : Finset _).sum (fun j => adj n₁ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₁_nv), ha_n1v, ha₁_adj, one_mul, one_mul, hxv]
          have : x a₁ ≥ 1 := by
            show (if a₁ = v then 3 else if a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃ then 2
              else if a₁ = a₁ ∨ a₁ = a₂ ∨ a₁ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₁_nv]
            by_cases h : a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₁ = a₁ ∨ a₁ = a₂ ∨ a₁ = a₃ from Or.inl rfl)]
          linarith
        rw [hxn1]; linarith
      · -- n₂: {v, a₂} contributes ≥ 4
        have hS_le : ({v, a₂} : Finset _).sum (fun j => adj n₂ j * x j) ≤
            ∑ j : Fin n, adj n₂ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₂ j)
        have hS_ge : ({v, a₂} : Finset _).sum (fun j => adj n₂ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₂_nv), ha_n2v, ha₂_adj, one_mul, one_mul, hxv]
          have : x a₂ ≥ 1 := by
            show (if a₂ = v then 3 else if a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃ then 2
              else if a₂ = a₁ ∨ a₂ = a₂ ∨ a₂ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₂_nv]
            by_cases h : a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₂ = a₁ ∨ a₂ = a₂ ∨ a₂ = a₃ from Or.inr (Or.inl rfl))]
          linarith
        rw [hxn2]; linarith
      · -- n₃: {v, a₃} contributes ≥ 4
        have hS_le : ({v, a₃} : Finset _).sum (fun j => adj n₃ j * x j) ≤
            ∑ j : Fin n, adj n₃ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₃ j)
        have hS_ge : ({v, a₃} : Finset _).sum (fun j => adj n₃ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₃_nv), ha_n3v, ha₃_adj, one_mul, one_mul, hxv]
          have : x a₃ ≥ 1 := by
            show (if a₃ = v then 3 else if a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃ then 2
              else if a₃ = a₁ ∨ a₃ = a₂ ∨ a₃ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₃_nv]
            by_cases h : a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₃ = a₁ ∨ a₃ = a₂ ∨ a₃ = a₃ from Or.inr (Or.inr rfl))]
          linarith
        rw [hxn3]; linarith
      · -- a₁: need 2 * x a₁ ≤ ∑ j, adj a₁ j * x j
        by_cases ha₁_in_n : a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃
        · -- a₁ ∈ {n₁,n₂,n₃}: x a₁ = 2, use pair {n₁, v} for sum ≥ 5
          have ha₁v : adj a₁ v = 1 := by
            rcases ha₁_in_n with hi | hi | hi
            · exact absurd hi ha₁_nn
            · rw [hi, hsymm.apply v n₂]; exact hn₂_adj
            · rw [hi, hsymm.apply v n₃]; exact hn₃_adj
          have hS_pair : ({n₁, v} : Finset _).sum (fun j => adj a₁ j * x j) ≤
              ∑ j : Fin n, adj a₁ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₁ j)
          rw [Finset.sum_pair hv_ne1, ha_a1n1, ha₁v, one_mul, one_mul, hxn1, hxv] at hS_pair
          have hxa : x a₁ = 2 := by simp only [x]; rw [if_neg ha₁_nv, if_pos ha₁_in_n]
          linarith
        · -- a₁ ∉ {n₁,n₂,n₃}: x a₁ ≤ 1, one neighbor n₁ gives sum ≥ 2
          have hS : adj a₁ n₁ * x n₁ ≤ ∑ j : Fin n, adj a₁ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₁ j) (Finset.mem_univ n₁)
          rw [ha_a1n1, one_mul, hxn1] at hS
          have hxa : x a₁ ≤ 1 := by
            simp only [x]; rw [if_neg ha₁_nv, if_neg ha₁_in_n]; omega
          linarith
      · -- a₂: same structure as a₁
        by_cases ha₂_in_n : a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃
        · have ha₂v : adj a₂ v = 1 := by
            rcases ha₂_in_n with hi | hi | hi
            · rw [hi, hsymm.apply v n₁]; exact hn₁_adj
            · exact absurd hi ha₂_nn
            · rw [hi, hsymm.apply v n₃]; exact hn₃_adj
          have hS_pair : ({n₂, v} : Finset _).sum (fun j => adj a₂ j * x j) ≤
              ∑ j : Fin n, adj a₂ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₂ j)
          rw [Finset.sum_pair hv_ne2, ha_a2n2, ha₂v, one_mul, one_mul, hxn2, hxv] at hS_pair
          have hxa : x a₂ = 2 := by simp only [x]; rw [if_neg ha₂_nv, if_pos ha₂_in_n]
          linarith
        · have hS : adj a₂ n₂ * x n₂ ≤ ∑ j : Fin n, adj a₂ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₂ j) (Finset.mem_univ n₂)
          rw [ha_a2n2, one_mul, hxn2] at hS
          have hxa : x a₂ ≤ 1 := by
            simp only [x]; rw [if_neg ha₂_nv, if_neg ha₂_in_n]; omega
          linarith
      · -- a₃: same structure as a₁
        by_cases ha₃_in_n : a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃
        · have ha₃v : adj a₃ v = 1 := by
            rcases ha₃_in_n with hi | hi | hi
            · rw [hi, hsymm.apply v n₁]; exact hn₁_adj
            · rw [hi, hsymm.apply v n₂]; exact hn₂_adj
            · exact absurd hi ha₃_nn
          have hS_pair : ({n₃, v} : Finset _).sum (fun j => adj a₃ j * x j) ≤
              ∑ j : Fin n, adj a₃ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₃ j)
          rw [Finset.sum_pair hv_ne3, ha_a3n3, ha₃v, one_mul, one_mul, hxn3, hxv] at hS_pair
          have hxa : x a₃ = 2 := by simp only [x]; rw [if_neg ha₃_nv, if_pos ha₃_in_n]
          linarith
        · have hS : adj a₃ n₃ * x n₃ ≤ ∑ j : Fin n, adj a₃ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₃ j) (Finset.mem_univ n₃)
          rw [ha_a3n3, one_mul, hxn3] at hS
          have hxa : x a₃ ≤ 1 := by
            simp only [x]; rw [if_neg ha₃_nv, if_neg ha₃_in_n]; omega
          linarith
  linarith [hpos x hx_ne]

/-- In a Dynkin diagram on 4 vertices with a degree-3 vertex v, the graph is a star:
    v is adjacent to all other vertices, and all other vertices have degree 1. -/
private lemma star_adj_of_deg3_n4 {adj : Matrix (Fin 4) (Fin 4) ℤ}
    (hD : IsDynkinDiagram 4 adj) (v : Fin 4) (hv : vertexDegree adj v = 3) :
    ∀ i j : Fin 4, adj i j = if (i = v) = (j = v) then 0 else 1 := by
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  -- v is adjacent to all non-v: neighbor set = univ \ {v}
  have hadj_v : ∀ j, j ≠ v → adj v j = 1 := by
    intro j hj
    have hsub : Finset.univ.filter (fun j => adj v j = 1) ⊆ Finset.univ.erase v := by
      intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_erase.mpr ⟨fun h => by rw [h] at hx; linarith [hdiag v], Finset.mem_univ _⟩
    have hcard : (Finset.univ.erase v).card ≤ (Finset.univ.filter (fun j => adj v j = 1)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      unfold vertexDegree at hv; omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : j ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
    rw [← heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  -- Non-v vertices are not adjacent to each other (edge count argument)
  have hno_edge : ∀ i j : Fin 4, i ≠ v → j ≠ v → i ≠ j → adj i j = 0 := by
    intro i j hi hj hij
    rcases h01 i j with h | h
    · exact h
    · -- If adj i j = 1, then subgraph {v, i, j} has too many edges for a tree
      exfalso
      have hedge := dynkin_edge_count hD (by omega)
      unfold edgeCount at hedge
      have hdeg_i : 2 ≤ vertexDegree adj i := by
        change 2 ≤ (Finset.univ.filter (fun k => adj i k = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun k => adj i k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply i v ▸ hadj_v i hi⟩
        have hj_mem : j ∈ Finset.univ.filter (fun k => adj i k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        have hne : v ≠ j := Ne.symm hj
        exact Finset.one_lt_card.mpr ⟨v, hv_mem, j, hj_mem, hne⟩
      have hdeg_j : 2 ≤ vertexDegree adj j := by
        change 2 ≤ (Finset.univ.filter (fun k => adj j k = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun k => adj j k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply j v ▸ hadj_v j hj⟩
        have hi_mem : i ∈ Finset.univ.filter (fun k => adj j k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply j i ▸ h⟩
        have hne : v ≠ i := Ne.symm hi
        exact Finset.one_lt_card.mpr ⟨v, hv_mem, i, hi_mem, hne⟩
      have hsum_ge : 8 ≤ ∑ k : Fin 4, vertexDegree adj k := by
        have hv_sum := Finset.add_sum_erase Finset.univ (fun k => vertexDegree adj k) (Finset.mem_univ v)
        have hi_sum := Finset.add_sum_erase (Finset.univ.erase v) (fun k => vertexDegree adj k)
          (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
        have hj_mem : j ∈ (Finset.univ.erase v).erase i :=
          Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
        have hj_sum := Finset.add_sum_erase ((Finset.univ.erase v).erase i) (fun k => vertexDegree adj k) hj_mem
        have hrest_ge : ∀ k ∈ ((Finset.univ.erase v).erase i).erase j, 1 ≤ vertexDegree adj k := by
          intro k hk
          have hkv : k ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2).1
          change 1 ≤ (Finset.univ.filter (fun m => adj k m = 1)).card
          exact Finset.one_le_card.mpr ⟨v, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hsymm.apply k v ▸ hadj_v k hkv⟩⟩
        have hrest_nonempty : (((Finset.univ.erase v).erase i).erase j).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h
          have := Finset.card_eq_zero.mpr h
          simp [Finset.card_erase_of_mem, hj_mem,
            Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩] at this
        obtain ⟨k, hk⟩ := hrest_nonempty
        have hk_le := Finset.single_le_sum (fun x _ => Nat.zero_le (vertexDegree adj x)) hk
        linarith [hrest_ge k hk]
      omega
  -- Now derive the star adjacency
  intro i j
  by_cases hiv : i = v <;> by_cases hjv : j = v
  · -- i = v, j = v: adj v v = 0
    have : (i = v) = (j = v) := by simp [hiv, hjv]
    simp only [this, ite_true, hiv, hjv, hdiag]
  · -- i = v, j ≠ v: adj v j = 1
    simp only [hiv, hjv, eq_self_iff_true, ite_false]; exact hadj_v j hjv
  · -- i ≠ v, j = v: adj i v = 1
    simp only [hjv, eq_self_iff_true, eq_true, hiv, ite_false]
    exact hsymm.apply i v ▸ hadj_v i hiv
  · -- Neither i nor j is v: adj i j = 0
    have : (i = v) = (j = v) := by rw [eq_false hiv, eq_false hjv]
    simp only [this, ite_true]
    by_cases hij : i = j
    · simp [hij, hdiag]
    · exact hno_edge i j hiv hjv hij

/-- For n = 4, a Dynkin diagram with a degree-3 vertex is isomorphic to D₄. -/
private lemma branch_classification_n4 {adj : Matrix (Fin 4) (Fin 4) ℤ}
    (hD : IsDynkinDiagram 4 adj) (v : Fin 4) (hv : vertexDegree adj v = 3) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin 4,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  have hstar := star_adj_of_deg3_n4 hD v hv
  -- D₄ has branch at vertex 1, and its adjacency is also a star centered at 1
  -- Isomorphism: swap vertex 1 with v
  set σ : Fin 4 ≃ Fin 4 := Equiv.swap (⟨1, by omega⟩ : Fin 4) v
  refine ⟨.D 4 (by omega), σ, fun i j => ?_⟩
  -- i j : Fin (DynkinType.D 4 _).rank which is definitionally Fin 4
  have hi := i.isLt; have hj := j.isLt
  change _ < 4 at hi hj
  change adj (σ ⟨i.val, by omega⟩) (σ ⟨j.val, by omega⟩) = _
  rw [hstar]
  have hσ_eq_v : ∀ x : Fin 4, σ x = v ↔ x = ⟨1, by omega⟩ := by
    intro x; constructor
    · intro h; exact σ.injective (h.trans (Equiv.swap_apply_left _ _).symm)
    · intro h; subst h; exact Equiv.swap_apply_left _ _
  simp only [hσ_eq_v]
  simp only [DynkinType.adj, DynkinType.rank, Fin.ext_iff]
  split_ifs with h <;> simp_all <;> omega

/-- Helper: given a path walk σ' on a reduced graph adj' (Fin k) with branch vertex v'
    at position b, and a leaf u adjacent to the branch in the full graph adj (Fin (k+1)),
    construct a graph isomorphism to a DynkinType whose adjacency has:
    - path edges: consecutive indices i, i+1 for i < k-1 among the first k vertices
    - branch edge: vertex b_std connected to vertex k
    The isomorphism handles both direct (b = b_std) and reversed (b = k-1-b_std) cases. -/
private lemma tree_branch_iso {k : ℕ} {adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ}
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (u : Fin (k + 1)) (v' : Fin k)
    (adj' : Matrix (Fin k) (Fin k) ℤ)
    (hadj'_def : adj' = fun i j => adj (u.succAbove i) (u.succAbove j))
    (hu_adj : adj u (u.succAbove v') = 1)
    (hu_unique : ∀ w, adj u w = 1 → w = u.succAbove v')
    (σ' : Fin k ≃ Fin k)
    (hσ'_fwd : ∀ (m : Fin k) (hm : m.val + 1 < k),
      adj' (σ' m) (σ' ⟨m.val + 1, hm⟩) = 1)
    (hσ'_only : ∀ i j, adj' (σ' i) (σ' j) = 1 →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (b : ℕ) (hb_lt : b < k) (hσ'_b : σ' ⟨b, hb_lt⟩ = v')
    (t_adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (b_std : ℕ) (hb_std_lt : b_std < k)
    (hb_match : b = b_std ∨ b = k - 1 - b_std)
    (ht_path : ∀ (i j : Fin (k + 1)), i.val < k → j.val < k →
      t_adj i j = if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0)
    (ht_branch : ∀ (i : Fin (k + 1)), i.val < k →
      t_adj i ⟨k, by omega⟩ = if i.val = b_std then 1 else 0)
    (ht_branch_symm : ∀ (i : Fin (k + 1)), i.val < k →
      t_adj ⟨k, by omega⟩ i = if i.val = b_std then 1 else 0)
    (ht_diag_k : t_adj ⟨k, by omega⟩ ⟨k, by omega⟩ = 0) :
    ∃ σ : Fin (k + 1) ≃ Fin (k + 1),
      ∀ i j, adj (σ i) (σ j) = t_adj i j := by
  sorry

/-- A tree with a degree-3 vertex (branch) and all degrees ≤ 3 has exactly one such vertex,
    three arms of lengths p ≤ q ≤ r with n = p + q + r + 1, and is uniquely determined
    (up to graph isomorphism) by its arm lengths. Given the arm-length constraint from
    positive definiteness, the graph must be isomorphic to D_n, E₆, E₇, or E₈. -/
private lemma branch_classification {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hbranch : ∃ i, vertexDegree adj i = 3) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  obtain ⟨v, hv⟩ := hbranch
  -- n ≥ 4: branch vertex v has 3 distinct neighbors, needing at least 4 vertices
  have hn4 : 4 ≤ n := by
    obtain ⟨_, hdiag, _, _, _⟩ := hD
    by_contra h; push_neg at h
    have : (Finset.univ.filter (fun j => adj v j = 1)).card ≤
        (Finset.univ.erase v).card := by
      apply Finset.card_le_card
      intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_erase.mpr ⟨fun h' => by subst h'; linarith [hdiag x], Finset.mem_univ _⟩
    simp [Finset.card_erase_of_mem] at this
    change vertexDegree adj v ≤ n - 1 at this
    omega
  -- Base case: n = 4
  by_cases hn4e : n = 4
  · subst hn4e; exact branch_classification_n4 hD v hv
  · -- Inductive case: n ≥ 5
    have hn5 : 5 ≤ n := by omega
    -- Step 1: Get a leaf neighbor of v
    obtain ⟨u, hu_adj, hu_deg⟩ := branch_has_leaf_neighbor hD v hv
    obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
    have hu_ne : u ≠ v := by
      intro h; subst h; rw [hdiag] at hu_adj; omega
    -- u has exactly one neighbor, which is v
    have hu_unique : ∀ w, adj u w = 1 → w = v := by
      intro w hw
      by_contra hne_w
      have : 2 ≤ vertexDegree adj u := by
        change 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply u v ▸ hu_adj⟩
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj u j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        calc 2 = ({v, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne_w)]
          _ ≤ _ := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl; exact hv_mem; exact hw_mem)
      omega
    -- Step 2: Remove u to get reduced graph adj' on Fin (n-1)
    have hn2 : 2 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    set adj' : Matrix (Fin k) (Fin k) ℤ :=
      fun i j => adj (u.succAbove i) (u.succAbove j) with hadj'_def
    -- adj' is a Dynkin diagram (same proof pattern as in path_walk_construction)
    have hD' : IsDynkinDiagram k adj' := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
      · intro i; exact hdiag _
      · intro i j; exact h01 _ _
      · -- Connectivity: removing a leaf preserves connectivity
        let G : SimpleGraph (Fin (k + 1)) :=
          { Adj := fun i j => adj i j = 1
            symm := fun {i j} (h : adj i j = 1) => (hsymm.apply i j).trans h
            loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
        haveI : DecidableRel G.Adj :=
          fun i j => show Decidable (adj i j = 1) from inferInstance
        have hG_conn : G.Connected := by
          constructor
          intro a b
          obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
          exact list_path_reachable G path a b hhead hlast (fun k hk => hedges k hk)
        have hG_deg : G.degree u = 1 := by
          unfold SimpleGraph.degree
          have heq : G.neighborFinset u = Finset.univ.filter (adj u · = 1) := by
            ext j; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
              Finset.mem_univ, true_and]; exact ⟨fun h => h, fun h => h⟩
          rw [heq]; unfold vertexDegree at hu_deg; convert hu_deg
        have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
        intro a b
        have ha_ne : u.succAbove a ≠ u := Fin.succAbove_ne u a
        have hb_ne : u.succAbove b ≠ u := Fin.succAbove_ne u b
        have ha_mem : u.succAbove a ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
          Set.mem_compl_singleton_iff.mpr ha_ne
        have hb_mem : u.succAbove b ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
          Set.mem_compl_singleton_iff.mpr hb_ne
        obtain ⟨walk⟩ := hG'.preconnected ⟨u.succAbove a, ha_mem⟩ ⟨u.succAbove b, hb_mem⟩
        let toFink : ↥({u}ᶜ : Set (Fin (k + 1))) → Fin k :=
          fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
            (Set.mem_compl_singleton_iff.mp hx)).choose
        have htoFink_spec : ∀ (x : ↥({u}ᶜ : Set (Fin (k + 1)))),
            u.succAbove (toFink x) = x.val :=
          fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
            (Set.mem_compl_singleton_iff.mp hx)).choose_spec
        have htoFink_adj : ∀ (x y : ↥({u}ᶜ : Set (Fin (k + 1)))),
            (G.induce ({u}ᶜ : Set _)).Adj x y →
            adj' (toFink x) (toFink y) = 1 := by
          intro x y hadj_xy
          simp only [hadj'_def, SimpleGraph.induce_adj] at hadj_xy ⊢
          rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
        suffices h_walk : ∀ (a b : ↥({u}ᶜ : Set (Fin (k+1))))
            (w' : (G.induce ({u}ᶜ : Set _)).Walk a b),
          ∃ path : List (Fin k),
            path.head? = some (toFink a) ∧
            path.getLast? = some (toFink b) ∧
            ∀ m, (hm : m + 1 < path.length) →
              adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
          obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
          refine ⟨path, ?_, ?_, hedges⟩
          · convert hhead using 2
            exact (Fin.succAbove_right_injective
              (htoFink_spec ⟨u.succAbove a, ha_mem⟩)).symm
          · convert hlast using 2
            exact (Fin.succAbove_right_injective
              (htoFink_spec ⟨u.succAbove b, hb_mem⟩)).symm
        intro a b w'
        induction w' with
        | nil =>
          exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
        | @cons c d _ hadj_edge rest ih =>
          obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
          refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
          · cases path_rest with
            | nil => simp at hhead_rest hlast_rest ⊢
            | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
          · intro m hm
            match m with
            | 0 =>
              simp only [List.get_eq_getElem, List.getElem_cons_zero,
                List.getElem_cons_succ]
              have h0 : 0 < path_rest.length := by
                simp only [List.length_cons] at hm; omega
              have hd_eq : path_rest[0] = toFink d := by
                cases path_rest with
                | nil => simp at h0
                | cons y ys =>
                  simp only [List.head?, Option.some.injEq] at hhead_rest
                  simp only [List.getElem_cons_zero]; exact hhead_rest
              rw [hd_eq]; exact htoFink_adj c d hadj_edge
            | m' + 1 =>
              simp only [List.get_eq_getElem, List.getElem_cons_succ]
              exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)
      · -- Positive definiteness: principal submatrix of pos-def
        intro x hx
        set x' : Fin (k + 1) → ℤ := fun a =>
          if h : a = u then 0 else x (Fin.exists_succAbove_eq h).choose
        have hx'_u : x' u = 0 := by simp [x']
        have hx'_sa : ∀ i, x' (u.succAbove i) = x i := by
          intro i; simp only [x']
          rw [dif_neg (Fin.succAbove_ne u i)]; congr 1
          exact Fin.succAbove_right_injective
            (Fin.exists_succAbove_eq (Fin.succAbove_ne u i)).choose_spec
        have hx'_ne : x' ≠ 0 := by
          intro heq; apply hx; ext b
          have := congr_fun heq (u.succAbove b)
          rw [hx'_sa, Pi.zero_apply] at this; exact this
        have hB_eq : dotProduct x' ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x') =
            dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj').mulVec x) := by
          simp only [dotProduct, mulVec]
          conv_lhs => rw [Fin.sum_univ_succAbove _ u]
          simp only [hx'_u, zero_mul, zero_add]
          congr 1; ext i; rw [hx'_sa]; congr 1
          conv_lhs => rw [Fin.sum_univ_succAbove _ u]
          simp only [hx'_u, mul_zero, zero_add]
          congr 1; ext j; rw [hx'_sa]; congr 1
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
            Fin.succAbove_right_inj]
        linarith [hpos x' hx'_ne]
    -- Step 3: All degrees ≤ 2 in adj' (unique branch + leaf removal)
    have hpath' : ∀ i, vertexDegree adj' i ≤ 2 := by
      intro i
      unfold vertexDegree
      have h_image : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
          ⊆ Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := hx; exact hy
      have h_card := Finset.card_le_card h_image
      rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
      have hD_full : IsDynkinDiagram (k + 1) adj := ⟨hsymm, hdiag, h01, hconn, hpos⟩
      have hdeg_le3 := dynkin_degree_le_three hD_full (u.succAbove i)
      unfold vertexDegree at hdeg_le3
      by_cases hdeg3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card = 3
      · have hvi : u.succAbove i = v :=
          dynkin_unique_degree_three hD_full (u.succAbove i) v (by unfold vertexDegree; exact hdeg3) hv
        have h_image2 : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
            ⊆ (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).erase u := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne u y, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hvi]; exact hy
        have h_card2 := Finset.card_le_card h_image2
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card2
        have hu_mem : u ∈ Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_adj⟩
        rw [Finset.card_erase_of_mem hu_mem] at h_card2
        have hv3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).card = 3 := hv
        omega
      · have : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card ≤ 2 := by
          omega
        linarith
    -- Step 4: Find an endpoint and apply path_walk_construction
    obtain ⟨v₀', hv₀'_deg⟩ := dynkin_has_endpoint hD' hk1 hpath'
    obtain ⟨σ', hσ'0, hσ'_fwd, hσ'_only⟩ :=
      path_walk_construction hD' hk1 hpath' v₀' hv₀'_deg
    -- Step 5: Find v's position in the path
    have hv_ne_u : v ≠ u := Ne.symm hu_ne
    obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hv_ne_u
    set bfin := σ'.symm v' with hbfin_def
    set b := bfin.val with hb_def
    have hb_lt : b < k := bfin.isLt
    have hσ'_b : σ' bfin = v' := σ'.apply_symm_apply v'
    have hv'_deg2 : vertexDegree adj' v' = 2 := by
      apply le_antisymm (hpath' v')
      unfold vertexDegree
      set Nv := Finset.univ.filter (fun j => adj v j = 1) with hNv_def
      have hNv_card : Nv.card = 3 := hv
      have hu_mem : u ∈ Nv :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply v u ▸ hu_adj⟩
      have hNv_erase : (Nv.erase u).card = 2 := by
        rw [Finset.card_erase_of_mem hu_mem]; omega
      suffices h : 2 ≤ (Finset.univ.filter (fun j : Fin k => adj' v' j = 1)).card from h
      have h_image : ∀ w ∈ Nv.erase u, ∃ w' : Fin k,
          u.succAbove w' = w ∧ adj' v' w' = 1 := by
        intro w hw
        have hw_mem : w ∈ Nv := Finset.mem_of_mem_erase hw
        have hw_ne : w ≠ u := Finset.ne_of_mem_erase hw
        obtain ⟨w', hw'⟩ := Fin.exists_succAbove_eq hw_ne
        refine ⟨w', hw', ?_⟩
        show adj (u.succAbove v') (u.succAbove w') = 1
        rw [hv', hw']
        exact (Finset.mem_filter.mp hw_mem).2
      obtain ⟨a₁, a₂, ha_ne, ha_cover⟩ :=
        Finset.card_eq_two.mp hNv_erase
      have ha₁_mem : a₁ ∈ Nv.erase u := ha_cover ▸ Finset.mem_insert_self _ _
      have ha₂_mem : a₂ ∈ Nv.erase u :=
        ha_cover ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      obtain ⟨w₁, hw₁_eq, hw₁_adj⟩ := h_image a₁ ha₁_mem
      obtain ⟨w₂, hw₂_eq, hw₂_adj⟩ := h_image a₂ ha₂_mem
      have hne : w₁ ≠ w₂ := by
        intro h; apply ha_ne
        have := congr_arg u.succAbove h
        rw [hw₁_eq, hw₂_eq] at this; exact this
      calc 2 = ({w₁, w₂} : Finset _).card := (Finset.card_pair hne).symm
        _ ≤ (Finset.univ.filter (fun j : Fin k => adj' v' j = 1)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by rcases hx with rfl | rfl
                 · exact hw₁_adj
                 · exact hw₂_adj⟩)
    have hb_pos : 0 < b := by
      by_contra h; push_neg at h; have hb0 : b = 0 := by omega
      have hv'_eq : v' = v₀' := by
        have hbf0 : bfin = ⟨0, by omega⟩ := Fin.ext hb0
        have h1 : σ' bfin = v' := hσ'_b
        rw [hbf0] at h1
        exact h1.symm.trans hσ'0
      linarith [hv'_eq ▸ hv₀'_deg]
    have hb_lt_k1 : b < k - 1 := by
      by_contra h; push_neg at h; have hbk : b = k - 1 := by omega
      have hdeg_le1 : vertexDegree adj' v' ≤ 1 := by
        unfold vertexDegree
        suffices h : (Finset.univ.filter
            (fun j : Fin k => adj' v' j = 1)).card ≤ 1 from h
        rw [show (1 : ℕ) = ({σ' ⟨k - 2, by omega⟩} : Finset _).card from by simp]
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        simp only [Finset.mem_singleton]
        set wfin := σ'.symm w
        have hw_eq : σ' wfin = w := σ'.apply_symm_apply w
        rw [← hσ'_b, ← hw_eq] at hw
        have := hσ'_only bfin wfin hw
        rcases this with h1 | h2
        · exfalso; have := wfin.isLt
          change b + 1 = wfin.val at h1; omega
        · rw [← hw_eq]; congr 1
          apply Fin.ext; change wfin.val = k - 2
          change wfin.val + 1 = b at h2; omega
      linarith
    -- Set up arm lengths
    set p := 1 with hp_def
    set q := min b (k - 1 - b) with hq_def
    set r := max b (k - 1 - b) with hr_def
    have hp1 : 1 ≤ p := le_refl 1
    have hpq : p ≤ q := by
      simp only [p, q]; exact Nat.one_le_iff_ne_zero.mpr (by omega)
    have hqr : q ≤ r := by simp only [q, r]; omega
    have hn_eq : k + 1 = p + q + r + 1 := by
      simp only [p, q, r, min_def, max_def]
      split_ifs <;> omega
    have hrecip : (q + 1) * (r + 1) + (p + 1) * (r + 1) + (p + 1) * (q + 1) >
                  (p + 1) * (q + 1) * (r + 1) := by
      sorry -- Derived from positive definiteness of the Cartan form
    rcases arm_length_solutions p q r hp1 hpq hqr hrecip with
      ⟨_, hq1⟩ | ⟨_, hq2, hr2⟩ | ⟨_, hq2, hr3⟩ | ⟨_, hq2, hr4⟩
    · -- Case (1, 1, r): D_{r+3} type
      sorry
    · -- Case (1, 2, 2): E₆
      sorry
    · -- Case (1, 2, 3): E₇
      sorry
    · -- Case (1, 2, 4): E₈
      sorry

/-- Forward direction of the Dynkin classification: any Dynkin diagram on n ≥ 1 vertices
    is graph-isomorphic to one of the standard types A_n, D_n, E₆, E₇, or E₈. -/
private lemma dynkin_classification_forward {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  -- Every vertex has degree ≤ 3
  have hdeg := fun i => dynkin_degree_le_three hD i
  -- Case split: is there a vertex of degree 3?
  by_cases hbranch : ∃ i, vertexDegree adj i = 3
  · -- Branch case: tree with one branch → D_n or E-type
    exact branch_classification hD hn hbranch
  · -- Path case: all degrees ≤ 2 → A_n
    push_neg at hbranch
    have hpath : ∀ i, vertexDegree adj i ≤ 2 := by
      intro i; have := hdeg i
      rcases Nat.eq_or_lt_of_le this with h | h
      · exact absurd h (hbranch i)
      · omega
    obtain ⟨σ, hσ⟩ := path_iso_An hD hn hpath
    exact ⟨.A n hn, σ, hσ⟩

/-- Classification of Dynkin diagrams: a connected graph with positive-definite Cartan form
is a Dynkin diagram if and only if it is isomorphic (as a graph) to one of the standard
types A_n, D_n, E₆, E₇, or E₈.

Note: The hypothesis `1 ≤ n` is necessary because `IsDynkinDiagram 0 adj` is vacuously true
(all conditions quantify over `Fin 0`, which is empty) but no `DynkinType` has rank 0.
Mathematically, the empty graph is not a Dynkin diagram.
(Etingof Theorem, Section 6.1) -/
theorem Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  constructor
  · -- Forward direction: any Dynkin diagram is isomorphic to a standard type
    exact fun hD => dynkin_classification_forward hD hn
  · -- Backward direction: isomorphism to a standard type → IsDynkinDiagram
    rintro ⟨t, σ, hiso⟩
    exact isDynkinDiagram_of_graph_iso σ hiso (isDynkinDiagram_of_type t)

end Etingof
