import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification

/-!
# Example 6.4.9: D_n Root Count

The positive roots of D_n are parameterized by ordered pairs (i, j) with i < j
in Fin n. There are two families:
- **Type A**: interval vectors on the path 0—1—⋯—(n-2), with x_{n-1} = 0
  (corresponding to roots eᵢ - eⱼ)
- **Type B**: vectors involving the branch vertex n-1
  (corresponding to roots eᵢ + eⱼ)
Total: 2 · C(n,2) = n(n-1).
-/

section DnRootCount

open Matrix Finset

/-- SOS decomposition: 2·q_{D₄}(x) = (2x₀-x₁)² + (2x₂-x₁)² + (2x₃-x₁)² + x₁². -/
private lemma D4_sos (x₀ x₁ x₂ x₃ : ℤ) :
    2 * (2*(x₀^2+x₁^2+x₂^2+x₃^2) - 2*(x₀*x₁+x₁*x₂+x₁*x₃)) =
    (2*x₀-x₁)^2 + (2*x₂-x₁)^2 + (2*x₃-x₁)^2 + x₁^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
/-- Expand the D₄ quadratic form. -/
private lemma D4_qf (x : Fin 4 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) -
        (Etingof.DynkinType.D 4 le_rfl).adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2) -
    2*(x 0*x 1+x 1*x 2+x 1*x 3) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

/-- All positive roots of D₄ have each coordinate < 3. -/
private lemma D4_bound (x : Fin 4 → ℤ)
    (hr : Etingof.IsRoot 4 (Etingof.DynkinType.D 4 le_rfl).adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 3 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2) -
      2*(x 0*x 1+x 1*x 2+x 1*x 3) = 2 := by
    have := hr.2; rw [D4_qf] at this; exact this
  set a := x 0
  set b := x 1
  set c := x 2
  set d := x 3
  have hs : (2*a-b)^2 + (2*c-b)^2 + (2*d-b)^2 + b^2 = 4 := by
    nlinarith [D4_sos a b c d]
  have hb : b ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*c-b),
      sq_nonneg (2*d-b), sq_nonneg (b - 3)]
  have ha : a ≤ 2 := by
    nlinarith [sq_nonneg (2*c-b), sq_nonneg (2*d-b),
      sq_nonneg b, sq_nonneg (2*a - b - 3)]
  have hc : c ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*d-b),
      sq_nonneg b, sq_nonneg (2*c - b - 3)]
  have hd : d ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*c-b),
      sq_nonneg b, sq_nonneg (2*d - b - 3)]
  intro i; fin_cases i <;> simp_all <;> omega

-- The general D_n bound is proved by induction on n:
-- D_{n+1} QF decomposes as D_n QF on the tail + 2·x₀·(x₀ - x₁).
-- Since QFs on integer vectors are always even, this forces either
-- the tail to be a D_n root (so IH applies) or x = (1,0,...,0).

/-- The adjacency matrix of D_{m+1} restricted to Fin.succ indices
    equals the adjacency matrix of D_m. -/
private lemma Dn_adj_succ_succ (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj i.succ j.succ =
    (Etingof.DynkinType.D m hm).adj i j := by
  simp only [Etingof.DynkinType.adj, Fin.val_succ]
  have hi := i.isLt
  have hj := j.isLt
  congr 1
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩))
    · left; left; exact ⟨by omega, by omega⟩
    · left; right; exact ⟨by omega, by omega⟩
    · right; left; exact ⟨by omega, by omega⟩
    · right; right; exact ⟨by omega, by omega⟩
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩))
    · left; left; exact ⟨by omega, by omega⟩
    · left; right; exact ⟨by omega, by omega⟩
    · right; left; exact ⟨by omega, by omega⟩
    · right; right; exact ⟨by omega, by omega⟩

/-- Vertex 0 in D_{m+1} is only adjacent to vertex 1. -/
private lemma Dn_adj_zero_succ (m : ℕ) (hm : 4 ≤ m) (j : Fin m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj 0 j.succ =
    if j.val = 0 then 1 else 0 := by
  simp only [Etingof.DynkinType.adj, Fin.val_zero, Fin.val_succ]
  have hj := j.isLt
  split_ifs with h
  · -- j = 0: edge 0-1 exists
    simp only [h]
    simp only [ite_eq_left_iff, not_or, not_and]
    push_neg
    constructor
    · intro habs
      exfalso; exact habs.1 ⟨rfl, by omega⟩
    · intro habs; exfalso; exact habs.1 ⟨rfl, by omega⟩
  · -- j ≥ 1: no edge from 0
    simp only [ite_eq_right_iff]
    rintro ((⟨h1, _⟩ | ⟨h3, _⟩) | (⟨_, h6⟩ | ⟨h7, _⟩))
    · omega
    · omega
    · omega
    · omega

/-- Vertex 0 in D_{m+1} has no self-loop. -/
private lemma Dn_adj_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj 0 0 = 0 := by
  unfold Etingof.DynkinType.adj
  simp only [Fin.val_zero, ite_eq_right_iff]
  rintro ((⟨h1, _⟩ | ⟨h3, _⟩) | (⟨_, h6⟩ | ⟨_, h8⟩)) <;> omega

/-- adj(succ i, 0) in D_{m+1} equals adj(0, succ i) by symmetry. -/
private lemma Dn_adj_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj i.succ 0 =
    if i.val = 0 then 1 else 0 := by
  have hsymm := (Dn_isDynkin (m + 1) (by omega)).1
  rw [hsymm.apply i.succ 0]
  exact Dn_adj_zero_succ m hm i

/-- The Cartan matrix of D_{m+1} at (succ i, succ j) matches D_m at (i, j). -/
private lemma Dn_cartan_succ_succ (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) i.succ j.succ =
    (2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
      (Etingof.DynkinType.D m hm).adj) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  congr 1
  · congr 1; exact propext ⟨fun h => Fin.succ_injective _ h, fun h => congr_arg _ h⟩
  · exact Dn_adj_succ_succ m hm i j

/-- The Cartan matrix of D_{m+1} at (0, succ j). -/
private lemma Dn_cartan_zero_succ (m : ℕ) (hm : 4 ≤ m) (j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) 0 j.succ =
    if j.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.succ_ne_zero, ite_false]
  rw [Dn_adj_zero_succ m hm]
  split_ifs <;> simp

/-- The Cartan matrix of D_{m+1} at (succ i, 0). -/
private lemma Dn_cartan_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) i.succ 0 =
    if i.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.succ_ne_zero, ite_false]
  rw [Dn_adj_succ_zero m hm]
  split_ifs <;> simp

/-- The Cartan matrix of D_{m+1} at (0, 0) is 2. -/
private lemma Dn_cartan_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) 0 0 = 2 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ite_true, Dn_adj_zero_zero m hm]

/-- The D_{m+1} quadratic form decomposes as D_m on the tail plus 2x₀(x₀ - x₁). -/
private lemma Dn_qform_peel (m : ℕ) (hm : 4 ≤ m) (x : Fin (m + 1) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj).mulVec x) =
    dotProduct (x ∘ Fin.succ)
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm).adj).mulVec (x ∘ Fin.succ)) +
    2 * x 0 ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ := by
  set C := (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
    (Etingof.DynkinType.D (m + 1) (by omega)).adj) with hC
  set C' := (2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
    (Etingof.DynkinType.D m hm).adj) with hC'
  -- Expand dotProduct and mulVec
  simp only [dotProduct, mulVec, Function.comp]
  -- Peel off i = 0 from outer sum
  rw [Fin.sum_univ_succ]
  -- Peel off j = 0 from each inner sum
  simp_rw [Fin.sum_univ_succ]
  -- Substitute Cartan entries
  simp only [hC, hC', Dn_cartan_zero_zero m hm, Dn_cartan_zero_succ m hm,
    Dn_cartan_succ_zero m hm, Dn_cartan_succ_succ m hm]
  -- The sum ∑_j (if j.val = 0 then -1 else 0) * x j.succ = -x 1
  -- Clean up the if-then-else sums
  simp only [ite_mul, zero_mul, neg_mul, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- Positive definiteness of the D_n Cartan form: q(x) > 0 for nonzero x. -/
private lemma Dn_posDef (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ) (hx : x ≠ 0) :
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.D n hn).adj).mulVec x) :=
  (Dn_isDynkin n hn).2.2.2.2 x hx

/-- All positive roots of D_n have each coordinate < 3.
    Proved by induction: peel off vertex 0, apply IH to D_{n-1}. -/
private lemma Dn_bound : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    Etingof.IsRoot n (Etingof.DynkinType.D n hn).adj x →
    (∀ i, 0 ≤ x i) → ∀ i, x i < 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x hr hp
    -- Base case: m + 1 = 4, i.e., m = 3
    by_cases hm4 : m = 3
    · subst hm4
      exact D4_bound x (by convert hr) hp
    -- Inductive case: m + 1 ≥ 5, so m ≥ 4
    · have hm' : 4 ≤ m := by omega
      -- Decompose: q_{D_{m+1}}(x) = q_{D_m}(y) + 2x₀(x₀-x₁) where y = x∘succ
      set y : Fin m → ℤ := x ∘ Fin.succ with hy_def
      have hpeel := Dn_qform_peel m hm' x
      have hq : dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
        (Etingof.DynkinType.D (m + 1) hm).adj).mulVec x) = 2 := hr.2
      -- q_{D_m}(y) = 2 - 2x₀(x₀ - x₁)
      set qy := dotProduct y ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm').adj).mulVec y) with hqy_def
      have hqy_val : qy = 2 - 2 * x 0 ^ 2 + 2 * x 0 * x ⟨1, by omega⟩ := by
        linarith [hpeel]
      -- y is non-negative
      have hpy : ∀ i, 0 ≤ y i := fun i => hp i.succ
      -- Case split on whether x₀ ≤ x₁ (= y₀)
      by_cases hle : x 0 ≤ y ⟨0, by omega⟩
      · -- x₀ ≤ x₁: then qy ≥ 2 (since 2x₀(x₁-x₀) ≥ 0 is added to 2)
        -- But qy is even and qy > 0 for y ≠ 0, so qy ≥ 2.
        -- Combined: qy = 2, so y is a D_m root.
        -- Also 2x₀(x₀-x₁) = 0, so either x₀ = 0 or x₀ = x₁.
        have hqy_ge : qy ≥ 2 := by
          rw [hqy_val]
          nlinarith [sq_nonneg (x 0), hp 0, hp ⟨1, by omega⟩]
        -- If y = 0, then x = (x₀, 0, ..., 0), which has q = 2x₀².
        -- From hr.2: 2x₀² = 2, so x₀ = ±1, and since x₀ ≥ 0, x₀ = 1.
        -- Then x = (1, 0, ..., 0), all coords < 3. ✓
        by_cases hy0 : y = 0
        · -- y = 0 means x₁ = ... = x_m = 0
          intro i
          by_cases hi : i = 0
          · subst hi
            -- x₀² contributes to qy = 0 via the peel identity
            -- From hpeel: 2 = 0 + 2x₀² - 0, so x₀² = 1, x₀ = 1
            have : qy = 0 := by
              rw [hqy_def, hy0]; simp [dotProduct, mulVec]
            rw [this] at hqy_val
            have : x 0 ^ 2 = 1 := by nlinarith
            have : x 0 ≤ 1 := by nlinarith [sq_nonneg (x 0 - 1), hp 0]
            omega
          · -- i > 0, so x i = y (i-1) = 0
            have : ∃ j : Fin m, i = j.succ := by
              refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
              ext; simp; omega
            obtain ⟨j, rfl⟩ := this
            have := congr_fun hy0 j
            simp [hy_def, Function.comp] at this
            simp [this]
        · -- y ≠ 0, so qy ≥ 2 (from PD: qy > 0, and qy is even)
          -- Actually qy ≥ 2 from hqy_ge. And qy ≤ 2? Not directly...
          -- But q_{D_{m+1}} = qy + 2x₀(x₀-x₁) = 2.
          -- Since x₀ ≤ x₁: 2x₀(x₀-x₁) ≤ 0, so qy = 2 - 2x₀(x₀-x₁) ≥ 2.
          -- But also: qy = 2 - 2x₀(x₀-x₁). Since q = qy + 2x₀(x₀-x₁) = 2:
          -- If qy > 2: then 2x₀(x₀-x₁) < 0, so x₀ > 0 and x₀ < x₁.
          -- qy must be even. If qy ≥ 4: 2x₀(x₀-x₁) = 2 - qy ≤ -2.
          -- But x₀(x₀-x₁) ≤ 0, so |x₀(x₁-x₀)| ≥ 1. And qy = 2 + 2x₀(x₁-x₀) ≤ 2.
          -- Wait: qy = 2 - 2x₀(x₀-x₁) = 2 + 2x₀(x₁-x₀). Since x₀≤x₁ and x₀≥0:
          -- 2x₀(x₁-x₀) ≥ 0. So qy ≥ 2.
          -- From q = 2: qy + 2x₀(x₀-x₁) = 2, so qy = 2 + 2x₀(x₁-x₀) ≥ 2.
          -- For qy = 2: need x₀(x₁-x₀) = 0, so x₀ = 0 or x₀ = x₁.
          -- For qy ≥ 4: q = qy + 2x₀(x₀-x₁) ≤ qy. But q = 2 < 4. Contradiction.
          have hqy_le : qy ≤ 2 := by linarith [mul_nonneg (hp 0) (by linarith : (0 : ℤ) ≤ y ⟨0, by omega⟩ - x 0)]
          have hqy_eq : qy = 2 := le_antisymm hqy_le hqy_ge
          -- So y is a root of D_m
          have hroot_y : Etingof.IsRoot m (Etingof.DynkinType.D m hm').adj y := ⟨hy0, hqy_eq⟩
          -- Apply IH
          have hbound_y := ih hm' y hroot_y hpy
          -- Also: qy = 2 means 2x₀(x₀-x₁) = 0
          have hx0_eq : x 0 * (x 0 - x ⟨1, by omega⟩) = 0 := by nlinarith
          intro i
          by_cases hi : i = 0
          · subst hi
            -- x₀ = 0 or x₀ = x₁. Either way x₀ ≤ x₁ = y₀ < 3.
            rcases mul_eq_zero.mp hx0_eq with h0 | h0
            · simp [h0]
            · have : x 0 = x ⟨1, by omega⟩ := by linarith
              rw [this]
              exact hbound_y ⟨0, by omega⟩
          · have : ∃ j : Fin m, i = j.succ := by
              refine ⟨⟨i.val - 1, by omega⟩, ?_⟩; ext; simp; omega
            obtain ⟨j, rfl⟩ := this
            exact hbound_y j
      · -- x₀ > x₁: then qy < 2.
        push_neg at hle
        -- qy = 2 - 2x₀(x₀-x₁) with x₀ > x₁ ≥ 0, so x₀ ≥ 1 and x₀-x₁ ≥ 1.
        -- Hence x₀(x₀-x₁) ≥ 1, so qy ≤ 0.
        -- By PD: qy > 0 for y ≠ 0, and qy ≥ 0 for y = 0.
        -- So qy ≤ 0 forces y = 0 and qy = 0.
        have hx0_pos : x 0 ≥ 1 := by
          have := hp 0; have : y ⟨0, by omega⟩ = x ⟨1, by omega⟩ := rfl
          omega
        have hdiff_pos : x 0 - x ⟨1, by omega⟩ ≥ 1 := by
          have : y ⟨0, by omega⟩ = x ⟨1, by omega⟩ := rfl; omega
        have hqy_le : qy ≤ 0 := by nlinarith
        -- y must be zero (otherwise PD gives qy > 0)
        have hy0 : y = 0 := by
          by_contra hy_ne
          have := Dn_posDef m hm' y hy_ne
          linarith
        -- qy = 0, so 2x₀(x₀-x₁) = 2, i.e., x₀(x₀-x₁) = 1.
        -- Since x₀ ≥ 1 and x₀-x₁ ≥ 1: x₀ = 1 and x₁ = 0.
        have hprod : x 0 * (x 0 - x ⟨1, by omega⟩) = 1 := by
          have : qy = 0 := by rw [hqy_def, hy0]; simp [dotProduct, mulVec]
          linarith [this, hqy_val]
        have hx0_eq : x 0 = 1 := by
          -- From a * b = 1 with a ≥ 1 and b ≥ 1 (integers): a = 1
          have h1 := hx0_pos
          have h2 := hdiff_pos
          nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℤ) ≤ x 0 - 1)]
        -- x = (1, 0, 0, ..., 0), all coords < 3
        intro i
        by_cases hi : i = 0
        · subst hi; simp [hx0_eq]
        · have : ∃ j : Fin m, i = j.succ := by
            refine ⟨⟨i.val - 1, by omega⟩, ?_⟩; ext; simp; omega
          obtain ⟨j, rfl⟩ := this
          have := congr_fun hy0 j
          simp [hy_def, Function.comp] at this; simp [this]

set_option linter.style.nativeDecide false in
private lemma D4_count :
    (rootCountFinset 4 (Etingof.DynkinType.D 4 le_rfl).adj 3).card = 12 := by
  native_decide

set_option linter.style.nativeDecide false in
private lemma D5_count :
    (rootCountFinset 5 (Etingof.DynkinType.D 5 (by omega)).adj 3).card = 20 := by
  native_decide

/-- Filtering rootCountFinset by v₀ = 0 and dropping the first coordinate
    gives a set with the same cardinality as rootCountFinset of D_m. -/
private lemma Dn_filter_zero_card (m : ℕ) (hm : 4 ≤ m) :
    ((rootCountFinset (m + 1) (Etingof.DynkinType.D (m + 1) (by omega)).adj 3).filter
      (fun v => v 0 = 0)).card =
    (rootCountFinset m (Etingof.DynkinType.D m hm).adj 3).card := by
  set S := (rootCountFinset (m + 1) (Etingof.DynkinType.D (m + 1) (by omega)).adj 3).filter
    (fun v => v 0 = 0)
  set T := rootCountFinset m (Etingof.DynkinType.D m hm).adj 3
  -- Define the map: drop first coordinate
  set f : (Fin (m + 1) → Fin 3) → (Fin m → Fin 3) := fun v i => v i.succ
  -- Define the inverse: prepend 0
  set g : (Fin m → Fin 3) → (Fin (m + 1) → Fin 3) := fun w => Fin.cons 0 w
  apply Finset.card_nbij' f g
  · -- MapsTo f S T
    intro v hv
    simp only [S, Finset.mem_filter] at hv
    obtain ⟨hvm, hv0⟩ := hv
    simp only [T, f, rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hvm
    obtain ⟨hne, hq⟩ := hvm
    constructor
    · intro h; apply hne; ext i
      by_cases hi : i = 0
      · subst hi; exact hv0
      · have : ∃ j : Fin m, i = j.succ := ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
        obtain ⟨j, rfl⟩ := this; exact congr_fun h j
    · have hpeel := Dn_qform_peel m hm (fun i => (v i : ℤ))
      simp only [Function.comp] at hpeel
      have hv0z : (v (0 : Fin (m + 1)) : ℤ) = 0 := by
        have := hv0; simp [Fin.ext_iff] at this; exact_mod_cast this
      rw [hq] at hpeel; simp [hv0z] at hpeel
      convert hpeel using 2; ext i; simp
  · -- MapsTo g T S
    intro w hw
    simp only [S, T, g, Finset.mem_filter]
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
    obtain ⟨hne, hq⟩ := hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h; apply hne; ext i
      have := congr_fun h i.succ; simp [Fin.cons] at this; exact this
    · have hpeel := Dn_qform_peel m hm
        (fun i => ((Fin.cons (0 : Fin 3) w : Fin (m + 1) → Fin 3) i : ℤ))
      simp only [Function.comp, Fin.cons_succ, Fin.cons_zero] at hpeel
      rw [hpeel]; simp; convert hq using 2; ext i; simp
    · simp [Fin.cons]
  · -- LeftInvOn: g ∘ f = id on S
    intro v hv
    simp only [S, Finset.mem_filter] at hv
    funext i; simp only [f, g]
    by_cases hi : i = 0
    · subst hi; simp [Fin.cons]; exact hv.2
    · have : ∃ j : Fin m, i = j.succ := ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
      obtain ⟨j, rfl⟩ := this; simp [Fin.cons]
  · -- RightInvOn: f ∘ g = id on T
    intro w _
    funext i; simp [f, g, Fin.cons]

/-- No D_n root has first coordinate equal to 2. -/
private lemma Dn_no_coord2_at_zero : ∀ (n : ℕ) (hn : 4 ≤ n) (v : Fin n → Fin 3),
    v ∈ rootCountFinset n (Etingof.DynkinType.D n hn).adj 3 →
    v 0 ≠ 2 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm v hv hv0
    by_cases hm4 : m = 3
    · subst hm4
      simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hne, hq⟩ := hv
      have h2 : (v (0 : Fin 4) : ℤ) = 2 := by
        have := hv0; simp [Fin.ext_iff] at this; exact_mod_cast this
      have hqv := D4_qf (fun i => (v i : ℤ))
      rw [hq] at hqv
      have hs := D4_sos (v 0 : ℤ) (v 1 : ℤ) (v 2 : ℤ) (v 3 : ℤ)
      rw [hqv] at hs
      nlinarith [sq_nonneg (2 * (v (2 : Fin 4) : ℤ) - (v (1 : Fin 4) : ℤ)),
        sq_nonneg (2 * (v (3 : Fin 4) : ℤ) - (v (1 : Fin 4) : ℤ)),
        sq_nonneg ((v (1 : Fin 4) : ℤ)),
        (v 1).isLt]
    · have hm' : 4 ≤ m := by omega
      simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hne, hq⟩ := hv
      have hpeel := Dn_qform_peel m hm' (fun i => (v i : ℤ))
      simp only [Function.comp] at hpeel
      set x : Fin (m + 1) → ℤ := fun i => (v i : ℤ) with hx_def
      have hv0z : x 0 = 2 := by
        have := hv0; simp [hx_def, Fin.ext_iff] at this ⊢; exact_mod_cast this
      rw [hq] at hpeel
      set y := fun i : Fin m => x i.succ with hy_def
      have hqy : dotProduct y ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm').adj).mulVec y) = 4 * x ⟨1, by omega⟩ - 6 := by
        linarith [hpeel, hv0z]
      by_cases hy0 : y = 0
      · have : dotProduct y ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.D m hm').adj).mulVec y) = 0 := by
          rw [hy0]; simp [dotProduct, mulVec]
        linarith [(v ⟨1, by omega⟩).zero_le]
      · have hpd := Dn_posDef m hm' y hy0
        have hx1_bound : x ⟨1, by omega⟩ < 3 := by
          have := (v ⟨1, by omega⟩).isLt; simp [hx_def]; omega
        have hx1_eq : x ⟨1, by omega⟩ = 2 := by omega
        have hqy2 : dotProduct y ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.D m hm').adj).mulVec y) = 2 := by linarith
        have hy_root : (fun i : Fin m => v i.succ) ∈
            rootCountFinset m (Etingof.DynkinType.D m hm').adj 3 := by
          simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · intro h; apply hy0; ext i
            have := congr_fun h i; simp [hy_def, hx_def] at this ⊢; exact_mod_cast this
          · convert hqy2 using 2; ext i; simp [hy_def, hx_def]
        have hy0_eq : (fun i : Fin m => v i.succ) 0 = 2 := by
          show v (Fin.succ 0) = 2
          ext; simp; have := hx1_eq; simp [hx_def] at this; omega
        exact ih hm' _ hy_root hy0_eq

/-- Count of vectors with v₀ = 2, q_{D_n} = 4, all coords in Fin 3. -/
private def qFourFinset (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Finset (Fin n → Fin 3) :=
  (Finset.univ : Finset (Fin n → Fin 3)).filter fun v =>
    v 0 = 2 &&
    decide (dotProduct (fun i => (v i : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun i => (v i : ℤ))) = 4)

set_option linter.style.nativeDecide false in
private lemma D4_qfour :
    (qFourFinset 4 (Etingof.DynkinType.D 4 le_rfl).adj).card = 1 := by
  native_decide

/-- The q=4 count satisfies a recurrence: peeling off vertex 0. -/
private lemma qFourFinset_peel (m : ℕ) (hm : 4 ≤ m) :
    (qFourFinset (m + 1) (Etingof.DynkinType.D (m + 1) (by omega)).adj).card =
    (qFourFinset m (Etingof.DynkinType.D m hm).adj).card := by
  set S := qFourFinset (m + 1) (Etingof.DynkinType.D (m + 1) (by omega)).adj
  set T := qFourFinset m (Etingof.DynkinType.D m hm).adj
  set f : (Fin (m + 1) → Fin 3) → (Fin m → Fin 3) := fun v i => v i.succ
  set g : (Fin m → Fin 3) → (Fin (m + 1) → Fin 3) := fun w => Fin.cons 2 w
  apply Finset.card_nbij' f g
  · -- MapsTo f S T
    intro v hv
    simp only [S, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq, Bool.decide_and] at hv ⊢
    obtain ⟨hv0, hq⟩ := hv
    have hpeel := Dn_qform_peel m hm (fun i => (v i : ℤ))
    simp only [Function.comp] at hpeel
    have hv0z : (v (0 : Fin (m + 1)) : ℤ) = 2 := by
      have := hv0; simp [Fin.ext_iff] at this; exact_mod_cast this
    -- Need tail₀ = v₁ = 2 and q_tail = 4
    -- From peel: 4 = q_tail + 2·4 - 2·2·v₁ = q_tail + 8 - 4v₁
    -- So q_tail = 4v₁ - 4
    have hqy : dotProduct (fun i : Fin m => (v i.succ : ℤ))
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm).adj).mulVec (fun i => (v i.succ : ℤ))) =
      4 * (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) - 4 := by linarith [hpeel, hv0z, hq]
    by_cases hy0 : (fun i : Fin m => (v i.succ : ℤ)) = 0
    · exfalso
      have := congr_fun hy0 0; simp at this
      have : dotProduct (fun i : Fin m => (v i.succ : ℤ))
        ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.D m hm).adj).mulVec (fun i => (v i.succ : ℤ))) = 0 := by
        rw [hy0]; simp [dotProduct, mulVec]
      linarith [(v ⟨1, by omega⟩).zero_le]
    · have hpd := Dn_posDef m hm _ hy0
      have hv1_bound : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) < 3 := by
        have := (v ⟨1, by omega⟩).isLt; omega
      constructor
      · ext; simp
        have : 4 * (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) - 4 > 0 := by linarith
        have : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) ≥ 2 := by omega
        have : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) = 2 := by omega
        omega
      · convert show dotProduct (fun i : Fin m => (v i.succ : ℤ))
            ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
              (Etingof.DynkinType.D m hm).adj).mulVec
                (fun i : Fin m => (v i.succ : ℤ))) = 4 by
            have : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) = 2 := by omega
            linarith
          using 2 <;> ext i <;> simp
  · -- MapsTo g T S
    intro w hw
    simp only [S, T, g, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq, Bool.decide_and] at hw ⊢
    obtain ⟨hw0, hqw⟩ := hw
    constructor
    · simp [Fin.cons]
    · have hpeel := Dn_qform_peel m hm
        (fun i => ((Fin.cons (2 : Fin 3) w : Fin (m + 1) → Fin 3) i : ℤ))
      simp only [Function.comp, Fin.cons_succ, Fin.cons_zero] at hpeel
      rw [hpeel]
      have hw0z : (w 0 : ℤ) = 2 := by exact_mod_cast congr_arg Fin.val hw0
      simp [hw0z]; linarith
  · -- LeftInvOn
    intro v hv
    simp only [S, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    funext i; simp only [f, g]
    by_cases hi : i = 0
    · subst hi; simp [Fin.cons]; exact hv.1
    · have : ∃ j : Fin m, i = j.succ := ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
      obtain ⟨j, rfl⟩ := this; simp [Fin.cons]
  · -- RightInvOn
    intro w _
    funext i; simp [f, g, Fin.cons]

/-- The qFourFinset cardinality is always 1. -/
private lemma qFourFinset_card (m : ℕ) (hm : 4 ≤ m) :
    (qFourFinset m (Etingof.DynkinType.D m hm).adj).card = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm4 : m = 3
    · subst hm4; exact D4_qfour
    · have hm' : 4 ≤ m := by omega
      rw [qFourFinset_peel m hm', ih hm']

/-- The D_n root count equals n*(n-1). -/
private lemma Dn_count : ∀ (n : ℕ) (hn : 4 ≤ n),
    (rootCountFinset n (Etingof.DynkinType.D n hn).adj 3).card =
      n * (n - 1) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm
    by_cases hm4 : m = 3
    · subst hm4; exact D4_count
    · by_cases hm5 : m = 4
      · subst hm5; exact D5_count
      · -- m ≥ 5, so m ≥ 4 and m-1 ≥ 4
        have hm' : 4 ≤ m := by omega
        have hm'' : 4 ≤ m - 1 := by omega
        -- Split rootCountFinset(D_{m+1}) by v₀
        set S := rootCountFinset (m + 1) (Etingof.DynkinType.D (m + 1) (by omega)).adj 3
        set S0 := S.filter (fun v => v 0 = 0)
        set S1 := S.filter (fun v => v 0 = 1)
        set S2 := S.filter (fun v => v 0 = 2)
        -- S = S0 ∪ S1 ∪ S2
        have hpart : S.card = S0.card + S1.card + S2.card := by
          have hcover : S = S0 ∪ S1 ∪ S2 := by
            ext v; simp only [S0, S1, S2, Finset.mem_filter, Finset.mem_union]
            constructor
            · intro hv
              have h0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by
                have := (v 0).isLt; omega
              rcases h0 with h0 | h0 | h0 <;> simp_all
            · intro hv; rcases hv with ((hv | hv) | hv) <;> exact hv.1
          have hd01 : Disjoint S0 S1 :=
            Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all)
          have hd012 : Disjoint (S0 ∪ S1) S2 := by
            rw [Finset.disjoint_union_left]
            exact ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all),
                   Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all)⟩
          rw [hcover, Finset.card_union_of_disjoint hd012,
              Finset.card_union_of_disjoint hd01]
        -- S₂ = ∅ (no D_n root has first coordinate 2)
        have hS2 : S2.card = 0 := by
          rw [Finset.card_eq_zero]
          ext v; simp only [S2, Finset.mem_filter, Finset.mem_empty, iff_false, not_and]
          intro hv hv0
          exact Dn_no_coord2_at_zero (m + 1) (by omega) v hv hv0
        -- S₀ card = D_m count = m(m-1)
        have hS0 : S0.card = m * (m - 1) := by
          rw [show S0 = (rootCountFinset (m + 1)
            (Etingof.DynkinType.D (m + 1) (by omega)).adj 3).filter
              (fun v => v 0 = 0) from rfl,
            Dn_filter_zero_card m hm', ih hm']
        -- Split S₁ by v₁
        set S10 := S1.filter (fun v => (v ⟨1, by omega⟩ : Fin 3) = 0)
        set S11 := S1.filter (fun v => (v ⟨1, by omega⟩ : Fin 3) = 1)
        set S12 := S1.filter (fun v => (v ⟨1, by omega⟩ : Fin 3) = 2)
        have hS1_split : S1.card = S10.card + S11.card + S12.card := by
          have hcover : S1 = S10 ∪ S11 ∪ S12 := by
            ext v; simp only [S10, S11, S12, Finset.mem_filter, Finset.mem_union]
            constructor
            · intro hv
              have h1 : v ⟨1, by omega⟩ = 0 ∨ v ⟨1, by omega⟩ = 1 ∨ v ⟨1, by omega⟩ = 2 := by
                have := (v ⟨1, by omega⟩).isLt; omega
              rcases h1 with h1 | h1 | h1 <;> simp_all
            · intro hv; rcases hv with ((hv | hv) | hv) <;> exact hv.1
          have hd1 : Disjoint S10 S11 :=
            Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all)
          have hd2 : Disjoint (S10 ∪ S11) S12 := by
            rw [Finset.disjoint_union_left]
            exact ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all),
                   Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all)⟩
          rw [hcover, Finset.card_union_of_disjoint hd2,
              Finset.card_union_of_disjoint hd1]
        -- S₁₀ card = 1 (only (1, 0, ..., 0))
        have hS10 : S10.card = 1 := by
          rw [Finset.card_eq_one]
          use fun i => if i = 0 then 1 else 0
          ext v
          simp only [S10, S1, S, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · intro ⟨⟨hv, hv0⟩, hv1⟩
            simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.and_eq_true, decide_eq_true_eq] at hv
            obtain ⟨hne, hq⟩ := hv
            have hno2 := Dn_no_coord2_at_zero (m + 1) (by omega) v
              (by simp [rootCountFinset, Finset.mem_filter, Finset.mem_univ, hne, hq])
            have hv0_eq : (v 0 : ℤ) = 1 := by
              have := (v 0).isLt; have := hv0; have := hno2
              have : (v 0 : Fin 3) ≠ 0 := hv0
              have : (v 0 : Fin 3) ≠ 2 := hno2
              omega
            have hv1_eq : (v ⟨1, by omega⟩ : ℤ) = 0 := by
              have := hv1; simp [Fin.ext_iff] at this; exact_mod_cast this
            set x : Fin (m + 1) → ℤ := fun i => (v i : ℤ)
            set y : Fin m → ℤ := fun i => x i.succ
            have hpeel := Dn_qform_peel m hm' x
            have hcomp : x ∘ Fin.succ = y := rfl
            rw [hcomp] at hpeel; rw [hq] at hpeel
            set qy := dotProduct y ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
              (Etingof.DynkinType.D m hm').adj).mulVec y)
            have hqy : qy = 0 := by show dotProduct _ _ = 0; nlinarith
            have hy0 : y = 0 := by
              by_contra h
              have := Dn_posDef m hm' y h
              linarith
            funext i
            by_cases hi : i = 0
            · subst hi
              ext; simp; omega
            · have : ∃ j : Fin m, i = j.succ :=
                ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
              obtain ⟨j, rfl⟩ := this
              have hyj : y j = 0 := congr_fun hy0 j
              simp [y, x] at hyj
              simp [show ¬(Fin.succ j = (0 : Fin (m + 1))) from Fin.succ_ne_zero j]
              ext; omega
          · intro heq; subst heq
            set w : Fin (m + 1) → Fin 3 := fun i => if i = 0 then 1 else 0
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
                Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · intro h; have := congr_fun h (0 : Fin (m + 1)); simp [w] at this
              · have hpeel := Dn_qform_peel m hm' (fun i => (w i : ℤ))
                simp only [Function.comp] at hpeel
                have htail : ∀ i : Fin m, (w i.succ : ℤ) = 0 := by
                  intro i; simp [w, Fin.succ_ne_zero]
                have hw0 : (w (0 : Fin (m + 1)) : ℤ) = 1 := by simp [w]
                have hw1 : (w (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) = 0 := by
                  simp [w]; intro h; exact absurd h (by ext; simp; omega)
                rw [show (fun i : Fin m => (w i.succ : ℤ)) = (fun _ => (0 : ℤ)) from
                  funext htail] at hpeel
                simp [dotProduct, mulVec] at hpeel
                nlinarith
            · simp [w]
            · show (fun i => if i = 0 then (1 : Fin 3) else 0) ⟨1, by omega⟩ = 0
              simp; intro h; exact absurd h (by ext; simp; omega)
        -- S₁₁ card: bijection with D_m roots having v₀ = 1
        have hS11 : S11.card = 2 * (m - 1) := by
          have hbij : S11.card = ((rootCountFinset m (Etingof.DynkinType.D m hm').adj 3).filter
              (fun w => w 0 = 1)).card := by
            set T' := (rootCountFinset m (Etingof.DynkinType.D m hm').adj 3).filter
              (fun w => w 0 = 1)
            set f' : (Fin (m + 1) → Fin 3) → (Fin m → Fin 3) := fun v i => v i.succ
            set g' : (Fin m → Fin 3) → (Fin (m + 1) → Fin 3) := fun w => Fin.cons 1 w
            apply Finset.card_nbij' f' g'
            · -- MapsTo f' S11 T'
              intro v hv
              simp only [S11, S1, S, T', Finset.mem_filter, rootCountFinset,
                Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
              obtain ⟨⟨⟨hne, hq⟩, hv0⟩, hv1⟩ := hv
              have hno2 := Dn_no_coord2_at_zero (m + 1) (by omega) v
                (by simp [rootCountFinset, Finset.mem_filter, Finset.mem_univ, hne, hq])
              have hv0_eq : (v (0 : Fin (m + 1)) : ℤ) = 1 := by
                have := (v 0).isLt; omega
              have hv1_eq : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) = 1 := by
                have := hv1; simp [Fin.ext_iff] at this; exact_mod_cast this
              have hpeel := Dn_qform_peel m hm' (fun i => (v i : ℤ))
              simp only [Function.comp] at hpeel
              rw [hq] at hpeel
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · intro h; apply hne; ext i
                by_cases hi : i = 0
                · subst hi; ext; simp; omega
                · have : ∃ j : Fin m, i = j.succ :=
                    ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
                  obtain ⟨j, rfl⟩ := this; exact congr_fun h j
              · convert show dotProduct (fun i : Fin m => (v i.succ : ℤ))
                  ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
                    (Etingof.DynkinType.D m hm').adj).mulVec
                      (fun i : Fin m => (v i.succ : ℤ))) = 2 by
                    linarith [hv0_eq, hv1_eq]
                  using 2 <;> ext i <;> simp
              · ext; simp; omega
            · -- MapsTo g' T' S11
              intro w hw
              simp only [S11, S1, S, T', Finset.mem_filter, rootCountFinset,
                Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
              obtain ⟨⟨hne, hq⟩, hw0⟩ := hw
              refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
              · intro h; apply hne; ext i
                have := congr_fun h i.succ; simp [Fin.cons] at this; exact this
              · have hpeel := Dn_qform_peel m hm'
                  (fun i => ((Fin.cons (1 : Fin 3) w : Fin (m+1) → Fin 3) i : ℤ))
                simp only [Function.comp, Fin.cons_succ, Fin.cons_zero] at hpeel
                rw [hpeel]
                have hw0z : (w 0 : ℤ) = 1 := by exact_mod_cast congr_arg Fin.val hw0
                simp [hw0z]; linarith
              · simp [Fin.cons]
              · show Fin.cons 1 w ⟨1, by omega⟩ = 1
                simp [Fin.cons, show (⟨1, by omega⟩ : Fin (m + 1)) = Fin.succ ⟨0, by omega⟩
                  from by ext; simp]
                exact hw0
            · -- LeftInvOn
              intro v hv
              simp only [S11, S1, Finset.mem_filter] at hv
              funext i; simp only [f', g']
              by_cases hi : i = 0
              · subst hi; simp [Fin.cons]
                have hno2 := Dn_no_coord2_at_zero (m + 1) (by omega) v (by exact hv.1.1)
                have hv0ne := hv.1.2; have := (v 0).isLt
                ext; omega
              · have : ∃ j : Fin m, i = j.succ :=
                  ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
                obtain ⟨j, rfl⟩ := this; simp [Fin.cons]
            · -- RightInvOn
              intro w _; funext i; simp [f', g', Fin.cons]
          rw [hbij]
          -- |{w ∈ D_m roots | w₀ = 1}| = |D_m roots| - |w₀ = 0| - |w₀ = 2|
          have hsplit : (rootCountFinset m (Etingof.DynkinType.D m hm').adj 3).card =
              ((rootCountFinset m _ 3).filter (fun w => w 0 = 0)).card +
              ((rootCountFinset m _ 3).filter (fun w => w 0 = 1)).card +
              ((rootCountFinset m _ 3).filter (fun w => w 0 = 2)).card := by
            have hcover : rootCountFinset m (Etingof.DynkinType.D m hm').adj 3 =
                (rootCountFinset m _ 3).filter (fun w => w 0 = 0) ∪
                (rootCountFinset m _ 3).filter (fun w => w 0 = 1) ∪
                (rootCountFinset m _ 3).filter (fun w => w 0 = 2) := by
              ext w; simp only [Finset.mem_filter, Finset.mem_union]
              constructor
              · intro hw
                have h0 : w 0 = 0 ∨ w 0 = 1 ∨ w 0 = 2 := by
                  have := (w 0).isLt; omega
                rcases h0 with h0 | h0 | h0 <;> simp_all
              · intro hw; rcases hw with ((hw | hw) | hw) <;> exact hw.1
            rw [hcover,
              Finset.card_union_of_disjoint (by rw [Finset.disjoint_union_left]; exact
                ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all),
                 Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all)⟩),
              Finset.card_union_of_disjoint
                (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp_all))]
          have hno2 : ((rootCountFinset m (Etingof.DynkinType.D m hm').adj 3).filter
              (fun w => w 0 = 2)).card = 0 := by
            rw [Finset.card_eq_zero]; ext w
            simp only [Finset.mem_filter, Finset.mem_empty, iff_false, not_and]
            intro hw hw0; exact Dn_no_coord2_at_zero m hm' w hw hw0
          have hfilt0 : ((rootCountFinset m (Etingof.DynkinType.D m hm').adj 3).filter
              (fun w => w 0 = 0)).card = (m - 1) * (m - 2) := by
            rw [show m = (m - 1) + 1 from by omega] at hm' ⊢
            rw [Dn_filter_zero_card (m - 1) hm'', ih hm'']
          have hfm := ih hm'
          omega
        -- S₁₂ card = 1 (bijection with qFourFinset)
        have hS12 : S12.card = 1 := by
          have hbij : S12.card = (qFourFinset m (Etingof.DynkinType.D m hm').adj).card := by
            set T' := qFourFinset m (Etingof.DynkinType.D m hm').adj
            set f' : (Fin (m + 1) → Fin 3) → (Fin m → Fin 3) := fun v i => v i.succ
            set g' : (Fin m → Fin 3) → (Fin (m + 1) → Fin 3) := fun w => Fin.cons 1 w
            apply Finset.card_nbij' f' g'
            · -- MapsTo f' S12 T'
              intro v hv
              simp only [S12, S1, S, T', Finset.mem_filter, rootCountFinset, qFourFinset,
                Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
                Bool.decide_and] at hv ⊢
              obtain ⟨⟨⟨hne, hq⟩, hv0⟩, hv1⟩ := hv
              have hno2 := Dn_no_coord2_at_zero (m + 1) (by omega) v
                (by simp [rootCountFinset, Finset.mem_filter, Finset.mem_univ, hne, hq])
              have hv0_eq : (v (0 : Fin (m + 1)) : ℤ) = 1 := by
                have := (v 0).isLt; omega
              have hv1_eq : (v (⟨1, by omega⟩ : Fin (m + 1)) : ℤ) = 2 := by
                have := hv1; simp [Fin.ext_iff] at this; exact_mod_cast this
              have hpeel := Dn_qform_peel m hm' (fun i => (v i : ℤ))
              simp only [Function.comp] at hpeel
              rw [hq] at hpeel
              constructor
              · ext; simp; omega
              · convert show dotProduct (fun i : Fin m => (v i.succ : ℤ))
                  ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
                    (Etingof.DynkinType.D m hm').adj).mulVec
                      (fun i : Fin m => (v i.succ : ℤ))) = 4 by
                    linarith [hv0_eq, hv1_eq]
                  using 2 <;> ext i <;> simp
            · -- MapsTo g' T' S12
              intro w hw
              simp only [S12, S1, S, T', Finset.mem_filter, rootCountFinset, qFourFinset,
                Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
                Bool.decide_and] at hw ⊢
              obtain ⟨hw0, hqw⟩ := hw
              refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
              · intro h
                have := congr_fun h 0; simp [Fin.cons] at this
              · have hpeel := Dn_qform_peel m hm'
                  (fun i => ((Fin.cons (1 : Fin 3) w : Fin (m+1) → Fin 3) i : ℤ))
                simp only [Function.comp, Fin.cons_succ, Fin.cons_zero] at hpeel
                rw [hpeel]
                have hw0z : (w 0 : ℤ) = 2 := by exact_mod_cast congr_arg Fin.val hw0
                simp [hw0z]; linarith
              · simp [Fin.cons]
              · show Fin.cons 1 w ⟨1, by omega⟩ = 2
                simp [Fin.cons, show (⟨1, by omega⟩ : Fin (m + 1)) = Fin.succ ⟨0, by omega⟩
                  from by ext; simp]
                exact hw0
            · -- LeftInvOn
              intro v hv
              simp only [S12, S1, Finset.mem_filter] at hv
              funext i; simp only [f', g']
              by_cases hi : i = 0
              · subst hi; simp [Fin.cons]
                have hno2 := Dn_no_coord2_at_zero (m + 1) (by omega) v (by exact hv.1.1.1)
                have hv0ne := hv.1.1.2; have := (v 0).isLt
                ext; omega
              · have : ∃ j : Fin m, i = j.succ :=
                  ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
                obtain ⟨j, rfl⟩ := this; simp [Fin.cons]
            · -- RightInvOn
              intro w _; funext i; simp [f', g', Fin.cons]
          rw [hbij, qFourFinset_card m hm']
        -- Combine
        rw [hpart, hS0, hS1_split, hS10, hS11, hS12, hS2]
        omega

private lemma Dn_result (n : ℕ) (hn : 4 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj) =
      n * (n - 1) := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq (Dn_bound n hn)
  exact ⟨hfin, hcard ▸ Dn_count n hn⟩

end DnRootCount

/-- The number of positive roots for Dₙ is n(n-1).
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_Dn (n : ℕ) (hn : 4 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj) =
      n * (n - 1) :=
  Dn_result n hn
