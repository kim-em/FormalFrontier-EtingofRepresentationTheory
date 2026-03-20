import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification

/-!
# Example 6.4.9: A_n Root Count

The positive roots of A_n are exactly the "interval indicator" vectors: 1 on a
contiguous block [a, b] and 0 elsewhere, for 0 ≤ a ≤ b < n. There are n(n+1)/2
such intervals.
-/

section AnRootCount

open Matrix Finset

/-- The Cartan matrix entry for A_n at (k, j). -/
private lemma An_cartan_entry (n : ℕ) (hn : 1 ≤ n) (k j : Fin n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - (Etingof.DynkinType.A n hn).adj) k j =
    if k = j then 2
    else if (k.val + 1 = j.val) ∨ (j.val + 1 = k.val) then -1
    else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Etingof.DynkinType.adj, smul_eq_mul]
  split_ifs with h1 h2 <;> simp_all [Fin.ext_iff] <;> omega

/-- Decomposition: q_{m+1}(x) = q_m(x|_{0..m-1}) + 2x_m² - 2x_{m-1}·x_m. -/
private lemma An_qform_peel (m : ℕ) (hm : 1 ≤ m) (x : Fin (m + 1) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.A (m + 1) (by omega)).adj).mulVec x) =
    dotProduct (fun i : Fin m => x ⟨i.val, by omega⟩)
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.A m hm).adj).mulVec (fun i : Fin m => x ⟨i.val, by omega⟩)) +
    2 * x ⟨m, by omega⟩ ^ 2 - 2 * x ⟨m - 1, by omega⟩ * x ⟨m, by omega⟩ := by
  simp only [dotProduct, mulVec, An_cartan_entry]
  -- Split outer and inner sums: ∑_{Fin(m+1)} = ∑_{Fin m} ∘ castSucc + last
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  -- Simplify castSucc vs last comparisons
  simp only [Fin.castSucc_inj, Fin.val_castSucc, Fin.val_last]
  -- castSucc i ≠ last m, and last m ≠ castSucc i
  have : ∀ i : Fin m, (i.castSucc = Fin.last m) = False :=
    fun i => eq_false (Fin.castSucc_ne_last i)
  have : ∀ i : Fin m, (Fin.last m = i.castSucc) = False :=
    fun i => eq_false ((Fin.castSucc_ne_last i).symm)
  simp only [*, eq_self_iff_true, ite_true, ite_false]
  -- m + 1 = i.val impossible for i : Fin m
  simp only [show ∀ i : Fin m, (m + 1 = i.val) = False from fun i => by
    exact eq_false (by omega)]
  simp only [false_or]
  simp only [or_false]
  -- Convert castSucc/last to val-based indexing
  have hcast : ∀ i : Fin m, x i.castSucc = x ⟨i.val, by omega⟩ :=
    fun i => congrArg x (Fin.ext rfl)
  have hlast : x (Fin.last m) = x ⟨m, by omega⟩ :=
    congrArg x (Fin.ext rfl)
  simp_rw [hcast, hlast]
  -- Distribute multiplication over addition in the outer sum
  simp only [mul_add, Finset.sum_add_distrib]
  -- The adjacency-to-m sums pick out x_{m-1}
  have hm' : m - 1 < m := by omega
  -- Rewrite adjacency condition i.val + 1 = m as i = ⟨m-1, ...⟩
  have hadj : ∀ i : Fin m, (i.val + 1 = m) = (i = ⟨m - 1, hm'⟩) := by
    intro i; apply propext; constructor
    · intro h; ext; simp only [Fin.val_mk]; omega
    · intro h; subst h; simp only [Fin.val_mk]; omega
  simp_rw [hadj]
  -- Evaluate sums with ite_eq: ∑ i, (if i = a then c else 0) * f i = c * f a
  simp only [mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The quadratic form q(x) ≥ x₀² + x_{n-1}² for A_n. -/
private lemma An_qform_ge_endpoints : ∀ (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ),
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.A n hn).adj).mulVec x) ≥
    x ⟨0, by omega⟩ ^ 2 + x ⟨n - 1, by omega⟩ ^ 2 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn x
    by_cases hm : m = 0
    · -- n = 1: q(x) = 2x₀² = x₀² + x₀²
      subst hm
      show _ ≥ x 0 ^ 2 + x 0 ^ 2
      simp only [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [sq]
      ring_nf
      omega
    · -- n ≥ 2: use decomposition + IH
      have hm1 : 1 ≤ m := by omega
      rw [An_qform_peel m hm1 x]
      have hih := ih hm1 (fun i : Fin m => x ⟨i.val, by omega⟩)
      -- IH: q_m(x|_m) ≥ x₀² + x_{m-1}²
      -- Goal: q_m + 2x_m² - 2x_{m-1}x_m ≥ x₀² + x_m²
      -- From IH: ≥ x₀² + x_{m-1}² + 2x_m² - 2x_{m-1}x_m
      --        = x₀² + (x_{m-1} - x_m)² + x_m² ≥ x₀² + x_m²
      -- Simplify the goal: (m+1)-1 = m
      show _ ≥ x ⟨0, by omega⟩ ^ 2 + x ⟨m, by omega⟩ ^ 2
      nlinarith [sq_nonneg (x ⟨m - 1, by omega⟩ - x ⟨m, by omega⟩),
        show x ⟨(Fin.mk (m - 1) (by omega) : Fin m).val, by omega⟩ =
          x ⟨m - 1, by omega⟩ from rfl]

/-- If the A_n quadratic form vanishes on a nonneg vector, the vector is zero. -/
private lemma An_qform_zero : ∀ (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ),
    (∀ i, 0 ≤ x i) →
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.A n hn).adj).mulVec x) = 0 →
    x = 0 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn x hpos hq
    by_cases hm : m = 0
    · -- n = 1: 2x₀² = 0 → x₀ = 0
      subst hm
      have hx0 : x ⟨0, by omega⟩ = 0 := by
        have h := hq
        simp only [dotProduct, mulVec, An_cartan_entry, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
        norm_num at h
        exact h
      ext ⟨i, hi⟩; simp only [Pi.zero_apply]
      have : i = 0 := by omega
      subst this; exact hx0
    · -- n ≥ 2: use peel + induction
      have hm1 : 1 ≤ m := by omega
      rw [An_qform_peel m hm1 x] at hq
      set x' := fun i : Fin m => x ⟨i.val, by omega⟩ with hx'
      have hpos' : ∀ i, 0 ≤ x' i := fun i => hpos ⟨i.val, by omega⟩
      have hge := An_qform_ge_endpoints m hm1 x'
      have hqm_nonneg : dotProduct x' ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.A m hm1).adj).mulVec x') ≥ 0 := by
        linarith [sq_nonneg (x' ⟨0, by omega⟩), sq_nonneg (x' ⟨m - 1, by omega⟩)]
      have hxm := hpos ⟨m, by omega⟩
      have hxm1 := hpos ⟨m - 1, by omega⟩
      by_cases hxm_zero : x ⟨m, by omega⟩ = 0
      · -- x_m = 0: q_m(x') = 0, by IH x' = 0
        have hqm_zero : dotProduct x' ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (Etingof.DynkinType.A m hm1).adj).mulVec x') = 0 := by nlinarith [hxm_zero]
        have hx'_zero := ih hm1 x' hpos' hqm_zero
        ext i
        by_cases hi : i.val < m
        · have := congr_fun hx'_zero ⟨i.val, hi⟩
          simp only [Pi.zero_apply] at this
          have : x ⟨i.val, by omega⟩ = 0 := this
          rwa [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl] at this
        · have : i.val = m := by omega
          rw [show i = ⟨m, by omega⟩ from Fin.ext this]
          exact hxm_zero
      · -- x_m ≥ 1: contradiction
        exfalso
        have hxm_pos : x ⟨m, by omega⟩ ≥ 1 := by omega
        have hle : x ⟨m, by omega⟩ ≤ x ⟨m - 1, by omega⟩ := by nlinarith
        have hqm_zero : dotProduct x' ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (Etingof.DynkinType.A m hm1).adj).mulVec x') = 0 := by nlinarith
        have hx'_zero := ih hm1 x' hpos' hqm_zero
        have : x' ⟨m - 1, by omega⟩ = 0 := by
          have := congr_fun hx'_zero ⟨m - 1, by omega⟩; simpa using this
        simp only [hx'] at this
        omega

/-- No nonneg vector with q = 4, x_0 = 0, x_{m-1} = 2 exists for A_m. -/
private lemma An_qform_no_double : ∀ (m : ℕ) (hm : 1 ≤ m) (x : Fin m → ℤ),
    (∀ i, 0 ≤ x i) →
    x ⟨0, by omega⟩ = 0 →
    x ⟨m - 1, by omega⟩ = 2 →
    dotProduct x ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
      (Etingof.DynkinType.A m hm).adj).mulVec x) ≠ 4 := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ k ih =>
    intro hk x hpos hx0 hxk hq
    by_cases hk0 : k = 0
    · -- m = 1: q(x) = 2x₀² = 0, not 4
      subst hk0
      simp only [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero] at hq
      norm_num at hq; linarith [hx0]
    · -- m ≥ 2: peel and cascade
      have hk1 : 1 ≤ k := by omega
      rw [An_qform_peel k hk1 x] at hq
      set x' := fun i : Fin k => x ⟨i.val, by omega⟩
      have hpos' : ∀ i, 0 ≤ x' i := fun i => hpos ⟨i.val, by omega⟩
      have hge := An_qform_ge_endpoints k hk1 x'
      set r := dotProduct x' ((2 • (1 : Matrix (Fin k) (Fin k) ℤ) -
          (Etingof.DynkinType.A k hk1).adj).mulVec x')
      -- x_{k} = x_{m-1} = 2 (since m = k+1, m-1 = k)
      have hxk_val : x ⟨k, by omega⟩ = 2 := by
        have := hxk; simp only [show k + 1 - 1 = k from by omega] at this; exact this
      -- r = 4·x_{k-1} - 4 from the peel equation
      have hr_eq : r = 4 * x ⟨k - 1, by omega⟩ - 4 := by nlinarith [hxk_val]
      -- x'_0 = x_0 = 0
      have hx'0 : x' ⟨0, by omega⟩ = 0 := hx0
      -- r ≥ x'_0² + x'_{k-1}² = 0 + x_{k-1}²
      -- So x_{k-1}² ≤ 4·x_{k-1} - 4, (x_{k-1} - 2)² ≤ 0, x_{k-1} = 2
      have hxk1_sq : x ⟨k - 1, by omega⟩ ^ 2 ≤ 4 * x ⟨k - 1, by omega⟩ - 4 := by
        have : x ⟨(Fin.mk (k - 1) (by omega) : Fin k).val, by omega⟩ =
            x ⟨k - 1, by omega⟩ := rfl
        nlinarith [sq_nonneg (x ⟨0, by omega⟩)]
      have hxk1_val : x ⟨k - 1, by omega⟩ = 2 := by
        nlinarith [sq_nonneg (x ⟨k - 1, by omega⟩ - 2), hpos ⟨k - 1, by omega⟩]
      have hr4 : r = 4 := by nlinarith [hxk1_val]
      -- x'_{k-1} = x_{k-1} = 2
      have hx'k1 : x' ⟨k - 1, by omega⟩ = 2 := hxk1_val
      exact ih hk1 x' hpos' hx'0 hx'k1 hr4

/-- All positive roots of A_n have each coordinate < 2. -/
private lemma An_bound (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ)
    (hr : Etingof.IsRoot n (Etingof.DynkinType.A n hn).adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 2 := by
  have hq := hr.2
  have hne := hr.1
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · -- n = 1: 2x₀² = 2, x₀ = 1 < 2
      subst hm
      have hx0_bound : x 0 < 2 := by
        have h := hq
        simp only [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply,
          Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero] at h
        norm_num at h
        have hp0 : 0 ≤ x 0 := hp 0
        nlinarith [sq_nonneg (x 0 - 1)]
      intro i; have : i = 0 := Fin.ext (by omega); rw [this]; exact hx0_bound
    · have hm1 : 1 ≤ m := by omega
      rw [An_qform_peel m hm1 x] at hq
      set x' := fun i : Fin m => x ⟨i.val, by omega⟩ with hx'
      have hpos' : ∀ i, 0 ≤ x' i := fun i => hp ⟨i.val, by omega⟩
      have hge := An_qform_ge_endpoints m hm1 x'
      set r := dotProduct x' ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.A m hm1).adj).mulVec x') with hr_def
      have hxm := hp ⟨m, by omega⟩
      by_cases hxm0 : x ⟨m, by omega⟩ = 0
      · -- x_m = 0: r = 2, x' is a root, use IH
        have hr2 : r = 2 := by nlinarith [hxm0]
        have hne' : x' ≠ 0 := by
          intro heq
          apply hne; ext ⟨j, hj⟩
          simp only [Pi.zero_apply]
          by_cases hjm : j < m
          · have := congr_fun heq ⟨j, hjm⟩
            simp [Pi.zero_apply] at this
            exact this
          · have : j = m := by omega
            subst this; exact hxm0
        have hroot' : Etingof.IsRoot m (Etingof.DynkinType.A m hm1).adj x' :=
          ⟨hne', hr2 ▸ hr_def ▸ rfl⟩
        intro ⟨j, hj⟩
        by_cases hjm : j < m
        · exact ih hm1 x' hroot' hpos' hroot'.2 hroot'.1 ⟨j, hjm⟩
        · have : j = m := by omega
          subst this; simp [hxm0]
      · -- x_m ≥ 1: endpoint bound gives x_m = 1, then case split on x_{m-1}
        have hxm_pos : x ⟨m, by omega⟩ ≥ 1 := by omega
        have hkey : x ⟨0, by omega⟩ ^ 2 +
            (x ⟨m - 1, by omega⟩ - x ⟨m, by omega⟩) ^ 2 +
            x ⟨m, by omega⟩ ^ 2 ≤ 2 := by nlinarith
        have hxm1 : x ⟨m, by omega⟩ = 1 := by
          nlinarith [sq_nonneg (x ⟨0, by omega⟩),
            sq_nonneg (x ⟨m - 1, by omega⟩ - x ⟨m, by omega⟩)]
        have hr_eq : r = 2 * x ⟨m - 1, by omega⟩ := by nlinarith [hxm1]
        -- x_{m-1} ≤ 1 (if x_{m-1} = 2, An_qform_no_double gives contradiction)
        have hm1_le1 : x ⟨m - 1, by omega⟩ ≤ 1 := by
          by_contra h; push_neg at h
          have hle2 : x ⟨m - 1, by omega⟩ ≤ 2 := by
            nlinarith [sq_nonneg (x ⟨m - 1, by omega⟩ - 2),
              sq_nonneg (x ⟨0, by omega⟩)]
          have hval2 : x ⟨m - 1, by omega⟩ = 2 := by omega
          have hx0 : x ⟨0, by omega⟩ = 0 := by
            nlinarith [sq_nonneg (x ⟨0, by omega⟩), hval2]
          have hr4 : r = 4 := by nlinarith [hval2]
          exact An_qform_no_double m hm1 x' hpos' hx0
            (show x' ⟨m - 1, by omega⟩ = 2 from hval2) (hr_def ▸ hr4)
        intro ⟨j, hj⟩
        by_cases hjm : j = m
        · subst hjm; simp [hxm1]
        · have hjm' : j < m := by omega
          by_cases hxm1_val : x ⟨m - 1, by omega⟩ = 0
          · -- r = 0, x' = 0 by An_qform_zero
            have hr0 : r = 0 := by nlinarith
            have hx'z := An_qform_zero m hm1 x' hpos' (hr_def ▸ hr0)
            have : x ⟨j, by omega⟩ = 0 := by
              have := congr_fun hx'z ⟨j, hjm'⟩
              simp [Pi.zero_apply] at this; exact this
            omega
          · -- x_{m-1} = 1, r = 2, x' is a root
            have hm1pos := hp ⟨m - 1, by omega⟩
            have hval1 : x ⟨m - 1, by omega⟩ = 1 := by omega
            have hr2 : r = 2 := by nlinarith [hval1]
            have hne' : x' ≠ 0 := by
              intro heq
              have : r = 0 := by
                simp only [hr_def, heq, dotProduct, mulVec, Pi.zero_apply,
                  mul_zero, Finset.sum_const_zero]
              linarith
            have hroot' : Etingof.IsRoot m
                (Etingof.DynkinType.A m hm1).adj x' :=
              ⟨hne', hr2 ▸ hr_def ▸ rfl⟩
            exact ih hm1 x' hroot' hpos' hroot'.2 hroot'.1 ⟨j, hjm'⟩

/-- The interval indicator vector: 1 on [a, b], 0 elsewhere. -/
private def ivec (n : ℕ) (a b : ℕ) : Fin n → Fin 2 :=
  fun i => if a ≤ i.val ∧ i.val ≤ b then 1 else 0

/-- The quadratic form of an interval indicator always equals 2. -/
private lemma An_ivec_qform_eq : ∀ (n : ℕ) (hn : 1 ≤ n)
    (a b : ℕ) (hab : a ≤ b) (hb : b < n),
    dotProduct (fun i : Fin n => ((ivec n a b i : Fin 2) : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
        (Etingof.DynkinType.A n hn).adj).mulVec
        (fun i => ((ivec n a b i : Fin 2) : ℤ))) = 2 := by
  intro n; induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn a b hab hb
    by_cases hm0 : m = 0
    · subst hm0
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      simp only [dotProduct, mulVec, Etingof.DynkinType.adj,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
        Finset.sum_range_zero, ivec]
      norm_num
    · have hm1 : 1 ≤ m := by omega
      -- Set up the ℤ-valued function
      set xi : Fin (m + 1) → ℤ := fun i => ((ivec (m + 1) a b i : Fin 2) : ℤ)
        with hxi_def
      -- Use peel decomposition
      show dotProduct xi ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
        (Etingof.DynkinType.A (m + 1) hn).adj).mulVec xi) = 2
      rw [An_qform_peel m hm1 xi]
      -- Compute values at key positions
      have hxi_val : ∀ (j : ℕ) (hj : j < m + 1),
          xi ⟨j, hj⟩ = if a ≤ j ∧ j ≤ b then 1 else 0 := by
        intro j hj; simp [hxi_def, ivec]; split_ifs <;> simp
      -- Restriction to Fin m is ivec with capped b
      set b' := min b (m - 1) with hb'_def
      have hxi_res_eq : (fun i : Fin m => xi ⟨i.val, by omega⟩) =
          fun i : Fin m => ((ivec m a b' i : Fin 2) : ℤ) := by
        ext ⟨j, hj⟩
        simp only [hxi_def, ivec, hb'_def]
        split_ifs with h1 h2 h2
        · simp
        · exfalso; apply h2; exact ⟨h1.1, by omega⟩
        · exfalso; apply h1; exact ⟨h2.1, by omega⟩
        · simp
      by_cases hbm : b < m
      · -- b < m: x_m = 0, peel term vanishes
        have hm_val : xi ⟨m, by omega⟩ = 0 := by
          rw [hxi_val]; simp; omega
        have hb'_eq : b' = b := by simp [hb'_def]; omega
        rw [hm_val]; ring_nf; rw [hxi_res_eq, hb'_eq]
        exact ih hm1 a b hab hbm
      · -- b ≥ m: b = m
        have hbm' : b = m := by omega
        have hm_val : xi ⟨m, by omega⟩ = 1 := by
          rw [hxi_val]; simp; omega
        by_cases ham : a = m
        · -- Singleton at m: x_{m-1} = 0, restriction is zero
          have hm1_val : xi ⟨m - 1, by omega⟩ = 0 := by
            rw [hxi_val]; simp; omega
          have hres0 :
              (fun i : Fin m => xi ⟨i.val, by omega⟩) = 0 := by
            ext ⟨j, hj⟩
            simp [hxi_def, ivec, Pi.zero_apply]; omega
          rw [hm_val, hm1_val, hres0]
          simp [dotProduct, mulVec, Pi.zero_apply,
            Finset.sum_const_zero]
        · -- a < m: x_{m-1} = 1, peel gives q_m + 2 - 2 = q_m
          have hm1_val : xi ⟨m - 1, by omega⟩ = 1 := by
            rw [hxi_val]; simp; omega
          have hb'_eq : b' = m - 1 := by
            simp [hb'_def]; omega
          rw [hm_val, hm1_val]; ring_nf; rw [hxi_res_eq, hb'_eq]
          exact ih hm1 a (m - 1) (by omega) (by omega)

/-- Interval indicators are in rootCountFinset. -/
private lemma ivec_mem : ∀ (n : ℕ) (hn : 1 ≤ n) (a b : ℕ) (hab : a ≤ b) (hb : b < n),
    ivec n a b ∈ rootCountFinset n (Etingof.DynkinType.A n hn).adj 2 := by
  intro n; induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn a b hab hb
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · -- nonzero: position a has value 1
      intro h
      have : (fun i : Fin (m + 1) => ((ivec (m + 1) a b) i : ℤ)) = 0 := by
        ext i; have := congr_fun h i
        simp only [Pi.zero_apply] at this ⊢
        exact_mod_cast this
      have : ((ivec (m + 1) a b) ⟨a, by omega⟩ : ℤ) = 0 := by
        have := congr_fun this ⟨a, by omega⟩; simpa using this
      simp [ivec, hab] at this
    · -- q = 2: prove by An_ivec_qform_eq helper
      exact An_ivec_qform_eq (m + 1) hn a b hab hb

/-- The interval indicator map is injective on valid pairs. -/
private lemma ivec_injective (n : ℕ) (a₁ b₁ a₂ b₂ : ℕ)
    (h₁ : a₁ ≤ b₁) (hb₁ : b₁ < n) (h₂ : a₂ ≤ b₂) (hb₂ : b₂ < n)
    (heq : ivec n a₁ b₁ = ivec n a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have key : ∀ (a b : ℕ) (_ : a ≤ b) (_ : b < n) (j : ℕ) (hj : j < n),
      (ivec n a b ⟨j, hj⟩ = 1) ↔ (a ≤ j ∧ j ≤ b) := by
    intro a b hab _ j _
    simp only [ivec]
    constructor
    · intro h; split_ifs at h with hc <;> [exact hc; exact absurd h (by decide)]
    · intro ⟨h1, h2⟩; simp [show a ≤ j ∧ j ≤ b from ⟨h1, h2⟩]
  have mem12 : ∀ j (hj : j < n), ivec n a₁ b₁ ⟨j, hj⟩ = ivec n a₂ b₂ ⟨j, hj⟩ :=
    fun j hj => congr_fun heq ⟨j, hj⟩
  constructor
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : ivec n a₁ b₁ ⟨a₁, by omega⟩ = 1 := (key a₁ b₁ h₁ hb₁ a₁ (by omega)).mpr ⟨le_refl _, h₁⟩
      rw [mem12] at h1
      have := (key a₂ b₂ h₂ hb₂ a₁ (by omega)).mp h1; omega
    · have h1 : ivec n a₂ b₂ ⟨a₂, by omega⟩ = 1 := (key a₂ b₂ h₂ hb₂ a₂ (by omega)).mpr ⟨le_refl _, h₂⟩
      rw [← mem12] at h1
      have := (key a₁ b₁ h₁ hb₁ a₂ (by omega)).mp h1; omega
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : ivec n a₁ b₁ ⟨b₁, by omega⟩ = 1 := (key a₁ b₁ h₁ hb₁ b₁ (by omega)).mpr ⟨h₁, le_refl _⟩
      rw [mem12] at h1
      have h2 : ivec n a₂ b₂ ⟨b₂, by omega⟩ = 1 := (key a₂ b₂ h₂ hb₂ b₂ (by omega)).mpr ⟨h₂, le_refl _⟩
      rw [← mem12] at h2
      have := (key a₂ b₂ h₂ hb₂ b₁ (by omega)).mp h1
      have := (key a₁ b₁ h₁ hb₁ b₂ (by omega)).mp h2; omega
    · have h1 : ivec n a₂ b₂ ⟨b₂, by omega⟩ = 1 := (key a₂ b₂ h₂ hb₂ b₂ (by omega)).mpr ⟨h₂, le_refl _⟩
      rw [← mem12] at h1
      have h2 : ivec n a₁ b₁ ⟨b₁, by omega⟩ = 1 := (key a₁ b₁ h₁ hb₁ b₁ (by omega)).mpr ⟨h₁, le_refl _⟩
      rw [mem12] at h2
      have := (key a₁ b₁ h₁ hb₁ b₂ (by omega)).mp h1
      have := (key a₂ b₂ h₂ hb₂ b₁ (by omega)).mp h2; omega

/-- Helper: a Fin 2 value is either 0 or 1. -/
private lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩; interval_cases v <;> simp [Fin.ext_iff]

/-- Every element of rootCountFinset is an interval indicator. -/
private lemma root_is_ivec : ∀ (n : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin 2),
    v ∈ rootCountFinset n (Etingof.DynkinType.A n hn).adj 2 →
    ∃ a b : ℕ, a ≤ b ∧ b < n ∧ v = ivec n a b := by
  intro n; induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn v hv
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hne, hq⟩ := hv
    -- Helper: convert v to ℤ and use peel
    set x : Fin (m + 1) → ℤ := fun i => (v i : ℤ) with hx_def
    set v' : Fin m → Fin 2 := fun i => v ⟨i.val, by omega⟩ with hv'_def
    by_cases hm0 : m = 0
    · -- n = 1: v 0 must be 1
      subst hm0
      have hv0 : v 0 = 1 := by
        rcases fin2_eq_zero_or_one (v 0) with h | h
        · exfalso; apply hne; ext i; fin_cases i; simp [hx_def, h]
        · exact h
      refine ⟨0, 0, le_refl _, by omega, funext fun i => ?_⟩
      have : i = 0 := by ext; omega
      subst this; simp [ivec, hv0]
    · have hm1 : 1 ≤ m := by omega
      -- Peel the quadratic form
      have hq_peel : dotProduct (fun i : Fin m => (v' i : ℤ))
          ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (Etingof.DynkinType.A m hm1).adj).mulVec
            (fun i : Fin m => (v' i : ℤ))) +
          2 * (v ⟨m, by omega⟩ : ℤ) ^ 2 -
          2 * (v ⟨m - 1, by omega⟩ : ℤ) * (v ⟨m, by omega⟩ : ℤ) = 2 := by
        have := An_qform_peel m hm1 x
        simp only [hx_def] at this
        rw [this] at hq; convert hq using 2 <;> rfl
      -- Helper to build rootCountFinset membership for v'
      have mk_mem : ∀ (hne' : v' ≠ 0),
          dotProduct (fun i : Fin m => (v' i : ℤ))
            ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
              (Etingof.DynkinType.A m hm1).adj).mulVec
              (fun i : Fin m => (v' i : ℤ))) = 2 →
          v' ∈ rootCountFinset m (Etingof.DynkinType.A m hm1).adj 2 := by
        intro hne' hq'
        simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h; apply hne'; funext i
          have := congr_fun h i
          simp [Pi.zero_apply] at this
          exact_mod_cast this
        · convert hq' using 1
      -- Case split on v_m
      rcases fin2_eq_zero_or_one (v ⟨m, by omega⟩) with hvm0 | hvm1
      · -- v_m = 0: q_m(v') = 2
        have hvm_z : (v ⟨m, by omega⟩ : ℤ) = 0 := by simp [hvm0]
        have hq' : dotProduct (fun i : Fin m => (v' i : ℤ))
            ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
              (Etingof.DynkinType.A m hm1).adj).mulVec
              (fun i : Fin m => (v' i : ℤ))) = 2 := by
          have := hq_peel; rw [hvm_z] at this; linarith
        have hne' : v' ≠ 0 := by
          intro h; apply hne; funext ⟨i, hi⟩
          simp only [hx_def, Pi.zero_apply]
          by_cases him : i < m
          · have h1 : v' ⟨i, him⟩ = 0 := congr_fun h ⟨i, him⟩
            simp only [hv'_def] at h1; simp [h1]
          · have him' : i = m := by omega
            subst him'; simp [hvm0]
        obtain ⟨a, b, hab, hbm, hveq⟩ := ih hm1 v' (mk_mem hne' hq')
        refine ⟨a, b, hab, by omega, funext fun ⟨i, hi⟩ => ?_⟩
        simp only [ivec]
        by_cases him : i < m
        · have := congr_fun hveq ⟨i, him⟩
          simp only [ivec, hv'_def] at this; exact this
        · have h_neg : ¬(a ≤ i ∧ i ≤ b) := by omega
          simp only [h_neg, ite_false]
          have heq : i = m := by omega
          show v ⟨i, hi⟩ = 0
          convert hvm0 using 2; exact Fin.ext (by omega)
      · -- v_m = 1
        have hvm_z : (v ⟨m, by omega⟩ : ℤ) = 1 := by simp [hvm1]
        rcases fin2_eq_zero_or_one (v ⟨m - 1, by omega⟩) with hprev0 | hprev1
        · -- v_{m-1} = 0: q_m(v') = 0, so v' = 0
          have hprev_z : (v ⟨m - 1, by omega⟩ : ℤ) = 0 := by simp [hprev0]
          have hq0 : dotProduct (fun i : Fin m => (v' i : ℤ))
              ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
                (Etingof.DynkinType.A m hm1).adj).mulVec
                (fun i : Fin m => (v' i : ℤ))) = 0 := by
            have := hq_peel; rw [hvm_z, hprev_z] at this; linarith
          have hv'z := An_qform_zero m hm1 (fun i => (v' i : ℤ))
            (fun i => by positivity) hq0
          -- v' = 0 means all coords before m are 0
          have hv'_zero : ∀ i : Fin m, v' i = 0 := by
            intro i; have := congr_fun hv'z i
            simp [Pi.zero_apply] at this
            exact_mod_cast this
          refine ⟨m, m, le_refl _, by omega, funext fun ⟨i, hi⟩ => ?_⟩
          simp only [ivec]
          by_cases him : i = m
          · simp only [him, le_refl, and_self, ite_true]; exact hvm1
          · have hilm : i < m := by omega
            have h1 := hv'_zero ⟨i, hilm⟩
            simp only [hv'_def] at h1
            have : ¬(m ≤ i) := by omega
            simp [this, h1]
        · -- v_{m-1} = 1: q_m(v') = 2, v' is a root
          have hprev_z : (v ⟨m - 1, by omega⟩ : ℤ) = 1 := by simp [hprev1]
          have hq' : dotProduct (fun i : Fin m => (v' i : ℤ))
              ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
                (Etingof.DynkinType.A m hm1).adj).mulVec
                (fun i : Fin m => (v' i : ℤ))) = 2 := by
            have := hq_peel; rw [hvm_z, hprev_z] at this; linarith
          have hne' : v' ≠ 0 := by
            intro h
            have h1 := congr_fun h ⟨m - 1, by omega⟩
            simp only [hv'_def, Pi.zero_apply] at h1
            rw [hprev1] at h1; exact absurd h1 (by decide)
          obtain ⟨a, b, hab, hbm, hveq⟩ := ih hm1 v' (mk_mem hne' hq')
          -- b = m - 1 (since v'_{m-1} = 1 = ivec value at m-1)
          have hb_eq : b = m - 1 := by
            have h1 := congr_fun hveq ⟨m - 1, by omega⟩
            simp only [ivec, hv'_def] at h1
            by_contra hne_b
            have hcond : ¬(a ≤ m - 1 ∧ m - 1 ≤ b) := by omega
            simp only [hcond, ite_false] at h1
            rw [hprev1] at h1; exact absurd h1 (by decide)
          refine ⟨a, m, by omega, by omega, funext fun ⟨i, hi⟩ => ?_⟩
          simp only [ivec]
          by_cases him : i = m
          · have : a ≤ i ∧ i ≤ m := by omega
            simp only [this, ite_true]
            show v ⟨i, hi⟩ = 1
            convert hvm1 using 2; exact Fin.ext (by omega)
          · have hilm : i < m := by omega
            have h1 := congr_fun hveq ⟨i, hilm⟩
            simp only [ivec, hv'_def] at h1
            have key : (a ≤ i ∧ i ≤ m) ↔ (a ≤ i ∧ i ≤ b) := by
              constructor
              · intro ⟨ha, hle⟩; exact ⟨ha, by omega⟩
              · intro ⟨ha, hle⟩; exact ⟨ha, by omega⟩
            simp only [key]; exact h1

/-- Number of pairs (a, b) with a ≤ b in Fin n is n(n+1)/2. -/
private lemma pair_count (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 ≤ p.2)).card =
    n * (n + 1) / 2 := by
  -- Prove: 2 * card = n * (n+1), then divide
  suffices h : 2 * ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 ≤ p.2)).card = n * (n + 1) by omega
  induction n with
  | zero => simp
  | succ m ih =>
    -- Split by whether b = m
    have key : (Finset.univ.filter
        (fun p : Fin (m + 1) × Fin (m + 1) => p.1 ≤ p.2)) =
      ((Finset.univ.filter (fun p : Fin m × Fin m =>
          p.1 ≤ p.2)).image (fun p =>
          (Fin.castSucc p.1, Fin.castSucc p.2))) ∪
      ((Finset.univ : Finset (Fin (m + 1))).image
          (fun a => (a, Fin.last m))) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro hab
        by_cases hbm : b = Fin.last m
        · right; exact ⟨a, rfl, hbm.symm⟩
        · left
          have hblt : b.val < m := by
            simp [Fin.last, Fin.ext_iff] at hbm; omega
          refine ⟨(⟨a.val, by omega⟩, ⟨b.val, hblt⟩), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simpa using hab
          · constructor <;> exact Fin.ext rfl
      · rintro (⟨⟨a', b'⟩, hmem, ha, hb⟩ | ⟨a', ha', hb'⟩)
        · simp only [Finset.mem_filter, Finset.mem_univ,
            true_and] at hmem
          rw [← ha, ← hb]; simpa using hmem
        · rw [← ha', ← hb']; exact Fin.le_last a'
    rw [key, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (by
        intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
        simp [Prod.mk.injEq, Fin.castSucc_inj] at h
        exact Prod.ext h.1 h.2)]
      rw [Finset.card_image_of_injective _ (by
        intro a₁ a₂ h; simpa using h)]
      simp [Finset.card_fin]; linarith
    · rw [Finset.disjoint_left]
      intro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_image, Prod.mk.injEq,
        Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      obtain ⟨⟨a', b'⟩, _, _, hb⟩ := h1
      obtain ⟨_, _, hb'⟩ := h2
      rw [← hb] at hb'
      exact absurd hb'.symm (Fin.castSucc_ne_last b')

/-- The count of rootCountFinset for A_n with bound 2 equals n(n+1)/2. -/
private lemma An_count (n : ℕ) (hn : 1 ≤ n) :
    (rootCountFinset n (Etingof.DynkinType.A n hn).adj 2).card =
      n * (n + 1) / 2 := by
  have heq : rootCountFinset n (Etingof.DynkinType.A n hn).adj 2 =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≤ p.2)).image
        (fun p => ivec n p.1.val p.2.val) := by
    ext v; constructor
    · intro hv
      obtain ⟨a, b, hab, hbn, hveq⟩ := root_is_ivec n hn v hv
      exact Finset.mem_image.mpr ⟨(⟨a, by omega⟩, ⟨b, by omega⟩),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hab⟩, hveq.symm⟩
    · intro hv
      obtain ⟨⟨a, b⟩, hp, hveq⟩ := Finset.mem_image.mp hv
      have hab := (Finset.mem_filter.mp hp).2
      rw [← hveq]; exact ivec_mem n hn a.val b.val (by simpa using hab) b.isLt
  rw [heq, Finset.card_image_of_injOn (fun ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq => by
    have hab₁ := (Finset.mem_filter.mp h₁).2
    have hab₂ := (Finset.mem_filter.mp h₂).2
    obtain ⟨ha, hb⟩ := ivec_injective n a₁.val b₁.val a₂.val b₂.val
      (by simpa using hab₁) b₁.isLt (by simpa using hab₂) b₂.isLt
      (by simpa [Prod.mk.injEq] using heq)
    exact Prod.ext (Fin.ext ha) (Fin.ext hb))]
  exact pair_count n

lemma An_result (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq (An_bound n hn)
  exact ⟨hfin, hcard ▸ An_count n hn⟩

end AnRootCount

/-- The number of positive roots for Aₙ is n(n+1)/2.
(Etingof Example 6.4.9(1)) -/
theorem Etingof.Example_6_4_9_An (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 :=
  An_result n hn
