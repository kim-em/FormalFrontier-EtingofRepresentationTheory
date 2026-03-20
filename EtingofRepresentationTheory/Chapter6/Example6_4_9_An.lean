import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared

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
      · -- x_m ≥ 1: needs proof restructuring after Lean update
        -- Old proof's `linarith` at `r ≤ 2` no longer works; needs case split on x_{m-1}
        sorry

/-- The interval indicator vector: 1 on [a, b], 0 elsewhere. -/
private def ivec (n : ℕ) (a b : ℕ) : Fin n → Fin 2 :=
  fun i => if a ≤ i.val ∧ i.val ≤ b then 1 else 0

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
    · -- q = 2: by induction using peel (needs tactic updates after Lean upgrade)
      sorry

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

/-- Every element of rootCountFinset is an interval indicator. -/
private lemma root_is_ivec : ∀ (n : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin 2),
    v ∈ rootCountFinset n (Etingof.DynkinType.A n hn).adj 2 →
    ∃ a b : ℕ, a ≤ b ∧ b < n ∧ v = ivec n a b := by
  -- Needs tactic updates after Lean upgrade (interval_cases, mod_cast, show patterns)
  sorry

/-- Number of pairs (a, b) with a ≤ b in Fin n is n(n+1)/2. -/
private lemma pair_count (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≤ p.2)).card =
    n * (n + 1) / 2 := by
  -- Needs tactic updates after Lean upgrade (card_bij API change, omega with division)
  sorry

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
