import EtingofRepresentationTheory.Chapter6.Example6_4_9_Shared
import EtingofRepresentationTheory.Chapter6.DynkinTypes

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
  apply propext
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
    (Etingof.DynkinType.D (m + 1) (by omega)).adj (⟨0, by omega⟩ : Fin (m + 1)) j.succ =
    if j.val = 0 then 1 else 0 := by
  simp only [Etingof.DynkinType.adj, Fin.val_succ, Fin.val_mk]
  have hj := j.isLt
  congr 1; apply propext; constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩)) <;> omega
  · intro h; left; left; exact ⟨by omega, by omega⟩

/-- Vertex 0 in D_{m+1} has no self-loop. -/
private lemma Dn_adj_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj (⟨0, by omega⟩ : Fin (m + 1)) (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
  simp only [Etingof.DynkinType.adj, Fin.val_mk]
  have : ¬(((0 + 1 = 0 ∧ (0 : ℕ) ≤ m + 1 - 2) ∨ (0 + 1 = 0 ∧ (0 : ℕ) ≤ m + 1 - 2)) ∨
    ((0 = m + 1 - 3 ∧ (0 : ℕ) = m + 1 - 1) ∨ (0 = m + 1 - 3 ∧ (0 : ℕ) = m + 1 - 1))) := by omega
  rw [if_neg this]

/-- adj(succ i, 0) in D_{m+1} equals adj(0, succ i) by symmetry. -/
private lemma Dn_adj_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (Etingof.DynkinType.D (m + 1) (by omega)).adj i.succ (⟨0, by omega⟩ : Fin (m + 1)) =
    if i.val = 0 then 1 else 0 := by
  simp only [Etingof.DynkinType.adj, Fin.val_succ, Fin.val_mk]
  have hi := i.isLt
  congr 1; apply propext; constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩)) <;> omega
  · intro h; left; right; exact ⟨by omega, by omega⟩

/-- The Cartan matrix of D_{m+1} at (succ i, succ j) matches D_m at (i, j). -/
private lemma Dn_cartan_succ_succ (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) i.succ j.succ =
    (2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
      (Etingof.DynkinType.D m hm).adj) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Dn_adj_succ_succ m hm i j, show (i.succ : Fin (m + 1)) = j.succ ↔ i = j from Fin.succ_inj]

/-- The Cartan matrix of D_{m+1} at (0, succ j). -/
private lemma Dn_cartan_zero_succ (m : ℕ) (hm : 4 ≤ m) (j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) 0 j.succ =
    if j.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Etingof.DynkinType.adj, Fin.val_succ, Fin.val_mk]
  have hj := j.isLt
  have : ¬((0 : Fin (m + 1)) = j.succ) := (Fin.succ_ne_zero j).symm
  rw [if_neg this]; simp
  split_ifs <;> omega

/-- The Cartan matrix of D_{m+1} at (succ i, 0). -/
private lemma Dn_cartan_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) i.succ 0 =
    if i.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Etingof.DynkinType.adj, Fin.val_succ, Fin.val_mk]
  have hi := i.isLt
  have : ¬((i.succ : Fin (m + 1)) = 0) := Fin.succ_ne_zero i
  rw [if_neg this]; simp
  split_ifs <;> omega

/-- The Cartan matrix of D_{m+1} at (0, 0) is 2. -/
private lemma Dn_cartan_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj) 0 0 = 2 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have h := Dn_adj_zero_zero m hm
  rw [show (⟨0, by omega⟩ : Fin (m + 1)) = (0 : Fin (m + 1)) from rfl] at h
  rw [h]; norm_num

/-- The D_{m+1} quadratic form decomposes as D_m on the tail plus 2x₀(x₀ - x₁). -/
private lemma Dn_qform_peel (m : ℕ) (hm : 4 ≤ m) (x : Fin (m + 1) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) (by omega)).adj).mulVec x) =
    dotProduct (x ∘ Fin.succ)
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm).adj).mulVec (x ∘ Fin.succ)) +
    2 * x 0 ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ := by
  -- Expand dotProduct/mulVec into sums
  simp only [dotProduct, mulVec, Function.comp, Fin.sum_univ_succ]
  -- Substitute all Cartan matrix entries
  simp only [Dn_cartan_zero_zero m hm, Dn_cartan_zero_succ m hm,
    Dn_cartan_succ_zero m hm, Dn_cartan_succ_succ m hm]
  -- Simplify ite expressions
  simp only [ite_mul, one_mul, zero_mul, neg_mul, mul_ite, mul_one, mul_zero, mul_neg]
  -- Convert i.val = 0 conditions to i = ⟨0, _⟩
  have hconv : ∀ (i : Fin m) (a b : ℤ),
      (if i.val = 0 then a else b) = if i = ⟨0, by omega⟩ then a else b := by
    intro i a b; congr 1; exact propext ⟨fun h => Fin.ext h, fun h => congr_arg _ h⟩
  simp_rw [hconv]
  -- Reduce ite sums to single terms
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hx1 : Fin.succ (⟨0, by omega⟩ : Fin m) = (⟨1, by omega⟩ : Fin (m + 1)) := by
    ext; simp
  simp only [hx1]
  -- Distribute multiplication over addition in the sum
  simp_rw [mul_add, Finset.sum_add_distrib]
  -- Extract the ite sum
  have hite : ∑ i : Fin m, x i.succ * (if i = ⟨0, by omega⟩ then -x 0 else 0) =
      -x ⟨1, by omega⟩ * x 0 := by
    rw [Finset.sum_eq_single_of_mem ⟨0, by omega⟩ (Finset.mem_univ _)
      (fun b _ hb => by simp [hb])]
    simp
  linarith [hite, sq (x 0)]

/-- Strengthened: q_{D_n}(x) ≥ (x ⟨0, _⟩)² and q > 0 for nonzero x. -/
private lemma Dn_qform_ge_sq_and_posDef : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    (x ⟨0, by omega⟩) ^ 2 ≤ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.D n hn).adj).mulVec x) ∧
    (x ≠ 0 → 0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.D n hn).adj).mulVec x)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x
    set q := dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (Etingof.DynkinType.D (m + 1) hm).adj).mulVec x)
    by_cases hm4 : m = 3
    · subst hm4
      have hsos := D4_sos (x 0) (x 1) (x 2) (x 3)
      have hqf := D4_qf x
      have hq_eq : q = 2*(x 0^2+x 1^2+x 2^2+x 3^2) -
          2*(x 0*x 1+x 1*x 2+x 1*x 3) := hqf
      have hsos2 : 2 * q = (2*x 0-x 1)^2 + (2*x 2-x 1)^2 +
          (2*x 3-x 1)^2 + x 1^2 := by linarith
      constructor
      · -- 2q - 2x₀² = 2(x₀-x₁)² + (2x₂-x₁)² + (2x₃-x₁)² ≥ 0
        show (x 0) ^ 2 ≤ q
        nlinarith [hsos2, sq_nonneg (x 0 - x 1), sq_nonneg (2 * x 2 - x 1),
          sq_nonneg (2 * x 3 - x 1)]
      · intro hne
        show 0 < q
        by_cases h1 : x 1 = 0
        · -- x₁ = 0: 2q = 4(x₀²+x₂²+x₃²)
          have : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
            by_contra h; push_neg at h; apply hne; ext i; fin_cases i <;> simp_all
          simp only [h1, mul_zero, sub_zero, zero_mul, add_zero, sq_abs] at hsos2
          rcases this with h | h | h <;>
            nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3),
              mul_self_pos.mpr h]
        · -- x₁ ≠ 0: x₁² > 0
          have := mul_self_pos.mpr h1
          nlinarith [sq_nonneg (2 * x 0 - x 1), sq_nonneg (2 * x 2 - x 1),
            sq_nonneg (2 * x 3 - x 1)]
    · have hm' : 4 ≤ m := by omega
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ with htail_def
      set q_tail := dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm').adj).mulVec tail)
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by
        simp [htail_def]
      have hih := ih hm' tail
      rw [htail0] at hih
      have hq_eq : q = q_tail + 2 * x ⟨0, by omega⟩ ^ 2 -
          2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := hpeel
      constructor
      · -- q(x) ≥ x₀²
        -- q = q_tail + 2x₀² - 2x₀x₁, q_tail ≥ x₁²
        -- q - x₀² = q_tail - x₁² + x₀² + (x₀-x₁)² ≥ 0
        nlinarith [hih.1, sq_nonneg (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)]
      · intro hne
        by_cases hx0 : x ⟨0, by omega⟩ = 0
        · -- x₀ = 0: tail must be nonzero, use IH for positivity
          have htail_ne : tail ≠ 0 := by
            intro h; apply hne; ext i
            by_cases hi : i = ⟨0, by omega⟩
            · rw [hi]; exact hx0
            · have hiv : i.val ≠ 0 := fun heq => hi (Fin.ext heq)
              have : ∃ j : Fin m, i = j.succ :=
                ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
              obtain ⟨j, rfl⟩ := this
              exact congr_fun h j
          nlinarith [hih.2 htail_ne, sq_nonneg (x ⟨1, by omega⟩)]
        · -- x₀ ≠ 0: use q ≥ x₀² > 0
          have hx0_pos := mul_self_pos.mpr hx0
          nlinarith [hih.1, sq_nonneg (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)]

/-- Positive definiteness of the D_n Cartan form: q(x) > 0 for nonzero x. -/
private lemma Dn_posDef (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ) (hx : x ≠ 0) :
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.D n hn).adj).mulVec x) :=
  (Dn_qform_ge_sq_and_posDef n hn x).2 hx

/-- Cascade bound: if q = 2·(x 0) with x 0 ≤ 2 and positive coords, all coords < 3. -/
private lemma Dn_cascade_bound : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (Etingof.DynkinType.D n hn).adj).mulVec x) = 2 * x ⟨0, by omega⟩ →
    x ⟨0, by omega⟩ ≤ 2 →
    (∀ i, 0 ≤ x i) → ∀ i, x i < 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x hq hx0_le hpos
    by_cases hm4 : m = 3
    · subst hm4
      -- D4 base case: 2q = SOS ≤ 8
      have hsos := D4_sos (x 0) (x 1) (x 2) (x 3)
      have hqf := D4_qf x
      -- hq says q = 2*x₀, hqf gives explicit form
      have hq0 : x ⟨0, by omega⟩ = x 0 := rfl
      rw [hq0] at hq hx0_le
      have hsos_bound : (2*x 0-x 1)^2 + (2*x 2-x 1)^2 +
          (2*x 3-x 1)^2 + x 1^2 ≤ 8 := by nlinarith
      -- Each SOS term ≤ 8, so each square root ≤ 2 (since 3² = 9 > 8)
      have hx1 : x 1 ≤ 2 := by nlinarith [sq_nonneg (x 1 - 3)]
      have hx2 : x 2 ≤ 2 := by nlinarith [sq_nonneg (2*x 2 - x 1 - 3), sq_nonneg (2*x 2 - x 1 + 3)]
      have hx3 : x 3 ≤ 2 := by nlinarith [sq_nonneg (2*x 3 - x 1 - 3), sq_nonneg (2*x 3 - x 1 + 3)]
      intro i; fin_cases i <;> simp_all <;> omega
    · have hm' : 4 ≤ m := by omega
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by simp [tail]
      set q_tail := dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (Etingof.DynkinType.D m hm').adj).mulVec tail)
      have hge := (Dn_qform_ge_sq_and_posDef m hm' tail).1
      rw [htail0] at hge
      have hx0 := x ⟨0, by omega⟩
      by_cases hx0_eq : x ⟨0, by omega⟩ = 0
      · -- x₀ = 0: q = 0, x = 0
        have : q_tail = 0 := by nlinarith [hpeel]
        have htail_zero : tail = 0 := by
          by_contra h
          exact absurd this (ne_of_gt ((Dn_qform_ge_sq_and_posDef m hm' tail).2 h))
        intro i
        by_cases hi : i = ⟨0, by omega⟩
        · rw [hi, hx0_eq]; norm_num
        · have hiv : i.val ≠ 0 := fun heq => hi (Fin.ext heq)
          have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this
          have := congr_fun htail_zero j; simp [tail] at this
          linarith
      · -- x₀ ∈ {1, 2}
        have hx0_pos : 0 < x ⟨0, by omega⟩ := by
          have h0 := hpos ⟨0, by omega⟩; omega
        -- q_tail from peel
        have hpeel' := hpeel; rw [hq, show x (0 : Fin (m + 1)) = x ⟨0, by omega⟩ from rfl] at hpeel'
        have hq_tail_val : q_tail = 2 * x ⟨0, by omega⟩ -
            2 * x ⟨0, by omega⟩ ^ 2 + 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := by
          linarith [hpeel']
        -- ge_sq for tail: x₁² ≤ q_tail
        have hx1_sq : (x ⟨1, by omega⟩) ^ 2 ≤ q_tail := hge
        -- q = 2·x₀, so q_tail = 2x₀ - 2x₀² + 2x₀x₁ = 2x₀(1 - x₀ + x₁)
        -- ge_sq: x₁² ≤ 2x₀(1 - x₀ + x₁)
        -- For x₀ = 1: q_tail = 2x₁. For x₀ = 2: (x₁-2)² ≤ 0, x₁ = 2, q_tail = 4.
        -- Both: q_tail = 2·x₁ with x₁ ≤ 2.
        have hx1_bound : x ⟨1, by omega⟩ ≤ 2 := by
          nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
        have hq_tail_cascade : q_tail = 2 * tail ⟨0, by omega⟩ := by
          rw [htail0]
          by_cases hx0_1 : x ⟨0, by omega⟩ = 1
          · nlinarith [hq_tail_val, hx0_1]
          · have hx0_2 : x ⟨0, by omega⟩ = 2 := by omega
            have hq_t : q_tail = 4 * x ⟨1, by omega⟩ - 4 := by nlinarith
            have hx1_eq : x ⟨1, by omega⟩ = 2 := by
              nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
            linarith
        have htail0_le : tail ⟨0, by omega⟩ ≤ 2 := by rw [htail0]; exact hx1_bound
        have htail_pos : ∀ i, 0 ≤ tail i := fun i => hpos i.succ
        have hih_result := ih hm' tail hq_tail_cascade htail0_le htail_pos
        intro i
        by_cases hi : i = ⟨0, by omega⟩
        · rw [hi]; linarith
        · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this
          exact hih_result j

/-- All positive roots of D_n have each coordinate < 3.
    Proved by induction: peel off vertex 0, apply IH to D_{n-1}. -/
private lemma Dn_bound : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    Etingof.IsRoot n (Etingof.DynkinType.D n hn).adj x →
    (∀ i, 0 ≤ x i) → ∀ i, x i < 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x hr hpos
    by_cases hm4 : m = 3
    · subst hm4; exact D4_bound x hr hpos
    · have hm' : 4 ≤ m := by omega
      have hge := (Dn_qform_ge_sq_and_posDef (m + 1) hm x).1
      have hq := hr.2
      have hx0_bound : x ⟨0, by omega⟩ ≤ 1 := by nlinarith [sq_nonneg (x ⟨0, by omega⟩ - 1)]
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by simp [tail]
      have htail_pos : ∀ i, 0 ≤ tail i := fun i => hpos i.succ
      -- Helper to lift tail bounds to x bounds
      suffices h : ∀ j : Fin m, tail j < 3 by
        intro i
        by_cases hi : i.val = 0
        · have : i = ⟨0, by omega⟩ := Fin.ext hi; rw [this]; omega
        · have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this; exact h j
      have hpeel' := hpeel; rw [hq, show x (0 : Fin (m + 1)) = x ⟨0, by omega⟩ from rfl] at hpeel'
      by_cases hx0 : x ⟨0, by omega⟩ = 0
      · -- x₀ = 0: tail is a D_m root
        have hq_tail : dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (Etingof.DynkinType.D m hm').adj).mulVec tail) = 2 := by
          have h1 : x ⟨0, by omega⟩ ^ 2 = 0 := by rw [hx0]; ring
          have h2 : x ⟨0, by omega⟩ * x ⟨1, by omega⟩ = 0 := by rw [hx0]; ring
          linarith [hpeel', h1, h2]
        have htail_ne : tail ≠ 0 := by
          intro h; apply hr.1; ext i
          by_cases hi : i.val = 0
          · have : i = ⟨0, by omega⟩ := Fin.ext hi; rw [this]; exact hx0
          · have : ∃ j : Fin m, i = j.succ :=
              ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
            obtain ⟨j, rfl⟩ := this; exact congr_fun h j
        exact ih hm' tail ⟨htail_ne, hq_tail⟩ htail_pos
      · -- x₀ = 1: use cascade lemma
        have hx0_1 : x ⟨0, by omega⟩ = 1 := by
          have h0 := hpos ⟨0, by omega⟩; omega
        have hq_tail : dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (Etingof.DynkinType.D m hm').adj).mulVec tail) =
            2 * tail ⟨0, by omega⟩ := by
          rw [htail0]
          have h1 : x ⟨0, by omega⟩ ^ 2 = 1 := by rw [hx0_1]; ring
          have h2 : x ⟨0, by omega⟩ * x ⟨1, by omega⟩ = x ⟨1, by omega⟩ := by rw [hx0_1]; ring
          linarith [hpeel', h1, h2]
        have hge_tail := (Dn_qform_ge_sq_and_posDef m hm' tail).1
        rw [htail0] at hge_tail
        have hx1_bound : x ⟨1, by omega⟩ ≤ 2 := by
          nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
        have htail0_le : tail ⟨0, by omega⟩ ≤ 2 := by rw [htail0]; exact hx1_bound
        exact Dn_cascade_bound m hm' tail hq_tail htail0_le htail_pos

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
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons 0 w)
  · -- MapsTo forward: v with v₀=0 → tail in D_m roots
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    have hmem := hv.1
    have hv0 : v 0 = 0 := hv.2
    simp only [Finset.mem_coe, rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hmem
    refine ⟨?_, ?_⟩
    · -- tail ≠ 0
      intro htail
      apply hmem.1; funext i; simp only [Pi.zero_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact_mod_cast hv0
      · have := congr_fun htail j; simp only [Function.comp, Pi.zero_apply] at this; exact this
    · -- q_{D_m}(tail) = 2: use peel + v₀=0
      have hpeel := Dn_qform_peel m hm (fun i => (v i : ℤ))
      -- Normalize composition in hpeel to match goal
      have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ =
          fun i ↦ (↑↑((v ∘ Fin.succ) i) : ℤ) := rfl
      rw [hcomp] at hpeel
      rw [hmem.2] at hpeel
      have hv0z : (↑↑(v 0) : ℤ) = 0 := by exact_mod_cast hv0
      have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 0 := by rw [hv0z]; ring
      have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 0 := by rw [hv0z]; ring
      linarith [hpeel, h0sq, h0prod]
  · -- MapsTo backward: w in D_m roots → cons 0 w in filter
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter]
    simp only [Finset.mem_coe, rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hw
    set v : Fin (m + 1) → Fin 3 := Fin.cons 0 w with hv_def
    constructor
    · simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro heq
        apply hw.1; funext i
        have := congr_fun heq (Fin.succ i)
        simp only [hv_def, Fin.cons_succ, Pi.zero_apply] at this; exact this
      · have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
        have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑↑(w i) : ℤ) := by
          funext i; simp [hv_def, Fin.cons_succ]
        rw [hcomp] at hpeel
        have h0 : (↑↑(v 0) : ℤ) = 0 := by simp [hv_def, Fin.cons_zero]
        have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 0 := by rw [h0]; ring
        have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 0 := by rw [h0]; ring
        linarith [hpeel, hw.2, h0sq, h0prod]
    · show v 0 = 0
      simp [hv_def, Fin.cons_zero]
  · -- Left inverse: cons 0 (v ∘ succ) = v for v with v₀=0
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact hv.2.symm
    · simp only [Function.comp, Fin.cons_succ]
  · -- Right inverse: (cons 0 w) ∘ succ = w
    intro w _
    funext i; simp only [Function.comp, Fin.cons_succ]

/-- No D_n root has first coordinate equal to 2. -/
private lemma Dn_no_coord2_at_zero : ∀ (n : ℕ) (hn : 4 ≤ n) (v : Fin n → Fin 3),
    v ∈ rootCountFinset n (Etingof.DynkinType.D n hn).adj 3 →
    v ⟨0, by omega⟩ ≠ 2 := by
  intro n hn v hv hv0
  simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hne, hq⟩ := hv
  set x : Fin n → ℤ := fun i => (v i : ℤ)
  have hge := (Dn_qform_ge_sq_and_posDef n hn x).1
  rw [hq] at hge
  have hv0z : x ⟨0, by omega⟩ = 2 := by
    simp [x]; exact_mod_cast congr_arg Fin.val hv0
  nlinarith [hv0z, sq_nonneg (x ⟨0, by omega⟩ - 1)]

/-- Count of vectors with v₀ = 2, q_{D_n} = 4, all coords in Fin 3. -/
private def qFourFinset (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n := by omega) :
    Finset (Fin n → Fin 3) :=
  (Finset.univ : Finset (Fin n → Fin 3)).filter fun v =>
    v ⟨0, hn⟩ = 2 &&
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
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons 2 w)
  · -- MapsTo forward
    intro v hv
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    have hv0 := hv.1
    have hq := hv.2
    -- Use peel lemma
    have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
    have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ =
        fun i ↦ (↑↑((v ∘ Fin.succ) i) : ℤ) := rfl
    rw [hcomp] at hpeel
    rw [hq] at hpeel
    -- hpeel: 4 = q_tail + 2*↑↑(v 0)² - 2*↑↑(v 0)*↑↑(v ⟨1,_⟩)
    have h0z : (↑↑(v 0) : ℤ) = 2 := by
      have := congr_arg Fin.val hv0; simp at this; omega
    have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 4 := by rw [h0z]; ring
    have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 2 * ↑↑(v ⟨1, by omega⟩) := by
      rw [h0z]
    -- From hpeel: q_tail = 4 - 8 + 4*v₁ = 4*v₁ - 4
    -- Since q_tail ≥ (v₁)² ≥ 0, we get v₁ ≥ 1
    -- If v₁ = 0: q_tail = -4 < 0, contradiction with posDef
    -- If v₁ = 1: q_tail = 0, tail = 0, but v₁ = tail₀ = 1 ≠ 0, contradiction
    -- So v₁ = 2 and q_tail = 4
    -- First show v₁ = 2, which means (v ∘ Fin.succ) 0 = 2
    have hv1bound : (↑↑(v ⟨1, by omega⟩) : ℤ) ∈ ({0, 1, 2} : Set ℤ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have := (v ⟨1, by omega⟩).2; omega
    have hge := (Dn_qform_ge_sq_and_posDef m hm (fun i => (↑↑((v ∘ Fin.succ) i) : ℤ))).1
    -- hge: (tail ⟨0,_⟩)² ≤ q_tail = (v ⟨1,_⟩)²
    -- But tail ⟨0,_⟩ = (v ∘ succ) ⟨0,_⟩ = v ⟨1,_⟩
    have htail0 : (↑↑((v ∘ Fin.succ) ⟨0, by omega⟩) : ℤ) = ↑↑(v ⟨1, by omega⟩) := rfl
    rw [htail0] at hge
    -- From hpeel + h0sq + h0prod: q_tail = 4*v₁ - 4
    -- From hge: v₁² ≤ q_tail = 4*v₁ - 4
    -- So v₁² - 4*v₁ + 4 ≤ 0, i.e., (v₁-2)² ≤ 0, so v₁ = 2
    have hv1eq : (↑↑(v ⟨1, by omega⟩) : ℤ) = 2 := by
      nlinarith [hpeel, h0sq, h0prod, hge, sq_nonneg ((↑↑(v ⟨1, by omega⟩) : ℤ) - 2)]
    constructor
    · -- (v ∘ succ) ⟨0,_⟩ = 2
      have : (v ∘ Fin.succ) ⟨0, by omega⟩ = v ⟨1, by omega⟩ := rfl
      rw [this]; exact Fin.ext (by have := hv1eq; omega)
    · -- q_tail = 4
      linarith [hpeel, h0sq, h0prod, hv1eq]
  · -- MapsTo backward
    intro w hw
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
    set v : Fin (m + 1) → Fin 3 := Fin.cons 2 w with hv_def
    constructor
    · show v ⟨0, by omega⟩ = 2
      simp [hv_def, Fin.cons_zero]
    · have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
      have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑↑(w i) : ℤ) := by
        funext i; simp [hv_def, Fin.cons_succ]
      rw [hcomp] at hpeel
      have h0 : (↑↑(v 0) : ℤ) = 2 := by simp [hv_def, Fin.cons_zero]
      have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 4 := by rw [h0]; ring
      have hw0z : (↑↑(w ⟨0, by omega⟩) : ℤ) = 2 := congrArg (fun x => (↑↑x : ℤ)) hw.1
      -- v ⟨1,_⟩ = w ⟨0,_⟩ since v = Fin.cons 2 w
      have hv1z : (↑↑(v ⟨1, by omega⟩) : ℤ) = ↑↑(w ⟨0, by omega⟩) := by
        simp only [hv_def]; rfl
      have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 2 * ↑↑(w ⟨0, by omega⟩) := by
        rw [h0, hv1z]
      linarith [hpeel, h0sq, h0prod, hw0z, hw.2]
  · -- Left inverse
    intro v hv
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact hv.1.symm
    · simp only [Function.comp, Fin.cons_succ]
  · -- Right inverse
    intro w _
    funext i; simp only [Function.comp, Fin.cons_succ]

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
  sorry

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
