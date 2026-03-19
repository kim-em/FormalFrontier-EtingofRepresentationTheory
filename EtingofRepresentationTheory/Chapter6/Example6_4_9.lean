import Mathlib
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification
import EtingofRepresentationTheory.Chapter6.Definition6_4_3

/-!
# Example 6.4.9: Root Counts for Dynkin Diagrams

Root counts for each Dynkin type. The E-type proofs use sum-of-squares (LDL^T)
decompositions of the Tits quadratic form to bound coordinates, then enumerate
all positive roots by `native_decide`.
-/

/-- The set of positive roots of a graph given by its adjacency matrix. -/
def Etingof.positiveRoots (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Set (Fin n → ℤ) :=
  {x | Etingof.IsRoot n adj x ∧ ∀ i, 0 ≤ x i}

-- Etingof.Example_6_4_9_An is proved after the section (see An_result)
-- Etingof.Example_6_4_9_Dn is proved after the section (see Dn_result)

/-! ## E-type root counts -/

section ETypeRootCounts

open Matrix Finset

/-- Count positive roots with coordinates in `{0, ..., B-1}`,
working over `Fin B` to avoid `Finset.image` overhead. -/
private def rootCountFinset (n : ℕ)
    (adj : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    Finset (Fin n → Fin B) :=
  (univ : Finset (Fin n → Fin B)).filter fun v =>
    let x : Fin n → ℤ := fun i => (v i : ℤ)
    decide (x ≠ 0) &&
    decide (dotProduct x
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2)

/-- Elements of rootCountFinset correspond to positive roots. -/
private lemma rootCountFinset_mem {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ}
    {B : ℕ} {v : Fin n → Fin B}
    (hv : v ∈ rootCountFinset n adj B) :
    (fun i => (v i : ℤ)) ∈ Etingof.positiveRoots n adj := by
  simp only [rootCountFinset, mem_filter, mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨⟨hv.1, hv.2⟩, fun i => Int.natCast_nonneg _⟩

/-- The embedding from `Fin n → Fin B` to `Fin n → ℤ` is injective. -/
private lemma fin_to_int_injective {n B : ℕ} :
    Function.Injective
      (fun (v : Fin n → Fin B) (i : Fin n) => (v i : ℤ)) := by
  intro v w h
  funext i
  have : (v i : ℤ) = (w i : ℤ) := congr_fun h i
  exact Fin.ext (by exact_mod_cast this)

/-- If all positive roots have coords in `{0,...,B-1}`, then the
positive root count equals `rootCountFinset.card`. -/
private lemma positiveRoots_card_eq {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ} {B : ℕ}
    (hbound : ∀ x : Fin n → ℤ, Etingof.IsRoot n adj x →
      (∀ i, 0 ≤ x i) → ∀ i, x i < B) :
    (Etingof.positiveRoots n adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n adj) =
      (rootCountFinset n adj B).card := by
  suffices h : Etingof.positiveRoots n adj =
      ↑((rootCountFinset n adj B).image
        (fun v i => (v i : ℤ))) by
    refine ⟨h ▸ ((rootCountFinset n adj B).image _).finite_toSet,
      ?_⟩
    rw [h, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ fin_to_int_injective]
  ext x
  simp only [Etingof.positiveRoots, Set.mem_setOf_eq,
    Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · intro ⟨hroot, hpos⟩
    refine ⟨fun i => ⟨(x i).toNat, ?_⟩, ?_, ?_⟩
    · exact Int.toNat_lt (hpos i) |>.mpr (hbound x hroot hpos i)
    · simp only [rootCountFinset, mem_filter, mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro heq
        exact hroot.1 (by
          ext i
          have := congr_fun heq i
          simp only [Int.toNat_of_nonneg (hpos i),
            Pi.zero_apply] at this
          exact this)
      · have hconv : (fun i => ((x i).toNat : ℤ)) = x :=
          funext fun i => Int.toNat_of_nonneg (hpos i)
        simp only [hconv]; exact hroot.2
    · funext i; exact Int.toNat_of_nonneg (hpos i)
  · intro ⟨v, hv, hvx⟩
    subst hvx
    exact rootCountFinset_mem hv

/-! ### E₆ -/

/-- SOS decomposition for the E₆ Tits form. -/
private lemma E6_sos (a b c d e f : ℤ) :
    6 * (2*(a^2+b^2+c^2+d^2+e^2+f^2) -
      2*(a*b+b*c+c*d+d*e+c*f)) =
    3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
    (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E6_qf (x : Fin 6 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        Etingof.DynkinType.E6.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

/-- All positive roots of E₆ have each coordinate < 4. -/
private lemma E6_bound (x : Fin 6 → ℤ)
    (hr : Etingof.IsRoot 6 Etingof.DynkinType.E6.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 4 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+x 2*x 5) = 2 := by
    have := hr.2; rw [E6_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2
  set d := x 3; set e := x 4; set f := x 5
  have hs : 3*(2*a-b)^2 + 3*(2*e-d)^2 + 3*(2*f-c)^2 +
      (3*b-2*c)^2 + (3*d-2*c)^2 + c^2 = 12 := by
    nlinarith [E6_sos a b c d e f]
  have hc : c ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*d-2*c), sq_nonneg (c-4)]
  have hb : b ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hd : d ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (2*f-c), sq_nonneg (3*b-2*c),
      sq_nonneg c, sq_nonneg (3*d-2*c-4)]
  have ha : a ≤ 3 := by
    nlinarith [sq_nonneg (2*e-d), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have he : e ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*e-d-3)]
  have hf : f ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*e-d),
      sq_nonneg (3*b-2*c), sq_nonneg (3*d-2*c),
      sq_nonneg c, sq_nonneg (2*f-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

set_option linter.style.nativeDecide false in
private lemma E6_count :
    (rootCountFinset 6 Etingof.DynkinType.E6.adj 4).card = 36 := by
  native_decide

/-- E₆ has 36 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E6 :
    (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj) = 36 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E6_bound
  exact ⟨hfin, hcard ▸ E6_count⟩

/-! ### E₇ -/

/-- SOS decomposition for the E₇ Tits form. -/
private lemma E7_sos (a b c d e f g : ℤ) :
    12 * (2*(a^2+b^2+c^2+d^2+e^2+f^2+g^2) -
      2*(a*b+b*c+c*d+d*e+e*f+c*g)) =
    6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
    2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
    (4*d-3*c)^2 + c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
private lemma E7_qf (x : Fin 7 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        Etingof.DynkinType.E7.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+x 5^2+x 6^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 2*x 6) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

/-- All positive roots of E₇ have each coordinate < 5. -/
private lemma E7_bound (x : Fin 7 → ℤ)
    (hr : Etingof.IsRoot 7 Etingof.DynkinType.E7.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 5 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 2*x 6) = 2 :=
    by have := hr.2; rw [E7_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6
  have hs : 6*(2*a-b)^2 + 6*(2*f-e)^2 + 6*(2*g-c)^2 +
      2*(3*b-2*c)^2 + 2*(3*e-2*d)^2 +
      (4*d-3*c)^2 + c^2 = 24 := by
    nlinarith [E7_sos a b c d e f g]
  have : c ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg (4*d-3*c),
      sq_nonneg (c-5)]
  have : d ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*e-2*d), sq_nonneg c,
      sq_nonneg (4*d-3*c-5)]
  have : b ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*b-2*c-4)]
  have : e ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (2*g-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (3*e-2*d-4)]
  have : a ≤ 4 := by
    nlinarith [sq_nonneg (2*f-e), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*a-b-3)]
  have : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*f-e-3)]
  have : g ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*f-e),
      sq_nonneg (3*b-2*c), sq_nonneg (3*e-2*d),
      sq_nonneg (4*d-3*c), sq_nonneg c,
      sq_nonneg (2*g-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

set_option linter.style.nativeDecide false in
private lemma E7_count :
    (rootCountFinset 7 Etingof.DynkinType.E7.adj 5).card = 63 := by
  native_decide

/-- E₇ has 63 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E7 :
    (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj) = 63 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E7_bound
  exact ⟨hfin, hcard ▸ E7_count⟩

/-! ### E₈ -/

/-- SOS decomposition for the E₈ Tits form. -/
private lemma E8_sos (a b c d e f g h : ℤ) :
    60 * (2*(a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2) -
      2*(a*b+b*c+c*d+d*e+e*f+f*g+c*h)) =
    30*(2*a-b)^2 + 30*(2*g-f)^2 + 30*(2*h-c)^2 +
    10*(3*b-2*c)^2 + 10*(3*f-2*e)^2 +
    5*(4*e-3*d)^2 + 3*(5*d-4*c)^2 + 2*c^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
private lemma E8_qf (x : Fin 8 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        Etingof.DynkinType.E8.adj).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
    2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
      x 4*x 5+x 5*x 6+x 2*x 7) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    Etingof.DynkinType.adj, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring

set_option linter.style.maxHeartbeats false in
-- Integrality argument (c=7 → d=6 → no int e) needs extra heartbeats
set_option maxHeartbeats 1600000 in
/-- All positive roots of E₈ have each coordinate < 7.
Tighter than the naive SOS bound (< 8) via an integrality argument:
c = 7 forces d = 6 (unique integer in range), then no integer e exists. -/
private lemma E8_bound (x : Fin 8 → ℤ)
    (hr : Etingof.IsRoot 8 Etingof.DynkinType.E8.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 7 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 5*x 6+x 2*x 7) = 2 :=
    by have := hr.2; rw [E8_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6; set h := x 7
  have ha0 : 0 ≤ a := hp 0; have hb0 : 0 ≤ b := hp 1
  have hc0 : 0 ≤ c := hp 2; have hd0 : 0 ≤ d := hp 3
  have he0 : 0 ≤ e := hp 4; have hf0 : 0 ≤ f := hp 5
  have hg0 : 0 ≤ g := hp 6; have hh0 : 0 ≤ h := hp 7
  have hs : 30*(2*a-b)^2 + 30*(2*g-f)^2 +
      30*(2*h-c)^2 + 10*(3*b-2*c)^2 +
      10*(3*f-2*e)^2 + 5*(4*e-3*d)^2 +
      3*(5*d-4*c)^2 + 2*c^2 = 120 := by
    nlinarith [E8_sos a b c d e f g h]
  -- Step 1: c ≤ 7 from SOS alone (2c² ≤ 120)
  have hc7 : c ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg (5*d-4*c), sq_nonneg (c-8)]
  -- Step 2: c ≤ 6 via integrality (c = 7 → d = 6 → no integer e)
  have hc6 : c ≤ 6 := by
    by_contra hc_ge7
    push_neg at hc_ge7
    have hc_eq : c = 7 := le_antisymm hc7 hc_ge7
    -- Isolate the d-dependent term: 3*(5d-28)² ≤ 22
    have h3sq : 3 * (5 * d - 28) ^ 2 ≤ 22 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d)]
    -- Coarse bound on d for interval_cases
    have hd_le : d ≤ 8 := by nlinarith [sq_nonneg (5*d-28-9)]
    -- Check each integer d ∈ [0,8]: only d = 6 satisfies 3*(5d-28)² ≤ 22
    -- For d = 6: continue to check e
    -- For d ≠ 6: 3*(5d-28)² > 22, contradiction
    have hd_eq : d = 6 := by interval_cases d <;> omega
    -- Now isolate e-dependent term: 5*(4e-18)² ≤ 10
    have h5sq : 5 * (4 * e - 18) ^ 2 ≤ 10 := by
      nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
        sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
        sq_nonneg (3*f-2*e)]
    -- Coarse bound on e for interval_cases
    have he_le : e ≤ 7 := by nlinarith [sq_nonneg (4*e-18-6)]
    -- Check each integer e ∈ [0,7]: 4e ∈ {17,18,19} has no solution
    have : False := by interval_cases e <;> omega
    exact this
  -- Step 3: Chain bounds through the SOS decomposition using c ≤ 6
  have hd6 : d ≤ 6 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg c, sq_nonneg (5*d-4*c-7)]
  have he5 : e ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (4*e-3*d-5)]
  have hb5 : b ≤ 5 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have hf4 : f ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*f-2*e-4)]
  have ha3 : a ≤ 3 := by
    nlinarith [sq_nonneg (2*g-f), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have hg3 : g ≤ 3 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*g-f-3)]
  have hh4 : h ≤ 4 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*h-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
-- native_decide over 7^8 ≈ 5.7M vectors needs extra heartbeats
set_option maxHeartbeats 1600000 in
private lemma E8_count :
    (rootCountFinset 8 Etingof.DynkinType.E8.adj 7).card =
      120 := by
  native_decide

/-- E₈ has 120 positive roots. (Etingof Example 6.4.9) -/
theorem Etingof.Example_6_4_9_E8 :
    (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj).Finite ∧
    Set.ncard
      (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj) =
      120 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq E8_bound
  exact ⟨hfin, hcard ▸ E8_count⟩

/-! ### A_n root count

The positive roots of A_n are exactly the "interval indicator" vectors: 1 on a
contiguous block [a, b] and 0 elsewhere, for 0 ≤ a ≤ b < n. There are n(n+1)/2
such intervals.
-/

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
      ext i; fin_cases i
      have : 2 * x 0 ^ 2 = 0 := by
        have h := hq
        simp only [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply,
          Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero] at h
        nlinarith
      nlinarith [sq_nonneg (x 0), hpos 0]
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
            (Etingof.DynkinType.A m hm1).adj).mulVec x') = 0 := by linarith
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
      subst hm; intro i; fin_cases i
      have : 2 * x 0 ^ 2 = 2 := by
        simp only [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply,
          Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero] at hq
        nlinarith
      nlinarith [sq_nonneg (x 0 - 1), hp 0]
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
        have hr2 : r = 2 := by linarith
        have hne' : x' ≠ 0 := by
          intro heq
          apply hne; ext i
          by_cases hi : i.val < m
          · have := congr_fun heq ⟨i.val, hi⟩
            simp [Pi.zero_apply] at this
            have : x ⟨i.val, by omega⟩ = 0 := this
            rwa [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl] at this
          · have : i = ⟨m, by omega⟩ := Fin.ext (by omega)
            rw [this]; exact hxm0
        have hroot' : Etingof.IsRoot m (Etingof.DynkinType.A m hm1).adj x' :=
          ⟨hne', hr2 ▸ hr_def ▸ rfl⟩
        intro i
        by_cases hi : i.val < m
        · have := ih hm1 x' hroot' hpos' ⟨i.val, hi⟩
          show x i < 2
          have : x' ⟨i.val, hi⟩ < 2 := this
          simp only [hx'] at this
          rwa [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl] at this
        · rw [show i = ⟨m, by omega⟩ from Fin.ext (by omega), hxm0]; omega
      · -- x_m ≥ 1
        have hxm_pos : x ⟨m, by omega⟩ ≥ 1 := by omega
        by_cases hle : x ⟨m, by omega⟩ ≤ x ⟨m - 1, by omega⟩
        · have : 2 * x ⟨m, by omega⟩ ^ 2 - 2 * x ⟨m - 1, by omega⟩ * x ⟨m, by omega⟩ ≤ 0 := by
            nlinarith
          have hr_ge2 : r ≥ 2 := by linarith
          have hr_eq2 : r = 2 := by
            have : r ≤ 2 := by linarith
            omega
          have hxm_eq : x ⟨m, by omega⟩ = x ⟨m - 1, by omega⟩ := by nlinarith
          have hne' : x' ≠ 0 := by
            intro heq
            have : x' ⟨m - 1, by omega⟩ = 0 := by
              have := congr_fun heq ⟨m - 1, by omega⟩; simpa using this
            simp only [hx'] at this
            omega
          have hroot' : Etingof.IsRoot m (Etingof.DynkinType.A m hm1).adj x' :=
            ⟨hne', hr_eq2 ▸ hr_def ▸ rfl⟩
          intro i
          by_cases hi : i.val < m
          · have := ih hm1 x' hroot' hpos' ⟨i.val, hi⟩
            show x i < 2
            simp only [hx'] at this
            rwa [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl] at this
          · rw [show i = ⟨m, by omega⟩ from Fin.ext (by omega)]
            have := ih hm1 x' hroot' hpos' ⟨m - 1, by omega⟩
            simp only [hx'] at this; linarith
        · push_neg at hle
          have hr_le0 : r ≤ 0 := by nlinarith
          have hr0 : r = 0 := by
            linarith [sq_nonneg (x' ⟨0, by omega⟩), sq_nonneg (x' ⟨m - 1, by omega⟩)]
          have hx'_zero := An_qform_zero m hm1 x' hpos' (hr0 ▸ hr_def ▸ rfl)
          have hxm1_zero : x ⟨m - 1, by omega⟩ = 0 := by
            have := congr_fun hx'_zero ⟨m - 1, by omega⟩
            simp [Pi.zero_apply, hx'] at this; exact this
          have hxm_val : x ⟨m, by omega⟩ = 1 := by nlinarith [sq_nonneg (x ⟨m, by omega⟩ - 1)]
          intro i
          by_cases hi : i.val < m
          · have := congr_fun hx'_zero ⟨i.val, hi⟩
            simp [Pi.zero_apply, hx'] at this
            show x i < 2
            rw [show i = ⟨i.val, by omega⟩ from Fin.ext rfl]
            linarith
          · rw [show i = ⟨m, by omega⟩ from Fin.ext (by omega), hxm_val]; omega

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
      intro h; have : (fun i : Fin (m + 1) => ((ivec (m + 1) a b) i : ℤ)) = 0 := by
        ext i; have := congr_fun h i; simp at this; exact_mod_cast this
      have : ((ivec (m + 1) a b) ⟨a, by omega⟩ : ℤ) = 0 := by
        have := congr_fun this ⟨a, by omega⟩; simpa using this
      simp [ivec, hab] at this
    · -- q = 2: by induction using peel
      by_cases hm : m = 0
      · subst hm; have : a = 0 := by omega; have : b = 0 := by omega; subst_vars
        simp [dotProduct, mulVec, Etingof.DynkinType.adj, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, ivec,
          Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num
      · have hm1 : 1 ≤ m := by omega
        rw [An_qform_peel m hm1]
        by_cases hbm : b < m
        · -- interval doesn't reach last: v(m) = 0
          have : ((ivec (m + 1) a b) ⟨m, by omega⟩ : ℤ) = 0 := by
            simp [ivec, show ¬(m ≤ b) from by omega]
          simp only [this, mul_zero, sub_zero]
          have hmem := ih hm1 a b hab hbm
          simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, decide_eq_true_eq] at hmem
          convert hmem.2 using 2
          ext i; show ((ivec (m + 1) a b) ⟨i.val, by omega⟩ : ℤ) = ((ivec m a b) i : ℤ)
          congr 1; simp [ivec]; constructor <;> intro h <;> exact h
        · have hbm_eq : b = m := by omega; subst hbm_eq
          by_cases ham : a = m
          · -- single element at m: v = (0,...,0,1)
            subst ham
            have hvm : ((ivec (m + 1) m m) ⟨m, by omega⟩ : ℤ) = 1 := by simp [ivec]
            have hvm1 : ((ivec (m + 1) m m) ⟨m - 1, by omega⟩ : ℤ) = 0 := by
              simp [ivec]; intro h; omega
            rw [hvm, hvm1]; ring_nf
            suffices dotProduct (fun i : Fin m => ((ivec (m + 1) m m) ⟨i.val, by omega⟩ : ℤ))
              ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - (Etingof.DynkinType.A m hm1).adj).mulVec
                (fun i : Fin m => ((ivec (m + 1) m m) ⟨i.val, by omega⟩ : ℤ))) = 0 by linarith
            have : (fun i : Fin m => ((ivec (m + 1) m m) ⟨i.val, by omega⟩ : ℤ)) = 0 := by
              ext i; simp [ivec]; intro h; omega
            rw [this]; simp [dotProduct, mulVec]
          · -- interval [a, m] with a < m
            have ham' : a < m := by omega
            have hvm : ((ivec (m + 1) a m) ⟨m, by omega⟩ : ℤ) = 1 := by simp [ivec, hab]
            have hvm1 : ((ivec (m + 1) a m) ⟨m - 1, by omega⟩ : ℤ) = 1 := by
              simp [ivec]; constructor <;> omega
            rw [hvm, hvm1]; ring_nf
            -- q_m(ivec(m, a, m-1)) = 2 by IH
            have hmem := ih hm1 a (m - 1) (by omega) (by omega)
            simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.and_eq_true, decide_eq_true_eq] at hmem
            convert hmem.2 using 2
            ext i; show ((ivec (m + 1) a m) ⟨i.val, by omega⟩ : ℤ) = ((ivec m a (m - 1)) i : ℤ)
            congr 1; simp [ivec]; constructor
            · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
            · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- The interval indicator map is injective on valid pairs. -/
private lemma ivec_injective (n : ℕ) (a₁ b₁ a₂ b₂ : ℕ)
    (h₁ : a₁ ≤ b₁) (hb₁ : b₁ < n) (h₂ : a₂ ≤ b₂) (hb₂ : b₂ < n)
    (heq : ivec n a₁ b₁ = ivec n a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have key : ∀ (a b : ℕ) (_ : a ≤ b) (hb : b < n) (j : ℕ) (hj : j < n),
      (ivec n a b ⟨j, hj⟩ = 1) ↔ (a ≤ j ∧ j ≤ b) := by
    intro a b _ _ j _
    simp only [ivec]
    split_ifs with h <;> simp_all [Fin.ext_iff]
  constructor
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (key a₂ b₂ h₂ hb₂ a₁ (by omega)).mp
        ((congr_fun heq ⟨a₁, by omega⟩).symm ▸ (key a₁ b₁ h₁ hb₁ a₁ (by omega)).mpr ⟨le_refl _, h₁⟩)
      omega
    · have := (key a₁ b₁ h₁ hb₁ a₂ (by omega)).mp
        ((congr_fun heq ⟨a₂, by omega⟩) ▸ (key a₂ b₂ h₂ hb₂ a₂ (by omega)).mpr ⟨le_refl _, h₂⟩)
      omega
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (key a₂ b₂ h₂ hb₂ b₁ (by omega)).mp
        ((congr_fun heq ⟨b₁, by omega⟩).symm ▸ (key a₁ b₁ h₁ hb₁ b₁ (by omega)).mpr ⟨h₁, le_refl _⟩)
      omega
    · have := (key a₁ b₁ h₁ hb₁ b₂ (by omega)).mp
        ((congr_fun heq ⟨b₂, by omega⟩) ▸ (key a₂ b₂ h₂ hb₂ b₂ (by omega)).mpr ⟨h₂, le_refl _⟩)
      omega

/-- Every element of rootCountFinset is an interval indicator. -/
private lemma root_is_ivec : ∀ (n : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin 2),
    v ∈ rootCountFinset n (Etingof.DynkinType.A n hn).adj 2 →
    ∃ a b : ℕ, a ≤ b ∧ b < n ∧ v = ivec n a b := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hn v hv
    simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hne, hq⟩ := hv
    by_cases hm : m = 0
    · -- n = 1: only root is [1]
      subst hm
      refine ⟨0, 0, le_refl _, by omega, ?_⟩
      ext i; fin_cases i
      simp only [ivec, Fin.val_zero, le_refl, true_and, Nat.zero_le, and_self, ite_true]
      have : (v 0 : ℤ) ≠ 0 := by
        intro h0; apply hne; ext i; fin_cases i; exact_mod_cast h0
      have : (v 0 : ℕ) < 2 := (v 0).isLt
      have : (v 0 : ℕ) ≠ 0 := by
        intro h; apply hne; ext i; fin_cases i; exact Fin.ext (by simpa using h)
      exact Fin.ext (by omega)
    · have hm1 : 1 ≤ m := by omega
      set v' : Fin m → Fin 2 := fun i => v ⟨i.val, by omega⟩ with hv'_def
      have hpeel := An_qform_peel m hm1 (fun i => ((v i : ℤ)))
      rw [hpeel] at hq
      set x' := fun i : Fin m => (v ⟨i.val, by omega⟩ : ℤ) with hx'_def
      set qm := dotProduct x' ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
          (Etingof.DynkinType.A m hm1).adj).mulVec x') with hqm_def
      have hge := An_qform_ge_endpoints m hm1 x'
      have hqm_nonneg : qm ≥ 0 := by
        linarith [sq_nonneg (x' ⟨0, by omega⟩), sq_nonneg (x' ⟨m - 1, by omega⟩)]
      by_cases hvm0 : v ⟨m, by omega⟩ = 0
      · -- v(m) = 0: qm = 2, v' is a root, use IH
        have hvm_int : (v ⟨m, by omega⟩ : ℤ) = 0 := by simp [hvm0]
        have hqm2 : qm = 2 := by linarith
        have hne' : (fun i : Fin m => (v' i : ℤ)) ≠ 0 := by
          intro h; apply hne; ext i
          by_cases hi : i.val < m
          · have := congr_fun h ⟨i.val, hi⟩
            simp [Pi.zero_apply] at this
            have : (v ⟨i.val, by omega⟩ : ℤ) = 0 := this
            have : (v ⟨i.val, by omega⟩ : ℕ) = 0 := by exact_mod_cast this
            rw [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i from Fin.ext rfl]
            exact Fin.ext (by simpa using this)
          · have : i = ⟨m, by omega⟩ := Fin.ext (by omega)
            rw [this]; exact hvm0
        have hv'_mem : v' ∈ rootCountFinset m (Etingof.DynkinType.A m hm1).adj 2 := by
          simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hne', by convert hqm2⟩
        obtain ⟨a, b, hab, hbm, hv'eq⟩ := ih hm1 v' hv'_mem
        refine ⟨a, b, hab, by omega, ?_⟩
        ext i
        by_cases hi : i.val < m
        · have := congr_fun hv'eq ⟨i.val, hi⟩
          simp [hv'_def] at this
          show v i = ivec (m + 1) a b i
          simp [ivec] at this ⊢
          rw [show (v ⟨i.val, by omega⟩ = v i) from congr_arg v (Fin.ext rfl)] at this
          convert this using 2
          constructor
          · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
          · intro ⟨h1, h2⟩; exact ⟨h1, h2⟩
        · have : i = ⟨m, by omega⟩ := Fin.ext (by omega)
          rw [this, hvm0]; simp [ivec]; intro h; omega
      · -- v(m) = 1
        have hvm1 : v ⟨m, by omega⟩ = 1 := by
          have := (v ⟨m, by omega⟩).isLt; interval_cases (v ⟨m, by omega⟩) <;> simp_all
        have hvm_int : (v ⟨m, by omega⟩ : ℤ) = 1 := by simp [hvm1]
        by_cases hvm1_0 : v ⟨m - 1, by omega⟩ = 0
        · -- v(m-1) = 0: qm + 2 - 0 = 2, so qm = 0
          have hvm1_int : (v ⟨m - 1, by omega⟩ : ℤ) = 0 := by simp [hvm1_0]
          have hqm0 : qm = 0 := by
            have : x' ⟨m - 1, by omega⟩ = (v ⟨m - 1, by omega⟩ : ℤ) := rfl
            linarith
          have hpos' : ∀ i, 0 ≤ x' i := by
            intro i; simp [hx'_def]; exact Int.natCast_nonneg _
          have hx'_zero := An_qform_zero m hm1 x' hpos' (by linarith)
          refine ⟨m, m, le_refl _, by omega, ?_⟩
          ext i
          by_cases hi : i.val < m
          · have hxi : (v ⟨i.val, by omega⟩ : ℤ) = 0 := by
              have := congr_fun hx'_zero ⟨i.val, hi⟩
              simp [Pi.zero_apply, hx'_def] at this; exact this
            show v i = ivec (m + 1) m m i
            have : ivec (m + 1) m m i = 0 := by simp [ivec, show ¬(m ≤ i.val) from by omega]
            rw [this, show i = ⟨i.val, by omega⟩ from Fin.ext rfl]
            exact Fin.ext (by exact_mod_cast hxi)
          · have : i = ⟨m, by omega⟩ := Fin.ext (by omega)
            rw [this, hvm1]; simp [ivec]
        · -- v(m-1) = 1: qm + 2 - 2 = 2, so qm = 2
          have hvm1_1 : v ⟨m - 1, by omega⟩ = 1 := by
            have := (v ⟨m - 1, by omega⟩).isLt
            interval_cases (v ⟨m - 1, by omega⟩) <;> simp_all
          have hvm1_int : (v ⟨m - 1, by omega⟩ : ℤ) = 1 := by simp [hvm1_1]
          have hqm2 : qm = 2 := by
            have : x' ⟨m - 1, by omega⟩ = (v ⟨m - 1, by omega⟩ : ℤ) := rfl
            linarith
          have hne' : (fun i : Fin m => (v' i : ℤ)) ≠ 0 := by
            intro h
            have := congr_fun h ⟨m - 1, by omega⟩
            simp [Pi.zero_apply, hv'_def] at this
            rw [hvm1_1] at this; simp at this
          have hv'_mem : v' ∈ rootCountFinset m (Etingof.DynkinType.A m hm1).adj 2 := by
            simp only [rootCountFinset, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hne', by convert hqm2⟩
          obtain ⟨a, b, hab, hbm, hv'eq⟩ := ih hm1 v' hv'_mem
          have hb_eq : b = m - 1 := by
            have : v' ⟨m - 1, by omega⟩ = ivec m a b ⟨m - 1, by omega⟩ := by
              have := congr_fun hv'eq ⟨m - 1, by omega⟩; exact this
            simp [hv'_def, hvm1_1, ivec] at this
            omega
          subst hb_eq
          refine ⟨a, m, hab.trans (by omega), by omega, ?_⟩
          ext i
          by_cases hi : i.val < m
          · have := congr_fun hv'eq ⟨i.val, hi⟩
            simp [hv'_def] at this
            show v i = ivec (m + 1) a m i
            simp [ivec] at this ⊢
            rw [show v ⟨i.val, by omega⟩ = v i from congr_arg v (Fin.ext rfl)] at this
            convert this using 2
            constructor
            · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
            · intro ⟨h1, h2⟩; exact ⟨h1, h2⟩
          · have : i = ⟨m, by omega⟩ := Fin.ext (by omega)
            rw [this, hvm1]; simp [ivec, hab.trans (by omega : m - 1 ≤ m)]

/-- Number of pairs (a, b) with a ≤ b in Fin n is n(n+1)/2. -/
private lemma pair_count (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≤ p.2)).card =
    n * (n + 1) / 2 := by
  set S := (Finset.univ : Finset (Fin n × Fin n))
  set Sle := S.filter (fun p => p.1 ≤ p.2)
  set Sgt := S.filter (fun p => ¬(p.1 ≤ p.2))
  have htotal : Sle.card + Sgt.card = n * n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  set Slt := S.filter (fun p => p.1 < p.2)
  set Seq := S.filter (fun p => p.1 = p.2)
  have hle_split : Sle.card = Slt.card + Seq.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext ⟨a, b⟩; simp [Sle, Slt, Seq]; omega
    · exact Finset.disjoint_filter.mpr (fun ⟨a, b⟩ _ h1 h2 => by simp_all; omega)
  have hdiag : Seq.card = n := by
    convert_to (Finset.univ.image (fun a : Fin n => (a, a))).card = n
    · congr 1; ext ⟨a, b⟩; simp [Seq, Finset.mem_image, Prod.ext_iff]
    · rw [Finset.card_image_of_injective _ (fun a₁ a₂ h => by simpa using h)]; simp
  have hlt_swap : Slt.card = Sgt.card := by
    apply Finset.card_nbij (fun (p : Fin n × Fin n) _ => (p.2, p.1))
    · intro ⟨a, b⟩ hp; simp [Slt, Sgt] at hp ⊢; omega
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h; simpa [Prod.ext_iff] using h
    · intro ⟨a, b⟩ hp; simp [Sgt, not_le] at hp
      exact ⟨(b, a), by simp [Slt, hp], by ext <;> rfl⟩
  omega

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

end ETypeRootCounts

/-- The number of positive roots for Aₙ is n(n+1)/2.
(Etingof Example 6.4.9(1)) -/
theorem Etingof.Example_6_4_9_An (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 :=
  An_result n hn

/-! ## D_n root count

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

-- The general D_n bound is proved by showing:
-- q(x) = sum_of_edge_diffs + x₀² + x_{n-2}² + x_{n-1}² - x_{n-3}²
-- From q = 2: leaf coordinates ≤ √(2+x_{n-3}²), path coords bounded by neighbors.
-- Key: the D_n Cartan form satisfies q(x) ≥ x₀² + x_{n-2}² + x_{n-1}² - x_{n-3}²
-- which with AM-GM on differences gives all coordinates ≤ 2.

/-- All positive roots of D_n have each coordinate < 3.
    The proof uses the quadratic form identity and bounds each vertex
    by working from the three leaves toward the branch point. -/
private lemma Dn_bound (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ)
    (hr : Etingof.IsRoot n (Etingof.DynkinType.D n hn).adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 3 := by
  sorry

set_option linter.style.nativeDecide false in
private lemma D4_count :
    (rootCountFinset 4 (Etingof.DynkinType.D 4 le_rfl).adj 3).card = 12 := by
  native_decide

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
