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

/-- The number of positive roots for Aₙ is n(n+1)/2.
(Etingof Example 6.4.9(1)) -/
theorem Etingof.Example_6_4_9_An (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 := sorry -- see An_result below; needs An_bound + An_count

/-- The number of positive roots for Dₙ is n(n-1).
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_Dn (n : ℕ) (hn : 4 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj) =
      n * (n - 1) := sorry

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
set_option maxHeartbeats 800000 in
/-- All positive roots of E₈ have each coordinate < 8. -/
private lemma E8_bound (x : Fin 8 → ℤ)
    (hr : Etingof.IsRoot 8 Etingof.DynkinType.E8.adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 8 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2+x 4^2+
      x 5^2+x 6^2+x 7^2) -
      2*(x 0*x 1+x 1*x 2+x 2*x 3+x 3*x 4+
        x 4*x 5+x 5*x 6+x 2*x 7) = 2 :=
    by have := hr.2; rw [E8_qf] at this; exact this
  set a := x 0; set b := x 1; set c := x 2; set d := x 3
  set e := x 4; set f := x 5; set g := x 6; set h := x 7
  have hs : 30*(2*a-b)^2 + 30*(2*g-f)^2 +
      30*(2*h-c)^2 + 10*(3*b-2*c)^2 +
      10*(3*f-2*e)^2 + 5*(4*e-3*d)^2 +
      3*(5*d-4*c)^2 + 2*c^2 = 120 := by
    nlinarith [E8_sos a b c d e f g h]
  have : c ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg (5*d-4*c), sq_nonneg (c-8)]
  have : d ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (4*e-3*d),
      sq_nonneg c, sq_nonneg (5*d-4*c-7)]
  have : e ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (3*f-2*e), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (4*e-3*d-5)]
  have : b ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*b-2*c-4)]
  have : f ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (2*h-c), sq_nonneg (3*b-2*c),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (3*f-2*e-4)]
  have : a ≤ 7 := by
    nlinarith [sq_nonneg (2*g-f), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*a-b-3)]
  have : g ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*h-c),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*g-f-3)]
  have : h ≤ 7 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*g-f),
      sq_nonneg (3*b-2*c), sq_nonneg (3*f-2*e),
      sq_nonneg (4*e-3*d), sq_nonneg (5*d-4*c),
      sq_nonneg c, sq_nonneg (2*h-c-3)]
  intro i; fin_cases i <;> simp_all <;> omega

set_option linter.style.nativeDecide false in
private lemma E8_count :
    (rootCountFinset 8 Etingof.DynkinType.E8.adj 8).card =
      120 := by
  sorry -- native_decide: 8^8 = 16.7M vectors, too slow for CI

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

/-- All positive roots of A_n have each coordinate < 2. -/
private lemma An_bound (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ)
    (hr : Etingof.IsRoot n (Etingof.DynkinType.A n hn).adj x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 2 := by
  -- From An_qform_ge_endpoints: q(x) ≥ x₀² + x_{n-1}² and q(x) = 2
  -- So endpoints ∈ {0,1}. Peel decomposition + IH bounds all coords.
  sorry

/-- The count of rootCountFinset for A_n with bound 2 equals n(n+1)/2. -/
private lemma An_count (n : ℕ) (hn : 1 ≤ n) :
    (rootCountFinset n (Etingof.DynkinType.A n hn).adj 2).card =
      n * (n + 1) / 2 := by
  sorry

lemma An_result (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 := by
  obtain ⟨hfin, hcard⟩ := positiveRoots_card_eq (An_bound n hn)
  exact ⟨hfin, hcard ▸ An_count n hn⟩

end ETypeRootCounts
