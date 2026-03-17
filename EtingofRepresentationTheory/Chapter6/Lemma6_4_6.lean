import EtingofRepresentationTheory.Chapter6.Definition6_4_3
import EtingofRepresentationTheory.Chapter6.Lemma6_4_2

/-!
# Lemma 6.4.6: Roots are Positive or Negative

Let α be a root, α = Σᵢ kᵢ αᵢ. Then either kᵢ ≥ 0 for all i or kᵢ ≤ 0 for all i.

**Proof sketch:** Assume for contradiction that some kᵢ > 0 and some kⱼ < 0.
Define β = max(x, 0) (positive part) and γ = min(x, 0) (negative part), so x = β + γ.
Then B(β,β) ≥ 2 and B(γ,γ) ≥ 2 (positive definite + even), and B(β,γ) ≥ 0
(off-diagonal entries of adj are 0 or 1, disjoint support with opposite signs).
So B(x,x) = B(β,β) + 2B(β,γ) + B(γ,γ) ≥ 4, contradicting B(x,x) = 2.

## Mathlib correspondence

This is a specific combinatorial/algebraic lemma about Dynkin diagrams not in Mathlib.
The proof uses positive definiteness and the tree structure of Dynkin diagrams.
-/

/-- Abbreviation for the Cartan quadratic form. -/
private abbrev cartanQ (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)

/-- Every root of a Dynkin diagram has all nonnegative or all nonpositive coordinates
with respect to the simple root basis. (Etingof Lemma 6.4.6) -/
theorem Etingof.Lemma_6_4_6 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hdyn : Etingof.IsDynkinDiagram n adj)
    (x : Fin n → ℤ)
    (hroot : Etingof.IsRoot n adj x) :
    (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨i₀, hi₀⟩, ⟨j₀, hj₀⟩⟩ := h
  -- hi₀ : x i₀ < 0, hj₀ : 0 < x j₀
  set A := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hA_def
  -- Define positive and negative parts
  set β : Fin n → ℤ := fun i => max (x i) 0
  set γ : Fin n → ℤ := fun i => min (x i) 0
  have hsum : x = β + γ := by ext i; simp only [β, γ, Pi.add_apply]; omega
  have hβ_ne : β ≠ 0 := by
    intro heq; have := congr_fun heq j₀; simp only [β, Pi.zero_apply] at this; omega
  have hγ_ne : γ ≠ 0 := by
    intro heq; have := congr_fun heq i₀; simp only [γ, Pi.zero_apply] at this; omega
  have hβ_nonneg : ∀ i, 0 ≤ β i := fun i => le_max_right _ _
  have hγ_nonpos : ∀ i, γ i ≤ 0 := fun i => min_le_right _ _
  -- β i * γ i = 0 for all i (disjoint support)
  have hβγ_zero : ∀ i, β i * γ i = 0 := by
    intro i; simp only [β, γ]
    rcases le_or_gt (x i) 0 with h | h
    · simp [max_eq_right h, min_eq_left h]
    · simp [max_eq_left h.le, min_eq_right h.le]
  -- Step 1: B(β,β) ≥ 2
  have hBβ : 2 ≤ cartanQ n adj β := by
    have hpos : (0 : ℤ) < cartanQ n adj β := Etingof.Lemma_6_4_2_pos_def n adj hdyn β hβ_ne
    obtain ⟨k, hk⟩ : Even (cartanQ n adj β) := Etingof.Lemma_6_4_2_even n adj hdyn.1 hdyn.2.1 β
    omega
  -- Step 2: B(γ,γ) ≥ 2
  have hBγ : 2 ≤ cartanQ n adj γ := by
    have hpos : (0 : ℤ) < cartanQ n adj γ := Etingof.Lemma_6_4_2_pos_def n adj hdyn γ hγ_ne
    obtain ⟨k, hk⟩ : Even (cartanQ n adj γ) := Etingof.Lemma_6_4_2_even n adj hdyn.1 hdyn.2.1 γ
    omega
  -- Step 3: cross term ≥ 0
  -- cross = dotProduct β (A.mulVec γ) = 2·dotProduct β γ - dotProduct β (adj.mulVec γ)
  set cross := dotProduct β (A.mulVec γ)
  have hcross : 0 ≤ cross := by
    -- cross = ∑ᵢ βᵢ · ∑ⱼ (2δᵢⱼ - adj(i,j)) γⱼ
    -- Expand to: 2·∑ βᵢγᵢ - ∑ᵢ βᵢ · ∑ⱼ adj(i,j)γⱼ
    -- First sum = 0 (disjoint). Second ≤ 0 (adj ∈ {0,1}, β ≥ 0, γ ≤ 0).
    simp only [cross, dotProduct, Matrix.mulVec]
    have key : ∀ i : Fin n,
        0 ≤ β i * ∑ j,
          (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * γ j := by
      intro i
      -- Expand inner sum using Matrix.sub_apply, Matrix.smul_apply
      have inner_eq :
          ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * γ j =
          2 * γ i - ∑ j, adj i j * γ j := by
        simp_rw [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.sum_ite_eq, Finset.mem_univ]
      rw [inner_eq]
      -- β i * (2γ i - ∑ adj γ) = 2 · βᵢγᵢ - βᵢ · ∑ adj γ
      -- Case: β i = 0 → trivial
      rcases eq_or_lt_of_le (hβ_nonneg i) with hi | hi
      · simp [← hi]
      -- β i > 0, so γ i = 0 (from disjoint support: β i * γ i = 0)
      have hγi : γ i = 0 := by
        rcases mul_eq_zero.mp (hβγ_zero i) with h | h
        · linarith
        · exact h
      rw [hγi, mul_zero, zero_sub]
      -- Goal: 0 ≤ β i * (-(∑ j, adj i j * γ j))
      apply mul_nonneg hi.le
      rw [neg_nonneg]
      apply Finset.sum_nonpos
      intro j _
      rcases hdyn.2.2.1 i j with h0 | h1
      · simp [h0]
      · rw [h1, one_mul]; exact hγ_nonpos j
    exact Finset.sum_nonneg (fun i _ => key i)
  -- Step 4: cross' ≥ 0 (same argument, reversed roles)
  set cross' := dotProduct γ (A.mulVec β)
  have hcross' : 0 ≤ cross' := by
    simp only [cross', dotProduct, Matrix.mulVec]
    have key : ∀ i : Fin n,
        0 ≤ γ i * ∑ j,
          (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * β j := by
      intro i
      have inner_eq :
          ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * β j =
          2 * β i - ∑ j, adj i j * β j := by
        simp_rw [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.sum_ite_eq, Finset.mem_univ]
      rw [inner_eq]
      rcases eq_or_lt_of_le (hγ_nonpos i) with hi | hi
      · -- γ i = 0
        simp [hi]
      · -- γ i < 0, so β i = 0 (disjoint support)
        have hγi_neg : γ i < 0 := by linarith
        have hβi : β i = 0 := by
          rcases mul_eq_zero.mp (hβγ_zero i) with h | h
          · exact h
          · linarith
        rw [hβi, mul_zero, zero_sub]
        -- Goal: 0 ≤ γ i * -(∑ j, adj i j * β j)
        apply mul_nonneg_of_nonpos_of_nonpos (hγ_nonpos i)
        rw [neg_nonpos]
        apply Finset.sum_nonneg
        intro j _
        rcases hdyn.2.2.1 i j with h0 | h1
        · simp [h0]
        · rw [h1, one_mul]; exact hβ_nonneg j
    exact Finset.sum_nonneg (fun i _ => key i)
  -- Step 5: B(x,x) = B(β,β) + cross + cross' + B(γ,γ) by bilinearity
  have hBx : cartanQ n adj x =
      cartanQ n adj β + cross + cross' + cartanQ n adj γ := by
    change dotProduct x (A.mulVec x) = _
    conv_lhs => rw [hsum]
    simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add]
    ring
  -- Step 6: B(x,x) = 2 but B(x,x) ≥ 4
  have : cartanQ n adj x = 2 := hroot.2
  linarith
