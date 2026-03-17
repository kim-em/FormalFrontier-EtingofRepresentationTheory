import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Lemma 6.4.2: Properties of the Cartan Inner Product

(1) B is positive definite (follows from the definition of Dynkin diagram).

(2) B(x, x) takes only even values for x ∈ ℤⁿ.

## Mathlib correspondence

The positive-definiteness follows from the definition. The evenness property is a
direct computation using the structure of the Cartan matrix A = 2·Id - R.
-/

/-- (1) The bilinear form B associated to a Dynkin diagram is positive definite.
(Etingof Lemma 6.4.2(1)) -/
theorem Etingof.Lemma_6_4_2_pos_def (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hdyn : Etingof.IsDynkinDiagram n adj) (x : Fin n → ℤ) (hx : x ≠ 0) :
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) :=
  hdyn.2.2.2.2 x hx

-- Helper: off-diagonal sum of a symmetric function is even
private lemma even_sum_off_diag {n : ℕ} (f : Fin n → Fin n → ℤ)
    (hf_symm : ∀ i j, f i j = f j i)
    (hf_diag : ∀ i, f i i = 0) :
    Even (∑ i : Fin n, ∑ j : Fin n, f i j) := by
  -- Decompose: ∑ i j = (∑_{i<j} + ∑_{i=j} + ∑_{j<i}) f i j
  -- Diagonal is 0, lower = upper by symmetry, so total = 2 * upper
  -- Convert to product sum
  rw [← Finset.sum_product' (f := fun (i j : Fin n) => f i j)]
  -- Set up the three regions
  set S := (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))
  set upper := S.filter (fun p : Fin n × Fin n => p.1 < p.2)
  set diag := S.filter (fun p : Fin n × Fin n => p.1 = p.2)
  set lower := S.filter (fun p : Fin n × Fin n => p.2 < p.1)
  set g : Fin n × Fin n → ℤ := fun p => f p.1 p.2
  -- S = upper ∪ diag ∪ lower
  have h_partition : S = upper ∪ diag ∪ lower := by
    ext ⟨i, j⟩
    simp only [upper, diag, lower, S, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and, true_iff]
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h_disj_ud : Disjoint upper diag := by
    apply Finset.disjoint_filter.mpr
    intro ⟨i, j⟩ _ h1 h2; exact absurd (h2 ▸ h1) (lt_irrefl _)
  have h_disj_l : Disjoint (upper ∪ diag) lower := by
    rw [Finset.disjoint_union_left]
    constructor
    · apply Finset.disjoint_filter.mpr
      intro ⟨i, j⟩ _ h1 h2; exact absurd (lt_trans h1 h2) (lt_irrefl _)
    · apply Finset.disjoint_filter.mpr
      intro ⟨i, j⟩ _ h1 h2; exact absurd (h1 ▸ h2) (lt_irrefl _)
  rw [h_partition, Finset.sum_union h_disj_l, Finset.sum_union h_disj_ud]
  -- Diagonal sum = 0
  have hD : ∑ p ∈ diag, g p = 0 := Finset.sum_eq_zero (fun ⟨i, j⟩ hp => by
    simp only [diag, Finset.mem_filter] at hp
    simp [g, hp, hf_diag])
  -- Lower sum = upper sum via swap
  have hRL : ∑ p ∈ lower, g p = ∑ p ∈ upper, g p := by
    apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    · intro ⟨i, j⟩ hp
      have := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, this⟩
    · intro ⟨i, j⟩ hp
      have := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, this⟩
    · intro ⟨i, j⟩ _; rfl
    · intro ⟨i, j⟩ _; rfl
    · intro ⟨i, j⟩ _; simp only [g]; exact hf_symm _ _
  rw [hD, add_zero, hRL]
  -- Goal: Even (∑ x ∈ upper, f x.1 x.2 + ∑ p ∈ upper, g p)
  -- g = fun p => f p.1 p.2, so change the first sum to use g
  change Even (∑ p ∈ upper, g p + ∑ p ∈ upper, g p)
  rw [← two_mul]
  exact even_two_mul _

/-- (2) B(x, x) takes only even values for x ∈ ℤⁿ, where B is the bilinear form
of the Cartan matrix A = 2·Id - R. (Etingof Lemma 6.4.2(2)) -/
theorem Etingof.Lemma_6_4_2_even (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (x : Fin n → ℤ) :
    Even (dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)) := by
  -- Unfold to sums
  simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  -- Simplify each term
  have step1 : ∀ (i j : Fin n),
      ((2 • if i = j then (1 : ℤ) else 0) - adj i j) * x j =
      (if i = j then 2 * x j else 0) - adj i j * x j := by
    intro i j; split_ifs with h <;> simp_all
  simp_rw [step1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mul_sub, Finset.sum_sub_distrib]
  -- First sum: ∑ i, x i * (2 * x i) = 2 * ∑ i, x i ^ 2
  have h1 : ∑ i : Fin n, x i * (2 * x i) = 2 * ∑ i : Fin n, x i ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h1]
  -- Suffices: adj sum is even
  suffices h_adj : Even (∑ i : Fin n, x i * ∑ j : Fin n, adj i j * x j) from
    (even_two_mul _).sub h_adj
  -- Expand and rearrange
  simp_rw [Finset.mul_sum]
  have : ∀ (i j : Fin n), x i * (adj i j * x j) = adj i j * x i * x j := fun i j => by ring
  simp_rw [this]
  -- Apply the off-diagonal helper with f(i,j) = adj i j * x i * x j
  exact even_sum_off_diag (fun i j => adj i j * x i * x j)
    (fun i j => by change adj i j * x i * x j = adj j i * x j * x i; rw [hsymm.apply j i]; ring)
    (fun i => by change adj i i * x i * x i = 0; rw [hdiag]; ring)
