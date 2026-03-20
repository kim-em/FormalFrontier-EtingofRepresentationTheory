import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4

/-!
# Theorem: Classification of Dynkin Diagrams

Γ is a Dynkin diagram if and only if it is one of the following graphs:
- Aₙ (n ≥ 1): a path with n vertices
- Dₙ (n ≥ 4): a path on vertices 0,...,n-2 with an extra edge from vertex n-3 to vertex n-1
- E₆, E₇, E₈: the three exceptional Dynkin diagrams (path with branch at vertex 2)

## Mathlib correspondence

Mathlib has `CoxeterMatrix` with Coxeter-Dynkin data for classical types, but the
classification theorem for positive-definite graphs is not present. The graph theory
and quadratic form infrastructure exists but the classification itself is absent.

## Formalization note

We define `DynkinType` as an inductive type enumerating the five families, together
with their adjacency matrices. The classification theorem states that `IsDynkinDiagram`
(positive-definite Cartan form) is equivalent to being graph-isomorphic to one of these
standard types.
-/

/-- The five families of Dynkin diagrams: A_n (n ≥ 1), D_n (n ≥ 4), E₆, E₇, E₈. -/
inductive Etingof.DynkinType where
  | A (n : ℕ) (hn : 1 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E6
  | E7
  | E8

/-- The number of vertices (rank) of a Dynkin diagram. -/
def Etingof.DynkinType.rank : Etingof.DynkinType → ℕ
  | .A n _ => n
  | .D n _ => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The adjacency matrix of a Dynkin diagram of the given type.

- **A_n**: path graph 0—1—2—⋯—(n-1)
- **D_n**: path 0—1—⋯—(n-2) with branch edge (n-3)—(n-1)
- **E₆**: path 0—1—2—3—4 with branch edge 2—5
- **E₇**: path 0—1—2—3—4—5 with branch edge 2—6
- **E₈**: path 0—1—2—3—4—5—6 with branch edge 2—7 -/
def Etingof.DynkinType.adj : (t : Etingof.DynkinType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A _n _ => fun i j =>
      if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  | .D n _ => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨
          (j.val + 1 = i.val ∧ i.val ≤ n - 2)) ∨
         ((i.val = n - 3 ∧ j.val = n - 1) ∨
          (j.val = n - 3 ∧ i.val = n - 1))
      then 1 else 0
  | .E6 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 4) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 4)) ∨
         ((i.val = 2 ∧ j.val = 5) ∨ (j.val = 2 ∧ i.val = 5))
      then 1 else 0
  | .E7 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 5) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 5)) ∨
         ((i.val = 2 ∧ j.val = 6) ∨ (j.val = 2 ∧ i.val = 6))
      then 1 else 0
  | .E8 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 6) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 6)) ∨
         ((i.val = 2 ∧ j.val = 7) ∨ (j.val = 2 ∧ i.val = 7))
      then 1 else 0

namespace Etingof

open Matrix Finset

/-! ## Graph isomorphism preserves IsDynkinDiagram -/

/-- If `adj'` is the image of `adj` under a graph isomorphism `σ`, and `adj` is a
Dynkin diagram, then so is `adj'`. -/
lemma isDynkinDiagram_of_graph_iso {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {adj' : Matrix (Fin m) (Fin m) ℤ} (σ : Fin n ≃ Fin m)
    (hiso : ∀ i j, adj' (σ i) (σ j) = adj i j)
    (hD : IsDynkinDiagram n adj) : IsDynkinDiagram m adj' := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  -- Helper: rewrite adj' in terms of adj via σ.symm
  have rw_adj' : ∀ i j : Fin m, adj' i j = adj (σ.symm i) (σ.symm j) := by
    intro i j
    conv_lhs => rw [show i = σ (σ.symm i) from (σ.apply_symm_apply i).symm,
      show j = σ (σ.symm j) from (σ.apply_symm_apply j).symm]
    exact hiso _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by rw [rw_adj', rw_adj']; exact hsymm.apply _ _)
  · -- Zero diagonal
    intro i; rw [rw_adj']; exact hdiag _
  · -- 0-1 entries
    intro i j; rw [rw_adj']; exact h01 _ _
  · -- Connectivity
    intro i j
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn (σ.symm i) (σ.symm j)
    refine ⟨path.map σ, ?_, ?_, ?_⟩
    · -- head
      cases path with
      | nil => exact absurd hhead (by simp)
      | cons a _ => simp only [List.map, List.head?]; rw [List.head?] at hhead; exact congr_arg _ (Option.some.inj hhead ▸ σ.apply_symm_apply i)
    · -- last
      rw [List.getLast?_map]
      rw [hlast]; simp [σ.apply_symm_apply]
    · -- edges
      intro k hk
      have hk' : k + 1 < path.length := by rwa [List.length_map] at hk
      -- Convert List.get to getElem notation, then use getElem_map
      show adj' (path.map σ)[k] (path.map σ)[k + 1] = 1
      rw [List.getElem_map, List.getElem_map, hiso]
      exact hedges k hk'
  · -- Positive definiteness: quadratic form is invariant under graph isomorphism
    intro x hx
    have hx' : x ∘ σ ≠ 0 := by
      intro h; apply hx; ext i
      have := congr_fun h (σ.symm i); simp [Function.comp] at this; exact this
    specialize hpos (x ∘ σ) hx'
    -- Show xᵀ(2I - adj')x = (x∘σ)ᵀ(2I - adj)(x∘σ) by reindexing sums via σ
    suffices heq : dotProduct x ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj').mulVec x) =
        dotProduct (x ∘ σ) ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (x ∘ σ)) by
      linarith
    simp only [dotProduct, mulVec, Finset.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Function.comp]
    symm
    apply Fintype.sum_equiv σ; intro i; congr 1
    apply Fintype.sum_equiv σ; intro j
    simp only [hiso, σ.injective.eq_iff]

/-! ## D_n quadratic form infrastructure

For D_n, we define a recursive quadratic form `DnQF` that peels off vertex 0 at each step,
with D₄ as the base case. This mirrors the `pathQF` approach for A_n.
The key insight is that removing vertex 0 from D_n gives D_{n-1} (for n ≥ 5).
-/

/-- Recursive quadratic form for D_n, using ℕ → ℤ to avoid Fin casting.
    Base case is D₄, and each step peels off vertex 0:
    DnQF (m+1) x = 2x₀² - 2x₀x₁ + DnQF m (x ∘ (·+1)). -/
private def DnQF : ℕ → (ℕ → ℤ) → ℤ
  | 0, x => 2*x 0^2 + 2*x 1^2 + 2*x 2^2 + 2*x 3^2 -
             2*x 0*x 1 - 2*x 1*x 2 - 2*x 1*x 3
  | m + 1, x => 2 * x 0 ^ 2 - 2 * x 0 * x 1 + DnQF m (fun i => x (i + 1))

/-- DnQF m x ≥ (x 0)². Base case uses SOS decomposition of D₄; inductive step peels vertex 0. -/
private lemma DnQF_lower : ∀ (m : ℕ) (x : ℕ → ℤ), (x 0) ^ 2 ≤ DnQF m x := by
  intro m
  induction m with
  | zero =>
    intro x; simp only [DnQF]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
  | succ k ih =>
    intro x; simp only [DnQF]
    have := ih (fun i => x (i + 1))
    nlinarith [sq_nonneg (x 0 - x 1)]

/-- If DnQF m x ≤ 0, then x is zero on {0, ..., m+3}. -/
private lemma DnQF_le_zero_imp : ∀ (m : ℕ) (x : ℕ → ℤ),
    DnQF m x ≤ 0 → ∀ i, i ≤ m + 3 → x i = 0 := by
  intro m
  induction m with
  | zero =>
    intro x hle i hi
    simp only [DnQF] at hle
    have h0 : x 0 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 - x 1),
        sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
    have h1 : x 1 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
    have hle' : 2 * (x 2) ^ 2 + 2 * (x 3) ^ 2 ≤ 0 := by
      have : x 0 ^ 2 = 0 := by rw [h0]; ring
      have : x 1 ^ 2 = 0 := by rw [h1]; ring
      have : x 0 * x 1 = 0 := by rw [h0]; ring
      have : x 1 * x 2 = 0 := by rw [h1]; ring
      have : x 1 * x 3 = 0 := by rw [h1]; ring
      linarith
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have h3 : x 3 = 0 := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    interval_cases i <;> assumption
  | succ k ih =>
    intro x hle i hi
    have hshift_lower := DnQF_lower k (fun j => x (j + 1))
    simp only [DnQF] at hle
    have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0)]
    have htail : DnQF k (fun j => x (j + 1)) ≤ 0 := by nlinarith
    rcases i with _ | i
    · exact hx0
    · exact ih (fun j => x (j + 1)) htail i (by omega)

/-! ## Dn Cartan matrix recurrence

The D_n Cartan matrix has the same structure as A_n when peeling vertex 0:
the (n-1)×(n-1) sub-matrix obtained by removing row/col 0 from D_n is exactly D_{n-1}.
We use concrete index forms (k+5 instead of abstract n) to avoid Fin type class issues.
-/

/-- The D_{k+5} Cartan sub-matrix property: removing row/col 0 gives D_{k+4}. -/
private lemma cartan_Dn_succ' (k : ℕ) (i j : Fin (k + 4)) :
    (2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
      DynkinType.adj (.D (k + 5) (by omega))) (Fin.succ i) (Fin.succ j) =
    (2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
      DynkinType.adj (.D (k + 4) (by omega))) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, DynkinType.adj,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

/-- The D_{k+5} dot product recurrence: peel off vertex 0. -/
private lemma Dn_dotProduct_recurrence' (k : ℕ) (x : Fin (k + 5) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
      DynkinType.adj (.D (k + 5) (by omega))).mulVec x) =
    2 * (x 0) ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ +
    dotProduct (x ∘ Fin.succ) ((2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
      DynkinType.adj (.D (k + 4) (by omega))).mulVec (x ∘ Fin.succ)) := by
  set C := (2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
    DynkinType.adj (.D (k + 5) (by omega)))
  set C' := (2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
    DynkinType.adj (.D (k + 4) (by omega)))
  -- Split dotProduct at i = 0
  rw [show dotProduct x (C.mulVec x) =
      x 0 * (C.mulVec x) 0 + ∑ i : Fin (k + 4), x (Fin.succ i) * (C.mulVec x) (Fin.succ i) from
    Fin.sum_univ_succ (f := fun i => x i * (C.mulVec x) i)]
  -- Compute (C.mulVec x) 0 = 2*x(0) - x(1)
  have hmv0 : (C.mulVec x) 0 = 2 * x 0 - x ⟨1, by omega⟩ := by
    change ∑ j, C 0 j * x j = _
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ (f := fun j : Fin (k + 4) => C 0 (Fin.succ j) * x (Fin.succ j))]
    have hC00 : C 0 0 = 2 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_zero, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
    have hC01 : C 0 (Fin.succ (0 : Fin (k + 4))) = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
    have hrest : ∑ i : Fin (k + 3), C 0 (Fin.succ (Fin.succ i)) * x (Fin.succ (Fin.succ i)) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        have : C 0 (Fin.succ (Fin.succ j)) = 0 := by
          simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
            DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
          split_ifs <;> simp_all <;> omega
        rw [this, zero_mul]
    rw [hC00, hC01, hrest]
    have : x (Fin.succ (0 : Fin (k + 4))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hmv0]
  -- Decompose (C.mulVec x)(succ i)
  have hmv_succ : ∀ i : Fin (k + 4), (C.mulVec x) (Fin.succ i) =
      C (Fin.succ i) 0 * x 0 + (C'.mulVec (x ∘ Fin.succ)) i := by
    intro i; change ∑ j, C (Fin.succ i) j * x j = _
    rw [Fin.sum_univ_succ]; congr 1
    change _ = ∑ j, C' i j * (x ∘ Fin.succ) j
    apply Finset.sum_congr rfl; intro j _
    simp only [Function.comp]; congr 1
    simp only [C, C']
    exact cartan_Dn_succ' k i j
  simp_rw [hmv_succ, mul_add, Finset.sum_add_distrib]
  have hsum_C0 : ∑ i : Fin (k + 4), x (Fin.succ i) * (C (Fin.succ i) 0 * x 0) =
      -(x ⟨1, by omega⟩ * x 0) := by
    rw [Fin.sum_univ_succ]
    have hC10 : C (Fin.succ (0 : Fin (k + 4))) 0 = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    rw [hC10]
    have hrest : ∀ j : Fin (k + 3), C (Fin.succ (Fin.succ j)) 0 = 0 := by
      intro j
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    have : ∑ j : Fin (k + 3), x (Fin.succ (Fin.succ j)) *
        (C (Fin.succ (Fin.succ j)) 0 * x 0) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hrest]; ring)
    rw [this, add_zero]
    have : x (Fin.succ (0 : Fin (k + 4))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hsum_C0]
  rw [show ∑ i : Fin (k + 4), x (Fin.succ i) * (C'.mulVec (x ∘ Fin.succ)) i =
    dotProduct (x ∘ Fin.succ) (C'.mulVec (x ∘ Fin.succ)) from rfl]
  ring

/-- DnQF relates to the D_n dotProduct form. -/
private lemma DnQF_eq_dotProduct : ∀ (m : ℕ) (x : Fin (m + 4) → ℤ),
    DnQF m (fun i => if h : i < m + 4 then x ⟨i, h⟩ else 0) =
    dotProduct x ((2 • (1 : Matrix (Fin (m + 4)) (Fin (m + 4)) ℤ) -
      DynkinType.adj (.D (m + 4) (by omega))).mulVec x) := by
  intro m
  induction m with
  | zero =>
    intro x
    simp only [DnQF]
    set C := 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) - DynkinType.adj (.D 4 (by omega))
    have hC : C = !![2,-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
      ext i j; fin_cases i <;> fin_cases j <;> native_decide
    rw [hC]
    simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, vecHead]
    ring
  | succ k ih =>
    intro x
    set ext_x : ℕ → ℤ := fun i => if h : i < k + 5 then x ⟨i, h⟩ else 0
    show DnQF (k + 1) ext_x = _
    simp only [DnQF]
    have hx0 : ext_x 0 = x 0 := by simp [ext_x]
    have hx1 : ext_x 1 = x ⟨1, by omega⟩ := by simp [ext_x, show (1 : ℕ) < k + 5 from by omega]
    rw [hx0, hx1]
    set x' : Fin (k + 4) → ℤ := fun j => x ⟨j.val + 1, by omega⟩
    have hshift : (fun i => ext_x (i + 1)) =
        fun i => if h : i < k + 4 then x' ⟨i, h⟩ else 0 := by
      ext i; simp only [ext_x, x']
      by_cases hi : i < k + 4
      · simp [hi, show i + 1 < k + 5 from by omega]
      · simp [hi, show ¬(i + 1 < k + 5) from by omega]
    rw [hshift, ih x']
    rw [Dn_dotProduct_recurrence' k x]
    have hx'_eq : x' = x ∘ Fin.succ := by ext j; simp [x', Function.comp, Fin.succ]
    rw [hx'_eq]

/-- Positive definiteness for D_n Cartan form. -/
private lemma Dn_posDef (n : ℕ) (hn : 4 ≤ n) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      DynkinType.adj (.D n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  intro x hx
  rw [← DnQF_eq_dotProduct m x]
  by_contra h
  push_neg at h
  have hzero := DnQF_le_zero_imp m
    (fun i => if hi : i < m + 4 then x ⟨i, hi⟩ else 0) h
  apply hx; ext ⟨i, hi⟩
  have := hzero i (by omega)
  simp only [show (i < m + 4) = True from by simp; omega, dite_true] at this
  exact this

/-! ## A_n is a Dynkin diagram

For the path graph A_n, the Tits form q(x) = x^T(2I-adj)x satisfies the sum-of-squares
identity q(x) = x₀² + Σᵢ(xᵢ-xᵢ₊₁)² + x_{n-1}², from which positive definiteness follows.
-/

/-- Recursive quadratic form for A_n path graph, using ℕ → ℤ to avoid Fin casting.
  Peels off vertex 0 at each step: q_{n+1}(x) = 2x₀² - 2x₀x₁ + q_n(x∘(·+1)). -/
private def pathQF : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | 1, x => 2 * x 0 ^ 2
  | n + 2, x => 2 * x 0 ^ 2 - 2 * x 0 * x 1 + pathQF (n + 1) (fun i => x (i + 1))

/-- Lower bound: pathQF (m+1) x ≥ (x 0)² + (x m)².
    Parameterized by m to avoid subtraction in the inductive step. -/
private lemma pathQF_lower : ∀ (m : ℕ) (x : ℕ → ℤ),
    (x 0) ^ 2 + (x m) ^ 2 ≤ pathQF (m + 1) x := by
  intro m
  induction m with
  | zero => intro x; simp [pathQF]; nlinarith [sq_nonneg (x 0)]
  | succ k ih =>
    intro x
    simp only [pathQF]
    have ih' := ih (fun i => x (i + 1))
    -- ih' : (x 1)² + (x (k+1))² ≤ pathQF (k+1) (fun i => x (i+1))
    -- Goal: (x 0)² + (x (k+1))² ≤ 2*(x 0)² - 2*(x 0)*(x 1) + pathQF (k+1) (shift x)
    nlinarith [sq_nonneg (x 0 - x 1)]

/-- If pathQF (m+1) x ≤ 0 then x is zero on {0,...,m}. -/
private lemma pathQF_le_zero_imp : ∀ (m : ℕ) (x : ℕ → ℤ),
    pathQF (m + 1) x ≤ 0 → ∀ i, i ≤ m → x i = 0 := by
  intro m
  induction m with
  | zero =>
    intro x hle i hi
    have : x 0 = 0 := by
      simp [pathQF] at hle; nlinarith [sq_nonneg (x 0)]
    interval_cases i; exact this
  | succ k ih =>
    intro x hle i hi
    -- Use lower bound on the tail to extract x 0 = 0
    have htb := pathQF_lower k (fun j => x (j + 1))
    -- htb : (x 1)² + (x (k+1))² ≤ pathQF (k+1) (shift x)
    simp only [pathQF] at hle
    -- hle : 2*(x 0)² - 2*(x 0)*(x 1) + pathQF (k+1) (shift x) ≤ 0
    have hx0 : x 0 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x (k + 1))]
    have htail : pathQF (k + 1) (fun j => x (j + 1)) ≤ 0 := by nlinarith
    rcases i with _ | i
    · exact hx0
    · exact ih (fun j => x (j + 1)) htail i (by omega)

/-- The Cartan matrix of A_{k+2} restricted to {1,...,k+1} equals that of A_{k+1}. -/
private lemma cartan_An_succ (k : ℕ) (i j : Fin (k + 1)) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      DynkinType.adj (.A (k + 2) (by omega))) (Fin.succ i) (Fin.succ j) =
    (2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
      DynkinType.adj (.A (k + 1) (by omega))) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, DynkinType.adj,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> omega

/-- Cartan matrix entry C(0, succ(succ j)) = 0 for A_{k+2}. -/
private lemma cartan_An_zero_ge2 (k : ℕ) (j : Fin k) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      DynkinType.adj (.A (k + 2) (by omega))) 0 (Fin.succ (Fin.succ j)) = 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, DynkinType.adj,
    Fin.val_zero, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

/-- Cartan matrix entry C(succ i, 0) for A_{k+2}. -/
private lemma cartan_An_succ_zero (k : ℕ) (i : Fin (k + 1)) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      DynkinType.adj (.A (k + 2) (by omega))) (Fin.succ i) 0 =
    if (i : ℕ) = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, DynkinType.adj,
    Fin.val_zero, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

/-- The A_n quadratic form satisfies a recurrence: peeling off vertex 0. -/
private lemma An_dotProduct_recurrence (k : ℕ) (x : Fin (k + 2) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      DynkinType.adj (.A (k + 2) (by omega))).mulVec x) =
    2 * (x 0) ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ +
    dotProduct (x ∘ Fin.succ) ((2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
      DynkinType.adj (.A (k + 1) (by omega))).mulVec (x ∘ Fin.succ)) := by
  set C := (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
    DynkinType.adj (.A (k + 2) (by omega)))
  set C' := (2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
    DynkinType.adj (.A (k + 1) (by omega)))
  -- Step 1: Split dotProduct at i = 0
  rw [show dotProduct x (C.mulVec x) =
      x 0 * (C.mulVec x) 0 + ∑ i : Fin (k + 1), x (Fin.succ i) * (C.mulVec x) (Fin.succ i) from
    Fin.sum_univ_succ (f := fun i => x i * (C.mulVec x) i)]
  -- Step 2: Compute (C.mulVec x) 0 = 2*x(0) - x(1)
  have hmv0 : (C.mulVec x) 0 = 2 * x 0 - x ⟨1, by omega⟩ := by
    change ∑ j, C 0 j * x j = _
    rw [Fin.sum_univ_succ]
    -- First term is C 0 0 * x 0 = 2 * x 0
    have hC00 : C 0 0 = 2 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    -- Remaining sum: split off j=0 in Fin (k+1)
    rw [Fin.sum_univ_succ (f := fun j : Fin (k + 1) => C 0 (Fin.succ j) * x (Fin.succ j))]
    -- Second term: C 0 (succ 0) = C 0 1 = -1
    have hC01 : C 0 (Fin.succ (0 : Fin (k + 1))) = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    -- Remaining sum: C 0 (succ (succ j)) = 0 for all j
    have hrest : ∑ i : Fin k, C 0 (Fin.succ (Fin.succ i)) * x (Fin.succ (Fin.succ i)) = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [show C 0 (Fin.succ (Fin.succ j)) = 0 from cartan_An_zero_ge2 k j, zero_mul]
    rw [hC00, hC01, hrest]
    have : x (Fin.succ (0 : Fin (k + 1))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hmv0]
  -- Step 3: Decompose (C.mulVec x)(succ i) = C(succ i, 0)*x(0) + (C'.mulVec (x∘succ))(i)
  have hmv_succ : ∀ i : Fin (k + 1), (C.mulVec x) (Fin.succ i) =
      C (Fin.succ i) 0 * x 0 + (C'.mulVec (x ∘ Fin.succ)) i := by
    intro i
    change ∑ j, C (Fin.succ i) j * x j = _
    rw [Fin.sum_univ_succ]
    change C (Fin.succ i) 0 * x 0 + ∑ j : Fin (k + 1), C (Fin.succ i) (Fin.succ j) *
      x (Fin.succ j) = _
    congr 1
    change _ = ∑ j, C' i j * (x ∘ Fin.succ) j
    apply Finset.sum_congr rfl; intro j _
    simp only [Function.comp, C, C']
    rw [cartan_An_succ]
  simp_rw [hmv_succ]
  -- Step 4: Expand x(succ i) * (C(succ i,0)*x(0) + (C'.mulVec x')(i))
  simp only [mul_add, Finset.sum_add_distrib]
  -- Step 5: Evaluate ∑ x(succ i) * C(succ i, 0) * x(0)
  -- C(succ i, 0) = -1 if i=0, else 0
  have hsum_C0 : ∑ i : Fin (k + 1), x (Fin.succ i) * (C (Fin.succ i) 0 * x 0) =
      -(x ⟨1, by omega⟩ * x 0) := by
    -- Split off i = 0
    rw [Fin.sum_univ_succ]
    -- i = 0 term: C(succ 0, 0) = C(1, 0) = -1
    have hC10 : C (Fin.succ (0 : Fin (k + 1))) 0 = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    rw [hC10]
    -- Remaining terms: C(succ(succ j), 0) = 0 for all j
    have hrest : ∀ j : Fin k, C (Fin.succ (Fin.succ j)) 0 = 0 := by
      intro j
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        DynkinType.adj, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    have : ∑ j : Fin k, x (Fin.succ (Fin.succ j)) *
        (C (Fin.succ (Fin.succ j)) 0 * x 0) = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [hrest]; ring
    rw [this, add_zero]
    have : x (Fin.succ (0 : Fin (k + 1))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hsum_C0]
  -- Step 6: The remaining sum is dotProduct (x∘succ) (C'.mulVec (x∘succ))
  -- ∑ x(succ i) * (C'.mulVec (x∘succ))(i) = dotProduct (x∘succ) (C'.mulVec (x∘succ))
  rw [show ∑ i : Fin (k + 1), x (Fin.succ i) * (C'.mulVec (x ∘ Fin.succ)) i =
    dotProduct (x ∘ Fin.succ) (C'.mulVec (x ∘ Fin.succ)) from rfl]
  ring

/-- pathQF relates to the dotProduct form: pathQF n (x ∘ Fin.val) = xᵀ(2I-adj)x.
    We prove this by induction on n. -/
private lemma pathQF_eq_dotProduct (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ) :
    pathQF n (fun i => if h : i < n then x ⟨i, h⟩ else 0) =
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      DynkinType.adj (.A n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    -- n = 1: both sides = 2*(x 0)^2
    simp only [pathQF, show (0 : ℕ) < 1 from by omega, dite_true]
    simp only [dotProduct, mulVec]
    simp only [show Finset.univ (α := Fin (0 + 1)) = {0} from rfl, Finset.sum_singleton]
    have hmat : (2 • (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℤ) -
        DynkinType.adj (.A (0 + 1) (by omega))) 0 0 = 2 := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply,
        smul_eq_mul, DynkinType.adj, Fin.ext_iff, Fin.val_zero]
    rw [hmat]; simp [Fin.ext_iff]; ring
  | succ k ih =>
    -- n = k + 2
    set ext_x : ℕ → ℤ := fun i => if h : i < k + 2 then x ⟨i, h⟩ else 0
    show pathQF (k + 2) ext_x = _
    simp only [pathQF]
    -- ext_x 0 = x 0, ext_x 1 = x ⟨1, _⟩
    have hx0 : ext_x 0 = x 0 := by simp [ext_x]
    have hx1 : ext_x 1 = x ⟨1, by omega⟩ := by
      simp [ext_x, show (1 : ℕ) < k + 2 from by omega]
    rw [hx0, hx1]
    -- The shifted function matches the IH form with x' j = x ⟨j+1, _⟩
    set x' : Fin (k + 1) → ℤ := fun j => x ⟨j.val + 1, by omega⟩
    have hshift : (fun i => ext_x (i + 1)) =
        fun i => if h : i < k + 1 then x' ⟨i, h⟩ else 0 := by
      ext i; simp only [ext_x, x']
      by_cases hi : i < k + 1
      · simp [hi, show i + 1 < k + 2 from by omega]
      · simp [hi, show ¬(i + 1 < k + 2) from by omega]
    rw [hshift, ih (by omega) x']
    -- Use the recurrence
    rw [An_dotProduct_recurrence k x]
    -- x' and x ∘ Fin.succ are the same function
    have hx'_eq : x' = x ∘ Fin.succ := by ext j; simp [x', Function.comp, Fin.succ]
    rw [hx'_eq]

/-- Positive definiteness for A_n Cartan form. -/
private lemma An_posDef (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      DynkinType.adj (.A n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro x hx
  rw [← pathQF_eq_dotProduct (m + 1) (by omega) x]
  by_contra h
  push_neg at h
  have hzero := pathQF_le_zero_imp m
    (fun i => if hi : i < m + 1 then x ⟨i, hi⟩ else 0) h
  apply hx; ext ⟨i, hi⟩
  have := hzero i (by omega)
  simp only [show (i < m + 1) = True from by simp; omega, dite_true] at this
  exact this

/-- A_n (path graph) is a Dynkin diagram. -/
private lemma An_isDynkin (n : ℕ) (hn : 1 ≤ n) :
    IsDynkinDiagram n (DynkinType.adj (.A n hn)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by
      simp only [DynkinType.adj]; congr 1; exact propext or_comm)
  · -- Zero diagonal
    intro i; simp only [DynkinType.adj]; split_ifs with h
    · exact absurd h (by push_neg; constructor <;> omega)
    · rfl
  · -- 0-1 entries
    intro i j; simp only [DynkinType.adj]; split_ifs <;> simp
  · -- Connectivity: path graph on Fin n is connected
    intro i j
    by_cases hij : i.val ≤ j.val
    · -- Ascending path [i, i+1, ..., j]
      refine ⟨List.ofFn (fun (k : Fin (j.val - i.val + 1)) =>
        (⟨i.val + k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · -- head?
        rw [List.ofFn_succ, List.head?_cons]; simp
      · -- getLast?
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; ext; simp [Fin.last]; omega
      · -- edges
        intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, DynkinType.adj, Fin.val_mk]
        rw [if_pos (Or.inl (by omega))]
    · -- Descending path [i, i-1, ..., j]
      push_neg at hij
      refine ⟨List.ofFn (fun (k : Fin (i.val - j.val + 1)) =>
        (⟨i.val - k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · -- head?
        rw [List.ofFn_succ, List.head?_cons]; simp
      · -- getLast?
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; ext; simp [Fin.last]; omega
      · -- edges
        intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, DynkinType.adj, Fin.val_mk]
        rw [if_pos (Or.inr (by omega))]
  · -- Positive definiteness
    exact An_posDef n hn

/-- D_n (path with branch) is a Dynkin diagram. -/
private lemma Dn_isDynkin (n : ℕ) (hn : 4 ≤ n) :
    IsDynkinDiagram n (DynkinType.adj (.D n hn)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry: adj is symmetric (swap conditions in the disjunction)
    exact Matrix.IsSymm.ext (fun i j => by
      simp only [DynkinType.adj]; congr 1; exact propext ⟨fun h => by tauto, fun h => by tauto⟩)
  · -- Zero diagonal
    intro i; simp only [DynkinType.adj]; split_ifs with h
    · exfalso; rcases h with (⟨h1, _⟩ | ⟨h2, _⟩) | (⟨h3, h4⟩ | ⟨h5, h6⟩) <;> omega
    · rfl
  · -- 0-1 entries
    intro i j; simp only [DynkinType.adj]; split_ifs <;> simp
  · -- Connectivity: D_n is connected
    -- D_n: path 0—1—...—(n-2) with branch edge (n-3)—(n-1)
    intro i j
    -- Helper for main path connectivity (both vertices < n-1, ascending)
    have main_asc : ∀ (a b : Fin n), a.val < n - 1 → b.val < n - 1 → a.val ≤ b.val →
        ∃ path : List (Fin n), path.head? = some a ∧ path.getLast? = some b ∧
        ∀ k, (h : k + 1 < path.length) →
          (DynkinType.adj (.D n hn)) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
      intro a b ha hb hab
      refine ⟨List.ofFn (fun (k : Fin (b.val - a.val + 1)) =>
        (⟨a.val + k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · rw [List.ofFn_succ, List.head?_cons]; simp
      · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; simp only [Fin.ext_iff, Fin.val_mk, Fin.val_last]; omega
      · intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, DynkinType.adj, Fin.val_mk]
        rw [if_pos]; left; left; constructor <;> omega
    -- Helper for descending main path
    have main_desc : ∀ (a b : Fin n), a.val < n - 1 → b.val < n - 1 → b.val < a.val →
        ∃ path : List (Fin n), path.head? = some a ∧ path.getLast? = some b ∧
        ∀ k, (h : k + 1 < path.length) →
          (DynkinType.adj (.D n hn)) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
      intro a b ha hb hab
      refine ⟨List.ofFn (fun (k : Fin (a.val - b.val + 1)) =>
        (⟨a.val - k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · rw [List.ofFn_succ, List.head?_cons]; simp
      · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; simp only [Fin.ext_iff, Fin.val_mk, Fin.val_last]; omega
      · intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, DynkinType.adj, Fin.val_mk]
        rw [if_pos]; left; right; constructor <;> omega
    -- Now handle all cases
    by_cases hi : i.val = n - 1
    · by_cases hj : j.val = n - 1
      · -- i = j = n-1
        have hij : i = j := Fin.ext (by omega)
        subst hij
        exact ⟨[i], by simp, by simp, fun k hk => by simp at hk⟩
      · -- i = n-1, j on main path: route through n-3
        have hjlt : j.val < n - 1 := by omega
        -- Split into j < n-3, j = n-3, j = n-2
        rcases Nat.lt_or_eq_of_le (show j.val ≤ n - 2 by omega) with hjlt2 | hjn2
        · rcases Nat.lt_or_eq_of_le (show j.val ≤ n - 3 by omega) with hjlt3 | hjn3
          · -- j < n-3: get main path from n-3 to j, prepend n-1
            obtain ⟨path, hhead, hlast, hedges⟩ := main_desc ⟨n - 3, by omega⟩ j
              (show (n - 3 : ℕ) < n - 1 by omega) hjlt (show j.val < n - 3 from hjlt3)
            refine ⟨⟨n - 1, by omega⟩ :: path, ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · cases path with
              | nil => simp at hhead
              | cons p ps => simp only [List.getLast?_cons_cons]; exact hlast
            · intro k hk
              simp only [List.length_cons] at hk
              match k with
              | 0 =>
                cases path with
                | nil => simp at hhead
                | cons p ps =>
                  simp only [List.head?_cons, Option.some.injEq] at hhead
                  simp only [List.get_eq_getElem, List.getElem_cons_zero,
                    List.getElem_cons_succ]
                  rw [hhead]; simp only [DynkinType.adj]
                  rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
              | k + 1 =>
                simp only [List.get_eq_getElem, List.getElem_cons_succ]
                exact hedges k (by omega)
          · -- j = n-3: path [n-1, n-3]
            refine ⟨[⟨n - 1, by omega⟩, ⟨n - 3, by omega⟩], ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_cons, List.length_nil] at hk
              match k with
              | 0 =>
                dsimp only [List.get]; simp only [DynkinType.adj]
                rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
        · -- j = n-2: path [n-1, n-3, n-2]
          refine ⟨[⟨n - 1, by omega⟩, ⟨n - 3, by omega⟩, ⟨n - 2, by omega⟩], ?_, ?_, ?_⟩
          · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
            exact Fin.ext (by dsimp; omega)
          · intro k hk
            simp only [List.length_cons, List.length_nil] at hk
            match k with
            | 0 =>
              dsimp only [List.get]; simp only [DynkinType.adj]
              rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
            | 1 =>
              dsimp only [List.get]; simp only [DynkinType.adj]
              rw [if_pos]; left; left; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
    · by_cases hj : j.val = n - 1
      · -- j = n-1, i on main path: route through n-3
        have hilt : i.val < n - 1 := by omega
        rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 by omega) with hilt2 | hin2
        · rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 3 by omega) with hilt3 | hin3
          · -- i < n-3: get main path from i to n-3, append n-1
            obtain ⟨path, hhead, hlast, hedges⟩ := main_asc i ⟨n - 3, by omega⟩
              hilt (show (n - 3 : ℕ) < n - 1 by omega)
              (show i.val ≤ n - 3 from Nat.le_of_lt hilt3)
            refine ⟨path ++ [⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
            · cases path with
              | nil => simp at hhead
              | cons p ps =>
                simp only [List.cons_append, List.head?_cons]
                exact hhead
            · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
              simp only [List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_append, List.length_cons, List.length_nil] at hk
              by_cases hk_main : k + 1 < path.length
              · simp only [List.get_eq_getElem]
                rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
                exact hedges k hk_main
              · -- Last edge: path[k] = n-3, (path++[n-1])[k+1] = n-1
                have hk_eq : k + 1 = path.length := by omega
                have hpne : path ≠ [] := by
                  cases path with | nil => simp at hhead | cons _ _ => exact List.cons_ne_nil _ _
                -- Extract what path[k] equals: it's the last element = n-3
                have hpath_last : path.getLast hpne = ⟨n - 3, by omega⟩ := by
                  have h := List.getLast?_eq_getLast_of_ne_nil hpne
                  rw [hlast] at h; exact Option.some.inj h.symm
                -- path[k] = path.getLast = n-3
                have hk_last : k = path.length - 1 := by omega
                have hpath_k : path[k]'(by omega) = ⟨n - 3, by omega⟩ := by
                  subst hk_last
                  rw [List.getLast_eq_getElem] at hpath_last; exact hpath_last
                -- (path++[n-1])[k+1] = n-1
                have hsucc : (path ++ [⟨n - 1, by omega⟩])[k + 1]'(by simp; omega) =
                    ⟨n - 1, by omega⟩ := by
                  rw [List.getElem_append_right (by omega)]
                  simp [hk_eq]
                simp only [List.get_eq_getElem]
                -- Now just compute the adjacency
                show (DynkinType.adj (.D n hn))
                  ((path ++ [⟨n - 1, by omega⟩])[k]'(by simp; omega))
                  ((path ++ [⟨n - 1, by omega⟩])[k + 1]'(by simp; omega)) = 1
                rw [List.getElem_append_left (by omega), hpath_k, hsucc]
                simp only [DynkinType.adj]
                rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
          · -- i = n-3: path [n-3, n-1]
            refine ⟨[⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_cons, List.length_nil] at hk
              match k with
              | 0 =>
                dsimp only [List.get]; simp only [DynkinType.adj]
                rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
        · -- i = n-2: path [n-2, n-3, n-1]
          refine ⟨[⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
          · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
            exact Fin.ext (by dsimp; omega)
          · intro k hk
            simp only [List.length_cons, List.length_nil] at hk
            match k with
            | 0 =>
              dsimp only [List.get]; simp only [DynkinType.adj]
              rw [if_pos]; left; right; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
            | 1 =>
              dsimp only [List.get]; simp only [DynkinType.adj]
              rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp <;> omega
      · -- Both on main path
        by_cases hij : i.val ≤ j.val
        · exact main_asc i j (by omega) (by omega) hij
        · exact main_desc i j (by omega) (by omega) (by omega)
  · -- Positive definiteness
    exact Dn_posDef n hn

/-- Explicit tree-paths for E₆: vertex `i` to vertex `j` through the unique tree path. -/
private def E6_treePath : Fin 6 → Fin 6 → List (Fin 6) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 5]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 5]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 5]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 2, 5]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 3, 2, 5]
  | 5, 0 => [5, 2, 1, 0] | 5, 1 => [5, 2, 1] | 5, 2 => [5, 2]
  | 5, 3 => [5, 2, 3] | 5, 4 => [5, 2, 3, 4] | 5, 5 => [5]

-- No separate path_valid lemma needed; we verify inline below.

/-- E₆ is a Dynkin diagram. -/
private lemma E6_isDynkin : IsDynkinDiagram 6 (DynkinType.adj .E6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry
    exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · -- Zero diagonal
    intro i; fin_cases i <;> native_decide
  · -- 0-1 entries
    intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity: provide explicit tree paths and verify
    intro i j
    refine ⟨E6_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E6_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | _))) <;>
        (first | omega | (dsimp only [E6_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky sum-of-squares decomposition.
    -- The LDLᵀ factorization of the Cartan matrix 2I - adj_E6 gives
    -- D = diag(2, 3/2, 4/3, 5/4, 6/5, 1/2), all positive.
    -- Clearing denominators: 60 · xᵀCx = 30(2x₀−x₁)² + 10(3x₁−2x₂)² +
    --   5(4x₂−3x₃−3x₅)² + 3(5x₃−4x₄−3x₅)² + 18(2x₄−x₅)² + 30x₅²
    intro x hx
    -- Abbreviate coordinates
    set a := x 0; set b := x 1; set c := x 2; set d := x 3; set e := x 4; set f := x 5
    -- It suffices to show 60 * q(x) > 0 (since 60 > 0)
    suffices h60 : 0 < 60 * dotProduct x
        ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - DynkinType.adj .E6).mulVec x) by linarith
    -- Step 1: Expand the quadratic form to a polynomial in a,b,c,d,e,f
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        DynkinType.adj .E6).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f := by
      -- First show the Cartan matrix equals a concrete matrix
      set C := 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - DynkinType.adj .E6
      have hC : C = !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
                        0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, vecHead]
      ring
    -- Step 2: Rewrite as SOS
    rw [expand]
    have sos : 60 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f) =
        30*(2*a-b)^2 + 10*(3*b-2*c)^2 + 5*(4*c-3*d-3*f)^2 +
        3*(5*d-4*e-3*f)^2 + 18*(2*e-f)^2 + 30*f^2 := by ring
    rw [sos]
    -- Step 3: SOS > 0 when x ≠ 0. Proof by contradiction.
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*f)
    have s4 := sq_nonneg (5*d-4*e-3*f)
    have s5 := sq_nonneg (2*e-f)
    have s6 := sq_nonneg f
    -- Back-substitute: from f upward, each variable must be 0
    have hf : f = 0 := by
      have : f ^ 2 ≤ 0 := by nlinarith
      have := le_antisymm this (sq_nonneg f)
      exact pow_eq_zero (show f ^ 2 = 0 from this)
    have he : e = 0 := by
      have : (2*e-f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*e-f)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*f)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*f)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Explicit tree-paths for E₇: path 0—1—2—3—4—5 with branch 2—6. -/
private def E7_treePath : Fin 7 → Fin 7 → List (Fin 7) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 6]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 6]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 6]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 2, 6]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 3, 2, 6]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 4, 3, 2, 6]
  | 6, 0 => [6, 2, 1, 0] | 6, 1 => [6, 2, 1] | 6, 2 => [6, 2]
  | 6, 3 => [6, 2, 3] | 6, 4 => [6, 2, 3, 4] | 6, 5 => [6, 2, 3, 4, 5]
  | 6, 6 => [6]

set_option maxHeartbeats 400000 in
/-- E₇ is a Dynkin diagram. -/
private lemma E7_isDynkin : IsDynkinDiagram 7 (DynkinType.adj .E7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · intro i; fin_cases i <;> native_decide
  · intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity
    intro i j
    refine ⟨E7_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E7_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | _)))) <;>
        (first | omega | (dsimp only [E7_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky SOS decomposition
    -- 420·q = 210(2a-b)² + 70(3b-2c)² + 35(4c-3d-3g)² + 21(5d-4e-3g)² +
    --         14(6e-5f-3g)² + 10(7f-3g)² + 120g²
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6
    suffices h420 : 0 < 420 * dotProduct x
        ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - DynkinType.adj .E7).mulVec x) by linarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        DynkinType.adj .E7).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g := by
      set C := 2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - DynkinType.adj .E7
      have hC : C = !![2,-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1;
                        0,0,-1,2,-1,0,0; 0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0;
                        0,0,-1,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [expand]
    have sos : 420 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g) =
        210*(2*a-b)^2 + 70*(3*b-2*c)^2 + 35*(4*c-3*d-3*g)^2 + 21*(5*d-4*e-3*g)^2 +
        14*(6*e-5*f-3*g)^2 + 10*(7*f-3*g)^2 + 120*g^2 := by ring
    rw [sos]
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*g)
    have s4 := sq_nonneg (5*d-4*e-3*g)
    have s5 := sq_nonneg (6*e-5*f-3*g)
    have s6 := sq_nonneg (7*f-3*g)
    have s7 := sq_nonneg g
    have hg : g = 0 := by
      have : g ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg g))
    have hf : f = 0 := by
      have : (7*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-3*g)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*g)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*g)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*g)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Explicit tree-paths for E₈: path 0—1—2—3—4—5—6 with branch 2—7. -/
private def E8_treePath : Fin 8 → Fin 8 → List (Fin 8) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 3, 4, 5, 6] | 0, 7 => [0, 1, 2, 7]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 3, 4, 5, 6] | 1, 7 => [1, 2, 7]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 3, 4, 5, 6] | 2, 7 => [2, 7]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 4, 5, 6] | 3, 7 => [3, 2, 7]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 5, 6] | 4, 7 => [4, 3, 2, 7]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 6] | 5, 7 => [5, 4, 3, 2, 7]
  | 6, 0 => [6, 5, 4, 3, 2, 1, 0] | 6, 1 => [6, 5, 4, 3, 2, 1] | 6, 2 => [6, 5, 4, 3, 2]
  | 6, 3 => [6, 5, 4, 3] | 6, 4 => [6, 5, 4] | 6, 5 => [6, 5]
  | 6, 6 => [6] | 6, 7 => [6, 5, 4, 3, 2, 7]
  | 7, 0 => [7, 2, 1, 0] | 7, 1 => [7, 2, 1] | 7, 2 => [7, 2]
  | 7, 3 => [7, 2, 3] | 7, 4 => [7, 2, 3, 4] | 7, 5 => [7, 2, 3, 4, 5]
  | 7, 6 => [7, 2, 3, 4, 5, 6] | 7, 7 => [7]

set_option maxHeartbeats 400000 in
/-- E₈ is a Dynkin diagram. -/
private lemma E8_isDynkin : IsDynkinDiagram 8 (DynkinType.adj .E8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> native_decide)
  · intro i; fin_cases i <;> native_decide
  · intro i j; fin_cases i <;> fin_cases j <;> native_decide
  · -- Connectivity
    intro i j
    refine ⟨E8_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E8_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | (_ | _))))) <;>
        (first | omega | (dsimp only [E8_treePath, List.get]; native_decide))
  · -- Positive definiteness via Cholesky SOS decomposition
    -- 840·q = 420(2a-b)² + 140(3b-2c)² + 70(4c-3d-3h)² + 42(5d-4e-3h)² +
    --         28(6e-5f-3h)² + 20(7f-6g-3h)² + 15(8g-3h)² + 105h²
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6; set h := x 7
    suffices h840 : 0 < 840 * dotProduct x
        ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - DynkinType.adj .E8).mulVec x) by linarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        DynkinType.adj .E8).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h := by
      set C := 2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - DynkinType.adj .E8
      have hC : C = !![2,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1;
                        0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
                        0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> native_decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [expand]
    have sos : 840 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h) =
        420*(2*a-b)^2 + 140*(3*b-2*c)^2 + 70*(4*c-3*d-3*h)^2 + 42*(5*d-4*e-3*h)^2 +
        28*(6*e-5*f-3*h)^2 + 20*(7*f-6*g-3*h)^2 + 15*(8*g-3*h)^2 + 105*h^2 := by ring
    rw [sos]
    by_contra h_le
    push_neg at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*h)
    have s4 := sq_nonneg (5*d-4*e-3*h)
    have s5 := sq_nonneg (6*e-5*f-3*h)
    have s6 := sq_nonneg (7*f-6*g-3*h)
    have s7 := sq_nonneg (8*g-3*h)
    have s8 := sq_nonneg h
    have hh : h = 0 := by
      have : h ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg h))
    have hg : g = 0 := by
      have : (8*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (8*g-3*h)))
      omega
    have hf : f = 0 := by
      have : (7*f-6*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-6*g-3*h)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*h)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*h)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*h)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)

/-- Each standard Dynkin type gives a Dynkin diagram. -/
lemma isDynkinDiagram_of_type (t : DynkinType) :
    IsDynkinDiagram t.rank t.adj := by
  cases t with
  | A n hn => exact An_isDynkin n hn
  | D n hn => exact Dn_isDynkin n hn
  | E6 => exact E6_isDynkin
  | E7 => exact E7_isDynkin
  | E8 => exact E8_isDynkin


end Etingof
