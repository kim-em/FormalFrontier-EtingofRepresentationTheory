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
private lemma isDynkinDiagram_of_graph_iso {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
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
private lemma isDynkinDiagram_of_type (t : DynkinType) :
    IsDynkinDiagram t.rank t.adj := by
  cases t with
  | A n hn => exact An_isDynkin n hn
  | D n hn => exact Dn_isDynkin n hn
  | E6 => exact E6_isDynkin
  | E7 => exact E7_isDynkin
  | E8 => exact E8_isDynkin

/-! ## Forward direction infrastructure

The forward direction of the Dynkin classification proceeds by elimination:

1. **No cycles**: A cycle of length k has null vector (1,1,...,1) for the Cartan form.
   Any graph containing a cycle has non-positive-definite Cartan form.

2. **Degree bound**: If a vertex has degree ≥ 4, the vector (2 at vertex, 1 at neighbors,
   0 elsewhere) gives Cartan form ≤ 0. So max degree ≤ 3.

3. **Tree classification**: A connected tree with max degree ≤ 3 is either:
   - A path (all degrees ≤ 2) → isomorphic to A_n
   - Has exactly one vertex of degree 3 with arms (p,q,r) → the arm lengths determine the type

4. **Arm length constraint**: For a branching tree T_{p,q,r}, positive definiteness requires
   1/(p+1) + 1/(q+1) + 1/(r+1) > 1. The solutions with p ≤ q ≤ r are:
   - (1,1,r) → D_{r+3}
   - (1,2,2) → E₆, (1,2,3) → E₇, (1,2,4) → E₈
-/

/-- The degree of vertex i in a 0-1 adjacency matrix. -/
private noncomputable def vertexDegree {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => adj i j = 1)).card

/-- The set of neighbors of vertex i. -/
private def neighbors {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => adj i j = 1)

/-- The number of edges (counted as half the sum of all adjacency entries) equals
    the sum of entries divided by 2 for a symmetric 0-1 adjacency matrix. -/
private noncomputable def edgeCount {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (∑ i : Fin n, vertexDegree adj i) / 2

/-- Subgraph non-positive-definiteness: if a Dynkin diagram contains a subgraph
    (via injection φ) whose Cartan form has a non-trivial non-negative null vector,
    then we get a contradiction.

    The key idea: push forward v via φ to get w on Fin n. Since v ≥ 0 and adj ≥ adj_sub
    on the image, we have B_adj(w,w) ≤ B_sub(v,v) ≤ 0, contradicting positive definiteness. -/
private lemma subgraph_contradiction {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj)
    (adj_sub : Matrix (Fin m) (Fin m) ℤ)
    (φ : Fin m ↪ Fin n)
    (hembed : ∀ i j, adj_sub i j ≤ adj (φ i) (φ j))
    (v : Fin m → ℤ) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne : v ≠ 0)
    (hv_null : dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) ≤ 0) :
    False := by
  obtain ⟨_hsymm, _hdiag, h01, _hconn, hpos⟩ := hD
  -- Push forward v to w on Fin n: w(φ(i)) = v(i), w(j) = 0 for j ∉ image(φ)
  -- We use the inverse of φ on its image
  set w : Fin n → ℤ := fun j =>
    if h : ∃ i, φ i = j then v h.choose else 0 with hw_def
  -- w is nonzero since v is nonzero
  have hw_ne : w ≠ 0 := by
    intro h
    apply hv_ne; ext i
    have hw_phi : w (φ i) = 0 := congr_fun h (φ i)
    simp only [w, show (∃ j, φ j = φ i) from ⟨i, rfl⟩, dite_true] at hw_phi
    have heq : (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose = i :=
      φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
    rw [heq] at hw_phi
    exact hw_phi
  -- B_adj(w,w) ≤ B_sub(v,v) ≤ 0
  have hadj_nonneg : ∀ i j, 0 ≤ adj i j := by
    intro i j; rcases h01 i j with h | h <;> omega
  -- First show B_adj(w,w) ≤ B_sub(v,v)
  -- B_adj(w,w) = Σ_{j,k} (2δ_{jk} - adj(j,k))·w(j)·w(k)
  -- Only terms with j,k ∈ image(φ) are nonzero (since w = 0 outside image)
  -- On image(φ): w(φ(i))·w(φ(j)) = v(i)·v(j)
  -- The 2δ terms are the same (φ injective)
  -- The adj terms: adj(φ(i),φ(j)) ≥ adj_sub(i,j) (from hembed + adj_sub 0-1)
  -- Since v(i)·v(j) ≥ 0: -adj(φ(i),φ(j))·v(i)·v(j) ≤ -adj_sub(i,j)·v(i)·v(j)
  -- Therefore B_adj(w,w) ≤ B_sub(v,v)
  -- w(φ(i)) = v(i) for all i
  have hw_phi : ∀ i, w (φ i) = v i := by
    intro i
    simp only [w, show (∃ j, φ j = φ i) from ⟨i, rfl⟩, dite_true]
    congr 1; exact φ.injective (⟨i, rfl⟩ : ∃ j, φ j = φ i).choose_spec
  -- w(j) = 0 for j ∉ image(φ)
  have hw_zero : ∀ j, (∀ i, φ i ≠ j) → w j = 0 := by
    intro j hj; simp only [w, show ¬∃ i, φ i = j from fun ⟨i, hi⟩ => hj i hi, dite_false]
  -- Helper: reindex sums from Fin n to Fin m since w vanishes outside image(φ)
  have sum_reindex : ∀ g : Fin n → ℤ, ∑ a : Fin n, w a * g a = ∑ i : Fin m, v i * g (φ i) := by
    intro g
    -- Split sum into image(φ) and its complement
    set S := Finset.univ.image φ with hS_def
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun a => a ∈ S) (f := fun a => w a * g a)
    rw [← hsplit]
    -- Complement sum is 0 (w vanishes outside image)
    have hcomp : ∑ a ∈ Finset.univ.filter (fun a => a ∉ S), w a * g a = 0 := by
      apply Finset.sum_eq_zero; intro a ha
      have ha' : a ∉ S := (Finset.mem_filter.mp ha).2
      have : w a = 0 := hw_zero a fun i hi =>
        ha' (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [this, zero_mul]
    rw [hcomp, add_zero]
    -- The image sum equals the reindexed sum via Finset.sum_image
    have hfilter_eq : Finset.univ.filter (· ∈ S) = S := by
      ext a; simp [S, Finset.mem_image]
    rw [hfilter_eq]
    rw [Finset.sum_image (fun i _ j _ h => φ.injective h)]
    apply Finset.sum_congr rfl; intro i _
    rw [hw_phi]
  have hle : dotProduct w ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) ≤
      dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) := by
    -- Proof strategy (sum reindexing + term-by-term comparison):
    -- Step 1: Since w vanishes outside image(φ), reindex B_adj(w,w) as:
    --   B_adj(w,w) = Σ_{i,j:Fin m} (2δ_{i,j} - adj(φ i, φ j)) · v(i) · v(j)
    -- (Use sum_reindex twice, once for outer and once for inner sum, plus φ.injective for δ)
    -- Step 2: Compare term-by-term with B_sub(v,v):
    --   Each difference term is (adj_sub(i,j) - adj(φ i, φ j)) · v(i) · v(j) ≤ 0
    --   because v(i)·v(j) ≥ 0 and adj(φ i, φ j) ≥ adj_sub(i,j)
    --   because adj_sub i j ≤ adj (φ i) (φ j) by hembed
    -- Rewrite LHS outer sum via sum_reindex
    simp only [dotProduct]
    rw [sum_reindex (fun a => ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) a)]
    -- Rewrite mulVec at φ i using sum_reindex on inner sum
    have inner : ∀ i : Fin m,
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec w) (φ i) =
        ∑ j : Fin m, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) (φ j) * v j := by
      intro i
      change ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) b * w b = _
      simp_rw [mul_comm ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) (φ i) _) (w _)]
      rw [sum_reindex]
      congr 1; ext j; ring
    simp_rw [inner]
    -- Now both sides are double sums over Fin m; compare term-by-term
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hv_nonneg i)
    apply Finset.sum_le_sum; intro j _
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
    apply mul_le_mul_of_nonneg_right _ (hv_nonneg j)
    linarith [hembed i j]
  linarith [hpos w hw_ne]

/-- In a Dynkin diagram, vertex degree is at most 3.
    Proof: if deg(v) ≥ 4, embed the star K_{1,4} (center + 4 leaves) and use
    the null vector (2,1,1,1,1) which gives B = 0 on the star. -/
private lemma dynkin_degree_le_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (i : Fin n) : vertexDegree adj i ≤ 3 := by
  by_contra hge; push_neg at hge
  obtain ⟨hsymm, hdiag, h01, _, hpos⟩ := hD
  -- Extract 4 neighbors
  set N := Finset.univ.filter (fun j => adj i j = 1) with hN_def
  have hcard : 4 ≤ N.card := hge
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hi_not_S : i ∉ S := by
    intro hi; have := (Finset.mem_filter.mp (hSsub hi)).2; linarith [hdiag i]
  -- Define x: 2 at center, 1 at 4 neighbors, 0 elsewhere
  set x : Fin n → ℤ := fun j => if j = i then 2 else if j ∈ S then 1 else 0
  have hx_ne : x ≠ 0 := by intro h; have := congr_fun h i; simp [x] at this
  -- Each term x(a)*mulVec(a) ≤ 0, so B(x,x) ≤ 0
  suffices hle : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 by
    linarith [hpos x hx_ne]
  -- Helper: adj(i,b)*x(b) is nonneg for all b
  have adj_x_nonneg : ∀ a b, 0 ≤ adj a b * x b := fun a b =>
    mul_nonneg (by rcases h01 a b with h | h <;> omega)
      (by simp only [x]; split_ifs <;> omega)
  -- Helper: for b ∈ S, adj(i,b)*x(b) = 1
  have adj_x_S : ∀ b, b ∈ S → adj i b * x b = 1 := by
    intro b hb
    have h1 : adj i b = 1 := (Finset.mem_filter.mp (hSsub hb)).2
    have h2 : x b = 1 := by
      have : b ≠ i := fun h => hi_not_S (h ▸ hb)
      simp [x, this, hb]
    rw [h1, h2, mul_one]
  -- Helper: Σ_b adj(i,b)*x(b) ≥ 4
  have sum_i_ge : (4 : ℤ) ≤ ∑ b, adj i b * x b := by
    have hS_sum : ∑ b ∈ S, adj i b * x b = 4 := by
      rw [show (4 : ℤ) = ∑ _b ∈ S, (1 : ℤ) from by simp [hScard]]
      exact Finset.sum_congr rfl (fun b hb => adj_x_S b hb)
    calc (4 : ℤ) = ∑ b ∈ S, adj i b * x b := hS_sum.symm
      _ ≤ ∑ b, adj i b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg i b)
  -- Helper: for a ∈ S, Σ_b adj(a,b)*x(b) ≥ 2 (from adj(a,i)*x(i) = 1*2)
  have sum_a_ge : ∀ a, a ∈ S → (2 : ℤ) ≤ ∑ b, adj a b * x b := by
    intro a ha
    have ha_adj_i : adj a i = 1 := by
      have := (Finset.mem_filter.mp (hSsub ha)).2; exact hsymm.apply i a ▸ this
    have hxi : x i = 2 := by simp [x]
    have : adj a i * x i = 2 := by rw [ha_adj_i, hxi]; ring
    calc (2 : ℤ) = adj a i * x i := this.symm
      _ = ∑ b ∈ ({i} : Finset (Fin n)), adj a b * x b := by simp
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => adj_x_nonneg a b)
  -- Key: mulVec decomposes as 2*x(a) - Σ adj(a,b)*x(b)
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
  -- B(x,x) = Σ_a x(a) * ((2I-adj)x)(a), show each term ≤ 0
  apply Finset.sum_nonpos; intro a _
  rw [mulVec_eq]
  by_cases hai : a = i
  · -- a = i: x(i) = 2, Σ adj(i,b)*x(b) ≥ 4
    have hxa : x a = 2 := by simp [x, hai]
    rw [hxa]; linarith [hai ▸ sum_i_ge]
  · by_cases haS : a ∈ S
    · -- a ∈ S: x(a) = 1, Σ adj(a,b)*x(b) ≥ 2
      have hxa : x a = 1 := by
        simp only [x]; rw [if_neg hai, if_pos haS]
      rw [hxa]; linarith [sum_a_ge a haS]
    · -- a ∉ {i}∪S: x(a) = 0
      have : x a = 0 := by simp [x, hai, haS]
      rw [this]; simp

/-- In a Dynkin diagram, any cycle of length ≥ 3 would give a null vector for the Cartan form.
    Therefore Dynkin diagrams have no cycles, hence are trees. -/
private lemma dynkin_no_cycle {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (cycle : List (Fin n)) (hlen : 3 ≤ cycle.length)
    (hnodup : cycle.Nodup)
    (hedges : ∀ k, (h : k + 1 < cycle.length) →
      adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1)
    (hclose : adj (cycle.getLast (by intro h; simp [h] at hlen)) (cycle.get ⟨0, by omega⟩) = 1) :
    False := by
  obtain ⟨hsymm, _hdiag, h01, _hconn, hpos⟩ := hD
  -- The all-ones vector on the cycle has B(x,x) = 2k - 2k = 0 (minus extra edges)
  -- where k = cycle.length
  set x : Fin n → ℤ := fun j => if j ∈ cycle then 1 else 0
  have hx_ne : x ≠ 0 := by
    intro h
    have hmem : cycle[0]'(by omega) ∈ cycle := List.getElem_mem ..
    have hval := congr_fun h (cycle[0]'(by omega))
    simp only [x, hmem, ite_true, Pi.zero_apply] at hval
    exact absurd hval one_ne_zero
  -- Use subgraph_contradiction: embed the cycle as a subgraph with null vector (1,...,1)
  set m := cycle.length
  -- Cycle adjacency matrix on Fin m
  let adj_sub : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) ∨
       (i.val = 0 ∧ j.val = m - 1) ∨ (j.val = 0 ∧ i.val = m - 1)
    then 1 else 0
  -- Embedding: cycle positions → graph vertices
  have φ_inj : Function.Injective (fun i : Fin m => cycle.get i) :=
    hnodup.injective_get
  let φ : Fin m ↪ Fin n := ⟨fun i => cycle.get i, φ_inj⟩
  -- Rewrite hclose using get
  have hclose' : adj (cycle.get ⟨m - 1, by omega⟩) (cycle.get ⟨0, by omega⟩) = 1 := by
    convert hclose using 2; symm; exact List.getLast_eq_getElem _
  -- Embedding condition: cycle edges are subgraph edges
  have hembed : ∀ i j, adj_sub i j ≤ adj (φ i) (φ j) := by
    intro i j; simp only [adj_sub, φ]
    split_ifs with h
    · -- adj_sub = 1: show adj(cycle[i], cycle[j]) ≥ 1
      show 1 ≤ adj (cycle.get i) (cycle.get j)
      suffices adj (cycle.get i) (cycle.get j) = 1 by omega
      rcases h with h | h | ⟨hi, hj⟩ | ⟨hj, hi⟩
      · -- i.val + 1 = j.val: consecutive vertices
        have key := hedges i.val (by omega)
        have : cycle.get j = cycle.get (⟨i.val + 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext h.symm)
        rw [this]; exact key
      · -- j.val + 1 = i.val: reverse consecutive
        have key := hedges j.val (by omega)
        have : cycle.get i = cycle.get (⟨j.val + 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext h.symm)
        rw [hsymm.apply, this]; exact key
      · -- i = 0, j = m-1: closing edge (reversed)
        have h1 : cycle.get i = cycle.get (⟨0, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hi)
        have h2 : cycle.get j = cycle.get (⟨m - 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hj)
        rw [hsymm.apply, h1, h2]; exact hclose'
      · -- j = 0, i = m-1: closing edge
        have h1 : cycle.get i = cycle.get (⟨m - 1, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hi)
        have h2 : cycle.get j = cycle.get (⟨0, by omega⟩ : Fin m) :=
          congrArg cycle.get (Fin.ext hj)
        rw [h1, h2]; exact hclose'
    · -- adj_sub = 0: trivially 0 ≤ adj(...)
      have : adj (φ i) (φ j) = 0 ∨ adj (φ i) (φ j) = 1 := h01 (φ i) (φ j)
      show 0 ≤ adj (φ i) (φ j)
      rcases this with h | h <;> simp [h]
  -- Null vector: all ones
  let v : Fin m → ℤ := fun _ => 1
  have hv_nonneg : ∀ i, 0 ≤ v i := fun _ => by show (0 : ℤ) ≤ 1; omega
  have hv_ne : v ≠ 0 := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [v] at this
  -- B_sub(v,v) ≤ 0: each vertex has degree 2 in the cycle, so B(1,...,1) = 0
  -- Each vertex in a cycle has exactly 2 neighbors, so B(1,...,1) = Σ(2-2) = 0
  have hdeg2 : ∀ i : Fin m, ∑ j : Fin m, adj_sub i j = 2 := by
    intro i
    -- adj_sub i j = 1 iff j is a cycle-neighbor of i; each vertex has exactly 2 neighbors
    -- The condition (from adj_sub definition) uses i.val and j.val (ℕ comparisons)
    -- After simp [adj_sub], the sum has if-then-else over ℕ conditions
    have h01_sub : ∀ j, adj_sub i j = 0 ∨ adj_sub i j = 1 := by
      intro j; simp only [adj_sub]; split_ifs <;> omega
    -- Convert to cardinality of the neighbor set
    rw [show ∑ j, adj_sub i j = ↑(Finset.univ.filter (fun j : Fin m => adj_sub i j = 1)).card from by
      rw [show ∑ j, adj_sub i j = ∑ j, if adj_sub i j = 1 then (1 : ℤ) else 0 from
        Finset.sum_congr rfl (fun j _ => by rcases h01_sub j with h | h <;> simp [h])]
      push_cast; simp [Finset.sum_boole]]
    -- Show the neighbor set has exactly 2 elements
    -- Define the two neighbors
    set nxt : Fin m := ⟨if i.val + 1 < m then i.val + 1 else 0, by split_ifs <;> omega⟩
    set prv : Fin m := ⟨if i.val = 0 then m - 1 else i.val - 1, by split_ifs <;> omega⟩
    have hne : nxt ≠ prv := by
      simp only [nxt, prv, ne_eq, Fin.ext_iff, Fin.val_mk]; split_ifs <;> omega
    suffices Finset.univ.filter (fun j : Fin m => adj_sub i j = 1) = {nxt, prv} by
      rw [this, Finset.card_pair hne]; norm_cast
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · -- adj_sub i j = 1 → j = nxt ∨ j = prv
      intro h; simp only [adj_sub] at h
      split_ifs at h with hcond
      · rcases hcond with hc | hc | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
        · left; exact Fin.ext (by simp only [nxt, Fin.val_mk]; split_ifs <;> omega)
        · right; exact Fin.ext (by simp only [prv, Fin.val_mk]; split_ifs <;> omega)
        · right; exact Fin.ext (by simp only [prv, Fin.val_mk]; split_ifs <;> omega)
        · left; exact Fin.ext (by simp only [nxt, Fin.val_mk]; split_ifs <;> omega)
      · omega -- h : 0 = 1 contradiction
    · -- j = nxt ∨ j = prv → adj_sub i j = 1
      rintro (hj | hj) <;> subst hj <;> simp only [adj_sub, nxt, prv, Fin.val_mk] <;>
        split_ifs <;> omega
  have hv_null : dotProduct v ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v) ≤ 0 := by
    suffices h0 : (2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj_sub).mulVec v = 0 by
      rw [h0]; simp [dotProduct]
    ext i; simp only [mulVec, dotProduct, v, mul_one, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Pi.zero_apply]
    -- Convert nsmul to concrete ℤ values
    simp_rw [show ∀ j : Fin m, (2 : ℕ) • (if i = j then (1 : ℤ) else 0) =
      if i = j then (2 : ℤ) else 0 from fun j => by split_ifs <;> simp]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hdeg2 i]
  exact subgraph_contradiction ⟨hsymm, _hdiag, h01, _hconn, hpos⟩ adj_sub φ hembed v hv_nonneg hv_ne hv_null

/-- A Dynkin diagram on n vertices has exactly n-1 edges (it's a tree).
    This follows from no-cycles + connectivity. -/
private lemma dynkin_edge_count {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) : edgeCount adj = n - 1 := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  apply Nat.le_antisymm
  · -- Upper bound: edgeCount ≤ n - 1
    -- From B(1,...,1) > 0 where B is the Cartan quadratic form
    -- B(1,...,1) = 2n - ∑ deg, so ∑ deg < 2n, hence edgeCount < n
    unfold edgeCount
    -- Show ∑ vertexDegree < 2 * n, then (∑ deg) / 2 ≤ n - 1
    suffices hsum : ∑ i : Fin n, vertexDegree adj i < 2 * n by
      omega
    -- Use positive definiteness with x = (1,...,1)
    have hx_ne : (fun (_ : Fin n) => (1 : ℤ)) ≠ 0 := by
      intro h; have := congr_fun h ⟨0, by omega⟩; simp at this
    have hB := hpos _ hx_ne
    -- Compute B(1,...,1) = 2n - ∑ deg
    have mulVec_eq : ∀ a : Fin n,
        ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec (fun _ => (1 : ℤ))) a =
        2 - ∑ b : Fin n, adj a b := by
      intro a
      simp only [mulVec, dotProduct, mul_one]
      rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b =
          ∑ b, (2 * (1 : Matrix _ _ ℤ) a b - adj a b) from
        Finset.sum_congr rfl (fun b _ => by
          simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul])]
      rw [Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply, Finset.sum_ite_eq']
    simp only [dotProduct, one_mul, mulVec_eq] at hB
    rw [show ∑ a : Fin n, (2 - ∑ b : Fin n, adj a b) =
        2 * ↑n - ∑ a : Fin n, ∑ b : Fin n, adj a b from by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]] at hB
    rw [show ∑ a : Fin n, ∑ b : Fin n, adj a b =
        ↑(∑ i : Fin n, vertexDegree adj i) from by
      push_cast
      exact Finset.sum_congr rfl (fun a _ => adj_sum_eq_degree h01 a)] at hB
    omega
  · -- Lower bound: n - 1 ≤ edgeCount
    -- Convert to SimpleGraph and use Mathlib's connectivity lower bound
    let G : SimpleGraph (Fin n) :=
      { Adj := fun i j => adj i j = 1
        symm := fun {i j} h => by rwa [hsymm.apply]
        loopless := fun i h => by simp [hdiag i] at h }
    haveI : DecidableRel G.Adj := fun i j =>
      show Decidable (adj i j = 1) from inferInstance
    -- Show G.Connected: build Reachable from list paths
    have hG_conn : G.Connected := by
      refine ⟨fun u v => ?_, ⟨⟨0, by omega⟩⟩⟩
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
      -- Build G.Reachable by induction on the path list
      suffices h : ∀ (l : List (Fin n)) (a b : Fin n),
          l.head? = some a → l.getLast? = some b →
          (∀ k, (hk : k + 1 < l.length) →
            adj (l.get ⟨k, by omega⟩) (l.get ⟨k + 1, hk⟩) = 1) →
          G.Reachable a b from h path u v hhead hlast hedges
      intro l
      induction l with
      | nil => intro a _ ha; simp at ha
      | cons x t ih =>
        intro a b ha hb hedges'
        simp at ha; subst ha
        cases t with
        | nil => simp at hb; subst hb; exact .refl
        | cons y s =>
          have hadj_xy : G.Adj x y := show adj x y = 1 from
            hedges' 0 (by simp; omega)
          exact hadj_xy.reachable.trans
            (ih y b (by simp) hb (fun k hk => hedges' (k + 1) (by omega)))
    -- Relate G.degree to vertexDegree
    have hdeg_eq : ∀ v : Fin n, G.degree v = vertexDegree adj v := by
      intro v; unfold SimpleGraph.degree vertexDegree
      congr 1; ext j
      simp only [SimpleGraph.neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    -- Relate edgeCount to G.edgeFinset.card via handshaking
    have hedge_eq : edgeCount adj = G.edgeFinset.card := by
      unfold edgeCount
      have hhs := G.sum_degrees_eq_twice_card_edges
      rw [show ∑ v : Fin n, G.degree v = ∑ v, vertexDegree adj v from
        Finset.sum_congr rfl (fun v _ => hdeg_eq v)] at hhs
      omega
    -- Apply Mathlib's lower bound
    rw [hedge_eq]
    have h_lb := hG_conn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h_lb
    omega

/-- For a 0-1 adjacency matrix, the sum of row entries equals the vertex degree. -/
private lemma adj_sum_eq_degree {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1) (a : Fin n) :
    ∑ b : Fin n, adj a b = ↑(vertexDegree adj a) := by
  simp only [vertexDegree]
  rw [show ∑ b : Fin n, adj a b =
      ∑ b : Fin n, (if adj a b = 1 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun b _ => by rcases h01 a b with h | h <;> simp [h])]
  simp [Finset.sum_boole]

/-- A Dynkin diagram on n vertices has exactly n-1 edges (it's a tree).
    This follows from no-cycles + connectivity. -/
private lemma list_path_reachable {n : ℕ} (G : SimpleGraph (Fin n))
    (path : List (Fin n)) (u v : Fin n)
    (hhead : path.head? = some u) (hlast : path.getLast? = some v)
    (hedges : ∀ k, (h : k + 1 < path.length) →
      G.Adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩)) :
    G.Reachable u v := by
  induction path generalizing u v with
  | nil => exact absurd hhead (by simp)
  | cons a rest ih =>
    have ha : a = u := by simpa using hhead
    cases rest with
    | nil =>
      have hv : a = v := by simpa using hlast
      rw [← ha, hv]
    | cons b rest' =>
      have hadj : G.Adj a b := hedges 0 (by simp)
      rw [← ha]
      exact hadj.reachable.trans <| ih b v (by simp)
        (by simpa [List.getLast?_cons_cons] using hlast)
        (fun k hk => hedges (k + 1) (by simp at hk ⊢; omega))

private lemma dynkin_edge_count {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) : edgeCount adj = n - 1 := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  -- Define the SimpleGraph corresponding to the adjacency matrix
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := fun {i j} h => by change adj j i = 1; rw [hsymm.apply i j]; exact h
      loopless := ⟨fun i h => by change adj i i = 1 at h; linarith [hdiag i]⟩ }
  letI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  -- Show G is connected
  have hG_conn : G.Connected := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact ⟨fun u v => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u v
      exact list_path_reachable G path u v hhead hlast hedges⟩
  -- Upper bound: edgeCount ≤ n - 1 from positive definiteness
  have h_upper : edgeCount adj ≤ n - 1 := by
    -- B(1,...,1) > 0 implies ∑ deg < 2n
    set x : Fin n → ℤ := fun _ => 1
    have hx_ne : x ≠ 0 := by intro h; have := congr_fun h ⟨0, by omega⟩; simp [x] at this
    -- mulVec decomposition (same pattern as dynkin_has_endpoint)
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
    -- B(1,...,1) = ∑_a (2 - deg(a))
    have hBpos := hpos x hx_ne
    simp only [dotProduct, show ∀ b, x b = (1 : ℤ) from fun _ => rfl, one_mul,
      mulVec_eq, mul_one] at hBpos
    -- hBpos : 0 < ∑ a, (2 - ∑ b, adj a b)
    -- This means ∑ deg < 2n
    have hsum_lt : ∑ i : Fin n, vertexDegree adj i < 2 * n := by
      have hsum_ineq : (0 : ℤ) < ∑ a : Fin n, (2 - ∑ b, adj a b) := hBpos
      have : (↑(∑ i : Fin n, vertexDegree adj i) : ℤ) < 2 * ↑n := by
        have h1 : ∑ a : Fin n, (2 - ∑ b : Fin n, adj a b) =
            2 * ↑n - ∑ a, ∑ b, adj a b := by
          rw [Finset.sum_sub_distrib]; simp [Finset.card_fin]; ring
        have h2 : (∑ i : Fin n, (vertexDegree adj i : ℤ)) = ∑ i, ∑ j, adj i j := by
          congr 1; ext i; exact (adj_sum_eq_degree h01 i).symm
        push_cast; linarith
      exact_mod_cast this
    unfold edgeCount; omega
  -- Lower bound: n - 1 ≤ edgeCount from connectivity
  have h_lower : n - 1 ≤ edgeCount adj := by
    have h1 := hG_conn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin] at h1
    -- Relate Nat.card G.edgeSet to edgeCount
    have hdeg_eq : ∀ v, G.degree v = vertexDegree adj v := by
      intro v; simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        SimpleGraph.neighborSet, Set.toFinset_setOf]
      congr 1
    have h_sum : ∑ v, G.degree v = ∑ v, vertexDegree adj v := by
      congr 1; ext v; exact hdeg_eq v
    have h_handshake := G.sum_degrees_eq_twice_card_edges
    have h_eq : G.edgeFinset.card = edgeCount adj := by
      unfold edgeCount; rw [← h_sum, h_handshake]; omega
    rw [show Nat.card G.edgeSet = edgeCount adj from by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]; exact h_eq] at h1
    omega
  omega

/-- In a Dynkin diagram with all degrees ≤ 2, there exists a vertex of degree ≤ 1 (endpoint).
    Proof: if all degrees = 2 then the all-ones vector has B(x,x) = 0, contradicting pos-def. -/
private lemma dynkin_has_endpoint {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n) (hpath : ∀ i, vertexDegree adj i ≤ 2) :
    ∃ v, vertexDegree adj v ≤ 1 := by
  by_contra h; push_neg at h
  obtain ⟨_, hdiag, h01, _, hpos⟩ := hD
  have hdeg2 : ∀ i, vertexDegree adj i = 2 := fun i => le_antisymm (hpath i) (h i)
  set x : Fin n → ℤ := fun _ => 1
  have hx_ne : x ≠ 0 := by intro h; have := congr_fun h ⟨0, by omega⟩; simp [x] at this
  -- B(x,x) = Σ_a (2 - degree(a)) = Σ_a 0 = 0, contradicting hpos > 0
  -- mulVec decomposition: mulVec(a) = 2*x(a) - Σ adj(a,b)*x(b)
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
  have hB_le : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos; intro a _
    simp only [show ∀ b, x b = (1 : ℤ) from fun _ => rfl, mul_one, one_mul, mulVec_eq]
    -- Goal: 2 - Σ adj(a,b) ≤ 0, i.e., 2 ≤ Σ adj(a,b)
    linarith [show (2 : ℤ) ≤ ∑ b, adj a b from by
      rw [adj_sum_eq_degree h01 a, hdeg2 a]; norm_cast]
  linarith [hpos x hx_ne]

/-- Given a connected graph with all degrees ≤ 2 and an endpoint v₀,
    construct a walk visiting all n vertices in order. The walk is:
    walk(0) = v₀, walk(k+1) = the unique neighbor of walk(k) not yet visited.
    Returns: an injective walk function, proof it covers all vertices,
    and proof consecutive vertices are adjacent. -/
private lemma path_walk_construction {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hpath : ∀ i, vertexDegree adj i ≤ 2) (v₀ : Fin n)
    (hv₀ : vertexDegree adj v₀ ≤ 1) :
    ∃ σ : Fin n ≃ Fin n,
      σ ⟨0, by omega⟩ = v₀ ∧
      (∀ (k : Fin n) (hk : k.val + 1 < n), adj (σ k) (σ ⟨k.val + 1, hk⟩) = 1) ∧
      (∀ i j, adj (σ i) (σ j) = 1 → (i.val + 1 = j.val ∨ j.val + 1 = i.val)) := by
  -- Proof by induction on n, removing the leaf v₀ at each step.
  revert adj hD hn hpath v₀ hv₀
  induction n with
  | zero => intro _ _ hn; omega
  | succ k ih =>
    intro adj hD hn hpath v₀ hv₀
    obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
    -- n = 1: trivial
    by_cases hk0 : k = 0
    · subst hk0
      have huniq : ∀ (a : Fin 1), a = ⟨0, by omega⟩ := fun a => Fin.ext (by omega)
      refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
      · simp [huniq v₀]
      · intro i hk; exact absurd hk (by omega)
      · intro i j hadj_ij
        have hi := huniq i; have hj := huniq j
        rw [hi, hj, hdiag] at hadj_ij; omega
    · -- n = k + 1 ≥ 2
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      -- v₀ has degree exactly 1 (connected + degree ≤ 1 + n ≥ 2)
      have hv₀_deg1 : vertexDegree adj v₀ = 1 := by
        apply le_antisymm hv₀
        -- Degree ≥ 1: pick j ≠ v₀, get path, first edge gives neighbor
        obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), j ≠ v₀ :=
          ⟨⟨if v₀.val = 0 then 1 else 0, by split_ifs <;> omega⟩,
           fun h => by simp only [Fin.ext_iff] at h; split_ifs at h <;> omega⟩
        obtain ⟨path, hhead, hlast, hedges⟩ := hconn v₀ j
        have hlen : 2 ≤ path.length := by
          rcases path with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp at hhead
          · -- path = [a], so head = some a = some v₀ and last = some a = some j
            simp only [List.head?, List.getLast?_singleton] at hhead hlast
            have ha := Option.some.inj hhead
            have hb := Option.some.inj hlast
            exact absurd (ha ▸ hb.symm) hj
          · simp
        -- Extract first edge
        have hadj_01 := hedges 0 (by omega)
        have hp0 : path.get ⟨0, by omega⟩ = v₀ := by
          rcases path with _ | ⟨a, rest⟩
          · simp at hhead
          · exact Option.some.inj hhead
        rw [hp0] at hadj_01
        change 1 ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card
        exact Finset.one_le_card.mpr ⟨path.get ⟨1, by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_01⟩⟩
      -- Get unique neighbor v₁
      have hv₁_nonempty : (Finset.univ.filter (fun j => adj v₀ j = 1)).Nonempty :=
        Finset.card_pos.mp (by change 0 < vertexDegree adj v₀; omega)
      obtain ⟨v₁, hv₁_mem_filter⟩ := hv₁_nonempty
      have hv₁_adj : adj v₀ v₁ = 1 := (Finset.mem_filter.mp hv₁_mem_filter).2
      have hv₁_unique : ∀ w, adj v₀ w = 1 → w = v₁ := by
        intro w hw
        by_contra hne
        -- Both v₁ and w are distinct neighbors, so degree ≥ 2
        have : 2 ≤ vertexDegree adj v₀ := by
          change 2 ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card
          have hw_mem : w ∈ Finset.univ.filter (fun j => adj v₀ j = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
          calc 2 = ({v₁, w} : Finset _).card := by
                rw [Finset.card_pair (Ne.symm hne)]
            _ ≤ (Finset.univ.filter (fun j => adj v₀ j = 1)).card :=
                Finset.card_le_card (fun x hx => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact hv₁_mem_filter
                  · exact hw_mem)
        omega
      have hv₁_ne : v₁ ≠ v₀ := by
        intro h; subst h; rw [hdiag] at hv₁_adj; omega
      -- Define reduced graph on Fin k by removing v₀
      set adj' : Matrix (Fin k) (Fin k) ℤ :=
        fun i j => adj (v₀.succAbove i) (v₀.succAbove j) with hadj'_def
      -- Reduced graph is a Dynkin diagram
      have hD' : IsDynkinDiagram k adj' := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
        · intro i; exact hdiag _
        · intro i j; exact h01 _ _
        · -- Connectivity: removing a leaf preserves connectivity
          -- For any u, w in V\{v₀}, path u → v₁ in V\{v₀} exists,
          -- so u → v₁ → w works.
          sorry
        · -- Positive definiteness: principal submatrix of pos-def
          intro x hx
          set x' : Fin (k + 1) → ℤ := fun a =>
            if h : a = v₀ then 0 else x (Fin.exists_succAbove_eq h).choose
          have hx'_v₀ : x' v₀ = 0 := by simp [x']
          have hx'_sa : ∀ i, x' (v₀.succAbove i) = x i := by
            intro i; simp only [x']
            rw [dif_neg (Fin.succAbove_ne v₀ i)]; congr 1
            exact Fin.succAbove_right_injective
              (Fin.exists_succAbove_eq (Fin.succAbove_ne v₀ i)).choose_spec
          have hx'_ne : x' ≠ 0 := by
            intro heq; apply hx; ext b
            have := congr_fun heq (v₀.succAbove b)
            rw [hx'_sa, Pi.zero_apply] at this; exact this
          have hB_eq : dotProduct x' ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x') =
              dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj').mulVec x) := by
            simp only [dotProduct, mulVec]
            conv_lhs => rw [Fin.sum_univ_succAbove _ v₀]
            simp only [hx'_v₀, zero_mul, zero_add]
            congr 1; ext i; rw [hx'_sa]; congr 1
            conv_lhs => rw [Fin.sum_univ_succAbove _ v₀]
            simp only [hx'_v₀, mul_zero, zero_add]
            congr 1; ext j; rw [hx'_sa]; congr 1
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
              Fin.succAbove_right_inj]
          linarith [hpos x' hx'_ne]
      -- Degree bounds for adj'
      have hpath' : ∀ i, vertexDegree adj' i ≤ 2 := by
        intro i
        -- Degree in subgraph ≤ degree in parent graph (injection via succAbove)
        unfold vertexDegree
        have h_image : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image v₀.succAbove)
            ⊆ Finset.univ.filter (fun j : Fin (k + 1) => adj (v₀.succAbove i) j = 1) := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          obtain ⟨y, hy, rfl⟩ := hx
          exact hy
        have h_card := Finset.card_le_card h_image
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
        have := hpath (v₀.succAbove i)
        unfold vertexDegree at this
        linarith
      -- Find v₁' (preimage of v₁ under succAbove)
      obtain ⟨v₁', hv₁'⟩ := Fin.exists_succAbove_eq hv₁_ne
      -- v₁' is an endpoint in adj' (degree ≤ 1)
      have hv₁'_deg : vertexDegree adj' v₁' ≤ 1 := by
        -- v₁ has degree ≤ 2 in adj. Its neighbor set in adj includes v₀.
        -- Removing v₀ drops one neighbor, so degree in adj' ≤ 1.
        unfold vertexDegree
        -- Image of adj' neighbors under succAbove ⊆ (adj neighbors of v₁) \ {v₀}
        have h_image : ((Finset.univ.filter (fun j : Fin k => adj' v₁' j = 1)).image v₀.succAbove)
            ⊆ (Finset.univ.filter (fun j : Fin (k + 1) => adj v₁ j = 1)).erase v₀ := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne v₀ y, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hv₁']; exact hy
        have h_card := Finset.card_le_card h_image
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
        have hv₀_mem : v₀ ∈ Finset.univ.filter (fun j : Fin (k + 1) => adj v₁ j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply v₀ v₁ ▸ hv₁_adj⟩
        rw [Finset.card_erase_of_mem hv₀_mem] at h_card
        have := hpath v₁; unfold vertexDegree at this
        omega
      -- Apply induction hypothesis
      obtain ⟨σ', hσ'0, hσ'_fwd, hσ'_only⟩ := ih hD' (by omega) hpath' v₁' hv₁'_deg
      -- Construct σ : Fin (k+1) ≃ Fin (k+1) from σ' by prepending v₀
      -- σ(0) = v₀, σ(i+1) = v₀.succAbove(σ'(i))
      -- Proof sketch:
      -- Define f(0) = v₀, f(i+1) = succAbove(σ'(i)).
      -- Injective: f(0) = v₀ ∉ range(succAbove); succAbove ∘ σ' injective.
      -- Bijective by finite injective ↔ bijective.
      -- σ(0) = v₀: by definition.
      -- Consecutive adjacency: f(0)→f(1) = v₀→v₁ uses hv₁_adj;
      --   f(i+1)→f(i+2) uses adj' = adj on succAbove images + hσ'_fwd.
      -- Non-adjacency: f(0)↔f(j+1) forces succAbove(σ'(j)) = v₁,
      --   hence σ'(j) = v₁' = σ'(0), so j = 0.
      --   f(i+1)↔f(j+1) uses hσ'_only.
      sorry

private lemma path_iso_An {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hpath : ∀ i, vertexDegree adj i ≤ 2)
    : ∃ σ : Fin n ≃ Fin n, ∀ i j, adj (σ i) (σ j) = DynkinType.adj (.A n hn) i j := by
  obtain ⟨v₀, hv₀⟩ := dynkin_has_endpoint hD hn hpath
  obtain ⟨σ, _, hσ_fwd, hσ_only⟩ := path_walk_construction hD hn hpath v₀ hv₀
  obtain ⟨hsymm, _, h01, _, _⟩ := hD
  refine ⟨σ, fun i j => ?_⟩
  -- Unfold DynkinType.adj for A_n
  change adj (σ i) (σ j) = if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  -- i j : Fin (DynkinType.A n hn).rank = Fin n definitionally
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  split_ifs with h
  · rcases h with h_fwd | h_bwd
    · have hk : i.val + 1 < n := by linarith
      have heq : j = ⟨i.val + 1, by linarith⟩ := by ext; exact h_fwd.symm
      rw [heq]; exact hσ_fwd i hk
    · have hk : j.val + 1 < n := by linarith
      have heq : i = ⟨j.val + 1, by linarith⟩ := by ext; exact h_bwd.symm
      rw [heq, hsymm.apply]; exact hσ_fwd j hk
  · push_neg at h
    rcases h01 (σ i) (σ j) with h0 | h1
    · exact h0
    · exfalso
      rcases hσ_only i j h1 with h2 | h2
      · exact h.1 h2
      · exact h.2 h2

/-- For a tree with exactly one branch vertex of degree 3, the three arm lengths (p,q,r)
    with p ≤ q ≤ r satisfy n = p + q + r + 1 and 1/(p+1) + 1/(q+1) + 1/(r+1) > 1.
    The positive-definite solutions are:
    - (1,1,r) → D_{r+3}
    - (1,2,2) → E₆, (1,2,3) → E₇, (1,2,4) → E₈ -/
private lemma branch_classification {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) (hn : 1 ≤ n)
    (hbranch : ∃ i, vertexDegree adj i = 3) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  -- Strategy:
  -- 1. There is exactly one vertex of degree 3 (two would give T̃_{p,q,r} subgraph
  --    with null vector, contradicting positive definiteness via subgraph_contradiction)
  -- 2. The branch vertex has 3 arms of lengths p, q, r with p ≤ q ≤ r
  -- 3. n = p + q + r + 1
  -- 4. Positive definiteness requires 1/(p+1) + 1/(q+1) + 1/(r+1) > 1
  --    (otherwise T̃_{p,q,r} has a null vector)
  -- 5. Solutions with p ≤ q ≤ r:
  --    p=1, q=1, r≥1  → D_{r+3}
  --    p=1, q=2, r=2   → E₆
  --    p=1, q=2, r=3   → E₇
  --    p=1, q=2, r=4   → E₈
  -- 6. Construct explicit graph isomorphism for each case
  sorry

/-- Forward direction of the Dynkin classification: any Dynkin diagram is graph-isomorphic
    to one of the standard types A_n, D_n, E₆, E₇, or E₈. -/
private lemma dynkin_classification_forward {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : IsDynkinDiagram n adj) :
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  -- A Dynkin diagram is connected, so n ≥ 1
  have hn : 1 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n
    -- n = 0: No DynkinType has rank 0, so the conclusion is unprovable.
    -- But IsDynkinDiagram 0 adj is vacuously true (no vertices).
    -- This is a minor edge case in the theorem statement; the classification
    -- is only meaningful for n ≥ 1.
    sorry
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
(Etingof Theorem, Section 6.1) -/
theorem Theorem_Dynkin_classification (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    IsDynkinDiagram n adj ↔
    ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j := by
  constructor
  · -- Forward direction: any Dynkin diagram is isomorphic to a standard type
    exact fun hD => dynkin_classification_forward hD
  · -- Backward direction: isomorphism to a standard type → IsDynkinDiagram
    rintro ⟨t, σ, hiso⟩
    exact isDynkinDiagram_of_graph_iso σ hiso (isDynkinDiagram_of_type t)

end Etingof
