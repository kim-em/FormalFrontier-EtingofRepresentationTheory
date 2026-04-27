import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Schur-Weyl L_i (part C-4b): Simplicity transfer from `diagonalActionImage` to GL_N

For an algebraically closed (hence infinite) field `k` and `V = Fin N → k`,
GL_N(k) spans `End_k V` as a `k`-vector space. Combined with multilinearity
of `PiTensorProduct.map`, this yields

  `Algebra.adjoin k {g^⊗n : g ∈ GL_N(k)} = diagonalActionImage k V n`.

Hence every `diagonalActionImage`-stable submodule of a module is GL_N-stable
(via the natural action `g ↦ g^⊗n`), and conversely. Simplicity transfers
along this equivalence: a B-simple module is simple as a GL_N-rep.

This is part C-4b of the Schur-Weyl L_i programme (issue #2611). It is the
GL_N-transfer step that combines with #2610 (algebraic core: image of the
primitive idempotent c_λ is a simple B-module) to yield #2583 (simplicity
of `SchurModule k N λ` as a GL_N-rep).
-/

namespace Etingof

open scoped TensorProduct

universe u v

variable (k : Type u) [Field k]

/-! ### Polynomial-subspace closure

If `c ↦ ∑ c^i • m_i` lies in a `k`-submodule `W` for `n+1` distinct values
of `c`, then each coefficient `m_i` lies in `W`. This is the Vandermonde
inversion specialised to module-valued coefficients.
-/

/-- Vandermonde inversion: distinct evaluation points uniquely determine the
coefficients of a polynomial map `k → M` of degree ≤ n. If all evaluations
land in a `k`-submodule `W`, so do the coefficients. -/
theorem submodule_coeffs_mem_of_eval_mem
    {M : Type*} [AddCommGroup M] [Module k M]
    (W : Submodule k M)
    {n : ℕ} (m : Fin (n + 1) → M)
    (c : Fin (n + 1) → k) (hc : Function.Injective c)
    (h : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c j ^ (i : ℕ) • m i ∈ W) :
    ∀ i : Fin (n + 1), m i ∈ W := by
  classical
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) k := Matrix.vandermonde c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde_ne_zero_iff]; exact hc
  have key : ∀ j, ∑ i, V j i • m i ∈ W := by
    intro j
    have := h j
    simpa [V, hV, Matrix.vandermonde_apply] using this
  have h_adj : V.adjugate * V = V.det • (1 : Matrix _ _ k) := Matrix.adjugate_mul V
  intro i
  set v : Fin (n + 1) → M := fun j => ∑ i, V j i • m i
  have hsum : ∑ l, V.adjugate i l • v l = V.det • m i := by
    have step1 : ∀ l, V.adjugate i l • v l =
        ∑ i', (V.adjugate i l * V l i') • m i' := by
      intro l
      simp only [v, Finset.smul_sum, smul_smul]
    calc ∑ l, V.adjugate i l • v l
        = ∑ l, ∑ i', (V.adjugate i l * V l i') • m i' := by simp_rw [step1]
      _ = ∑ i', ∑ l, (V.adjugate i l * V l i') • m i' := Finset.sum_comm
      _ = ∑ i', (∑ l, V.adjugate i l * V l i') • m i' := by
          simp_rw [← Finset.sum_smul]
      _ = ∑ i', (V.adjugate * V) i i' • m i' := by
          simp_rw [Matrix.mul_apply]
      _ = ∑ i', (V.det • (1 : Matrix _ _ k)) i i' • m i' := by rw [h_adj]
      _ = ∑ i', (if i = i' then V.det else 0) • m i' := by
          apply Finset.sum_congr rfl
          intro i' _
          rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
            mul_one, mul_zero]
      _ = V.det • m i := by
          simp [ite_smul, zero_smul]
  have : V.det • m i ∈ W := by
    rw [← hsum]
    exact W.sum_smul_mem _ (fun l _ => key l)
  have := W.smul_mem (V.det)⁻¹ this
  rwa [smul_smul, inv_mul_cancel₀ hVdet, one_smul] at this

/-! ### Polynomial expansion of `(f - c • 1)^⊗n`

We expand `(f - c • 1)^⊗n` via multilinearity of `PiTensorProduct.map` as a
polynomial in `c` of degree at most `n`. The constant term (coefficient of `c^0`)
is `f^⊗n`. Combined with the polynomial-subspace lemma above and the fact that
`f - c • 1` is invertible for cofinitely many `c` (when `V` is finite-dim),
this lets us deduce `f^⊗n ∈ Submodule.span k {g^⊗n : g ∈ Units(End k V)}`.
-/

variable {V : Type v} [AddCommGroup V] [Module k V]

/-- "Mixed tensor power" with `f` on slots in `s` and `1` on slots outside. -/
noncomputable def mixedTensorPow (n : ℕ) (f : Module.End k V)
    (s : Finset (Fin n)) : Module.End k (TensorPower k V n) :=
  PiTensorProduct.map (R := k)
    (fun j : Fin n => if j ∈ s then f else (1 : Module.End k V))

@[simp]
theorem mixedTensorPow_univ (n : ℕ) (f : Module.End k V) :
    mixedTensorPow k n f Finset.univ =
      PiTensorProduct.map (R := k) (fun _ : Fin n => f) := by
  unfold mixedTensorPow
  congr 1
  funext j
  simp

/-- The "tensor coefficient" `A_i(f) ∈ End k (V^⊗n)`: coefficient of `c^i`
in the polynomial expansion of `(f - c • 1)^⊗n`. Defined as
`(-1)^i • ∑_{|s| = n - i} map(s.piecewise (·↦f) (·↦1))`.
The key value is `tensorPowCoeff k n f 0 = f^⊗n`. -/
noncomputable def tensorPowCoeff (n : ℕ) (f : Module.End k V) (i : ℕ) :
    Module.End k (TensorPower k V n) :=
  ((-1 : k)) ^ i • ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard (n - i),
    mixedTensorPow k n f s

/-- The constant coefficient of `(f - c • 1)^⊗n` (as a polynomial in `c`) is `f^⊗n`. -/
theorem tensorPowCoeff_zero (n : ℕ) (f : Module.End k V) :
    tensorPowCoeff k n f 0 =
      PiTensorProduct.map (R := k) (fun _ : Fin n => f) := by
  unfold tensorPowCoeff
  simp only [pow_zero, one_smul, Nat.sub_zero]
  have h1 : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.mem_singleton, Finset.subset_univ,
      true_and]
    refine ⟨fun hcard => Finset.eq_univ_of_card s ?_, fun hs => hs ▸ ?_⟩
    · simpa [Fintype.card_fin] using hcard
    · simp [Fintype.card_fin]
  rw [h1, Finset.sum_singleton, mixedTensorPow_univ]

/-- For each subset `s ⊆ Fin n`, applying `mapMultilinear` to the piecewise
selection of `f` on `s` and `(-c) • 1` outside extracts a `(-c)^{n - |s|}` factor. -/
private theorem map_piecewise_neg_smul_eq (n : ℕ) (f : Module.End k V) (c : k)
    (s : Finset (Fin n)) :
    PiTensorProduct.map (R := k)
      (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
      (-c) ^ (n - s.card) • mixedTensorPow k n f s := by
  classical
  -- Rewrite `s.piecewise f (-c•1)` as a coordinate-wise scaling of the family
  -- `(if j ∈ s then f else 1)` by the scalar `(if j ∈ s then 1 else -c)`.
  have hpw : s.piecewise (fun _ : Fin n => f)
      (fun _ : Fin n => (-c) • (1 : Module.End k V)) =
      fun j : Fin n =>
        (if j ∈ s then (1 : k) else (-c)) •
          (if j ∈ s then f else (1 : Module.End k V)) := by
    funext j
    by_cases hj : j ∈ s
    · simp [Finset.piecewise_eq_of_mem _ _ _ hj, hj]
    · simp [Finset.piecewise_eq_of_notMem _ _ _ hj, hj]
  -- Use map_smul_univ on the multilinear `mapMultilinear`.
  set ml := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ : Fin n => V)
  have h_lhs : PiTensorProduct.map (R := k)
      (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
      ml (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) := rfl
  rw [h_lhs, hpw]
  rw [ml.map_smul_univ
    (c := fun j : Fin n => if j ∈ s then (1 : k) else (-c))
    (m := fun j : Fin n => if j ∈ s then f else (1 : Module.End k V))]
  -- Compute `∏_j (if j ∈ s then 1 else -c) = (-c)^(n - |s|)`.
  have hprod : (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) =
      (-c) ^ (n - s.card) := by
    rw [show (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) =
        ∏ j ∈ Finset.univ, (if j ∈ s then (1 : k) else (-c)) from rfl]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    -- {j : Fin n | j ∉ s}.card = n - s.card
    have hfilt : (Finset.univ.filter (fun j : Fin n => j ∉ s)) =
        (Finset.univ : Finset (Fin n)) \ s := by
      ext j; simp [Finset.mem_sdiff]
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Fintype.card_fin]
  show (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) •
      PiTensorProduct.map (R := k)
        (fun j : Fin n => if j ∈ s then f else (1 : Module.End k V)) =
      (-c) ^ (n - s.card) • mixedTensorPow k n f s
  rw [hprod]
  rfl

/-- Multilinear expansion: `(f - c • 1)^⊗n = ∑_{i=0}^n c^i • A_i(f)` where
`A_i(f) := tensorPowCoeff k n f i`. The constant term `A_0(f)` is `f^⊗n`. -/
theorem tensorPow_sub_smul_eq_sum_coeff (n : ℕ)
    (f : Module.End k V) (c : k) :
    PiTensorProduct.map (R := k) (fun _ : Fin n => f - c • (1 : Module.End k V)) =
      ∑ i ∈ Finset.range (n + 1), c ^ i • tensorPowCoeff k n f i := by
  classical
  -- Step 1: Use `map_add_univ` on `f + (-c)•1`.
  set ml := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ : Fin n => V)
  have h_eq : (fun _ : Fin n => f - c • (1 : Module.End k V))
      = (fun _ : Fin n => f) + (fun _ : Fin n => (-c) • (1 : Module.End k V)) := by
    funext i; simp [neg_smul, sub_eq_add_neg]
  have lhs_eq :
      PiTensorProduct.map (R := k) (fun _ : Fin n => f - c • (1 : Module.End k V)) =
        ∑ s : Finset (Fin n),
          PiTensorProduct.map (R := k)
            (s.piecewise (fun _ : Fin n => f)
              (fun _ : Fin n => (-c) • (1 : Module.End k V))) := by
    show ml _ = _
    rw [h_eq]
    have : ml ((fun _ : Fin n => f) + (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
        ∑ s : Finset (Fin n),
          ml (s.piecewise (fun _ : Fin n => f)
            (fun _ : Fin n => (-c) • (1 : Module.End k V))) :=
      ml.map_add_univ _ _
    convert this using 1
  rw [lhs_eq]
  -- Step 2: Apply `map_piecewise_neg_smul_eq` to extract scalar from each summand.
  rw [Finset.sum_congr rfl (fun s _ => map_piecewise_neg_smul_eq k n f c s)]
  -- Step 3: Group by |s| = j.
  rw [show ((Finset.univ : Finset (Finset (Fin n))) : Finset _) =
      (Finset.range (n + 1)).biUnion
        (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) from by
    ext s
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, true_iff]
    refine ⟨s.card, ?_, Finset.subset_univ _, rfl⟩
    have h1 : s.card ≤ Fintype.card (Fin n) :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Fintype.card_fin] at h1
    omega]
  rw [Finset.sum_biUnion (by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro s ha hb
    rw [Finset.mem_powersetCard] at ha hb
    exact hab (ha.2.symm.trans hb.2))]
  -- Step 4: Reindex j = |s| → i = n - j (involution on Finset.range (n+1)).
  refine Finset.sum_nbij' (fun j => n - j) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    show n - (n - j) = j
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    -- Goal: ∑_{|s| = j} (-c)^{n - |s|} • mixedTensorPow ... = c^(n - j) • tensorPowCoeff k n f (n - j)
    show ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (-c) ^ (n - s.card) • mixedTensorPow k n f s =
      c ^ (n - j) • tensorPowCoeff k n f (n - j)
    have hj' : n - (n - j) = j := by omega
    unfold tensorPowCoeff
    rw [hj']
    -- First simplify the LHS: each s in powersetCard j univ has card = j, so n - card = n - j.
    rw [show ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (-c) ^ (n - s.card) • mixedTensorPow k n f s =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (-c) ^ (n - j) • mixedTensorPow k n f s from by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mem_powersetCard] at hs
      rw [hs.2]]
    -- Pull scalar out and rewrite (-c)^(n-j) = c^(n-j) * (-1)^(n-j).
    rw [← Finset.smul_sum]
    rw [show ((-c) ^ (n - j) : k) = c ^ (n - j) * (-1) ^ (n - j) from by
      rw [neg_pow]; ring]
    rw [mul_smul]

end Etingof
