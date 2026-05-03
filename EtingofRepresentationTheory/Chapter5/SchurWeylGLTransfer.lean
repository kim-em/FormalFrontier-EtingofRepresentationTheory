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

/-! ### Cofinite invertibility of `f - c • 1`

For any `f : End k V` with `V` finite-dimensional, `f - c • 1` is invertible
for all but finitely many `c ∈ k`. The bad set is the eigenvalue set, which
has cardinality at most `finrank V`. -/

/-- For a finite-dim k-vector space V and any `f : End k V`, the set of
`c ∈ k` for which `f - c • 1` is non-invertible is finite (at most `dim V`). -/
theorem exists_finset_isUnit_sub_smul_one [Module.Finite k V] (f : Module.End k V) :
    ∃ S : Finset k, ∀ c, c ∉ S → IsUnit (f - c • (1 : Module.End k V)) := by
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  classical
  -- Use the characteristic polynomial: c is an eigenvalue ↔ c is a root of f.charpoly.
  refine ⟨f.charpoly.roots.toFinset, fun c hc => ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots f.charpoly_monic.ne_zero] at hc
  -- Show: IsUnit (c • 1 - f), hence IsUnit (-(c • 1 - f)) = IsUnit (f - c • 1).
  have h_aux : IsUnit (algebraMap k (Module.End k V) c - f) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.eval_charpoly]
    rw [Polynomial.IsRoot.def] at hc
    exact Ne.isUnit hc
  have h_eq : f - c • (1 : Module.End k V) = -(algebraMap k (Module.End k V) c - f) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [h_eq]
  exact h_aux.neg

/-! ### Main span lemma

For an infinite field `k` and finite-dim `V`, every `f^⊗n` lies in the `k`-span
of `{g^⊗n : g ∈ Units(End k V)}`. This is the Zariski-density fact that GL(V)
spans `End k V`.
-/

/-- For an infinite field `k` and finite-dim `V`, `f^⊗n` lies in the `k`-span
of `{g^⊗n : g ∈ Units(End k V)}` for every `f : End k V`. -/
theorem tensorPow_mem_span_unitsTensorPow [Module.Finite k V] [Infinite k]
    (n : ℕ) (f : Module.End k V) :
    PiTensorProduct.map (R := k) (fun _ : Fin n => f) ∈
      Submodule.span k
        (Set.range fun (g : (Module.End k V)ˣ) =>
          PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
  classical
  set W := Submodule.span k
        (Set.range fun (g : (Module.End k V)ˣ) =>
          PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) with hW
  -- Step 1: Pick n+1 distinct values c_0, ..., c_n ∈ k with `f - c_j • 1 ∈ Units`.
  obtain ⟨S, hS⟩ := exists_finset_isUnit_sub_smul_one k f
  -- The complement Sᶜ ⊆ k is infinite (since S is finite and k is infinite).
  have hSc_infinite : (↑S : Set k)ᶜ.Infinite := S.finite_toSet.infinite_compl
  -- Pick `n + 1` distinct values from Sᶜ via natEmbedding.
  let e : ℕ ↪ ((↑S : Set k)ᶜ : Set k) := hSc_infinite.natEmbedding
  let c : Fin (n + 1) → k := fun j => ((e j.val) : k)
  have hc_inj : Function.Injective c := by
    intro j₁ j₂ hjj
    have h1 : e j₁.val = e j₂.val := Subtype.ext hjj
    have h2 : j₁.val = j₂.val := e.injective h1
    exact Fin.val_injective h2
  have hc_notin_S : ∀ j, c j ∉ S := fun j => by
    have h1 : (c j : k) ∈ ((↑S : Set k)ᶜ : Set k) := (e j.val).property
    rw [Set.mem_compl_iff, Finset.mem_coe] at h1
    exact h1
  -- For each j, `f - c j • 1 ∈ Units`, so `(f - c j • 1)^⊗n ∈ W`.
  have h_in_W : ∀ j : Fin (n + 1), PiTensorProduct.map (R := k)
      (fun _ : Fin n => f - c j • (1 : Module.End k V)) ∈ W := by
    intro j
    have h_unit : IsUnit (f - c j • (1 : Module.End k V)) := hS (c j) (hc_notin_S j)
    refine Submodule.subset_span ⟨h_unit.unit, ?_⟩
    rfl
  -- Apply Vandermonde: each `tensorPowCoeff k n f i ∈ W`.
  -- Reformulate the sum over `Finset.range (n+1)` as `∑ i : Fin (n+1)`.
  have h_in_W' : ∀ j : Fin (n + 1),
      ∑ i : Fin (n + 1), c j ^ (i : ℕ) • tensorPowCoeff k n f i ∈ W := by
    intro j
    have h_eq := tensorPow_sub_smul_eq_sum_coeff k n f (c j)
    rw [show (∑ i ∈ Finset.range (n + 1), c j ^ i • tensorPowCoeff k n f i) =
        ∑ i : Fin (n + 1), c j ^ (i : ℕ) • tensorPowCoeff k n f i from by
      rw [Finset.sum_range (fun i => c j ^ i • tensorPowCoeff k n f i)]] at h_eq
    rw [← h_eq]
    exact h_in_W j
  have h_coeff_in_W : ∀ i : Fin (n + 1), tensorPowCoeff k n f (i : ℕ) ∈ W := by
    apply submodule_coeffs_mem_of_eval_mem k W _ c hc_inj
    exact h_in_W'
  -- In particular, `tensorPowCoeff k n f 0 = f^⊗n ∈ W`.
  have := h_coeff_in_W ⟨0, Nat.zero_lt_succ n⟩
  rw [show ((⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) : ℕ) = 0 from rfl,
    tensorPowCoeff_zero] at this
  exact this

/-! ### Algebra equality `Algebra.adjoin k {g^⊗n : g ∈ Units} = diagonalActionImage` -/

/-- For an infinite field `k` and finite-dim `V`, the `k`-subalgebra
generated by `{g^⊗n : g ∈ Units(End k V)}` equals `diagonalActionImage k V n`. -/
theorem adjoin_unitsTensorPow_eq_diagonalActionImage
    [Module.Finite k V] [Infinite k] (n : ℕ) :
    Algebra.adjoin k (Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) =
    diagonalActionImage k V n := by
  apply le_antisymm
  · -- ⊆: every g^⊗n with g a unit is f^⊗n for f = g.val ∈ End k V.
    apply Algebra.adjoin_le
    rintro x ⟨g, rfl⟩
    exact Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩
  · -- ⊇: every f^⊗n is in span ⊆ adjoin of g^⊗n's.
    apply Algebra.adjoin_le
    rintro x ⟨f, rfl⟩
    -- f^⊗n ∈ span k {g^⊗n : g ∈ Units} ⊆ adjoin k {g^⊗n : g ∈ Units}.
    have h_span := tensorPow_mem_span_unitsTensorPow k n f
    exact Algebra.span_le_adjoin k _ h_span

/-! ### Simplicity transfer

If a `diagonalActionImage`-module `M` is `B`-simple, then it is GL-simple in
the sense that every k-subspace of `M` closed under all `g^⊗n` (for `g` a unit
in `End k V`) is either `⊥` or `⊤`.

The key is `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem`: a
k-subspace closed under units is closed under all of `B`. The simplicity
transfer is then immediate: a B-submodule (in disguise) of a simple B-module
is `⊥` or `⊤`.
-/

-- Heartbeat bump: nested `Algebra.adjoin_induction` + `Submodule.span_induction`
-- with subtype-membership predicates triggers heavy `isDefEq` work.
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Submodule transfer: every k-submodule of a `diagonalActionImage`-module
closed under the action of `g^⊗n` (for every unit `g` in `End k V`) is closed
under the action of all of `B = diagonalActionImage`. -/
theorem submodule_smul_mem_diagonalActionImage_of_unit_smul_mem
    [Module.Finite k V] [Infinite k]
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (diagonalActionImage k V n) M]
    [IsScalarTower k (diagonalActionImage k V n) M]
    (W : Submodule k M)
    (hW : ∀ (g : (Module.End k V)ˣ),
        ∀ x ∈ W, (⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
            Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩⟩ :
              diagonalActionImage k V n) • x ∈ W)
    (b : diagonalActionImage k V n) (x : M) (hx : x ∈ W) :
    b • x ∈ W := by
  classical
  -- Reformulate as adjoin induction over `b.val ∈ adjoin k {f^⊗n : f ∈ End k V}`
  -- (the original definition of `diagonalActionImage`).
  obtain ⟨b_val, b_mem⟩ := b
  -- Generalise `x` to all `y ∈ W` so adjoin induction can be applied.
  -- Generalize x ∈ W to all y ∈ W so adjoin induction can be applied.
  suffices h : ∀ y ∈ W, (⟨b_val, b_mem⟩ : diagonalActionImage k V n) • y ∈ W by
    exact h x hx
  -- Goal: ∀ y ∈ W, (⟨b_val, b_mem⟩ : B) • y ∈ W. Induct on b_mem.
  refine Algebra.adjoin_induction
    (s := Set.range fun (f : Module.End k V) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => f))
    (p := fun b_val' _ =>
      ∀ (h_mem : b_val' ∈ diagonalActionImage k V n),
      ∀ y ∈ W, (⟨b_val', h_mem⟩ : diagonalActionImage k V n) • y ∈ W)
    ?_ ?_ ?_ ?_ b_mem b_mem
  · -- Generator case: b_val' = f^⊗n for some f ∈ End k V.
    rintro b_val' ⟨f, rfl⟩ h_mem y hy
    -- f^⊗n is in span k {g^⊗n : g unit}, so this is a k-linear combination.
    have h_span := tensorPow_mem_span_unitsTensorPow k n f
    -- Use Submodule.span_induction as a function.
    refine Submodule.span_induction
      (M := Module.End k (TensorPower k V n))
      (R := k)
      (s := Set.range fun (g : (Module.End k V)ˣ) =>
        PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)))
      (p := fun b'' _ =>
        ∀ (h_b_mem : b'' ∈ diagonalActionImage k V n),
        (⟨b'', h_b_mem⟩ : diagonalActionImage k V n) • y ∈ W)
      ?_ ?_ ?_ ?_ h_span h_mem
    · rintro b'' ⟨g, rfl⟩ h_b_mem
      have := hW g y hy
      convert this
    · intro h_zero_mem
      rw [show (⟨0, h_zero_mem⟩ : diagonalActionImage k V n) = 0 from rfl, zero_smul]
      exact W.zero_mem
    · intro b₁ b₂ h₁_in h₂_in ih₁ ih₂ h_b_mem
      have h₁_mem : b₁ ∈ diagonalActionImage k V n := by
        rw [← adjoin_unitsTensorPow_eq_diagonalActionImage]
        exact Algebra.span_le_adjoin k _ h₁_in
      have h₂_mem : b₂ ∈ diagonalActionImage k V n := by
        rw [← adjoin_unitsTensorPow_eq_diagonalActionImage]
        exact Algebra.span_le_adjoin k _ h₂_in
      rw [show (⟨b₁ + b₂, h_b_mem⟩ : diagonalActionImage k V n) =
          (⟨b₁, h₁_mem⟩ : diagonalActionImage k V n) +
          (⟨b₂, h₂_mem⟩ : diagonalActionImage k V n) from rfl, add_smul]
      exact W.add_mem (ih₁ h₁_mem) (ih₂ h₂_mem)
    · intro a b₁ h₁_in ih h_smul_mem
      have h₁_mem : b₁ ∈ diagonalActionImage k V n := by
        rw [← adjoin_unitsTensorPow_eq_diagonalActionImage]
        exact Algebra.span_le_adjoin k _ h₁_in
      rw [show (⟨a • b₁, h_smul_mem⟩ : diagonalActionImage k V n) =
          a • (⟨b₁, h₁_mem⟩ : diagonalActionImage k V n) from rfl, smul_assoc]
      exact W.smul_mem a (ih h₁_mem)
  · -- algebraMap r:
    intros r h_mem y hy
    rw [show (⟨algebraMap k _ r, h_mem⟩ : diagonalActionImage k V n) =
        algebraMap k _ r from rfl,
      Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    exact W.smul_mem r hy
  · -- Add case (top-level adjoin):
    rintro b₁ b₂ h₁_adj h₂_adj ih₁ ih₂ h_mem y hy
    have h₁_mem : b₁ ∈ diagonalActionImage k V n := h₁_adj
    have h₂_mem : b₂ ∈ diagonalActionImage k V n := h₂_adj
    rw [show (⟨b₁ + b₂, h_mem⟩ : diagonalActionImage k V n) =
        (⟨b₁, h₁_mem⟩ : diagonalActionImage k V n) +
        (⟨b₂, h₂_mem⟩ : diagonalActionImage k V n) from rfl, add_smul]
    exact W.add_mem (ih₁ h₁_mem y hy) (ih₂ h₂_mem y hy)
  · -- Mul case (top-level adjoin):
    rintro b₁ b₂ h₁_adj h₂_adj ih₁ ih₂ h_mem y hy
    have h₁_mem : b₁ ∈ diagonalActionImage k V n := h₁_adj
    have h₂_mem : b₂ ∈ diagonalActionImage k V n := h₂_adj
    have hy₂ := ih₂ h₂_mem y hy
    have hy₁ := ih₁ h₁_mem _ hy₂
    rw [show (⟨b₁ * b₂, h_mem⟩ : diagonalActionImage k V n) =
        (⟨b₁, h₁_mem⟩ : diagonalActionImage k V n) *
        (⟨b₂, h₂_mem⟩ : diagonalActionImage k V n) from rfl, mul_smul]
    exact hy₁

/-- Simplicity transfer: if `M` is a `diagonalActionImage`-simple module, then
every k-subspace of `M` closed under the action of `g^⊗n` (for every unit `g`)
is either `⊥` or `⊤`. -/
theorem submodule_eq_bot_or_top_of_unit_smul_mem
    [Module.Finite k V] [Infinite k]
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (diagonalActionImage k V n) M]
    [IsScalarTower k (diagonalActionImage k V n) M]
    [IsSimpleModule (diagonalActionImage k V n) M]
    (W : Submodule k M)
    (hW : ∀ (g : (Module.End k V)ˣ),
        ∀ x ∈ W, (⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
            Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩⟩ :
              diagonalActionImage k V n) • x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  -- W is closed under all of B (by submodule transfer), so it's a B-submodule.
  let W' : Submodule (diagonalActionImage k V n) M :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun b x hx =>
        submodule_smul_mem_diagonalActionImage_of_unit_smul_mem k W hW b x hx }
  -- B-simplicity: W' is ⊥ or ⊤.
  rcases (IsSimpleOrder.eq_bot_or_eq_top W' : W' = ⊥ ∨ W' = ⊤) with h | h
  · left
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have : x ∈ W' := hx
      rw [h] at this
      exact this
    · simp at hx
      exact hx ▸ W.zero_mem
  · right
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have : x ∈ W' := by rw [h]; trivial
    exact this

/-! ### MonoidAlgebra-simplicity transfer

A representation of `GL_N(k)` whose action factors through
`g ↦ ⟨g^⊗n, _⟩ ∈ diagonalActionImage k V n` (with `V = Fin N → k`) inherits
simplicity from the `diagonalActionImage`-side: a `diagonalActionImage`-simple
module becomes simple as a `MonoidAlgebra k GL_N`-module via the
representation.

This packages the chain
* `Submodule k[GL_N] ρ.asModule` ↪ `Submodule k M` (via `restrictScalars`),
* GL_N-closure ⇒ `(End k V)ˣ`-closure (via `Matrix.GeneralLinearGroup.toLin`),
* `(End k V)ˣ`-closure + `diagonalActionImage`-simplicity ⇒ `⊥` or `⊤`
  (via `submodule_eq_bot_or_top_of_unit_smul_mem`),
* `⊥`/`⊤` of `restrictScalars` ⇔ `⊥`/`⊤` of original (via
  `restrictScalars_eq_bot_iff`/`_top_iff`).
-/

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Simplicity transfer for representations factoring through `diagonalActionImage`:
if `M` is a `diagonalActionImage k (Fin N → k) n`-simple module and the
`GL_N`-representation `ρ` on `M` factors through `g ↦ ⟨g^⊗n, _⟩`, then `M`
is simple as a `MonoidAlgebra k GL_N`-module via `ρ`. -/
theorem isSimpleModule_monoidAlgebra_GL_of_centralizer_simple
    {N n : ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module (diagonalActionImage k (Fin N → k) n) M]
    [IsScalarTower k (diagonalActionImage k (Fin N → k) n) M]
    [IsSimpleModule (diagonalActionImage k (Fin N → k) n) M]
    [IsAlgClosed k]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) M)
    (h_act : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M),
        ρ g x =
          (⟨PiTensorProduct.map (R := k)
              (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val),
            Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩⟩ :
              diagonalActionImage k (Fin N → k) n) • x) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      ρ.asModule := by
  haveI : Module.Finite k (Fin N → k) := inferInstance
  haveI : Nontrivial M :=
    IsSimpleModule.nontrivial (diagonalActionImage k (Fin N → k) n) M
  haveI : Nontrivial ρ.asModule := (show Nontrivial M from inferInstance)
  haveI : Nontrivial (Submodule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) ρ.asModule) :=
    (Submodule.nontrivial_iff
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))).mpr inferInstance
  rw [isSimpleModule_iff]
  -- `IsSimpleOrder` extends `Nontrivial`; supply `Nontrivial` via instance synthesis
  -- and provide the `eq_bot_or_eq_top` field directly.
  refine ⟨fun W => ?_⟩
  -- Reinterpret W as a k-submodule of M (via restrictScalars k).
  set W_k : Submodule k M := W.restrictScalars k with hW_k_def
  -- W_k is closed under `⟨f^⊗n, _⟩` for every `f : (End k V)ˣ`,
  -- via the bridge `Matrix.GeneralLinearGroup.toLin.symm`.
  have hW_k_closed : ∀ (f : (Module.End k (Fin N → k))ˣ),
      ∀ x ∈ W_k,
      (⟨PiTensorProduct.map (R := k)
          (fun _ : Fin n => (f : Module.End k (Fin N → k))),
        Algebra.subset_adjoin ⟨(f : Module.End k (Fin N → k)), rfl⟩⟩ :
          diagonalActionImage k (Fin N → k) n) • x ∈ W_k := by
    intro f x hx
    -- Bridge: pick `g : GL_N` with `mulVecLin g.val = f.val`.
    set g : Matrix.GeneralLinearGroup (Fin N) k :=
      (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := k)).symm f with hg_def
    have hg_eq : Matrix.mulVecLin (R := k) g.val =
        (f : Module.End k (Fin N → k)) := by
      have h := MulEquiv.apply_symm_apply
        (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := k)) f
      exact congrArg Units.val h
    -- Rewrite the LHS using `hg_eq` so it matches `ρ g x` via `h_act`.
    have hfg : (fun _ : Fin n => (f : Module.End k (Fin N → k))) =
        (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val) :=
      funext fun _ => hg_eq.symm
    have h_subst : (⟨PiTensorProduct.map (R := k)
        (fun _ : Fin n => (f : Module.End k (Fin N → k))),
        Algebra.subset_adjoin ⟨(f : Module.End k (Fin N → k)), rfl⟩⟩ :
          diagonalActionImage k (Fin N → k) n) =
        ⟨PiTensorProduct.map (R := k)
            (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val),
          Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩⟩ :=
      Subtype.ext (congrArg (PiTensorProduct.map (R := k)) hfg)
    rw [h_subst, ← h_act g x]
    -- `ρ g x = (single g 1) • x` on `ρ.asModule` (`Representation.single_smul`),
    -- and `W` is closed under the `MonoidAlgebra` action.
    change ρ g x ∈ W_k
    have hxW : (show ρ.asModule from x) ∈ W := hx
    have h_single : (MonoidAlgebra.single g (1 : k) :
        MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) •
        (show ρ.asModule from x) = ρ g x := by
      rw [Representation.single_smul, one_smul]
      rfl
    rw [hW_k_def, Submodule.restrictScalars_mem]
    exact h_single ▸ W.smul_mem _ hxW
  have h_W_k := submodule_eq_bot_or_top_of_unit_smul_mem k W_k hW_k_closed
  rcases h_W_k with h | h
  · left
    rwa [hW_k_def, Submodule.restrictScalars_eq_bot_iff] at h
  · right
    rwa [hW_k_def, Submodule.restrictScalars_eq_top_iff] at h

-- Heartbeats and synth-heartbeats bumped: the existential output has 11+ ∀-binders
-- with `Subalgebra → Ring → Module.End` instance chains, and the per-i transport
-- through `Subalgebra.equivOfEq` adds further `Module.compHom` synthesis cost
-- (matching the budgets used by `_GL_rep_decomposition_explicit`).
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- Schur-Weyl duality, part (iii), GL_N-representation form, with the
**simplicity** clause for each `L i` summand.

Refines `Theorem5_18_4_GL_rep_decomposition` by adding
`∀ i, IsSimpleModule (MonoidAlgebra k GL_N) (Representation.asModule (L i).ρ)`.

This wrapper sits in `SchurWeylGLTransfer.lean` (and not next to its
companions in `Theorem5_18_4.lean`) because the simplicity transfer
helper `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` is
defined here, after `Theorem5_18_4.lean` in the import order.

Combines:

* `Theorem5_18_4_bimodule_decomposition_explicit`'s simplicity clause:
  each `↥(S i) →ₗ[symGroupImage k V n] V^⊗n` is simple over
  `centralizer(symGroupImage k V n)`;
* `Theorem5_18_4_centralizers`: the subalgebra equality
  `centralizer(symGroupImage) = diagonalActionImage`;
* `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` (above): a
  `diagonalActionImage`-simple module whose `GL_N`-action factors
  through `g ↦ ⟨g^⊗n, _⟩` is simple as a `MonoidAlgebra k GL_N`-module.
-/
theorem Theorem5_18_4_GL_rep_decomposition_simple
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (symGroupImage k (Fin N → k) n) (S i))
      (_ : ∀ i, IsSimpleModule (symGroupImage k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (S i ≃ₗ[symGroupImage k (Fin N → k) n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)),
      Nonempty (TensorPower k (Fin N → k) n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] (L i : Type u))) := by
  set V : Type u := Fin N → k with hV
  haveI : Module.Finite k V := inferInstance
  have hfinrank : Module.finrank k V = N :=
    (Module.finrank_pi k).trans (Fintype.card_fin N)
  have hN' : n ≤ Module.finrank k V := hfinrank.symm ▸ hN
  haveI := symGroupImage_isSemisimpleRing k V n
  haveI := symGroupImage_faithfulSMul k V n hN'
  -- Re-destructure the bimodule decomposition; this time we keep `homA_simp`
  -- (the centralizer-side simplicity clause) which the inner
  -- `_GL_rep_decomposition_explicit` discards.
  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, homA_simp, e, _he⟩ :=
    Theorem5_18_4_bimodule_decomposition_explicit k V n hN'
  -- Build the GL_N action data exactly as in `_explicit`.
  let glHom : Matrix.GeneralLinearGroup (Fin N) k →*
      ↥(Subalgebra.centralizer k
        (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))) :=
    glHom_to_centralizer_symGroupImage k N n
  haveI hLi_fin : ∀ i, Module.Finite k
      ((↥(S' i) : Type u) →ₗ[symGroupImage k V n] TensorPower k V n) :=
    fun i => by
      haveI : Module.Finite k (↥(S' i) : Type u) := hS'_fin i
      haveI : Module.Free k (↥(S' i) : Type u) :=
        Module.Free.of_divisionRing k (↥(S' i))
      haveI : Module.Finite k
          ((↥(S' i) : Type u) →ₗ[k] TensorPower k V n) :=
        Module.Finite.linearMap k k (↥(S' i)) (TensorPower k V n)
      exact Module.Finite.of_injective
        (LinearMap.restrictScalarsₗ k (symGroupImage k V n) (↥(S' i))
          (TensorPower k V n) k)
        (LinearMap.restrictScalars_injective _)
  let ρ_i : ∀ i, Matrix.GeneralLinearGroup (Fin N) k →*
      Module.End k (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) := fun i =>
    (postCompCentralizerMonoidHom k (TensorPower k V n) (symGroupImage k V n)
      (↥(S' i))).comp glHom
  -- Centralizer = diagonalActionImage equality (Theorem5_18_4_centralizers, RHS).
  have h_eq : Subalgebra.centralizer k
      (symGroupImage k V n : Set (Module.End k (TensorPower k V n))) =
      diagonalActionImage k V n :=
    ((Theorem5_18_4_centralizers k V n hN').2).symm
  -- For each i, prove simplicity of the GL_N-representation `FDRep.of (ρ_i i)`
  -- as a `MonoidAlgebra k GL_N`-module.
  have hL_simple : ∀ i, IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (FDRep.of (ρ_i i)).ρ) := by
    intro i
    -- Pin the canonical centralizer-module structure on the hom-space.
    letI hC_mod :
        Module (↥(Subalgebra.centralizer k
          (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) :=
      centralizerModuleHom (A := symGroupImage k V n)
        (V := (↥(S' i) : Type u))
    haveI hC_st :
        IsScalarTower k
          (↥(Subalgebra.centralizer k
            (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) := by
      refine ⟨fun a c f => ?_⟩
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)
    haveI hC_simp :
        IsSimpleModule
          (↥(Subalgebra.centralizer k
            (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) :=
      homA_simp i
    -- Algebra equiv `diagonalActionImage ≃ₐ centralizer(symGroupImage)`.
    let φ : ↥(diagonalActionImage k V n) ≃ₐ[k]
        ↥(Subalgebra.centralizer k
          (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))) :=
      Subalgebra.equivOfEq _ _ h_eq.symm
    -- Transport `Module centralizer M` ⇝ `Module diagonalActionImage M` via φ.
    letI hD_mod :
        Module (↥(diagonalActionImage k V n))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) :=
      Module.compHom (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n)
        (φ : ↥(diagonalActionImage k V n) →+*
          ↥(Subalgebra.centralizer k
            (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))
    haveI hD_st :
        IsScalarTower k (↥(diagonalActionImage k V n))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) := by
      refine ⟨fun a d m => ?_⟩
      change φ (a • d) • m = a • φ d • m
      rw [map_smul]
      exact (smul_assoc a (φ d) m).symm
    haveI hφ_surj :
        RingHomSurjective
          (φ : ↥(diagonalActionImage k V n) →+*
            ↥(Subalgebra.centralizer k
              (symGroupImage k V n : Set (Module.End k (TensorPower k V n))))) :=
      ⟨φ.surjective⟩
    haveI hD_simp :
        IsSimpleModule (↥(diagonalActionImage k V n))
          (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) := by
      let l : (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n)
          →ₛₗ[(φ : ↥(diagonalActionImage k V n) →+*
              ↥(Subalgebra.centralizer k
                (symGroupImage k V n : Set (Module.End k (TensorPower k V n)))))]
            (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) :=
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact (LinearMap.isSimpleModule_iff_of_bijective l
        Function.bijective_id).mpr hC_simp
    haveI : Module.Finite k
        (↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n) :=
      hLi_fin i
    refine isSimpleModule_monoidAlgebra_GL_of_centralizer_simple k
      (N := N) (n := n)
      (M := ↥(S' i) →ₗ[symGroupImage k V n] TensorPower k V n)
      (FDRep.of (ρ_i i)).ρ ?_
    intro g x
    -- LHS: `(L i).ρ g x = ρ_i i g x = (centralizerToEndA (glHom g)).comp x`,
    --      i.e. `v ↦ g^⊗n (x v) = v ↦ PiTensorProduct.map (mulVecLin g.val) (x v)`.
    -- RHS: `⟨g^⊗n, …⟩_D • x = φ ⟨g^⊗n, …⟩_D • x = ⟨g^⊗n, h_eq.symm ▸ …⟩_C • x`,
    --      i.e. `v ↦ g^⊗n (x v)`. They agree pointwise.
    exact LinearMap.ext fun _ => rfl
  refine ⟨ι, hι, hι_dec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    hS'_simp, hS'_dist, hS'_fin,
    fun i => FDRep.of (ρ_i i), hL_simple, ⟨e⟩⟩

end Etingof
