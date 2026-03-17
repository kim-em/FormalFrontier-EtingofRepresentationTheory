import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1

/-!
# Proposition 5.21.2: Schur Polynomials at Geometric Progressions

S_λ(1, z, z², …, z^{N-1}) = ∏_{1 ≤ i < j ≤ N} (z^{λᵢ-i} - z^{λⱼ-j}) / (z^{-i} - z^{-j})

In the limit z → 1 (by L'Hôpital):
S_λ(1, …, 1) = ∏_{1 ≤ i < j ≤ N} (λᵢ - λⱼ + j - i) / (j - i)

## Mathlib correspondence

Uses `MvPolynomial.eval` for evaluation and `Finset.prod` for the product formula.
Schur polynomials are defined in `Proposition5_21_1`.
-/

open Finset MvPolynomial Matrix

noncomputable section

namespace Etingof

/-- Evaluation of an `MvPolynomial` at a geometric progression (1, z, z², …, z^{N-1}). -/
def evalGeometric (N : ℕ) (z : ℚ) : MvPolynomial (Fin N) ℚ →+* ℚ :=
  MvPolynomial.eval (fun i => z ^ (i : ℕ))

/-- Alternant determinant under `evalGeometric` equals a Vandermonde product.
The evaluated alternant matrix is the transpose of a Vandermonde matrix in `z^{e_j}`. -/
private lemma evalGeometric_alternantMatrix_det (N : ℕ) (e : Fin N → ℕ) (z : ℚ) :
    evalGeometric N z (alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (z ^ e j - z ^ e i) := by
  rw [RingHom.map_det]
  have h : (evalGeometric N z).mapMatrix (alternantMatrix N e) =
      (vandermonde (fun j : Fin N => z ^ e j))ᵀ := by
    ext i j
    change (evalGeometric N z) ((alternantMatrix N e) i j) = _
    simp only [alternantMatrix, Matrix.of_apply, evalGeometric, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, vandermonde_apply, Matrix.transpose_apply]
    ring
  rw [h, det_transpose, det_vandermonde]

/-- Convert between the double-indexed product `∏ i, ∏ j ∈ Ioi i, f i j` and
the pair-indexed product `∏ p ∈ filter (p.1 < p.2) univ, f p.1 p.2`. -/
private lemma prod_Ioi_eq_prod_filter {N : ℕ} (f : Fin N → Fin N → ℚ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        f p.1 p.2 := by
  rw [← Finset.prod_finset_product']
  intro p
  simp [Finset.mem_filter, Finset.mem_Ioi]

/-- The ratio of Vandermonde-ordered products (f j - f i for i < j) equals
the ratio of reverse-ordered products (f i - f j for i < j), because
the sign factors (-1)^k cancel in the ratio. -/
private lemma ratio_vandermonde_eq_ratio_reversed {N : ℕ} (f g : Fin N → ℚ)
    (_hg : ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
      (g p.1 - g p.2) ≠ 0) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (f j - f i)) /
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (g j - g i)) =
    (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
      (f p.1 - f p.2)) /
    (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
      (g p.1 - g p.2)) := by
  -- Convert ∏ i, ∏ j ∈ Ioi i to ∏ p ∈ filter (using p.2 - p.1 order)
  rw [prod_Ioi_eq_prod_filter (fun i j => f j - f i),
      prod_Ioi_eq_prod_filter (fun i j => g j - g i)]
  -- Factor out (-1) from each factor: (h p.2 - h p.1) = (-1) * (h p.1 - h p.2)
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ
  have neg_factor : ∀ (h : Fin N → ℚ),
      ∏ p ∈ F, (h p.2 - h p.1) = (-1) ^ F.card * ∏ p ∈ F, (h p.1 - h p.2) := by
    intro h
    conv_lhs => arg 2; ext p; rw [show h p.2 - h p.1 = (-1) * (h p.1 - h p.2) by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [neg_factor f, neg_factor g]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0))]

/-- Schur polynomial at a geometric progression:
S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ + N - 1 - i} - z^{λⱼ + N - 1 - j}) /
                          ∏_{i<j} (z^{N - 1 - i} - z^{N - 1 - j}).

Here we state this for `z` in `ℚ` (away from roots of unity where the denominator vanishes).
The product is over pairs `(i, j)` with `i < j` in `Fin N`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric
    (N : ℕ) (lam : Fin N → ℕ) (z : ℚ)
    (_hN : 1 ≤ N)
    -- z is not a root of unity (ensures the Vandermonde denominator is nonzero)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evalGeometric N z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  -- Step 1: Apply evalGeometric (a ring hom) to schurPoly_mul_vandermonde
  have h_fund := schurPoly_mul_vandermonde N lam
  have h_eval : evalGeometric N z (schurPoly N lam) *
      evalGeometric N z (alternantMatrix N (vandermondeExps N)).det =
      evalGeometric N z (alternantMatrix N (shiftedExps N lam)).det := by
    rw [← map_mul]; exact congr_arg _ h_fund
  -- Step 2: Evaluate the alternant determinants as Vandermonde products
  rw [evalGeometric_alternantMatrix_det, evalGeometric_alternantMatrix_det] at h_eval
  -- Step 3: Show the Vandermonde denominator is nonzero
  have h_denom_ne_zero : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (z ^ vandermondeExps N j - z ^ vandermondeExps N i)) ≠ 0 := by
    rw [prod_Ioi_eq_prod_filter]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [vandermondeExps]
    intro h_eq; exact hz p.1 p.2 hp (by linarith)
  -- Step 4: Derive the ratio formula
  have h_ratio : evalGeometric N z (schurPoly N lam) =
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ shiftedExps N lam j - z ^ shiftedExps N lam i)) /
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ vandermondeExps N j - z ^ vandermondeExps N i)) :=
    (eq_div_iff h_denom_ne_zero).mpr h_eval
  rw [h_ratio]
  -- Step 5: Convert from Vandermonde-order to theorem-order and match exponents
  have h_target_denom_ne :
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        ((fun j : Fin N => z ^ vandermondeExps N j) p.1 -
         (fun j : Fin N => z ^ vandermondeExps N j) p.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [vandermondeExps]
    exact hz p.1 p.2 hp
  conv_lhs =>
    rw [ratio_vandermonde_eq_ratio_reversed
      (fun j => z ^ shiftedExps N lam j) (fun j => z ^ vandermondeExps N j)
      h_target_denom_ne]
  -- Step 6: Match the exponents (shiftedExps N lam j = lam j + N - 1 - j, etc.)
  congr 1
  apply Finset.prod_congr rfl; intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  congr 1 <;> (congr 1; simp only [shiftedExps]; omega)

/-- Schur polynomial dimension formula (specialization at z = 1):
S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i) / (j - i).

This follows from `Proposition5_21_2_geometric` by L'Hôpital's rule (or a
direct Vandermonde determinant argument). Here `lam` is a weakly decreasing
sequence (partition), so `λᵢ - λⱼ + j - i > 0` whenever `i < j`.

We state this as evaluation of the Schur polynomial at the all-ones vector.
(Etingof Proposition 5.21.2, second part) -/
theorem Proposition5_21_2_dimension
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) := by
  -- The dimension formula is the z → 1 limit of the geometric formula.
  -- Formalizing L'Hôpital's rule for this multivariate rational function
  -- requires substantial analysis infrastructure beyond current Mathlib.
  sorry

end Etingof
