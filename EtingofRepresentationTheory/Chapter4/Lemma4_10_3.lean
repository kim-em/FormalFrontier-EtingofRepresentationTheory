import Mathlib

/-!
# Lemma 4.10.3: Irreducibility of the Generic Determinant

For an n × n matrix Y with entries y_{ij} treated as independent variables,
det(Y) is an irreducible polynomial in the n² variables {y_{ij}}.

## Proof strategy

By induction on n using cofactor expansion along row 0 and
`MvPolynomial.irreducible_mul_X_add`.

## Mathlib correspondence

Mathlib has `Matrix.det` and `MvPolynomial.Irreducible`. The irreducibility of
the generic determinant is not proved in Mathlib.
-/

open MvPolynomial Matrix Finset

-- Abbreviation for the generic matrix
private noncomputable def genMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  of fun i j => X (i, j)

@[simp] private lemma genMatrix_apply (m : ℕ) (i j : Fin m) :
    genMatrix m i j = X (i, j) := rfl

private lemma genMatrix_eq_mvPolynomialX (m : ℕ) :
    genMatrix m = mvPolynomialX (Fin m) (Fin m) ℂ := rfl

/-- A submatrix determinant equals the rename of the smaller determinant. -/
private lemma submatrix_eq_rename (n : ℕ) (c : Fin (n + 2)) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c)) =
    rename (Prod.map Fin.succ (Fin.succAbove c)) (det (genMatrix (n + 1))) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [genMatrix_apply, submatrix_apply, AlgHom.mapMatrix_apply, rename_X]

/-- Variables in any submatrix determinant have first component ≥ 1. -/
private lemma submatrix_vars_fst_ne_zero (n : ℕ) (c : Fin (n + 2))
    {v : Fin (n + 2) × Fin (n + 2)}
    (hv : v ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))).vars) :
    v.1 ≠ 0 := by
  rw [submatrix_eq_rename] at hv
  obtain ⟨⟨a, b⟩, _, hab⟩ := mem_vars_rename _ _ hv
  exact hab ▸ Fin.succ_ne_zero a

/-- The (0,0) minor equals the rename of the smaller determinant (column 0 case). -/
private lemma minor00_eq_rename (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) =
    rename (Prod.map Fin.succ Fin.succ) (det (genMatrix (n + 1))) := by
  have := submatrix_eq_rename n 0
  simp only [Fin.succAbove_zero] at this ⊢
  exact this

/-- The (0,0) minor is nonzero. -/
private lemma minor00_ne_zero (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) ≠ 0 := by
  rw [minor00_eq_rename]
  exact (rename_injective _
    (Prod.map_injective.mpr ⟨Fin.succ_injective _, Fin.succ_injective _⟩)).ne
    (det_mvPolynomialX_ne_zero (Fin (n + 1)) ℂ)

/-- The (0,0) minor doesn't involve variable (0,0). -/
private lemma minor00_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))).vars := by
  intro h
  exact absurd rfl (submatrix_vars_fst_ne_zero n 0 h)

/-- The remaining cofactor terms don't involve X(0,0). -/
private lemma rest_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (∑ j : Fin (n + 1),
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
      X ((0 : Fin (n + 2)), j.succ) *
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))).vars := by
  intro h
  have h' := vars_sum_subset (Finset.univ) _ h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h'
  obtain ⟨j, hj⟩ := h'
  -- vars of each term ⊆ vars of the two factors
  have hj' := vars_mul _ _ hj
  simp only [Finset.mem_union] at hj'
  rcases hj' with hj' | hj'
  · -- (0,0) in vars of (-1)^(j+1) * X(0, j.succ)
    have hj'' := vars_mul _ _ hj'
    simp only [Finset.mem_union] at hj''
    rcases hj'' with hj'' | hj''
    · -- (0,0) in vars of (-1)^(j+1) — impossible, it's a constant
      exact absurd (vars_pow _ _ hj'') (by simp)
    · -- (0,0) in vars(X(0, j.succ)) = {(0, j.succ)}
      rw [vars_X] at hj''
      simp only [Finset.mem_singleton] at hj''
      exact absurd (congr_arg Prod.snd hj'').symm (Fin.succ_ne_zero j)
  · -- (0,0) in vars of det(submatrix ... j.succ)
    exact absurd rfl (submatrix_vars_fst_ne_zero n j.succ hj')

/-- Irreducibility is preserved by `MvPolynomial.rename` with an injective function.
This is a general fact: in MvPolynomial over a domain, if `f` is injective then
`rename f` preserves irreducibility. The proof uses: (1) pick left inverse `g` of `f`,
(2) if `rename f p = a * b`, apply `rename g` to get `p = (rename g a) * (rename g b)`,
(3) WLOG `rename g a` is a unit, (4) show `a` is a unit using `degreeOf_mul_eq` to
establish `vars(a) ⊆ range f`, then `rename (f ∘ g) a = a`, hence `a = rename f (C c)`.
Missing from Mathlib; see https://github.com/leanprover-community/mathlib4/issues/XXXXX -/
private lemma rename_irreducible {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ ℂ} (hp : Irreducible p) :
    Irreducible (rename f p) := by
  sorry

/-- The (0,0) minor is coprime to the rest of the cofactor expansion. -/
private lemma minor00_isRelPrime (n : ℕ) (ih' : Irreducible (det (genMatrix (n + 1)))) :
    IsRelPrime
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)))
      (∑ j : Fin (n + 1),
        (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
        X ((0 : Fin (n + 2)), j.succ) *
        det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) := by
  -- The minor M₀₀ is irreducible (hence prime in UFD) by IH + rename
  have hf_irr : Irreducible (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) := by
    rw [minor00_eq_rename]
    exact rename_irreducible (Prod.map_injective.mpr
      ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih'
  -- Irreducible ↔ not-dvd for IsRelPrime
  rw [hf_irr.isRelPrime_iff_not_dvd]
  -- M₀₀ doesn't divide the rest: evaluating X(0,1)→1, X(0,j)→0 for j>1
  -- would give M₀₀ | M₀₁, but (1,1) ∈ vars(M₀₀) and (1,1) ∉ vars(M₀₁).
  sorry

/-- The determinant of a generic n × n matrix is an irreducible polynomial.
(Etingof Lemma 4.10.3) -/
theorem Etingof.Lemma4_10_3 (n : ℕ) (hn : 0 < n) :
    Irreducible (det (genMatrix n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- 1×1 case: det = X(0,0), which has totalDegree 1
      have hdet : det (genMatrix 1) = X ((0 : Fin 1), (0 : Fin 1)) := by
        unfold genMatrix; rw [det_fin_one]; rfl
      rw [hdet]
      exact irreducible_of_totalDegree_eq_one
        (totalDegree_X _)
        (fun x hx => isUnit_of_dvd_one (by
          have := hx (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1)
          rwa [coeff_X] at this))
    | succ n =>
      -- (n+2)×(n+2) case. IH gives irreducibility for (n+1)×(n+1).
      have ih' := ih (by omega)
      -- Cofactor expansion: det = f * X(0,0) + g
      suffices heq : det (genMatrix (n + 2)) =
          det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) *
          X ((0 : Fin (n + 2)), (0 : Fin (n + 2))) +
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
            X ((0 : Fin (n + 2)), j.succ) *
            det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) by
        rw [heq]
        exact irreducible_mul_X_add _ _ _
          (minor00_ne_zero n)
          (minor00_vars n)
          (rest_vars n)
          (minor00_isRelPrime n ih')
      -- Prove via det_succ_row_zero
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [genMatrix_apply, Fin.val_zero, pow_zero, one_mul]
      congr 1
      · ring
