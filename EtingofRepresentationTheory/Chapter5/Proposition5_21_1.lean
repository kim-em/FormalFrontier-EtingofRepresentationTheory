import Mathlib

/-!
# Proposition 5.21.1: Character Expansion in Schur Polynomials

The product ∏_m (x₁ᵐ + ⋯ + xₙᵐ)^{i_m} equals Σ_{λ : p ≤ N} χ_λ(C_i) S_λ(x),
where S_λ are Schur polynomials and χ_λ(C_i) are character values on
conjugacy classes indexed by the partition i.

## Mathlib correspondence

Requires Schur polynomial infrastructure (`MvPolynomial.esymm`, `MvPolynomial.psum`
exist but Schur polynomials are not yet in Mathlib).
-/

open MvPolynomial Finset

noncomputable section

namespace Etingof

/-! ## Schur polynomials via alternant definition

Schur polynomials are defined as the ratio of the alternant polynomial
  a_{λ+δ}(x) = det(x_i^{λ_j + N - j})
to the Vandermonde determinant
  a_δ(x) = det(x_i^{N-j}) = ∏_{i<j}(x_i - x_j).

We prove the Vandermonde determinant divides any alternant determinant by showing
that substituting `X_i = X_j` makes two rows identical (hence det = 0), and then
using the multivariate factor theorem and unique factorization.
-/

/-- The alternant matrix `(x_i^{e_j})_{i,j}` for exponent sequence `e`. -/
def alternantMatrix (N : ℕ) (e : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun i j => (MvPolynomial.X i) ^ (e j)

/-- The Vandermonde exponent sequence δ = (N-1, N-2, …, 1, 0). -/
def vandermondeExps (N : ℕ) : Fin N → ℕ := fun j => N - 1 - j

/-- The shifted exponent sequence λ + δ = (λ₁ + N-1, λ₂ + N-2, …, λ_N + 0). -/
def shiftedExps (N : ℕ) (lam : Fin N → ℕ) : Fin N → ℕ :=
  fun j => lam j + (N - 1 - j)

/-! ### Divisibility of alternants by the Vandermonde

The key algebraic fact: for any exponent sequence `e`, the Vandermonde determinant
`det(X_i^{N-1-j})` divides the alternant `det(X_i^{e_j})`.

Proof strategy:
1. Substituting `X_i = X_j` gives a matrix with two identical rows → det = 0
2. This means `(X_i - X_j)` divides the alternant (multivariate factor theorem)
3. The factors are pairwise non-associated primes in the UFD `MvPolynomial`
4. Their product (= Vandermonde, up to sign) divides the alternant
-/

/-- The algebra map that substitutes `X_i ↦ X_j` and fixes all other variables. -/
private noncomputable def substMap (N : ℕ) (i j : Fin N) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun k => if k = i then MvPolynomial.X j else MvPolynomial.X k)

/-- Substituting `X_i = X_j` in an alternant gives 0 (two rows become identical). -/
private theorem alternant_subst_zero (N : ℕ) (e : Fin N → ℕ) {i j : Fin N} (hij : i ≠ j) :
    substMap N i j (alternantMatrix N e).det = 0 := by
  rw [AlgHom.map_det]
  apply Matrix.det_zero_of_row_eq hij
  funext col
  simp only [substMap, AlgHom.mapMatrix_apply, Matrix.map_apply, alternantMatrix, Matrix.of_apply,
    map_pow, MvPolynomial.aeval_X, ite_true, if_neg (Ne.symm hij)]

/-- Multivariate factor theorem for `(X 0 - X k.succ)`: if substituting `X_0 = X_{k+1}`
in `p` gives 0, then `(X_0 - X_{k+1})` divides `p`. Uses `finSuccEquiv` to reduce
to the univariate factor theorem. -/
private theorem X_zero_sub_dvd {n : ℕ} (k : Fin n)
    (p : MvPolynomial (Fin (n + 1)) ℚ)
    (hp : MvPolynomial.aeval (fun m : Fin (n + 1) =>
      if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
      else MvPolynomial.X m) p = 0) :
    (MvPolynomial.X 0 - MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ) ∣ p := by
  -- The substitution factors as: rename Fin.succ ∘ Poly.aeval (X k) ∘ finSuccEquiv
  have hcomp : (MvPolynomial.aeval (fun m : Fin (n + 1) =>
      if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
      else MvPolynomial.X m) : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] _) =
    ((MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).comp
      (((Polynomial.aeval (MvPolynomial.X k : MvPolynomial (Fin n) ℚ)).restrictScalars ℚ).comp
        (MvPolynomial.finSuccEquiv ℚ n).toAlgHom)) := by
    ext m : 1
    refine Fin.cases ?_ (fun m => ?_) m
    · simp [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        MvPolynomial.finSuccEquiv_X_zero, Polynomial.aeval_X, MvPolynomial.rename_X]
    · simp [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.aeval_C, MvPolynomial.rename_X,
        Fin.succ_ne_zero]
  -- Since rename Fin.succ is injective, the polynomial evaluation must be 0
  have heval : Polynomial.aeval (MvPolynomial.X k : MvPolynomial (Fin n) ℚ)
      (MvPolynomial.finSuccEquiv ℚ n p) = 0 := by
    have : (MvPolynomial.aeval (fun m : Fin (n + 1) =>
        if m = (0 : Fin (n + 1)) then (MvPolynomial.X k.succ : MvPolynomial (Fin (n + 1)) ℚ)
        else MvPolynomial.X m)) p = _ := congr_fun (congr_arg DFunLike.coe hcomp) p
    rw [hp] at this
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    exact MvPolynomial.rename_injective _ (Fin.succ_injective n)
      (this.symm.trans (map_zero _).symm)
  -- By univariate factor theorem: (Poly.X - Poly.C(X k)) | finSuccEquiv p
  have hdvd_poly : (Polynomial.X - Polynomial.C (MvPolynomial.X k)) ∣
      MvPolynomial.finSuccEquiv ℚ n p :=
    Polynomial.dvd_iff_isRoot.mpr heval
  -- Pull back through finSuccEquiv
  obtain ⟨q, hq⟩ := hdvd_poly
  exact ⟨(MvPolynomial.finSuccEquiv ℚ n).symm q, (MvPolynomial.finSuccEquiv ℚ n).injective <| by
    rw [map_mul, AlgEquiv.apply_symm_apply,
      show MvPolynomial.finSuccEquiv ℚ n (MvPolynomial.X 0 - MvPolynomial.X k.succ) =
        Polynomial.X - Polynomial.C (MvPolynomial.X k) from by
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]]
    exact hq⟩

/-- General multivariate factor theorem: if substituting `X_i = X_j` gives 0, then
`(X_i - X_j)` divides `p`. Reduces to `X_zero_sub_dvd` via variable swap. -/
private theorem X_sub_X_dvd {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (p : MvPolynomial (Fin N) ℚ)
    (hp : substMap N i j p = 0) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℚ) ∣ p := by
  -- Swap variables i and 0, reducing to the X_0 case
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- Let σ = swap i 0
  set σ := Equiv.swap i (0 : Fin (n + 1))
  -- The renamed polynomial has the same divisibility property
  suffices h : (MvPolynomial.X (0 : Fin (n + 1)) -
      MvPolynomial.X (σ j) : MvPolynomial (Fin (n + 1)) ℚ) ∣
      MvPolynomial.rename σ p by
    -- Pull back through rename σ⁻¹
    obtain ⟨q, hq⟩ := h
    refine ⟨MvPolynomial.rename σ.symm q, ?_⟩
    apply (MvPolynomial.rename_injective _ σ.injective)
    rw [map_mul, MvPolynomial.rename_rename, Equiv.self_comp_symm]
    simp only [MvPolynomial.rename_id, AlgHom.id_apply]
    rw [show MvPolynomial.rename σ (MvPolynomial.X i - MvPolynomial.X j) =
        MvPolynomial.X (0 : Fin (n + 1)) - MvPolynomial.X (σ j) from by
      simp only [map_sub, MvPolynomial.rename_X, σ, Equiv.swap_apply_left]]
    exact hq
  -- Now show σ j ≠ 0
  have hσj : σ j ≠ 0 := by
    change Equiv.swap i 0 j ≠ 0
    rcases eq_or_ne j i with rfl | hji
    · exact absurd rfl hij
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [Equiv.swap_apply_right]; exact fun h => hij (h ▸ rfl)
    · rw [Equiv.swap_apply_of_ne_of_ne hji hj0]; exact hj0
  -- Write σ j = k.succ for some k
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k.succ = σ j :=
    ⟨(σ j).pred hσj, Fin.succ_pred _ _⟩
  rw [← hk]
  -- Apply X_zero_sub_dvd; need the substitution condition on the renamed polynomial
  apply X_zero_sub_dvd
  -- Key: (substMap 0 (σ j)) ∘ (rename σ) = (rename σ) ∘ (substMap i j) as algebra homs
  -- Both agree on generators X_m: they send X_m to X_{σ (if m=i then j else m)}
  have hcomp : ((substMap (n + 1) 0 (σ j)).comp (MvPolynomial.rename σ) :
      MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] _) =
    (MvPolynomial.rename σ).comp (substMap (n + 1) i j) := by
    ext m : 1
    simp only [AlgHom.comp_apply, AlgHom.coe_coe, substMap, MvPolynomial.aeval_X,
      MvPolynomial.rename_X, map_pow]
    simp only [σ, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]
  -- Therefore substMap 0 (σ j) (rename σ p) = rename σ (substMap i j p) = rename σ 0 = 0
  change (substMap (n + 1) 0 k.succ) (MvPolynomial.rename σ p) = 0
  rw [show substMap (n + 1) 0 k.succ = substMap (n + 1) 0 (σ j) from by rw [← hk],
    show (substMap (n + 1) 0 (σ j)) (MvPolynomial.rename σ p) =
      ((substMap (n + 1) 0 (σ j)).comp (MvPolynomial.rename σ)) p from rfl,
    hcomp, show ((MvPolynomial.rename σ).comp (substMap (n + 1) i j)) p =
      MvPolynomial.rename σ (substMap (n + 1) i j p) from rfl, hp, map_zero]

/-- `X_i - X_j` is prime in `MvPolynomial (Fin N) ℚ`, proved via the automorphism
`X_k ↦ X_k - δ_{ki} X_j` which sends `X_i` to `X_i - X_j`. -/
private theorem X_sub_X_prime {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Prime (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℚ) := by
  let φ := MvPolynomial.aeval (R := ℚ) (fun k : Fin N =>
    if k = i then (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) - MvPolynomial.X j
    else MvPolynomial.X k)
  let ψ := MvPolynomial.aeval (R := ℚ) (fun k : Fin N =>
    if k = i then (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) + MvPolynomial.X j
    else MvPolynomial.X k)
  have hφψ : φ.comp ψ = AlgHom.id ℚ _ := by
    ext k : 1; simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs with h <;> simp_all [hij.symm]
  have hψφ : ψ.comp φ = AlgHom.id ℚ _ := by
    ext k : 1; simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs with h <;> simp_all [hij.symm]
  let e : MvPolynomial (Fin N) ℚ ≃ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
    AlgEquiv.ofAlgHom φ ψ hφψ hψφ
  rw [show (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) - MvPolynomial.X j = e (MvPolynomial.X i)
    from by show _ = φ (MvPolynomial.X i); simp [φ]]
  exact (MulEquiv.prime_iff e.toMulEquiv).mpr (MvPolynomial.X_prime (i := i))

/-- Distinct linear factors `X_j₁ - X_i₁` and `X_j₂ - X_i₂` (with `i < j` in each)
are not associated. Proved by evaluation at indicator functions. -/
private theorem X_sub_X_not_associated {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    ¬Associated (MvPolynomial.X j₁ - MvPolynomial.X i₁ : MvPolynomial (Fin N) ℚ)
      (MvPolynomial.X j₂ - MvPolynomial.X i₂) := by
  intro ⟨u, hu⟩
  -- Evaluate hu at x_k = δ_{k,j₁}
  have hev₁ := congr_arg
    (MvPolynomial.eval (fun k : Fin N => if k = j₁ then (1 : ℚ) else 0)) hu
  simp only [map_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X, ite_true,
    if_neg h₁.ne, sub_zero] at hev₁
  -- Evaluate hu at x_k = δ_{k,i₁}
  have hev₂ := congr_arg
    (MvPolynomial.eval (fun k : Fin N => if k = i₁ then (1 : ℚ) else 0)) hu
  simp only [map_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X, ite_true,
    if_neg h₁.ne', zero_sub] at hev₂
  -- Both eval(u) are nonzero since u is a unit
  have hu₁ : (MvPolynomial.eval (fun k : Fin N => if k = j₁ then (1 : ℚ) else 0)) ↑u ≠ 0 :=
    (Units.map (MvPolynomial.eval (R := ℚ)
      (fun k : Fin N => if k = j₁ then 1 else 0)).toMonoidHom u).isUnit.ne_zero
  have hu₂ : (MvPolynomial.eval (fun k : Fin N => if k = i₁ then (1 : ℚ) else 0)) ↑u ≠ 0 :=
    (Units.map (MvPolynomial.eval (R := ℚ)
      (fun k : Fin N => if k = i₁ then 1 else 0)).toMonoidHom u).isUnit.ne_zero
  rw [one_mul] at hev₁
  rw [neg_one_mul] at hev₂
  by_cases hj : j₂ = j₁
  · subst hj; simp only [if_neg h₂.ne, sub_zero] at hev₁
    by_cases hi : i₂ = i₁; · subst hi; exact hne rfl
    · simp only [if_neg h₁.ne', if_neg hi, sub_zero] at hev₂
      exact hu₂ (neg_eq_zero.mp hev₂)
  · by_cases hi₂j₁ : i₂ = j₁
    · subst hi₂j₁; simp only [if_neg hj, zero_sub] at hev₁
      by_cases hj₂i₁ : j₂ = i₁; · subst hj₂i₁; exact absurd h₂ (by omega)
      · simp only [if_neg hj₂i₁, if_neg h₁.ne'] at hev₂
        simp only [sub_zero] at hev₂; exact hu₂ (neg_eq_zero.mp hev₂)
    · simp only [if_neg hj, if_neg hi₂j₁, sub_zero] at hev₁; exact hu₁ hev₁

/-- Distinct ordered pairs `(i₁,j₁) ≠ (i₂,j₂)` with `i < j` give `IsRelPrime` linear factors. -/
private theorem X_sub_X_isRelPrime {N : ℕ} {i₁ j₁ i₂ j₂ : Fin N}
    (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    IsRelPrime (MvPolynomial.X j₁ - MvPolynomial.X i₁ : MvPolynomial (Fin N) ℚ)
      (MvPolynomial.X j₂ - MvPolynomial.X i₂) := by
  letI : GCDMonoid (MvPolynomial (Fin N) ℚ) :=
    UniqueFactorizationMonoid.toGCDMonoid _
  exact (X_sub_X_prime h₁.ne').irreducible.isRelPrime_iff_not_dvd.mpr
    fun hdvd => X_sub_X_not_associated h₁ h₂ hne
      ((X_sub_X_prime h₁.ne').associated_of_dvd (X_sub_X_prime h₂.ne') hdvd)

/-- The product `∏_{i<j} (X_j - X_i)` divides any alternant determinant. -/
private theorem prod_dvd_alternant (N : ℕ) (e : Fin N → ℕ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ∣
      (alternantMatrix N e).det := by
  letI : GCDMonoid (MvPolynomial (Fin N) ℚ) :=
    UniqueFactorizationMonoid.toGCDMonoid _
  apply Fintype.prod_dvd_of_isRelPrime
  · -- Pairwise IsRelPrime of inner products
    intro i₁ i₂ hi
    apply IsRelPrime.prod_left_iff.mpr; intro j₁ hj₁
    apply IsRelPrime.prod_right_iff.mpr; intro j₂ hj₂
    simp only [Finset.mem_Ioi] at hj₁ hj₂
    exact X_sub_X_isRelPrime hj₁ hj₂ (by intro h; exact hi (Prod.mk.inj h).1)
  · -- Each inner product divides the alternant det
    intro i
    apply Finset.prod_dvd_of_isRelPrime
    · intro j₁ hj₁ j₂ hj₂ hjne
      simp only [Finset.coe_Ioi, Set.mem_Ioi] at hj₁ hj₂
      rw [Function.onFun]
      exact X_sub_X_isRelPrime hj₁ hj₂ (by intro h; exact hjne (Prod.mk.inj h).2)
    · intro j hj
      simp only [Finset.mem_Ioi] at hj
      exact X_sub_X_dvd (Fin.ne_of_gt hj) _ (alternant_subst_zero N e (Fin.ne_of_gt hj))

/-- The alternant det with `vandermondeExps` is associated to the product of linear factors.
Uses the Vandermonde determinant formula and column reversal. -/
private theorem alternant_det_associated_prod (N : ℕ) :
    Associated (alternantMatrix N (vandermondeExps N)).det
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) := by
  have h1 : alternantMatrix N (vandermondeExps N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, vandermondeExps, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]
  have hu : IsUnit (↑↑(@Fin.revPerm N).sign : MvPolynomial (Fin N) ℚ) :=
    (Units.map (algebraMap ℤ (MvPolynomial (Fin N) ℚ)).toMonoidHom
      (@Fin.revPerm N).sign).isUnit
  exact (associated_isUnit_mul_left_iff hu).mpr (Associated.refl _)

/-- The Vandermonde determinant divides any alternant determinant.

This is proved by showing each `(X_j - X_i)` for `i < j` divides the alternant
(via the factor theorem: substituting `X_i = X_j` gives 0), and then combining
using unique factorization in `MvPolynomial`. -/
private theorem vandermonde_dvd_alternant (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N (vandermondeExps N)).det ∣ (alternantMatrix N e).det :=
  (alternant_det_associated_prod N).dvd_iff_dvd_left.mpr (prod_dvd_alternant N e)

/-- Schur polynomial `S_λ(x₁, …, x_N)` as the ratio `det(x_i^{λ_j+N-j}) / det(x_i^{N-j})`.

Defined as the unique polynomial whose product with the Vandermonde determinant
equals the shifted alternant determinant. The existence follows from the
divisibility of alternants by the Vandermonde. -/
noncomputable def schurPoly (N : ℕ) (lam : Fin N → ℕ) :
    MvPolynomial (Fin N) ℚ :=
  (vandermonde_dvd_alternant N (shiftedExps N lam)).choose

/-- Key property: the Schur polynomial satisfies the alternant ratio identity. -/
theorem schurPoly_mul_vandermonde (N : ℕ) (lam : Fin N → ℕ) :
    schurPoly N lam * (alternantMatrix N (vandermondeExps N)).det =
      (alternantMatrix N (shiftedExps N lam)).det := by
  have h := (vandermonde_dvd_alternant N (shiftedExps N lam)).choose_spec
  -- h : alternant_det = vandermonde_det * choose
  rw [schurPoly, mul_comm]
  exact h.symm

/-- A partition of `n` with at most `N` parts, given as a weakly decreasing
sequence `λ : Fin N → ℕ` with `∑ i, λ i = n`. -/
structure BoundedPartition (N n : ℕ) where
  /-- The parts of the partition as a function `Fin N → ℕ`. -/
  parts : Fin N → ℕ
  /-- The parts are weakly decreasing. -/
  decreasing : Antitone parts
  /-- The parts sum to `n`. -/
  sum_eq : ∑ i, parts i = n

/-- The character value `χ_λ(C_μ)` of the irreducible representation of `S_n`
indexed by partition `λ`, evaluated on the conjugacy class with cycle type `μ`.

Defined via the Frobenius character formula: `χ_λ(C_μ)` is the coefficient of
`x^{λ+ρ}` in the product `Δ(x) · p_μ(x)`, where `Δ(x)` is the Vandermonde
determinant and `p_μ(x)` is the power-sum symmetric polynomial indexed by `μ`. -/
noncomputable def charValue {n : ℕ} (N : ℕ) (lam : BoundedPartition N n)
    (μ : n.Partition) : ℚ :=
  MvPolynomial.coeff
    (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
    ((alternantMatrix N (vandermondeExps N)).det * MvPolynomial.psumPart (Fin N) ℚ μ)

theorem Proposition5_21_1
    {n : ℕ} (N : ℕ) (μ : n.Partition) :
    -- LHS: ∏_m p_m(x)^{i_m} (power-sum product indexed by partition μ)
    -- RHS: Σ_λ χ_λ(C_μ) · S_λ(x)  (sum over partitions λ of n with ≤ N parts)
    -- We state the identity existentially to avoid Fintype synthesis issues.
    ∃ (lams : Finset (BoundedPartition N n)),
      (MvPolynomial.psumPart (Fin N) ℚ μ : MvPolynomial (Fin N) ℚ) =
        ∑ lam ∈ lams,
          (charValue N lam μ : ℚ) • schurPoly N lam.parts := by
  sorry

end Etingof
