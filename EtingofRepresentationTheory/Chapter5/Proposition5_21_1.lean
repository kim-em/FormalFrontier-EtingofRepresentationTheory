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

/-! ## Infrastructure for the Frobenius character formula -/

/-- DecidableEq for BoundedPartition: two bounded partitions are equal iff their parts agree. -/
instance boundedPartition_decEq {N n : ℕ} : DecidableEq (BoundedPartition N n) :=
  fun a b => decidable_of_iff (a.parts = b.parts) ⟨
    fun h => by cases a; cases b; simp_all,
    fun h => by subst h; rfl⟩

/-- BoundedPartition N n is finite: each part is ≤ n, so we inject into Fin N → Fin (n+1). -/
noncomputable instance boundedPartition_fintype {N n : ℕ} :
    Fintype (BoundedPartition N n) := by
  classical
  exact Fintype.ofInjective
    (fun p : BoundedPartition N n => fun i =>
      (⟨p.parts i, Nat.lt_succ_of_le (le_trans
        (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
        (le_of_eq p.sum_eq))⟩ : Fin (n + 1)))
    (fun a b h => by
      cases a; cases b; simp only [BoundedPartition.mk.injEq]
      funext i; exact congrArg Fin.val (congrFun h i))

/-- The alternant determinant is antisymmetric: `rename σ (det M) = sgn(σ) • det M`.
This is the key algebraic fact underlying the Frobenius character formula. -/
theorem rename_alternant_det {N : ℕ} (e : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) :
    (MvPolynomial.rename σ) (alternantMatrix N e).det =
      Equiv.Perm.sign σ • (alternantMatrix N e).det := by
  rw [AlgHom.map_det]
  have hmat : (MvPolynomial.rename σ).mapMatrix (alternantMatrix N e) =
      (alternantMatrix N e).submatrix σ id := by
    apply Matrix.ext; intro i j
    change (MvPolynomial.rename σ) ((alternantMatrix N e) i j) =
      (alternantMatrix N e) (σ i) j
    simp [alternantMatrix, Matrix.of_apply, map_pow, MvPolynomial.rename_X]
  rw [hmat, Matrix.det_permute]
  simp [Units.smul_def]

/-! ## Helper lemmas for the antisymmetric basis decomposition -/

/-- A strictly monotone permutation of `Fin N` must be the identity. -/
lemma perm_eq_one_of_strictMono {N : ℕ} {σ : Equiv.Perm (Fin N)}
    (h : StrictMono (⇑σ : Fin N → Fin N)) : σ = 1 := by
  rcases N with _ | n
  · exact Subsingleton.elim _ _
  · have hle : ∀ j : Fin (n + 1), j ≤ σ j := by
      intro j; induction j using Fin.inductionOn with
      | zero => exact Fin.zero_le _
      | succ k ih =>
          apply Fin.le_def.mpr
          have h1 : (σ k.castSucc).val < (σ k.succ).val :=
            Fin.lt_def.mp (h (by simp [Fin.lt_def]))
          have h2 := Fin.le_def.mp ih
          have h3 : k.succ.val = k.castSucc.val + 1 := rfl
          omega
    by_contra hne
    obtain ⟨i, hi⟩ := not_forall.mp
      (mt (fun heq => Equiv.ext (fun j => Eq.symm (heq j))) hne)
    linarith [Finset.sum_lt_sum (g := fun j => (σ j : ℕ)) (fun j _ => hle j)
      ⟨i, Finset.mem_univ _, Fin.lt_def.mp (lt_of_le_of_ne (hle i) hi)⟩,
      Fintype.sum_equiv σ (fun j => ((σ j) : ℕ)) (fun j => (j : ℕ)) (fun _ => rfl)]

/-- A product of `X_i ^ f_i` equals the corresponding monomial. -/
lemma prod_X_pow_eq_monomial' {N : ℕ} (f : Fin N → ℕ) :
    ∏ i : Fin N, (X i : MvPolynomial (Fin N) ℚ) ^ f i =
    monomial (Finsupp.equivFunOnFinite.symm f) 1 := by
  set s := Finsupp.equivFunOnFinite.symm f
  rw [show ∏ i : Fin N, (X i : MvPolynomial (Fin N) ℚ) ^ f i = ∏ i, X i ^ s i from rfl,
    ← MvPolynomial.prod_X_pow_eq_monomial]; symm
  exact Finset.prod_subset (Finset.subset_univ _)
    fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

/-- Power-sum symmetric polynomials are symmetric. -/
theorem psumPart_isSymmetric {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ).IsSymmetric := by
  unfold MvPolynomial.psumPart
  induction μ.parts using Multiset.induction with
  | empty => exact MvPolynomial.IsSymmetric.one
  | cons a s ih => rw [Multiset.map_cons, Multiset.prod_cons]
                   exact (MvPolynomial.psum_isSymmetric _ ℚ a).mul ih

/-- Antisymmetric polynomial has zero coefficient at multi-indices with repeated entries. -/
theorem coeff_zero_of_antisym_repeated {N : ℕ}
    (p : MvPolynomial (Fin N) ℚ)
    (hp : ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ p = Equiv.Perm.sign σ • p)
    (d : (Fin N) →₀ ℕ) {i j : Fin N} (hij : i ≠ j) (hd : d i = d j) :
    MvPolynomial.coeff d p = 0 := by
  have h1 := hp (Equiv.swap i j); rw [Equiv.Perm.sign_swap hij] at h1
  have h3 := MvPolynomial.coeff_rename_mapDomain (⇑(Equiv.swap i j))
    (Equiv.swap i j).injective p d
  rw [show Finsupp.mapDomain (⇑(Equiv.swap i j)) d = d from by
    have hsymm : (Equiv.swap i j).symm = Equiv.swap i j := Equiv.symm_swap i j
    ext k; rw [Finsupp.mapDomain_equiv_apply, hsymm, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact hd.symm
    · subst h2; exact hd
    · rfl,
    h1] at h3
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul,
    MvPolynomial.coeff_neg] at h3; linarith

/-- The shifted exponent sequence is strictly anti-monotone. -/
theorem shiftedExps_strictAnti {N n : ℕ} (lam : BoundedPartition N n) :
    StrictAnti (shiftedExps N lam.parts) := by
  intro i j hij; simp only [shiftedExps]; have := lam.decreasing (le_of_lt hij); omega

/-- Kronecker delta property: `coeff_{e'}(D_e) = δ_{e,e'}` for strictly anti exponents. -/
theorem alternant_coeff_kronecker {N : ℕ}
    {e e' : Fin N → ℕ} (he : StrictAnti e) (he' : StrictAnti e') :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e') (alternantMatrix N e).det =
    if e = e' then 1 else 0 := by
  rw [Matrix.det_apply]; simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  simp_rw [show ∀ σ : Equiv.Perm (Fin N), ∏ j, alternantMatrix N e (σ j) j =
      monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) 1 from fun σ => by
    rw [show ∏ j, alternantMatrix N e (σ j) j = ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j
      from rfl, show ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j =
        ∏ i, X i ^ (e (σ.symm i)) from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial' _]
  simp only [MvPolynomial.coeff_monomial]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm) = Finsupp.equivFunOnFinite.symm e') ↔
      (e ∘ ⇑σ.symm = e') := fun σ => Finsupp.equivFunOnFinite.symm.injective.eq_iff
  have unique : ∀ σ : Equiv.Perm (Fin N), e ∘ ⇑σ.symm = e' → e = e' ∧ σ = 1 := by
    intro σ h
    have hmono : StrictMono (⇑σ.symm : Fin N → Fin N) := by
      intro a b hab
      have hgt := (congr_fun h a) ▸ (congr_fun h b) ▸ he' hab
      by_contra h_not_lt; push_neg at h_not_lt
      rcases h_not_lt.eq_or_lt with heq | hlt
      · exact absurd hgt (not_lt.mpr (le_of_eq (congr_arg e heq.symm)))
      · exact absurd hgt (not_lt.mpr (le_of_lt (he hlt)))
    exact ⟨by rw [← h]; simp [show σ.symm = 1 from perm_eq_one_of_strictMono hmono],
           by rw [← σ.symm_symm, perm_eq_one_of_strictMono hmono]; simp⟩
  split_ifs with heq
  · rw [Finset.sum_eq_single 1]; · simp [heq]
    · intro σ _ hne; simp only [key]; split_ifs with h
      · exact absurd (unique σ h).2 hne
      · exact smul_zero _
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun σ _ => by
      simp only [key]; split_ifs with h
      · exact absurd (unique σ h).1 heq
      · exact smul_zero _

/-- An antisymmetric polynomial whose coefficients at all strictly anti multi-indices
are zero must be the zero polynomial. -/
theorem antisym_eq_zero {N : ℕ} (p : MvPolynomial (Fin N) ℚ)
    (hp : ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ p = Equiv.Perm.sign σ • p)
    (hc : ∀ e : Fin N → ℕ, StrictAnti e →
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) p = 0) :
    p = 0 := by
  ext d; simp only [MvPolynomial.coeff_zero]
  set f := Finsupp.equivFunOnFinite d
  by_cases hinj : Function.Injective f
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin N), StrictAnti (f ∘ ⇑σ) :=
      ⟨Tuple.sort (OrderDual.toDual ∘ f), fun a b hab =>
        (Tuple.monotone_sort _).strictMono_of_injective
          (OrderDual.toDual.injective.comp hinj |>.comp (Tuple.sort _).injective) hab⟩
    have h1 := MvPolynomial.coeff_rename_mapDomain (⇑σ.symm) σ.symm.injective p d
    rw [show Finsupp.mapDomain (⇑σ.symm) d = Finsupp.equivFunOnFinite.symm (f ∘ ⇑σ) from by
      ext i; simp [Finsupp.mapDomain_equiv_apply, f, Finsupp.equivFunOnFinite], hp σ.symm] at h1
    rw [show MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (f ∘ ⇑σ))
          (Equiv.Perm.sign σ.symm • p) = 0 from by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h, hc _ hσ]] at h1
    exact h1.symm
  · simp only [Function.Injective] at hinj; push_neg at hinj
    obtain ⟨i, j, hij_val, hij_ne⟩ := hinj
    exact coeff_zero_of_antisym_repeated p hp d hij_ne hij_val

/-- For StrictAnti `e`, the entry `e j` is at least `N - 1 - j`. -/
theorem strictAnti_ge_rev {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e) (j : Fin N) :
    N - 1 - (j : ℕ) ≤ e j := by
  suffices ∀ m : ℕ, ∀ j : Fin N, m = N - 1 - (j : ℕ) → m ≤ e j by exact this _ j rfl
  intro m; induction m with
  | zero => intro j _; omega
  | succ m ih =>
    intro j hj; have hj1 : (j : ℕ) + 1 < N := by omega
    have := ih ⟨(j : ℕ) + 1, hj1⟩ (by simp; omega)
    have := he (show j < (⟨(j : ℕ) + 1, hj1⟩ : Fin N) from by simp [Fin.lt_def]); omega

/-- For StrictAnti `e`, the gap between entries is at least the index gap. -/
private theorem strictAnti_gap {N : ℕ} {e : Fin N → ℕ} (he : StrictAnti e)
    {i j : Fin N} (hij : i ≤ j) : e j + ((j : ℕ) - (i : ℕ)) ≤ e i := by
  suffices ∀ d : ℕ, ∀ i j : Fin N, d = (j : ℕ) - (i : ℕ) → i ≤ j → e j + d ≤ e i by
    exact this _ i j rfl hij
  intro d; induction d with
  | zero => intro i j hd hij; have : i = j := Fin.ext (by omega); subst this; omega
  | succ d ih =>
    intro i j hd hij; let j' : Fin N := ⟨(j : ℕ) - 1, by omega⟩
    have := ih i j' (by simp [j']; omega) (by simp [j', Fin.le_iff_val_le_val]; omega)
    have := he (show j' < j from by simp [j', Fin.lt_def]; omega); omega

/-- The alternant determinant is homogeneous of degree `∑ e_j`. -/
theorem alternant_isHomogeneous {N : ℕ} (e : Fin N → ℕ) :
    (alternantMatrix N e).det.IsHomogeneous (∑ j : Fin N, e j) := by
  rw [Matrix.det_apply, show ∑ j : Fin N, e j = ∑ j : Fin N, 1 * e j by simp]
  apply MvPolynomial.IsHomogeneous.sum; intro σ _ d hd
  rw [MvPolynomial.coeff_smul] at hd
  exact (MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ =>
    (MvPolynomial.isHomogeneous_X ℚ (σ j)).pow (e j))) (right_ne_zero_of_mul hd)

/-- Power-sum symmetric polynomials are homogeneous of degree `n`. -/
theorem psumPart_isHomogeneous {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ).IsHomogeneous n := by
  unfold MvPolynomial.psumPart
  suffices h : (Multiset.map (psum (Fin N) ℚ) μ.parts).prod.IsHomogeneous μ.parts.sum by
    rwa [μ.parts_sum] at h
  induction μ.parts using Multiset.induction with
  | empty => simpa using MvPolynomial.isHomogeneous_one (Fin N) ℚ
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact ((show (∑ i : Fin N, X i ^ a).IsHomogeneous a from by
      apply IsHomogeneous.sum; intro i _
      convert (MvPolynomial.isHomogeneous_X ℚ i).pow a using 1; ring)).mul ih

/-- If `e` is StrictAnti with the right sum, it comes from a BoundedPartition. -/
theorem exists_bp_of_strictAnti_sum {N n : ℕ}
    (e : Fin N → ℕ) (he : StrictAnti e)
    (hsum : ∑ j : Fin N, e j = (∑ j : Fin N, vandermondeExps N j) + n) :
    ∃ lam : BoundedPartition N n, shiftedExps N lam.parts = e := by
  set parts : Fin N → ℕ := fun j => e j - (N - 1 - ↑j)
  have hge := strictAnti_ge_rev he
  refine ⟨⟨parts, ?_, ?_⟩, ?_⟩
  · intro i j hij; simp only [parts]; have := strictAnti_gap he hij; omega
  · have h1 : ∑ i : Fin N, (parts i + (N - 1 - ↑i)) = ∑ i : Fin N, e i :=
      Finset.sum_congr rfl fun j _ => by simp only [parts]; exact Nat.sub_add_cancel (hge j)
    rw [Finset.sum_add_distrib] at h1
    simp only [vandermondeExps] at hsum; omega
  · funext j; simp only [shiftedExps, parts]; exact Nat.sub_add_cancel (hge j)

/-- **Frobenius character formula (universe form).** Stronger version of
`Proposition5_21_1` where the indexing finset is `Finset.univ`: every
power-sum partition expands as a sum over *all* bounded partitions, with
coefficients given by `charValue`. -/
theorem Proposition5_21_1_univ
    {n : ℕ} (N : ℕ) (μ : n.Partition) :
    (MvPolynomial.psumPart (Fin N) ℚ μ : MvPolynomial (Fin N) ℚ) =
      ∑ lam : BoundedPartition N n,
        (charValue N lam μ : ℚ) • schurPoly N lam.parts := by
  -- Step 1: Cancel the Vandermonde determinant Δ from both sides (integral domain)
  have hΔ : (alternantMatrix N (vandermondeExps N)).det ≠ 0 := by
    obtain ⟨u, hu⟩ := alternant_det_associated_prod N
    intro h
    have hprod : ∏ i : Fin N, ∏ j ∈ Ioi i,
        (X j - X i : MvPolynomial (Fin N) ℚ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j hj =>
          (X_sub_X_prime (mem_Ioi.mp hj).ne').ne_zero
    exact hprod (by rw [← hu, h, zero_mul])
  apply mul_left_cancel₀ hΔ
  -- Step 2: Rewrite RHS: Δ * Σ c_λ • S_λ = Σ c_λ • (S_λ * Δ) = Σ c_λ • D_λ
  rw [Finset.mul_sum]
  simp_rw [Algebra.mul_smul_comm,
    mul_comm (alternantMatrix N (vandermondeExps N)).det (schurPoly _ _),
    schurPoly_mul_vandermonde]
  -- Step 3: Antisymmetric basis decomposition
  -- Goal: Δ * p_μ = Σ_λ coeff_{λ+ρ}(Δ * p_μ) • D_λ
  simp only [charValue]
  rw [← sub_eq_zero]
  apply antisym_eq_zero
  · -- Antisymmetry of the difference
    intro σ; rw [map_sub, smul_sub]; congr 1
    · rw [map_mul, rename_alternant_det, (psumPart_isSymmetric N μ) σ, smul_mul_assoc]
    · -- rename σ (∑ c • D) = sign σ • ∑ c • D
      trans ∑ lam : BoundedPartition N n, Equiv.Perm.sign σ •
        (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
          ((alternantMatrix N (vandermondeExps N)).det * psumPart (Fin N) ℚ μ) •
         (alternantMatrix N (shiftedExps N lam.parts)).det)
      · rw [map_sum]; apply Finset.sum_congr rfl; intro lam _
        rw [AlgHom.map_smul_of_tower, rename_alternant_det, smul_comm]
      · exact (Finset.smul_sum ..).symm
  · -- Coefficient condition: for StrictAnti e, coeff_e(F - Σ c • D) = 0
    intro e he
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, sub_eq_zero]
    simp_rw [alternant_coeff_kronecker (shiftedExps_strictAnti _) he, mul_ite, mul_one, mul_zero]
    have hsub : ∀ lam : BoundedPartition N n,
        (if shiftedExps N lam.parts = e
         then MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
                ((alternantMatrix N (vandermondeExps N)).det * psumPart (Fin N) ℚ μ) else 0) =
        if shiftedExps N lam.parts = e
        then MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
              ((alternantMatrix N (vandermondeExps N)).det * psumPart (Fin N) ℚ μ) else 0 :=
      fun lam => by split_ifs with h <;> [rw [h]; rfl]
    simp_rw [hsub]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    set filt := Finset.univ.filter (fun lam : BoundedPartition N n =>
      shiftedExps N lam.parts = e)
    have hle : filt.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : a.parts = b.parts := by
        funext j; have := congr_fun (ha'.trans hb'.symm) j; simp [shiftedExps] at this; omega
      cases a; cases b; simp_all
    rcases Nat.eq_zero_or_pos filt.card with hcard | hcard
    · -- No matching partition → coeff_e(F) = 0 by homogeneity
      rw [hcard, zero_nsmul]; symm
      have hne : ∀ lam : BoundedPartition N n, shiftedExps N lam.parts ≠ e := by
        intro lam hlam
        have hmem : lam ∈ filt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlam⟩
        rw [Finset.card_eq_zero.mp hcard] at hmem
        exact absurd hmem (by simp)
      by_contra h
      have h' : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          ((alternantMatrix N (vandermondeExps N)).det * psumPart (Fin N) ℚ μ) ≠ 0 := by
        intro heq; exact h heq.symm
      have hF := (alternant_isHomogeneous (vandermondeExps N)).mul (psumPart_isHomogeneous N μ)
      have hd := hF h'
      have hweight : Finsupp.weight (1 : Fin N → ℕ) (Finsupp.equivFunOnFinite.symm e) =
          ∑ j : Fin N, e j := by
        simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      rw [hweight] at hd
      obtain ⟨lam, hlam⟩ := exists_bp_of_strictAnti_sum e he (by exact_mod_cast hd)
      exact hne lam hlam
    · -- Matching partition exists, card = 1
      have : filt.card = 1 := by omega
      rw [this, one_nsmul]

/-- **Proposition 5.21.1** (Etingof). Every power-sum partition decomposes
as a sum of Schur polynomials weighted by character values: there exists
a finset of bounded partitions over which the expansion holds.

This is the existential form; for the universe form (which fixes the
indexing finset to `Finset.univ`), see `Proposition5_21_1_univ`. -/
theorem Proposition5_21_1
    {n : ℕ} (N : ℕ) (μ : n.Partition) :
    ∃ (lams : Finset (BoundedPartition N n)),
      (MvPolynomial.psumPart (Fin N) ℚ μ : MvPolynomial (Fin N) ℚ) =
        ∑ lam ∈ lams,
          (charValue N lam μ : ℚ) • schurPoly N lam.parts :=
  ⟨Finset.univ, Proposition5_21_1_univ N μ⟩

end Etingof
