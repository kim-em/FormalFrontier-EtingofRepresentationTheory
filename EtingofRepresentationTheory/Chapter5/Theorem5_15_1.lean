import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_14_3
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2

/-!
# Theorem 5.15.1: Frobenius Character Formula for Specht Modules

The character of the Specht module V_λ evaluated at conjugacy class C_i is:

  χ_{V_λ}(C_i) = coefficient of x^{λ+ρ} in Δ(x) · ∏_{m≥1} p_m(x)^{i_m}

where ρ = (n-1, n-2, ..., 1, 0), Δ(x) = ∏_{i<j} (xⱼ - xᵢ) is the
Vandermonde determinant, and p_m are power sum symmetric polynomials.

## Formalization approach

The character of the Specht module V_λ is defined as the trace of left
multiplication by σ on V_λ ⊆ ℂ[S_n]. The Vandermonde polynomial and the
shift vector ρ are defined as multivariate polynomial / finsupp respectively.

The formula relates three objects:
1. The LHS: trace of the S_n-action on the Specht module (left ideal of ℂ[S_n])
2. The Vandermonde factor Δ(x), which accounts for the antisymmetrization in
   the Young symmetrizer
3. The power sum polynomial product from Theorem 5.14.3, shifted by ρ

## Proof structure

The proof follows Etingof's argument (Discussion after Theorem 5.15.1):

1. **Vandermonde expansion**: Δ(x) = Σ_{π ∈ S_n} sign(π) · x^{permuted ρ}
   This is the determinant expansion of the Vandermonde matrix.

2. **Coefficient extraction**: Multiplying the expansion by ∏ p_m^{i_m} and
   extracting x^{λ+ρ} gives an alternating sum of permutation module characters
   (via Theorem 5.14.3).

3. **Upper-triangularity**: Define θ_λ as the RHS. The book shows
   θ_λ = Σ_{μ ≥ λ} L_{μλ} χ_{V_μ} with L_{λλ} = 1, via decomposition of
   permutation modules U_μ = Σ_ν K_{νμ} V_ν (Kostka numbers).

4. **Induction on dominance order**: Since the Specht module characters {χ_{V_μ}}
   form a basis of class functions, upper-triangularity with L_{λλ} = 1 forces
   θ_λ = χ_{V_λ}.

## Mathlib correspondence

- `MvPolynomial.psum`: power sum symmetric polynomials p_m = Σᵢ xᵢᵐ
- `MvPolynomial.X`: polynomial variables
- `MvPolynomial.coeff`: coefficient extraction
- `LinearMap.trace`: trace of a linear endomorphism
- `Matrix.det_vandermonde`: det of Vandermonde matrix = ∏_{i<j} (v_j - v_i)
-/

namespace Etingof

/-- The Vandermonde polynomial Δ(x) = ∏_{i<j} (xⱼ - xᵢ) in n variables.
This is the polynomial form of the Vandermonde determinant. -/
noncomputable def vandermondePoly (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X j - MvPolynomial.X i)

/-- The shift vector ρ = (n-1, n-2, ..., 1, 0) used in the Frobenius character formula.
Component i equals n - 1 - i. -/
noncomputable def rhoShift (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => n - 1 - i.val)

/-- The left multiplication action of σ ∈ S_n on the Specht module V_λ.
Since V_λ is a left ideal of ℂ[S_n], left multiplication by `of σ` preserves it. -/
noncomputable def spechtModuleAction (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ↥(SpechtModule n la) →ₗ[ℂ] ↥(SpechtModule n la) where
  toFun := fun ⟨m, hm⟩ => ⟨MonoidAlgebra.of ℂ _ σ * m,
    (SpechtModule n la).smul_mem (MonoidAlgebra.of ℂ _ σ) hm⟩
  map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (mul_add _ a b)
  map_smul' := fun _ ⟨m, _⟩ => Subtype.ext (Algebra.mul_smul_comm _ _ m)

/-- The character of the Specht module V_λ at a permutation σ ∈ S_n, defined as the
trace of left multiplication by σ restricted to V_λ ⊆ ℂ[S_n]. -/
noncomputable def spechtModuleCharacter (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  LinearMap.trace ℂ _ (spechtModuleAction n la σ)

/-! ## Intermediate lemmas for the Frobenius character formula -/

noncomputable section

/-- The exponent vector from the Vandermonde determinant expansion for permutation π:
the monomial ∏_i X_{π(i)}^i has exponent (π⁻¹(j)).val at variable j.
Equivalently, permExponent n π = fun j ↦ (π⁻¹ j).val. -/
def permExponent (n : ℕ) (π : Equiv.Perm (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (π⁻¹ j).val)

/-- The Vandermonde polynomial expands as an alternating sum of monomials:
Δ(x) = Σ_{π ∈ S_n} sign(π) · x^{(π(0), π(1), ..., π(n-1))}.
This is the determinant expansion of the Vandermonde matrix det(xᵢ^j)_{i,j}.

Proof idea: vandermondePoly n = det(Matrix.vandermonde (MvPolynomial.X · )),
and the determinant expands as Σ_π sign(π) ∏_i X_i^{π(i)}. -/
theorem vandermondePoly_eq_sum_sign_monomial (n : ℕ) :
    vandermondePoly n =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • MvPolynomial.monomial (permExponent n π) (1 : ℂ) := by
  -- Step 1: vandermondePoly n = det(vandermonde(X))
  have hvand : vandermondePoly n =
      (Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))).det := by
    simp only [vandermondePoly, Matrix.det_vandermonde]
  rw [hvand, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  -- Goal: sign σ • ∏ i, (vandermonde X) (σ i) i = (↑(sign σ) : ℤ) • monomial ... 1
  congr 1
  simp only [Matrix.vandermonde_apply]
  -- Goal: ∏ i, X (σ i) ^ i.val = monomial (permExponent n σ) 1
  -- Reindex ∏_i X_{σ(i)}^i = ∏_j X_j^{(σ⁻¹ j).val}
  rw [Fintype.prod_equiv σ
    (fun i => MvPolynomial.X (σ i) ^ (i : ℕ))
    (fun j => MvPolynomial.X j ^ (permExponent n σ) j)
    (fun i => by simp [permExponent, Finsupp.equivFunOnFinite])]
  -- Goal: ∏ j, X j ^ (permExponent n σ) j = monomial (permExponent n σ) 1
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun i => by simp)]

/-- Coefficient of x^{α+e} in (monomial e c) · P equals c · coeff(x^α, P).
This is the shift property of polynomial multiplication by a monomial. -/
theorem coeff_monomial_mul_shift {n : ℕ} (e α : Fin n →₀ ℕ) (c : ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.coeff (α + e) (MvPolynomial.monomial e c * P) =
      c * MvPolynomial.coeff α P := by
  rw [mul_comm, MvPolynomial.coeff_mul_monomial]; ring

/-- The coefficient of x^{λ+ρ} in Δ·P equals an alternating sum of shifted coefficients.
This combines the Vandermonde expansion with the coefficient shift property. -/
theorem coeff_vandermonde_mul (n : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (vandermondePoly n * P) =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • (if _ : permExponent n π ≤ α
          then (MvPolynomial.coeff (α - permExponent n π) P : ℂ) else 0) := by
  -- Expand Vandermonde as alternating sum, distribute multiplication, extract coefficients
  rw [vandermondePoly_eq_sum_sign_monomial]
  simp only [Finset.sum_mul, smul_mul_assoc, MvPolynomial.coeff_sum]
  congr 1; ext π
  -- Goal: coeff α (sign π • (monomial ... 1 * P)) = sign π • (if ... then ... else 0)
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial_mul', one_mul]
  simp only [dite_eq_ite]

/-- The permutation module character χ_{U_μ} at σ as a natural number cast to ℂ,
extracted from Theorem 5.14.3. -/
theorem permModuleCharacter_eq_coeff (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n la σ : ℂ) =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypePsumProduct n σ) :=
  Theorem5_14_3 n la σ

/-! ### Symmetric polynomial infrastructure for the Frobenius formula -/

/-- Symmetric polynomials are closed under `pow`. -/
private theorem MvPolynomial.IsSymmetric.pow {σ : Type*} {R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P.IsSymmetric) (k : ℕ) : (P ^ k).IsSymmetric := by
  induction k with
  | zero => simp [MvPolynomial.IsSymmetric.one]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A multiset product of symmetric polynomials is symmetric. -/
private theorem multiset_prod_isSymmetric {σ : Type*} {R : Type*} [CommSemiring R]
    (s : Multiset (MvPolynomial σ R)) (hs : ∀ p ∈ s, MvPolynomial.IsSymmetric p) :
    (s.prod).IsSymmetric := by
  induction s using Multiset.induction with
  | empty => simp [MvPolynomial.IsSymmetric.one]
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (hs a (Multiset.mem_cons_self a s)).mul
      (ih (fun p hp => hs p (Multiset.mem_cons_of_mem hp)))

/-- The product of power sum symmetric polynomials is symmetric. Since `psum m` is
symmetric for each m (Mathlib: `psum_isSymmetric`), any product of power sums is
also symmetric. The `cycleTypePsumProduct` is exactly such a product. -/
theorem cycleTypePsumProduct_isSymmetric (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (cycleTypePsumProduct n σ).IsSymmetric := by
  unfold cycleTypePsumProduct
  apply MvPolynomial.IsSymmetric.mul
  · exact multiset_prod_isSymmetric _ (fun p hp => by
      rw [Multiset.mem_map] at hp
      obtain ⟨m, _, rfl⟩ := hp
      exact MvPolynomial.psum_isSymmetric (Fin n) ℂ m)
  · exact MvPolynomial.IsSymmetric.pow (MvPolynomial.psum_isSymmetric (Fin n) ℂ 1) _

/-- For a symmetric polynomial, coefficients are invariant under permutation of
the exponent vector. This follows from `rename σ P = P` for symmetric P and
the coefficient extraction formula `coeff_rename_mapDomain`. -/
theorem symmetric_coeff_mapDomain_perm {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P.IsSymmetric)
    (d : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    P.coeff (d.mapDomain σ) = P.coeff d := by
  conv_lhs => rw [← hP σ]
  exact MvPolynomial.coeff_rename_mapDomain σ σ.injective P d

/-! ### Multiplicity of Specht modules in permutation modules

The multiplicity of V_ν in U_μ is dim Hom_{S_n}(U_μ, V_ν). By Maschke's
theorem, ℂ[S_n]-modules are semisimple, so this equals the number of copies
of V_ν in any direct sum decomposition of U_μ.

Proposition 5.14.1 establishes:
- `spechtMultiplicity n mu nu = 0` when mu strictly dominates nu
- `spechtMultiplicity n la la = 1` (diagonal)

These are the Kostka numbers K_{ν,μ} (though the SSYT connection is not
proved here).
-/

/-- The multiplicity of V_ν in U_μ, defined as dim Hom_{S_n}(U_μ, V_ν).
By Maschke + Schur, this equals the isotypic multiplicity. -/
noncomputable def spechtMultiplicity (n : ℕ) (mu nu : Nat.Partition n) : ℕ :=
  Module.finrank ℂ (PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu))

/-- Multiplicity is zero when μ strictly dominates ν (Prop 5.14.1 vanishing). -/
theorem spechtMultiplicity_vanishing (n : ℕ) (mu nu : Nat.Partition n)
    (h : Nat.Partition.StrictDominates mu nu) :
    spechtMultiplicity n mu nu = 0 := by
  simp only [spechtMultiplicity]
  have hall : ∀ f : PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu), f = 0 :=
    Proposition5_14_1_vanishing n mu nu h
  have : Subsingleton (PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu)) :=
    ⟨fun f g => by rw [hall f, hall g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Multiplicity of V_λ in U_λ is 1 (Prop 5.14.1 diagonal). -/
theorem spechtMultiplicity_diagonal (n : ℕ) (la : Nat.Partition n) :
    spechtMultiplicity n la la = 1 :=
  Proposition5_14_1_diagonal n la

/-! ### Helper lemmas for Young's Rule

The proof of Young's Rule requires connecting three different perspectives:
1. `permModuleCharacter` (fixed-point count) = trace of the permutation representation
2. The trace decomposes via isotypic decomposition of the semisimple module
3. The multiplicities match `spechtMultiplicity` (Hom-space dimensions)
-/

private abbrev G_n (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q_n (n : ℕ) (la : Nat.Partition n) := G_n n ⧸ RowSubgroup n la

/-- The linear endomorphism of `PermutationModule n la` induced by left multiplication
by σ, viewed as a ℂ-linear map. This is the representation action. -/
noncomputable def permModuleEndomorphism (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : PermutationModule n la →ₗ[ℂ] PermutationModule n la :=
  Finsupp.lmapDomain ℂ ℂ (fun q : Q_n n la => σ • q)

/-- The trace of the permutation action on `PermutationModule` equals
`permModuleCharacter` (the fixed-point count). This is the standard fact that
the trace of a permutation matrix equals the number of fixed points.

**Proof**: Using the canonical basis `{single q 1 | q ∈ Q}`, the matrix of
`lmapDomain (σ • ·)` has entry 1 at (σ•q, q) and 0 elsewhere. The trace
is `∑_q [σ•q = q] = card(fixedBy Q σ)`. -/
theorem permModuleCharacter_eq_trace (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n la σ : ℂ) =
      LinearMap.trace ℂ _ (permModuleEndomorphism n la σ) := by
  classical
  simp only [permModuleCharacter, permModuleEndomorphism]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Finsupp.lmapDomain_apply]
  have hb : ∀ q : Q_n n la,
      (Finsupp.basisSingleOne (R := ℂ) (ι := Q_n n la) q) = Finsupp.single q 1 :=
    fun q => rfl
  have hr : ∀ v : Q_n n la →₀ ℂ,
      (Finsupp.basisSingleOne (R := ℂ) (ι := Q_n n la)).repr v = v :=
    fun v => rfl
  simp only [hb, hr, Finsupp.mapDomain_single, Finsupp.single_apply,
    Finset.sum_boole]
  push_cast
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MulAction.mem_fixedBy]

/-! ### Isotypic decomposition infrastructure for Young's Rule

The proof of Young's Rule proceeds via the isotypic decomposition of the
semisimple module `PermutationModule n mu`. Since `ℂ[S_n]` is semisimple
(Maschke's theorem), every `ℂ[S_n]`-module is semisimple, so `U_μ`
decomposes as `⊕_ν V_ν^{⊕m(μ,ν)}`. The trace of `σ` on `U_μ` then
decomposes as `Σ_ν m(μ,ν) · χ_{V_ν}(σ)`.

We structure this as:
1. The isotypic component of `U_μ` for type `V_ν` (as a ℂ-submodule)
2. These form an internal direct sum decomposition
3. The permutation action preserves each isotypic component
4. The trace on each component equals `m(μ,ν) · χ_{V_ν}(σ)`
-/

/-- The ℂ-scalar action on `PermutationModule` is compatible with the `SymGroupAlgebra`-module
structure: scalar multiplication by `c : ℂ` through the Finsupp structure agrees with
the action of `algebraMap ℂ (SymGroupAlgebra n) c` through the representation.
This is because the representation `ρ` is a ℂ-algebra homomorphism, so
`ρ(c · 1) = c · id`, meaning the derived ℂ-action matches the Finsupp ℂ-action. -/
private lemma permMod_smul_eq' (n : ℕ) (la : Nat.Partition n)
    (a : SymGroupAlgebra n) (x : PermutationModule n la) :
    a • x = (Representation.ofMulAction ℂ (G_n n) (Q_n n la)).asAlgebraHom a x := rfl

noncomputable instance permModule_isScalarTower (n : ℕ) (la : Nat.Partition n) :
    IsScalarTower ℂ (SymGroupAlgebra n) (PermutationModule n la) where
  smul_assoc c a m := by
    -- Need: c • (a • m) = (c • a) • m
    -- Both sides reduce to applications of the representation algebra homomorphism
    simp only [permMod_smul_eq']
    -- Goal: c • (rep a m) = rep (c • a) m
    -- Since rep is a ℂ-algebra hom: rep(c • a) = c • rep(a)
    rw [map_smul (Representation.ofMulAction ℂ (G_n n) (Q_n n la)).asAlgebraHom c a]
    -- Goal: c • (rep a m) = (c • rep a) m
    simp [LinearMap.smul_apply]

/-- The isotypic component of `PermutationModule n mu` corresponding to partition `nu`,
viewed as a ℂ-submodule. This is the sum of all simple `SymGroupAlgebra n`-submodules
of `U_μ` that are isomorphic (as `SymGroupAlgebra n`-modules) to `SpechtModule n nu`,
restricted to a ℂ-submodule via the scalar tower. -/
noncomputable def permModuleIsotypicComponent (n : ℕ) (mu nu : Nat.Partition n) :
    Submodule ℂ (PermutationModule n mu) :=
  (isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu) (SpechtModule n nu)).restrictScalars ℂ

/-- The isotypic components form an internal direct sum decomposition of `U_μ` as
ℂ-vector spaces. This follows from the semisimplicity of `ℂ[S_n]` and the
fact that isotypic components for distinct simple types are independent. -/
theorem permModule_isotypic_isInternal (n : ℕ) (mu : Nat.Partition n) :
    DirectSum.IsInternal (fun nu : Nat.Partition n =>
      permModuleIsotypicComponent n mu nu) := by
  sorry

/-- The permutation action `σ` on `U_μ` maps each isotypic component to itself.
This is because `σ` acts as a `ℂ[S_n]`-module endomorphism (left multiplication
by `of(σ)`), and isotypic components are fully invariant. -/
theorem permModuleEndomorphism_mapsTo_isotypic (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (nu : Nat.Partition n) :
    Set.MapsTo (permModuleEndomorphism n mu σ)
      (permModuleIsotypicComponent n mu nu) (permModuleIsotypicComponent n mu nu) := by
  sorry

/-- Each isotypic component of a finite-dimensional module is finite-dimensional. -/
instance permModuleIsotypicComponent_finite (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Finite ℂ (permModuleIsotypicComponent n mu nu) :=
  inferInstance

/-- Each isotypic component is a free ℂ-module (all ℂ-modules are free). -/
instance permModuleIsotypicComponent_free (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Free ℂ (permModuleIsotypicComponent n mu nu) :=
  inferInstance

/-- The trace of `σ` restricted to the isotypic component of type `V_ν` equals
`m(μ,ν) · χ_{V_ν}(σ)` where `m(μ,ν) = spechtMultiplicity n mu nu`.

**Proof sketch**: The isotypic component has the form `V_ν^{⊕m}`. Under
any such decomposition, `σ` acts as the "diagonal" map
`(σ|_{V_ν}, σ|_{V_ν}, ..., σ|_{V_ν})`, so the trace is `m · tr(σ on V_ν)`.
The multiplicity `m` equals `dim Hom_{S_n}(U_μ, V_ν)` by Schur's lemma. -/
theorem trace_isotypic_eq_mult_character (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ _ ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu)) =
    (spechtMultiplicity n mu nu : ℂ) * spechtModuleCharacter n nu σ := by
  sorry

/-! ### Young's Rule (character decomposition)

**Young's Rule**: χ_{U_μ}(σ) = Σ_ν m(μ,ν) · χ_{V_ν}(σ) where
m(μ,ν) = `spechtMultiplicity n mu nu`.

The proof combines:
1. `permModuleCharacter_eq_trace`: LHS = trace of σ on U_μ
2. `permModule_isotypic_isInternal`: U_μ = ⊕_ν (isotypic component)_ν
3. `trace_eq_sum_trace_restrict`: trace decomposes over the direct sum
4. `trace_isotypic_eq_mult_character`: each component contributes m(μ,ν)·χ_{V_ν}
-/

/-- **Young's Rule** (character identity): The permutation module character
equals a linear combination of Specht module characters weighted by
multiplicities m(μ,ν) = dim Hom_{S_n}(U_μ, V_ν).

With `spechtMultiplicity_vanishing` and `spechtMultiplicity_diagonal`, this
gives the upper-triangular decomposition with 1s on the diagonal. -/
theorem youngsRule_character (n : ℕ) (mu : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n mu σ : ℂ) =
      ∑ nu : Nat.Partition n,
        (spechtMultiplicity n mu nu : ℂ) * spechtModuleCharacter n nu σ := by
  -- Step 1: Reduce LHS to trace of permutation action on U_μ
  rw [permModuleCharacter_eq_trace]
  -- Step 2: Decompose trace via isotypic components
  rw [LinearMap.trace_eq_sum_trace_restrict (permModule_isotypic_isInternal n mu)
    (permModuleEndomorphism_mapsTo_isotypic n mu σ)]
  -- Step 3: Each component contributes multiplicity × character
  congr 1; ext nu
  exact trace_isotypic_eq_mult_character n mu nu σ

/-! ### Frobenius formula: alternating sum identity

The main theorem reduces to showing:
  χ_{V_λ}(σ) = Σ_π sign(π) · coeff(x^{λ+ρ-π(ρ)}, ∏ p_m^{i_m})

The proof uses:
1. Theorem 5.14.3 + symmetry: coeff(x^α, ∏ p_m^{i_m}) relates to χ_{U_{sort(α)}}
2. Young's Rule: substitute character decomposition
3. Upper-triangular determinant identity gives δ_{λ,ν}
-/

/-- **Key representation-theoretic step**: The alternating sum
  Σ_π sign(π) · coeff(x^{λ+ρ-π(ρ)}, ∏ p_m^{i_m})
equals the Specht module character χ_{V_λ}(σ).

**Proof outline** (Etingof, proof of Theorem 5.15.1):
1. Via Theorem 5.14.3 and symmetry, the RHS = Σ_π sign(π) χ_{U_{⟨λ+ρ-π(ρ)⟩}}(σ)
2. Via `youngsRule_character`: substitute χ_{U_μ} = Σ_ν m(μ,ν) χ_{V_ν}
3. Exchange summation: RHS = Σ_ν (Σ_π sign(π) m(sort(λ+ρ-π(ρ)), ν)) χ_{V_ν}(σ)
4. The inner sum = δ_{λ,ν} by the upper-triangular determinant identity
5. Therefore RHS = χ_{V_λ}(σ)

**Blocked on**: `youngsRule_character` and the alternating determinant identity. -/
theorem spechtCharacter_eq_alternating_sum_permCharacter
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • (if h : permExponent n π ≤
            Nat.Partition.toFinsupp la + rhoShift n
          then (MvPolynomial.coeff
            (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
            (cycleTypePsumProduct n σ) : ℂ) else 0) := by
  sorry

end

/-- **Theorem 5.15.1** (Frobenius character formula): The character of the Specht module
V_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals the coefficient
of x^{λ+ρ} in Δ(x) · ∏_{m≥1} p_m(x)^{i_m}, where Δ is the Vandermonde polynomial,
ρ = (n-1, ..., 1, 0), and p_m is the power sum symmetric polynomial.
(Etingof Theorem 5.15.1) -/
theorem Theorem5_15_1
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la + rhoShift n)
        (vandermondePoly n * cycleTypePsumProduct n σ) := by
  rw [spechtCharacter_eq_alternating_sum_permCharacter,
      coeff_vandermonde_mul]

end Etingof
