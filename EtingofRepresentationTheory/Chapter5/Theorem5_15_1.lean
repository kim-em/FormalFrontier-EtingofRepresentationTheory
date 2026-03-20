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
  (isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
    (SpechtModule n nu)).restrictScalars ℂ

/-- Specht modules for distinct partitions are non-isomorphic as `SymGroupAlgebra n`-modules.
This follows from the upper-triangular structure of the Kostka matrix: the multiplicity
of `V_ν` in `U_μ` is zero when `μ` strictly dominates `ν`, and 1 when `μ = ν`. -/
theorem spechtModule_noniso (n : ℕ) (nu₁ nu₂ : Nat.Partition n) (hne : nu₁ ≠ nu₂) :
    IsEmpty (↥(SpechtModule n nu₁) ≃ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu₂)) :=
  Theorem5_12_2_distinct n nu₁ nu₂ hne

/-- Every simple `SymGroupAlgebra n`-submodule of a module is isomorphic to some Specht module.
This is the completeness of the classification of S_n irreps: the Specht modules `{V_λ | λ ⊢ n}`
form a complete set of pairwise non-isomorphic simple modules for `ℂ[S_n]`. -/
theorem spechtModules_exhaust_simples (n : ℕ) (mu : Nat.Partition n)
    (S : Submodule (SymGroupAlgebra n) (PermutationModule n mu))
    [IsSimpleModule (SymGroupAlgebra n) S] :
    ∃ nu : Nat.Partition n, Nonempty (↥S ≃ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu)) :=
  Theorem5_12_2_classification n S

/-- Isotypic components for non-isomorphic simple modules are disjoint.
This follows from `sSupIndep_isotypicComponents`: the isotypic components (viewed as
a set) are supremum-independent, which implies pairwise disjointness. Since Specht modules
for distinct partitions are non-isomorphic, their isotypic components are distinct
(when nonzero) and hence disjoint. -/
private theorem isotypicComponent_disjoint_of_ne (n : ℕ) (mu : Nat.Partition n)
    (nu₁ nu₂ : Nat.Partition n) (hne : nu₁ ≠ nu₂) :
    Disjoint
      (isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₁))
      (isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₂)) := by
  -- The intersection is a submodule of the semisimple PermutationModule,
  -- hence semisimple. If nonzero, it contains a simple submodule S.
  -- S ≤ isotypicComponent for nu₁ implies S ≃ SpechtModule nu₁.
  -- S ≤ isotypicComponent for nu₂ implies S ≃ SpechtModule nu₂.
  -- But SpechtModule nu₁ ≇ SpechtModule nu₂, contradiction.
  rw [disjoint_iff]
  set I := isotypicComponent (SymGroupAlgebra n)
    (PermutationModule n mu) (SpechtModule n nu₁) ⊓
    isotypicComponent (SymGroupAlgebra n)
    (PermutationModule n mu) (SpechtModule n nu₂)
  -- I is a submodule of a semisimple module, hence semisimple
  haveI : IsSemisimpleModule (SymGroupAlgebra n) I :=
    IsSemisimpleModule.of_injective
      (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  -- Either I = ⊥ or I contains a simple submodule
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le I with h | ⟨S, hS_le, hS_simple⟩
  · exact h
  · exfalso
    -- S ≤ I ≤ isotypicComponent for nu₁
    have hS_le₁ : S ≤ isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₁) :=
      hS_le.trans inf_le_left
    -- S ≤ I ≤ isotypicComponent for nu₂
    have hS_le₂ : S ≤ isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₂) :=
      hS_le.trans inf_le_right
    -- By IsIsotypicOfType, S ≃ SpechtModule nu₁
    haveI := hS_simple
    haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n nu₁) :=
      Theorem5_12_2_irreducible n nu₁
    haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n nu₂) :=
      Theorem5_12_2_irreducible n nu₂
    have h₁ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₁)) S hS_le₁
    have h₂ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu₂)) S hS_le₂
    obtain ⟨e₁⟩ := h₁
    obtain ⟨e₂⟩ := h₂
    exact (spechtModule_noniso n nu₁ nu₂ hne).false (e₁.symm.trans e₂)

/-- The isotypic components indexed by partitions span the entire
module (as `SymGroupAlgebra n`-submodules). This follows from the
classification: every simple `SymGroupAlgebra n`-module is isomorphic
to some Specht module, so every isotypic component is covered. -/
private theorem iSup_isotypicComponent_eq_top (n : ℕ) (mu : Nat.Partition n) :
    ⨆ nu : Nat.Partition n,
      isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu) (SpechtModule n nu) = ⊤ := by
  rw [eq_top_iff, ← sSup_isotypicComponents (SymGroupAlgebra n) (PermutationModule n mu)]
  apply sSup_le
  intro c hc
  obtain ⟨S, hS_simple, rfl⟩ := hc
  -- S is simple; by classification, S ≃ SpechtModule n nu
  haveI := hS_simple
  obtain ⟨nu, ⟨e⟩⟩ := spechtModules_exhaust_simples n mu S
  rw [e.isotypicComponent_eq]
  exact le_iSup (fun nu => isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
    (SpechtModule n nu)) nu

/-- The indexed family of isotypic components is iSup-independent
in the SymGroupAlgebra-submodule lattice. This bridges from
`sSupIndep_isotypicComponents` (Mathlib) to the indexed version
via the classification of simple modules. -/
private theorem iSupIndep_isotypicComponent (n : ℕ)
    (mu : Nat.Partition n) :
    iSupIndep (fun nu : Nat.Partition n =>
      isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu)) := by
  -- Helper: non-bot isotypic component is in isotypicComponents
  have mem_of_ne_bot : ∀ nu,
      isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu) ≠ ⊥ →
      isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu) ∈
        isotypicComponents (SymGroupAlgebra n)
          (PermutationModule n mu) := by
    intro nu hbot
    obtain ⟨S, hS_le, hS_simple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left
        hbot
    haveI := hS_simple
    haveI := Theorem5_12_2_irreducible n nu
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu)) S hS_le
    exact ⟨S, hS_simple, e.symm.isotypicComponent_eq⟩
  rw [iSupIndep_def]
  intro nu
  by_cases hbot : isotypicComponent (SymGroupAlgebra n)
      (PermutationModule n mu) (SpechtModule n nu) = ⊥
  · simp [hbot]
  · -- Use sSupIndep_isotypicComponents: f nu is disjoint from
    -- sSup (isotypicComponents \ {f nu}), and ⨆ j≠nu, f j ≤ that
    apply (sSupIndep_isotypicComponents (SymGroupAlgebra n)
      (PermutationModule n mu) (mem_of_ne_bot nu hbot)).mono_right
    apply iSup₂_le
    intro nu' hne
    by_cases hbot' : isotypicComponent (SymGroupAlgebra n)
        (PermutationModule n mu) (SpechtModule n nu') = ⊥
    · simp [hbot']
    · -- f nu' ≠ f nu by non-isomorphism of Specht modules
      have hne_val : isotypicComponent (SymGroupAlgebra n)
          (PermutationModule n mu) (SpechtModule n nu') ≠
          isotypicComponent (SymGroupAlgebra n)
            (PermutationModule n mu)
            (SpechtModule n nu) := by
        intro heq
        obtain ⟨S, hS_le, hS_simple⟩ :=
          (IsSemisimpleModule.eq_bot_or_exists_simple_le
            _).resolve_left hbot
        haveI := hS_simple
        haveI := Theorem5_12_2_irreducible n nu
        haveI := Theorem5_12_2_irreducible n nu'
        obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n)
            (PermutationModule n mu) (SpechtModule n nu))
          S hS_le
        obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp
          (IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n)
            (PermutationModule n mu) (SpechtModule n nu'))
          S (heq ▸ hS_le)
        exact (spechtModule_noniso n nu nu' hne.symm).false
          (e₁.symm.trans e₂)
      exact le_sSup ⟨mem_of_ne_bot nu' hbot', hne_val⟩

/-- The isotypic components form an internal direct sum
decomposition of `U_μ` as ℂ-vector spaces. This follows from
the semisimplicity of `ℂ[S_n]` and the fact that isotypic
components for distinct simple types are independent. -/
theorem permModule_isotypic_isInternal (n : ℕ)
    (mu : Nat.Partition n) :
    DirectSum.IsInternal (fun nu : Nat.Partition n =>
      permModuleIsotypicComponent n mu nu) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- iSupIndep: transfer from A-lattice to ℂ-lattice
    have h := iSupIndep_isotypicComponent n mu
    rw [iSupIndep_def] at h ⊢
    intro nu
    simp only [permModuleIsotypicComponent]
    specialize h nu
    rw [disjoint_iff] at h ⊢
    simp only [← Submodule.restrictScalars_iSup]
    rw [← Submodule.restrictScalars_inf,
        Submodule.restrictScalars_eq_bot_iff]
    exact h
  · -- iSup = ⊤: the isotypic components span everything
    simp only [permModuleIsotypicComponent]
    rw [← Submodule.restrictScalars_iSup,
        show (⨆ i, isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
          (SpechtModule n i)) = (⊤ : Submodule (SymGroupAlgebra n) (PermutationModule n mu))
          from iSup_isotypicComponent_eq_top n mu,
        Submodule.restrictScalars_top]

/-- The permutation action `σ` on `U_μ` maps each isotypic component to itself.
This is because `σ` acts as a `ℂ[S_n]`-module endomorphism (left multiplication
by `of(σ)`), and isotypic components are fully invariant. -/
private lemma permModuleEndomorphism_eq_smul (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (v : PermutationModule n mu) :
    permModuleEndomorphism n mu σ v =
      (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • v := by
  simp only [permMod_smul_eq', permModuleEndomorphism]
  -- Both sides are Finsupp.lmapDomain ℂ ℂ (σ • ·) v
  -- rep.asAlgebraHom (of σ) = representation σ = lmapDomain (σ • ·)
  change Finsupp.lmapDomain ℂ ℂ (fun q => σ • q) v =
    (Representation.ofMulAction ℂ (G_n n) (Q_n n mu)).asAlgebraHom
      (MonoidAlgebra.of ℂ _ σ) v
  simp [Representation.asAlgebraHom_single]
  rfl

theorem permModuleEndomorphism_mapsTo_isotypic (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (nu : Nat.Partition n) :
    Set.MapsTo (permModuleEndomorphism n mu σ)
      (permModuleIsotypicComponent n mu nu) (permModuleIsotypicComponent n mu nu) := by
  intro v hv
  rw [permModuleEndomorphism_eq_smul]
  exact (isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
    (SpechtModule n nu)).smul_mem _ hv

/-- Each isotypic component of a finite-dimensional module is finite-dimensional. -/
instance permModuleIsotypicComponent_finite (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Finite ℂ (permModuleIsotypicComponent n mu nu) :=
  inferInstance

/-- Each isotypic component is a free ℂ-module (all ℂ-modules are free). -/
instance permModuleIsotypicComponent_free (n : ℕ) (mu nu : Nat.Partition n) :
    Module.Free ℂ (permModuleIsotypicComponent n mu nu) :=
  inferInstance
/-- Trace of a componentwise endomorphism on `Fin k → V` equals `k * trace(f)`.
This is the key lemma for computing traces on isotypic components. -/
private lemma trace_pi_diag {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (Fin k → V) (LinearMap.pi (fun i => f ∘ₗ LinearMap.proj i)) =
    (k : ℂ) * LinearMap.trace ℂ V f := by
  classical
  let bV := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : Fin k => bV),
      LinearMap.trace_eq_matrix_trace ℂ bV]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Pi.basis_apply, Pi.basis_repr,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp [Finset.sum_const]

/-- The isotypic component (as R-module) is isotypic of type `SpechtModule n nu`,
and it is finite as an R-module. -/
private lemma isotypicComponent_isIsotypicOfType (n : ℕ) (mu nu : Nat.Partition n) :
    IsIsotypicOfType (SymGroupAlgebra n)
      (isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu) (SpechtModule n nu))
      (SpechtModule n nu) := by
  haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n nu) :=
    Theorem5_12_2_irreducible n nu
  exact IsIsotypicOfType.isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
    (SpechtModule n nu)

/-- The restricted endomorphism on the isotypic component equals scalar multiplication
by `of ℂ _ σ` (an element of the group algebra) at the level of the underlying module. -/
private lemma restrict_val_eq_smul (n : ℕ) (mu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (nu : Nat.Partition n)
    (v : ↥(permModuleIsotypicComponent n mu nu)) :
    ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu) v : PermutationModule n mu) =
    (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • (v : PermutationModule n mu) :=
  permModuleEndomorphism_eq_smul n mu σ v

/-- Under an R-linear equiv `C_ν ≃ₗ[R] Fin k → V_ν`, the σ-action on C_ν
(which is R-multiplication by `of σ`) conjugates to componentwise σ-action on V_ν.
This is because the equiv is R-linear, so it commutes with the R-action. -/
private lemma conj_restrict_eq_pi_spechtAction (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (e_R : ↥(isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
      (SpechtModule n nu)) ≃ₗ[SymGroupAlgebra n] (Fin k → ↥(SpechtModule n nu))) :
    (e_R.restrictScalars ℂ).conj
      ((permModuleEndomorphism n mu σ).restrict
        (permModuleEndomorphism_mapsTo_isotypic n mu σ nu)) =
    LinearMap.pi (fun i => spechtModuleAction n nu σ ∘ₗ LinearMap.proj i) := by
  -- Both sides equal "multiply by of σ" on Fin k → V_ν
  -- LHS: e_R ∘ (of σ • ·) ∘ e_R⁻¹ = of σ • · (since e_R is R-linear)
  -- RHS: componentwise (of σ • ·) = of σ • · (Pi.smul)
  set r : SymGroupAlgebra n := MonoidAlgebra.of ℂ _ σ
  apply LinearMap.ext; intro v
  -- Step 1: show restrict acts as R-smul by of σ on the isotypicComponent
  have h_restrict : ∀ (w : ↥(isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
      (SpechtModule n nu))),
    ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu) w : PermutationModule n mu) =
      r • (w : PermutationModule n mu) := by
    intro w; exact permModuleEndomorphism_eq_smul n mu σ w
  -- Show the conj applied to v equals what we want
  change (e_R.restrictScalars ℂ) (((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu))
        ((e_R.restrictScalars ℂ).symm v)) =
      (LinearMap.pi (fun i => spechtModuleAction n nu σ ∘ₗ LinearMap.proj i)) v
  -- Step 2: show e_R (restrict ... (e_R.symm v)) = e_R (r • e_R.symm v)
  have h_eq : (e_R ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu) (e_R.symm v)) :
      Fin k → ↥(SpechtModule n nu)) = e_R (r • e_R.symm v) := by
    congr 1; apply Subtype.ext; exact h_restrict _
  -- (e_R.restrictScalars ℂ) and e_R agree on elements
  change (e_R ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu) (e_R.symm v))) = _
  rw [h_eq, map_smul e_R, LinearEquiv.apply_symm_apply]
  -- Goal: r • v = pi(fun i => spechtModuleAction ∘ proj i) v
  -- Both sides equal fun i => r • v i = fun i => spechtModuleAction n nu σ (v i)
  rfl

/-- An R-linear map from the wrong isotypic component to a simple module is zero.
This is a consequence of Schur's lemma: the isotypic component of type V_λ is
generated by simple submodules isomorphic to V_λ, and any map V_λ → V_ν
is zero when λ ≠ ν (since V_λ ≇ V_ν). -/
private lemma hom_from_wrong_isotypic_eq_zero (n : ℕ) (mu : Nat.Partition n)
    (nu la : Nat.Partition n) (hla : la ≠ nu)
    (f : PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu))
    (x : PermutationModule n mu)
    (hx : x ∈ isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
      (SpechtModule n la)) : f x = 0 := by
  set R := SymGroupAlgebra n
  set V := ↥(SpechtModule n nu)
  set U := PermutationModule n mu
  haveI : IsSimpleModule R V := Theorem5_12_2_irreducible n nu
  haveI : IsSimpleModule R (SpechtModule n la) := Theorem5_12_2_irreducible n la
  -- ker f is an R-submodule of U; show isotypicComponent for V_la ≤ ker f
  suffices h : isotypicComponent R U (SpechtModule n la) ≤ LinearMap.ker f from
    LinearMap.mem_ker.mp (h hx)
  -- isotypicComponent = sSup of simple submodules isomorphic to V_la
  apply sSup_le
  intro S ⟨e_S⟩
  -- S ≅ V_la so S is simple
  haveI : IsSimpleModule R S := IsSimpleModule.congr e_S
  -- f restricted to S : S →ₗ[R] V, with S ≅ V_la and V = V_nu
  -- By Schur, this is zero or bijective
  intro s hs
  rw [LinearMap.mem_ker]
  rcases LinearMap.bijective_or_eq_zero (f.comp (Submodule.subtype S)) with h_bij | h_zero
  · -- If bijective, S ≅ V contradicting S ≅ V_la ≇ V_nu
    exfalso
    have e_SV := LinearEquiv.ofBijective (f.comp (Submodule.subtype S)) h_bij
    exact (spechtModule_noniso n la nu hla).false (e_S.symm.trans e_SV)
  · -- f ∘ S.subtype = 0
    have := congr_fun (congr_arg DFunLike.coe h_zero) ⟨s, hs⟩
    simpa using this

set_option maxHeartbeats 800000 in
-- Schur's lemma + dimension counting requires more heartbeats
/-- The number of copies in the R-linear decomposition `C_ν ≃ₗ[R] Fin k → V_ν`
equals `spechtMultiplicity n mu nu = finrank Hom_R(U_μ, V_ν)`.

**Proof**: Uses the isotypic decomposition, Schur's lemma for algebraically closed
fields, and dimension counting. -/
private lemma multiplicity_eq_spechtMultiplicity (n : ℕ) (mu nu : Nat.Partition n)
    (k : ℕ) (e_R : ↥(isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu)
      (SpechtModule n nu)) ≃ₗ[SymGroupAlgebra n] (Fin k → ↥(SpechtModule n nu))) :
    k = spechtMultiplicity n mu nu := by
  -- Abbreviations
  set R := SymGroupAlgebra n
  set V := ↥(SpechtModule n nu)
  set U := PermutationModule n mu
  set C := isotypicComponent R U V
  -- Instances needed throughout
  haveI : IsSimpleModule R V := Theorem5_12_2_irreducible n nu
  haveI : Module.Finite ℂ V := inferInstance
  haveI : FiniteDimensional ℂ V := inferInstance
  -- Step 1: Schur's lemma — finrank ℂ (End_R V) = 1
  have h_schur : Module.finrank ℂ (V →ₗ[R] V) = 1 := by
    have h_bij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ (A := R) (V := V)
    rw [LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective (Algebra.linearMap ℂ (Module.End R V)) h_bij).symm]
    exact Module.finrank_self ℂ
  -- Step 2: finrank ℂ ((Fin k → V) →ₗ[R] V) = k (via lsum + Step 1)
  have h_lsum_finrank : Module.finrank ℂ ((Fin k → V) →ₗ[R] V) = k := by
    rw [LinearEquiv.finrank_eq (LinearMap.lsum (R := R) ℂ (φ := fun _ : Fin k => V) (M := V)).symm,
        Module.finrank_pi_fintype, h_schur, Finset.sum_const, Finset.card_fin, smul_eq_mul,
        mul_one]
  -- Step 3: Transport by e_R — finrank ℂ (C →ₗ[R] V) = k
  have h_transport : Module.finrank ℂ (↥C →ₗ[R] V) = k := by
    have e_hom : (↥C →ₗ[R] V) ≃ₗ[ℂ] ((Fin k → V) →ₗ[R] V) :=
      { toFun := fun f => f.comp e_R.symm.toLinearMap
        invFun := fun g => g.comp e_R.toLinearMap
        left_inv := fun f => by
          apply LinearMap.ext; intro x
          simp only [LinearMap.comp_apply]
          congr 1; exact e_R.symm_apply_apply x
        right_inv := fun g => by
          apply LinearMap.ext; intro v
          simp only [LinearMap.comp_apply]
          congr 1; exact e_R.apply_symm_apply v
        map_add' := fun f g => by apply LinearMap.ext; intro; simp
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          simp [LinearMap.smul_apply] }
    rw [LinearEquiv.finrank_eq e_hom]; exact h_lsum_finrank
  -- Step 4: finrank ℂ (U →ₗ[R] V) = k (via restriction to isotypic component)
  have h_restrict : Module.finrank ℂ (U →ₗ[R] V) = k := by
    -- The complement of C in the R-submodule lattice
    have h_indep := iSupIndep_isotypicComponent n mu
    -- D = ⨆_{la ≠ nu} C_la
    set D : Submodule R U := ⨆ (la : Nat.Partition n) (_ : la ≠ nu),
      isotypicComponent R U (SpechtModule n la) with hD_def
    -- C and D are complementary R-submodules
    have h_disj : Disjoint C D := by
      exact h_indep.disjoint_biSup (show nu ∉ {la : Nat.Partition n | la ≠ nu} from fun h => h rfl)
    have h_codisj : Codisjoint C D := by
      rw [codisjoint_iff, eq_top_iff, ← iSup_isotypicComponent_eq_top n mu]
      apply iSup_le; intro la
      by_cases h : la = nu
      · exact h ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup_of_le la (le_iSup_of_le h le_rfl))
    have h_compl : IsCompl C D := ⟨h_disj, h_codisj⟩
    -- R-linear projection onto C
    set proj_C : U →ₗ[R] ↥C := Submodule.linearProjOfIsCompl C D h_compl
    -- Key fact: f vanishes on D for any R-linear map f : U → V
    have h_vanish_D : ∀ (f : U →ₗ[R] V) (d : U), d ∈ D → f d = 0 := by
      intro f d hd
      -- d ∈ D = ⨆_{la ≠ nu} C_la, so d is in the span of these components
      -- Need: f vanishes on each C_la for la ≠ nu
      have : D ≤ LinearMap.ker f := by
        rw [hD_def]
        apply iSup₂_le
        intro la hla x hx
        exact LinearMap.mem_ker.mpr (hom_from_wrong_isotypic_eq_zero n mu nu la hla f x hx)
      exact LinearMap.mem_ker.mp (this hd)
    -- Build ℂ-linear equiv (U →ₗ[R] V) ≃ₗ[ℂ] (C →ₗ[R] V) via restriction
    have e_restrict : (U →ₗ[R] V) ≃ₗ[ℂ] (↥C →ₗ[R] V) :=
      { toFun := fun f => f.comp C.subtype
        invFun := fun g => g.comp proj_C
        left_inv := fun f => by
          apply LinearMap.ext; intro u
          change (f.comp C.subtype).comp proj_C u = f u
          simp only [LinearMap.comp_apply]
          -- u = C.subtype(proj_C u) + (u - C.subtype(proj_C u))
          have h_decomp : f u = f (C.subtype (proj_C u)) + f (u - C.subtype (proj_C u)) := by
            rw [← map_add f]; congr 1; abel
          rw [h_decomp]
          -- f vanishes on the D-component: u - subtype(proj_C u) ∈ D
          have h_mem_D : u - C.subtype (proj_C u) ∈ D := by
            rw [← Submodule.linearProjOfIsCompl_ker h_compl]
            rw [LinearMap.mem_ker, map_sub]
            have : proj_C (C.subtype (proj_C u)) = proj_C u :=
              Submodule.linearProjOfIsCompl_apply_left h_compl (proj_C u)
            rw [this, sub_self]
          rw [h_vanish_D f _ h_mem_D, add_zero]
        right_inv := fun g => by
          apply LinearMap.ext; intro ⟨x, hx⟩
          change g.comp proj_C (C.subtype ⟨x, hx⟩) = g ⟨x, hx⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply]
          congr 1
          exact Submodule.linearProjOfIsCompl_apply_left h_compl ⟨x, hx⟩
        map_add' := fun f g => by apply LinearMap.ext; intro; simp [LinearMap.comp_apply]
        map_smul' := fun c f => by
          apply LinearMap.ext; intro x
          simp [LinearMap.comp_apply, LinearMap.smul_apply] }
    rw [LinearEquiv.finrank_eq e_restrict]; exact h_transport
  -- Combine: k = finrank ℂ (U →ₗ[R] V) = spechtMultiplicity
  unfold spechtMultiplicity; linarith

/-- The isotypic component for `V_ν` in `U_μ` is isomorphic (as `ℂ`-vector space)
to `Fin m → V_ν` where `m = spechtMultiplicity n mu nu`. This is the structural
decomposition of the isotypic component as a direct sum of copies of the simple module. -/
theorem isotypicComponent_linearEquiv_fun (n : ℕ) (mu nu : Nat.Partition n) :
    Nonempty (↥(permModuleIsotypicComponent n mu nu) ≃ₗ[ℂ]
      (Fin (spechtMultiplicity n mu nu) → ↥(SpechtModule n nu))) := by
  have hiso := isotypicComponent_isIsotypicOfType n mu nu
  haveI : Module.Finite ℂ
      (↥(isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu) (SpechtModule n nu))) :=
    permModuleIsotypicComponent_finite n mu nu
  haveI : Module.Finite (SymGroupAlgebra n)
      (isotypicComponent (SymGroupAlgebra n) (PermutationModule n mu) (SpechtModule n nu)) :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  obtain ⟨k, ⟨e_R⟩⟩ := hiso.linearEquiv_fun
  rw [← multiplicity_eq_spechtMultiplicity n mu nu k e_R]
  exact ⟨e_R.restrictScalars ℂ⟩

/-- The trace of a "diagonal" endomorphism on a pi type `Fin m → V` that applies the same
linear map `f` componentwise equals `m * trace f`. -/
private theorem trace_pi_diagonal {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Module.Free ℂ V]
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)) =
      (m : ℂ) * LinearMap.trace ℂ _ f := by
  -- g : (Fin m → V) →ₗ[ℂ] (Fin m → V) is the "apply f componentwise" map
  set g := LinearMap.pi (fun (i : Fin m) => f ∘ₗ LinearMap.proj i)
  -- Key: g sends Pi.single i v ↦ Pi.single i (f v)
  have hg_single : ∀ (i : Fin m) (v : V), g (Pi.single i v) = Pi.single i (f v) := by
    intro i v
    ext k
    simp only [g, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Pi.single_apply]
    split <;> simp [*]
  -- Use trace_eq_matrix_trace with the Pi basis
  set b := Module.Free.chooseBasis ℂ V
  haveI : Fintype (Module.Free.ChooseBasisIndex ℂ V) :=
    FiniteDimensional.fintypeBasisIndex b
  set pb := Pi.basis (fun (_ : Fin m) => b)
  rw [LinearMap.trace_eq_matrix_trace ℂ pb g, LinearMap.trace_eq_matrix_trace ℂ b f]
  -- Both sides are sums of diagonal matrix entries
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  conv_lhs =>
    arg 2; ext p
    rw [show pb (p) = Pi.single p.1 (b p.2) from Pi.basis_apply _ p]
  simp only [hg_single]
  have hrepr : ∀ (i : Fin m) (j : Module.Free.ChooseBasisIndex ℂ V),
      (pb.repr (Pi.single i (f (b j)))) ⟨i, j⟩ = (b.repr (f (b j))) j := by
    intro i j
    simp [pb, Pi.basis_repr, Pi.single_eq_same]
  simp_rw [hrepr]
  simp_rw [Fintype.sum_sigma, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- On the isotypic component `V_ν^{⊕m}`, any `SymGroupAlgebra n`-endomorphism acts
diagonally: the same endomorphism on each copy. In particular, for the permutation
action `σ`, the restricted endomorphism is conjugate (via the isotypic decomposition)
to the diagonal map `(σ|_{V_ν}, ..., σ|_{V_ν})`.

This gives: `trace(σ|_{C_ν}) = m · trace(σ|_{V_ν})`. -/
theorem trace_isotypic_eq_mult_trace (n : ℕ) (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (_e : ↥(permModuleIsotypicComponent n mu nu) ≃ₗ[ℂ]
      (Fin (spechtMultiplicity n mu nu) → ↥(SpechtModule n nu))) :
    LinearMap.trace ℂ _ ((permModuleEndomorphism n mu σ).restrict
      (permModuleEndomorphism_mapsTo_isotypic n mu σ nu)) =
    (spechtMultiplicity n mu nu : ℂ) * LinearMap.trace ℂ _
      (spechtModuleAction n nu σ) := by
  -- Strategy: Get an R-linear equiv via IsIsotypicOfType.linearEquiv_fun,
  -- use it to show trace = m' * trace(σ on V_ν), then match m' = m via dimensions.
  set A := SymGroupAlgebra n
  set C_R := isotypicComponent A (PermutationModule n mu) (SpechtModule n nu) with hCR_def
  -- Provide ℂ-module structure on ↥C_R via restrictScalars
  letI : Module ℂ ↥C_R := (C_R.restrictScalars ℂ).module
  -- IsScalarTower for the submodule
  haveI : IsScalarTower ℂ A ↥C_R :=
    ⟨fun c a m => Subtype.ext (smul_assoc c a (m : PermutationModule n mu))⟩
  -- IsSimpleModule for Specht modules
  haveI : IsSimpleModule A ↥(SpechtModule n nu) := Theorem5_12_2_irreducible n nu
  -- The isotypic component is isotypic of type V_ν
  have hiso : IsIsotypicOfType A C_R (SpechtModule n nu) :=
    IsIsotypicOfType.isotypicComponent _ _ _
  -- Module.Finite ℂ for C_R (subspace of finite-dim vector space)
  haveI : Module.Finite ℂ ↥C_R := by
    change Module.Finite ℂ ↥(C_R.restrictScalars ℂ)
    infer_instance
  -- Module.Finite over A follows from Module.Finite over ℂ
  haveI : Module.Finite A ↥C_R :=
    Module.Finite.of_restrictScalars_finite ℂ A ↥C_R
  -- Get R-linear equiv
  obtain ⟨m', ⟨e'⟩⟩ := hiso.linearEquiv_fun
  -- Restrict to ℂ-linear equiv
  let e'_ℂ : ↥C_R ≃ₗ[ℂ] (Fin m' → ↥(SpechtModule n nu)) := e'.restrictScalars ℂ
  -- Step 1: Show the conjugated endomorphism is componentwise.
  set f := (permModuleEndomorphism n mu σ).restrict
    (permModuleEndomorphism_mapsTo_isotypic n mu σ nu) with hf_def
  -- The conjugated map through e'_ℂ equals the componentwise smul
  have hconj_eq : ∀ v i,
      (e'_ℂ.conj f v) i = (MonoidAlgebra.of ℂ _ σ : A) • v i := by
    intro v i
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    -- f acts as A-smul on elements of the submodule
    have hfsmul : (f (e'_ℂ.symm v) : PermutationModule n mu) =
        (MonoidAlgebra.of ℂ _ σ : A) • ((e'_ℂ.symm v : ↥C_R) : PermutationModule n mu) :=
      permModuleEndomorphism_eq_smul n mu σ _
    -- Lift to subtype equality
    have hfsmul' : f (e'_ℂ.symm v) = (MonoidAlgebra.of ℂ _ σ : A) • (e'_ℂ.symm v) :=
      Subtype.ext hfsmul
    -- Combine steps: e'_ℂ (f (e'_ℂ.symm v)) = (of σ) • v
    have step : e'_ℂ (f (e'_ℂ.symm v)) = (MonoidAlgebra.of ℂ _ σ : A) • v :=
      show e' (f (e'.symm v)) = _ by
        rw [show (f (e'.symm v) : ↥C_R) = (MonoidAlgebra.of ℂ _ σ : A) • (e'.symm v) from
          Subtype.ext (permModuleEndomorphism_eq_smul n mu σ _),
          e'.map_smul, LinearEquiv.apply_symm_apply]
    exact congr_fun step i
  -- Step 2: The componentwise (of σ) • is the same as spechtModuleAction
  have hact : ∀ (v : ↥(SpechtModule n nu)),
      (MonoidAlgebra.of ℂ _ σ : A) • v = spechtModuleAction n nu σ v := by
    intro ⟨m, hm⟩; rfl
  -- Step 3: Show e'_ℂ.conj f = pi (fun i => spechtModuleAction ∘ proj i)
  have hconj_pi : e'_ℂ.conj f =
      LinearMap.pi (fun (i : Fin m') => spechtModuleAction n nu σ ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro w; funext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [← hact]
    exact hconj_eq w i
  -- Step 4: trace f = trace (e'_ℂ.conj f) = m' * trace(spechtModuleAction)
  have htrace : LinearMap.trace ℂ _ f =
      (m' : ℂ) * LinearMap.trace ℂ _ (spechtModuleAction n nu σ) := by
    calc LinearMap.trace ℂ _ f
        = LinearMap.trace ℂ _ (e'_ℂ.conj f) := (LinearMap.trace_conj' f e'_ℂ).symm
      _ = LinearMap.trace ℂ _ (LinearMap.pi (fun (i : Fin m') =>
            spechtModuleAction n nu σ ∘ₗ LinearMap.proj i)) := by rw [hconj_pi]
      _ = (m' : ℂ) * LinearMap.trace ℂ _ (spechtModuleAction n nu σ) := trace_pi_diagonal _
  rw [htrace]
  -- Goal: m' * trace(spechtModuleAction) = spechtMultiplicity * trace(spechtModuleAction)
  -- Need m' = spechtMultiplicity (via dimension matching with e)
  congr 1
  -- Dimension comparison: both equivs give finrank C = k * finrank V
  have hdim_e' : Module.finrank ℂ ↥C_R =
      m' * Module.finrank ℂ ↥(SpechtModule n nu) := by
    rw [LinearEquiv.finrank_eq e'_ℂ, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin,
      smul_eq_mul]
  have hdim_e : Module.finrank ℂ ↥C_R =
      spechtMultiplicity n mu nu * Module.finrank ℂ ↥(SpechtModule n nu) := by
    rw [show (Module.finrank ℂ ↥C_R) =
        Module.finrank ℂ ↥(permModuleIsotypicComponent n mu nu) from rfl,
      LinearEquiv.finrank_eq _e, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin,
      smul_eq_mul]
  -- Specht modules are nonzero simple modules, so finrank > 0
  haveI : Nontrivial ↥(SpechtModule n nu) :=
    IsSimpleModule.nontrivial (SymGroupAlgebra n) _
  have hpos : 0 < Module.finrank ℂ ↥(SpechtModule n nu) := Module.finrank_pos
  exact_mod_cast Nat.eq_of_mul_eq_mul_right hpos (hdim_e'.symm.trans hdim_e)

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
  obtain ⟨e⟩ := isotypicComponent_linearEquiv_fun n mu nu
  rw [trace_isotypic_eq_mult_trace n mu nu σ e]
  -- spechtModuleCharacter = trace of spechtModuleAction by definition
  rfl

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


/-! ### Sorting infrastructure for the Frobenius formula proof

To connect polynomial coefficients to permutation module characters, we need to
"sort" a `Fin n →₀ ℕ` vector into a `Nat.Partition n`. The key facts are:
1. A non-negative integer vector summing to n determines a partition (by sorting)
2. Symmetric polynomial coefficients are invariant under permutation of exponents
3. Theorem 5.14.3 converts partition coefficients to permutation module characters
-/

/-- Convert a `Fin n →₀ ℕ` whose values sum to `n` into a `Nat.Partition n`,
by taking the multiset of values and filtering out zeros. -/
noncomputable def finsuppToPartition {n : ℕ} (v : Fin n →₀ ℕ)
    (hsum : ∑ i : Fin n, v i = n) : Nat.Partition n :=
  Nat.Partition.ofSums n (Finset.univ.val.map v) (by
    change Finset.univ.sum v = n
    exact hsum)

private lemma list_sum_eq_fin_sum_getD (l : List ℕ) (n : ℕ) (h : l.length ≤ n) :
    l.sum = ∑ i : Fin n, l.getD i 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp [List.length] at h
    | succ n =>
      have ht : t.length ≤ n := Nat.succ_le_succ_iff.mp (by simpa [List.length] using h)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [List.sum_cons, ih n ht]

/-- The sum of entries of `la.toFinsupp + rhoShift n - permExponent n π` equals `n`,
when the subtraction is componentwise valid. This follows from the fact that both
`rhoShift` and `permExponent` are permutations of `{0, ..., n-1}`, so their sums
cancel, leaving `∑ la.toFinsupp = n`. -/
theorem sum_shifted_sub_permExponent {n : ℕ} (la : Nat.Partition n)
    (π : Equiv.Perm (Fin n))
    (h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n) :
    ∑ i : Fin n, (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π) i = n := by
  -- From h, (la + ρ - e_π) + e_π = la + ρ
  have hcancel := tsub_add_cancel_of_le h
  -- Sum both sides: ∑(la+ρ-e_π) + ∑ e_π = ∑ la + ∑ ρ
  have key : ∑ i : Fin n, (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π) i +
      ∑ i : Fin n, (permExponent n π) i =
      ∑ i : Fin n, (Nat.Partition.toFinsupp la) i + ∑ i : Fin n, (rhoShift n) i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; exact congr_fun (congr_arg DFunLike.coe hcancel) i
  -- ∑ permExponent = ∑ i, i.val (reindexing by π⁻¹)
  have hperm : ∑ i : Fin n, (permExponent n π) i = ∑ i : Fin n, i.val := by
    simp only [permExponent, Finsupp.coe_equivFunOnFinite_symm]
    exact Fintype.sum_equiv π⁻¹ _ _ (fun _ => rfl)
  -- ∑ rhoShift = ∑ i, i.val (by reversal symmetry)
  have hrho : ∑ i : Fin n, (rhoShift n) i = ∑ i : Fin n, i.val := by
    simp only [rhoShift, Finsupp.coe_equivFunOnFinite_symm]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]; omega
  -- ∑ la.toFinsupp = n (partition sum property)
  have hla : ∑ i : Fin n, (Nat.Partition.toFinsupp la) i = n := by
    have hfs : (Nat.Partition.toFinsupp la).sum (fun _ m => m) =
        ∑ i : Fin n, (Nat.Partition.toFinsupp la) i :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    rw [← hfs, Nat.Partition.toFinsupp, Finsupp.equivFunOnFinite_symm_sum]
    have hsorted : la.sortedParts.sum = n := by
      unfold Nat.Partition.sortedParts
      have h := congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
      rw [Multiset.sum_coe] at h; linarith [la.parts_sum]
    have hlen : la.sortedParts.length ≤ n := by
      calc la.sortedParts.length
          ≤ la.sortedParts.sum := List.length_le_sum_of_one_le _ (fun i hi => by
            unfold Nat.Partition.sortedParts at hi
            exact la.parts_pos (Multiset.sort_eq la.parts (· ≥ ·) ▸ Multiset.mem_coe.mpr hi))
        _ = n := hsorted
    linarith [list_sum_eq_fin_sum_getD la.sortedParts n hlen]
  -- Combine
  omega

/-- For `c ≠ 0` and `l.length ≤ n`, the number of `i : Fin n` with `l.getD i 0 = c`
equals `List.count c l`. Out-of-bounds indices get default `0 ≠ c`. -/
private lemma card_filter_getD_eq_count (l : List ℕ) (n : ℕ) (hn : l.length ≤ n)
    (c : ℕ) (hc : c ≠ 0) :
    ((Finset.univ : Finset (Fin n)).val.filter
      (fun i : Fin n => c = l.getD (↑i) 0)).card = l.count c := by
  -- Convert filter.card to Multiset.count via count_map
  rw [← Multiset.count_map (f := fun i : Fin n => l.getD (↑i) 0)]
  -- Prove count c (map getD univ.val) = l.count c by induction
  induction l generalizing n with
  | nil =>
    simp only [List.getD_nil, List.count_nil, Multiset.map_const', Multiset.count_replicate]
    exact if_neg (Ne.symm hc)
  | cons a t ih =>
    cases n with
    | zero => simp at hn
    | succ m =>
      have htlen : t.length ≤ m := by simp at hn; omega
      -- Decompose univ.val for Fin(m+1): 0 ::ₘ map succ (univ.val for Fin m)
      have huniv : (Finset.univ : Finset (Fin (m + 1))).val =
          (0 : Fin (m + 1)) ::ₘ (Finset.univ : Finset (Fin m)).val.map Fin.succ := by
        rw [Fin.univ_succ, Finset.cons_val, Finset.map_val]
        simp only [Function.Embedding.coeFn_mk]
      rw [huniv, Multiset.map_cons, Multiset.map_map]
      simp only [Function.comp, Fin.val_succ, List.getD_cons_succ,
        Fin.val_zero, List.getD_cons_zero]
      rw [Multiset.count_cons, ih m htlen]
      by_cases h : c = a
      · subst h; simp [List.count_cons_self]
      · rw [if_neg h, List.count_cons_of_ne (Ne.symm h)]; omega

/-- For a symmetric polynomial P, the coefficient at any vector v equals the
coefficient at `(finsuppToPartition v hsum).toFinsupp`. This follows from the
fact that symmetric polynomials have permutation-invariant coefficients, and
sorting v into a partition amounts to permuting the exponent indices. -/
theorem coeff_symmetric_eq_coeff_partition {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P.IsSymmetric)
    (v : Fin n →₀ ℕ) (hsum : ∑ i : Fin n, v i = n) :
    P.coeff v = P.coeff (Nat.Partition.toFinsupp (finsuppToPartition v hsum)) := by
  -- The sorted partition has the same multiset of values as v, just rearranged.
  -- Symmetric polynomials have permutation-invariant coefficients, so the result follows.
  set w := Nat.Partition.toFinsupp (finsuppToPartition v hsum) with hw_def
  -- Key: construct a permutation σ with w(σ i) = v i
  suffices hfiber : ∀ c : ℕ, Fintype.card {i : Fin n // v i = c} =
      Fintype.card {i : Fin n // w i = c} by
    let e := fun c => Fintype.equivOfCardEq (hfiber c)
    let σ : Fin n ≃ Fin n := Equiv.ofFiberEquiv (f := v) (g := w) e
    have hσ : ∀ i, w (σ i) = v i := Equiv.ofFiberEquiv_map e
    have : P.coeff w = P.coeff (w.mapDomain σ.symm) :=
      (symmetric_coeff_mapDomain_perm P hP w σ.symm).symm
    rw [this]; congr 1; ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]; exact (hσ i).symm
  -- Fiber cardinalities: v and w have the same value distribution.
  -- Strategy: for c ≠ 0, both count the multiplicity of c in the partition parts.
  -- For c = 0, use that both have n total elements and matching non-zero counts.
  set p := finsuppToPartition v hsum
  set M := Finset.univ.val.map (⇑v) with hM_def
  set Mw := Finset.univ.val.map (⇑w) with hMw_def
  -- Convert Fintype.card to Multiset.count
  have hcard_eq_count : ∀ (f : Fin n →₀ ℕ) (c : ℕ),
      Fintype.card {i : Fin n // f i = c} =
      Multiset.count c (Finset.univ.val.map (⇑f)) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩)
  intro c
  rw [hcard_eq_count v c, hcard_eq_count w c]
  -- Now prove: count c M = count c Mw
  -- p.parts = M.filter(· ≠ 0) (definition of finsuppToPartition/ofSums)
  have hparts : p.parts = M.filter (· ≠ 0) := by
    simp [p, finsuppToPartition, Nat.Partition.ofSums, M, hM_def]
  -- sortedParts = parts as multisets
  have hsorted_eq : (p.sortedParts : Multiset ℕ) = p.parts :=
    Multiset.sort_eq p.parts (· ≥ ·)
  -- w's non-zero filter also equals p.parts
  have hparts_w : Mw.filter (· ≠ 0) = p.parts := by
    -- Mw.filter(· ≠ 0) = ↑sortedParts = p.parts
    rw [hsorted_eq.symm]
    -- Show by Multiset.ext: for all c', count equality
    ext c'
    simp only [Multiset.coe_count, Multiset.count_filter]
    split_ifs with hc'
    · -- c' ≠ 0: count c' (map w univ) = List.count c' sortedParts
      rw [show Mw = Finset.univ.val.map (⇑w) from rfl, hw_def, Nat.Partition.toFinsupp]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Multiset.count_map]
      -- Goal: (univ.val.filter (fun i => c' = sortedParts.getD i 0)).card = List.count c' sortedParts
      have hlen : p.sortedParts.length ≤ n := by
        calc p.sortedParts.length = p.parts.card := by
              simp [Nat.Partition.sortedParts, Multiset.length_sort]
            _ ≤ p.parts.sum := by
              suffices h : ∀ (s : Multiset ℕ), (∀ x ∈ s, 0 < x) → s.card ≤ s.sum from
                h p.parts (fun x hx => p.parts_pos hx)
              intro s hs
              induction s using Multiset.induction with
              | empty => simp
              | cons a t ih =>
                rw [Multiset.card_cons, Multiset.sum_cons]
                have := hs a (Multiset.mem_cons_self a t)
                have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
                omega
            _ = n := p.parts_sum
      exact card_filter_getD_eq_count p.sortedParts n hlen c' hc'
    · -- c' = 0 (i.e., ¬(c' ≠ 0)): LHS = 0, RHS = List.count 0 sortedParts = 0
      push_neg at hc'
      subst hc'
      symm; rw [List.count_eq_zero]
      exact fun h => Nat.lt_irrefl 0 (p.parts_pos (hsorted_eq ▸ Multiset.mem_coe.mpr h))
  by_cases hc : c = 0
  · -- c = 0: both multisets have card n, and same non-zero filter, so same zero count
    subst hc
    have hcardM : M.card = n := by simp [M, hM_def]
    have hcardMw : Mw.card = n := by simp [Mw, hMw_def]
    -- count 0 s = s.card - (s.filter (· ≠ 0)).card
    have h_count_zero : ∀ s : Multiset ℕ,
        Multiset.count 0 s = s.card - (s.filter (· ≠ 0)).card := by
      intro s
      have h := Multiset.filter_add_not (· ≠ (0 : ℕ)) s
      have hc := congr_arg Multiset.card h
      rw [Multiset.card_add] at hc
      have hfilt : s.filter (fun a => ¬(a ≠ 0)) = s.filter (· = 0) :=
        Multiset.filter_congr (fun x _ => by simp)
      rw [hfilt] at hc
      have hcnt : (s.filter (· = 0)).card = Multiset.count 0 s := by
        rw [Multiset.filter_eq' s 0, Multiset.card_replicate]
      omega
    rw [h_count_zero M, h_count_zero Mw, hcardM, hcardMw]
    congr 1; rw [hparts.symm, hparts_w]
  · -- c ≠ 0: both filter to p.parts, so counts match
    have hfv : Multiset.count c (M.filter (· ≠ 0)) = Multiset.count c M :=
      Multiset.count_filter_of_pos hc
    have hfw : Multiset.count c (Mw.filter (· ≠ 0)) = Multiset.count c Mw :=
      Multiset.count_filter_of_pos hc
    rw [← hfv, ← hfw]
    exact congrArg (Multiset.count c) (hparts.symm.trans hparts_w.symm)

/-! ### Alternating Kostka identity

The key algebraic identity for the Frobenius formula proof. For partitions λ and ν of n:

  ∑_π sign(π) · m(sort(λ+ρ-e_π), ν) = sign(rev) · δ_{λ,ν}

where m(μ,ν) = spechtMultiplicity (Kostka number), ρ = (n-1,...,1,0),
e_π is the Vandermonde exponent vector for permutation π, and
sign(rev) = (-1)^{n(n-1)/2} is the sign of the reversal permutation.

The sign factor arises because `vandermondePoly` is defined as ∏_{i<j}(xⱼ-xᵢ),
while the book's Frobenius formula uses the alternant a_ρ = ∏_{i<j}(xᵢ-xⱼ),
which differs by sign(rev).

**Proof**: The Kostka matrix K_{μν} = spechtMultiplicity(μ,ν) is unitriangular
(1s on diagonal, 0 below) in the dominance order. This alternating sum computes
the signed inverse via the Leibniz-type expansion over Vandermonde permutations.
The proof requires the full upper-triangularity structure of Kostka numbers.
-/

/-- The exponent vector of the reversal permutation equals the rho shift. -/
private theorem permExponent_revPerm (n : ℕ) :
    permExponent n Fin.revPerm = rhoShift n := by
  ext j
  simp only [permExponent, rhoShift, Finsupp.coe_equivFunOnFinite_symm]
  -- rev is an involution, so rev⁻¹ = rev
  show (Fin.revPerm⁻¹ j).val = n - 1 - j.val
  have : Fin.revPerm⁻¹ = (Fin.revPerm (n := n)) := by
    ext i; simp [Fin.revPerm]
  rw [this]; simp [Fin.revPerm_apply]; omega

/-- The rho shift is componentwise ≤ la.toFinsupp + rhoShift. -/
private theorem rhoShift_le_toFinsupp_add_rhoShift {n : ℕ} (la : Nat.Partition n) :
    rhoShift n ≤ Nat.Partition.toFinsupp la + rhoShift n := by
  intro i
  simp only [Finsupp.add_apply, le_add_iff_nonneg_left]
  exact Nat.zero_le _

/-- When the exponent equals rhoShift, the difference la+ρ-ρ = la.toFinsupp. -/
private theorem toFinsupp_add_rhoShift_sub_rhoShift {n : ℕ} (la : Nat.Partition n) :
    Nat.Partition.toFinsupp la + rhoShift n - rhoShift n = Nat.Partition.toFinsupp la := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply]
  omega

/-- finsuppToPartition of la.toFinsupp gives back la. -/
private theorem finsuppToPartition_toFinsupp {n : ℕ} (la : Nat.Partition n)
    (hsum : ∑ i : Fin n, Nat.Partition.toFinsupp la i = n) :
    finsuppToPartition (Nat.Partition.toFinsupp la) hsum = la := by
  -- Show parts are equal as multisets
  have hsorted : (la.sortedParts : Multiset ℕ) = la.parts :=
    Multiset.sort_eq la.parts (· ≥ ·)
  have hlen : la.sortedParts.length ≤ n := by
    calc la.sortedParts.length
        ≤ la.sortedParts.sum := List.length_le_sum_of_one_le _ (fun i hi => by
          exact la.parts_pos (hsorted ▸ Multiset.mem_coe.mpr hi))
      _ = n := by
          have h := congrArg Multiset.sum hsorted
          rw [Multiset.sum_coe] at h; linarith [la.parts_sum]
  suffices h : (finsuppToPartition (Nat.Partition.toFinsupp la) hsum).parts = la.parts from
    Nat.Partition.ext h
  simp only [finsuppToPartition, Nat.Partition.ofSums_parts,
    Nat.Partition.toFinsupp, Finsupp.coe_equivFunOnFinite_symm]
  -- Goal: filter (· ≠ 0) (map (fun i => sortedParts.getD i 0) univ.val) = la.parts
  rw [← hsorted]
  -- Show: map getD over Fin n = sortedParts + zeros (as multiset), then filter removes zeros
  -- The mapped list = sortedParts ++ zeros
  set sp := la.sortedParts
  have hmap : (List.map (fun i : Fin n => sp.getD i.val 0) (List.finRange n)) =
      sp ++ List.replicate (n - sp.length) 0 := by
    apply List.ext_getElem
    · simp [List.length_finRange]; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange]
      simp only [List.getElem_finRange, Fin.val_cast, List.getD]
      by_cases hlt : i < sp.length
      · rw [List.getElem_append_left hlt, sp.getElem?_eq_getElem hlt, Option.getD_some]
      · push_neg at hlt
        rw [List.getElem_append_right (by omega), List.getElem_replicate,
            sp.getElem?_eq_none (by omega), Option.getD_none]
  rw [show Finset.univ.val = ↑(List.finRange n) from rfl,
      Multiset.map_coe, hmap]
  -- ↑(sp ++ replicate ...) = ↑sp + ↑(replicate ...)
  simp only [← Multiset.coe_add]
  rw [Multiset.filter_add]
  have hfsp : Multiset.filter (fun x => x ≠ 0) (↑sp : Multiset ℕ) = ↑sp :=
    Multiset.filter_eq_self.mpr (fun x hx => by
      exact Nat.pos_iff_ne_zero.mp (la.parts_pos (hsorted ▸ hx)))
  have hfrep : Multiset.filter (fun x => x ≠ 0)
      (↑(List.replicate (n - sp.length) 0) : Multiset ℕ) = 0 :=
    Multiset.filter_eq_nil.mpr (fun x hx => by
      simp only [ne_eq, not_not]
      exact (List.mem_replicate.mp (Multiset.mem_coe.mp hx)).2)
  rw [hfsp, hfrep, add_zero]

/-- For π ≠ rev and permExponent n π ≤ la.toFinsupp + rhoShift n, the sorted partition
`finsuppToPartition(la + ρ - e_π)` strictly dominates `la`.

This follows from the rearrangement inequality: since `la + ρ` is strictly decreasing
and `ρ` is the uniquely matched decreasing permutation of `{0,...,n-1}`, subtracting
any other permutation `e_π ≠ ρ` produces a vector whose sorted version has strictly
larger initial partial sums. -/
private theorem sorted_shifted_strict_dominates {n : ℕ}
    (la : Nat.Partition n)
    (π : Equiv.Perm (Fin n))
    (hπ : π ≠ Fin.revPerm)
    (hle : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n) :
    Nat.Partition.StrictDominates
      (finsuppToPartition
        (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
        (sum_shifted_sub_permExponent la π hle))
      la := by
  constructor
  · -- Dominance: ∀ k, (la.sortedParts.take k).sum ≤ (mu.sortedParts.take k).sum
    -- where mu = finsuppToPartition(la + ρ - e_π)
    -- This is the rearrangement inequality for partial sums
    sorry
  · -- Inequality: finsuppToPartition(la + ρ - e_π) ≠ la
    -- Since π ≠ rev, e_π ≠ ρ, so la + ρ - e_π ≠ la.toFinsupp componentwise
    -- After sorting, the partition differs because the multiset of values differs
    intro heq
    apply hπ
    -- If finsuppToPartition(la + ρ - e_π) = la, then the multisets of entries match.
    -- Since la + ρ is strictly decreasing, this forces e_π = ρ, so π = rev.
    -- Proof sketch: from heq, {u(j) - e_π(j)} = {u(j) - ρ(j)} as multisets where
    -- u = la + ρ is strictly decreasing. So there exists σ with u(j) - e_π(j) = u(σ(j)) - ρ(σ(j))
    -- for all j. Since u is strictly decreasing, this forces σ = id and e_π = ρ.
    sorry

/-- The alternating Kostka identity: the alternating sum of Kostka numbers over
Vandermonde permutations equals sign(rev) times the Kronecker delta.

Note: The sign factor arises because `vandermondePoly` uses `∏_{i<j}(x_j - x_i)` (matching
Mathlib's `Matrix.det_vandermonde`), while the book uses `∏_{i<j}(x_i - x_j)`. These differ
by `(-1)^{n(n-1)/2} = sign(Fin.revPerm)`. -/
theorem alternating_kostka_eq_delta {n : ℕ} (la nu : Nat.Partition n) :
    (∑ π : Equiv.Perm (Fin n),
      (Equiv.Perm.sign π : ℤ) •
        (if h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
         then ((spechtMultiplicity n
           (finsuppToPartition
             (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
             (sum_shifted_sub_permExponent la π h))
           nu : ℕ) : ℂ)
         else (0 : ℂ))) =
      (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) •
        (if la = nu then (1 : ℂ) else (0 : ℂ)) := by
  set rev := Fin.revPerm (n := n)
  by_cases hla_nu : la = nu
  · -- Case la = nu: prove fully using vanishing + diagonal
    subst hla_nu
    simp only [if_true]
    -- Isolate the rev permutation term
    have hrev_mem : rev ∈ Finset.univ := Finset.mem_univ _
    rw [Finset.sum_eq_add_sum_diff_singleton hrev_mem]
    have hrev_le : permExponent n rev ≤ Nat.Partition.toFinsupp la + rhoShift n :=
      permExponent_revPerm n ▸ rhoShift_le_toFinsupp_add_rhoShift la
    -- Non-rev terms vanish: for π ≠ rev, sort(la+ρ-e_π) ▷ la, so m(sort(...), la) = 0
    have hrest : (∑ π ∈ Finset.univ \ {rev},
        (Equiv.Perm.sign π : ℤ) •
          (if h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
           then ((spechtMultiplicity n
             (finsuppToPartition
               (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
               (sum_shifted_sub_permExponent la π h))
             la : ℕ) : ℂ)
           else (0 : ℂ))) = 0 := by
      -- For π ≠ rev, finsuppToPartition(la+ρ-e_π) strictly dominates la,
      -- so spechtMultiplicity = 0 by vanishing
      apply Finset.sum_eq_zero
      intro π hπ
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hπ
      -- Each summand is sign(π) • (either 0 or spechtMultiplicity = 0)
      by_cases hle : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
      · simp only [dif_pos hle]
        -- Need: spechtMultiplicity n (finsuppToPartition ...) la = 0
        -- because finsuppToPartition(la+ρ-e_π) strictly dominates la when π ≠ rev
        have hdom : Nat.Partition.StrictDominates
            (finsuppToPartition
              (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
              (sum_shifted_sub_permExponent la π hle))
            la := sorted_shifted_strict_dominates la π hπ hle
        rw [spechtMultiplicity_vanishing n _ la hdom]
        simp
      · simp [dif_neg hle]
    rw [hrest, add_zero]
    simp only [dif_pos hrev_le]
    -- la + ρ - ρ = la.toFinsupp
    have hsub : Nat.Partition.toFinsupp la + rhoShift n - permExponent n rev =
        Nat.Partition.toFinsupp la := by
      rw [permExponent_revPerm]; exact toFinsupp_add_rhoShift_sub_rhoShift la
    -- Generalize over the dependent sum proof
    suffices h : ∀ (v : Fin n →₀ ℕ) (hv : v = Nat.Partition.toFinsupp la)
        (hsum : ∑ i, v i = n),
        (Equiv.Perm.sign rev : ℤ) • ((spechtMultiplicity n
          (finsuppToPartition v hsum) la : ℕ) : ℂ) =
        (Equiv.Perm.sign rev : ℤ) • (1 : ℂ) by
      exact h _ hsub _
    intro v hv hsum
    subst hv
    rw [finsuppToPartition_toFinsupp]
    congr 1
    simp [spechtMultiplicity_diagonal]
  · -- Case la ≠ nu: requires the full orthogonality/norm argument from the book
    -- (Σ_π sign(π) m(sort(la+ρ-e_π), nu) = 0 requires genuine cancellation,
    -- not just term-by-term vanishing)
    simp only [if_neg hla_nu, smul_zero]
    sorry

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

**Proof** (Etingof, proof of Theorem 5.15.1):
1. Via Theorem 5.14.3 and symmetry, each coeff term = permModuleCharacter at a sorted partition
2. Via `youngsRule_character`: substitute χ_{U_μ} = Σ_ν m(μ,ν) χ_{V_ν}
3. Exchange summation: RHS = Σ_ν (Σ_π sign(π) m(sort(λ+ρ-π(ρ)), ν)) χ_{V_ν}(σ)
4. The inner sum = δ_{λ,ν} by `alternating_kostka_eq_delta`
5. Therefore RHS = χ_{V_λ}(σ) -/
-- Each coefficient term equals a Young's Rule expansion via symmetry + Thm 5.14.3.
private theorem coeff_eq_youngsRule_expansion
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (π : Equiv.Perm (Fin n))
    (h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n) :
    (MvPolynomial.coeff
      (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
      (cycleTypePsumProduct n σ) : ℂ) =
    ∑ nu : Nat.Partition n,
      ((spechtMultiplicity n
        (finsuppToPartition
          (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
          (sum_shifted_sub_permExponent la π h))
        nu : ℕ) : ℂ) * spechtModuleCharacter n nu σ := by
  -- Step 1: By symmetry, coeff at v = coeff at sorted partition
  rw [coeff_symmetric_eq_coeff_partition _ (cycleTypePsumProduct_isSymmetric n σ)]
  · -- Step 2: By Theorem 5.14.3, coeff at partition = permModuleCharacter
    rw [← permModuleCharacter_eq_coeff]
    -- Step 3: By Young's Rule, permModuleCharacter = sum of multiplicities × characters
    exact youngsRule_character n _ σ

-- Helper: push ℤ-smul through dite into a finite sum
private theorem smul_dite_sum {α : Prop} [Decidable α] {ι : Type*} [Fintype ι]
    (z : ℤ) (f : α → ι → ℂ) :
    z • (if h : α then ∑ i, f h i else (0 : ℂ)) =
      ∑ i, z • (if h : α then f h i else 0) := by
  by_cases hα : α
  · simp only [dif_pos hα, Finset.smul_sum]
  · simp only [dif_neg hα, smul_zero, Finset.sum_const_zero]

-- Helper: factor a constant out of smul-dite product
private theorem smul_dite_mul {α : Prop} [Decidable α]
    (z : ℤ) (f : α → ℂ) (c : ℂ) :
    z • (if h : α then f h * c else (0 : ℂ)) =
      (z • (if h : α then f h else 0)) * c := by
  by_cases hα : α
  · simp only [dif_pos hα, smul_mul_assoc]
  · simp only [dif_neg hα, smul_zero, zero_mul]

theorem spechtCharacter_eq_alternating_sum_permCharacter
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • spechtModuleCharacter n la σ =
      ∑ π : Equiv.Perm (Fin n),
        (Equiv.Perm.sign π : ℤ) • (if _h : permExponent n π ≤
            Nat.Partition.toFinsupp la + rhoShift n
          then (MvPolynomial.coeff
            (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
            (cycleTypePsumProduct n σ) : ℂ) else 0) := by
  -- Step 1: Each summand converts to a Young's Rule expansion via
  -- symmetry + Theorem 5.14.3 + Young's Rule
  have hcoeff : ∀ (π : Equiv.Perm (Fin n)),
      (Equiv.Perm.sign π : ℤ) •
        (if h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
          then (MvPolynomial.coeff
            (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
            (cycleTypePsumProduct n σ) : ℂ) else 0) =
      ∑ nu : Nat.Partition n,
        ((Equiv.Perm.sign π : ℤ) •
          (if h : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
            then ((spechtMultiplicity n
              (finsuppToPartition
                (Nat.Partition.toFinsupp la + rhoShift n - permExponent n π)
                (sum_shifted_sub_permExponent la π h))
              nu : ℕ) : ℂ)
            else 0)) * spechtModuleCharacter n nu σ := by
    intro π
    by_cases hle : permExponent n π ≤ Nat.Partition.toFinsupp la + rhoShift n
    · simp only [dif_pos hle]
      rw [coeff_eq_youngsRule_expansion n la σ π hle, Finset.smul_sum]
      congr 1; ext nu; rw [smul_mul_assoc]
    · simp only [dif_neg hle, smul_zero]
      exact (Finset.sum_eq_zero (fun nu _ => by simp)).symm
  -- Step 2: Rewrite each summand, then exchange sums
  conv_rhs => arg 2; ext π; rw [hcoeff π]
  rw [Finset.sum_comm]
  -- Step 3: Factor out χ_ν(σ) and apply alternating Kostka identity
  conv_rhs => arg 2; ext y; rw [← Finset.sum_mul, alternating_kostka_eq_delta la y]
  -- Goal: sign(rev) • χ_la = ∑ y, (sign(rev) • δ_{la,y}) * χ_y
  -- Factor out sign(rev) from the sum
  simp_rw [smul_mul_assoc]
  rw [← Finset.smul_sum]
  -- Goal: sign(rev) • χ_la = sign(rev) • ∑ y, δ_{la,y} * χ_y
  congr 1
  -- Goal: χ_la = ∑ y, δ_{la,y} * χ_y
  have hvan : ∀ y ∈ Finset.univ, y ≠ la →
      (if la = y then (1 : ℂ) else 0) * spechtModuleCharacter n y σ = 0 :=
    fun y _ hy => by simp [Ne.symm hy]
  rw [Finset.sum_eq_single la (fun b hb hne => hvan b hb hne)
    (fun h => absurd (Finset.mem_univ la) h)]
  simp

end

/-- **Theorem 5.15.1** (Frobenius character formula): The character of the Specht module
V_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals sign(rev) times the
coefficient of x^{λ+ρ} in Δ(x) · ∏_{m≥1} p_m(x)^{i_m}, where Δ is the Vandermonde
polynomial, ρ = (n-1, ..., 1, 0), and p_m is the power sum symmetric polynomial.

The sign(rev) factor arises because `vandermondePoly` uses `∏_{i<j}(x_j - x_i)`
(Mathlib convention), while the book uses `∏_{i<j}(x_i - x_j)`.
(Etingof Theorem 5.15.1) -/
theorem Theorem5_15_1
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) • spechtModuleCharacter n la σ =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la + rhoShift n)
        (vandermondePoly n * cycleTypePsumProduct n σ) := by
  rw [spechtCharacter_eq_alternating_sum_permCharacter,
      coeff_vandermonde_mul]

end Etingof
