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

/-! ### Young's Rule (character decomposition)

The Frobenius character formula requires **Young's Rule**, which states that
the permutation module U_μ decomposes as:

  U_μ ≅ ⊕_ν K_{ν,μ} · V_ν

where K_{ν,μ} are the **Kostka numbers** (the number of semistandard Young tableaux
of shape ν with content μ), and V_ν is the Specht module.

In terms of characters:

  χ_{U_μ}(σ) = Σ_ν K_{ν,μ} · χ_{V_ν}(σ)

**Proof dependencies:**
1. **Maschke's theorem** (in Mathlib): ℂ[S_n]-modules are semisimple → U_μ = ⊕ V_ν^{⊕m_ν}
2. **Schur's lemma** (in Mathlib): m_ν = dim Hom(U_μ, V_ν)
3. **Proposition 5.14.1** (proved): Hom(U_μ, V_ν) = 0 when μ > ν, dim = 1 when μ = ν
4. **Kostka number interpretation**: m_ν = K_{ν,μ} (requires connecting Hom-space dimension
   to semistandard Young tableaux count)

**What's missing**: The bridge from "dim Hom = K_{ν,μ}" to the character identity. This requires
formalizing the semisimple decomposition in terms of characters and connecting multiplicities
to Hom-space dimensions. The infrastructure exists in Mathlib (`IsSemisimpleModule`,
`isotypicComponent`) but the specific application to ℂ[S_n] representations and the
connection to Kostka numbers has not been formalized.

Once Young's Rule is proved as characters, the Frobenius formula follows by:
1. Substituting χ_{U_μ} = Σ_ν K_{ν,μ} χ_{V_ν} into the alternating sum
2. Using K_{ν,ν} = 1, K_{ν,μ} = 0 for μ < ν (upper triangularity)
3. The alternating sum Σ_π sign(π) K_{ν, sort(λ+ρ-π(ρ))} = δ_{ν,λ}
   (inverse of upper-triangular matrix with 1s on diagonal)
-/

/-- **Key representation-theoretic step**: The alternating sum
  Σ_π sign(π) · coeff(x^{λ+ρ-π(ρ)}, ∏ p_m^{i_m})
equals the Specht module character χ_{V_λ}(σ).

This is the core of the Frobenius formula proof and requires Young's Rule
(decomposition of permutation modules into Specht modules via Kostka numbers)
plus the alternating sum cancellation identity. See the detailed proof strategy
in the module docstring above.

**Blocked on**: Young's Rule character identity — the decomposition
  χ_{U_μ} = Σ_ν K_{ν,μ} · χ_{V_ν}
requires connecting Mathlib's semisimple module infrastructure to the specific
representation theory of S_n. Key Mathlib components:
- `IsSemisimpleModule k[G] V` (Maschke's theorem)
- `isotypicComponent` (decomposition into isotypic components)
- `Theorem5_12_2_irreducible` (V_λ is simple)
- `Proposition5_14_1_vanishing/diagonal` (Hom-space dimensions)
-/
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
