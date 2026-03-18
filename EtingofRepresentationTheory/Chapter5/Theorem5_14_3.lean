import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_14_1

/-!
# Theorem 5.14.3: Character Formula via Power Sums

The character of the permutation module U_λ evaluated at conjugacy class C_i
(where i = (i₁, i₂, ...) is the cycle type) is given by:

  χ_{U_λ}(C_i) = coefficient of x^λ in ∏_{m≥1} p_m(x)^{i_m}

where p_m(x) = Σᵢ xᵢᵐ is the power sum symmetric polynomial.

## Formalization approach

The character of the permutation module U_λ = ℂ[S_n/S_λ] at σ is the number
of cosets gS_λ fixed by σ (since U_λ is a permutation representation, the
character equals the number of fixed points).

A coset gS_λ is fixed by σ iff each cycle of σ lies entirely within one row
of the partition λ (under the relabeling given by g). This "monochromatic"
condition is captured exactly by the power sum polynomial p_m = Σᵢ xᵢᵐ,
where each term xᵢᵐ represents placing an entire m-cycle into row i.

**Note**: An earlier version of this file incorrectly used `MvPolynomial.hsymm`
(complete homogeneous symmetric polynomials). The hsymm polynomial
H_m = Σ_{|α|=m} x^α allows distributing m elements across multiple rows,
but cycles must go to a single row. The power sum p_m = Σᵢ xᵢᵐ correctly
enforces this constraint.

## Mathlib correspondence

- `MvPolynomial.psum`: power sum symmetric polynomials p_m = Σᵢ xᵢᵐ
- `Equiv.Perm.cycleType`: cycle type as multiset (excluding fixed points)
- `MvPolynomial.coeff`: coefficient extraction
- `MulAction.fixedBy`: fixed points of a group element
-/

namespace Etingof

/-- Convert a partition's sorted parts to a finsupp for MvPolynomial coefficient extraction.
Position i maps to the i-th largest part (or 0 if i ≥ number of parts).
This encodes x^λ = x_0^{λ_1} · x_1^{λ_2} · ... -/
noncomputable def Nat.Partition.toFinsupp {n : ℕ} (la : Nat.Partition n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => la.sortedParts.getD i 0)

/-- The character of the permutation module U_λ at a permutation σ, defined as the number
of left cosets gS_λ fixed by left multiplication by σ. For permutation representations,
this equals the trace of the representation matrix. -/
noncomputable def permModuleCharacter (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  Nat.card (MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) σ)

/-- The product ∏_{m≥1} p_m(x)^{i_m} where i = (i₁, i₂, ...) counts cycles of each length
in σ (including fixed points as 1-cycles). The power sum polynomial p_m = Σᵢ xᵢᵐ ensures
each cycle is assigned to a single row, which is the correct generating function for
permutation module characters.

**Previous version used hsymm (H_m), which is incorrect**: H_m allows distributing m
elements across rows, but each cycle must go entirely to one row. -/
noncomputable def cycleTypePsumProduct (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) ℂ :=
  (σ.cycleType.map (MvPolynomial.psum (Fin n) ℂ)).prod *
    MvPolynomial.psum (Fin n) ℂ 1 ^ (n - σ.support.card)

/-- **Theorem 5.14.3** (Character formula via power sums): The character of the permutation
module U_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals the coefficient
of x^λ in ∏_{m≥1} p_m(x)^{i_m}, where p_m is the power sum symmetric polynomial
of degree m. (Etingof Theorem 5.14.3)

## Proof sketch

The LHS counts cosets gS_λ fixed by σ. A coset gS_λ is fixed by σ iff each cycle
of σ is monochromatic under the row coloring induced by g (i.e., all elements of
each cycle lie in the same row of the partition λ).

The RHS counts functions f : {cycles of σ} → {rows} such that the total size of
cycles assigned to row i equals λ_i. This is because p_m = Σᵢ xᵢᵐ, so the product
∏_c p_{|c|} = ∏_c (Σᵢ xᵢ^{|c|}) expands to Σ_f ∏_c x_{f(c)}^{|c|}, and the
coefficient of x^λ extracts exactly those assignments with correct row sizes.

These two counts are equal via a bijection between fixed cosets and valid
cycle-to-row assignments. -/
theorem Theorem5_14_3
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n la σ : ℂ) =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypePsumProduct n σ) := by
  sorry

end Etingof
