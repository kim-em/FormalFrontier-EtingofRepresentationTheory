import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_14_1

/-!
# Theorem 5.14.3: Character Formula via Power Sums

The character of the permutation module U_λ evaluated at conjugacy class C_i
(where i = (i₁, i₂, ...) is the cycle type) is given by:

  χ_{U_λ}(C_i) = coefficient of x^λ in ∏_{m≥1} H_m(x)^{i_m}

where H_m(x) = Σ_{|α|=m} x^α is the complete homogeneous symmetric polynomial.

## Formalization approach

The character of the permutation module U_λ = ℂ[S_n/S_λ] at σ is the number
of cosets gS_λ fixed by σ (since U_λ is a permutation representation, the
character equals the number of fixed points).

The RHS uses `MvPolynomial.hsymm` (complete homogeneous symmetric polynomials)
from Mathlib. The product ∏_{m≥1} H_m(x)^{i_m} is expressed as the product
of H_m over each cycle length in σ's cycle type (including fixed points as
1-cycles).

## Mathlib correspondence

- `MvPolynomial.hsymm`: complete homogeneous symmetric polynomials
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

/-- The product ∏_{m≥1} H_m(x)^{i_m} where i = (i₁, i₂, ...) counts cycles of each length
in σ (including fixed points as 1-cycles). This is the generating function for
permutation module characters. -/
noncomputable def cycleTypeHsymmProduct (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) ℂ :=
  (σ.cycleType.map (MvPolynomial.hsymm (Fin n) ℂ)).prod *
    MvPolynomial.hsymm (Fin n) ℂ 1 ^ (n - σ.support.card)

/-- **Theorem 5.14.3** (Character formula via power sums): The character of the permutation
module U_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals the coefficient
of x^λ in ∏_{m≥1} H_m(x)^{i_m}, where H_m is the complete homogeneous symmetric
polynomial of degree m. (Etingof Theorem 5.14.3) -/
theorem Theorem5_14_3
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n la σ : ℂ) =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypeHsymmProduct n σ) := by
  sorry

end Etingof
