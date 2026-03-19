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

/-! ## Helper infrastructure for Theorem 5.14.3

### Key types and constructions

The proof proceeds by showing both sides count "monochromatic colorings":
an assignment of each orbit of σ (cycles + fixed points) to a row of λ,
such that the total number of elements assigned to row j equals λ_j.

**LHS path**: A coset gS_λ is fixed by σ iff g⁻¹σg ∈ S_λ, i.e., σ preserves
each row under g's relabeling. This is equivalent to a monochromatic coloring.

**RHS path**: The product ∏ p_{|c|}(x) = ∏ (Σᵢ xᵢ^{|c|}) expands as a sum
over assignments of cycles to rows. The coefficient of x^λ counts assignments
with correct row sizes.
-/

/-- The "full cycle type" of σ, including fixed points as 1-cycles.
This is σ.cycleType (which only lists cycles of length ≥ 2) plus
(n - σ.support.card) copies of 1 (for fixed points). -/
noncomputable def fullCycleType (n : ℕ) (σ : Equiv.Perm (Fin n)) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (n - σ.support.card) 1

/-- The sum of the full cycle type equals n. -/
theorem fullCycleType_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fullCycleType n σ).sum = n := by
  simp only [fullCycleType, Multiset.sum_add, Multiset.sum_replicate]
  have h1 := σ.sum_cycleType
  have h2 : σ.support.card ≤ n :=
    (σ.support.card_le_univ).trans_eq (Fintype.card_fin n)
  -- Goal should be: σ.cycleType.sum + (n - σ.support.card) • 1 = n
  simp only [smul_eq_mul, mul_one] at *
  omega

/-- A monochromatic coloring: an assignment of each orbit (indexed by position in the
full cycle type multiset) to a row (indexed by Fin n), such that the total size of
orbits assigned to row j equals λ_j. -/
noncomputable def MonochromaticColoring (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin n //
    ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) =
      la.sortedParts.getD j 0 }

/-- The cycleTypePsumProduct can be rewritten using the full cycle type. -/
theorem cycleTypePsumProduct_eq_fullCycleType (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cycleTypePsumProduct n σ =
      ((fullCycleType n σ).map (MvPolynomial.psum (Fin n) ℂ)).prod := by
  unfold cycleTypePsumProduct fullCycleType
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]

/-- Each psum polynomial equals a sum of monomials: p_m = ∑ i, monomial (single i m) 1. -/
theorem psum_eq_sum_monomial (m : ℕ) :
    MvPolynomial.psum (Fin n) ℂ m = ∑ i : Fin n, MvPolynomial.monomial (Finsupp.single i m) 1 := by
  simp only [MvPolynomial.psum, MvPolynomial.X_pow_eq_monomial]

/-- The coefficient of x^λ in a product of psum polynomials equals the number of
monochromatic colorings. This is the polynomial side of the bijection. -/
-- Helper: the finsupp sum condition is equivalent to the pointwise condition
private lemma finsupp_sum_single_iff (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin n) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) =
      Nat.Partition.toFinsupp la) ↔
    (∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) =
      la.sortedParts.getD j 0) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
      Nat.Partition.toFinsupp, Finsupp.coe_equivFunOnFinite_symm] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
      Nat.Partition.toFinsupp, Finsupp.coe_equivFunOnFinite_symm]
    rw [← Finset.sum_filter]
    exact hall j

theorem coeff_psum_prod_eq_card_colorings (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypePsumProduct n σ) =
      Nat.card (MonochromaticColoring n la σ) := by
  rw [cycleTypePsumProduct_eq_fullCycleType]
  -- Convert multiset product to list product to Fin-indexed product
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  -- Expand each psum as a sum of monomials, distribute, collapse to single monomial
  simp_rw [psum_eq_sum_monomial]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  -- Extract coefficients
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  -- Goal: ↑(filter card) = ↑(Nat.card MonochromaticColoring)
  norm_cast
  -- Construct equiv between MonochromaticColoring and the filter
  have equiv : MonochromaticColoring n la σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[↑i])) =
          Nat.Partition.toFinsupp la } := by
    unfold MonochromaticColoring
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff n la σ f).symm)
  rw [Nat.card_congr equiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  congr

/-- The number of fixed cosets equals the number of monochromatic colorings.
This is the group action side of the bijection.

A coset gS_λ is fixed by σ iff g⁻¹σg ∈ RowSubgroup, meaning each cycle of σ
lies in one row under g's relabeling. The coloring sends each cycle to its row.

The proof constructs a bijection via σ-invariant row colorings:
- Forward: fixed coset aP_λ ↦ coloring c(i) = rowOfPos(a⁻¹(i))
- Backward: valid coloring → coset of any permutation implementing it -/
theorem fixedCosets_eq_card_colorings (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    permModuleCharacter n la σ = Nat.card (MonochromaticColoring n la σ) := by
  sorry

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
  rw [coeff_psum_prod_eq_card_colorings, ← fixedCosets_eq_card_colorings]

end Etingof
