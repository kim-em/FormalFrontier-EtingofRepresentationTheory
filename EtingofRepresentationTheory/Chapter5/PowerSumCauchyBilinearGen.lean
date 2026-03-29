import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinear
import EtingofRepresentationTheory.Chapter5.PermDiagonalTrace

/-!
# Generalized Power Sum Cauchy Identity: N ≠ n

This file generalizes the bilinear Cauchy identity infrastructure from `PowerSumCauchyBilinear`
to the case where the number of variables N may differ from the permutation group size n.

The original `CycleColoring n α σ` colors cycles of σ ∈ S_n with Fin n colors.
Here `CycleColoringGen N n α σ` colors cycles of σ ∈ S_n with Fin N colors.

This generalization is needed for the Weyl character formula (Theorem 5.22.1),
where `charValue` uses N variables (dim V) with S_n permutations (n = |λ|).

## Main definitions

* `CycleColoringGen N n α σ`: Cycle coloring with Fin N colors for σ ∈ S_n
* `NNMatrixWithMarginsGen N n α β`: N×N non-negative integer matrices with row sums α,
  column sums β, and entries bounded by n+1

## Main results

* `coeff_powerSumCycleProduct_eq_card`: The coefficient of x^α in the power sum cycle
  product equals the number of generalized cycle colorings
* `powerSum_bilinear_coeff_gen`: The generalized bilinear Cauchy identity (sorry'd)
-/

open MvPolynomial Finset

namespace Etingof

noncomputable section

variable (N : ℕ) {n : ℕ}

/-! ### Generalized cycle colorings -/

/-- A generalized cycle coloring assigns each cycle of σ ∈ S_n a "color" from Fin N
(where N may differ from n), such that the total cycle lengths for each color match α.
This generalizes `CycleColoring` from the case N = n. -/
def CycleColoringGen (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin N //
    ∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) = α j }

instance (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CycleColoringGen N α σ) := by
  unfold CycleColoringGen
  exact Subtype.fintype _

/-- The finsupp sum condition is equivalent to the pointwise condition for generalized
cycle colorings. -/
private lemma finsupp_sum_single_iff_gen (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin N) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

/-- Each psum polynomial in N variables over ℚ equals a sum of monomials. -/
private theorem psum_eq_sum_monomial_gen (m : ℕ) :
    MvPolynomial.psum (Fin N) ℚ m =
    ∑ i : Fin N, MvPolynomial.monomial (Finsupp.single i m) 1 := by
  simp only [MvPolynomial.psum, MvPolynomial.X_pow_eq_monomial]

/-- The MvPolynomial coefficient of powerSumCycleProduct N σ at a composition α
equals the number of generalized cycle colorings. -/
theorem coeff_powerSumCycleProduct_eq_card (α : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (powerSumCycleProduct N σ) =
    ↑(Fintype.card (CycleColoringGen N α σ)) := by
  unfold powerSumCycleProduct
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial_gen]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast
  have equiv : CycleColoringGen N α σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α } := by
    unfold CycleColoringGen
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff_gen N α σ f).symm)
  rw [show Fintype.card (CycleColoringGen N α σ) = Fintype.card
      { f : Fin (fullCycleType n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

/-! ### Generalized non-negative integer matrices -/

/-- A non-negative integer N×N matrix with prescribed row and column sums.
Entries are bounded by `n + 1` (since row sums α_i ≤ n) to ensure finiteness.
This generalizes `NNMatrixWithMargins` from the case N = n. -/
def NNMatrixWithMarginsGen (α β : Fin N → ℕ) : Type :=
  { K : Fin N → Fin N → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

instance (α β : Fin N → ℕ) : Fintype (NNMatrixWithMarginsGen N (n := n) α β) :=
  Subtype.fintype _

/-! ### Generalized double counting and bilinear identity -/

/-- **Generalized double counting lemma**: The total number of (σ, f, g) triples
(where σ ∈ S_n, f colors cycles with Fin N colors matching α, g matches β)
equals n! times the number of N×N matrices with margins (α, β).

This generalizes `double_counting` from the case N = n. The proof follows the
same structure but with N×N matrices instead of n×n matrices. -/
theorem double_counting_gen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoringGen N α σ) * Fintype.card (CycleColoringGen N β σ) =
    n.factorial * Fintype.card (NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) := by
  sorry

/-- **Generalized Power Sum Cauchy Identity** (coefficient-level bilinear version):

For α β : Fin N →₀ ℕ with total degree n,

  ∑_{σ∈Sₙ} [x^α](P_σ) · [x^β](P_σ) = n! · [x^α y^β](∏_{i,j∈[N]} 1/(1-xᵢyⱼ))

where P_σ = powerSumCycleProduct N σ is the power sum product with N variables.

This generalizes `powerSum_bilinear_coeff` from the case N = n. -/
theorem powerSum_bilinear_coeff_gen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (powerSumCycleProduct N σ) : ℚ) *
      (MvPolynomial.coeff β (powerSumCycleProduct N σ) : ℚ)) =
    (Nat.factorial n : ℚ) * MvPowerSeries.coeff (bilinExponent N (⇑α) (⇑β))
      (fullCauchyProd N ℚ) := by
  -- Rewrite each MvPolynomial coefficient as card of CycleColoringGen
  simp_rw [coeff_powerSumCycleProduct_eq_card]
  sorry

end

end Etingof
