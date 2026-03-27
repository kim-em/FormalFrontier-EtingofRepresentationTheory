import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_14_3

/-!
# Permutation-Diagonal Trace Formula on Tensor Powers

For σ ∈ S_n acting on V^⊗n (V = k^N), the generating function of σ-fixed
standard basis vectors, weighted by monomial x^{weight}, equals the power sum
product indexed by the cycle type of σ:

  ∑_{f : f∘σ = f} ∏_j x_{f(j)} = ∏_{l ∈ cycleType(σ)} p_l(x₁,...,x_N)

This is a key step in the trace-based proof of the Weyl character formula
(Theorem 5.22.1).
-/

open MvPolynomial Finset

namespace Etingof

noncomputable section

variable {n : ℕ} (N : ℕ)

/-- The generating function of σ-fixed N-colorings of Fin n.
For each coloring f : Fin n → Fin N fixed by σ (i.e., f ∘ σ = f),
we sum the monomial ∏_j X_{f(j)}. -/
def permTracePoly (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin N) ℚ :=
  ∑ f ∈ (univ.filter fun f : Fin n → Fin N => ∀ j, f (σ j) = f j),
    ∏ j : Fin n, X (f j)

/-- The power sum product with N variables for the full cycle type of σ. -/
def powerSumCycleProduct (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin N) ℚ :=
  ((fullCycleType n σ).map (psum (Fin N) ℚ)).prod

/-! ### Helper: fiberwise product decomposition -/

/-- A product over Fin n, where the function depends only on the orbit index π,
equals a product over orbits with the appropriate exponent. -/
private lemma prod_X_comp_eq_prod_pow
    {L : ℕ} (π : Fin n → Fin L) (lens : Fin L → ℕ)
    (hπ_card : ∀ i, (univ.filter (fun k => π k = i)).card = lens i)
    (g : Fin L → Fin N) :
    ∏ j : Fin n, X (g (π j)) =
      (∏ i : Fin L, X (g i) ^ lens i : MvPolynomial (Fin N) ℚ) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin L)))
    (g := π) (fun _ _ => mem_univ _)
    (f := fun j => (X (g (π j)) : MvPolynomial (Fin N) ℚ))]
  apply Finset.prod_congr rfl
  intro i _
  have hsub : ∀ j ∈ univ.filter (fun k => π k = i),
      (X (g (π j)) : MvPolynomial (Fin N) ℚ) = X (g i) := by
    intro j hj; rw [show π j = i from (mem_filter.mp hj).2]
  rw [Finset.prod_congr rfl hsub, Finset.prod_const, hπ_card]

/-! ### Bijection between fixed colorings and orbit functions -/

/-- A σ-fixed coloring is constant on SameCycle orbits. -/
private lemma fixed_coloring_const_on_orbit {σ : Equiv.Perm (Fin n)}
    {f : Fin n → Fin N} (hf : ∀ j, f (σ j) = f j)
    {x y : Fin n} (h : σ.SameCycle x y) : f x = f y := by
  obtain ⟨i, rfl⟩ := h
  induction i using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show (↑k + 1 : ℤ) = 1 + ↑k from by ring, zpow_add, zpow_one,
      Equiv.Perm.mul_apply, hf, ih]
  | pred k ih =>
    rw [show (-(↑k : ℤ) - 1 : ℤ) = -1 + -(↑k : ℤ) from by ring, zpow_add, zpow_neg_one,
      Equiv.Perm.mul_apply]
    have hinv : f (σ⁻¹ ((σ ^ (-(↑k : ℤ))) x)) = f ((σ ^ (-(↑k : ℤ))) x) := by
      conv_rhs => rw [← Equiv.apply_symm_apply σ ((σ ^ (-(↑k : ℤ))) x)]
      exact (hf _).symm
    rw [hinv, ih]

/-! ### Main theorem -/

/-- **Permutation-diagonal trace formula**: The generating function of σ-fixed
N-colorings equals the power sum product indexed by the full cycle type.

This is step D of the trace-based approach to the Weyl character formula:
for σ ∈ S_n acting on (k^N)^{⊗n}, the trace weighted by monomials x^μ
equals ∏_{l ∈ cycle-type(σ)} p_l(x₁,...,x_N). -/
theorem permTracePoly_eq_powerSumCycleProduct (σ : Equiv.Perm (Fin n)) :
    permTracePoly N σ = powerSumCycleProduct N σ := by
  classical
  obtain ⟨π, hπ_orbit, hπ_card⟩ := exists_orbIdx σ
  -- π is surjective (orbit fibers are nonempty since cycle lengths ≥ 1)
  have hπ_surj : Function.Surjective π := by
    intro i; by_contra h; push_neg at h
    have h1 := hπ_card i
    have h2 : (univ.filter (fun k : Fin n => π k = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; exact h k
    rw [h2] at h1
    have := fullCycleType_pos σ _
      (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
    omega
  have hrep : ∀ i, π ((hπ_surj i).choose) = i :=
    fun i => (hπ_surj i).choose_spec
  -- Step 1: Expand RHS
  unfold powerSumCycleProduct
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum]
  rw [prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  -- Step 2: Show LHS = same sum, via bijection g ↦ g ∘ π
  unfold permTracePoly
  symm
  apply Finset.sum_nbij (fun g => g ∘ π)
  -- Maps into the filter (g ∘ π is σ-fixed since σ j and j are in the same orbit)
  · intro g _; simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
    intro j
    have : π (σ j) = π j :=
      (hπ_orbit _ _).mpr ((Equiv.Perm.SameCycle.refl σ j).apply_left)
    rw [this]
  -- Injective (since π is surjective)
  · intro g₁ _ g₂ _ h
    funext i; obtain ⟨k, hk⟩ := hπ_surj i
    have := congr_fun h k
    simp only [Function.comp_apply] at this
    rwa [hk] at this
  -- Surjective (every σ-fixed coloring factors through π)
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf
    exact ⟨fun i => f ((hπ_surj i).choose), mem_univ _, by
      funext j; simp only [Function.comp_apply]
      exact fixed_coloring_const_on_orbit N hf
        ((hπ_orbit _ _).mp (hrep (π j)))⟩
  -- Summand equality: ∏_i X(g i)^{list[i]} = ∏_j X((g∘π) j)
  · intro g _
    exact (prod_X_comp_eq_prod_pow N π
      (fun i => (fullCycleType n σ).toList[↑i]) hπ_card g).symm

end

end Etingof
