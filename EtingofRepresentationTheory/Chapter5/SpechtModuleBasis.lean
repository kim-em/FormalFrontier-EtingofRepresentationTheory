import Mathlib
import EtingofRepresentationTheory.Chapter5.TabloidModule

/-!
# Specht Module Dimension Theorem

This file proves `finrank_spechtModule_eq_card_syt'`: dim V_λ = |SYT(λ)|,
combining:
- `finrank_spechtModule_ge_card_syt` (from TabloidModule.lean): dim V_λ ≥ |SYT(λ)|
- `finrank_spechtModule_le_card_syt` (proved here): dim V_λ ≤ |SYT(λ)|

The ≤ direction uses the tabloid-level straightening theorem
(`generalizedPolytabloidTab_mem_span_polytabloidTab`), which says every
generalized polytabloidTab lies in the ℂ-span of standard polytabloidTabs.
This implies the image ψ(V_λ) ⊆ span{polytabloidTab(T)}, giving the
dimension bound via injectivity of ψ on V_λ.

## Main results

* `Etingof.generalizedPolytabloidTab_mem_span_polytabloidTab` — straightening (sorry)
* `Etingof.finrank_spechtModule_le_card_syt` — dim V_λ ≤ |SYT(λ)|
* `Etingof.finrank_spechtModule_eq_card_syt'` — dim V_λ = |SYT(λ)|

## References

* James, "The Representation Theory of the Symmetric Groups", Chapter 7-8
* Fulton, "Young Tableaux", Chapter 7
-/

namespace Etingof

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}

/-! ### Tabloid-level straightening theorem

The straightening theorem: every generalized polytabloidTab ψ_σ lies in the
ℂ-span of the standard polytabloidTabs {e_T : T ∈ SYT(λ)}.

The proof requires a Garnir-type argument with well-founded induction on the
dominance ordering of tabloids. The standard approach (James Ch. 7-8):
1. If σ is column-standard, express ψ_σ via row-sorting and Garnir reductions
2. If σ has a column inversion, use the entry-level Garnir identity to express
   ψ_σ as a signed sum of ψ_{wσ} with strictly more dominant tabloids
3. Well-founded induction on the (finite) dominance partial order
-/

/-- The tabloid-level straightening theorem: for any permutation σ, the
generalized polytabloidTab ψ_σ = Σ_{q ∈ Q_λ} sign(q)·[q⁻¹σ] lies in the
ℂ-span of the standard polytabloidTabs {e_T : T ∈ SYT(λ)}.

This is the key ingredient for dim V_λ ≤ |SYT(λ)|. The proof requires
entry-level Garnir identities and well-founded induction on tabloid dominance.
See James Ch. 7-8 or Fulton Ch. 7 for the classical proof. -/
theorem generalizedPolytabloidTab_mem_span_polytabloidTab (σ : Equiv.Perm (Fin n)) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        polytabloidTab (n := n) (la := la) T)) := by
  sorry

/-! ### Dimension upper bound -/

/-- The image of V_λ under tabloidProjection is contained in the span of
standard polytabloidTabs. This follows from the straightening theorem:
every ψ(of(σ) * c_λ) = |P_λ| · ψ_{σ⁻¹} lies in span{e_T}. -/
private theorem tabloidProjection_spechtModule_le_span :
    Submodule.map (tabloidProjection (n := n) (la := la))
      ((SpechtModule n la).restrictScalars ℂ) ≤
    Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
      polytabloidTab (n := n) (la := la) T)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  rw [Submodule.mem_comap]
  -- v ∈ V_λ = ℂ[S_n] · c_λ, so v = a * c_λ for some a
  have hv' : v ∈ SpechtModule n la := hv
  rw [SpechtModule, Submodule.mem_span_singleton] at hv'
  obtain ⟨a, rfl⟩ := hv'
  -- ψ(a * c_λ) = Σ_{σ ∈ supp(a)} a(σ) · ψ(of(σ) * c_λ)
  -- Each ψ(of(σ) * c_λ) = |P_λ| · ψ_{σ⁻¹} ∈ span{e_T} by straightening
  show tabloidProjection (a • YoungSymmetrizer n la) ∈ _
  -- Decompose a • c_λ = Σ a(σ) • (of(σ) * c_λ)
  have key : a • YoungSymmetrizer n la =
      a.sum (fun g c => c • (MonoidAlgebra.of ℂ _ g * YoungSymmetrizer n la)) := by
    conv_lhs => rw [show a • YoungSymmetrizer n la =
        a * YoungSymmetrizer n la from rfl]
    conv_lhs => rw [← Finsupp.sum_single a]
    simp only [Finsupp.sum, Finset.sum_mul]
    congr 1; ext σ
    simp [MonoidAlgebra.of_apply]
  rw [key, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro σ _
  rw [map_smul, tabloidProjection_of_mul_youngSymmetrizer]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact generalizedPolytabloidTab_mem_span_polytabloidTab σ⁻¹

/-- dim V_λ ≤ |SYT(λ)|.

The proof uses:
1. ψ: V_λ → M^λ is injective (by irreducibility of V_λ, Theorem 5.12.2)
2. Image ψ(V_λ) ⊆ span{polytabloidTab(T)} (from the straightening theorem)
3. span{polytabloidTab(T)} has dimension ≤ |SYT(λ)| (at most |SYT| generators) -/
theorem finrank_spechtModule_le_card_syt :
    Module.finrank ℂ (SpechtModule n la) ≤
      Fintype.card (StandardYoungTableau n la) := by
  -- Define the restricted map ψ|_{V_λ}: V_λ → M^λ
  let ψ_res : (SpechtModule n la).restrictScalars ℂ →ₗ[ℂ] TabloidRepresentation n la :=
    (tabloidProjection (n := n) (la := la)).comp
      ((SpechtModule n la).restrictScalars ℂ).subtype
  -- ψ_res is injective
  have h_inj : Function.Injective ψ_res := by
    intro ⟨v, hv⟩ ⟨w, hw⟩ heq
    simp only [ψ_res, LinearMap.comp_apply, Submodule.subtype_apply] at heq
    have : (v : SymGroupAlgebra n) - w = 0 := by
      apply tabloidProjection_injective_on_spechtModule (n := n) (la := la)
      · exact ((SpechtModule n la).restrictScalars ℂ).sub_mem hv hw
      · rw [map_sub]; exact sub_eq_zero.mpr heq
    exact Subtype.ext (sub_eq_zero.mp this)
  -- dim(V_λ) = dim(range ψ_res) by injectivity
  have h_finrank_eq : Module.finrank ℂ (SpechtModule n la) =
      Module.finrank ℂ (LinearMap.range ψ_res) :=
    (LinearMap.finrank_range_of_inj h_inj).symm
  -- range ψ_res = image = Submodule.map ψ (V_λ.restrictScalars ℂ)
  have h_range : LinearMap.range ψ_res =
      Submodule.map (tabloidProjection (n := n) (la := la))
        ((SpechtModule n la).restrictScalars ℂ) := by
    simp only [ψ_res, LinearMap.range_comp, Submodule.range_subtype]
  -- image ⊆ span{e_T} by the straightening
  have hS_le := tabloidProjection_spechtModule_le_span (n := n) (la := la)
  -- dim(image) ≤ dim(span{e_T}) ≤ |SYT|
  calc Module.finrank ℂ (SpechtModule n la)
      = Module.finrank ℂ (LinearMap.range ψ_res) := h_finrank_eq
    _ = Module.finrank ℂ (Submodule.map (tabloidProjection (n := n) (la := la))
          ((SpechtModule n la).restrictScalars ℂ)) := by rw [h_range]
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
          polytabloidTab (n := n) (la := la) T))) :=
        Submodule.finrank_mono hS_le
    _ ≤ Fintype.card (StandardYoungTableau n la) :=
        finrank_range_le_card _

/-- dim V_λ = |SYT(λ)|.

This is the main dimension theorem: the Specht module V_λ has dimension
equal to the number of standard Young tableaux of shape λ.

Combines the two directions:
- ≥: from `finrank_spechtModule_ge_card_syt` (TabloidModule.lean)
- ≤: from `finrank_spechtModule_le_card_syt` (above, via straightening) -/
theorem finrank_spechtModule_eq_card_syt' (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Fintype.card (StandardYoungTableau n la) :=
  le_antisymm finrank_spechtModule_le_card_syt finrank_spechtModule_ge_card_syt

end

end Etingof
