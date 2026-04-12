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

* `Etingof.generalizedPolytabloidTab_mem_span_polytabloidTab` — straightening (2 sorries)
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

The proof proceeds in two stages:
1. **Column standardization**: Reduce to column-standard σ using Q_λ-equivariance.
   For any σ, there exists q₀ ∈ Q_λ such that q₀σ is column-standard, and
   ψ_σ = sign(q₀)·ψ_{q₀σ} by `generalizedPolytabloidTab_col_mul`.
2. **Column-standard straightening**: For column-standard σ, show ψ_σ ∈ span{e_T}
   using the tabloid-level Garnir identity (`garnirAnnihilate_tabloid`) and
   well-founded induction on the dominance order. This is the core mathematical
   content (James Ch. 7-8, Fulton Ch. 7).
-/

/-- For any permutation σ, there exists q₀ ∈ Q_λ such that q₀ * σ is
column-standard (entries increase down each column). The column-sorting
permutation permutes entries within each column, hence lies in Q_λ. -/
private theorem exists_column_standard_mul (σ : Equiv.Perm (Fin n)) :
    ∃ q₀ ∈ ColumnSubgroup n la, isColumnStandard' n la (q₀ * σ) := by
  sorry

/-- For column-standard σ, the generalized polytabloidTab ψ_σ lies in the
span of standard polytabloidTabs. This is the core of the straightening
theorem, requiring the tabloid-level Garnir identity and well-founded
induction on the dominance order of tabloids.

Proof sketch (James Ch. 7-8):
- By `column_standard_coset_has_syt'`, σ = p · σ_T for some SYT T and p ∈ P_λ.
- If p = 1, then ψ_σ = e_T ∈ span{e_T}. ✓
- If p ≠ 1, σ has a "row descent" (entries in a row not increasing left to right).
  Apply `garnirAnnihilate_tabloid` with the Garnir set for this descent to each
  term of ψ_σ. After regrouping, ψ_σ equals a ℂ-linear combination of elements
  supported on strictly more dominant tabloids. By well-founded induction on the
  finite dominance order, these are in span{e_T}. -/
private theorem polytabloidTab_column_standard_in_span
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        polytabloidTab (n := n) (la := la) T)) := by
  sorry

/-- The tabloid-level straightening theorem: for any permutation σ, the
generalized polytabloidTab ψ_σ = Σ_{q ∈ Q_λ} sign(q)·[q⁻¹σ] lies in the
ℂ-span of the standard polytabloidTabs {e_T : T ∈ SYT(λ)}.

This is the key ingredient for dim V_λ ≤ |SYT(λ)|. The proof reduces to the
column-standard case via Q_λ-equivariance, then uses the Garnir identity. -/
theorem generalizedPolytabloidTab_mem_span_polytabloidTab (σ : Equiv.Perm (Fin n)) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        polytabloidTab (n := n) (la := la) T)) := by
  -- Step 1: Find q₀ ∈ Q_λ such that q₀ * σ is column-standard
  obtain ⟨q₀, hq₀, hcs⟩ := exists_column_standard_mul (la := la) σ
  -- Step 2: ψ_σ = sign(q₀⁻¹) · ψ_{q₀σ} by Q_λ-equivariance
  -- From ψ_{q₀σ} = sign(q₀) · ψ_σ, we get ψ_σ = sign(q₀)⁻¹ · ψ_{q₀σ}
  -- Since sign(q₀) ∈ {±1}, sign(q₀)⁻¹ = sign(q₀)
  have hq₀σ_mem := polytabloidTab_column_standard_in_span (q₀ * σ) hcs
  have hcol := generalizedPolytabloidTab_col_mul q₀ hq₀ σ
  -- ψ_{q₀σ} = sign(q₀) · ψ_σ, so ψ_σ = sign(q₀) · ψ_{q₀σ}
  -- (because sign(q₀)² = 1, i.e., sign(q₀) · sign(q₀) · ψ_σ = ψ_σ)
  have hsign_sq : ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) *
      ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) = 1 := by
    have : Equiv.Perm.sign q₀ = 1 ∨ Equiv.Perm.sign q₀ = -1 :=
      Int.units_eq_one_or q₀.sign
    rcases this with h | h <;> simp [h]
  rw [hcol] at hq₀σ_mem
  -- ψ_σ = sign(q₀) · ψ_{q₀σ} and sign(q₀) · ψ_{q₀σ} = sign(q₀) · (sign(q₀) · ψ_σ)
  -- So we need: sign(q₀) · ψ_{q₀σ} ∈ span ← from hq₀σ_mem smul
  -- Actually, ψ_{q₀σ} ∈ span implies sign(q₀) · ψ_{q₀σ} ∈ span (span is a submodule)
  -- And ψ_{q₀σ} = sign(q₀) · ψ_σ, so sign(q₀) · ψ_{q₀σ} = sign(q₀)² · ψ_σ = ψ_σ
  -- But we need to go the other way: from ψ_{q₀σ} ∈ span to ψ_σ ∈ span
  -- ψ_{q₀σ} = sign(q₀) · ψ_σ ∈ span, and sign(q₀)·(sign(q₀)·ψ_σ) = ψ_σ ∈ span
  have : generalizedPolytabloidTab (n := n) (la := la) σ =
      ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) •
        generalizedPolytabloidTab (n := n) (la := la) (q₀ * σ) := by
    rw [hcol, smul_smul, hsign_sq, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (polytabloidTab_column_standard_in_span (q₀ * σ) hcs)

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
