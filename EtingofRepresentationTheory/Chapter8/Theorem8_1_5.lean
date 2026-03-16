import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Theorem 8.1.5: Equivalent characterizations of injective modules

The following properties of I are equivalent:

(i) If α : N → M is an injective morphism and ν : N → I is any morphism, then there exists
a morphism μ : M → I such that μ ∘ α = ν.

(ii) Any injective morphism α : I → M splits; i.e., there exists μ : M → I such that
μ ∘ α = id.

(iii) The functor Hom_A(?, I) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Injective` captures condition (i) (the extension property). Baer's criterion
(`Module.Baer`) provides an equivalent characterization via extension from ideals.

- `Module.Injective` : the extension property (condition (i))
- `Module.Baer.iff_injective` : equivalence with Baer's criterion
-/

universe u v

/-- **Part (i) ↔ (ii)**: I is injective (extension property) if and only if every injection
from I splits.
(Etingof Theorem 8.1.5, equivalence of conditions (i) and (ii)) -/
theorem Etingof.Theorem_8_1_5_i_iff_ii
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : I →ₗ[R] M), Function.Injective f →
          ∃ g : M →ₗ[R] I, g.comp f = LinearMap.id) := by
  constructor
  · -- Forward: Injective → injections from I split
    intro hI M _ _ f hf
    obtain ⟨g, hg⟩ := hI.out f hf LinearMap.id
    exact ⟨g, LinearMap.ext hg⟩
  · -- Backward: injections from I split → Injective
    -- Use pushout construction: given injective α : X → Y and g : X → I,
    -- form P = (I × Y) / K where K = {(g(x), -α(x)) | x ∈ X}
    intro h
    constructor
    intro X Y _ _ _ _ α hα g
    set K : Submodule R (I × Y) := LinearMap.range (g.prod (-α))
    set j := K.mkQ ∘ₗ LinearMap.inl R I Y with j_def
    set k := K.mkQ ∘ₗ LinearMap.inr R I Y with k_def
    -- j is injective: if j(a) = j(b) then (a-b, 0) ∈ K, forcing a = b
    have hj : Function.Injective j := by
      intro a b hab
      simp only [j_def, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply] at hab
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hab
      -- hab : (a, 0) - (b, 0) ∈ K
      simp only [Prod.mk_sub_mk, sub_zero] at hab
      obtain ⟨x, hx⟩ := hab
      have h2 : (-α) x = 0 := congr_arg Prod.snd hx
      simp only [LinearMap.neg_apply, neg_eq_zero] at h2
      have h3 : x = 0 := hα (by rw [h2, map_zero])
      have h1 : g x = a - b := congr_arg Prod.fst hx
      rw [h3, map_zero] at h1
      exact sub_eq_zero.mp h1.symm
    -- By hypothesis, j splits
    obtain ⟨r, hr⟩ := h j hj
    -- Key: j(g(x)) = k(α(x)) because (g(x), 0) - (0, α(x)) = (g(x), -α(x)) ∈ K
    have key : ∀ x, j (g x) = k (α x) := by
      intro x
      simp only [j_def, k_def, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      show (g x, (0 : Y)) - ((0 : I), α x) ∈ K
      simp only [Prod.mk_sub_mk, sub_zero, zero_sub]
      exact ⟨x, rfl⟩
    -- Extension: h' = r ∘ k, and h'(α(x)) = r(k(α(x))) = r(j(g(x))) = g(x)
    refine ⟨r.comp k, fun x => ?_⟩
    simp only [LinearMap.comp_apply]
    rw [← key x]
    exact congr_fun (congr_arg DFunLike.coe hr) (g x)

/-- **Baer's criterion**: I is injective if and only if every linear map from an ideal of R
to I extends to a linear map from R to I.
(Etingof Theorem 8.1.5, relates to the extension property) -/
theorem Etingof.Theorem_8_1_5_Baer
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔ Module.Baer R I := by
  exact Module.Baer.iff_injective.symm
