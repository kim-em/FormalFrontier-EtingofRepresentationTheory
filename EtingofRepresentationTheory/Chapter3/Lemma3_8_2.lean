import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Lemma 3.8.2: Endomorphisms of Indecomposable Representations

Let W be a finite dimensional indecomposable representation of A. Then:

(i) Any homomorphism θ : W → W is either an isomorphism or nilpotent.

(ii) If θₛ : W → W, s = 1, …, n, are nilpotent homomorphisms, then so is
     θ := θ₁ + ⋯ + θₙ.

The proof of (i) uses the Fitting decomposition: W = ker(θ^n) ⊕ range(θ^n) for large n.
Since these are A-submodules and W is indecomposable, one must be zero.

The proof of (ii) is by induction on n, using that if the sum were an isomorphism,
the inverse composed with each summand would give nilpotent maps summing to the identity.
-/

/-- Any endomorphism of a finite dimensional indecomposable representation is either
an isomorphism or nilpotent. Etingof Lemma 3.8.2(i). -/
theorem Etingof.endo_indecomposable_iso_or_nilpotent (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : Etingof.IsIndecomposable A W)
    (θ : W →ₗ[A] W) :
    Function.Bijective θ ∨ IsNilpotent θ := by
  -- W is Noetherian and Artinian as an A-module (since it's finite-dimensional over k)
  haveI : IsNoetherian A W := isNoetherian_of_tower k inferInstance
  haveI : IsArtinian A W := isArtinian_of_tower k inferInstance
  -- Fitting decomposition: ker(θ^n) and range(θ^n) are complementary A-submodules
  have hFit := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow θ
  -- By indecomposability, one factor must be ⊥
  have h_triv : (⨆ n, LinearMap.ker (θ ^ n)) = ⊥ ∨ (⨅ n, LinearMap.range (θ ^ n)) = ⊥ :=
    hW.2 _ _ hFit
  rcases h_triv with hker_bot | hrange_bot
  · -- Case: ⨆ ker(θ^n) = ⊥, so ker θ = ⊥, θ is injective hence bijective
    left
    have hker : LinearMap.ker θ = ⊥ := by
      refine eq_bot_iff.mpr ?_
      have h1 : LinearMap.ker θ ≤ ⨆ n, LinearMap.ker (θ ^ n) :=
        le_iSup_of_le 1 (by simp)
      rwa [hker_bot] at h1
    have hinj : Function.Injective θ := LinearMap.ker_eq_bot.mp hker
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := θ.restrictScalars k)).mp hinj⟩
  · -- Case: ⨅ range(θ^n) = ⊥, so ⨆ ker(θ^n) = ⊤, θ is nilpotent
    right
    -- The chain ker(θ^n) stabilizes (Noetherian)
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp θ.eventually_iSup_ker_pow_eq
    -- Since the complement is ⊥, the kernel side is ⊤
    have htop : (⨆ n, LinearMap.ker (θ ^ n)) = ⊤ := by
      have := codisjoint_iff.mp hFit.codisjoint
      rwa [hrange_bot, sup_bot_eq] at this
    rw [hm m le_rfl] at htop
    exact ⟨m, LinearMap.ext fun w => by
      have : w ∈ LinearMap.ker (θ ^ m) := htop ▸ Submodule.mem_top
      exact LinearMap.mem_ker.mp this⟩

/-- A sum of nilpotent endomorphisms of an indecomposable representation is nilpotent.
Etingof Lemma 3.8.2(ii). -/
theorem Etingof.sum_nilpotent_endo_indecomposable (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : Etingof.IsIndecomposable A W)
    {n : ℕ} (θ : Fin n → (W →ₗ[A] W)) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) := by
  haveI := hW.1
  -- Key fact: nilpotent endomorphisms of a nontrivial module are not units
  have nilp_not_unit : ∀ (f : Module.End A W), IsNilpotent f → ¬ IsUnit f := by
    rintro f ⟨m, hm⟩ huf
    exact not_isUnit_zero (hm ▸ huf.pow m)
  -- Induction on n
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hN : IsNilpotent (∑ i : Fin n, θ (Fin.succ i)) := ih _ (fun i => hθ _)
    -- By part (i), the total sum is bijective or nilpotent
    rcases Etingof.endo_indecomposable_iso_or_nilpotent k A W hW
      (θ 0 + ∑ i : Fin n, θ (Fin.succ i)) with hbij | hnil
    · -- S is bijective → contradiction
      exfalso
      -- S is a unit in End A W
      have huS : IsUnit (θ 0 + ∑ i : Fin n, θ (Fin.succ i)) :=
        (Module.End.isUnit_iff _).mpr hbij
      obtain ⟨u, hu_eq⟩ := huS
      -- u⁻¹ * θ 0 + u⁻¹ * N = 1
      have h1 : (↑u⁻¹ : Module.End A W) * (θ 0) +
          ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) = 1 := by
        rw [← mul_add, ← hu_eq, Units.inv_mul]
      -- Helper: if u⁻¹ * f were bijective, then f = u * (u⁻¹ * f) would be a unit
      have unit_lift : ∀ (f : Module.End A W),
          Function.Bijective ((↑u⁻¹ : Module.End A W) * f) → IsUnit f := by
        intro f hbf
        have : (f : Module.End A W) = ↑u * (↑u⁻¹ * f) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [this]; exact u.isUnit.mul ((Module.End.isUnit_iff _).mpr hbf)
      -- u⁻¹ * θ 0 is nilpotent (bijective would make θ 0 a unit, contradicting nilpotent)
      have h_nilp0 : IsNilpotent ((↑u⁻¹ : Module.End A W) * θ 0) := by
        rcases Etingof.endo_indecomposable_iso_or_nilpotent k A W hW (↑u⁻¹ * θ 0) with hb | hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ (hθ 0))
        · exact hn
      -- u⁻¹ * N is nilpotent (similarly)
      have h_nilpN : IsNilpotent ((↑u⁻¹ : Module.End A W) * ∑ i : Fin n, θ (Fin.succ i)) := by
        rcases Etingof.endo_indecomposable_iso_or_nilpotent k A W hW
          (↑u⁻¹ * ∑ i : Fin n, θ (Fin.succ i)) with hb | hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ hN)
        · exact hn
      -- From h1: u⁻¹ * θ 0 = 1 - u⁻¹ * N
      have h_eq : (↑u⁻¹ : Module.End A W) * θ 0 =
          1 - ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) :=
        eq_sub_of_add_eq h1
      -- u⁻¹ * N nilpotent → 1 - u⁻¹ * N is a unit → u⁻¹ * θ 0 is a unit
      have h_unit0 : IsUnit ((↑u⁻¹ : Module.End A W) * θ 0) := by
        rw [h_eq]; exact h_nilpN.isUnit_one_sub
      -- But u⁻¹ * θ 0 is nilpotent and a unit: contradiction
      exact nilp_not_unit _ h_nilp0 h_unit0
    · exact hnil
