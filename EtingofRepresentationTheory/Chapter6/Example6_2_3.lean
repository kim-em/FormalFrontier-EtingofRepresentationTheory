import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2

/-!
# Example 6.2.3: Indecomposable Representations of A₂

The quiver A₂ consists of two vertices connected by a single edge: • → •.
A representation consists of two vector spaces V₁, V₂ and a linear map f : V₁ → V₂.

By rank-nullity / Gauss elimination, the three indecomposable representations are:
- (k, 0, 0): kernel component
- (0, k, 0): cokernel component
- (k, k, id): isomorphism component

## Formalization

We define indecomposability for A₂-representations (pairs of vector spaces with a
linear map) and prove the classification by dimension: any indecomposable has
(dim V₁, dim V₂) ∈ {(1,0), (0,1), (1,1)} with f injective in the last case.
-/

/-- A representation of the A₂ quiver (• → •) over a field k. -/
structure A₂Rep (k : Type*) [Field k] where
  V₁ : Type*
  V₂ : Type*
  [addCommGroup₁ : AddCommGroup V₁]
  [module₁ : Module k V₁]
  [finiteDimensional₁ : FiniteDimensional k V₁]
  [addCommGroup₂ : AddCommGroup V₂]
  [module₂ : Module k V₂]
  [finiteDimensional₂ : FiniteDimensional k V₂]
  f : V₁ →ₗ[k] V₂

attribute [instance] A₂Rep.addCommGroup₁ A₂Rep.module₁ A₂Rep.finiteDimensional₁
  A₂Rep.addCommGroup₂ A₂Rep.module₂ A₂Rep.finiteDimensional₂

/-- An A₂-representation is indecomposable if it is nontrivial and for any decomposition
of V₁ = p₁ ⊕ q₁ and V₂ = p₂ ⊕ q₂ compatible with f (f maps p₁ into p₂ and q₁
into q₂), one of the summands is zero. -/
def A₂Rep.Indecomposable {k : Type*} [Field k] (ρ : A₂Rep k) : Prop :=
  (0 < Module.finrank k ρ.V₁ ∨ 0 < Module.finrank k ρ.V₂) ∧
  ∀ (p₁ q₁ : Submodule k ρ.V₁) (p₂ q₂ : Submodule k ρ.V₂),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ →
    (∀ x ∈ p₁, ρ.f x ∈ p₂) → (∀ x ∈ q₁, ρ.f x ∈ q₂) →
    (p₁ = ⊥ ∧ p₂ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥)

private lemma ker_or_V₂_zero {k : Type*} [Field k] (ρ : A₂Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.f = ⊥ ∨ Module.finrank k ρ.V₂ = 0 := by
  by_contra h
  push_neg at h
  obtain ⟨hker, hV₂⟩ := h
  -- Decompose V₁ = ker f ⊕ complement, V₂ = ⊥ ⊕ ⊤
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.f)
  have hres := hind.2 (LinearMap.ker ρ.f) q₁ ⊥ ⊤ hq₁ isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨hk, _⟩ | ⟨_, htop⟩
  · exact hker hk
  · rw [← finrank_top (R := k) (M := ρ.V₂), htop, finrank_bot] at hV₂
    exact hV₂ rfl

private lemma range_or_V₁_zero {k : Type*} [Field k] (ρ : A₂Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.range ρ.f = ⊤ ∨ Module.finrank k ρ.V₁ = 0 := by
  by_contra h
  push_neg at h
  obtain ⟨hrange, hV₁⟩ := h
  obtain ⟨q₂, hq₂⟩ := Submodule.exists_isCompl (LinearMap.range ρ.f)
  have hind_cond := hind.2 ⊤ ⊥ (LinearMap.range ρ.f) q₂ isCompl_top_bot hq₂
    (fun x _ => LinearMap.mem_range_self ρ.f x)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact q₂.zero_mem)
  rcases hind_cond with ⟨htop, _⟩ | ⟨_, hq₂'⟩
  · rw [← finrank_top (R := k) (M := ρ.V₁), htop, finrank_bot] at hV₁
    exact hV₁ rfl
  · exact hrange (eq_top_of_isCompl_bot (hq₂' ▸ hq₂))

/-- **Example 6.2.3 (Etingof)**: Every indecomposable representation of the A₂ quiver
(• → •) satisfies one of:
- (dim V₁, dim V₂) = (1, 0) — the kernel representation
- (dim V₁, dim V₂) = (0, 1) — the cokernel representation
- (dim V₁, dim V₂) = (1, 1) with f injective — the identity representation -/
theorem Etingof.Example_6_2_3 (k : Type*) [Field k] (ρ : A₂Rep k)
    (hind : ρ.Indecomposable) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Function.Injective ρ.f) := by
  -- Key facts: either ker f = ⊥ or V₂ = 0; either range f = ⊤ or V₁ = 0
  have hker := ker_or_V₂_zero ρ hind
  have hrange := range_or_V₁_zero ρ hind
  obtain ⟨hnt, hind_cond⟩ := hind
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₁) with h₁ | h₁ <;>
    rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₂) with h₂ | h₂
  · -- V₁ = 0, V₂ = 0: contradicts nontrivial
    omega
  · -- V₁ = 0, V₂ ≠ 0: case (0, 1)
    right; left; refine ⟨h₁, ?_⟩
    -- V₂ is indecomposable as a vector space
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
    -- Any decomposition of V₂ gives a decomposition of the rep with V₁ = ⊥ ⊕ ⊤
    have hV₁_zero : ∀ (x : ρ.V₁), x = 0 := fun x => by
      have htop₁ : (⊤ : Submodule k ρ.V₁) = ⊥ :=
        Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₁)
      have : x ∈ (⊤ : Submodule k ρ.V₁) := Submodule.mem_top
      rwa [htop₁, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ p₂ q₂ isCompl_bot_top hpq₂
      (fun x _ => by rw [hV₁_zero x, map_zero]; exact p₂.zero_mem)
      (fun x _ => by rw [hV₁_zero x, map_zero]; exact q₂.zero_mem)
    rcases hind_cond with ⟨_, h⟩ | ⟨_, h⟩
    · left; exact h
    · right; exact h
  · -- V₁ ≠ 0, V₂ = 0: case (1, 0)
    left; refine ⟨?_, h₂⟩
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
    have htop₂ : (⊤ : Submodule k ρ.V₂) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₂)
    have hV₂_zero : ∀ (y : ρ.V₂), y = 0 := fun y => by
      have : y ∈ (⊤ : Submodule k ρ.V₂) := Submodule.mem_top
      rwa [htop₂, Submodule.mem_bot] at this
    specialize hind_cond p₁ q₁ ⊥ ⊤ hpq₁ isCompl_bot_top
      (fun x _ => by rw [hV₂_zero (ρ.f x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨h, _⟩ | ⟨h, _⟩
    · left; exact h
    · right; exact h
  · -- V₁ ≠ 0, V₂ ≠ 0: f is injective (from hker) and surjective (from hrange)
    have hf_inj : Function.Injective ρ.f :=
      LinearMap.ker_eq_bot.mp (hker.resolve_right (by omega))
    have hf_surj : LinearMap.range ρ.f = ⊤ := hrange.resolve_right (by omega)
    -- dim V₁ = dim V₂ because f is bijective
    have hdim_eq : Module.finrank k ρ.V₂ = Module.finrank k ρ.V₁ := by
      have h := ρ.f.finrank_range_add_finrank_ker
      rw [LinearMap.ker_eq_bot.mpr hf_inj, finrank_bot, add_zero] at h
      rw [hf_surj, finrank_top] at h; omega
    -- V₁ is indecomposable: any decomposition of V₁ lifts through f to V₂
    have hV₁_dim1 : Module.finrank k ρ.V₁ = 1 := by
      rw [← Etingof.Example_6_2_2]
      refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
      set p₂ := Submodule.map ρ.f p₁
      set q₂ := Submodule.map ρ.f q₁
      have hpq₂ : IsCompl p₂ q₂ := by
        constructor
        · rw [Submodule.disjoint_def]
          intro y hy₁ hy₂
          obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
          obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
          have heq : x₁ = x₂ := hf_inj h_eq.symm
          rw [heq] at hx₁
          have hmem : x₂ ∈ p₁ ⊓ q₁ := ⟨hx₁, hx₂⟩
          rw [hpq₁.1.eq_bot, Submodule.mem_bot] at hmem
          rw [heq, hmem, map_zero]
        · rw [codisjoint_iff]
          ext y
          simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
          obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.mp hf_surj y
          have : x ∈ (⊤ : Submodule k ρ.V₁) := Submodule.mem_top
          rw [← hpq₁.2.eq_top] at this
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
          exact ⟨ρ.f a, ⟨a, ha, rfl⟩, ρ.f b, ⟨b, hb, rfl⟩, by rw [← map_add, hab]⟩
      specialize hind_cond p₁ q₁ p₂ q₂ hpq₁ hpq₂
        (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
        (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
      rcases hind_cond with ⟨hp₁, _⟩ | ⟨hq₁, _⟩
      · left; exact hp₁
      · right; exact hq₁
    right; right; exact ⟨hV₁_dim1, hdim_eq ▸ hV₁_dim1, hf_inj⟩

