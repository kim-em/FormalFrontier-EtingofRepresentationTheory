import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2
import EtingofRepresentationTheory.Chapter6.Example6_2_3

/-!
# Example 6.2.4: Indecomposable Representations of A₃

The quiver A₃ consists of three vertices and two edges: • → • → •.
A representation consists of three vector spaces V₁, V₂, V₃ and linear maps
f : V₁ → V₂, g : V₂ → V₃.

The six indecomposable representations (by dimension triple) are:
- (1,0,0), (0,1,0), (0,0,1): simple representations at each vertex
- (1,1,0) with f injective: interval [1,2]
- (0,1,1) with g injective: interval [2,3]
- (1,1,1) with f, g injective: interval [1,3]

## Formalization

We define A₃-representations, indecomposability, and state the classification.
The boundary cases (some Vᵢ = 0) reduce to A₂/A₁ results via Example 6.2.2/6.2.3.
The interior case (all Vᵢ nonzero) uses decomposition arguments:
ker f = ⊥, range g = ⊤, g∘f injective, ker g = ⊥ → g bijective →
V₂ = range f ⊕ W forces W = ⊥ → all dimensions = 1.
-/

/-- A representation of the A₃ quiver (• → • → •) over a field k. -/
structure A₃Rep (k : Type*) [Field k] where
  V₁ : Type*
  V₂ : Type*
  V₃ : Type*
  [addCommGroup₁ : AddCommGroup V₁]
  [module₁ : Module k V₁]
  [finiteDimensional₁ : FiniteDimensional k V₁]
  [addCommGroup₂ : AddCommGroup V₂]
  [module₂ : Module k V₂]
  [finiteDimensional₂ : FiniteDimensional k V₂]
  [addCommGroup₃ : AddCommGroup V₃]
  [module₃ : Module k V₃]
  [finiteDimensional₃ : FiniteDimensional k V₃]
  f : V₁ →ₗ[k] V₂
  g : V₂ →ₗ[k] V₃

attribute [instance] A₃Rep.addCommGroup₁ A₃Rep.module₁ A₃Rep.finiteDimensional₁
  A₃Rep.addCommGroup₂ A₃Rep.module₂ A₃Rep.finiteDimensional₂
  A₃Rep.addCommGroup₃ A₃Rep.module₃ A₃Rep.finiteDimensional₃

/-- An A₃-representation is indecomposable if it is nontrivial and for any
compatible decomposition, one summand is zero. -/
def A₃Rep.Indecomposable {k : Type*} [Field k] (ρ : A₃Rep k) : Prop :=
  (0 < Module.finrank k ρ.V₁ ∨ 0 < Module.finrank k ρ.V₂ ∨
   0 < Module.finrank k ρ.V₃) ∧
  ∀ (p₁ q₁ : Submodule k ρ.V₁) (p₂ q₂ : Submodule k ρ.V₂)
    (p₃ q₃ : Submodule k ρ.V₃),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.f x ∈ p₂) → (∀ x ∈ q₁, ρ.f x ∈ q₂) →
    (∀ x ∈ p₂, ρ.g x ∈ p₃) → (∀ x ∈ q₂, ρ.g x ∈ q₃) →
    (p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

private lemma a3_zero_of_finrank_zero {k : Type*} [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h : Module.finrank k V = 0) (x : V) : x = 0 := by
  have htop : (⊤ : Submodule k V) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h)
  have hx : x ∈ (⊤ : Submodule k V) := Submodule.mem_top
  rwa [htop, Submodule.mem_bot] at hx

/-- In a finite-dimensional vector space, if two subspaces are disjoint,
there exists a complement of the first containing the second. -/
private lemma exists_isCompl_containing {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A B : Submodule k V) (h : Disjoint A B) :
    ∃ C : Submodule k V, IsCompl A C ∧ B ≤ C := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl (A ⊔ B)
  refine ⟨B ⊔ C₀, ?_, le_sup_left⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxA hxBC
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hxBC
    -- x = b + c, so c = x - b ∈ A ⊔ B
    have hc_AB : c ∈ A ⊔ B := by
      have hceq : c = x - b := eq_sub_of_add_eq' hbc
      rw [hceq]; exact (A ⊔ B).sub_mem (Submodule.mem_sup_left hxA) (Submodule.mem_sup_right hb)
    have : c ∈ (A ⊔ B) ⊓ C₀ := ⟨hc_AB, hc⟩
    rw [hC₀.1.eq_bot, Submodule.mem_bot] at this
    rw [this, add_zero] at hbc
    have : x ∈ A ⊓ B := ⟨hxA, hbc ▸ hb⟩
    rw [h.eq_bot, Submodule.mem_bot] at this
    exact this
  · rw [codisjoint_iff]
    calc A ⊔ (B ⊔ C₀) = (A ⊔ B) ⊔ C₀ := by rw [sup_assoc]
    _ = ⊤ := hC₀.2.eq_top

/-- Bijective linear map preserves IsCompl under map. -/
private lemma isCompl_map_of_bijective {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (g : V →ₗ[k] W) (hg : Function.Bijective g)
    (p q : Submodule k V) (hpq : IsCompl p q) :
    IsCompl (Submodule.map g p) (Submodule.map g q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz₁ hz₂
    obtain ⟨y₁, hy₁, rfl⟩ := Submodule.mem_map.mp hz₁
    obtain ⟨y₂, hy₂, h_eq⟩ := Submodule.mem_map.mp hz₂
    have heq : y₁ = y₂ := hg.1 h_eq.symm
    rw [heq] at hy₁
    have hmem : y₂ ∈ p ⊓ q := ⟨hy₁, hy₂⟩
    rw [hpq.1.eq_bot, Submodule.mem_bot] at hmem
    rw [heq, hmem, map_zero]
  · rw [codisjoint_iff]; ext z
    simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
    obtain ⟨y, rfl⟩ := hg.2 z
    have : y ∈ (⊤ : Submodule k V) := Submodule.mem_top
    rw [← hpq.2.eq_top] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
    exact ⟨g a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩,
           g b, Submodule.mem_map.mpr ⟨b, hb, rfl⟩,
           by rw [← map_add, hab]⟩

private lemma a3_V₂_zero {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) (h₂ : Module.finrank k ρ.V₂ = 0) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₃ = 1) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₂z : ∀ y : ρ.V₂, y = 0 := a3_zero_of_finrank_zero ρ.V₂ h₂
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₁) with h₁ | h₁ <;>
    rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₃) with h₃ | h₃
  · exfalso; omega
  · right; refine ⟨h₁, ?_⟩
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₃, fun p₃ q₃ hpq₃ => ?_⟩
    have := hind_cond ⊥ ⊤ ⊥ ⊤ p₃ q₃ isCompl_bot_top isCompl_bot_top hpq₃
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV₂z x, map_zero]; exact p₃.zero_mem)
      (fun x _ => by rw [hV₂z x, map_zero]; exact q₃.zero_mem)
    rcases this with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · left; exact h
    · right; exact h
  · left; refine ⟨?_, h₃⟩
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
    have := hind_cond p₁ q₁ ⊥ ⊤ ⊥ ⊤ hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂z (ρ.f x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases this with ⟨h, _, _⟩ | ⟨h, _, _⟩
    · left; exact h
    · right; exact h
  · exfalso
    have := hind_cond ⊤ ⊥ ⊥ ⊤ ⊥ ⊤ isCompl_top_bot isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂z (ρ.f x)]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.mem_top)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases this with ⟨htop, _, _⟩ | ⟨_, _, htop⟩
    · rw [← finrank_top (R := k) (M := ρ.V₁), htop, finrank_bot] at h₁; omega
    · rw [← finrank_top (R := k) (M := ρ.V₃), htop, finrank_bot] at h₃; omega

private lemma a3_V₁_zero {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) (h₁ : Module.finrank k ρ.V₁ = 0) :
    (Module.finrank k ρ.V₂ = 1 ∧ Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₂ = 0 ∧ Module.finrank k ρ.V₃ = 1) ∨
    (Module.finrank k ρ.V₂ = 1 ∧ Module.finrank k ρ.V₃ = 1 ∧
      Function.Injective ρ.g) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₁z : ∀ x : ρ.V₁, x = 0 := a3_zero_of_finrank_zero ρ.V₁ h₁
  have hA₂ : (A₂Rep.mk ρ.V₂ ρ.V₃ ρ.g).Indecomposable := by
    refine ⟨?_, fun p₂ q₂ p₃ q₃ hpq₂ hpq₃ hfp hfq => ?_⟩
    · rcases hnt with h | h | h
      · omega
      · left; exact h
      · right; exact h
    · have := hind_cond ⊥ ⊤ p₂ q₂ p₃ q₃ isCompl_bot_top hpq₂ hpq₃
        (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact p₂.zero_mem)
        (fun x _ => by rw [hV₁z x, map_zero]; exact q₂.zero_mem)
        hfp hfq
      rcases this with ⟨_, h₂, h₃⟩ | ⟨_, h₂, h₃⟩
      · left; exact ⟨h₂, h₃⟩
      · right; exact ⟨h₂, h₃⟩
  exact Etingof.Example_6_2_3 k (A₂Rep.mk ρ.V₂ ρ.V₃ ρ.g) hA₂

private lemma a3_V₃_zero {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) (h₃ : Module.finrank k ρ.V₃ = 0) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Function.Injective ρ.f) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₃z : ∀ x : ρ.V₃, x = 0 := a3_zero_of_finrank_zero ρ.V₃ h₃
  have hA₂ : (A₂Rep.mk ρ.V₁ ρ.V₂ ρ.f).Indecomposable := by
    refine ⟨?_, fun p₁ q₁ p₂ q₂ hpq₁ hpq₂ hfp hfq => ?_⟩
    · rcases hnt with h | h | h
      · left; exact h
      · right; exact h
      · omega
    · have := hind_cond p₁ q₁ p₂ q₂ ⊥ ⊤ hpq₁ hpq₂ isCompl_bot_top
        hfp hfq
        (fun x _ => by rw [hV₃z (ρ.g x)]; exact Submodule.zero_mem _)
        (fun _ _ => Submodule.mem_top)
      rcases this with ⟨h₁, h₂, _⟩ | ⟨h₁, h₂, _⟩
      · left; exact ⟨h₁, h₂⟩
      · right; exact ⟨h₁, h₂⟩
  exact Etingof.Example_6_2_3 k (A₂Rep.mk ρ.V₁ ρ.V₂ ρ.f) hA₂

private lemma a3_ker_f {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.f = ⊥ ∨
    (Module.finrank k ρ.V₂ = 0 ∧ Module.finrank k ρ.V₃ = 0) := by
  by_contra h; push_neg at h; obtain ⟨hker, hV₂₃⟩ := h
  obtain ⟨_, hind_cond⟩ := hind
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.f)
  have := hind_cond (LinearMap.ker ρ.f) q₁ ⊥ ⊤ ⊥ ⊤ hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨hk, _, _⟩ | ⟨_, htop₂, htop₃⟩
  · exact hker hk
  · have h₂ : Module.finrank k ρ.V₂ = 0 := by
      rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot]
    have h₃ : Module.finrank k ρ.V₃ = 0 := by
      rw [← finrank_top (R := k) (M := ρ.V₃), htop₃, finrank_bot]
    exact hV₂₃ h₂ h₃

private lemma a3_range_g {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.range ρ.g = ⊤ ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 0) := by
  by_contra h; push_neg at h; obtain ⟨hrange, hV₁₂⟩ := h
  obtain ⟨_, hind_cond⟩ := hind
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.range ρ.g)
  have := hind_cond ⊤ ⊥ ⊤ ⊥ (LinearMap.range ρ.g) q₃
    isCompl_top_bot isCompl_top_bot hq₃
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => LinearMap.mem_range_self ρ.g x)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact q₃.zero_mem)
  rcases this with ⟨htop₁, htop₂, _⟩ | ⟨_, _, hq₃'⟩
  · have h₁ : Module.finrank k ρ.V₁ = 0 := by
      rw [← finrank_top (R := k) (M := ρ.V₁), htop₁, finrank_bot]
    have h₂ : Module.finrank k ρ.V₂ = 0 := by
      rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot]
    exact hV₁₂ h₁ h₂
  · exact hrange (eq_top_of_isCompl_bot (hq₃' ▸ hq₃))

private lemma a3_gf_injective {k : Type*} [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable)
    (hf_inj : Function.Injective ρ.f)
    (h₃ : 0 < Module.finrank k ρ.V₃) :
    Function.Injective (ρ.g.comp ρ.f) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  obtain ⟨_, hind_cond⟩ := hind
  set K := LinearMap.ker (ρ.g.comp ρ.f)
  have hfK_le_kerg : Submodule.map ρ.f K ≤ LinearMap.ker ρ.g := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl K
  have hf_disj : Disjoint (Submodule.map ρ.f K) (Submodule.map ρ.f q₁) := by
    rw [Submodule.disjoint_def]
    intro y hy₁ hy₂
    obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
    obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
    have heq : x₁ = x₂ := hf_inj h_eq.symm
    rw [heq] at hx₁
    have hmem : x₂ ∈ K ⊓ q₁ := ⟨hx₁, hx₂⟩
    rw [hq₁.1.eq_bot, Submodule.mem_bot] at hmem
    rw [heq, hmem, map_zero]
  obtain ⟨q₂, hpq₂, hfq₁_le_q₂⟩ := exists_isCompl_containing
    (Submodule.map ρ.f K) (Submodule.map ρ.f q₁) hf_disj
  have := hind_cond K q₁ (Submodule.map ρ.f K) q₂ ⊥ ⊤
    hq₁ hpq₂ isCompl_bot_top
    (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    (fun x hx => hfq₁_le_q₂ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
    (fun x hx => by
      have := hfK_le_kerg hx
      rw [LinearMap.mem_ker] at this
      rw [this]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨hK_bot, _, _⟩ | ⟨_, _, htop⟩
  · exact hker hK_bot
  · rw [← finrank_top (R := k) (M := ρ.V₃), htop, finrank_bot] at h₃; omega

/-- **Example 6.2.4 (Etingof)**: Every indecomposable representation of the A₃ quiver
(• → • → •) has dimension triple in
{(1,0,0),(0,1,0),(0,0,1),(1,1,0),(0,1,1),(1,1,1)},
with appropriate injectivity conditions on the maps. -/
theorem Etingof.Example_6_2_4 (k : Type*) [Field k] (ρ : A₃Rep k)
    (hind : ρ.Indecomposable) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 0 ∧
      Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
      Module.finrank k ρ.V₃ = 1) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 0 ∧ Function.Injective ρ.f) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 1 ∧ Function.Injective ρ.g) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 1 ∧ Function.Injective ρ.f ∧
      Function.Injective ρ.g) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hind : ρ.Indecomposable := ⟨hnt, hind_cond⟩
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₂) with h₂ | h₂
  · rcases a3_V₂_zero ρ hind h₂ with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
    · left; exact ⟨h₁, h₂, h₃⟩
    · right; right; left; exact ⟨h₁, h₂, h₃⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₁) with h₁ | h₁
    · rcases a3_V₁_zero ρ hind h₁ with ⟨h₂', h₃⟩ | ⟨h₂', h₃⟩ | ⟨h₂', h₃, hinj⟩
      · right; left; exact ⟨h₁, h₂', h₃⟩
      · right; right; left; exact ⟨h₁, h₂', h₃⟩
      · right; right; right; right; left; exact ⟨h₁, h₂', h₃, hinj⟩
    · rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₃) with h₃ | h₃
      · rcases a3_V₃_zero ρ hind h₃ with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩ | ⟨h₁', h₂', hinj⟩
        · left; exact ⟨h₁', h₂', h₃⟩
        · right; left; exact ⟨h₁', h₂', h₃⟩
        · right; right; right; left; exact ⟨h₁', h₂', h₃, hinj⟩
      · -- ALL THREE NONZERO
        have hf_inj : Function.Injective ρ.f :=
          LinearMap.ker_eq_bot.mp ((a3_ker_f ρ hind).resolve_right (by omega))
        have hg_surj : LinearMap.range ρ.g = ⊤ :=
          (a3_range_g ρ hind).resolve_right (by omega)
        have hgf_inj := a3_gf_injective ρ hind hf_inj h₃
        -- ker g ∩ range f = ⊥
        have hkerg_rangef : Disjoint (LinearMap.ker ρ.g) (LinearMap.range ρ.f) := by
          rw [Submodule.disjoint_def]
          intro y hyk hyf
          obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hyf
          have : x ∈ LinearMap.ker (ρ.g.comp ρ.f) := by
            rw [LinearMap.mem_ker, LinearMap.comp_apply]
            exact LinearMap.mem_ker.mp hyk
          rw [LinearMap.ker_eq_bot.mpr hgf_inj, Submodule.mem_bot] at this
          rw [this, map_zero]
        -- Get complement of ker g containing range f
        obtain ⟨C, hC, hrf_le_C⟩ := exists_isCompl_containing
          (LinearMap.ker ρ.g) (LinearMap.range ρ.f) hkerg_rangef
        -- Use indecomposability: (⊥, ker g, ⊥) ⊕ (V₁, C, V₃)
        have hkerg_bot : LinearMap.ker ρ.g = ⊥ := by
          have := hind_cond ⊥ ⊤ (LinearMap.ker ρ.g) C ⊥ ⊤
            isCompl_bot_top hC isCompl_bot_top
            (fun x hx => by
              rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]
              exact (LinearMap.ker ρ.g).zero_mem)
            (fun x _ => hrf_le_C (LinearMap.mem_range_self ρ.f x))
            (fun x hx => by
              rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _)
            (fun _ _ => Submodule.mem_top)
          rcases this with ⟨_, hkg, _⟩ | ⟨_, _, htop⟩
          · exact hkg
          · rw [← finrank_top (R := k) (M := ρ.V₃), htop, finrank_bot] at h₃; omega
        -- g is bijective
        have hg_inj : Function.Injective ρ.g := LinearMap.ker_eq_bot.mp hkerg_bot
        have hg_bij : Function.Bijective ρ.g :=
          ⟨hg_inj, LinearMap.range_eq_top.mp hg_surj⟩
        -- Show dim V₁ = 1: V₁ is indecomposable
        -- Any decomp p₁ ⊕ q₁ lifts through f, then use exists_isCompl_containing for V₂
        have hV₁_dim1 : Module.finrank k ρ.V₁ = 1 := by
          rw [← Etingof.Example_6_2_2]
          refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
          have hfp_fq_disj : Disjoint (Submodule.map ρ.f p₁) (Submodule.map ρ.f q₁) := by
            rw [Submodule.disjoint_def]
            intro y hy₁ hy₂
            obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
            obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
            have heq : x₁ = x₂ := hf_inj h_eq.symm
            rw [heq] at hx₁
            have hmem : x₂ ∈ p₁ ⊓ q₁ := ⟨hx₁, hx₂⟩
            rw [hpq₁.1.eq_bot, Submodule.mem_bot] at hmem
            rw [heq, hmem, map_zero]
          obtain ⟨q₂, hpq₂, hfq₁_le_q₂⟩ := exists_isCompl_containing
            (Submodule.map ρ.f p₁) (Submodule.map ρ.f q₁) hfp_fq_disj
          have hpq₃ := isCompl_map_of_bijective ρ.g hg_bij _ _ hpq₂
          have := hind_cond p₁ q₁ (Submodule.map ρ.f p₁) q₂
            (Submodule.map ρ.g (Submodule.map ρ.f p₁)) (Submodule.map ρ.g q₂)
            hpq₁ hpq₂ hpq₃
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => hfq₁_le_q₂ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
          rcases this with ⟨hp₁, _, _⟩ | ⟨hq₁, _, _⟩
          · left; exact hp₁
          · right; exact hq₁
        -- Show dim V₂ = 1: decompose V₂ = range f ⊕ W, then A₃ indecomp forces W = ⊥
        have hV₂_dim1 : Module.finrank k ρ.V₂ = 1 := by
          obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ρ.f)
          have hpq₃ := isCompl_map_of_bijective ρ.g hg_bij _ _ hW
          have := hind_cond ⊤ ⊥ (LinearMap.range ρ.f) W
            (Submodule.map ρ.g (LinearMap.range ρ.f)) (Submodule.map ρ.g W)
            isCompl_top_bot hW hpq₃
            (fun x _ => LinearMap.mem_range_self ρ.f x)
            (fun x hx => by
              rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact W.zero_mem)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
          rcases this with ⟨htop, _, _⟩ | ⟨_, hW_bot, _⟩
          · -- ⊤ = ⊥ contradicts dim V₁ > 0
            rw [← finrank_top (R := k) (M := ρ.V₁), htop, finrank_bot] at h₁; omega
          · -- W = ⊥ means range f = V₂, so dim V₂ = dim(range f) = dim V₁ = 1
            have hf_surj : LinearMap.range ρ.f = ⊤ :=
              eq_top_of_isCompl_bot (hW_bot ▸ hW)
            have h := ρ.f.finrank_range_add_finrank_ker
            rw [LinearMap.ker_eq_bot.mpr hf_inj, finrank_bot, add_zero,
                hf_surj, finrank_top] at h
            omega
        -- dim V₃ = dim V₂ = 1 (g bijective)
        have hV₃_dim1 : Module.finrank k ρ.V₃ = 1 := by
          have h := ρ.g.finrank_range_add_finrank_ker
          rw [hkerg_bot, finrank_bot, add_zero, hg_surj, finrank_top] at h
          omega
        right; right; right; right; right
        exact ⟨hV₁_dim1, hV₂_dim1, hV₃_dim1, hf_inj, hg_inj⟩
