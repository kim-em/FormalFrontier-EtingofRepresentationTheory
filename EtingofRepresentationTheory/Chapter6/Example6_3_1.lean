import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2

/-!
# Example 6.3.1: Indecomposable Representations of D₄

The quiver D₄ (with one central vertex and three arms) has 12 indecomposable
representations for the orientation where three arrows point into the central vertex.

The classification reduces to the **triple of subspaces problem**: classifying
triples of subspaces V₁, V₂, V₃ of a vector space V up to isomorphism.

The 12 indecomposable representations have dimension vectors (center, arm₁, arm₂, arm₃):
- (0,1,0,0), (0,0,1,0), (0,0,0,1): kernel representations at each arm
- (1,0,0,0): simple representation at center
- (1,1,0,0), (1,0,1,0), (1,0,0,1): one arm maps isomorphically to center
- (1,1,1,0), (1,1,0,1), (1,0,1,1): two arms map isomorphically, V₁∩V₂ = 0 type
- (1,1,1,1): all three arms map isomorphically, V₁∩V₂∩V₃ = 0 type
- (2,1,1,1): the "generic" indecomposable (graph of isomorphism)

## Mathlib correspondence

Not in Mathlib. The classification of D₄ representations requires solving the
triple of subspaces problem, which is a classical result in linear algebra.

## Formalization note

We follow Etingof's proof, which proceeds by iteratively splitting off
representations: first kernels of the maps, then the complement of the sum,
then pairwise intersections, then the triple intersection, and finally reducing
to the triple of subspaces problem with conditions (1) V₁+V₂+V₃=V,
(2) pairwise disjoint, (3) each Vᵢ ⊆ sum of other two, which forces dim V = 2n
and produces n copies of the (2,1,1,1) indecomposable.
-/

/-- A representation of the D₄ quiver with orientation V₁ → V, V₂ → V, V₃ → V
(three arms mapping into a central vertex). -/
structure D₄Rep (k : Type*) [Field k] where
  /-- The central vector space -/
  V : Type*
  /-- The first arm -/
  V₁ : Type*
  /-- The second arm -/
  V₂ : Type*
  /-- The third arm -/
  V₃ : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module k V]
  [finiteDimensionalV : FiniteDimensional k V]
  [addCommGroup₁ : AddCommGroup V₁]
  [module₁ : Module k V₁]
  [finiteDimensional₁ : FiniteDimensional k V₁]
  [addCommGroup₂ : AddCommGroup V₂]
  [module₂ : Module k V₂]
  [finiteDimensional₂ : FiniteDimensional k V₂]
  [addCommGroup₃ : AddCommGroup V₃]
  [module₃ : Module k V₃]
  [finiteDimensional₃ : FiniteDimensional k V₃]
  /-- Linear map from arm 1 to center -/
  A₁ : V₁ →ₗ[k] V
  /-- Linear map from arm 2 to center -/
  A₂ : V₂ →ₗ[k] V
  /-- Linear map from arm 3 to center -/
  A₃ : V₃ →ₗ[k] V

attribute [instance] D₄Rep.addCommGroupV D₄Rep.moduleV D₄Rep.finiteDimensionalV
  D₄Rep.addCommGroup₁ D₄Rep.module₁ D₄Rep.finiteDimensional₁
  D₄Rep.addCommGroup₂ D₄Rep.module₂ D₄Rep.finiteDimensional₂
  D₄Rep.addCommGroup₃ D₄Rep.module₃ D₄Rep.finiteDimensional₃

/-- A D₄-representation is indecomposable if it is nontrivial and for any
decomposition V = p ⊕ q, V₁ = p₁ ⊕ q₁, V₂ = p₂ ⊕ q₂, V₃ = p₃ ⊕ q₃
compatible with the maps (Aᵢ maps pᵢ into p and qᵢ into q), one of the
summands is zero. -/
def D₄Rep.Indecomposable {k : Type*} [Field k] (ρ : D₄Rep k) : Prop :=
  (0 < Module.finrank k ρ.V ∨ 0 < Module.finrank k ρ.V₁ ∨
   0 < Module.finrank k ρ.V₂ ∨ 0 < Module.finrank k ρ.V₃) ∧
  ∀ (p q : Submodule k ρ.V)
    (p₁ q₁ : Submodule k ρ.V₁)
    (p₂ q₂ : Submodule k ρ.V₂)
    (p₃ q₃ : Submodule k ρ.V₃),
    IsCompl p q → IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.A₁ x ∈ p) → (∀ x ∈ q₁, ρ.A₁ x ∈ q) →
    (∀ x ∈ p₂, ρ.A₂ x ∈ p) → (∀ x ∈ q₂, ρ.A₂ x ∈ q) →
    (∀ x ∈ p₃, ρ.A₃ x ∈ p) → (∀ x ∈ q₃, ρ.A₃ x ∈ q) →
    (p = ⊥ ∧ p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨
    (q = ⊥ ∧ q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- The dimension vector of a D₄ representation: (dim V, dim V₁, dim V₂, dim V₃). -/
noncomputable def D₄Rep.dimVector {k : Type*} [Field k] (ρ : D₄Rep k) : ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank k ρ.V, Module.finrank k ρ.V₁,
   Module.finrank k ρ.V₂, Module.finrank k ρ.V₃)

/-- The set of dimension vectors of the 12 indecomposable representations of D₄.
These correspond to the 12 positive roots of the D₄ root system.

Organized as (dim V, dim V₁, dim V₂, dim V₃):
- 3 kernel representations: (0,1,0,0), (0,0,1,0), (0,0,0,1)
- 1 simple at center: (1,0,0,0)
- 3 center + one arm: (1,1,0,0), (1,0,1,0), (1,0,0,1)
- 3 center + two arms: (1,1,1,0), (1,1,0,1), (1,0,1,1)
- 1 all arms: (1,1,1,1)
- 1 generic: (2,1,1,1) -/
def D₄_indecomposable_dimVectors : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(0,1,0,0), (0,0,1,0), (0,0,0,1),  -- kernel reps
   (1,0,0,0),                          -- simple at center
   (1,1,0,0), (1,0,1,0), (1,0,0,1),  -- center + one arm
   (1,1,1,0), (1,1,0,1), (1,0,1,1),  -- center + two arms
   (1,1,1,1),                          -- all arms equal
   (2,1,1,1)}                          -- generic

/-- **Example 6.3.1 (Etingof)**: Every indecomposable representation of the D₄ quiver
(with orientation V₁ → V ← V₃, V₂ → V) has dimension vector in the set of
12 positive roots of D₄. These are all the dimension vectors (dim V, dim V₁, dim V₂, dim V₃)
of indecomposable representations.

The proof proceeds by iteratively splitting off direct summands:
1. Split off kernels of A₁, A₂, A₃ to make all maps injective
2. Split off complement of V₁+V₂+V₃ (simple at center) to make sum = V
3. Split off V₁∩V₂∩V₃ to make triple intersection = 0
4. Split off pairwise intersections to make all pairwise intersections = 0
5. Split off Vᵢ ∩ (Vⱼ⊕Vₖ) complements to get Vᵢ ⊆ Vⱼ⊕Vₖ
6. The remaining representation decomposes into copies of (2,1,1,1) -/
-- Step 1: Splitting off kernels. For each map Aᵢ, either ker Aᵢ = ⊥
-- or all other components have dimension 0.
private lemma ker_A₁_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₁ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₁)
  -- Decompose: (⊥, ker A₁, ⊥, ⊥) ⊕ (⊤, q₁, ⊤, ⊤)
  have := hind.2 ⊥ ⊤ (LinearMap.ker ρ.A₁) q₁ ⊥ ⊤ ⊥ ⊤
    isCompl_bot_top hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, hk, _, _⟩ | ⟨htop, _, htop₂, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₃), htop₃, finrank_bot]⟩

private lemma ker_A₂_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₂ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₁ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₂, hq₂⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₂)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.A₂) q₂ ⊥ ⊤
    isCompl_bot_top isCompl_bot_top hq₂ isCompl_bot_top
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, hk, _⟩ | ⟨htop, htop₁, _, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₁), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₃), htop₃, finrank_bot]⟩

private lemma ker_A₃_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₃ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₁ = 0 ∧
     Module.finrank k ρ.V₂ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₃)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.A₃) q₃
    isCompl_bot_top isCompl_bot_top isCompl_bot_top hq₃
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, _, hk⟩ | ⟨htop, htop₁, htop₂, _⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₁), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot]⟩

-- Helper: if ρ is indecomposable and V = V₂ = V₃ = 0, then V₁ is indecomposable
-- as a vector space, hence dim V₁ = 1.
private lemma dim_V₁_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₂ : Module.finrank k ρ.V₂ = 0)
    (hV₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V₁ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₁ q₁ hpq₁ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₁ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have htopV₂ : (⊤ : Submodule k ρ.V₂) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₂)
    have htopV₃ : (⊤ : Submodule k ρ.V₃) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₃)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ p₁ q₁ ⊥ ⊤ ⊥ ⊤
      isCompl_bot_top hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV_zero (ρ.A₁ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, hp₁, _, _⟩ | ⟨_, hq₁, _, _⟩
    · left; exact hp₁
    · right; exact hq₁

private lemma dim_V₂_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₁ : Module.finrank k ρ.V₁ = 0)
    (hV₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V₂ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₂ q₂ hpq₂ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₂ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ p₂ q₂ ⊥ ⊤
      isCompl_bot_top isCompl_bot_top hpq₂ isCompl_bot_top
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.A₂ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, hp₂, _⟩ | ⟨_, _, hq₂, _⟩
    · left; exact hp₂
    · right; exact hq₂

private lemma dim_V₃_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₁ : Module.finrank k ρ.V₁ = 0)
    (hV₂ : Module.finrank k ρ.V₂ = 0) :
    Module.finrank k ρ.V₃ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₃ q₃ hpq₃ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₃ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ p₃ q₃
      isCompl_bot_top isCompl_bot_top isCompl_bot_top hpq₃
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.A₃ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, _, hp₃⟩ | ⟨_, _, _, hq₃⟩
    · left; exact hp₃
    · right; exact hq₃

-- Helper: injective linear map into a zero-dimensional space means the source is zero-dimensional
private lemma finrank_eq_zero_of_injective_into_zero {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V₁ →ₗ[k] V) (hf : LinearMap.ker f = ⊥) (hV : Module.finrank k V = 0) :
    Module.finrank k V₁ = 0 := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hf
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

-- Helper: if all arms are zero-dimensional and ρ is indecomposable, then dim V = 1
private lemma dim_V_eq_one_of_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (h₁ : Module.finrank k ρ.V₁ = 0) (h₂ : Module.finrank k ρ.V₂ = 0)
    (h₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p q hpq => ?_⟩
  · have : 0 < Module.finrank k ρ.V := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htop₁ : (⊤ : Submodule k ρ.V₁) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₁)
    have htop₂ : (⊤ : Submodule k ρ.V₂) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₂)
    have htop₃ : (⊤ : Submodule k ρ.V₃) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₃)
    have hV₁_zero : ∀ (x : ρ.V₁), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₁) := Submodule.mem_top
      rwa [htop₁, Submodule.mem_bot] at this
    have hV₂_zero : ∀ (x : ρ.V₂), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₂) := Submodule.mem_top
      rwa [htop₂, Submodule.mem_bot] at this
    have hV₃_zero : ∀ (x : ρ.V₃), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₃) := Submodule.mem_top
      rwa [htop₃, Submodule.mem_bot] at this
    specialize hind_cond p q ⊥ ⊤ ⊥ ⊤ ⊥ ⊤
      hpq isCompl_bot_top isCompl_bot_top isCompl_bot_top
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₁_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₂_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₃_zero x, map_zero]; exact Submodule.zero_mem _)
    rcases hind_cond with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
    · left; exact hp
    · right; exact hq

-- Step 2: range sum = ⊤ or all arms are zero
private lemma range_sum_eq_top_or_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥) :
    LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤ ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hR, harms⟩ := h
  set R := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ with hR_def
  obtain ⟨S, hRS⟩ := Submodule.exists_isCompl R
  -- Decompose: (R, V₁, V₂, V₃) ⊕ (S, 0, 0, 0)
  have := hind.2 R S ⊤ ⊥ ⊤ ⊥ ⊤ ⊥
    hRS isCompl_top_bot isCompl_top_bot isCompl_top_bot
    (fun x _ => by
      have h : ρ.A₁ x ∈ LinearMap.range ρ.A₁ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_left h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.A₂ x ∈ LinearMap.range ρ.A₂ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_right h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.A₃ x ∈ LinearMap.range ρ.A₃ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_right h)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
  rcases this with ⟨hRbot, htop₁, htop₂, htop₃⟩ | ⟨hSbot, _, _, _⟩
  · -- R = ⊥ means all ranges are zero, so all arms are zero
    apply harms
    have hR₁ : LinearMap.range ρ.A₁ = ⊥ := by
      have h : LinearMap.range ρ.A₁ ≤ R :=
        le_sup_left.trans (le_sup_left (a := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂))
      rw [hRbot] at h; exact bot_unique h
    have hR₂ : LinearMap.range ρ.A₂ = ⊥ := by
      have h : LinearMap.range ρ.A₂ ≤ R :=
        le_sup_right.trans (le_sup_left (a := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂))
      rw [hRbot] at h; exact bot_unique h
    have hR₃ : LinearMap.range ρ.A₃ = ⊥ := by
      have h : LinearMap.range ρ.A₃ ≤ R := le_sup_right
      rw [hRbot] at h; exact bot_unique h
    exact ⟨by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₁)]; simp [hR₁],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₂)]; simp [hR₂],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₃)]; simp [hR₃]⟩
  · have : R = ⊤ := by
      have := hRS.sup_eq_top
      rw [hSbot, sup_bot_eq] at this
      exact this
    exact hR this

-- Helper: a "clean" decomposition where each range lies in one summand.
-- If V = p ⊕ q and each range(Aᵢ) ≤ p or ≤ q, then p = ⊥ or q = ⊥.
private lemma decomp_of_ranges_split {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (p q : Submodule k ρ.V) (hpq : IsCompl p q)
    (h₁ : LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q)
    (h₂ : LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q)
    (h₃ : LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) :
    p = ⊥ ∨ q = ⊥ := by
  -- For each arm: if range ≤ p, use (⊤, ⊥); if range ≤ q, use (⊥, ⊤)
  -- Construct compatible decomposition per arm
  have arm₁ : ∃ (p₁ q₁ : Submodule k ρ.V₁), IsCompl p₁ q₁ ∧
      (∀ x ∈ p₁, ρ.A₁ x ∈ p) ∧ (∀ x ∈ q₁, ρ.A₁ x ∈ q) := by
    rcases h₁ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.V₂), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.A₂ x ∈ p) ∧ (∀ x ∈ q₂, ρ.A₂ x ∈ q) := by
    rcases h₂ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.V₃), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.A₃ x ∈ p) ∧ (∀ x ∈ q₃, ρ.A₃ x ∈ q) := by
    rcases h₃ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := arm₁
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

-- When A₁ is surjective (range = ⊤) and A₁ is injective, the comap of a
-- complement p ⊕ q = V gives a valid IsCompl decomposition of V₁.
private lemma comap_isCompl_of_surj_inj {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V] [Module k V]
    (A : V₁ →ₗ[k] V) (hA_inj : Function.Injective A) (hA_surj : LinearMap.range A = ⊤)
    (p q : Submodule k V) (hpq : IsCompl p q) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff]; ext x
    simp only [Submodule.mem_sup, Submodule.mem_comap, Submodule.mem_top, iff_true]
    have hA_surj' : Function.Surjective A := LinearMap.range_eq_top.mp hA_surj
    have hx_top : A x ∈ (⊤ : Submodule k V) := Submodule.mem_top
    rw [← hpq.sup_eq_top] at hx_top
    obtain ⟨yp, hyp, yq, hyq, heq⟩ := Submodule.mem_sup.mp hx_top
    obtain ⟨x₁, hx₁⟩ := hA_surj' yp
    obtain ⟨x₂, hx₂⟩ := hA_surj' yq
    have : x = x₁ + x₂ := hA_inj (by rw [map_add, hx₁, hx₂, heq])
    exact ⟨x₁, by change A x₁ ∈ p; rw [hx₁]; exact hyp,
           x₂, by change A x₂ ∈ q; rw [hx₂]; exact hyq, this.symm⟩

-- dim V ≥ 3, all injective, range sum = ⊤ → decomposable
private lemma decomp_dim_ge_three {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥)
    (hR : LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤)
    (hV : Module.finrank k ρ.V ≥ 3) : False := by
  sorry

-- Helper: if A₁ is bijective in a D₄ rep and p ⊕ q = V with other ranges split,
-- then p = ⊥ or q = ⊥.
private lemma decomp_bijective_and_split {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁_inj : Function.Injective ρ.A₁)
    (hA₁_surj : LinearMap.range ρ.A₁ = ⊤)
    (p q : Submodule k ρ.V) (hpq : IsCompl p q)
    (h₂ : LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q)
    (h₃ : LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) :
    p = ⊥ ∨ q = ⊥ := by
  have hc₁ := comap_isCompl_of_surj_inj ρ.A₁ hA₁_inj hA₁_surj p q hpq
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.V₂), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.A₂ x ∈ p) ∧ (∀ x ∈ q₂, ρ.A₂ x ∈ q) := by
    rcases h₂ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.V₃), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.A₃ x ∈ p) ∧ (∀ x ∈ q₃, ρ.A₃ x ∈ q) := by
    rcases h₃ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q (Submodule.comap ρ.A₁ p) (Submodule.comap ρ.A₁ q)
    p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃
    (fun x hx => hx) (fun x hx => hx)
    hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

-- Helper: if dim V ≥ 2, all injective, range sum = ⊤, indecomposable,
-- then dim V = 2 and all dim Vᵢ = 1.
private lemma classification_injective_dim_bound {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥)
    (hR : LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤)
    (hV : Module.finrank k ρ.V ≥ 2) :
    Module.finrank k ρ.V = 2 ∧ Module.finrank k ρ.V₁ = 1 ∧
    Module.finrank k ρ.V₂ = 1 ∧ Module.finrank k ρ.V₃ = 1 := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  -- dim V ≤ 2 (dim V ≥ 3 is impossible for indecomposable reps)
  have hV_le : Module.finrank k ρ.V ≤ 2 := by
    by_contra h; push_neg at h
    exact decomp_dim_ge_three ρ hind hA₁ hA₂ hA₃ hR (by omega)
  have hV_eq : Module.finrank k ρ.V = 2 := by omega
  -- All arm dims are between 0 and 2 (by injectivity into dim-2 V).
  -- We show each = 1 by eliminating 0 and 2.
  -- Proving all three at once since the arguments are symmetric.
  sorry

-- The main classification for the all-injective case
private lemma classification_injective {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥) :
    ρ.dimVector ∈ D₄_indecomposable_dimVectors := by
  -- Get dimension bounds from injectivity
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  -- Step 2: Either range sum = ⊤ or all arms zero
  rcases range_sum_eq_top_or_arms_zero ρ hind hA₁ hA₂ hA₃ with hR | ⟨h₁, h₂, h₃⟩
  · -- Range sum = ⊤ case
    -- dim V ≥ 1 from nontriviality
    have hV_pos : 0 < Module.finrank k ρ.V := by
      rcases hind.1 with h | h | h | h
      · exact h
      · exact Nat.lt_of_lt_of_le h hle₁
      · exact Nat.lt_of_lt_of_le h hle₂
      · exact Nat.lt_of_lt_of_le h hle₃
    by_cases hV2 : Module.finrank k ρ.V ≥ 2
    · -- dim V ≥ 2: use the dimension bound lemma
      obtain ⟨hd, hd₁, hd₂, hd₃⟩ := classification_injective_dim_bound ρ hind hA₁ hA₂ hA₃ hR hV2
      unfold D₄Rep.dimVector D₄_indecomposable_dimVectors
      rw [hd, hd₁, hd₂, hd₃]
      simp [Finset.mem_insert]
    · -- dim V = 1: all dᵢ ∈ {0, 1}, membership is trivial
      push_neg at hV2
      have hV1 : Module.finrank k ρ.V = 1 := by omega
      have h₁ : Module.finrank k ρ.V₁ ≤ 1 := by omega
      have h₂ : Module.finrank k ρ.V₂ ≤ 1 := by omega
      have h₃ : Module.finrank k ρ.V₃ ≤ 1 := by omega
      simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert, Prod.mk.injEq]
      -- (1, d₁, d₂, d₃) with dᵢ ∈ {0, 1}: enumerate
      interval_cases (Module.finrank k ρ.V₁) <;>
        interval_cases (Module.finrank k ρ.V₂) <;>
          interval_cases (Module.finrank k ρ.V₃) <;> simp_all
  · -- All arms zero: dim V = 1, so dim vector is (1, 0, 0, 0)
    have hV := dim_V_eq_one_of_arms_zero ρ hind h₁ h₂ h₃
    simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert, Prod.mk.injEq]
    right; right; right; left
    exact ⟨hV, h₁, h₂, h₃⟩

theorem Etingof.Example_6_3_1 (k : Type*) [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    ρ.dimVector ∈ D₄_indecomposable_dimVectors := by
  -- Case split on whether each kernel is trivial
  rcases ker_A₁_or_rest_zero ρ hind with hA₁ | ⟨hV, hV₂, hV₃⟩
  · rcases ker_A₂_or_rest_zero ρ hind with hA₂ | ⟨hV, hV₁, hV₃⟩
    · rcases ker_A₃_or_rest_zero ρ hind with hA₃ | ⟨hV, hV₁, hV₂⟩
      · -- All kernels trivial: triple of subspaces problem
        exact classification_injective ρ hind hA₁ hA₂ hA₃
      · -- ker A₃ ≠ ⊥, V = V₁ = V₂ = 0: dim V₃ = 1
        have hV₃ := dim_V₃_eq_one_of_rest_zero ρ hind hV hV₁ hV₂
        simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
          Prod.mk.injEq]
        right; right; left
        exact ⟨hV, hV₁, hV₂, hV₃⟩
    · -- ker A₂ ≠ ⊥, V = V₁ = V₃ = 0: dim V₂ = 1
      have hV₂ := dim_V₂_eq_one_of_rest_zero ρ hind hV hV₁ hV₃
      simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
        Prod.mk.injEq]
      right; left
      exact ⟨hV, hV₁, hV₂, hV₃⟩
  · -- ker A₁ ≠ ⊥, V = V₂ = V₃ = 0: dim V₁ = 1
    have hV₁ := dim_V₁_eq_one_of_rest_zero ρ hind hV hV₂ hV₃
    simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
      Prod.mk.injEq]
    left
    exact ⟨hV, hV₁, hV₂, hV₃⟩

/-- The set of indecomposable dimension vectors has exactly 12 elements,
corresponding to the 12 positive roots of D₄. -/
theorem D₄_indecomposable_dimVectors_card :
    D₄_indecomposable_dimVectors.card = 12 := by
  decide
