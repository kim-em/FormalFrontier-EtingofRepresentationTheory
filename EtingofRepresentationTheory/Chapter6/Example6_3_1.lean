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

-- The main classification: all maps injective case requires the triple of subspaces
-- problem. This is the heart of Example 6.3.1 and requires substantial Lean machinery.
-- For now, we sorry this part and handle the kernel cases.
private lemma classification_injective {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥) :
    ρ.dimVector ∈ D₄_indecomposable_dimVectors := by
  -- When all maps are injective, we identify V₁, V₂, V₃ with subspaces of V
  -- and solve the triple of subspaces problem:
  -- Step 2: Split off complement of range(A₁)+range(A₂)+range(A₃) → (1,0,0,0) or sum = V
  -- Step 3: Split off triple intersection → (1,1,1,1) or triple intersection = 0
  -- Step 4: Split off pairwise intersections → (1,1,*,0) types or pairwise disjoint
  -- Step 5: Split off Vᵢ ∩ (Vⱼ⊕Vₖ) complements → (1,*,0,0) types or containment
  -- Step 6: Remaining case → dim V = 2n, each Vᵢ has dim n → n copies of (2,1,1,1)
  --         Indecomposability forces n = 1 → (2,1,1,1)
  sorry

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
