import Mathlib

/-!
# Problem 6.9.1: Classification of Indecomposable Representations of Q₂

The cyclic quiver Q₂ has 2 vertices connected by 2 oriented edges forming a cycle:
a pair of linear operators A : V → W and B : W → V.

The classification states that every indecomposable representation of Q₂ belongs to
exactly one of four families:

1. **E_{n,λ}** (n ≥ 1, λ ∈ ℂ): V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id
2. **E_{n,∞}** (n ≥ 1): obtained from E_{n,0} by exchanging V ↔ W and A ↔ B
3. **H_n** (n ≥ 1): V = ℂⁿ, W = ℂⁿ⁻¹, A sends basis vᵢ to wᵢ (i < n), vₙ to 0,
   B sends wᵢ to v_{i+1}
4. **K_n** (n ≥ 1): obtained from H_n by exchanging V ↔ W and A ↔ B

## Mathlib correspondence

Not in Mathlib. The classification relies on the Jordan normal form theorem and
a chain decomposition argument for nilpotent operators.
-/

/-- A representation of the cyclic quiver Q₂: a pair of vector spaces V, W with
linear maps A : V → W and B : W → V. -/
structure Q₂Rep (k : Type*) [Field k] where
  V : Type*
  W : Type*
  [instACV : AddCommGroup V]
  [instModV : Module k V]
  [instFDV : FiniteDimensional k V]
  [instACW : AddCommGroup W]
  [instModW : Module k W]
  [instFDW : FiniteDimensional k W]
  A : V →ₗ[k] W
  B : W →ₗ[k] V

attribute [instance] Q₂Rep.instACV Q₂Rep.instModV Q₂Rep.instFDV
  Q₂Rep.instACW Q₂Rep.instModW Q₂Rep.instFDW

/-- A Q₂-representation is indecomposable if it is nontrivial and for any
compatible decomposition V = V' ⊕ V'', W = W' ⊕ W'' (with A, B respecting
the decomposition), one of the summands is zero. -/
def Q₂Rep.Indecomposable {k : Type*} [Field k] (ρ : Q₂Rep k) : Prop :=
  (0 < Module.finrank k ρ.V ∨ 0 < Module.finrank k ρ.W) ∧
  ∀ (pV qV : Submodule k ρ.V) (pW qW : Submodule k ρ.W),
    IsCompl pV qV → IsCompl pW qW →
    (∀ x ∈ pV, ρ.A x ∈ pW) → (∀ x ∈ qV, ρ.A x ∈ qW) →
    (∀ x ∈ pW, ρ.B x ∈ pV) → (∀ x ∈ qW, ρ.B x ∈ qV) →
    (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥)

/-- **Problem 6.9.1(a), Family E_{n,λ} (Etingof)**: For n ≥ 1 and λ ∈ ℂ,
the Q₂-representation with V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id is
indecomposable. This family is parameterized by (n, λ) ∈ ℕ₊ × ℂ. -/
noncomputable def Etingof.Q₂Rep_E (n : ℕ) (hn : 0 < n) (eigenval : ℂ) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin n)
  A := sorry -- Jordan block J_n(eigenval) as a linear map
  B := LinearMap.id

/-- **Problem 6.9.1(a), Family H_n (Etingof)**: For n ≥ 1, V = ℂⁿ with basis vᵢ,
W = ℂⁿ⁻¹ with basis wᵢ. A sends vᵢ ↦ wᵢ (i < n) and vₙ ↦ 0.
B sends wᵢ ↦ v_{i+1}. This is an indecomposable representation with dim V ≠ dim W. -/
noncomputable def Etingof.Q₂Rep_H (n : ℕ) (hn : 0 < n) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin (n - 1))
  A := sorry -- vᵢ ↦ wᵢ for i < n-1, vₙ ↦ 0
  B := sorry -- wᵢ ↦ v_{i+1}

/-- **Problem 6.9.1(a) (Etingof)**: The four families E_{n,λ}, E_{n,∞}, H_n, K_n
(as defined above) are indecomposable and pairwise nonisomorphic. Moreover, these
are all the indecomposable representations of Q₂.

Specifically, every indecomposable representation of Q₂ is isomorphic to exactly one of:
- E_{n,λ} for some n ≥ 1, λ ∈ ℂ
- E_{n,∞} for some n ≥ 1 (obtained from E_{n,0} by swapping V ↔ W and A ↔ B)
- H_n for some n ≥ 1
- K_n for some n ≥ 1 (obtained from H_n by swapping V ↔ W and A ↔ B)

This extends the Jordan normal form classification from Q₁ (single vertex with a loop)
to Q₂ (two vertices with a cycle). -/
theorem Etingof.Problem6_9_1 (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable) :
    -- The representation belongs to one of the four families (existential form):
    -- Either dim V = dim W (E_{n,λ} or E_{n,∞} family)
    -- or |dim V - dim W| = 1 (H_n or K_n family)
    (Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W ∨
     Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W + 1 ∨
     Module.finrank ℂ ρ.W = Module.finrank ℂ ρ.V + 1) := by
  sorry

/-- **Problem 6.9.1(b) (Etingof)**: If AB : W → W is not nilpotent in a Q₂-representation,
then the representation decomposes as E' ⊕ E_{n,λ} for some λ ≠ 0.

This reduces the classification to the case where AB is nilpotent. -/
theorem Etingof.Problem6_9_1b (ρ : Q₂Rep ℂ)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    ∃ (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, ρ.A x ∈ pW) ∧ (∀ x ∈ qV, ρ.A x ∈ qW) ∧
      (∀ x ∈ pW, ρ.B x ∈ pV) ∧ (∀ x ∈ qW, ρ.B x ∈ qV) ∧
      -- The q-summand has equal dimensions (E_{n,λ} type with λ ≠ 0)
      Module.finrank ℂ (↥qV) = Module.finrank ℂ (↥qW) := by
  sorry

/-- **Problem 6.9.1(c) (Etingof)**: When AB is nilpotent, the operator X on V ⊕ W
defined by X(v,w) = (Bw, Av) is also nilpotent and admits a basis of chains
compatible with the V ⊕ W decomposition.

This reduces to showing X has a Jordan chain basis where each chain starts in either
V or W. The chain structure directly gives the H_n and K_n families. -/
theorem Etingof.Problem6_9_1c (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B)) :
    -- The operator X = (0, B; A, 0) on V × W is nilpotent
    IsNilpotent ((ρ.B.comp ρ.A).prodMap (ρ.A.comp ρ.B) : (ρ.V × ρ.W) →ₗ[ℂ] (ρ.V × ρ.W)) := by
  sorry
