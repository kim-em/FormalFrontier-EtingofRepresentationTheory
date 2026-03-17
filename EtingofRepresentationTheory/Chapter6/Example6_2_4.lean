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
The interior case (all Vᵢ nonzero) requires a chain of decomposition arguments:
ker f = ⊥, range g = ⊤, then g∘f injective → range(g∘f) = V₃ → ker g = ⊥ →
g bijective → all dimensions = 1.
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

/-- **Example 6.2.4 (Etingof)**: Every indecomposable representation of the A₃ quiver
(• → • → •) has dimension triple in
{(1,0,0),(0,1,0),(0,0,1),(1,1,0),(0,1,1),(1,1,1)},
with appropriate injectivity conditions on the maps.

The proof strategy:
1. If V₂ = 0: decomposes as (V₁,0,0) ⊕ (0,0,V₃), reduces to A₁
2. If V₁ = 0 or V₃ = 0: reduces to A₂ via Example 6.2.3
3. If all nonzero: ker f = ⊥ (decompose via (ker f, ⊥, ⊥)),
   range g = ⊤ (decompose via (⊥, ⊥, range g)), then a chain of
   composition arguments shows g∘f bijective, ker g = ⊥, and all dims = 1. -/
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
  -- The proof uses decomposition arguments reducing to Examples 6.2.2 and 6.2.3.
  -- Key structural lemmas (proved via specific decompositions):
  -- 1. ker f = ⊥ ∨ (V₂ = 0 ∧ V₃ = 0): decompose (ker f, ⊥, ⊥) ⊕ (compl, V₂, V₃)
  -- 2. range g = ⊤ ∨ (V₁ = 0 ∧ V₂ = 0): decompose (⊥, ⊥, range g) ⊕ (V₁, V₂, compl)
  -- 3. ker(g∘f) = ⊥: decompose (ker(g∘f), f(ker(g∘f)), ⊥) ⊕ (compl, Q₂, V₃)
  --    where Q₂ ⊇ f(compl) and f(ker(g∘f)) ⊆ ker g
  -- 4. range(g∘f) = V₃: decompose (V₁, comap g range(g∘f), range(g∘f)) ⊕ (⊥, B, g(B))
  -- 5. ker g = ⊥: use (W₁, f(W₁), g∘f(W₁)) ⊕ (C₁, f(C₁)⊕ker_g, g∘f(C₁))
  -- 6. g bijective → lift V₁ decomposition through f,g → V₁ indecomposable → dim = 1
  sorry
