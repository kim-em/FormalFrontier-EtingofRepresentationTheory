import Mathlib

/-!
# Definition 6.4.10: Reflections and Simple Reflections

For a positive root α ∈ ℤⁿ, the reflection sα is defined by
  sα(v) = v - B(v, α) · α

The reflections sᵢ = sαᵢ (for simple roots αᵢ) are called **simple reflections**.

## Mathlib correspondence

Mathlib has reflections in the context of root pairings via `RootPairing.reflection`
and Weyl group elements. The formula matches the standard definition.
-/

/-- The reflection associated to a root α, defined by sα(v) = v - B(v, α)·α,
where B is the bilinear form of the Cartan matrix A.
(Etingof Definition 6.4.10) -/
def Etingof.rootReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  v - (dotProduct v (A.mulVec α)) • α

/-- The i-th simple reflection is the reflection associated to the i-th simple root αᵢ.
(Etingof Definition 6.4.10) -/
def Etingof.simpleReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (Fin n → ℤ) → (Fin n → ℤ) :=
  Etingof.rootReflection n A (Pi.single i 1)
