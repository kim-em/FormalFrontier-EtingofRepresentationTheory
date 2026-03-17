import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1

/-!
# Corollary 6.8.2: Dimension Vectors Are Positive Roots

For any indecomposable representation V of a Dynkin quiver Q, d(V) is a positive root,
i.e., B(d(V), d(V)) = 2.

The proof: by Theorem 6.8.1, s_{i₁} ⋯ s_{iₘ}(d(V)) = αₚ. Since the sᵢ preserve B,
B(d(V), d(V)) = B(αₚ, αₚ) = 2.

## Mathlib correspondence

Requires dimension vectors, simple reflections preserving the bilinear form,
and Theorem 6.8.1. This is part of Gabriel's theorem (classification of
quivers of finite representation type).
-/

/-- Simple reflections preserve the Cartan bilinear form:
B(sᵢ(x), sᵢ(x)) = B(x, x) for any x ∈ ℤⁿ. -/
theorem Etingof.simpleReflection_preserves_bilinearForm
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (i : Fin n) (x : Fin n → ℤ) :
    dotProduct (Etingof.simpleReflection n A i x)
      (A.mulVec (Etingof.simpleReflection n A i x)) =
    dotProduct x (A.mulVec x) :=
  sorry

/-- Iterated simple reflections preserve the Cartan bilinear form. -/
theorem Etingof.iteratedSimpleReflection_preserves_bilinearForm
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (vertices : List (Fin n)) (x : Fin n → ℤ) :
    dotProduct (Etingof.iteratedSimpleReflection n A vertices x)
      (A.mulVec (Etingof.iteratedSimpleReflection n A vertices x)) =
    dotProduct x (A.mulVec x) :=
  sorry

/-- The dimension vector of any indecomposable representation of a Dynkin quiver
is a positive root.

Given that d is the dimension vector of an indecomposable representation of a
Dynkin quiver (so d ≥ 0, d ≠ 0, and by Theorem 6.8.1 there exist reflections
reducing d to a simple root), we conclude that d is a positive root:
d ≠ 0, B(d, d) = 2, and all coordinates are nonneg.

The proof reduces to: simple reflections preserve B, and B(αₚ, αₚ) = 2 for
any simple root αₚ.
(Etingof Corollary 6.8.2) -/
theorem Etingof.Corollary6_8_2
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hreflect : ∃ (vertices : List (Fin n)) (p : Fin n),
      Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices d =
        Etingof.simpleRoot n p) :
    Etingof.IsPositiveRoot n adj d :=
  sorry
