import EtingofRepresentationTheory.Chapter2.Definition2_8_3

/-!
# Definition 2.8.9: Direct Sum of Quiver Representations

The **direct sum** of two quiver representations assigns to each vertex the direct sum
of the vector spaces, and to each arrow the direct sum of the linear maps.

## Mathlib correspondence (partial)

No direct Mathlib support. We provide a sorry'd construction.
-/

/-- The direct sum of two quiver representations, in the sense of Etingof Definition 2.8.9.
At each vertex, takes the product of the two vector spaces; at each arrow, takes the
product map. -/
noncomputable def Etingof.QuiverRepresentation.directSum (k : Type*) (Q : Type*)
    [CommSemiring k] [Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) : Etingof.QuiverRepresentation k Q :=
  sorry
