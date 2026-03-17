import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import Mathlib.LinearAlgebra.Prod

/-!
# Definition 2.8.9: Direct Sum of Quiver Representations

The **direct sum** of two quiver representations assigns to each vertex the direct sum
of the vector spaces, and to each arrow the direct sum of the linear maps.

## Mathlib correspondence (partial)

No direct Mathlib support. We provide the construction using `Prod` and `LinearMap.prodMap`.
-/

/-- The direct sum of two quiver representations, in the sense of Etingof Definition 2.8.9.
At each vertex, takes the product of the two vector spaces; at each arrow, takes the
product map. -/
noncomputable def Etingof.QuiverRepresentation.directSum (k : Type*) (Q : Type*)
    [CommSemiring k] [Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) : Etingof.QuiverRepresentation k Q where
  obj := fun v => ρ₁.obj v × ρ₂.obj v
  mapLinear := fun h => (ρ₁.mapLinear h).prodMap (ρ₂.mapLinear h)
