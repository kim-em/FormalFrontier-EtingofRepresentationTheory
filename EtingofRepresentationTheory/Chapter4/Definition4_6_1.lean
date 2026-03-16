import Mathlib

/-!
# Definition 4.6.1: Unitary Representation

A **unitary** finite dimensional representation of a group G is a representation
(ρ, V) on a complex vector space V equipped with a G-invariant positive definite
Hermitian form (·,·), i.e., such that ρ(g) are unitary operators:
  (ρ(g)v, ρ(g)w) = (v, w) for all g ∈ G, v, w ∈ V.

## Mathlib correspondence

Mathlib does not have a dedicated `UnitaryRepresentation` type. This can be modeled as a
`Representation ℂ G V` where V carries an `InnerProductSpace ℂ V` structure and ρ(g)
preserves the inner product (i.e., each ρ(g) is a unitary operator).
-/

/-- A unitary representation: a representation where each group element acts by a
unitary operator with respect to a given inner product. (Etingof Definition 4.6.1) -/
structure Etingof.UnitaryRepresentation
    (G : Type*) [Group G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying representation. -/
  ρ : Representation ℂ G V
  /-- Each group element acts unitarily: preserves the inner product. -/
  unitary : ∀ g : G, ∀ v w : V,
    @inner ℂ V _ (ρ g v) (ρ g w) = @inner ℂ V _ v w
