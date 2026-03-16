import Mathlib

/-!
# Definition 6.5.1: Dimension Vector

Let Q be a quiver with vertices labeled 1, …, n. Let V = (V₁, …, Vₙ) be a
representation of Q. The **dimension vector** of this representation is
  d(V) = (dim V₁, …, dim Vₙ).

## Mathlib correspondence

The dimension vector of a quiver representation is not in Mathlib. It needs to be
defined as a function from vertices to ℕ, mapping each vertex to the dimension
of the corresponding vector space in the representation.

## Formalization note

This is a straightforward definition: given a quiver Q and a representation
assigning a finite-dimensional vector space to each vertex, the dimension vector
records the dimensions.
-/

/-- The dimension vector of a quiver representation assigns to each vertex i
the dimension of the vector space Vᵢ at that vertex.
(Etingof Definition 6.5.1) -/
noncomputable def Etingof.dimensionVector {V : Type*} [Fintype V] (k : Type*)
    [Field k] (spaces : V → Type*)
    [∀ v, AddCommGroup (spaces v)] [∀ v, Module k (spaces v)]
    [∀ v, FiniteDimensional k (spaces v)] :
    V → ℕ :=
  fun v => Module.finrank k (spaces v)
