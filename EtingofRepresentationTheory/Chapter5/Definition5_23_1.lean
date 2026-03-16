import Mathlib

/-!
# Definition 5.23.1: Algebraic Representation of GL(V)

A finite dimensional representation Y of GL(V) is **algebraic** (or rational,
or polynomial) if its matrix elements are polynomial functions of the entries
of g, g⁻¹, for g ∈ GL(V) — i.e., belong to k[gᵢⱼ][1/det(g)].

## Mathlib correspondence

Not in Mathlib. Needs to be defined from scratch. Related to the regular
representation on the coordinate ring of GL_n.
-/

/-- A representation of GL(V) is algebraic if its matrix elements are
polynomial functions of the matrix entries and 1/det.
(Etingof Definition 5.23.1)

TODO: Define properly once GL_n coordinate ring infrastructure exists. -/
def Etingof.IsAlgebraicRepresentation
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : (Matrix.GeneralLinearGroup (Fin n) k) → Y →ₗ[k] Y) : Prop :=
  sorry
