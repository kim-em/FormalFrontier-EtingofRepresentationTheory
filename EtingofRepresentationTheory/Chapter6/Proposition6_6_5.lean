import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Proposition 6.6.5: Surjectivity/Injectivity at Sinks and Sources

Let Q be a quiver and V an indecomposable representation.

(1) If i is a sink, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    φ : ⊕_{j→i} V_j → V_i is surjective.

(2) If i is a source, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    ψ : V_i → ⊕_{i→j} V_j is injective.

The proof uses decomposition: if φ is not surjective, complement of Im(φ) gives a
direct sum decomposition, contradicting indecomposability unless V is the simple
representation at i.

## Mathlib correspondence

Requires quiver representation infrastructure (indecomposable representations,
dimension vectors). Not directly available in Mathlib.
-/

/-- A quiver representation is **indecomposable** if it is nonzero and cannot be
written as a direct sum of two nonzero sub-representations.

Formally: ρ is nonzero, and for any pair of subfamilies of submodules
(Wᵥ ≤ ρ.obj v) that are stable under all representation maps and such that
ρ.obj v = Wᵥ ⊕ W'ᵥ for all v, one of the two families is zero everywhere.

A full Lean definition requires sub-representation and internal direct sum
infrastructure; we define it using submodules and `IsCompl`. -/
def Etingof.QuiverRepresentation.IsIndecomposable
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) : Prop :=
  -- Nonzero: at least one vertex space is nontrivial
  (∃ v, Nontrivial (ρ.obj v)) ∧
  -- Cannot decompose: for any pair of complementary sub-representations,
  -- one is trivial.
  ∀ (W₁ W₂ : ∀ v, Submodule k (ρ.obj v)),
    -- Both are stable under all representation maps
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.mapLinear e x ∈ W₁ b) →
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.mapLinear e x ∈ W₂ b) →
    -- They give an internal direct sum at each vertex
    (∀ v, IsCompl (W₁ v) (W₂ v)) →
    -- Then one is trivial
    (∀ v, W₁ v = ⊥) ∨ (∀ v, W₂ v = ⊥)

/-- A quiver representation is the **simple representation at vertex i** if
the space at i is one-dimensional and all other spaces are zero. -/
def Etingof.QuiverRepresentation.IsSimpleAt
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] : Prop :=
  Module.finrank k (ρ.obj i) = 1 ∧ ∀ j, j ≠ i → Module.finrank k (ρ.obj j) = 0

/-- The canonical map φ : ⊕_{j→i} V_j → V_i at a sink vertex i, defined as the
sum of all representation maps ρ(h) for arrows h : j → i. -/
noncomputable def Etingof.QuiverRepresentation.sinkMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i) (fun a => ρ.mapLinear a.2)

/-- The canonical map ψ : V_i → ⊕_{i→j} V_j at a source vertex i, defined by
mapping x ∈ V_i to the element whose j-th component is ρ(h)(x) for each arrow h : i → j.

This requires choosing a specific construction via the universal property of the
direct sum. The definition is sorry'd pending proper infrastructure. -/
noncomputable def Etingof.QuiverRepresentation.sourceMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) :=
  sorry -- TODO: construct via DirectSum.lof components

/-- For an indecomposable representation at a sink, either V is the simple
representation at i, or the canonical map ⊕_{j→i} V_j → V_i is surjective.
(Etingof Proposition 6.6.5, part 1) -/
theorem Etingof.Proposition6_6_5_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hi : Etingof.IsSink Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Surjective (ρ.sinkMap i) :=
  sorry

/-- For an indecomposable representation at a source, either V is the simple
representation at i, or the canonical map V_i → ⊕_{i→j} V_j is injective.
(Etingof Proposition 6.6.5, part 2) -/
theorem Etingof.Proposition6_6_5_source
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hi : Etingof.IsSource Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Injective (ρ.sourceMap i) :=
  sorry
