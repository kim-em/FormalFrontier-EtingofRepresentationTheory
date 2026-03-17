import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import Mathlib.Algebra.DirectSum.Module

/-!
# Definition 6.6.4: Reflection Functor F⁻ᵢ (at a Source)

Let Q be a quiver and i ∈ Q be a source. Let ψ : V_i → ⊕_{i→j} V_j be the
canonical map. The reflection functor F⁻ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁻ᵢ(V)_k = V_k for k ≠ i
- F⁻ᵢ(V)_i = Coker(ψ) = (⊕_{i→j} V_j) / Im ψ

All maps now pointing into i are replaced by the compositions of the inclusions
V_k → ⊕_{i→j} V_j with the natural quotient map ⊕_{i→j} V_j → (⊕_{i→j} V_j)/Im ψ.

## Mathlib correspondence

BGP reflection functors are not in Mathlib. The cokernel-based construction uses
`Submodule.mkQ` for quotient maps and `LinearMap.range` for image.

**Note:** The cokernel construction (quotient module) requires `AddCommGroup`
and `Ring` structure, but `QuiverRepresentation` only assumes `AddCommMonoid`
and `CommSemiring`. A full implementation would either:
1. Strengthen the `QuiverRepresentation` definition to use `AddCommGroup`, or
2. Add `[Ring k]` and `[∀ v, AddCommGroup (ρ.obj v)]` hypotheses here.
This is tracked as a design issue for the reflection functor definitions.
-/

/-- The type indexing the direct sum for F⁻ᵢ: pairs (j, h) where h : i ⟶ j is an arrow
out of the source vertex i. -/
def Etingof.ArrowsOutOf (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)

/-- The reflection functor F⁻ᵢ at a source vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁻ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁻ᵢ(ρ)_i = coker(ψ) where ψ : ρ_i → ⊕_{i→j} ρ_j is the sum of
the representation maps ρ(h) for each arrow h : i → j.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows into i in Q̄ᵢ (= reversed arrows out of i in Q):
  ρ_j → ⊕_{i→j} ρ_j → coker(ψ) (inclusion then quotient)

(Etingof Definition 6.6.4) -/
noncomputable def Etingof.reflectionFunctorMinus
    {k : Type*} [CommSemiring k]
    (V : Type*) [DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) := by
  classical
  -- The cokernel type at vertex i.
  -- Mathematically: (⊕_{i→j} ρ_j) / Im(ψ) where ψ : ρ_i → ⊕_{i→j} ρ_j.
  -- Requires AddCommGroup for quotient modules; QuiverRepresentation only has AddCommMonoid.
  -- Using sorry as a placeholder for the cokernel type.
  let CokerType : Type* := sorry
  letI : AddCommMonoid CokerType := sorry
  letI : Module k CokerType := sorry
  -- The obj field: CokerType at vertex i, ρ.obj v elsewhere.
  -- Same dependent type issues as F⁺ᵢ (Definition 6.6.3).
  refine @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => if v = i then CokerType else ρ.obj v)
    (fun v => by dsimp only; split <;> infer_instance)
    (fun v => by exact sorry)
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      dsimp only
      -- Case split on whether a and b equal i:
      -- Case a ≠ i, b ≠ i: arrow is (a ⟶ b) in Q, map is ρ.mapLinear e
      -- Case a ≠ i, b = i: reversed arrow (i ⟶ a), map is ρ_a →ₗ ⊕ →ₗ coker(ψ)
      --   via (Submodule.mkQ _).comp (DirectSum.lof k _ _ ⟨a, e⟩)
      -- Case a = i, b ≠ i: arrow is (a ⟶ i) in Q; i is source, so vacuous
      -- Case a = i, b = i: arrow is (i ⟶ i) in Q; i is source, so vacuous
      exact sorry)
