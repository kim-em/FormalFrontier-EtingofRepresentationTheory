import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import Mathlib.Algebra.DirectSum.Module

/-!
# Definition 6.6.3: Reflection Functor F⁺ᵢ (at a Sink)

Let Q be a quiver and i ∈ Q be a sink. The reflection functor
F⁺ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁺ᵢ(V)_k = V_k for k ≠ i
- F⁺ᵢ(V)_i = ker(φ : ⊕_{j→i} V_j → V_i)

All maps stay the same except those now pointing out of i; these are replaced by
compositions of the inclusion of ker φ into ⊕_{j→i} V_j with the projections
⊕_{j→i} V_j → V_j.

## Mathlib correspondence

Bernstein-Gelfand-Ponomarev (BGP) reflection functors are not in Mathlib.
Needs custom definition using `LinearMap.ker`, `DirectSum`, and composition of
linear maps. The functor goes from representations of Q to representations of Q̄ᵢ.
-/

/-- The type indexing the direct sum for F⁺ᵢ: pairs (j, h) where h : j ⟶ i is an arrow
into the sink vertex i. -/
def Etingof.ArrowsInto (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (j ⟶ i)

/-- The reflection functor F⁺ᵢ at a sink vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁺ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁺ᵢ(ρ)_i = ker(φ) where φ : ⊕_{j→i} ρ_j → ρ_i is the sum of
the representation maps ρ(h) for each arrow h : j → i.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows out of i in Q̄ᵢ (= reversed arrows into i in Q):
  ker(φ) ↪ ⊕_{j→i} ρ_j → ρ_j (inclusion then projection)

(Etingof Definition 6.6.3) -/
noncomputable def Etingof.reflectionFunctorPlus
    {k : Type*} [CommSemiring k]
    (V : Type*) [DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) := by
  classical
  -- φ : ⊕_{j→i} ρ_j → ρ_i, the sum of representation maps for arrows into i
  let φ : DirectSum (Etingof.ArrowsInto V i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i :=
    DirectSum.toModule k (Etingof.ArrowsInto V i) (ρ.obj i) (fun a => ρ.mapLinear a.2)
  -- Shared Decidable instance ensures type-level match reduction aligns
  -- between obj, instAddCommMonoid, instModule, and mapLinear.
  let dec : (v : V) → Decidable (v = i) := fun v => Classical.propDecidable _
  -- All type-level branching uses Decidable.rec with explicit motives to ensure
  -- obj, AddCommMonoid, and Module reduce in lockstep
  let branch (v : V) (d : Decidable (v = i)) : Type _ :=
    d.rec (fun _ => ρ.obj v) (fun _ => ↥(LinearMap.ker φ))
  refine @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => branch v (dec v))
    (fun v => @Decidable.rec (v = i) (fun d => AddCommMonoid (branch v d))
      (fun _ => inferInstance) (fun _ => inferInstance) (dec v))
    (fun v => @Decidable.rec (v = i)
      (fun d => @Module k (branch v d) _
        (@Decidable.rec (v = i) (fun d => AddCommMonoid (branch v d))
          (fun _ => inferInstance) (fun _ => inferInstance) d))
      (fun _ => inferInstance) (fun _ => inferInstance) (dec v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => ?_)
  -- mapLinear: dispatch on dec a and dec b
  -- After dsimp, the goal type exposes the Decidable.rec which the match can reduce
  dsimp only [branch]
  match ha : dec a, hb : dec b with
  | .isTrue ha', .isTrue hb' =>
    -- a = i, b = i: self-loop at sink, vacuous
    exfalso
    have hempty : IsEmpty (Etingof.ReversedAtVertexHom V i a b) := by
      unfold Etingof.ReversedAtVertexHom
      rw [if_pos ha', if_pos hb', ha', hb']
      exact hi i
    exact hempty.false e
  | .isTrue ha', .isFalse hb' =>
    -- a = i, b ≠ i: reversed arrow (was b → i in Q, now i → b in Q̄ᵢ)
    have he : (Etingof.ReversedAtVertexHom V i a b) = (b ⟶ i) := by
      unfold Etingof.ReversedAtVertexHom; rw [if_pos ha', if_neg hb']
    -- Goal: ↥(ker φ) →ₗ[k] ρ.obj b
    exact (DirectSum.component k (Etingof.ArrowsInto V i) (fun x => ρ.obj x.1)
      ⟨b, cast he e⟩).comp (LinearMap.ker φ).subtype
  | .isFalse ha', .isTrue hb' =>
    -- a ≠ i, b = i: arrow from a to sink, vacuous (i is a sink)
    exfalso
    have hempty : IsEmpty (Etingof.ReversedAtVertexHom V i a b) := by
      unfold Etingof.ReversedAtVertexHom
      rw [if_neg ha', if_pos hb']
      exact hi a
    exact hempty.false e
  | .isFalse ha', .isFalse hb' =>
    -- a ≠ i, b ≠ i: unchanged arrow in Q
    have he : (Etingof.ReversedAtVertexHom V i a b) = (a ⟶ b) := by
      unfold Etingof.ReversedAtVertexHom; rw [if_neg ha', if_neg hb']
    -- Goal: ρ.obj a →ₗ[k] ρ.obj b
    exact ρ.mapLinear (cast he e)
