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

/-- The canonical map φ : ⊕_{j→i} V_j → V_i at a sink vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sinkMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i) (fun a => ρ.mapLinear a.2)

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
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V) :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) :=
  -- φ : ⊕_{j→i} ρ_j → ρ_i, the canonical sink map
  let φ := ρ.sinkMap i
  -- Use Decidable.casesOn with the [DecidableEq V] instance to construct
  -- obj, AddCommMonoid, and Module coherently. All three fields share the same
  -- Decidable instance, so the type-level case-split computes correctly.
  let dp : ∀ v, Decidable (v = i) := fun v => inst v i
  let objAt : ∀ v, Decidable (v = i) → Type _ :=
    fun v d => @Decidable.casesOn _ (fun _ => Type _) d (fun _ => ρ.obj v) (fun _ => ↥φ.ker)
  let acmAt : ∀ v d, AddCommMonoid (objAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => AddCommMonoid (objAt v d)) d
      (fun _ => ρ.instAddCommMonoid v) (fun _ => Submodule.addCommMonoid φ.ker)
  let modAt : ∀ v d, @Module k (objAt v d) _ (acmAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => @Module k (objAt v d) _ (acmAt v d)) d
      (fun _ => ρ.instModule v) (fun _ => Submodule.module φ.ker)
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => objAt v (dp v))
    (fun v => acmAt v (dp v))
    (fun v => modAt v (dp v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) =>
      -- Reinterpret e's type to explicitly use dp (= inst · i), so that
      -- matching dp a, dp b, e' simultaneously puts dp in the motive.
      -- This avoids Eq.mpr casts and ensures mapLinear uses the same
      -- Decidable instance as obj.
      show objAt a (dp a) →ₗ[k] objAt b (dp b) from
      let e' : @ite _ (a = i) (dp a)
          (@ite _ (b = i) (dp b) (a ⟶ b) (b ⟶ i))
          (@ite _ (b = i) (dp b) (i ⟶ a) (a ⟶ b)) := e
      match dp a, dp b, e' with
      | .isFalse _, .isFalse _, e =>
        -- a ≠ i, b ≠ i: unchanged arrow, pass through ρ.mapLinear
        ρ.mapLinear e
      | .isTrue _, .isFalse _, e =>
        -- a = i, b ≠ i: reversed arrow, ker φ ↪ ⊕ → proj_b
        (DirectSum.component k (Etingof.ArrowsInto V i)
          (fun x => ρ.obj x.1) ⟨b, e⟩).comp
          (LinearMap.ker φ).subtype
      | .isFalse _, .isTrue _, e =>
        -- a ≠ i, b = i: arrow i → a, vacuous since i is a sink
        ((hi a).false e).elim
      | .isTrue ha, .isTrue _, e =>
        -- a = i, b = i: self-loop at i, vacuous since i is a sink
        by subst ha; exact ((hi b).false e).elim)

section ReflectionFunctorPlusAPI

/-! ## API for `reflectionFunctorPlus`

The reflection functor `F⁺ᵢ` is defined using `Decidable.casesOn`, making the types
at each vertex opaque. These API lemmas provide `LinearEquiv`s that reduce the
`Decidable.casesOn` once, so downstream proofs can compose them without
re-doing the case analysis. -/

/-- At a vertex v ≠ i, the type `F⁺ᵢ(ρ).obj v` is propositionally equal to `ρ.obj v`. -/
theorem Etingof.reflFunctorPlus_obj_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v = ρ.obj v := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- At vertex i, the type `F⁺ᵢ(ρ).obj i` is propositionally equal to `ker(sinkMap i)`. -/
theorem Etingof.reflFunctorPlus_obj_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i = ↥(ρ.sinkMap i).ker := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

/-- `LinearEquiv` at vertex v ≠ i: `F⁺ᵢ(ρ).obj v ≃ₗ[k] ρ.obj v`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorPlus` definition. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) v ≃ₗ[k] ρ.obj v := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- `LinearEquiv` at vertex i: `F⁺ᵢ(ρ).obj i ≃ₗ[k] ker(sinkMap i)`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorPlus` definition. -/
noncomputable def Etingof.reflFunctorPlus_equivAt_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i ≃ₗ[k] ↥(ρ.sinkMap i).ker := by
  unfold Etingof.reflectionFunctorPlus
  simp only
  match hd : (‹DecidableEq Q› i i) with
  | .isTrue _ => rw [hd]
  | .isFalse hii => exact absurd rfl hii

end ReflectionFunctorPlusAPI
