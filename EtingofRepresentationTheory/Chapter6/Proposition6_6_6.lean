import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Proposition 6.6.6: Inverse Relationship of Reflection Functors

(1) If φ : ⊕_{j→i} V_j → V_i is surjective, then F⁻ᵢ F⁺ᵢ V ≅ V.
(2) If ψ : V_i → ⊕_{i→j} V_j is injective, then F⁺ᵢ F⁻ᵢ V ≅ V.

The proof uses the homomorphism theorem: when φ is surjective, K = ker φ embeds
in ⊕V_j, and then (⊕V_j)/K ≅ Im φ = V_i.

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

section Reversal

/-- A sink in Q becomes a source in the reversed quiver Q̄ᵢ.
All arrows into i in Q̄ᵢ correspond to arrows out of i in Q, which are empty
since i is a sink. -/
theorem Etingof.isSink_reversedAtVertex_isSource
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) :
    @Etingof.IsSource Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i j i at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq hj rfl] at e
    rw [hj] at e; exact (hi i).false e
  · rw [Etingof.ReversedAtVertexHom_ne_eq hj rfl] at e
    exact (hi j).false e

/-- A source in Q becomes a sink in the reversed quiver Q̄ᵢ.
All arrows out of i in Q̄ᵢ correspond to arrows into i in Q, which are empty
since i is a source. -/
theorem Etingof.isSource_reversedAtVertex_isSink
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) :
    @Etingof.IsSink Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact (hi i).false e
  · rw [Etingof.ReversedAtVertexHom_eq_ne rfl hj] at e
    exact (hi j).false e

end Reversal

section Iso

/-- An isomorphism between two quiver representations on the same quiver.
Consists of pointwise linear equivalences that commute with the representation maps. -/
structure Etingof.QuiverRepresentation.Iso
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) : Type _ where
  /-- Pointwise linear equivalences between vertex spaces -/
  equivAt : ∀ v : Q, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- Naturality: the diagram commutes -/
  naturality : ∀ {a b : Q} (e : a ⟶ b) (x : ρ₁.obj a),
    (equivAt b) (ρ₁.mapLinear e x) = ρ₂.mapLinear e ((equivAt a) x)

/-- The double reversal at vertex i recovers the original quiver instance.
This enables transporting representations from (Q̄ᵢ)̄ᵢ back to Q. -/
@[ext]
private theorem Quiver.ext' {V : Type*} {inst₁ inst₂ : Quiver V}
    (h : ∀ a b, @Quiver.Hom V inst₁ a b = @Quiver.Hom V inst₂ a b) :
    inst₁ = inst₂ := by
  cases inst₁; cases inst₂
  congr 1; funext a b; exact h a b

private theorem Etingof.reversedAtVertex_twice
    (Q : Type*) [DecidableEq Q] [inst : Quiver Q] (i : Q) :
    @Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i = inst := by
  apply Quiver.ext'
  intro a b
  change @Etingof.ReversedAtVertexHom Q _ (Etingof.reversedAtVertex Q i) i a b = (a ⟶ b)
  -- Two-layer reduction: outer ReversedAtVertexHom uses reversed quiver,
  -- inner uses original quiver. Use `trans` + `change` to bridge.
  by_cases ha : a = i <;> by_cases hb : b = i
  · -- a = i, b = i
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b
    · exact @Etingof.ReversedAtVertexHom_eq_eq Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i a b = (a ⟶ b)
      exact Etingof.ReversedAtVertexHom_eq_eq ha hb
  · -- a = i, b ≠ i: outer gives reversed (b ⟶ i in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) b i
    · exact @Etingof.ReversedAtVertexHom_eq_ne Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i b i = (a ⟶ b)
      rw [Etingof.ReversedAtVertexHom_ne_eq hb rfl]
      exact congrArg (· ⟶ b) ha.symm
  · -- a ≠ i, b = i: outer gives reversed (i ⟶ a in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i a
    · exact @Etingof.ReversedAtVertexHom_ne_eq Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i i a = (a ⟶ b)
      rw [Etingof.ReversedAtVertexHom_eq_ne rfl ha]
      exact congrArg (a ⟶ ·) hb.symm
  · -- a ≠ i, b ≠ i: outer gives unchanged (a ⟶ b in reversed quiver)
    trans @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b
    · exact @Etingof.ReversedAtVertexHom_ne_ne Q _ (Etingof.reversedAtVertex Q i) i a b ha hb
    · change Etingof.ReversedAtVertexHom Q i a b = (a ⟶ b)
      exact Etingof.ReversedAtVertexHom_ne_ne ha hb

/-- Transport a representation from the double-reversed quiver (Q̄ᵢ)̄ᵢ back to Q.

Reversing all arrows at vertex i twice recovers the original quiver. Vertex spaces
are unchanged; maps are transported through the canonical arrow identification. -/
noncomputable def Etingof.QuiverRepresentation.transportReversedTwice
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q}
    (ρ : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i)) :
    Etingof.QuiverRepresentation k Q :=
  Etingof.reversedAtVertex_twice Q i ▸ ρ

/-- If we can construct a `QuiverRepresentation.Iso` between ρ₁ and ρ₂ on
quiver instance `inst₁`, this gives an Iso between `(h ▸ ρ₁)` and `(h ▸ ρ₂)` on `inst₂`.
This is the key lemma for handling the `Eq.mpr` from `transportReversedTwice`. -/
private noncomputable def Etingof.QuiverRepresentation.transport_iso
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₁}
    (iso : @Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ ρ₂) :
    @Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) (h ▸ ρ₂) := by
  subst h; exact iso

/-- Key lemma: to prove `Nonempty (Iso (h ▸ ρ₁) ρ₂)` on `inst₂`,
it suffices to prove `Nonempty (Iso ρ₁ (h.symm ▸ ρ₂))` on `inst₁`.
This allows working on a single quiver instance after `subst`. -/
private theorem Etingof.QuiverRepresentation.Iso.transport_nonempty
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ : @Etingof.QuiverRepresentation k Q _ inst₁}
    {ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₂}
    (iso : Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ (h.symm ▸ ρ₂))) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) ρ₂) := by
  subst h; exact iso

/-- A cross-quiver isomorphism: linear equivalences at each vertex between
representations on potentially different (but equal) quiver instances.
Uses `@` notation throughout to avoid synthesis check issues.
Converts to a standard Iso via `subst`. -/
private noncomputable def Etingof.QuiverRepresentation.crossIsoToIso
    {k : Type*} [CommSemiring k] {Q : Type*}
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ : @Etingof.QuiverRepresentation k Q _ inst₁}
    {ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₂}
    (equivAt : ∀ v : Q,
      @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ₁ v ≃ₗ[k]
      @Etingof.QuiverRepresentation.obj k Q _ inst₂ ρ₂ v)
    (naturality : ∀ {a b : Q} (e : @Quiver.Hom Q inst₂ a b)
      (x : @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ₁ a),
      (equivAt b)
        (@Etingof.QuiverRepresentation.mapLinear k Q _ inst₁ ρ₁ a b (h.symm ▸ e) x) =
      @Etingof.QuiverRepresentation.mapLinear k Q _ inst₂ ρ₂ a b e ((equivAt a) x)) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) ρ₂) := by
  subst h; exact ⟨⟨equivAt, naturality⟩⟩

end Iso

section Helpers

/-- The obj of a ▸-transported representation is unchanged at each vertex. -/
private theorem Etingof.QuiverRepresentation.obj_transport
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    (ρ : @Etingof.QuiverRepresentation k Q _ inst₁) (v : Q) :
    @Etingof.QuiverRepresentation.obj k Q _ inst₂ (h ▸ ρ) v =
    @Etingof.QuiverRepresentation.obj k Q _ inst₁ ρ v := by
  subst h; rfl

-- Note: reflFunctorPlus_obj_ne, reflFunctorPlus_obj_eq, reflFunctorMinus_obj_ne
-- are now public API in Definition6_6_3.lean and Definition6_6_4.lean.
-- The reflFunctorPlus_equivAt_ne and reflFunctorPlus_equivAt_eq LinearEquivs
-- are also available from Definition6_6_3.lean.

/-- For an arrow `i →_{Q̄ᵢ} j` in the reversed quiver (with i a sink), the target vertex
j ≠ i. This is because i is a source in Q̄ᵢ. -/
private theorem Etingof.arrowsOutReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact ((hi i).false e).elim
  · exact hj

/-- Extract the original arrow j →_Q i from a reversed arrow i →_{Q̄ᵢ} j. -/
private def Etingof.arrowsOutReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ⟶ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  have hne := Etingof.arrowsOutReversed_ne hi ⟨j, e⟩
  rw [Etingof.ReversedAtVertexHom_eq_ne rfl hne] at e; exact e

/-- Map arrows into i in Q to arrows out of i in Q̄ᵢ.
Since i is a sink (no arrows out), any arrow j → i in Q gives a reversed
arrow i →_{Q̄ᵢ} j. The underlying arrow data is unchanged. -/
private def Etingof.arrowsInto_to_arrowsOutReversed
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i := by
  obtain ⟨j, e⟩ := b
  refine ⟨j, ?_⟩
  -- Need i →_{Q̄ᵢ} j, i.e., ReversedAtVertexHom Q i i j
  change Etingof.ReversedAtVertexHom Q i i j
  have hji : j ≠ i := by
    intro heq; rw [heq] at e; exact (hi i).false e
  rw [Etingof.ReversedAtVertexHom_eq_ne rfl hji]; exact e

/-- The component of `arrowsInto_to_arrowsOutReversed` at j gives the original arrow j ⟶ i. -/
private theorem Etingof.arrowsInto_to_arrowsOutReversed_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    (Etingof.arrowsInto_to_arrowsOutReversed hi b).fst = b.fst := by
  rfl

/-- Round-trip: extracting the original arrow from a reversed-then-unreversed arrow
recovers the original. This is used to connect Φ_component with sinkMap. -/
private theorem Etingof.origArrow_arrowsInto_roundtrip
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    Etingof.arrowsOutReversed_origArrow hi
      (Etingof.arrowsInto_to_arrowsOutReversed hi b) = b.2 := by
  obtain ⟨j, e⟩ := b
  unfold arrowsOutReversed_origArrow arrowsInto_to_arrowsOutReversed
  simp only [id]
  -- Goal: h.mp (h.mpr e) = e where h : ReversedAtVertexHom Q i i j = (j ⟶ i)
  -- Convert to cast form and use cast_cast to cancel
  change cast _ (cast _ e) = e
  rw [cast_cast]; rfl

/-- At v ≠ i, F⁻(F⁺(V)).obj v ≃ₗ[k] ρ.obj v. Both sides reduce to ρ.obj v
through the Decidable.casesOn in the reflection functor definitions. -/
private noncomputable def Etingof.equivAt_ne_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorMinus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) _) v ≃ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ inst ρ v := by
  unfold Etingof.reflectionFunctorMinus
  simp only
  match hd1 : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ =>
    rw [hd1]; dsimp only []
    -- After reducing F⁻, goal becomes F⁺(V).obj v ≃ₗ[k] ρ.obj v
    -- Unfold F⁺ and reduce similarly
    unfold Etingof.reflectionFunctorPlus
    simp only
    match hd2 : (‹DecidableEq Q› v i) with
    | .isTrue hvi => exact absurd hvi hv
    | .isFalse _ => rw [hd2]

open scoped Classical in
/-- sinkMap applied to a single direct sum component gives the representation map. -/
private theorem Etingof.sinkMap_of
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    (b : Etingof.ArrowsInto Q i) (v : ρ.obj b.fst) :
    (ρ.sinkMap i) (DirectSum.of (fun a => ρ.obj a.fst) b v) = ρ.mapLinear b.2 v := by
  erw [Etingof.QuiverRepresentation.sinkMap, DirectSum.toModule_lof]

set_option maxHeartbeats 800000 in
-- reason: unfolding reflectionFunctorMinus + reflectionFunctorPlus + first isomorphism theorem
/-- At vertex i, F⁻(F⁺(V)).obj i ≃ₗ[k] ρ.obj i when the sink map is surjective.

F⁺ᵢ(V).obj i = ker(φ) where φ = sinkMap. Then F⁻ᵢ produces the cokernel
of the source map at i, which is the inclusion ker(φ) ↪ ⊕V_j.
So F⁻(F⁺(V)).obj i = (⊕V_j) / ker(φ) ≅ V_i by the first isomorphism theorem. -/
private noncomputable def Etingof.equivAt_eq_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorMinus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) _) i ≃ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ inst ρ i := by
  -- Upgrade to AddCommGroup (needed for quotient module)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  -- Reduce F⁻ at vertex i (isTrue branch)
  unfold Etingof.reflectionFunctorMinus
  simp only
  match hd1 : (‹DecidableEq Q› i i) with
  | .isFalse hii => exact absurd rfl hii
  | .isTrue _ =>
    -- Goal: (⊕_{a : ArrowsOutOf Q̄ᵢ i} F⁺(V)_a.fst) ⧸ range(ψ') ≃ₗ[k] V_i
    -- Strategy: Φ = sinkMap after reindexing, then first isomorphism theorem
    rw [hd1]; dsimp only []
    classical
    -- Goal: (⊕_{a : ArrowsOutOf_{Q̄ᵢ} i} F⁺(V).obj a.fst) ⧸ range(ψ') ≃ₗ[k] ρ.obj i
    -- Strategy: construct forward and inverse maps directly
    let instR := @Etingof.reversedAtVertex Q _ inst i
    let ρ' := @Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ
    -- Forward map: quotient → V_i
    -- Component maps: F⁺(V).obj a.fst → V_i via equivAt_ne then mapLinear
    let Φ_component : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ inst ρ i :=
      fun a =>
        (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ a.fst i
          (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi a)).comp
        (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
          (@Etingof.arrowsOutReversed_ne Q _ inst i hi a)).toLinearMap
    let Φ : (DirectSum (@Etingof.ArrowsOutOf Q instR i)
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ inst ρ i :=
      DirectSum.toModule k (@Etingof.ArrowsOutOf Q instR i)
        (@Etingof.QuiverRepresentation.obj k Q _ inst ρ i) Φ_component
    -- Provide AddCommGroup instances for quotient module construction
    letI acg_comp : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        AddCommGroup (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) :=
      fun a => @Etingof.addCommGroupOfField k _ _ (ρ'.instAddCommMonoid a.fst) (ρ'.instModule a.fst)
    letI acg_ds : AddCommGroup (DirectSum (@Etingof.ArrowsOutOf Q instR i)
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) :=
      @Etingof.addCommGroupOfField k _ _ _ _
    -- Use first isomorphism theorem: need Φ surjective and range(ψ') = ker(Φ)
    -- Step 1: Show Φ is surjective (follows from surjectivity of sinkMap φ)
    -- Construct reindexing equivalence: ArrowsOutOf Q̄ᵢ i → ArrowsInto Q i
    let reindex : @Etingof.ArrowsOutOf Q instR i → @Etingof.ArrowsInto Q inst i :=
      fun a => ⟨a.fst, @Etingof.arrowsOutReversed_origArrow Q _ inst i hi a⟩
    -- Component transport: equivAt_ne gives F⁺(V)_j ≃ V_j for j ≠ i
    -- So Φ_component a = ρ.mapLinear(origArrow) ∘ equivAt_ne
    --                   = sinkMap component at (reindex a)
    have hΦsurj : Function.Surjective Φ := by
      intro y
      obtain ⟨z, hz⟩ := hsurj y
      subst hz
      -- z : DirectSum (ArrowsInto Q i) (fun a => ρ.obj a.1), sinkMap z = y
      -- Construct preimage by induction on z
      induction z using DirectSum.induction_on with
      | zero => exact ⟨0, map_zero Φ⟩
      | of b v =>
        -- b : ArrowsInto Q i, v : ρ.obj b.fst
        let a := @Etingof.arrowsInto_to_arrowsOutReversed Q _ inst i hi b
        let ha_ne := @Etingof.arrowsOutReversed_ne Q _ inst i hi a
        refine ⟨DirectSum.lof k _ _ a
          ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst ha_ne).symm v), ?_⟩
        -- Φ (lof a (equivAt_ne.symm v)) = sinkMap (of b v)
        -- LHS unfolds to Φ_component a (equivAt_ne.symm v)
        --   = ρ.mapLinear (origArrow a) (equivAt_ne (equivAt_ne.symm v))
        --   = ρ.mapLinear (origArrow a) v
        --   = ρ.mapLinear b.2 v  (by round-trip)
        -- RHS unfolds to ρ.mapLinear b.2 v (by toModule_lof)
        -- So both sides equal ρ.mapLinear b.2 v
        -- Work entirely with @ to avoid instance synthesis issues
        show Φ (DirectSum.lof k _ _ a _) = _
        rw [show Φ (DirectSum.lof k _ _ a _) = Φ_component a
          ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst ha_ne).symm v)
          from DirectSum.toModule_lof _ a _]
        change ((@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ a.fst i
            (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi a)).comp
          (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst ha_ne).toLinearMap)
          ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst ha_ne).symm v) = _
        simp only [LinearMap.comp_apply]
        erw [LinearEquiv.apply_symm_apply]
        -- Goal: ρ.mapLinear (origArrow a) v = sinkMap (of b v)
        rw [@Etingof.origArrow_arrowsInto_roundtrip Q _ inst i hi b]
        -- Goal: ρ.mapLinear b.2 v = sinkMap (of b v)
        -- Use helper lemma to avoid instance synthesis picking instR
        exact (@Etingof.sinkMap_of k _ Q _ inst ρ i b v).symm
      | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        obtain ⟨wx, hwx⟩ := hx
        obtain ⟨wy, hwy⟩ := hy
        exact ⟨wx + wy, by rw [map_add, hwx, hwy]⟩
    -- Step 2: Show range(source map) = ker(Φ)
    have hker : (∑ a : @Etingof.ArrowsOutOf Q instR i,
        (DirectSum.lof k (@Etingof.ArrowsOutOf Q instR i)
          (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) a).comp
          (@Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i a.fst a.snd)).range =
        LinearMap.ker Φ := by
      -- Exactness of ker(φ) →^{ψ'} ⊕F⁺(V)_j →^{Φ} V_i:
      -- (≤) Φ ∘ ψ' = 0 because ψ' embeds ker(φ) and Φ is essentially φ
      -- (≥) If Φ(x) = 0 then x comes from ker(φ) via ψ'
      -- Both directions require unfolding F⁺ maps through Decidable.casesOn
      -- and reindexing between ArrowsOutOf Q̄ᵢ i and ArrowsInto Q i.
      -- Needs API lemma `reflFunctorPlus_mapLinear_eq_ne` (F⁺ map from i to j≠i).
      sorry
    -- Compose quotEquivOfEq with quotKerEquivOfSurjective
    exact (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective Φ hΦsurj)

end Helpers

set_option maxHeartbeats 800000 in
-- reason: unfolding two layers of reflection functors + crossIsoToIso
/-- If φ is surjective at a sink, then applying F⁻ᵢ after F⁺ᵢ recovers V
up to isomorphism of representations.

The composition F⁻ᵢ(F⁺ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 1) -/
theorem Etingof.Proposition6_6_6_sink
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    Nonempty (Etingof.QuiverRepresentation.Iso
      (Etingof.QuiverRepresentation.transportReversedTwice
        (@Etingof.reflectionFunctorMinus k _ Q _
          (Etingof.reversedAtVertex Q i) i
          (Etingof.isSink_reversedAtVertex_isSource hi)
          (Etingof.reflectionFunctorPlus Q i hi ρ) _))
      ρ) := by
  -- Use crossIsoToIso: construct linear equivs at each vertex between
  -- F⁻(F⁺(V)) (on instDR) and ρ (on inst), using @ to avoid synthesis checks.
  let instR := @Etingof.reversedAtVertex Q _ inst i
  let instDR := @Etingof.reversedAtVertex Q _ instR i
  let ρ_plus := @Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ
  let ρ_dr := @Etingof.reflectionFunctorMinus k _ Q _ instR i
      (@Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi) ρ_plus _
  exact Etingof.QuiverRepresentation.crossIsoToIso
    (@Etingof.reversedAtVertex_twice Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      · -- v = i: first isomorphism theorem
        cases hv
        exact @Etingof.equivAt_eq_sink k _ Q _ inst i hi ρ _ _ _ hsurj
      · -- v ≠ i: both sides reduce to ρ.obj v
        exact @Etingof.equivAt_ne_sink k _ Q _ inst i hi ρ _ v hv)
    (fun {a b} e x => by
      -- Naturality: the isomorphism commutes with representation maps.
      -- Case analysis on a = i and b = i:
      -- • a ≠ i, b ≠ i: both equivs are identity, maps unchanged — trivial
      -- • a = i, b ≠ i: involves equivAt_eq_sink on the source vertex
      -- • a ≠ i, b = i: involves equivAt_eq_sink on the target vertex
      -- • a = i, b = i: self-loop at sink, vacuous
      -- BLOCKER: Same Decidable.casesOn type transport issue as equivAt_eq_sink.
      -- The representation maps of F⁻(F⁺(V)) are defined via Decidable.casesOn
      -- and don't reduce without explicit case-splitting on DecidableEq instances.
      sorry)

/-- If ψ is injective at a source, then applying F⁺ᵢ after F⁻ᵢ recovers V
up to isomorphism of representations.

The composition F⁺ᵢ(F⁻ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 2) -/
theorem Etingof.Proposition6_6_6_source
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hinj : Function.Injective (ρ.sourceMap i)) :
    Nonempty (Etingof.QuiverRepresentation.Iso
      (Etingof.QuiverRepresentation.transportReversedTwice
        (@Etingof.reflectionFunctorPlus k _ Q _
          (Etingof.reversedAtVertex Q i) i
          (Etingof.isSource_reversedAtVertex_isSink hi)
          (Etingof.reflectionFunctorMinus Q i hi ρ)))
      ρ) := by
  -- Dual of the sink case:
  -- • F⁻ᵢ(V).obj i = coker(ψ) where ψ = sourceMap
  -- • F⁺ᵢ at vertex i gives ker of sink map of F⁻(V)
  -- • When ψ is injective: ker(sink map of F⁻(V)) ≅ V_i
  -- BLOCKER: Same Decidable.casesOn type transport issue as the sink case.
  -- Proving this requires the same infrastructure: direct sum reindexing
  -- between ArrowsInto Q̄ᵢ i and ArrowsOutOf Q i, plus type transport
  -- for the component types through Decidable.casesOn.
  sorry
