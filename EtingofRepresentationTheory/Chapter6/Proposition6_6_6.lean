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

/-- The reversed arrow type at (i, i, j) equals j ⟶ i for all j.
This works by case-splitting on inst i i (which succeeds here because
inst i i appears only as the casesOn major premise in the isolated goal). -/
private theorem Etingof.ReversedAtVertexHom_at_first
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} :
    Etingof.ReversedAtVertexHom Q i i j = (j ⟶ i) := by
  unfold Etingof.ReversedAtVertexHom
  cases inst i i with
  | isFalse h => exact absurd rfl h
  | isTrue _ =>
    cases inst j i with
    | isFalse _ => rfl
    | isTrue hj => subst hj; rfl

/-- Extract the original arrow j →_Q i from a reversed arrow i →_{Q̄ᵢ} j.
Defined via `reversedArrow_eq_ne` to ensure definitional compatibility with the
API lemmas (e.g., `reflFunctorPlus_mapLinear_eq_ne`). -/
private def Etingof.arrowsOutReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ⟶ i :=
  Etingof.reversedArrow_eq_ne (Etingof.arrowsOutReversed_ne hi a) a.snd

/-- The type equality `ReversedAtVertexHom Q i i j = (j ⟶ i)` as a computable
definition (not a theorem), so that `cast`/`Eq.mpr` with it reduces properly. -/
private def Etingof.ReversedAtVertexHom_at_first_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i) :
    Etingof.ReversedAtVertexHom Q i i j = (j ⟶ i) := by
  unfold Etingof.ReversedAtVertexHom
  cases inst i i with
  | isFalse h => exact absurd rfl h
  | isTrue _ =>
    cases inst j i with
    | isTrue h => exact absurd h hj
    | isFalse _ => rfl

/-- Map arrows into i in Q to arrows out of i in Q̄ᵢ.
Since i is a sink (no arrows out), any arrow j → i in Q gives a reversed
arrow i →_{Q̄ᵢ} j. Uses `cast` with computable type equality. -/
private def Etingof.arrowsInto_to_arrowsOutReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i :=
  have hne : b.fst ≠ i := fun h =>
    (hi i).false (cast (congrArg (· ⟶ i) h) b.snd)
  ⟨b.fst, cast (Etingof.ReversedAtVertexHom_at_first_def hne).symm b.snd⟩

set_option maxHeartbeats 800000 in
-- reason: unfolding reversedArrow_eq_ne + ReversedAtVertexHom_at_first_def + proof irrelevance
/-- `reversedArrow_eq_ne` agrees with `cast` using the computable type equality. -/
private theorem Etingof.reversedArrow_eq_ne_eq_cast_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i)
    (e : Etingof.ReversedAtVertexHom Q i i j) :
    Etingof.reversedArrow_eq_ne hj e =
    cast (Etingof.ReversedAtVertexHom_at_first_def hj) e := by
  -- Both functions case-split on inst i i and inst j i.
  -- Fix the Decidable values, then revert e and rw to reduce both sides.
  have h_ii : inst i i = .isTrue rfl := by
    match inst i i with
    | .isTrue _ => rfl
    | .isFalse h => exact absurd rfl h
  have h_ji : inst j i = .isFalse hj := by
    match inst j i with
    | .isFalse _ => rfl
    | .isTrue h => exact absurd h hj
  revert e
  unfold Etingof.reversedArrow_eq_ne Etingof.ReversedAtVertexHom_at_first_def
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ii, h_ji]
  intro e; rfl

/-- Round-trip: extracting the original arrow from a converted ArrowsInto
gives back the original arrow. -/
private theorem Etingof.origArrow_arrowsInto_to_arrowsOutReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    Etingof.arrowsOutReversed_origArrow hi
      (Etingof.arrowsInto_to_arrowsOutReversed hi b) = b.2 := by
  obtain ⟨j, e⟩ := b
  have hji : j ≠ i := by intro heq; rw [heq] at e; exact (hi i).false e
  simp only [arrowsOutReversed_origArrow, arrowsInto_to_arrowsOutReversed]
  rw [reversedArrow_eq_ne_eq_cast_def]
  simp [cast_cast]

/-- The component of `arrowsInto_to_arrowsOutReversed` at j gives the original arrow j ⟶ i. -/
private theorem Etingof.arrowsInto_to_arrowsOutReversed_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    (Etingof.arrowsInto_to_arrowsOutReversed hi b).fst = b.fst := by
  simp [arrowsInto_to_arrowsOutReversed]

/-- Reverse round-trip: converting an arrow from ArrowsOutOf instR i to ArrowsInto
and back gives the original element. -/
private theorem Etingof.arrowsInto_to_arrowsOutReversed_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) :
    Etingof.arrowsInto_to_arrowsOutReversed hi
      ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩ = x := by
  obtain ⟨j, e⟩ := x
  have hji : j ≠ i := Etingof.arrowsOutReversed_ne hi ⟨j, e⟩
  refine Sigma.ext rfl ?_
  simp only [arrowsInto_to_arrowsOutReversed, arrowsOutReversed_origArrow]
  rw [reversedArrow_eq_ne_eq_cast_def]
  exact heq_of_eq (by simp [cast_cast])

/-- Equivalence between ArrowsOutOf in the reversed quiver and ArrowsInto in the original.
This is the key reindexing used in the round-trip proof. -/
private def Etingof.arrowReindexEquiv
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) :
    @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i ≃
    Etingof.ArrowsInto Q i where
  toFun x := ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩
  invFun b := Etingof.arrowsInto_to_arrowsOutReversed hi b
  left_inv x := Etingof.arrowsInto_to_arrowsOutReversed_roundtrip hi x
  right_inv b := by
    refine Sigma.ext (Etingof.arrowsInto_to_arrowsOutReversed_fst hi b) ?_
    exact heq_of_eq (Etingof.origArrow_arrowsInto_to_arrowsOutReversed hi b)

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

/-- The reindexed map Φ : ⊕_{ArrowsOutOf Q̄ᵢ i} F⁺(V).obj a.fst →ₗ ρ.obj i
is surjective when sinkMap is surjective.

Φ is essentially sinkMap after reindexing through the
ArrowsInto ↔ ArrowsOutOf correspondence and equivAt_ne.

The Φ parameter must be `DirectSum.toModule k _ _ Φ_component` where
Φ_component a = mapLinear(origArrow a) ∘ equivAt_ne. We take it as a parameter
to avoid type class synthesis issues with multiple quiver instances. -/
private theorem Etingof.sinkMap_reindex_surj
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Finite (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (hsurj : Function.Surjective (ρ.sinkMap i))
    {M : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i → Type*}
    [∀ a, AddCommMonoid (M a)] [∀ a, Module k (M a)]
    (Φ : DirectSum (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) M →ₗ[k] ρ.obj i)
    (hΦ_basic : ∀ (b : @Etingof.ArrowsInto Q inst i) (v : ρ.obj b.fst),
      ∃ z, Φ z = ρ.mapLinear b.2 v) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)
  -- Prove: sinkMap x ∈ range(Φ) for all x, hence Φ is surjective
  suffices h : ∀ x, (ρ.sinkMap i) x ∈ Set.range Φ by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    obtain ⟨z, hz⟩ := h x
    exact ⟨z, by rw [hz, hx]⟩
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp [map_zero]⟩
  | of b v =>
    obtain ⟨z, hz⟩ := hΦ_basic b v
    refine ⟨z, ?_⟩
    -- Goal: sinkMap (of b v) = Φ z = mapLinear b.2 v (by hz)
    rw [hz]
    -- Goal: sinkMap (of b v) = mapLinear b.2 v
    -- sinkMap is DirectSum.toModule (after classical), so toModule_lof applies
    delta Etingof.QuiverRepresentation.sinkMap
    erw [DirectSum.toModule_lof]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add]
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩

set_option maxHeartbeats 3200000 in
-- reason: unfolding reflectionFunctorPlus + Decidable.casesOn reduction for exactness
/-- The composition Φ ∘ source_map = 0: applying Φ after the F⁺ source map
vanishes on ker(sinkMap). This is the forward direction of exactness.

Proved by reducing everything through reflFunctorPlus_mapLinear_eq_ne and
showing the resulting sum equals sinkMap applied to a kernel element. -/
private theorem Etingof.Φ_comp_source_eq_zero
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i) :
    ∑ x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i,
      (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ x.fst i
        (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi x))
      ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ x.fst
        (@Etingof.arrowsOutReversed_ne Q _ inst i hi x))
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i x.fst x.snd w)) = 0 := by
  -- Use the API lemma to reduce each term
  simp_rw [Etingof.reflFunctorPlus_mapLinear_eq_ne hi ρ]
  -- Normalize: fold reversedArrow_eq_ne back to arrowsOutReversed_origArrow
  change ∑ x : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i,
    ρ.mapLinear (Etingof.arrowsOutReversed_origArrow hi x)
      (DirectSum.component k (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1)
        ⟨x.fst, Etingof.arrowsOutReversed_origArrow hi x⟩
        ((ρ.sinkMap i).ker.subtype (Etingof.reflFunctorPlus_equivAt_eq hi ρ w))) = 0
  -- Goal: ∑ x, mapLinear(origArrow x)(component ⟨x.fst, origArrow x⟩ y) = 0
  -- Strategy: show sum = sinkMap(y) = 0 since y ∈ ker(sinkMap).
  classical
  haveI : Fintype (Etingof.ArrowsInto Q i) :=
    Fintype.ofEquiv _ (Etingof.arrowReindexEquiv hi)
  set y := (ρ.sinkMap i).ker.subtype (Etingof.reflFunctorPlus_equivAt_eq hi ρ w) with hy_def
  -- Express the sum as ∑ x, g(equiv(x)) where g b = mapLinear b.2 (component b y)
  let g : Etingof.ArrowsInto Q i → ρ.obj i :=
    fun b => ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
      (fun a => ρ.obj a.1) b y)
  change ∑ x, g (Etingof.arrowReindexEquiv hi x) = 0
  -- Step 1: Reindex using bijection
  rw [(Etingof.arrowReindexEquiv hi).bijective.sum_comp g]
  -- Step 2: Show ∑ b, g b = sinkMap y = 0
  change ∑ b : Etingof.ArrowsInto Q i,
    ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
      (fun a => ρ.obj a.1) b y) = 0
  -- Decompose: sinkMap y = ∑ b, mapLinear b.2 (component b y)
  rw [show ∑ b : Etingof.ArrowsInto Q i,
      ρ.mapLinear b.2 (DirectSum.component k (Etingof.ArrowsInto Q i)
        (fun a => ρ.obj a.1) b y) = (ρ.sinkMap i) y from by
    symm
    delta Etingof.QuiverRepresentation.sinkMap
    change (DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i)
      (fun a => ρ.mapLinear a.2)) y = _
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, Finset.sum_const_zero]
    | of i x =>
      erw [DirectSum.toModule_lof]
      rw [Finset.sum_eq_single i]
      · erw [DirectSum.component.lof_self]
      · intro b _ hb
        erw [DirectSum.component.of]; rw [dif_neg (Ne.symm hb), map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    | add x y hx hy =>
      simp only [map_add, hx, hy, Finset.sum_add_distrib]]
  -- Step 3: sinkMap y = 0 (kernel property)
  exact (Etingof.reflFunctorPlus_equivAt_eq hi ρ w).property

set_option maxHeartbeats 400000 in
-- reason: finrank arithmetic with rank-nullity for both ψ and Φ
/-- If ψ.range ≤ ker Φ, Φ is surjective, ψ is injective, and
finrank(source ψ) + finrank(target Φ) = finrank(source Φ), then ψ.range = ker Φ.
This is the "first isomorphism theorem" applied to an exact sequence. -/
private theorem Etingof.exact_of_dim
    {k : Type*} [Field k]
    {A B C : Type*}
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup C] [Module k C] [FiniteDimensional k C]
    {ψ' : A →ₗ[k] B} {Φ' : B →ₗ[k] C}
    (hfwd : ψ'.range ≤ Φ'.ker)
    (hΦ_surj : Function.Surjective Φ')
    (hψ_inj : Function.Injective ψ')
    (hdim : Module.finrank k A + Module.finrank k C = Module.finrank k B) :
    ψ'.range = Φ'.ker := by
  apply Submodule.eq_of_le_of_finrank_eq hfwd
  -- finrank(ψ'.range) = finrank(A) since ψ' is injective
  have hr : Module.finrank k ↥ψ'.range = Module.finrank k A :=
    LinearMap.finrank_range_of_inj hψ_inj
  -- finrank(Φ'.ker) + finrank(C) = finrank(B)
  have hk : Module.finrank k ↥Φ'.ker + Module.finrank k C = Module.finrank k B := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ'
    rw [LinearMap.range_eq_top.mpr hΦ_surj, finrank_top] at h1
    omega
  -- Combine: finrank(A) = finrank(B) - finrank(C) = finrank(Φ'.ker)
  omega



set_option maxHeartbeats 800000 in
-- reason: finrank arithmetic with FiniteDimensional instances for reflectionFunctorPlus objects
/-- The reflectionFunctorPlus object at vertex i is finite-dimensional. -/
private theorem Etingof.reflFunctorPlus_finiteDim_i
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)] :
    @Module.Finite k
      (@Etingof.QuiverRepresentation.obj k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) i)
      (inferInstanceAs (Semiring k))
      (@Etingof.QuiverRepresentation.instAddCommMonoid k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) i)
      (@Etingof.QuiverRepresentation.instModule k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) i) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  haveI : Fintype (@Etingof.ArrowsInto Q inst i) :=
    Fintype.ofEquiv _ (@Etingof.arrowReindexEquiv Q _ inst i hi)
  exact Module.Finite.equiv
    (@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ inst i hi ρ).symm

set_option maxHeartbeats 800000 in
-- reason: finrank computation for reflectionFunctorPlus at non-sink vertices
/-- Each F⁺(V).obj a.fst is finite-dimensional for arrows out of i in Q̄ᵢ. -/
private theorem Etingof.reflFunctorPlus_finiteDim_ne
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (@Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i)]
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) :
    @Module.Finite k
      (@Etingof.QuiverRepresentation.obj k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) a.fst)
      (inferInstanceAs (Semiring k))
      (@Etingof.QuiverRepresentation.instAddCommMonoid k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) a.fst)
      (@Etingof.QuiverRepresentation.instModule k Q _
        (@Etingof.reversedAtVertex Q _ inst i)
        (@Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ) a.fst) :=
  Module.Finite.equiv
    (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
      (@Etingof.arrowsOutReversed_ne Q _ inst i hi a)).symm

set_option maxHeartbeats 800000 in
-- reason: unfolding reflectionFunctorMinus + first isomorphism theorem + DirectSum reindexing
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
    have hΦsurj : Function.Surjective Φ :=
      @Etingof.sinkMap_reindex_surj k _ Q _ inst i hi ρ _ hsurj
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)
        (fun a => ρ'.instAddCommMonoid a.fst) (fun a => ρ'.instModule a.fst) Φ
        (fun b v => by
          -- Construct preimage: lof a (equivAt_ne.symm v)
          -- where a = arrowsInto_to_arrowsOutReversed b
          let a := @Etingof.arrowsInto_to_arrowsOutReversed Q _ inst i hi b
          let hne := @Etingof.arrowsOutReversed_ne Q _ inst i hi a
          let v' := (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst hne).symm v
          refine ⟨DirectSum.lof k _ _ a v', ?_⟩
          simp only [Φ, Φ_component, DirectSum.toModule_lof, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap, v']
          -- Goal: mapLinear (origArrow a) (equivAt_ne ⋯ (equivAt_ne hne).symm v) = mapLinear b.2 v
          -- Two equivAt_ne have different proof args; apply_symm_apply still works
          have heq_proof : @Etingof.arrowsOutReversed_ne Q _ inst i hi a =
              @Etingof.arrowsOutReversed_ne Q _ inst i hi
                (@Etingof.arrowsInto_to_arrowsOutReversed Q _ inst i hi b) := rfl
          conv_lhs =>
            rw [show ∀ h, (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst h)
                ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst hne).symm v) = v
              from fun h => by exact LinearEquiv.apply_symm_apply _ v]
          exact congrArg (fun e => @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ _ i e v)
            (@Etingof.origArrow_arrowsInto_to_arrowsOutReversed Q _ inst i hi b))
    -- Step 2: Show range(source map) = ker(Φ)
    -- Source map ψ : F⁺(V)_i → ⊕ F⁺(V)_j
    let ψ := ∑ a : @Etingof.ArrowsOutOf Q instR i,
        (DirectSum.lof k (@Etingof.ArrowsOutOf Q instR i)
          (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) a).comp
          (@Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i a.fst a.snd)
    have hker : ψ.range = LinearMap.ker Φ := by
      apply le_antisymm
      · -- Forward: range(ψ) ≤ ker(Φ), i.e., Φ ∘ ψ = 0
        rw [LinearMap.range_le_ker_iff]
        ext w
        simp only [LinearMap.comp_apply, LinearMap.zero_apply]
        -- Φ(ψ(w)) = ∑_a Φ_comp(a)(ρ'.mapLinear(a.snd, w)) = 0
        simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply]
        -- Goal: Φ (∑ a, lof a (ρ'.mapLinear a.snd w)) = 0
        simp only [Φ, map_sum, DirectSum.toModule_lof]
        -- Goal: ∑ x, Φ_component x (ρ'.mapLinear x.snd w) = 0
        exact @Etingof.Φ_comp_source_eq_zero k _ Q _ inst i hi ρ _ w
      · -- Reverse: ker(Φ) ≤ range(ψ)
        have hfwd : ψ.range ≤ LinearMap.ker Φ := by
          rw [LinearMap.range_le_ker_iff]; ext w
          simp only [LinearMap.comp_apply, LinearMap.zero_apply]
          simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply]
          simp only [Φ, map_sum, DirectSum.toModule_lof]
          exact @Etingof.Φ_comp_source_eq_zero k _ Q _ inst i hi ρ _ w
        -- FiniteDimensional instances from external helpers (avoid instR pollution)
        letI acg_rho'_i : AddCommGroup
            (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i) :=
          @Etingof.addCommGroupOfField k _ _
            (ρ'.instAddCommMonoid i) (ρ'.instModule i)
        haveI fd_i :
            @Module.Finite k
              (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i)
              (inferInstanceAs (Semiring k))
              (@Etingof.QuiverRepresentation.instAddCommMonoid k Q _
                instR ρ' i)
              (@Etingof.QuiverRepresentation.instModule k Q _
                instR ρ' i) :=
          @Etingof.reflFunctorPlus_finiteDim_i k _ Q _ inst i hi ρ _ _ _
        haveI fd_ne : ∀ a : @Etingof.ArrowsOutOf Q instR i,
            @Module.Finite k
              (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)
              (inferInstanceAs (Semiring k))
              (@Etingof.QuiverRepresentation.instAddCommMonoid k Q _
                instR ρ' a.fst)
              (@Etingof.QuiverRepresentation.instModule k Q _
                instR ρ' a.fst) :=
          fun a => @Etingof.reflFunctorPlus_finiteDim_ne k _ Q _ inst i hi ρ _ _ _ a
        haveI : FiniteDimensional k (DirectSum (@Etingof.ArrowsOutOf Q instR i)
            (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) :=
          @Module.Finite.instDirectSum k (@Etingof.ArrowsOutOf Q instR i) _
            inferInstance
            (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)
            (fun a => (acg_comp a).toAddCommMonoid)
            (fun a => ρ'.instModule a.fst)
            (fun a => fd_ne a)
        -- Now prove ker Φ ≤ ψ.range via dimension count
        -- BLOCKER: instR type class pollution makes finrank/injectivity proofs
        -- extremely difficult. Each use of Module.finrank or Function.Injective
        -- triggers synthesis conflicts between inst and instR.
        -- Mathematical argument for hψ_inj: ψ factors as
        --   equivAt_eq → subtype → reindex ∘ ⊕equivAt_ne⁻¹
        -- which is injective (equiv ∘ injection ∘ equiv).
        -- Mathematical argument for hdim:
        --   finrank(ρ'.obj i) = finrank(ker sinkMap) [equivAt_eq]
        --   finrank(ker sinkMap) + finrank(V_i) = finrank(⊕V_j) [rank-nullity]
        --   finrank(⊕V_j) = finrank(⊕ρ'.obj a.fst) [equivAt_ne + reindex]
        have hψ_inj : Function.Injective ψ := by
          intro w₁ w₂ heq
          rw [← sub_eq_zero]; set w := w₁ - w₂
          have hψ_zero : ψ w = 0 := by rw [map_sub, sub_eq_zero.mpr heq]
          -- Each component: (ψ w) a = mapLinear a.snd w = 0
          have hcomp : ∀ a : @Etingof.ArrowsOutOf Q instR i,
              @Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i a.fst a.snd w = 0 := by
            intro a
            -- (ψ w) a = 0
            have h₀ : (ψ w) a = 0 := by
              have := congr_arg (· a) hψ_zero
              simp only [DirectSum.zero_apply] at this
              exact this
            -- (ψ w) a = mapLinear a.snd w (by expanding ψ as sum of lof)
            suffices hψa : (ψ w) a =
                @Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i a.fst a.snd w by
              rw [← hψa]; exact h₀
            -- ψ is let-bound; ψ w evaluates to ∑ b, lof(b)(mapLinear b.snd w)
            -- Applying at index a extracts mapLinear a.snd w
            have hψ_rfl : ψ = ∑ b : @Etingof.ArrowsOutOf Q instR i,
                (DirectSum.lof k (@Etingof.ArrowsOutOf Q instR i)
                  (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) b).comp
                  (@Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ' i b.fst b.snd) := rfl
            rw [hψ_rfl, LinearMap.sum_apply]
            simp only [LinearMap.comp_apply]
            rw [DFinsupp.finset_sum_apply,
              Finset.sum_eq_single a
                (fun b _ hb => DFinsupp.single_eq_of_ne (Ne.symm hb))
                (fun h => absurd (Finset.mem_univ a) h)]
            exact DFinsupp.single_eq_same
          -- Via reflFunctorPlus_mapLinear_eq_ne, all components of subtype(equivAt_eq w) are 0
          haveI : Fintype (@Etingof.ArrowsInto Q inst i) :=
            Fintype.ofEquiv _ (@Etingof.arrowReindexEquiv Q _ inst i hi)
          -- Show the underlying ⊕V_j element of equivAt_eq(w) is 0
          set ew := (@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ inst i hi ρ) w
          have hval_zero : (ew : DirectSum (@Etingof.ArrowsInto Q inst i)
              (fun a => @Etingof.QuiverRepresentation.obj k Q _ inst ρ a.fst)) = 0 := by
            apply DFinsupp.ext; intro b
            let a := (@Etingof.arrowReindexEquiv Q _ inst i hi).symm b
            have hne := @Etingof.arrowsOutReversed_ne Q _ inst i hi a
            have hapi := @Etingof.reflFunctorPlus_mapLinear_eq_ne k _ Q _ inst i hi ρ
              a.fst hne a.snd w
            rw [hcomp a, map_zero] at hapi
            have hb_eq : (⟨a.fst, @Etingof.reversedArrow_eq_ne Q _ inst i a.fst hne a.snd⟩ :
                @Etingof.ArrowsInto Q inst i) = b :=
              Equiv.apply_symm_apply (@Etingof.arrowReindexEquiv Q _ inst i hi) b
            -- hapi : 0 = component(reindex(a))(subtype(ew))
            -- Goal: ↑ew b = 0
            -- Use hb_eq to transport: reindex(a) = b
            simp only [DirectSum.zero_apply]
            -- hapi says component(reindex a)(subtype(ew)) = 0
            -- but reindex a = b (by hb_eq), so component(b)(...) = 0
            -- The subtype coercion goes through inst, so use @
            -- hapi says: component(reindex a)(subtype(ew)) = 0
            -- Goal: ↑ew b = 0
            -- reindex a = b (by hb_eq)
            -- ↑ew b is DFinsupp eval at b, which equals component b (↑ew)
            -- Use hapi with index transport
            -- hapi : 0 = component(⟨a.fst,...⟩)(subtype(equivAt_eq w))
            -- Goal: ↑ew b = 0, where ↑ew b = component b (↑ew)
            -- Use hb_eq to substitute b with ⟨a.fst,...⟩ via ▸
            exact hb_eq ▸ hapi.symm
          have heq_zero : ew = 0 := Subtype.val_injective hval_zero
          exact (@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ inst i hi ρ).injective
            (by change ew = _; rw [heq_zero, map_zero])
        -- Prove hdim using abstract theorem to avoid instR/inst type class pollution
        -- We need: finrank(ρ'.obj i) + finrank(ρ.obj i) = finrank(⊕ ρ'.obj a.fst)
        -- Strategy: compute both sides as ℕ values, then use linarith
        haveI : Fintype (@Etingof.ArrowsInto Q inst i) :=
          Fintype.ofEquiv _ (@Etingof.arrowReindexEquiv Q _ inst i hi)
        -- Module.Free instances for ρ' objects
        haveI : ∀ a : @Etingof.ArrowsOutOf Q instR i,
            Module.Free k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) :=
          fun a => Module.Free.of_equiv
            (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
              (@Etingof.arrowsOutReversed_ne Q _ inst i hi a)).symm
        haveI : Module.Free k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i) :=
          Module.Free.of_equiv
            (@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ inst i hi ρ).symm
        have hdim : Module.finrank k
              (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i) +
            Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ i) =
            Module.finrank k (DirectSum (@Etingof.ArrowsOutOf Q instR i)
              (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) := by
          -- Assign finranks to ℕ variables to isolate from instR synthesis
          set d1 := Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i)
          set d2 := Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ i)
          set d3 := Module.finrank k (DirectSum (@Etingof.ArrowsOutOf Q instR i)
            (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst))
          -- d3 = ∑ finrank(ρ'.obj a.fst) via finrank_directSum
          have heq3a : d3 = ∑ a : @Etingof.ArrowsOutOf Q instR i,
              Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) :=
            Module.finrank_directSum (R := k) _
          -- each component: finrank(ρ'.obj a.fst) = finrank(ρ.obj a.fst)
          have heq3b : ∀ a : @Etingof.ArrowsOutOf Q instR i,
              Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) =
              Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ a.fst) :=
            fun a => LinearEquiv.finrank_eq
              (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
                (@Etingof.arrowsOutReversed_ne Q _ inst i hi a))
          -- d3 = ∑ finrank(ρ.obj a.fst) via equivAt_ne
          have heq3 : d3 = ∑ a : @Etingof.ArrowsOutOf Q instR i,
              Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ a.fst) := by
            rw [heq3a]; exact Finset.sum_congr rfl (fun a _ => heq3b a)
          -- Re-register inst as the active Quiver Q instance to avoid instR pollution
          letI : Quiver Q := inst
          -- d1 = finrank(ker sinkMap) via equivAt_eq
          have heq1 : d1 = Module.finrank k ↥(LinearMap.ker (ρ.sinkMap i)) :=
            LinearEquiv.finrank_eq (@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ inst i hi ρ)
          -- Now rank-nullity and surjectivity can be stated cleanly
          have h_rn := (ρ.sinkMap i).finrank_range_add_finrank_ker
          have h_surj : Module.finrank k ↥(ρ.sinkMap i).range = d2 := by
            rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
          have h_ds := Module.finrank_directSum (R := k)
            (fun a : @Etingof.ArrowsInto Q inst i => ρ.obj a.fst)
          -- reindex sum: ∑ over ArrowsOutOf instR i = ∑ over ArrowsInto inst i
          -- Since (arrowReindexEquiv hi a).fst = a.fst definitionally
          have h_reindex : ∑ a : @Etingof.ArrowsOutOf Q instR i,
              Module.finrank k (ρ.obj a.fst) =
              ∑ b : @Etingof.ArrowsInto Q inst i, Module.finrank k (ρ.obj b.fst) :=
            (@Etingof.arrowReindexEquiv Q _ inst i hi).bijective.sum_comp
              (fun b => Module.finrank k (ρ.obj b.fst))
          linarith [heq1, heq3, h_rn, h_surj, h_ds, h_reindex]
        exact (Etingof.exact_of_dim hfwd hΦsurj hψ_inj hdim).ge
    -- Compose quotEquivOfEq with quotKerEquivOfSurjective
    exact (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective Φ hΦsurj)

/-- `reversedArrow_ne_ne ha hb` is a cast through `ReversedAtVertexHom_ne_ne`. -/
private theorem Etingof.reversedArrow_ne_ne_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) :
    Etingof.reversedArrow_ne_ne ha hb e =
    cast (Etingof.ReversedAtVertexHom_ne_ne ha hb) e := by
  have h_ai : inst_dec a i = .isFalse ha := by
    match inst_dec a i with | .isTrue h => exact absurd h ha | .isFalse _ => rfl
  have h_bi : inst_dec b i = .isFalse hb := by
    match inst_dec b i with | .isTrue h => exact absurd h hb | .isFalse _ => rfl
  revert e
  unfold Etingof.reversedArrow_ne_ne Etingof.ReversedAtVertexHom_ne_ne
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ai, h_bi]
  intro e; rfl

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through Decidable.casesOn
private theorem Etingof.reversedArrow_ne_ne_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q inst a b) :
    @Etingof.reversedArrow_ne_ne Q inst_dec inst i a b ha hb
      (@Etingof.reversedArrow_ne_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)) = e := by
  -- Convert each reversedArrow_ne_ne to cast via is_cast, then compose via HEq
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) a b),
      HEq (@Etingof.reversedArrow_ne_ne Q inst_dec inst i a b ha hb y) y := by
    intro y; rw [Etingof.reversedArrow_ne_ne_is_cast]; exact cast_heq _ _
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) a b),
      HEq (@Etingof.reversedArrow_ne_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb z) z := by
    intro z
    rw [@Etingof.reversedArrow_ne_ne_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i a b ha hb z]
    exact cast_heq _ _
  -- Use eqRec_heq_self with explicit motive using field projection (avoids instance synthesis)
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a b) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact eq_of_heq ((h1 _).trans ((h2 _).trans h3))

end Helpers

set_option maxHeartbeats 3200000 in
-- reason: crossIsoToIso + equivAt case analysis + Decidable.casesOn reduction
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
      by_cases ha : a = i
      · -- a = i: vacuous — i is a sink, so there are no arrows out of i
        subst ha; exact ((hi b).false e).elim
      · by_cases hb : b = i
        · -- a ≠ i, b = i: arrow a → i, involves equivAt_eq_sink at target
          sorry
        · -- a ≠ i, b ≠ i: both equivs reduce to equivAt_ne_sink (≃ id)
          simp only [dif_neg ha, dif_neg hb]
          have h_da : ‹DecidableEq Q› a i = .isFalse ha := by
            cases ‹DecidableEq Q› a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
          have h_db : ‹DecidableEq Q› b i = .isFalse hb := by
            cases ‹DecidableEq Q› b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
          -- BLOCKER: Decidable.casesOn opacity prevents reducing through
          -- F⁻(F⁺(V)).mapLinear for a≠i, b≠i. The equivAt_ne_sink equivs
          -- reduce to identity, but the map also needs reduction through
          -- reflFunctorMinus_mapLinear_ne_ne + reflFunctorPlus_mapLinear_ne_ne
          -- + reversedArrow_ne_ne_twice. The Decidable.rec terms in the
          -- goal types resist rw/simp/dsimp, causing "motive is not type correct".
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
