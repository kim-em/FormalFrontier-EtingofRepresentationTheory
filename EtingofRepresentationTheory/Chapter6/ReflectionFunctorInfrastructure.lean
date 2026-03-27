import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Reflection Functor Infrastructure

Shared infrastructure for the proof of Proposition 6.6.6 (inverse relationship of
reflection functors). This file provides:

- `QuiverRepresentation.Iso`: isomorphism between quiver representations
- `reversedAtVertex_twice`: double reversal recovers the original quiver
- `transportReversedTwice`, `crossIsoToIso`: transport through double reversal
- Arrow reindexing equivalences between reversed and original quivers
- `reversedArrow_*_is_cast` and `*_twice`: double-reversal cast lemmas
- `exact_of_dim`: first isomorphism theorem for exact sequences

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

theorem Etingof.reversedAtVertex_twice
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

/-- A cross-quiver isomorphism: linear equivalences at each vertex between
representations on potentially different (but equal) quiver instances.
Uses `@` notation throughout to avoid synthesis check issues.
Converts to a standard Iso via `subst`. -/
noncomputable def Etingof.QuiverRepresentation.crossIsoToIso
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

/-- For an arrow `i →_{Q̄ᵢ} j` in the reversed quiver (with i a sink), the target vertex
j ≠ i. This is because i is a source in Q̄ᵢ. -/
theorem Etingof.arrowsOutReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i i j at e
  by_cases hj : j = i
  · rw [Etingof.ReversedAtVertexHom_eq_eq rfl hj] at e
    rw [hj] at e; exact ((hi i).false e).elim
  · exact hj

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

/-- Extract the original arrow j →_Q i from a reversed arrow i →_{Q̄ᵢ} j.
Defined via `reversedArrow_eq_ne` to ensure definitional compatibility with the
API lemmas (e.g., `reflFunctorPlus_mapLinear_eq_ne`). -/
def Etingof.arrowsOutReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : @Etingof.ArrowsOutOf Q (Etingof.reversedAtVertex Q i) i) : a.fst ⟶ i :=
  Etingof.reversedArrow_eq_ne (Etingof.arrowsOutReversed_ne hi a) a.snd

/-- Map arrows into i in Q to arrows out of i in Q̄ᵢ.
Since i is a sink (no arrows out), any arrow j → i in Q gives a reversed
arrow i →_{Q̄ᵢ} j. Uses `cast` with computable type equality. -/
def Etingof.arrowsInto_to_arrowsOutReversed
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
theorem Etingof.origArrow_arrowsInto_to_arrowsOutReversed
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
theorem Etingof.arrowsInto_to_arrowsOutReversed_fst
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (b : Etingof.ArrowsInto Q i) :
    (Etingof.arrowsInto_to_arrowsOutReversed hi b).fst = b.fst := by
  simp [arrowsInto_to_arrowsOutReversed]

/-- Reverse round-trip: converting an arrow from ArrowsOutOf instR i to ArrowsInto
and back gives the original element. -/
theorem Etingof.arrowsInto_to_arrowsOutReversed_roundtrip
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
def Etingof.arrowReindexEquiv
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

/-- The reindexed map Φ : ⊕_{ArrowsOutOf Q̄ᵢ i} F⁺(V).obj a.fst →ₗ ρ.obj i
is surjective when sinkMap is surjective.

Φ is essentially sinkMap after reindexing through the
ArrowsInto ↔ ArrowsOutOf correspondence and equivAt_ne.

The Φ parameter must be `DirectSum.toModule k _ _ Φ_component` where
Φ_component a = mapLinear(origArrow a) ∘ equivAt_ne. We take it as a parameter
to avoid type class synthesis issues with multiple quiver instances. -/
theorem Etingof.sinkMap_reindex_surj
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
theorem Etingof.Φ_comp_source_eq_zero
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
theorem Etingof.exact_of_dim
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

end Helpers

section ReversedArrowCasts

/-- `reversedArrow_ne_ne ha hb` is a cast through `ReversedAtVertexHom_ne_ne`. -/
theorem Etingof.reversedArrow_ne_ne_is_cast
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
theorem Etingof.reversedArrow_ne_ne_twice
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


/-- `reversedArrow_eq_ne hb` is a cast through `ReversedAtVertexHom_eq_ne`. -/
theorem Etingof.reversedArrow_eq_ne_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i b) :
    Etingof.reversedArrow_eq_ne hb e =
    cast (Etingof.ReversedAtVertexHom_eq_ne (i := i) rfl hb) e := by
  have h_ii : inst_dec i i = .isTrue rfl := by
    match inst_dec i i with | .isTrue _ => rfl | .isFalse h => exact absurd rfl h
  have h_bi : inst_dec b i = .isFalse hb := by
    match inst_dec b i with | .isTrue h => exact absurd h hb | .isFalse _ => rfl
  revert e
  unfold Etingof.reversedArrow_eq_ne Etingof.ReversedAtVertexHom_eq_ne
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ii, h_bi]
  intro e; rfl

/-- `reversedArrow_ne_eq ha` is a cast through `ReversedAtVertexHom_ne_eq`. -/
theorem Etingof.reversedArrow_ne_eq_is_cast
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) :
    Etingof.reversedArrow_ne_eq ha e =
    cast (Etingof.ReversedAtVertexHom_ne_eq (i := i) ha rfl) e := by
  have h_ai : inst_dec a i = .isFalse ha := by
    match inst_dec a i with | .isTrue h => exact absurd h ha | .isFalse _ => rfl
  have h_ii : inst_dec i i = .isTrue rfl := by
    match inst_dec i i with | .isTrue _ => rfl | .isFalse h => exact absurd rfl h
  revert e
  unfold Etingof.reversedArrow_ne_eq Etingof.ReversedAtVertexHom_ne_eq
    Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_ai, h_ii]
  intro e; rfl

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through eq_ne + ne_eq path
/-- Double reversal for the (a ≠ i, b = i) case: reversing at i twice recovers the original arrow.
This mirrors `reversedArrow_ne_ne_twice` but goes through `reversedArrow_ne_eq` then
`reversedArrow_eq_ne` instead of `reversedArrow_ne_ne` twice. -/
theorem Etingof.reversedArrow_ne_eq_eq_ne_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q inst a i) :
    Etingof.arrowsOutReversed_origArrow hi
      ⟨a, @Etingof.reversedArrow_ne_eq Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a ha
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)⟩ = e := by
  simp only [arrowsOutReversed_origArrow]
  apply eq_of_heq
  -- Step 1: reversedArrow_eq_ne is HEq to identity
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) i a),
      HEq (@Etingof.reversedArrow_eq_ne Q inst_dec inst i a
        (Etingof.arrowsOutReversed_ne hi ⟨a, y⟩) y) y := by
    intro y
    rw [Etingof.reversedArrow_eq_ne_is_cast]
    exact cast_heq _ _
  -- Step 2: reversedArrow_ne_eq on instR is HEq to identity
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) a i),
      HEq (@Etingof.reversedArrow_ne_eq Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i a ha z) z := by
    intro z
    rw [@Etingof.reversedArrow_ne_eq_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i a ha z]
    exact cast_heq _ _
  -- Step 3: transport is HEq to identity
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom a i) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

set_option maxHeartbeats 1600000 in
-- reason: double-reversal cast simplification through eq_ne + ne_eq path (source direction)
/-- Double reversal for the (a = i, b ≠ i) case: reversing at i twice recovers the original arrow.
This mirrors `reversedArrow_ne_eq_eq_ne_twice` but goes through `reversedArrow_eq_ne` then
`reversedArrow_ne_eq` (source direction: arrow from i outward). -/
theorem Etingof.reversedArrow_eq_ne_ne_eq_twice
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (_hi : Etingof.IsSource Q i)
    {b : Q} (hb : b ≠ i)
    (e : @Quiver.Hom Q inst i b) :
    @Etingof.reversedArrow_ne_eq Q inst_dec inst i b hb
      (@Etingof.reversedArrow_eq_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i b hb
        ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e)) = e := by
  apply eq_of_heq
  -- Step 1: reversedArrow_ne_eq is HEq to identity
  have h1 : ∀ (y : @Quiver.Hom Q (@Etingof.reversedAtVertex Q _ inst i) b i),
      HEq (@Etingof.reversedArrow_ne_eq Q inst_dec inst i b hb y) y := by
    intro y
    rw [Etingof.reversedArrow_ne_eq_is_cast]
    exact cast_heq _ _
  -- Step 2: reversedArrow_eq_ne on instR is HEq to identity
  have h2 : ∀ (z : @Quiver.Hom Q
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i) i b),
      HEq (@Etingof.reversedArrow_eq_ne Q inst_dec
        (@Etingof.reversedAtVertex Q _ inst i) i b hb z) z := by
    intro z
    rw [@Etingof.reversedArrow_eq_ne_is_cast Q inst_dec
      (@Etingof.reversedAtVertex Q _ inst i) i b hb z]
    exact cast_heq _ _
  -- Step 3: transport is HEq to identity
  have h3 : HEq ((@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm ▸ e) e :=
    eqRec_heq_self (motive := fun q _ => q.Hom i b) e
      (@Etingof.reversedAtVertex_twice Q inst_dec inst i).symm
  exact (h1 _).trans ((h2 _).trans h3)

end ReversedArrowCasts
