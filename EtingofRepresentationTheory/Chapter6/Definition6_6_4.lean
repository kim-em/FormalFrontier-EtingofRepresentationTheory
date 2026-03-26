import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Defs

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

The cokernel construction (quotient module) requires `AddCommGroup` and `Ring`
structure. The definition requires `[CommRing k]` and constructs compatible
`AddCommGroup` instances internally using scalar multiplication by `-1`.
-/

/-- The type indexing the direct sum for F⁻ᵢ: pairs (j, h) where h : i ⟶ j is an arrow
out of the source vertex i. -/
def Etingof.ArrowsOutOf (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)

/-- Over a commutative ring, any `AddCommMonoid` module is actually an `AddCommGroup`,
with negation given by scalar multiplication by `-1`. This bridges `QuiverRepresentation`
(which uses `AddCommMonoid`) and APIs like `Submodule.exists_isCompl` (which require
`AddCommGroup`). The resulting `AddCommGroup` extends the existing `AddCommMonoid` —
no diamond. -/
noncomputable def Etingof.addCommGroupOfRing {k : Type*} [CommRing k] {M : Type*}
    [inst : AddCommMonoid M] [Module k M] : AddCommGroup M :=
  { inst with
    neg := fun x => (-1 : k) • x
    zsmul := fun n x => (n : k) • x
    neg_add_cancel := fun a => by
      change (-1 : k) • a + a = 0
      nth_rw 2 [show a = (1 : k) • a from (one_smul k a).symm]
      rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul_zero' := fun a => by simp [zero_smul]
    zsmul_succ' := fun n a => by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    zsmul_neg' := fun n a => by
      simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_neg, smul_smul, neg_one_mul] }

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
    {k : Type*} [CommRing k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [Fintype (Etingof.ArrowsOutOf V i)] :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) :=
  -- Upgrade vertex modules to AddCommGroup (extends existing AddCommMonoid, no diamond)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  -- The direct sum also gets AddCommGroup (extends its existing AddCommMonoid)
  letI instACG_DS : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- Classical instances needed for the ∑ (Finset.sum requires DecidableEq on index)
  letI : DecidableEq (Etingof.ArrowsOutOf V i) := Classical.decEq _
  -- ψ : V_i → ⊕_{i→j} V_j, the canonical source map
  let ψ : ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) :=
    ∑ a : Etingof.ArrowsOutOf V i,
      (DirectSum.lof k (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) a).comp (ρ.mapLinear a.2)
  -- Cokernel type: (⊕_{i→j} V_j) / Im(ψ)
  let CokerType := (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) ⧸ LinearMap.range ψ
  -- Use Decidable.casesOn with the [DecidableEq V] instance to construct
  -- obj, AddCommMonoid, and Module coherently. All three fields share the same
  -- Decidable instance, so the type-level case-split computes correctly.
  let dp : ∀ v, Decidable (v = i) := fun v => inst v i
  let objAt : ∀ v, Decidable (v = i) → Type _ :=
    fun v d => @Decidable.casesOn _ (fun _ => Type _) d
      (fun _ => ρ.obj v) (fun _ => CokerType)
  let acmAt : ∀ v d, AddCommMonoid (objAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => AddCommMonoid (objAt v d)) d
      (fun _ => ρ.instAddCommMonoid v)
      (fun _ => Submodule.Quotient.addCommGroup (p := LinearMap.range ψ) |>.toAddCommMonoid)
  let modAt : ∀ v d, @Module k (objAt v d) _ (acmAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => @Module k (objAt v d) _ (acmAt v d)) d
      (fun _ => ρ.instModule v)
      (fun _ => Submodule.Quotient.module (LinearMap.range ψ))
  -- Construct the mapLinear field using explicit @Decidable.casesOn (no `classical`)
  -- to match the pattern of reflectionFunctorPlus and enable API lemma proofs via rfl.
  @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => objAt v (dp v))
    (fun v => acmAt v (dp v))
    (fun v => modAt v (dp v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      -- Goal: objAt a (inst a i) →ₗ[k] objAt b (inst b i)
      -- Use the same explicit @Decidable.casesOn pattern as reflectionFunctorPlus.
      change objAt a (inst a i) →ₗ[k] objAt b (inst b i)
      change @Etingof.ReversedAtVertexHom V inst _ i a b at e
      unfold Etingof.ReversedAtVertexHom at e
      revert e
      -- arrowAt computes the arrow type for given Decidable values
      let arrowAt (da : Decidable (a = i)) (db : Decidable (b = i)) : Type _ :=
        @Decidable.casesOn _ (fun _ => Type _) da
          (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
            (fun _ => (a ⟶ b)) (fun _ => (i ⟶ a)))
          (fun _ => @Decidable.casesOn _ (fun _ => Type _) db
            (fun _ => (b ⟶ i)) (fun _ => (a ⟶ b)))
      exact @Decidable.casesOn (a = i)
        (fun da => arrowAt da (inst b i) → objAt a da →ₗ[k] objAt b (inst b i))
        (inst a i)
        (fun ha_ne => @Decidable.casesOn (b = i)
          (fun db => arrowAt (.isFalse ha_ne) db → ρ.obj a →ₗ[k] objAt b db)
          (inst b i)
          (fun _hb_ne => fun e => ρ.mapLinear e)
          (fun _hb_eq => fun e =>
            (Submodule.mkQ (LinearMap.range ψ)).comp
              (DirectSum.lof k (Etingof.ArrowsOutOf V i)
                (fun a => ρ.obj a.1) ⟨a, e⟩)))
        (fun ha_eq => @Decidable.casesOn (b = i)
          (fun db => arrowAt (.isTrue ha_eq) db → objAt a (.isTrue ha_eq) →ₗ[k] objAt b db)
          (inst b i)
          (fun _hb_ne => fun e =>
            ((hi b).false e).elim)
          (fun hb_eq => fun e =>
            -- a = i, b = i: e : a ⟶ b, cast to a ⟶ i since b = i
            ((hi a).false (show a ⟶ i by exact hb_eq ▸ e)).elim)))

section ReflectionFunctorMinusAPI

/-! ## API for `reflectionFunctorMinus`

Dual of the `reflectionFunctorPlus` API. Provides `LinearEquiv`s that reduce
the `Decidable.casesOn` in the definition of `reflectionFunctorMinus`. -/

/-- At a vertex v ≠ i, the type `F⁻ᵢ(ρ).obj v` is propositionally equal to `ρ.obj v`. -/
theorem Etingof.reflFunctorMinus_obj_ne
    {k : Type*} [CommRing k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v = ρ.obj v := by
  unfold Etingof.reflectionFunctorMinus
  simp only []
  match hd : (‹DecidableEq Q› v i) with
  | .isTrue hvi => exact absurd hvi hv
  | .isFalse _ => rw [hd]

/-- `LinearEquiv` at vertex v ≠ i: `F⁻ᵢ(ρ).obj v ≃ₗ[k] ρ.obj v`.
This reduces the `Decidable.casesOn` in the `reflectionFunctorMinus` definition. -/
noncomputable def Etingof.reflFunctorMinus_equivAt_ne
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v ≃ₗ[k] ρ.obj v := by
  unfold Etingof.reflectionFunctorMinus
  simp only []
  exact match inst v i with
  | .isTrue hvi => absurd hvi hv
  | .isFalse _ => LinearEquiv.refl k (ρ.obj v)

/-- For an arrow `j →_{Q̄ᵢ} i` in the reversed quiver (with i a source), the source vertex
j ≠ i. This is because i is a sink in Q̄ᵢ. -/
theorem Etingof.arrowsIntoReversed_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a
  intro heq; dsimp only at heq
  change Etingof.ReversedAtVertexHom Q i j i at e
  rw [Etingof.ReversedAtVertexHom_eq_eq heq rfl] at e
  exact (hi j).false (show j ⟶ i from e)

/-- Extract the original arrow i →_Q j from a reversed arrow j →_{Q̄ᵢ} i.
When i is a source, `ReversedAtVertexHom Q i j i` with j ≠ i is just `i ⟶ j` in Q. -/
def Etingof.arrowsIntoReversed_origArrow
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i) : i ⟶ a.fst := by
  obtain ⟨j, e⟩ := a
  change Etingof.ReversedAtVertexHom Q i j i at e
  have hne := Etingof.arrowsIntoReversed_ne hi ⟨j, e⟩
  rw [Etingof.ReversedAtVertexHom_ne_eq hne rfl] at e; exact e

set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + match reduction
/-- At non-source vertices (a ≠ i, b ≠ i), the F⁻ᵢ map equals the original ρ map,
after transport through the equivAt_ne equivalences.

Dual of `reflFunctorPlus_mapLinear_ne_ne`. -/
theorem Etingof.reflFunctorMinus_mapLinear_ne_ne
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    {a b : Q} (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a) :
    (Etingof.reflFunctorMinus_equivAt_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorMinus Q i hi ρ) a b e w) =
    ρ.mapLinear (Etingof.reversedArrow_ne_ne ha hb e)
      ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_db : inst b i = .isFalse hb := by
    cases inst b i with | isTrue h => exact absurd h hb | isFalse _ => rfl
  revert e w
  unfold Etingof.reflFunctorMinus_equivAt_ne Etingof.reversedArrow_ne_ne
    Etingof.reflectionFunctorMinus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_da, h_db]
  intro e w
  rfl

/-- Convert a reversed-quiver arrow from a ≠ i to i back to the original i ⟶ a in Q.
For a ≠ i, `ReversedAtVertexHom Q i a i = i ⟶ a`. -/
def Etingof.reversedArrow_ne_eq
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a : Q}
    (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i) : i ⟶ a := by
  change @Etingof.ReversedAtVertexHom Q inst _ i a i at e
  unfold Etingof.ReversedAtVertexHom at e
  revert e
  exact match inst a i, inst i i with
  | .isTrue h, _ => absurd h ha
  | .isFalse _, .isFalse h => absurd rfl h
  | .isFalse _, .isTrue _ => fun e => e

/-- Canonical quotient map into F⁻ᵢ(ρ).obj i from the direct sum.
Reduces the `Decidable.casesOn` at vertex i (which is `.isTrue` since i = i)
and injects via the quotient map `mkQ`. -/
noncomputable def Etingof.reflFunctorMinus_mkQ
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) →ₗ[k]
    @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i := by
  -- Need AddCommGroup for Submodule.mkQ
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  unfold Etingof.reflectionFunctorMinus
  simp only
  exact match inst i i with
  | .isTrue _ => Submodule.mkQ _
  | .isFalse h => absurd rfl h

open Classical in
set_option maxHeartbeats 800000 in -- unfolding reflFunctorMinus_mkQ + reflectionFunctorMinus + match reduction
/-- The quotient map mkQ kills sourceMap elements: mkQ(∑ lof(a)(mapLinear(a.snd)(v))) = 0.
The mathematical content is: ψ(v) ∈ range(ψ) = ker(mkQ), so mkQ(ψ(v)) = 0.

Key technique: avoid `= 0` (where `0 : F⁻(ρ).obj i` has Decidable.rec in its type) by
first proving `= mkQ(0)` (where `0 : DirectSum` has no Decidable dependency), then
using `map_zero` to bridge. The `revert; unfold; rw [h_di]` pattern works because
both sides share the same `Decidable.casesOn` structure. -/
theorem Etingof.reflFunctorMinus_mkQ_kills_sourceMap
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : ρ.obj i) :
    Etingof.reflFunctorMinus_mkQ hi ρ
      (∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a)
          (ρ.mapLinear a.2 v)) = 0 := by
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  -- Step 1: Reformulate as mkQ(ψ v) = mkQ(0), avoiding abstract 0 : F⁻(ρ).obj i
  suffices h : Etingof.reflFunctorMinus_mkQ hi ρ
      (∑ a : Etingof.ArrowsOutOf Q i,
        (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a)
          (ρ.mapLinear a.2 v)) = Etingof.reflFunctorMinus_mkQ hi ρ 0 by
    rwa [map_zero] at h
  -- Step 2: Both sides share Decidable.casesOn structure, so rw [h_di] works
  revert v
  unfold Etingof.reflFunctorMinus_mkQ Etingof.reflectionFunctorMinus
  simp only []
  dsimp only [id]
  rw [h_di]
  intro v
  simp only []
  -- Provide AddCommGroup instances (must be letI for transparency to match unfolded defs)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- Goal: mkQ(∑ lof a (mapLinear a.2 v)) = mkQ(0) in CokerType
  rw [map_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨v, by simp [LinearMap.sum_apply, LinearMap.comp_apply]⟩

open Classical in
set_option maxHeartbeats 1600000 in
-- reason: unfolding reflectionFunctorMinus + equivAt_ne + mkQ + match reduction
/-- At (a ≠ i, b = i), the F⁻ᵢ map sends w to mkQ(lof ⟨a, reversed_arrow⟩ (equivAt_ne w))
in the quotient at vertex i.

Dual of `reflFunctorPlus_mapLinear_eq_ne`. -/
theorem Etingof.reflFunctorMinus_mapLinear_ne_eq
    {k : Type*} [CommRing k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    {a : Q} (ha : a ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a i)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a) :
    @Etingof.QuiverRepresentation.mapLinear k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) a i e w =
    (Etingof.reflFunctorMinus_mkQ hi ρ)
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i)
        (fun a => ρ.obj a.1) ⟨a, Etingof.reversedArrow_ne_eq ha e⟩
        ((Etingof.reflFunctorMinus_equivAt_ne hi ρ a ha) w)) := by
  have h_da : inst a i = .isFalse ha := by
    cases inst a i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  revert e w
  unfold Etingof.reflFunctorMinus_mkQ Etingof.reflFunctorMinus_equivAt_ne
    Etingof.reversedArrow_ne_eq
    Etingof.reflectionFunctorMinus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_da, h_di]
  intro e w
  rfl


end ReflectionFunctorMinusAPI
