import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure

/-!
# Proposition 6.6.6 (Source Case): F⁺ᵢ F⁻ᵢ V ≅ V

If ψ : V_i → ⊕_{i→j} V_j is injective (i.e., i is a source with injective source map),
then applying the reflection functors F⁺ᵢ after F⁻ᵢ recovers V up to isomorphism.

(Etingof Proposition 6.6.6, part 2)

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

section Helpers

-- Source-case arrow reindexing infrastructure (dual of sink-case arrowReindexEquiv)

/-- At a source i, all arrows out of i have target ≠ i. No self-loops since
IsSource says no arrows INTO i, including self-loops. -/
private theorem Etingof.arrowsOutOf_ne_source
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) : a.fst ≠ i := by
  obtain ⟨j, e⟩ := a; dsimp; intro heq; subst heq; exact (hi j).false e

/-- `ReversedAtVertexHom Q i j i = (i ⟶ j)` for j ≠ i, as a computable def for cast reduction. -/
private def Etingof.ReversedAtVertexHom_at_second_def
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i j : Q} (hj : j ≠ i) :
    Etingof.ReversedAtVertexHom Q i j i = (i ⟶ j) := by
  unfold Etingof.ReversedAtVertexHom
  cases inst j i with
  | isTrue h => exact absurd h hj
  | isFalse _ => cases inst i i with
    | isFalse h => exact absurd rfl h
    | isTrue _ => rfl

/-- Equivalence between ArrowsOutOf Q i and ArrowsInto Q̄ᵢ i.
Source-case dual of `arrowReindexEquiv`. Uses `cast` consistently for clean roundtrips. -/
private def Etingof.arrowReindexEquivSource
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) :
    Etingof.ArrowsOutOf Q i ≃
    @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i where
  toFun a := ⟨a.fst, cast (Etingof.ReversedAtVertexHom_at_second_def
    (Etingof.arrowsOutOf_ne_source hi a)).symm a.snd⟩
  invFun b := ⟨b.fst, cast (Etingof.ReversedAtVertexHom_at_second_def
    (Etingof.arrowsIntoReversed_ne hi b)) b.snd⟩
  left_inv a := by
    obtain ⟨j, e⟩ := a; refine Sigma.ext rfl ?_
    exact heq_of_eq (by simp [cast_cast])
  right_inv b := by
    obtain ⟨j, e⟩ := b; refine Sigma.ext rfl ?_
    exact heq_of_eq (by simp [cast_cast])

/-- Roundtrip: `reversedArrow_ne_eq` undoes the cast in `arrowReindexEquivSource`.
For `a : ArrowsOutOf Q i`, let `b = arrowReindexEquivSource hi a`. Then
`reversedArrow_ne_eq (arrowsIntoReversed_ne hi b) b.snd = a.snd`. -/
private theorem Etingof.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    Etingof.reversedArrow_ne_eq
      (Etingof.arrowsIntoReversed_ne hi (Etingof.arrowReindexEquivSource hi a))
      (Etingof.arrowReindexEquivSource hi a).snd = a.snd := by
  obtain ⟨j, e⟩ := a
  simp only [arrowReindexEquivSource, Equiv.coe_fn_mk]
  rw [reversedArrow_ne_eq_is_cast]
  simp [cast_cast]

/-- The sigma pair `⟨b.fst, reversedArrow_ne_eq b.snd⟩` for `b = arrowReindexEquivSource hi a`
equals the original `a : ArrowsOutOf Q i`. -/
private theorem Etingof.arrowReindexEquivSource_sigma_roundtrip
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    (⟨(Etingof.arrowReindexEquivSource hi a).fst,
      Etingof.reversedArrow_ne_eq
        (Etingof.arrowsIntoReversed_ne hi (Etingof.arrowReindexEquivSource hi a))
        (Etingof.arrowReindexEquivSource hi a).snd⟩ : Etingof.ArrowsOutOf Q i) = a := by
  obtain ⟨j, e⟩ := a
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Etingof.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip hi ⟨j, e⟩)

/-- The sigma pair `⟨b.fst, reversedArrow_ne_eq b.snd⟩` for `b : ArrowsInto Q̄ᵢ i` equals
`(arrowReindexEquivSource hi).symm b`. This lets us use `Equiv.injective` for the sigma-pair map. -/
private theorem Etingof.sigma_out_eq_arrowReindexEquivSource_symm
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (b : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i) :
    (⟨b.fst, Etingof.reversedArrow_ne_eq
        (Etingof.arrowsIntoReversed_ne hi b) b.snd⟩ : Etingof.ArrowsOutOf Q i) =
    (Etingof.arrowReindexEquivSource hi).symm b := by
  obtain ⟨j, e⟩ := b
  simp only [arrowReindexEquivSource, Equiv.coe_fn_symm_mk]
  refine Sigma.ext rfl ?_
  exact heq_of_eq (by rw [reversedArrow_ne_eq_is_cast])

/-- Reindex the source-map sum from `ArrowsInto Q̄ᵢ i` to `ArrowsOutOf Q i`.
Stated outside `equivAt_eq_source` to avoid `instR` instance pollution. -/
private theorem Etingof.sourceMap_sum_reindex
    {k : Type*} [CommRing k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    [Fintype (@Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i)]
    [DecidableEq (Etingof.ArrowsOutOf Q i)]
    (v : ρ.obj i) :
    (∑ x : @Etingof.ArrowsInto Q (Etingof.reversedAtVertex Q i) i,
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.fst)
        ⟨x.fst, Etingof.reversedArrow_ne_eq
          (Etingof.arrowsIntoReversed_ne hi x) x.snd⟩)
        (ρ.mapLinear (Etingof.reversedArrow_ne_eq
          (Etingof.arrowsIntoReversed_ne hi x) x.snd) v)) =
    (∑ a : Etingof.ArrowsOutOf Q i,
      (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.fst) a)
        (ρ.mapLinear a.snd v)) := by
  classical
  rw [← (Etingof.arrowReindexEquivSource hi).symm.bijective.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  -- a : ArrowsInto Q̄ᵢ i; show summands agree
  -- Both sides apply lof and mapLinear through the same sigma pair, just constructed differently
  obtain ⟨j, e⟩ := a
  simp only [arrowReindexEquivSource, Equiv.coe_fn_symm_mk,
    reversedArrow_ne_eq_is_cast, cast_cast]
  congr 1
  congr 1
  rw [reversedArrow_ne_eq_is_cast]

open Classical in
set_option maxHeartbeats 3200000 in
/-- `reflFunctorMinus_mkQ` has kernel equal to `range(sourceMap)`. This allows
deducing membership in `range(sourceMap)` from `mkQ(y) = 0`. -/
private theorem Etingof.reflFunctorMinus_mkQ_ker
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q]
    [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (y : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1))
    (hy : @Etingof.reflFunctorMinus_mkQ k _ Q inst_dec inst i hi ρ _
      y = 0) :
    y ∈ LinearMap.range
      (@Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ i _) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) :=
    fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i)
      (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  have h_di : inst_dec i i = .isTrue rfl := by
    match inst_dec i i with
    | .isTrue _ => rfl
    | .isFalse h => exact absurd rfl h
  suffices h : ∀ z :
      DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1),
      @Etingof.reflFunctorMinus_mkQ k _ Q inst_dec inst i hi ρ _ z =
      @Etingof.reflFunctorMinus_mkQ k _ Q inst_dec inst i hi ρ _ 0 →
      z ∈ LinearMap.range
        (@Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ
          i _) by
    exact h y (by rw [hy, map_zero])
  unfold Etingof.reflFunctorMinus_mkQ Etingof.reflectionFunctorMinus
  simp only []
  dsimp only [id]
  rw [h_di]
  intro z heq
  simp only [] at heq
  rw [map_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at heq
  exact heq

open Classical in
set_option maxHeartbeats 3200000 in
/-- `reflFunctorMinus_mkQ` is surjective (it is the quotient projection
in the `isTrue` branch). -/
private theorem Etingof.reflFunctorMinus_mkQ_surjective
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q]
    [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Function.Surjective
      (@Etingof.reflFunctorMinus_mkQ k _ Q inst_dec inst i hi ρ _) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) :=
    fun v => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i)
      (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  have h_di : inst_dec i i = .isTrue rfl := by
    match inst_dec i i with
    | .isTrue _ => rfl
    | .isFalse h => exact absurd rfl h
  intro z
  revert z
  unfold Etingof.reflFunctorMinus_mkQ Etingof.reflectionFunctorMinus
  simp only []
  dsimp only [id]
  rw [h_di]
  intro z
  exact Submodule.mkQ_surjective _ z

set_option maxHeartbeats 12800000 in
-- reason: equivAt_eq composition + ker(sinkMap) ≃ V_i via injectivity
/-- At vertex i, F⁺(F⁻(V)).obj i ≃ₗ[k] ρ.obj i when the source map is injective.

F⁻ᵢ(V).obj i = coker(ψ) = (⊕V_j)/Im(ψ). Then F⁺ᵢ at vertex i (now a sink in Q̄ᵢ)
gives ker(sinkMap of F⁻(V)). When ψ is injective, this kernel is isomorphic to V_i
via the embedding v ↦ ψ(v) (viewed in the kernel after reindexing). -/
private noncomputable def Etingof.equivAt_eq_source
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hinj : Function.Injective (ρ.sourceMap i)) :
    @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorPlus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSource_reversedAtVertex_isSink Q _ inst i hi)
        (@Etingof.reflectionFunctorMinus k _ Q _ inst i hi ρ _)) i ≃ₗ[k]
    ρ.obj i := by
  -- Upgrade to AddCommGroup (needed for quotient module)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  -- Unfold F⁺ to expose ker(sinkMap of F⁻(ρ) at i)
  unfold Etingof.reflectionFunctorPlus
  simp only
  refine match inst_dec i i with
  | .isFalse h => absurd rfl h
  | .isTrue _ => ?_
  -- Now goal: ker(F⁻(ρ).sinkMap i) ≃ₗ[k] ρ.obj i
  dsimp only [id]
  classical
  let instR := @Etingof.reversedAtVertex Q _ inst i
  let ρ_minus := @Etingof.reflectionFunctorMinus k _ Q _ inst i hi ρ _
  -- Fintype for ArrowsInto in reversed quiver
  haveI : Fintype (@Etingof.ArrowsInto Q instR i) :=
    Fintype.ofEquiv _ (@Etingof.arrowReindexEquivSource Q _ inst i hi)
  -- AddCommGroup instances for F⁻ representation components
  letI acg_comp : ∀ b : @Etingof.ArrowsInto Q instR i,
      AddCommGroup (@Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst) :=
    fun b => @Etingof.addCommGroupOfRing k _ _ (ρ_minus.instAddCommMonoid b.fst) (ρ_minus.instModule b.fst)
  letI acg_ds : AddCommGroup (DirectSum (@Etingof.ArrowsInto Q instR i)
      (fun b => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst)) :=
    @Etingof.addCommGroupOfRing k _ _ _ _
  -- Forward map: ρ.obj i → ⊕ F⁻(ρ).obj b.fst via equivAt_ne⁻¹ ∘ mapLinear(reversedArrow)
  -- Using reversedArrow_ne_eq (not origArrow) for clean composition with
  -- reflFunctorMinus_mapLinear_ne_eq in the kernel proof.
  let f_component : (b : @Etingof.ArrowsInto Q instR i) →
      @Etingof.QuiverRepresentation.obj k Q _ inst ρ i →ₗ[k]
      @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst :=
    fun b =>
      ((@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
        (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)).symm.toLinearMap).comp
        (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i b.fst
          (@Etingof.reversedArrow_ne_eq Q _ inst i b.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b) b.snd))
  let f_ds : @Etingof.QuiverRepresentation.obj k Q _ inst ρ i →ₗ[k]
      DirectSum (@Etingof.ArrowsInto Q instR i)
        (fun b => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst) :=
    ∑ b, (DirectSum.lof k _ _ b).comp (f_component b)
  -- Kernel proof: sinkMap(f_ds v) = 0
  -- Mathematical argument: sinkMap(f_ds v) = ∑_b mapLinear(b.snd)(f_component b v)
  -- By reflFunctorMinus_mapLinear_ne_eq, each component becomes
  -- mkQ(lof ⟨b.fst, reversedArrow_ne_eq⟩ (equivAt_ne(equivAt_ne⁻¹(ρ.mapLinear(arrow)(v)))))
  -- = mkQ(lof(arrow_out)(ρ.mapLinear(arrow)(v)))
  -- Summing over b gives mkQ(sourceMap(v)) = 0 since sourceMap(v) ∈ range(sourceMap) = ker(mkQ).
  -- Helper: sinkMap(lof b w) = mapLinear(b.snd)(w)
  have sinkMap_lof : ∀ (b : @Etingof.ArrowsInto Q instR i)
      (w : @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst),
      @Etingof.QuiverRepresentation.sinkMap k _ Q instR ρ_minus i
        (DirectSum.lof k _ _ b w) =
      @Etingof.QuiverRepresentation.mapLinear k Q _ instR ρ_minus b.fst i b.snd w := by
    intro b w
    delta Etingof.QuiverRepresentation.sinkMap
    erw [DirectSum.toModule_lof]
  have h_ker : ∀ v, @Etingof.QuiverRepresentation.sinkMap k _ Q instR ρ_minus i (f_ds v) = 0 := by
    intro v
    simp only [f_ds, f_component]
    rw [LinearMap.sum_apply, map_sum]
    simp_rw [LinearMap.comp_apply]
    simp_rw [sinkMap_lof]
    -- Unfold let bindings so reflFunctorMinus_mapLinear_ne_eq can match
    change ∑ x : @Etingof.ArrowsInto Q (@Etingof.reversedAtVertex Q inst_dec inst i) i,
      @Etingof.QuiverRepresentation.mapLinear k Q _
        (@Etingof.reversedAtVertex Q inst_dec inst i)
        (@Etingof.reflectionFunctorMinus k _ Q inst_dec inst i hi ρ _) x.fst i x.snd
        ((↑(@Etingof.reflFunctorMinus_equivAt_ne k _ Q inst_dec inst i hi ρ _ x.fst
            (@Etingof.arrowsIntoReversed_ne Q inst_dec inst i hi x)).symm ∘ₗ
          @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i x.fst
            (@Etingof.reversedArrow_ne_eq Q inst_dec inst i x.fst
              (@Etingof.arrowsIntoReversed_ne Q inst_dec inst i hi x) x.snd)) v) = 0
    simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    -- Goal: ∑ x, mapLinear(x.snd)(equivAt_ne⁻¹(mapLinear(arrow)(v))) = 0
    -- Local wrapper for reflFunctorMinus_mapLinear_ne_eq with correct instances
    have h_mapL := fun (x : @Etingof.ArrowsInto Q instR i) (w : ρ_minus.obj x.fst) =>
      @Etingof.reflFunctorMinus_mapLinear_ne_eq k _ Q inst_dec inst i hi ρ _ x.fst
        (@Etingof.arrowsIntoReversed_ne Q inst_dec inst i hi x) x.snd w
    simp_rw [h_mapL, LinearEquiv.apply_symm_apply, ← map_sum]
    -- Goal: mkQ(∑ x : ArrowsInto Q̄ᵢ i, lof ⟨...⟩ (mapLinear(...)(v))) = 0
    -- Use sourceMap_sum_reindex to convert sum to ArrowsOutOf, then kills_sourceMap
    have h_sr := @Etingof.sourceMap_sum_reindex k _ Q inst_dec inst i hi ρ _ _ _ v
    rw [h_sr]
    exact @Etingof.reflFunctorMinus_mkQ_kills_sourceMap k _ Q inst_dec inst i hi ρ _ v
  -- Restrict to kernel subtype
  let f : @Etingof.QuiverRepresentation.obj k Q _ inst ρ i →ₗ[k]
      ↥(LinearMap.ker (@Etingof.QuiverRepresentation.sinkMap k _ Q instR ρ_minus i)) :=
    LinearMap.codRestrict _ f_ds (fun v => LinearMap.mem_ker.mpr (h_ker v))
  -- Injectivity: f(v) = 0 implies v = 0 via sourceMap injectivity
  -- Mathematical argument: f_ds(v) = 0 ⟹ each component equivAt_ne⁻¹(mapLinear(arrow b)(v)) = 0
  -- ⟹ mapLinear(arrow b)(v) = 0 for all arrows ⟹ sourceMap(v) = 0 ⟹ v = 0 by hinj
  have f_inj : Function.Injective f := by
    intro x y hxy
    apply hinj
    -- f = codRestrict f_ds, so f x = f y implies f_ds x = f_ds y
    have h_eq : f_ds x = f_ds y := congr_arg Subtype.val hxy
    -- Component extraction: (f_ds v) c = f_component c v via DFinsupp single properties
    have h_comp : ∀ c : @Etingof.ArrowsInto Q instR i,
        f_component c x = f_component c y := by
      intro c
      have h_c := DFunLike.congr_fun h_eq c
      suffices key : ∀ v, (f_ds v : Π₀ _, _) c = f_component c v from
        (key x).symm.trans (h_c.trans (key y))
      intro v
      simp only [f_ds, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [DFinsupp.finset_sum_apply,
        Finset.sum_eq_single c
          (fun b _ hbc => by erw [DFinsupp.single_eq_of_ne (Ne.symm hbc)])
          (fun h => absurd (Finset.mem_univ c) h)]
      erw [DFinsupp.single_eq_same]
    -- For each arrow a, mapLinear a.2 x = mapLinear a.2 y (via h_comp + arrowReindexEquivSource)
    have h_map : ∀ a : @Etingof.ArrowsOutOf Q inst i,
        @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i a.fst a.snd x =
        @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i a.fst a.snd y := by
      intro a
      let b := @Etingof.arrowReindexEquivSource Q inst_dec inst i hi a
      have h_b := h_comp b
      simp only [f_component] at h_b
      have h_ml := (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
        (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)).symm.injective h_b
      -- h_ml : mapLinear(reversedArrow_ne_eq b.snd)(x) = mapLinear(reversedArrow_ne_eq b.snd)(y)
      -- Use roundtrip: reversedArrow_ne_eq(arrowReindexEquivSource(a).snd) = a.snd
      have h_rt := @Etingof.reversedArrow_ne_eq_arrowReindexEquivSource_roundtrip
        Q inst_dec inst i hi a
      rw [h_rt] at h_ml
      exact h_ml
    -- sourceMap x = sourceMap y
    show @Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ i _ x =
         @Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ i _ y
    delta Etingof.QuiverRepresentation.sourceMap
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    exact Finset.sum_congr rfl (fun a _ => congrArg _ (h_map a))
  -- Surjectivity of f via Phi transport map.
  -- Override Quiver instance to reversedAtVertex so that ρ_minus.obj/sinkMap/mapLinear
  -- resolve correctly. Use @-notation with inst for all ρ-based references.
  have f_surj : Function.Surjective f := by
    letI : Quiver Q := instR
    -- Module k (ρ.obj v) no longer auto-derived (active Quiver ≠ inst); provide explicitly.
    letI : ∀ v, Module k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ v) :=
      fun v => @Etingof.QuiverRepresentation.instModule k Q _ inst ρ v
    -- Override DecidableEq for ArrowsOutOf to ensure consistency between Phi definition and usage
    letI dec_out : DecidableEq (@Etingof.ArrowsOutOf Q inst i) := Classical.decEq _
    -- Phi: componentwise equivAt_ne transport map
    let Phi : DirectSum (Etingof.ArrowsInto Q i)
          (fun b => ρ_minus.obj b.fst) →ₗ[k]
        DirectSum (@Etingof.ArrowsOutOf Q inst i)
          (fun a => @Etingof.QuiverRepresentation.obj k Q _ inst ρ a.fst) :=
      DirectSum.toModule k _ _ (fun b =>
        (DirectSum.lof k _ _
          (⟨b.fst, @Etingof.reversedArrow_ne_eq Q _ inst i b.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b) b.snd⟩ :
            @Etingof.ArrowsOutOf Q inst i)).comp
        ((@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
          (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)).toLinearMap))
    -- Named type families for the two direct sums
    let β_in : Etingof.ArrowsInto Q i → Type _ := fun c => ρ_minus.obj c.fst
    let β_out : @Etingof.ArrowsOutOf Q inst i → Type _ :=
      fun a => @Etingof.QuiverRepresentation.obj k Q _ inst ρ a.fst
    -- Phi(lof b w) = lof ⟨...⟩ (equivAt_ne w) via toModule_lof
    have Phi_lof : ∀ (b : @Etingof.ArrowsInto Q instR i) (w : β_in b),
        Phi (DirectSum.lof k _ β_in b w) =
        (DirectSum.lof k _ β_out
          ⟨b.fst, @Etingof.reversedArrow_ne_eq Q _ inst i b.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b) b.snd⟩)
        ((@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
          (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)) w) := by
      intro b w
      change (DirectSum.toModule _ _ _ _) (DirectSum.lof _ _ _ b w) = _
      erw [DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    -- sinkMap = mkQ ∘ Phi
    have h_sinkMap_Phi : ∀ x,
        ρ_minus.sinkMap i x =
        (@Etingof.reflFunctorMinus_mkQ k _ Q _ inst i hi ρ _) (Phi x) := by
      intro x
      -- Decompose x as sum of lof components
      rw [show x = ∑ b ∈ Finset.univ,
        DirectSum.of _ b ((x : Π₀ _, _) b) from
        (DirectSum.sum_univ_of x).symm]
      simp only [map_sum]
      apply Finset.sum_congr rfl; intro b _
      -- Convert of → lof (definitionally equal), then use sinkMap_lof + Phi_lof
      change ρ_minus.sinkMap i (DirectSum.lof k _ _ b ((x : Π₀ _, _) b)) =
        (@Etingof.reflFunctorMinus_mkQ k _ Q _ inst i hi ρ _)
          (Phi (DirectSum.lof k _ _ b ((x : Π₀ _, _) b)))
      rw [sinkMap_lof, Phi_lof]
      exact @Etingof.reflFunctorMinus_mapLinear_ne_eq k _ Q _ inst i hi ρ _
        b.fst (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b) b.snd
        ((x : Π₀ _, _) b)
    -- Phi ∘ f_ds = sourceMap
    have h_Phi_f_ds : ∀ v, Phi (f_ds v) =
        @Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ i _ v := by
      intro v
      -- Decompose f_ds v into sum of lof components
      have h_f_ds_def : ∀ w, f_ds w = ∑ b,
          (DirectSum.lof k _ _ b) (f_component b w) := by
        intro w; simp [f_ds, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [h_f_ds_def, map_sum]
      -- Apply Phi_lof to each summand
      conv_lhs =>
        arg 2; ext b
        rw [show DirectSum.lof k _ (fun b => ρ_minus.obj b.fst) b =
              DirectSum.lof k _ β_in b from rfl, Phi_lof]
      -- equivAt_ne(f_component b v) = mapLinear(reversedArrow_ne_eq b.snd)(v)
      have h_cancel : ∀ (b : @Etingof.ArrowsInto Q instR i),
          (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)) ((f_component b) v) =
          @Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i b.fst
            (@Etingof.reversedArrow_ne_eq Q _ inst i b.fst
              (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b) b.snd) v := by
        intro b; simp only [f_component]
        erw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
        exact LinearEquiv.apply_symm_apply _ _
      simp_rw [h_cancel]
      -- Now: ∑ b, lof ⟨...⟩ (mapLinear(reversedArrow_ne_eq b.snd)(v)) = sourceMap v
      change _ = (@Etingof.QuiverRepresentation.sourceMap k _ Q inst ρ i _) v
      delta Etingof.QuiverRepresentation.sourceMap
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      exact @Etingof.sourceMap_sum_reindex k _ Q inst_dec inst i hi ρ _ _ _ v
    -- Phi is injective: extract component via reindex bijection
    -- Component extraction helper: (Phi(lof d w))(reindex c) for d ≠ c gives 0
    have Phi_of_ne : ∀ (c d : @Etingof.ArrowsInto Q instR i)
        (w : ρ_minus.obj d.fst),
        c ≠ d →
        (Phi (DirectSum.of (fun d => ρ_minus.obj d.fst) d w) : Π₀ _, _)
          ⟨c.fst, @Etingof.reversedArrow_ne_eq Q _ inst i c.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi c) c.snd⟩ = 0 := by
      intro c d w hcd
      change (Phi (DirectSum.lof k _ β_in d w) : Π₀ _, _) _ = _
      rw [Phi_lof]; erw [DFinsupp.single_eq_of_ne]
      intro h_eq
      exact hcd ((@Etingof.arrowReindexEquivSource Q inst_dec inst i hi).symm.injective
        (by rw [← @Etingof.sigma_out_eq_arrowReindexEquivSource_symm Q _ inst i hi d,
                ← @Etingof.sigma_out_eq_arrowReindexEquivSource_symm Q _ inst i hi c, h_eq])).symm
    have Phi_of_eq : ∀ (c : @Etingof.ArrowsInto Q instR i)
        (w : ρ_minus.obj c.fst),
        (Phi (DirectSum.of (fun d => ρ_minus.obj d.fst) c w) : Π₀ _, _)
          ⟨c.fst, @Etingof.reversedArrow_ne_eq Q _ inst i c.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi c) c.snd⟩ =
        (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ c.fst
          (@Etingof.arrowsIntoReversed_ne Q _ inst i hi c)) w := by
      intro c w
      change (Phi (DirectSum.lof k _ β_in c w) : Π₀ _, _) _ = _
      rw [Phi_lof]; erw [DFinsupp.single_eq_same]
    have Phi_inj : Function.Injective Phi := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      have hPhi := LinearMap.mem_ker.mp hx
      ext c
      -- Decompose Phi x at component reindex(c)
      have h_decomp : (Phi x : Π₀ _, _)
          ⟨c.fst, @Etingof.reversedArrow_ne_eq Q _ inst i c.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi c) c.snd⟩ =
          (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ c.fst
            (@Etingof.arrowsIntoReversed_ne Q _ inst i hi c)) ((x : Π₀ _, _) c) := by
        conv_lhs => rw [(DirectSum.sum_univ_of x).symm]
        rw [map_sum, DFinsupp.finset_sum_apply]
        rw [Finset.sum_eq_single c
          (fun d _ hdc => Phi_of_ne c d _ (Ne.symm hdc))
          (fun h => absurd (Finset.mem_univ c) h)]
        exact Phi_of_eq c _
      rw [hPhi, DFinsupp.coe_zero, Pi.zero_apply] at h_decomp
      exact (LinearEquiv.map_eq_zero_iff _).mp h_decomp.symm
    -- Main surjectivity argument
    intro ⟨x, hx_mem⟩
    have hx : ρ_minus.sinkMap i x = 0 := LinearMap.mem_ker.mp hx_mem
    have h_Phi_x_mkQ :
        @Etingof.reflFunctorMinus_mkQ k _ Q _ inst i hi ρ _ (Phi x) = 0 := by
      rw [← h_sinkMap_Phi]; exact hx
    obtain ⟨v, hv⟩ := @Etingof.reflFunctorMinus_mkQ_ker k _ Q _ inst i hi ρ _
      (Phi x) h_Phi_x_mkQ
    have h_eq : f_ds v = x := Phi_inj (by rw [h_Phi_f_ds]; exact hv)
    exact ⟨v, Subtype.ext h_eq⟩
  -- Construct the LinearEquiv directly (avoiding ofBijective.symm which causes
  -- RingHomInvPair synthesis issues in downstream naturality proofs)
  let g := Function.surjInv f_surj
  have g_left : Function.LeftInverse g f :=
    fun v => f_inj (Function.surjInv_eq f_surj (f v))
  have g_right : Function.RightInverse g f := Function.surjInv_eq f_surj
  exact
  { f.inverse g g_left g_right with
    invFun := f
    left_inv := g_right
    right_inv := g_left }

set_option maxHeartbeats 6400000 in
-- reason: equivAt_eq_source unfold + Decidable.casesOn match reduction
/-- Source naturality for equivAt_eq_source: the b-component of ↑(equivAt_eq(x)),
after applying equivAt_ne, equals mapLinear(e)(equivAt_eq_source(x)).
Proved in a separate lemma to avoid instance diamond from the main proof's let-bound instances. -/
private theorem Etingof.equivAt_eq_source_naturality
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hinj : Function.Injective (ρ.sourceMap i))
    (b : Q) (hb : ¬b = i)
    (e : @Quiver.Hom Q inst i b)
    (x : @Etingof.QuiverRepresentation.obj k Q _
      (@Etingof.reversedAtVertex Q _ (@Etingof.reversedAtVertex Q _ inst i) i)
      (@Etingof.reflectionFunctorPlus k _ Q _
        (@Etingof.reversedAtVertex Q _ inst i) i
        (@Etingof.isSource_reversedAtVertex_isSink Q _ inst i hi)
        (@Etingof.reflectionFunctorMinus k _ Q _ inst i hi ρ _)) i) :
    let instR := @Etingof.reversedAtVertex Q _ inst i
    let ρ_minus := @Etingof.reflectionFunctorMinus k _ Q _ inst i hi ρ _
    let hi' := @Etingof.isSource_reversedAtVertex_isSink Q _ inst i hi
    let arrow_R : @Quiver.Hom Q
        (@Etingof.reversedAtVertex Q inst_dec instR i) i b :=
      (@Etingof.reversedAtVertex_twice Q _ inst i).symm ▸ e
    let b_idx : @Etingof.ArrowsInto Q instR i :=
      ⟨b, @Etingof.reversedArrow_eq_ne Q inst_dec instR i b hb arrow_R⟩
    (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b hb)
      ((DirectSum.component k (@Etingof.ArrowsInto Q instR i)
          (fun c => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus c.fst)
          b_idx)
        ((ρ_minus.sinkMap i).ker.subtype
          ((@Etingof.reflFunctorPlus_equivAt_eq k _ Q _ instR i hi' ρ_minus) x))) =
    (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ i b e)
      ((@Etingof.equivAt_eq_source k _ Q inst_dec inst i hi ρ _ _ _ hinj) x) := by
  -- Key insight: save the LinearEquiv property BEFORE unfolding.
  -- After unfolding equivAt_eq_source, the LinearEquiv structure is expanded and
  -- h_sym reduces to codRestrict(f_ds)(surjInv(x)) = x.
  have h_sym :=
    (@Etingof.equivAt_eq_source k _ Q inst_dec inst i hi ρ
      _ _ _ hinj).symm_apply_apply x
  simp only
  revert h_sym x e
  unfold Etingof.equivAt_eq_source Etingof.reflFunctorPlus_equivAt_eq
    Etingof.reflectionFunctorPlus
  simp only
  refine match inst_dec i i with
  | .isFalse h => absurd rfl h
  | .isTrue _ => ?_
  dsimp only [id]
  intro e x h_sym
  simp only [LinearEquiv.refl_apply, Submodule.coe_subtype]
  dsimp at h_sym ⊢
  dsimp [LinearMap.inverse] at h_sym ⊢
  -- h_sym : codRestrict(f_ds)(surjInv(x)) = x
  -- Extract val: f_ds(surjInv(x)) = ↑x
  have h_val := congr_arg Subtype.val h_sym
  dsimp [LinearMap.codRestrict] at h_val
  rw [← h_val]
  sorry

end Helpers

/-- If ψ is injective at a source, then applying F⁺ᵢ after F⁻ᵢ recovers V
up to isomorphism of representations.

The composition F⁺ᵢ(F⁻ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 2) -/
theorem Etingof.Proposition6_6_6_source
    {k : Type*} [Field k]
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
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
  let instR := @Etingof.reversedAtVertex Q _ inst i
  let instDR := @Etingof.reversedAtVertex Q _ instR i
  let ρ_minus := @Etingof.reflectionFunctorMinus k _ Q _ inst i hi ρ
  let hi' := @Etingof.isSource_reversedAtVertex_isSink Q _ inst i hi
  let ρ_dr := @Etingof.reflectionFunctorPlus k _ Q _ instR i hi' ρ_minus
  exact Etingof.QuiverRepresentation.crossIsoToIso
    (@Etingof.reversedAtVertex_twice Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      · cases hv
        exact @Etingof.equivAt_eq_source k _ Q _ inst i hi ρ _ _ _ hinj
      · exact (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _
          instR i hi' ρ_minus v hv).trans
          (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ v hv))
    (fun {a b} e x => by
      by_cases hb : b = i
      · -- b = i: vacuous — i is a source, no arrows into i
        subst hb; exact ((hi a).false e).elim
      · by_cases ha : a = i
        · -- a = i, b ≠ i: arrow from source, involves equivAt_eq_source
          rw [eq_comm] at ha; subst ha
          simp only [dif_neg hb, LinearEquiv.trans_apply, dite_true]
          -- Step 1: Reduce F⁺ map via API lemma
          rw [@Etingof.reflFunctorPlus_mapLinear_eq_ne k _ Q _ instR i hi' ρ_minus b hb
              ((@Etingof.reversedAtVertex_twice Q _ inst i).symm ▸ e) x]
          -- Source naturality via separate lemma (avoids instance diamond)
          exact @Etingof.equivAt_eq_source_naturality k _ Q inst_dec inst i hi ρ
            _ _ _ hinj b hb e x
        · -- a ≠ i, b ≠ i: use API lemmas compositionally
          simp only [dif_neg ha, dif_neg hb, LinearEquiv.trans_apply]
          rw [@Etingof.reflFunctorPlus_mapLinear_ne_ne k _ Q _
            instR i hi' ρ_minus a b ha hb
            ((@Etingof.reversedAtVertex_twice Q _ inst i).symm ▸ e) x]
          rw [@Etingof.reflFunctorMinus_mapLinear_ne_ne k _ Q _ inst i hi ρ _ a b ha hb]
          rw [@Etingof.reversedArrow_ne_ne_twice Q _ inst i a b ha hb e])
