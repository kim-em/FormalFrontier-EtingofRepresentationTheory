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
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
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
    fun b => @Etingof.addCommGroupOfField k _ _ (ρ_minus.instAddCommMonoid b.fst) (ρ_minus.instModule b.fst)
  letI acg_ds : AddCommGroup (DirectSum (@Etingof.ArrowsInto Q instR i)
      (fun b => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst)) :=
    @Etingof.addCommGroupOfField k _ _ _ _
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
  -- FiniteDimensional instances for linearEquivOfInjective
  -- Each F⁻(ρ).obj b.fst ≅ ρ.obj b.fst (via equivAt_ne), so finite-dimensional
  haveI : ∀ b : @Etingof.ArrowsInto Q instR i,
      Module.Free k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst) :=
    fun b => Module.Free.of_equiv
      (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
        (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)).symm
  haveI : ∀ b : @Etingof.ArrowsInto Q instR i,
      Module.Finite k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst) :=
    fun b => Module.Finite.equiv
      (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _ inst i hi ρ _ b.fst
        (@Etingof.arrowsIntoReversed_ne Q _ inst i hi b)).symm
  haveI : FiniteDimensional k (DirectSum (@Etingof.ArrowsInto Q instR i)
      (fun b => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst)) :=
    @Module.Finite.instDirectSum k (@Etingof.ArrowsInto Q instR i) _
      inferInstance
      (fun b => @Etingof.QuiverRepresentation.obj k Q _ instR ρ_minus b.fst)
      (fun b => (acg_comp b).toAddCommMonoid)
      (fun b => ρ_minus.instModule b.fst)
      (fun b => inferInstance)
  -- Dimension equality: finrank(V_i) = finrank(ker(sinkMap))
  -- Proof sketch: sinkMap_ρ_minus = mkQ ∘ T where T is componentwise equivAt_ne (isomorphism).
  -- So ker(sinkMap) = T⁻¹(ker(mkQ)) = T⁻¹(range(sourceMap)), giving
  -- finrank(ker(sinkMap)) = finrank(range(sourceMap)) = finrank(V_i) (by hinj).
  -- Blocked: requires establishing sinkMap = mkQ ∘ T, which involves unfolding
  -- reflectionFunctorMinus definitions through Decidable.casesOn wrappers.
  have hdim : Module.finrank k (@Etingof.QuiverRepresentation.obj k Q _ inst ρ i) =
      Module.finrank k ↥(LinearMap.ker (@Etingof.QuiverRepresentation.sinkMap k _ Q instR ρ_minus i)) := by
    sorry
  have f_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp f_inj
  exact (LinearEquiv.ofBijective f ⟨f_inj, f_surj⟩).symm

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
          -- Step 2: Unfold equivAt_eq_source and equivAt_eq to enter match
          revert x e
          unfold Etingof.equivAt_eq_source Etingof.reflFunctorPlus_equivAt_eq
            Etingof.reflectionFunctorPlus
          simp only
          refine match inst_dec i i with
          | .isFalse h => absurd rfl h
          | .isTrue _ => ?_
          dsimp only [id]
          intro x e
          -- Inside .isTrue: equivAt_eq = refl, equivAt_eq_source = ofBijective.symm
          simp only [LinearEquiv.refl_apply, Submodule.coe_subtype]
          -- Source naturality: for v = ofBijective.symm(e), ↑e = f_ds(v) by apply_symm_apply,
          -- component_b(f_ds(v)) = equivAt_ne⁻¹(mapLinear(arrow_b)(v)),
          -- so equivAt_ne(component_b(↑e)) = mapLinear(arrow_b)(v) by apply_symm_apply,
          -- and arrow_b = x by reversedArrow_eq_ne_ne_eq_twice.
          -- Blocked: instance diamond between Submodule.addCommMonoid and
          -- AddCommGroup.toAddCommMonoid prevents naming the ofBijective term
          -- (set/generalize/have all fail with synthesis errors).
          sorry
        · -- a ≠ i, b ≠ i: use API lemmas compositionally
          simp only [dif_neg ha, dif_neg hb, LinearEquiv.trans_apply]
          rw [@Etingof.reflFunctorPlus_mapLinear_ne_ne k _ Q _
            instR i hi' ρ_minus a b ha hb
            ((@Etingof.reversedAtVertex_twice Q _ inst i).symm ▸ e) x]
          rw [@Etingof.reflFunctorMinus_mapLinear_ne_ne k _ Q _ inst i hi ρ _ a b ha hb]
          rw [@Etingof.reversedArrow_ne_ne_twice Q _ inst i a b ha hb e])
