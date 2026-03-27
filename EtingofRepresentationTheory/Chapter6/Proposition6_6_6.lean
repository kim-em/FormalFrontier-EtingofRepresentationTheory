import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure

/-!
# Proposition 6.6.6 (Sink Case): F⁻ᵢ F⁺ᵢ V ≅ V

If φ : ⊕_{j→i} V_j → V_i is surjective (i.e., i is a sink with surjective sink map),
then applying the reflection functors F⁻ᵢ after F⁺ᵢ recovers V up to isomorphism.

(Etingof Proposition 6.6.6, part 1)

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

section Helpers

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
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
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
    {k : Type*} [Field k] {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
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
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  -- Eliminate Decidable.casesOn on (inst_dec i i) using `refine match` so that
  -- inside the .isTrue branch, inst_dec i i reduces definitionally. This avoids
  -- Eq.mpr wrappers from `rw [h_di]` that block external computation.
  unfold Etingof.reflectionFunctorMinus
  simp only
  refine match inst_dec i i with
  | .isFalse h => absurd rfl h
  | .isTrue _ => ?_
  -- Goal: (⊕_{a : ArrowsOutOf Q̄ᵢ i} F⁺(V)_a.fst) ⧸ range(ψ') ≃ₗ[k] V_i
  -- Strategy: Φ = sinkMap after reindexing, then first isomorphism theorem
  classical
    -- Goal: (⊕_{a : ArrowsOutOf_{Q̄ᵢ} i} F⁺(V).obj a.fst) ⧸ range(ψ') ≃ₗ[k] ρ.obj i
    -- Strategy: construct forward and inverse maps directly
    let instR := @Etingof.reversedAtVertex Q _ inst i
    let ρ' := @Etingof.reflectionFunctorPlus k _ Q _ inst i hi ρ
    -- Forward map Φ : ⊕ F⁺(V).obj a.fst → V_i (inline for instance synthesis)
    let Φ_component : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst →ₗ[k]
        @Etingof.QuiverRepresentation.obj k Q _ inst ρ i :=
      fun a => (@Etingof.QuiverRepresentation.mapLinear k Q _ inst ρ a.fst i
        (@Etingof.arrowsOutReversed_origArrow Q _ inst i hi a)).comp
        (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ a.fst
          (@Etingof.arrowsOutReversed_ne Q _ inst i hi a)).toLinearMap
    let Φ := DirectSum.toModule k _ _ Φ_component
    -- Provide AddCommGroup instances for quotient module construction
    letI acg_comp : ∀ a : @Etingof.ArrowsOutOf Q instR i,
        AddCommGroup (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst) :=
      fun a => @Etingof.addCommGroupOfRing k _ _ (ρ'.instAddCommMonoid a.fst) (ρ'.instModule a.fst)
    letI acg_ds : AddCommGroup (DirectSum (@Etingof.ArrowsOutOf Q instR i)
        (fun a => @Etingof.QuiverRepresentation.obj k Q _ instR ρ' a.fst)) :=
      @Etingof.addCommGroupOfRing k _ _ _ _
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
          @Etingof.addCommGroupOfRing k _ _
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
            simp only [DirectSum.zero_apply]
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
        haveI : Module.Free k (@Etingof.QuiverRepresentation.obj k Q _ instR ρ' i) := by
          -- In the .isTrue branch, ρ'.obj i is definitionally ker(sinkMap).
          -- Use Submodule.instModuleFree (submodules of free modules over PIDs are free).
          haveI : Fintype (@Etingof.ArrowsInto Q inst i) :=
            Fintype.ofEquiv _ (@Etingof.arrowReindexEquiv Q _ inst i hi)
          exact inferInstance
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

end Helpers

set_option maxHeartbeats 12800000 in
-- reason: crossIsoToIso + equivAt case analysis + full Decidable.casesOn reduction via unfold/rw
/-- If φ is surjective at a sink, then applying F⁻ᵢ after F⁺ᵢ recovers V
up to isomorphism of representations.

The composition F⁻ᵢ(F⁺ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 1) -/
theorem Etingof.Proposition6_6_6_sink
    {k : Type*} [Field k]
    {Q : Type*} [inst_dec : DecidableEq Q] [inst : Quiver Q]
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
  let hi' := @Etingof.isSink_reversedAtVertex_isSource Q _ inst i hi
  let ρ_dr := @Etingof.reflectionFunctorMinus k _ Q _ instR i hi' ρ_plus _
  exact Etingof.QuiverRepresentation.crossIsoToIso
    (@Etingof.reversedAtVertex_twice Q _ inst i)
    (fun v => by
      by_cases hv : v = i
      · -- v = i: first isomorphism theorem
        cases hv
        exact @Etingof.equivAt_eq_sink k _ Q _ inst i hi ρ _ _ _ hsurj
      · -- v ≠ i: use explicit composition of the two equivAt_ne equivs
        exact (@Etingof.reflFunctorMinus_equivAt_ne k _ Q _
          instR i hi' ρ_plus _ v hv).trans
          (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ inst i hi ρ v hv))
    (fun {a b} e x => by
      -- Naturality: the isomorphism commutes with representation maps.
      by_cases ha : a = i
      · -- a = i: vacuous — i is a sink, so there are no arrows out of i
        subst ha; exact ((hi b).false e).elim
      · by_cases hb : b = i
        · -- a ≠ i, b = i: arrow a → i, involves equivAt_eq_sink at target
          rw [eq_comm] at hb; subst hb
          -- Reduce crossIsoToIso dif/dite structure first
          simp only [dif_neg ha, LinearEquiv.trans_apply, dite_true]
          -- Step 1: Reduce F⁻ mapLinear at (a,i) with a≠i via API lemma
          rw [@Etingof.reflFunctorMinus_mapLinear_ne_eq k _ Q inst_dec instR i hi'
            ρ_plus _ a ha]
          -- Now goal:
          --   equivAt_eq_sink(mkQ(lof ⟨a,...⟩ (equivAt_ne_minus x))) =
          --   ρ.mapLinear(e)(equivAt_ne_plus(equivAt_ne_minus x))
          -- Step 2: Unfold equivAt_eq_sink and reflFunctorMinus_mkQ, then
          -- match on inst_dec i i to enter the .isTrue branch.
          -- We do NOT unfold equivAt_ne or match on inst_dec a i — those
          -- terms are already opaque API lemma results and don't need reduction.
          revert x e
          unfold Etingof.equivAt_eq_sink Etingof.reflFunctorMinus_mkQ
            Etingof.reflectionFunctorMinus
          simp only
          refine match inst_dec i i with
          | .isFalse h => absurd rfl h
          | .isTrue _ => ?_
          dsimp only [id]
          intro x e
          -- Now in .isTrue branch for inst_dec i i.
          -- equivAt_eq_sink → (quotEquivOfEq.trans quotKerEquivOfSurjective)
          -- reflFunctorMinus_mkQ → Submodule.mkQ
          -- All relevant reductions are definitional (quotEquivOfEq_mk is rfl,
          -- quotKerEquivOfSurjective_apply_mk is rfl, trans_apply is rfl).
          -- Try dsimp to reduce everything without needing instance synthesis.
          dsimp
          -- Goal: Φ(lof ⟨a,...⟩ v) = mapLinear(e)(equivAt_ne_plus(equivAt_ne_minus x))
          rw [DirectSum.toModule_lof]
          -- Goal should now be:
          -- Φ_component ⟨a,...⟩ (equivAt_ne_minus x) = mapLinear(e)(equivAt_ne_plus(equivAt_ne_minus x))
          -- i.e. (mapLinear(origArrow ...) ∘ equivAt_ne_plus)(equivAt_ne_minus x) = ...
          simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
          -- Goal: mapLinear(origArrow ⟨a, rev_arrow⟩)(...) = mapLinear(e)(...)
          -- Both sides apply to the same vector, just need arrow equality
          congr 1
          congr 1
          exact @Etingof.reversedArrow_ne_eq_eq_ne_twice Q inst_dec inst i hi a ha e
        · -- a ≠ i, b ≠ i: use API lemmas compositionally
          simp only [dif_neg ha, dif_neg hb, LinearEquiv.trans_apply]
          -- After trans_apply, goal has explicit composition of the two equivs
          -- Step 1: Use reflFunctorMinus_mapLinear_ne_ne to reduce through F⁻
          rw [@Etingof.reflFunctorMinus_mapLinear_ne_ne k _ Q _
            instR i hi' ρ_plus _ a b ha hb
            ((@Etingof.reversedAtVertex_twice Q _ inst i).symm ▸ e) x]
          -- Step 2: Use reflFunctorPlus_mapLinear_ne_ne to reduce through F⁺
          rw [@Etingof.reflFunctorPlus_mapLinear_ne_ne k _ Q _ inst i hi ρ a b ha hb]
          -- Step 3: Use reversedArrow_ne_ne_twice to close
          rw [@Etingof.reversedArrow_ne_ne_twice Q _ inst i a b ha hb e])
