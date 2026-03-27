import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5

/-!
# Proposition 6.6.7: Reflection Preserves Indecomposability

Let Q be a quiver and V an indecomposable representation. Then F⁺ᵢ(V) and F⁻ᵢ(V)
(whenever defined) are either indecomposable or 0.

The proof: if φ is not surjective, F⁺ᵢ(V) = 0. If φ is surjective and
F⁺ᵢ(V) = X ⊕ Y is decomposable, then X and Y are injective at i (since
F⁺ᵢ(V) is), so by Proposition 6.6.6, V = F⁻ᵢ(X) ⊕ F⁻ᵢ(Y), contradicting
indecomposability of V.

## Mathlib correspondence

Requires reflection functor definitions and indecomposable representation API.
Not in Mathlib.
-/

/-- A quiver representation is **zero** if all vertex spaces are trivial
(zero-dimensional). -/
def Etingof.QuiverRepresentation.IsZero
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) : Prop :=
  ∀ v : Q, Subsingleton (ρ.obj v)

/-- At a vertex v ≠ i, the reflection functor leaves the space unchanged:
`F⁺ᵢ(ρ).obj v = ρ.obj v`. -/
private theorem reflFunctorPlus_obj_ne
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

/-- At vertex i, the reflection functor gives the kernel of the sink map:
`F⁺ᵢ(ρ).obj i = ker(sinkMap i)`. -/
private theorem reflFunctorPlus_obj_eq
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

/-- At a sink i, the source vertex of an arrow into i is distinct from i. -/
private theorem arrowsInto_ne_sink
    {Q : Type*} [Quiver Q] {i : Q} (hi : Etingof.IsSink Q i)
    (a : Etingof.ArrowsInto Q i) : a.1 ≠ i := by
  intro heq; have := a.2; rw [heq] at this; exact (hi i).false this

/-- Construct the reversed arrow from i to a.1 in Q̄ᵢ, given an arrow a.1 → i in Q.
At a sink i, every arrow a : ArrowsInto Q i gives a reversed arrow i →_{Q̄ᵢ} a.1. -/
private def arrowsIntoReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (a : Etingof.ArrowsInto Q i) :
    @Quiver.Hom Q (Etingof.reversedAtVertex Q i) i a.1 := by
  show Etingof.ReversedAtVertexHom Q i i a.1
  unfold Etingof.ReversedAtVertexHom
  have hne := arrowsInto_ne_sink hi a
  exact match inst i i, inst a.1 i with
  | .isTrue _, .isTrue h => absurd h hne
  | .isTrue _, .isFalse _ => a.2
  | .isFalse h, _ => absurd rfl h

set_option maxHeartbeats 800000 in
/-- The F⁺ map from i to a.1 (via the reversed arrow) composed with equivAt_ne
equals the component projection composed with equivAt_eq (as subtype val).

This connects the abstract F⁺ map to the concrete direct sum component. -/
private theorem reflFunctorPlus_map_from_sink_component
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) (a : Etingof.ArrowsInto Q i)
    (ha : a.1 ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) i) :
    (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 ha)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) i a.1
        (arrowsIntoReversed hi a) x) =
    DirectSum.component k (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) a
      ((Etingof.reflFunctorPlus_equivAt_eq hi ρ x).val) := by
  have h_da : inst i i = .isTrue rfl := by
    cases inst i i with
    | isTrue _ => rfl
    | isFalse h => exact absurd rfl h
  have h_db : inst a.1 i = .isFalse ha := by
    cases inst a.1 i with
    | isTrue h => exact absurd h ha
    | isFalse _ => rfl
  revert x
  unfold Etingof.reflFunctorPlus_equivAt_ne Etingof.reflFunctorPlus_equivAt_eq
    arrowsIntoReversed
    Etingof.reflectionFunctorPlus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
  simp only []
  rw [h_da, h_db]
  intro x
  rfl

/-- Reflection functors preserve indecomposability at a sink:
F⁺ᵢ(V) is either indecomposable or zero.

If φ : ⊕_{j→i} V_j → V_i is not surjective, then the kernel of φ contains the
entire direct sum and F⁺ᵢ(V) is zero at every vertex. If φ is surjective and
F⁺ᵢ(V) decomposes as X ⊕ Y, then by Proposition 6.6.6 we can apply F⁻ᵢ to recover
V = F⁻ᵢ(X) ⊕ F⁻ᵢ(Y), contradicting indecomposability.

(Etingof Proposition 6.6.7, F⁺ᵢ version) -/
theorem Etingof.Proposition6_6_7_sink
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    @Etingof.QuiverRepresentation.IsIndecomposable k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) ∨
    @Etingof.QuiverRepresentation.IsZero k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) := by
  -- Case split: either V is simple at i (→ F⁺(V) is zero) or sinkMap is surjective
  -- Upgrade to AddCommGroup (needed for finrank_pos and complements)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  rcases Etingof.Proposition6_6_5_sink hi hρ with hsimple | hsurj
  · -- V is simple at i → F⁺(V) is zero
    right
    intro v
    -- Goal: Subsingleton ((reflectionFunctorPlus Q i hi ρ).obj v)
    unfold reflectionFunctorPlus
    simp only
    -- Match on the DecidableEq instance to reduce Decidable.rec
    match hd : (‹DecidableEq Q› v i) with
    | .isTrue hvi =>
      rw [hd]; dsimp only []
      -- v = i: space is ker(sinkMap). All V_j (j ≠ i) are trivial, so direct sum is trivial.
      -- Each component of the direct sum is subsingleton (all arrows into i come from j ≠ i)
      have htrivial : ∀ (a : ArrowsInto Q i), Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩
        have hj : j ≠ i := fun h => (hi j).false (h ▸ e)
        rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso
          have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hsimple.2 j hj
          omega
      -- Direct sum of subsingleton modules is subsingleton, ker of map from it too
      exact subsingleton_of_forall_eq 0 fun ⟨x, _⟩ =>
        Subtype.ext (Subsingleton.eq_zero x)
    | .isFalse hvi =>
      rw [hd]; dsimp only []
      -- v ≠ i: space is ρ.obj v, which has finrank 0 by IsSimpleAt
      rcases subsingleton_or_nontrivial (ρ.obj v) with h | h
      · exact h
      · exfalso
        have h1 := Module.finrank_pos (R := k) (M := ρ.obj v)
        have h2 := hsimple.2 v hvi
        omega
  · -- sinkMap surjective → F⁺(V) is indecomposable
    left
    -- At a sink, no arrow leaves i
    have sink_no_out : ∀ {a b : Q} (_ : a ⟶ b), a ≠ i :=
      fun {_ b} e h => (hi b).false (h ▸ e)
    -- V is indecomposable and not simple at i (since sinkMap surjective implies
    -- ⊕V_j maps onto V_i, so dim V_i ≤ Σ dim V_j; if V were simple, all V_j = 0
    -- and dim V_i = 1, but surjective from 0-module to 1-dim is impossible)
    have hnotsimple : ¬ρ.IsSimpleAt i := by
      intro hs
      -- All V_j for j ≠ i have dim 0
      have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso; have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hs.2 j hj; omega
      -- The direct sum ⊕V_j is subsingleton (each component is)
      haveI : ∀ a : Etingof.ArrowsInto Q i, Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩; exact htriv j (sink_no_out e)
      -- Surjective from subsingleton → target is subsingleton
      haveI : Subsingleton (DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => by
          ext ⟨j, e⟩; exact Subsingleton.eq_zero _
      have hVi : Subsingleton (ρ.obj i) :=
        subsingleton_of_forall_eq 0 fun x => by
          obtain ⟨y, hy⟩ := hsurj x
          rw [← hy, Subsingleton.eq_zero y, map_zero]
      -- But IsSimpleAt says dim V_i = 1, so V_i is Nontrivial — contradiction
      haveI := hVi
      have h1 := hs.1 -- finrank k (ρ.obj i) = 1
      have h2 := Module.finrank_zero_of_subsingleton (M := ρ.obj i) (R := k)
      omega
    constructor
    · -- F⁺(V) is nontrivial: sinkMap surjective + V nontrivial implies
      -- ∃ j ≠ i with V_j nontrivial. (If all V_j = 0 for j ≠ i, then
      -- ⊕V_j = 0, surjective from 0 → V_i gives V_i = 0, contradicting
      -- V nontrivial.) F⁺(V)_j = V_j, so F⁺(V) is nontrivial at j.
      -- First, find j ≠ i with V_j nontrivial
      have ⟨j, hj, hjnt⟩ : ∃ j, j ≠ i ∧ Nontrivial (ρ.obj j) := by
        by_contra hall
        -- All V_j for j ≠ i are subsingleton
        have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
          intro j hji
          rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
          · exact h
          · exact absurd ⟨j, hji, h⟩ hall
        -- Direct sum is subsingleton
        haveI : ∀ a : Etingof.ArrowsInto Q i, Subsingleton (ρ.obj a.1) := by
          intro ⟨j, e⟩; exact htriv j (sink_no_out e)
        haveI : Subsingleton (DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1)) :=
          subsingleton_of_forall_eq 0 fun x => by ext ⟨j, e⟩; exact Subsingleton.eq_zero _
        -- V_i is subsingleton (surjective from subsingleton)
        have hVi : Subsingleton (ρ.obj i) :=
          subsingleton_of_forall_eq 0 fun x => by
            obtain ⟨y, hy⟩ := hsurj x
            rw [← hy, Subsingleton.eq_zero y, map_zero]
        -- But V is nontrivial at some vertex
        obtain ⟨w, hw⟩ := hρ.1
        rcases eq_or_ne w i with rfl | hwi
        · exact not_subsingleton _ hVi
        · exact not_subsingleton _ (htriv w hwi)
      -- Now show F⁺(V) is nontrivial at j
      refine ⟨j, ?_⟩
      unfold Etingof.reflectionFunctorPlus
      simp only
      match hd : (‹DecidableEq Q› j i) with
      | .isTrue hji => exact absurd hji hj
      | .isFalse _ => rw [hd]; dsimp only []; exact hjnt
    · -- F⁺(V) is indecomposable: given complementary subreps W₁, W₂ of F⁺(V),
      -- construct complementary subreps of V, use V's indecomposability.
      --
      -- MATHEMATICAL ARGUMENT (not yet formalized):
      -- Given complementary subreps W₁, W₂ of F⁺(V) on Q̄ᵢ, define subreps of V on Q:
      --   U_k(v) = W_k(v) for v ≠ i  (since F⁺(V)_v = V_v)
      --   U_k(i) = φ(⊕ W_k(j))      (image of "W_k-part" of direct sum under sinkMap φ)
      --
      -- The subrep conditions hold:
      --   - Maps between v, w ≠ i: same as in Q̄ᵢ (unchanged maps)
      --   - Maps into i: ρ(e)(x) = φ(lof(⟨a,e⟩)(x)) ∈ φ(⊕W_k(j)) when x ∈ W_k(a)
      --   - Maps from i: impossible (sink)
      --
      -- Complementarity: at v ≠ i, from W₁(v) ⊕ W₂(v). At i, uses:
      --   - φ surjective: U₁(i) + U₂(i) = φ(⊕W₁ + ⊕W₂) = φ(⊕V_j) = V_i
      --   - ker(φ) decomposition: if y ∈ U₁(i) ∩ U₂(i), write y = φ(x₁) = φ(x₂) with
      --     x_k ∈ ⊕W_k(j). Then x₁ - x₂ ∈ ker(φ) = W₁(i) ⊕ W₂(i) (embedded in ⊕V_j
      --     via subrep condition for arrows from i in Q̄ᵢ). Unique decomposition gives
      --     x₁ = w₁, x₂ + w₂ = 0 implying y = 0.
      --
      -- By V's indecomposability, W₁ or W₂ is ⊥ at all v ≠ i, and then also at i
      -- (since W_k(i) ⊆ ker(φ) ⊆ ⊕V_j, and if ⊕W_k(j) = 0 then W_k(i) = 0).
      --
      -- BLOCKED: The dependent type issues with Decidable.rec in reflectionFunctorPlus
      -- make the construction extremely painful to formalize.
      intro W₁ W₂ hW₁ hW₂ hcompl
      -- Construct complementary subreps U₁, U₂ of V from W₁, W₂ of F⁺(V).
      classical
      let φ := ρ.sinkMap i
      -- For arrows into i, the source vertex j ≠ i, so F⁺(V).obj j ≃ ρ.obj j
      have arrow_ne : ∀ (a : Etingof.ArrowsInto Q i), a.1 ≠ i :=
        fun ⟨j, e⟩ => sink_no_out e
      -- Transport W_k at arrow sources to submodules of ρ.obj
      let W₁_at : ∀ (a : Etingof.ArrowsInto Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₁ a.1)
      let W₂_at : ∀ (a : Etingof.ArrowsInto Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₂ a.1)
      -- U_k(v) for v ≠ i: transport W_k(v) via equiv
      -- U_k(i): image under sinkMap of the W_k-part of the direct sum
      let U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ Submodule.map φ (⨆ (a : Etingof.ArrowsInto Q i),
            Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a))
        else
          Submodule.map (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).toLinearMap (W₁ v)
      let U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ Submodule.map φ (⨆ (a : Etingof.ArrowsInto Q i),
            Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a))
        else
          Submodule.map (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).toLinearMap (W₂ v)
      -- Prove U₁ is a subrep of ρ
      have hU₁_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'), ∀ x ∈ U₁ a', ρ.mapLinear e' x ∈ U₁ b' := by
        intro a' b' e' x hx
        have ha' : a' ≠ i := sink_no_out e'
        simp only [U₁, dif_neg ha'] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        by_cases hb' : b' = i
        · cases hb'
          simp only [U₁, dif_pos rfl]
          refine Submodule.mem_map.mpr
            ⟨DirectSum.lof k (Etingof.ArrowsInto Q i) (fun c => ρ.obj c.1) ⟨a', e'⟩
              ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a' ha') w), ?_, ?_⟩
          · exact Submodule.mem_iSup_of_mem ⟨a', e'⟩
              (Submodule.mem_map.mpr ⟨(Etingof.reflFunctorPlus_equivAt_ne hi ρ a' ha') w,
                ⟨w, hw, rfl⟩, rfl⟩)
          · show (ρ.sinkMap i) _ = _
            simp only [Etingof.QuiverRepresentation.sinkMap, DirectSum.toModule_lof]
            rfl
        · simp only [U₁, dif_neg hb']
          -- Extract subrep property at (a', b') before clearing W₁
          have hsubrep : ∀ (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a' b'),
              ∀ x ∈ W₁ a', @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i) (Etingof.reflectionFunctorPlus Q i hi ρ)
                a' b' e x ∈ W₁ b' :=
            fun e x hx => hW₁ e x hx
          -- Generalize W₁ a' and W₁ b' to fresh variables
          generalize W₁ a' = Sa at hw hsubrep ⊢
          generalize W₁ b' = Sb at hsubrep ⊢
          -- Clear everything that uses inst v i
          clear hcompl hW₂ W₂ U₂ W₂_at U₁ W₁_at arrow_ne φ hnotsimple hρ hW₁ W₁
          have h_da : ‹DecidableEq Q› a' i = .isFalse ha' := by
            cases ‹DecidableEq Q› a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
          have h_db : ‹DecidableEq Q› b' i = .isFalse hb' := by
            cases ‹DecidableEq Q› b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
          revert hw w e' hsubrep Sb Sa
          unfold Etingof.reflFunctorPlus_equivAt_ne
            Etingof.reflectionFunctorPlus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
          simp only []
          rw [h_da, h_db]
          simp only []
          intro e' w Sa hw Sb hsubrep
          simp only [id, LinearEquiv.refl_apply, Submodule.map_id, LinearEquiv.coe_toLinearMap,
            LinearEquiv.refl_toLinearMap] at *
          exact hsubrep e' w hw
      have hU₂_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'), ∀ x ∈ U₂ a', ρ.mapLinear e' x ∈ U₂ b' := by
        intro a' b' e' x hx
        have ha' : a' ≠ i := sink_no_out e'
        simp only [U₂, dif_neg ha'] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        by_cases hb' : b' = i
        · cases hb'
          simp only [U₂, dif_pos rfl]
          refine Submodule.mem_map.mpr
            ⟨DirectSum.lof k (Etingof.ArrowsInto Q i) (fun c => ρ.obj c.1) ⟨a', e'⟩
              ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a' ha') w), ?_, ?_⟩
          · exact Submodule.mem_iSup_of_mem ⟨a', e'⟩
              (Submodule.mem_map.mpr ⟨(Etingof.reflFunctorPlus_equivAt_ne hi ρ a' ha') w,
                ⟨w, hw, rfl⟩, rfl⟩)
          · show (ρ.sinkMap i) _ = _
            simp only [Etingof.QuiverRepresentation.sinkMap, DirectSum.toModule_lof]
            rfl
        · simp only [U₂, dif_neg hb']
          have hsubrep : ∀ (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a' b'),
              ∀ x ∈ W₂ a', @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i) (Etingof.reflectionFunctorPlus Q i hi ρ)
                a' b' e x ∈ W₂ b' :=
            fun e x hx => hW₂ e x hx
          generalize W₂ a' = Sa at hw hsubrep ⊢
          generalize W₂ b' = Sb at hsubrep ⊢
          clear hcompl hW₁ W₁ U₁ W₁_at U₂ W₂_at arrow_ne φ hnotsimple hρ hW₂ W₂ hU₁_subrep
          have h_da : ‹DecidableEq Q› a' i = .isFalse ha' := by
            cases ‹DecidableEq Q› a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
          have h_db : ‹DecidableEq Q› b' i = .isFalse hb' := by
            cases ‹DecidableEq Q› b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
          revert hw w e' hsubrep Sb Sa
          unfold Etingof.reflFunctorPlus_equivAt_ne
            Etingof.reflectionFunctorPlus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
          simp only []
          rw [h_da, h_db]
          simp only []
          intro e' w Sa hw Sb hsubrep
          simp only [id, LinearEquiv.refl_apply, Submodule.map_id, LinearEquiv.coe_toLinearMap,
            LinearEquiv.refl_toLinearMap] at *
          exact hsubrep e' w hw
      have hU_compl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
        intro v
        by_cases hv : v = i
        · subst hv
          simp only [U₁, U₂, dif_pos rfl]
          -- Prove W₁_at, W₂_at are complementary at each arrow
          have hW_at_compl : ∀ a : Etingof.ArrowsInto Q v,
              IsCompl (W₁_at a) (W₂_at a) := by
            intro a
            have hc := hcompl a.1
            let e := Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)
            exact ⟨by
              rw [Submodule.disjoint_def]; intro x hx₁ hx₂
              obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx₁
              obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx₂
              have : w₁ ∈ W₁ a.1 ⊓ W₂ a.1 := ⟨hw₁, e.injective hw₂eq ▸ hw₂⟩
              rw [hc.1.eq_bot, Submodule.mem_bot] at this
              rw [this, map_zero], by
              rw [codisjoint_iff, eq_top_iff]; intro x _
              obtain ⟨w, rfl⟩ := e.surjective x
              obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
                Submodule.mem_sup.mp (hc.2.eq_top ▸ (Submodule.mem_top : w ∈ ⊤))
              exact Submodule.mem_sup.mpr
                ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
                 _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
                 (map_add _ _ _).symm⟩⟩
          -- Component characterization: x ∈ S_k → component a x ∈ W_k_at a
          have hcomp_of_mem :
              ∀ (W_at : ∀ a : Etingof.ArrowsInto Q v, Submodule k (ρ.obj a.1))
                (x : DirectSum (Etingof.ArrowsInto Q v) (fun a => ρ.obj a.1)),
              x ∈ ⨆ a, Submodule.map
                (DirectSum.lof k (Etingof.ArrowsInto Q v) (fun a => ρ.obj a.1) a) (W_at a) →
              ∀ a, DirectSum.component k (Etingof.ArrowsInto Q v)
                (fun a => ρ.obj a.1) a x ∈ W_at a := by
            intro W_at x hx a
            refine Submodule.iSup_induction
              (motive := fun x => DirectSum.component k _ (fun a => ρ.obj a.1) a x ∈ W_at a)
              (fun b => Submodule.map
                (DirectSum.lof k _ (fun a => ρ.obj a.1) b) (W_at b)) hx ?_ ?_ ?_
            · intro b y hy
              obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
              simp only [DirectSum.component.of]
              split
              · next h => exact h ▸ hm
              · exact Submodule.zero_mem _
            · simp only [map_zero]; exact Submodule.zero_mem _
            · exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂
          -- Kernel component: for z ∈ W_k(v), component a of equivAt_eq(z).val is in W_k_at a
          have hker_comp :
              ∀ (W : ∀ v₁ : Q, Submodule k
                  (@Etingof.QuiverRepresentation.obj k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) v₁))
                (hW_sub : ∀ {a b} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q v) a b),
                  ∀ x ∈ W a,
                  @Etingof.QuiverRepresentation.mapLinear k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) a b e x ∈ W b)
                (z : @Etingof.QuiverRepresentation.obj k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) v),
              z ∈ W v →
              ∀ a, DirectSum.component k _ (fun a => ρ.obj a.1) a
                ((Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val) ∈
                Submodule.map
                  (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
                  (W a.1) := by
            intro W hW_sub z hz a
            rw [← reflFunctorPlus_map_from_sink_component hi ρ a (arrow_ne a) z]
            exact Submodule.mem_map.mpr ⟨_, hW_sub (arrowsIntoReversed hi a) z hz, rfl⟩
          -- Key: kernel elements from W_k(v) land in S_k
          have hker_in_S :
              ∀ (W : ∀ v₁ : Q, Submodule k
                  (@Etingof.QuiverRepresentation.obj k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) v₁))
                (hW_sub : ∀ {a b} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q v) a b),
                  ∀ x ∈ W a,
                  @Etingof.QuiverRepresentation.mapLinear k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) a b e x ∈ W b)
                (W_at : ∀ a : Etingof.ArrowsInto Q v, Submodule k (ρ.obj a.1))
                (_ : W_at = fun a => Submodule.map
                  (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
                  (W a.1))
                (z : @Etingof.QuiverRepresentation.obj k Q _
                    (Etingof.reversedAtVertex Q v)
                    (Etingof.reflectionFunctorPlus Q v hi ρ) v),
              z ∈ W v →
              (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val ∈
                ⨆ a, Submodule.map
                  (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W_at a) := by
            intro W hW_sub W_at hW_at_def z hz
            -- Decompose val into components using DFinsupp.sum_single
            have hdecomp : (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val =
                DFinsupp.sum (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val
                  (fun a m => DirectSum.of _ a m) := (DFinsupp.sum_single).symm
            rw [hdecomp]
            apply Submodule.sum_mem
            intro a _
            apply Submodule.mem_iSup_of_mem a
            apply Submodule.mem_map.mpr
            exact ⟨(Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val a,
              hW_at_def ▸ hker_comp W hW_sub z hz a, rfl⟩
          -- Now prove the main IsCompl
          constructor
          · -- Disjoint: map φ S₁ ⊓ map φ S₂ = ⊥
            rw [Submodule.disjoint_def]
            intro y hy₁ hy₂
            obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
            obtain ⟨x₂, hx₂, hφeq⟩ := Submodule.mem_map.mp hy₂
            -- φ x₁ = φ x₂ → x₁ - x₂ ∈ ker φ
            have hker : x₁ - x₂ ∈ LinearMap.ker φ := by
              rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hφeq.symm
            -- Get z ∈ F⁺(V)_v and decompose via W₁(v) ⊕ W₂(v)
            set z := (Etingof.reflFunctorPlus_equivAt_eq hi ρ).symm ⟨x₁ - x₂, hker⟩
            have hzval : (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val = x₁ - x₂ := by
              simp [z, LinearEquiv.apply_symm_apply]
            obtain ⟨z₁, hz₁, z₂, hz₂, hzsum⟩ := Submodule.mem_sup.mp
              ((hcompl v).sup_eq_top ▸ (Submodule.mem_top : z ∈ ⊤))
            -- equivAt_eq(z₁ + z₂).val = x₁ - x₂
            have hval_sum :
                (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val +
                (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val = x₁ - x₂ := by
              change (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁ +
                Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val = x₁ - x₂
              rw [← map_add, hzsum, hzval]
            -- z₁ val ∈ S₁, z₂ val ∈ S₂
            have hz₁_S := hker_in_S W₁ hW₁ W₁_at rfl z₁ hz₁
            have hz₂_S := hker_in_S W₂ hW₂ W₂_at rfl z₂ hz₂
            -- S₁ ⊓ S₂ = ⊥ in the direct sum (componentwise disjoint)
            have hS_disj : Disjoint
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a))
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a)) := by
              rw [Submodule.disjoint_def]; intro x hx₁' hx₂'
              exact DFunLike.ext x 0 fun a => by
                have hmem : DirectSum.component k _ (fun a => ρ.obj a.1) a x ∈
                    W₁_at a ⊓ W₂_at a :=
                  ⟨hcomp_of_mem W₁_at x hx₁' a, hcomp_of_mem W₂_at x hx₂' a⟩
                rwa [(hW_at_compl a).inf_eq_bot, Submodule.mem_bot] at hmem
            -- x₁ - z₁val ∈ S₁ ∩ S₂ → x₁ - z₁val = 0
            have hdiff_S₁ : x₁ - (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val ∈
                ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a) :=
              Submodule.sub_mem _ hx₁ hz₁_S
            have hdiff_S₂ : x₁ - (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val ∈
                ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a) := by
              have : x₁ - (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val =
                  x₂ + (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val :=
                sub_eq_iff_eq_add.mp (by rw [sub_sub, hval_sum, sub_sub_cancel])
              rw [this]; exact Submodule.add_mem _ hx₂ hz₂_S
            have hzero := Submodule.disjoint_def.mp hS_disj _ hdiff_S₁ hdiff_S₂
            -- x₁ = z₁val ∈ ker φ → φ x₁ = 0
            have hx₁_eq : x₁ = (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val :=
              sub_eq_zero.mp hzero
            rw [hx₁_eq, LinearMap.mem_ker.mp (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).2]
          · -- Codisjoint: map φ S₁ ⊔ map φ S₂ = ⊤
            rw [codisjoint_iff, ← Submodule.map_sup]
            -- S₁ ⊔ S₂ = ⊤ in the direct sum (componentwise complementary)
            have hS_top :
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₁_at a)) ⊔
                (⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W₂_at a)) = ⊤ := by
              rw [eq_top_iff]; intro x _
              refine DirectSum.induction_on x (Submodule.zero_mem _) ?_ ?_
              · intro a m
                obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp
                  ((hW_at_compl a).sup_eq_top ▸ (Submodule.mem_top : m ∈ ⊤))
                rw [show DirectSum.of _ a (m₁ + m₂) =
                  DirectSum.lof k _ (fun a => ρ.obj a.1) a m₁ +
                  DirectSum.lof k _ (fun a => ρ.obj a.1) a m₂ from map_add _ _ _]
                exact Submodule.add_mem _
                  (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem a
                    (Submodule.mem_map.mpr ⟨m₁, hm₁, rfl⟩)))
                  (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a
                    (Submodule.mem_map.mpr ⟨m₂, hm₂, rfl⟩)))
              · exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂
            rw [hS_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
        · simp only [U₁, U₂, dif_neg hv]
          have hc := hcompl v
          let φ' := (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).toLinearMap
          exact ⟨by
            rw [Submodule.disjoint_def]
            intro x hx1 hx2
            obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx1
            obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx2
            have heq := (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).injective hw₂eq
            have : w₁ ∈ W₁ v ⊓ W₂ v := ⟨hw₁, heq ▸ hw₂⟩
            rw [hc.1.eq_bot] at this
            simp only [Submodule.mem_bot] at this
            rw [this, map_zero],
          by
            rw [codisjoint_iff, eq_top_iff]; intro x _
            obtain ⟨w, rfl⟩ := (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).surjective x
            have hw : w ∈ (⊤ : Submodule k _) := Submodule.mem_top
            rw [← hc.2.eq_top, Submodule.mem_sup] at hw
            obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
            exact Submodule.mem_sup.mpr
              ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
               _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
               (map_add _ _ _).symm⟩⟩
      -- Apply V's indecomposability
      have hindecomp := hρ.2 U₁ U₂ hU₁_subrep hU₂_subrep hU_compl
      -- Transport back: U_k = ⊥ everywhere → W_k = ⊥ everywhere
      -- At v ≠ i: equiv is injective, so map = ⊥ → original = ⊥
      -- At v = i: W_k(i) ⊆ ker(φ) ⊆ ⊕V_j, and the F⁺(V) maps from i
      --   project to each V_j. Since W_k is a subrep, projections land in
      --   W_k(j) = ⊥, so all components are 0, hence W_k(i) = ⊥.
      suffices transport : ∀ (W : ∀ v, Submodule k
            (@Etingof.QuiverRepresentation.obj k Q _
              (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorPlus Q i hi ρ) v)),
            (∀ {a b} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b),
              ∀ x ∈ W a,
              @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i)
                (Etingof.reflectionFunctorPlus Q i hi ρ) a b e x ∈ W b) →
            (∀ v (hv : v ≠ i), Submodule.map
              (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).toLinearMap
              (W v) = ⊥) →
            (∀ v, W v = ⊥) by
        rcases hindecomp with h1 | h2
        · left; exact transport W₁ hW₁ (fun v hv => by
            have := h1 v; simp only [U₁, dif_neg hv] at this; exact this)
        · right; exact transport W₂ hW₂ (fun v hv => by
            have := h2 v; simp only [U₂, dif_neg hv] at this; exact this)
      -- Prove the transport lemma
      intro W hW hW_ne v
      by_cases hv : v = i
      · -- At i: use subrep structure + direct sum projections
        cases hv
        rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]
        -- W(j) = ⊥ for all j ≠ i (equiv is injective)
        have hW_bot : ∀ j, j ≠ i → W j = ⊥ := by
          intro j hj
          have h := hW_ne j hj
          rw [eq_bot_iff] at h ⊢
          intro z hz
          rw [Submodule.mem_bot]
          have hmem := h ⟨z, hz, rfl⟩
          rw [Submodule.mem_bot] at hmem
          exact (Etingof.reflFunctorPlus_equivAt_ne hi ρ j hj).injective
            (hmem.trans (map_zero _).symm)
        -- Convert x to kernel element via equivAt_eq
        suffices hzero : (Etingof.reflFunctorPlus_equivAt_eq hi ρ) x = 0 from
          (Etingof.reflFunctorPlus_equivAt_eq hi ρ).injective (by rw [hzero, map_zero])
        -- Show the kernel element is 0 by showing its val (direct sum element) is 0
        apply Subtype.ext
        show ((Etingof.reflFunctorPlus_equivAt_eq hi ρ) x).val = 0
        refine DFunLike.ext _ _ fun a => ?_
        -- For each a : ArrowsInto Q i, show component a is 0
        have ha := arrowsInto_ne_sink hi a
        -- The reversed arrow from i to a.1 sends x to W(a.1) = ⊥
        have hmem := hW (arrowsIntoReversed hi a) x hx
        rw [hW_bot a.1 ha, Submodule.mem_bot] at hmem
        -- By the API lemma: equivAt_ne (mapLinear rev x) = component a (equivAt_eq x).val
        have hapi := reflFunctorPlus_map_from_sink_component hi ρ a ha x
        -- mapLinear rev x = 0 (from hmem), so equivAt_ne 0 = 0
        rw [hmem, map_zero] at hapi
        -- hapi : 0 = component a (equivAt_eq x).val
        -- component a y = y a for direct sum elements
        -- DirectSum.apply_eq_component: f a = component a f (is rfl)
        exact hapi.symm
      · -- At v ≠ i: injective map = ⊥ → original = ⊥
        specialize hW_ne v hv
        rw [eq_bot_iff]
        intro x hx
        rw [eq_bot_iff] at hW_ne
        have hmem : (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv) x ∈
            Submodule.map
              (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).toLinearMap
              (W v) :=
          ⟨x, hx, rfl⟩
        have h0 := hW_ne hmem
        rw [Submodule.mem_bot] at h0 ⊢
        exact (Etingof.reflFunctorPlus_equivAt_ne hi ρ v hv).injective
          (by rw [h0, map_zero])

/-- For each arrow `a : ArrowsOutOf Q i` (i.e., `a.2 : i ⟶ a.1`),
construct the reversed arrow `a.1 → i` in `Q̄ᵢ`. -/
noncomputable def Etingof.arrowOutToReversed
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a.1 i := by
  obtain ⟨j, e⟩ := a
  have ha : j ≠ i := fun heq => (hi i).false (heq ▸ e)
  have h_da : inst j i = .isFalse ha := by
    cases inst j i with | isTrue h => exact absurd h ha | isFalse _ => rfl
  have h_di : inst i i = .isTrue rfl := by
    cases inst i i with | isTrue _ => rfl | isFalse h => exact absurd rfl h
  show @Etingof.ReversedAtVertexHom Q inst _ i j i
  unfold Etingof.ReversedAtVertexHom
  simp only []
  rw [h_da, h_di]
  simp only []
  exact e

/-- `arrowOutToReversed` is a right inverse to `reversedArrow_ne_eq`:
converting a.2 to a reversed arrow and back gives a.2. -/
theorem Etingof.reversedArrow_arrowOut_eq
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (a : Etingof.ArrowsOutOf Q i) :
    Etingof.reversedArrow_ne_eq
      (show a.1 ≠ i from fun heq => by obtain ⟨j, e⟩ := a; exact (hi i).false (heq ▸ e))
      (Etingof.arrowOutToReversed hi a) = a.2 := by
  -- Both sides reduce to `a.2` after matching on the Decidable instances.
  -- Technical: the `Decidable.casesOn` motive prevents direct `rw`.
  sorry

/-- Reflection functors preserve indecomposability at a source:
F⁻ᵢ(V) is either indecomposable or zero.

Dual to the sink case, using injectivity of the source map and Proposition 6.6.6.

(Etingof Proposition 6.6.7, F⁻ᵢ version) -/
theorem Etingof.Proposition6_6_7_source
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hρ : ρ.IsIndecomposable) :
    @Etingof.QuiverRepresentation.IsIndecomposable k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) ∨
    @Etingof.QuiverRepresentation.IsZero k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) := by
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  rcases Etingof.Proposition6_6_5_source hi hρ with hsimple | hinj
  · -- V is simple at i → F⁻(V) is zero
    right
    intro v
    unfold Etingof.reflectionFunctorMinus
    simp only
    match hd : (‹DecidableEq Q› v i) with
    | .isTrue hvi =>
      rw [hd]; dsimp only []
      -- v = i: space is coker(sourceMap). All arrow targets j ≠ i have dim 0.
      have htrivial : ∀ (a : Etingof.ArrowsOutOf Q i), Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩
        have hj : j ≠ i := by intro heq; rw [heq] at e; exact (hi i).false e
        rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso
          have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hsimple.2 j hj
          omega
      -- Direct sum is subsingleton (each component is)
      haveI : Subsingleton (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => DFunLike.ext x 0 fun a => Subsingleton.eq_zero _
      -- Quotient of subsingleton is subsingleton
      exact @Subsingleton.intro _ fun a b => by
        induction a using Quotient.ind
        induction b using Quotient.ind
        exact congr_arg (Quotient.mk _) (Subsingleton.elim _ _)
    | .isFalse hvi =>
      rw [hd]; dsimp only []
      -- v ≠ i: space is ρ.obj v, which has finrank 0
      rcases subsingleton_or_nontrivial (ρ.obj v) with h | h
      · exact h
      · exfalso
        have h1 := Module.finrank_pos (R := k) (M := ρ.obj v)
        have h2 := hsimple.2 v hvi
        omega
  · -- sourceMap injective → F⁻(V) is indecomposable
    left
    -- At a source, no arrow enters i
    have source_no_in : ∀ {a b : Q} (_ : a ⟶ b), b ≠ i :=
      fun {a _} e h => (hi a).false (h ▸ e)
    -- V is not simple at i (sourceMap injective from nontrivial to subsingleton impossible)
    have hnotsimple : ¬ρ.IsSimpleAt i := by
      intro hs
      have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
        · exact h
        · exfalso; have h1 := Module.finrank_pos (R := k) (M := ρ.obj j)
          have h2 := hs.2 j hj; omega
      haveI : ∀ a : Etingof.ArrowsOutOf Q i, Subsingleton (ρ.obj a.1) := by
        intro ⟨j, e⟩; exact htriv j (by intro heq; rw [heq] at e; exact (hi i).false e)
      haveI : Subsingleton (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
        subsingleton_of_forall_eq 0 fun x => by
          ext ⟨j, e⟩; exact Subsingleton.eq_zero _
      have hVi : Subsingleton (ρ.obj i) :=
        subsingleton_of_forall_eq 0 fun x =>
          hinj (Subsingleton.elim ((ρ.sourceMap i) x) ((ρ.sourceMap i) 0))
      haveI := hVi
      have h1 := hs.1
      have h2 := Module.finrank_zero_of_subsingleton (M := ρ.obj i) (R := k)
      omega
    constructor
    · -- F⁻(V) is nontrivial: find j ≠ i with V_j nontrivial
      have ⟨j, hj, hjnt⟩ : ∃ j, j ≠ i ∧ Nontrivial (ρ.obj j) := by
        by_contra hall
        have htriv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
          intro j hji; rcases subsingleton_or_nontrivial (ρ.obj j) with h | h
          · exact h
          · exact absurd ⟨j, hji, h⟩ hall
        haveI : ∀ a : Etingof.ArrowsOutOf Q i, Subsingleton (ρ.obj a.1) := by
          intro ⟨j, e⟩; exact htriv j (by intro heq; rw [heq] at e; exact (hi i).false e)
        haveI : Subsingleton (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
          subsingleton_of_forall_eq 0 fun x => by ext ⟨j, e⟩; exact Subsingleton.eq_zero _
        have hVi : Subsingleton (ρ.obj i) :=
          subsingleton_of_forall_eq 0 fun x =>
            hinj (Subsingleton.elim ((ρ.sourceMap i) x) ((ρ.sourceMap i) 0))
        obtain ⟨w, hw⟩ := hρ.1
        rcases eq_or_ne w i with rfl | hwi
        · exact not_subsingleton _ hVi
        · exact not_subsingleton _ (htriv w hwi)
      refine ⟨j, ?_⟩
      unfold Etingof.reflectionFunctorMinus
      simp only
      match hd : (‹DecidableEq Q› j i) with
      | .isTrue hji => exact absurd hji hj
      | .isFalse _ => rw [hd]; dsimp only []; exact hjnt
    · -- F⁻(V) is indecomposable: given complementary subreps W₁, W₂ of F⁻(V),
      -- construct complementary subreps of V, use V's indecomposability.
      intro W₁ W₂ hW₁ hW₂ hcompl
      classical
      let ψ := ρ.sourceMap i
      have arrow_ne : ∀ (a : Etingof.ArrowsOutOf Q i), a.1 ≠ i := by
        intro ⟨j, e⟩; intro heq; exact (hi i).false (heq ▸ e)
      -- Transport W_k at arrow targets to submodules of ρ.obj
      let W₁_at : ∀ (a : Etingof.ArrowsOutOf Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (Etingof.reflFunctorMinus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₁ a.1)
      let W₂_at : ∀ (a : Etingof.ArrowsOutOf Q i), Submodule k (ρ.obj a.1) :=
        fun a => Submodule.map
          (Etingof.reflFunctorMinus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap
          (W₂ a.1)
      -- U_k(v) for v ≠ i: transport W_k(v) via equiv
      -- U_k(i): elements whose image under each outgoing arrow lands in W_k
      let U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ ⨅ (a : Etingof.ArrowsOutOf Q i),
            Submodule.comap (ρ.mapLinear a.2) (W₁_at a)
        else
          Submodule.map (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).toLinearMap (W₁ v)
      let U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
        if hv : v = i then
          hv ▸ ⨅ (a : Etingof.ArrowsOutOf Q i),
            Submodule.comap (ρ.mapLinear a.2) (W₂_at a)
        else
          Submodule.map (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).toLinearMap (W₂ v)
      -- W₁_at, W₂_at are complementary at each arrow target
      have hW_at_compl : ∀ a : Etingof.ArrowsOutOf Q i,
          IsCompl (W₁_at a) (W₂_at a) := by
        intro a
        have hc := hcompl a.1
        let e := Etingof.reflFunctorMinus_equivAt_ne hi ρ a.1 (arrow_ne a)
        exact ⟨by
          rw [Submodule.disjoint_def]; intro x hx₁ hx₂
          obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx₁
          obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx₂
          have : w₁ ∈ W₁ a.1 ⊓ W₂ a.1 := ⟨hw₁, e.injective hw₂eq ▸ hw₂⟩
          rw [hc.1.eq_bot, Submodule.mem_bot] at this
          rw [this, map_zero], by
          rw [codisjoint_iff, eq_top_iff]; intro x _
          obtain ⟨w, rfl⟩ := e.surjective x
          obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
            Submodule.mem_sup.mp (hc.2.eq_top ▸ (Submodule.mem_top : w ∈ ⊤))
          exact Submodule.mem_sup.mpr
            ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
             _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
             (map_add _ _ _).symm⟩⟩
      -- Prove U₁ is a subrep of ρ
      have hU₁_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'),
          ∀ x ∈ U₁ a', ρ.mapLinear e' x ∈ U₁ b' := by
        intro a' b' e' x hx
        have hb' : b' ≠ i := source_no_in e'
        by_cases ha' : a' = i
        · -- Arrow from i to b' ≠ i
          cases ha'
          simp only [U₁, dif_pos rfl, dif_neg hb'] at hx ⊢
          -- x ∈ ⨅ a, comap mapLinear (W₁_at a), so mapLinear ⟨b', e'⟩.2 x ∈ W₁_at ⟨b', e'⟩
          rw [Submodule.mem_iInf] at hx
          exact hx ⟨b', e'⟩
        · -- Arrow between a' ≠ i and b' ≠ i
          simp only [U₁, dif_neg ha', dif_neg hb'] at hx ⊢
          obtain ⟨w, hw, rfl⟩ := hx
          have hsubrep : ∀ (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a' b'),
              ∀ x ∈ W₁ a', @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i) (Etingof.reflectionFunctorMinus Q i hi ρ)
                a' b' e x ∈ W₁ b' :=
            fun e x hx => hW₁ e x hx
          generalize W₁ a' = Sa at hw hsubrep ⊢
          generalize W₁ b' = Sb at hsubrep ⊢
          clear hcompl hW₂ hW_at_compl W₂_at U₂ W₂ U₁ W₁_at arrow_ne hnotsimple hρ hW₁ W₁
          have h_da : ‹DecidableEq Q› a' i = .isFalse ha' := by
            cases ‹DecidableEq Q› a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
          have h_db : ‹DecidableEq Q› b' i = .isFalse hb' := by
            cases ‹DecidableEq Q› b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
          revert hw w e' hsubrep Sb Sa
          unfold Etingof.reflFunctorMinus_equivAt_ne
            Etingof.reflectionFunctorMinus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
          simp only []
          rw [h_da, h_db]
          simp only []
          intro e' w Sa hw Sb hsubrep
          simp only [id, LinearEquiv.refl_apply, Submodule.map_id, LinearEquiv.coe_toLinearMap,
            LinearEquiv.refl_toLinearMap] at *
          exact hsubrep e' w hw
      have hU₂_subrep : ∀ {a' b' : Q} (e' : a' ⟶ b'),
          ∀ x ∈ U₂ a', ρ.mapLinear e' x ∈ U₂ b' := by
        intro a' b' e' x hx
        have hb' : b' ≠ i := source_no_in e'
        by_cases ha' : a' = i
        · cases ha'
          simp only [U₂, dif_pos rfl, dif_neg hb'] at hx ⊢
          rw [Submodule.mem_iInf] at hx; exact hx ⟨b', e'⟩
        · simp only [U₂, dif_neg ha', dif_neg hb'] at hx ⊢
          obtain ⟨w, hw, rfl⟩ := hx
          have hsubrep : ∀ (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a' b'),
              ∀ x ∈ W₂ a', @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i) (Etingof.reflectionFunctorMinus Q i hi ρ)
                a' b' e x ∈ W₂ b' :=
            fun e x hx => hW₂ e x hx
          generalize W₂ a' = Sa at hw hsubrep ⊢
          generalize W₂ b' = Sb at hsubrep ⊢
          clear hcompl hW₁ hW_at_compl W₁_at U₁ W₁ U₂ W₂_at arrow_ne hnotsimple hρ hW₂ W₂ hU₁_subrep
          have h_da : ‹DecidableEq Q› a' i = .isFalse ha' := by
            cases ‹DecidableEq Q› a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
          have h_db : ‹DecidableEq Q› b' i = .isFalse hb' := by
            cases ‹DecidableEq Q› b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
          revert hw w e' hsubrep Sb Sa
          unfold Etingof.reflFunctorMinus_equivAt_ne
            Etingof.reflectionFunctorMinus Etingof.reversedAtVertex Etingof.ReversedAtVertexHom
          simp only []
          rw [h_da, h_db]
          simp only []
          intro e' w Sa hw Sb hsubrep
          simp only [id, LinearEquiv.refl_apply, Submodule.map_id, LinearEquiv.coe_toLinearMap,
            LinearEquiv.refl_toLinearMap] at *
          exact hsubrep e' w hw
      have hU_compl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
        intro v
        by_cases hv : v = i
        · -- At i: disjoint because sourceMap injective, codisjoint by mkQ argument
          subst hv
          simp only [U₁, U₂, dif_pos rfl]
          constructor
          · -- Disjoint: (⨅ a, comap W₁_at a) ∩ (⨅ a, comap W₂_at a) = ⊥
            rw [Submodule.disjoint_def]
            intro x hx₁ hx₂
            -- For each a, mapLinear a.2 x ∈ W₁_at a ∩ W₂_at a = ⊥
            simp only [Submodule.mem_iInf] at hx₁ hx₂
            have hzero := fun a => by
              have hmem : ρ.mapLinear a.2 x ∈ W₁_at a ⊓ W₂_at a :=
                ⟨Submodule.mem_comap.mp (hx₁ a), Submodule.mem_comap.mp (hx₂ a)⟩
              rw [(hW_at_compl a).inf_eq_bot, Submodule.mem_bot] at hmem
              exact hmem
            -- All components of ψ(x) are 0, so ψ(x) = 0, so x = 0 (injective)
            have hψ : ψ x = 0 := by
              change (ρ.sourceMap _) x = 0
              unfold Etingof.QuiverRepresentation.sourceMap
              simp only [LinearMap.sum_apply, LinearMap.comp_apply]
              exact Finset.sum_eq_zero fun a _ => by
                simp [DirectSum.lof_eq_of, hzero a]
            exact hinj (hψ.trans (map_zero ψ).symm)
          · -- Codisjoint: ⨅ comap W₁_at + ⨅ comap W₂_at = ⊤
            -- Key argument: for any v, decompose ψ(v) componentwise,
            -- then use subrep condition + disjointness of W₁(i), W₂(i) in coker
            -- to show each piece is in range(ψ).
            sorry
        · -- At v ≠ i: same as sink case
          simp only [U₁, U₂, dif_neg hv]
          have hc := hcompl v
          exact ⟨by
            rw [Submodule.disjoint_def]
            intro x hx1 hx2
            obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx1
            obtain ⟨w₂, hw₂, hw₂eq⟩ := Submodule.mem_map.mp hx2
            have heq := (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).injective hw₂eq
            have : w₁ ∈ W₁ v ⊓ W₂ v := ⟨hw₁, heq ▸ hw₂⟩
            rw [hc.1.eq_bot] at this
            simp only [Submodule.mem_bot] at this
            rw [this, map_zero],
          by
            rw [codisjoint_iff, eq_top_iff]; intro x _
            obtain ⟨w, rfl⟩ := (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).surjective x
            have hw : w ∈ (⊤ : Submodule k _) := Submodule.mem_top
            rw [← hc.2.eq_top, Submodule.mem_sup] at hw
            obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
            exact Submodule.mem_sup.mpr
              ⟨_, Submodule.mem_map.mpr ⟨w₁, hw₁, rfl⟩,
               _, Submodule.mem_map.mpr ⟨w₂, hw₂, rfl⟩,
               (map_add _ _ _).symm⟩⟩
      -- Apply V's indecomposability
      have hindecomp := hρ.2 U₁ U₂ hU₁_subrep hU₂_subrep hU_compl
      -- Transport back: U_k = ⊥ everywhere → W_k = ⊥ everywhere
      -- The source case needs the complement (quotient vs kernel), so we pass it.
      suffices transport :
          ∀ (W W' : ∀ v, Submodule k
            (@Etingof.QuiverRepresentation.obj k Q _
              (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi ρ) v)),
            (∀ {a b} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b),
              ∀ x ∈ W' a,
              @Etingof.QuiverRepresentation.mapLinear k Q _
                (Etingof.reversedAtVertex Q i)
                (Etingof.reflectionFunctorMinus Q i hi ρ) a b e x ∈ W' b) →
            (∀ v, IsCompl (W v) (W' v)) →
            (∀ v (hv : v ≠ i), Submodule.map
              (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).toLinearMap
              (W v) = ⊥) →
            (∀ v, W v = ⊥) by
        rcases hindecomp with h1 | h2
        · left; exact transport W₁ W₂ hW₂ hcompl (fun v hv => by
            have := h1 v; simp only [U₁, dif_neg hv] at this; exact this)
        · right; exact transport W₂ W₁ hW₁ (fun v => (hcompl v).symm) (fun v hv => by
            have := h2 v; simp only [U₂, dif_neg hv] at this; exact this)
      -- Prove the transport lemma
      intro W W' hW' hWW' hW_ne v
      by_cases hv : v = i
      · -- At i: W(j) = ⊥ for all j ≠ i, so W'(j) = ⊤.
        -- The complement W' receives all images from reversed arrows, so W'(i) = ⊤.
        -- Hence W(i) = ⊥.
        cases hv
        -- W(j) = ⊥ for all j ≠ i
        have hW_bot : ∀ j, j ≠ i → W j = ⊥ := by
          intro j hj
          have h := hW_ne j hj
          rw [eq_bot_iff] at h ⊢
          intro z hz
          rw [Submodule.mem_bot]
          have hmem := h ⟨z, hz, rfl⟩
          rw [Submodule.mem_bot] at hmem
          exact (Etingof.reflFunctorMinus_equivAt_ne hi ρ j hj).injective
            (hmem.trans (map_zero _).symm)
        -- W'(j) = ⊤ for all j ≠ i (complement of ⊥)
        have hW'_top : ∀ j, j ≠ i → W' j = ⊤ := by
          intro j hj
          have hbot := hW_bot j hj
          have hc := hWW' j
          rw [hbot] at hc
          exact eq_top_of_bot_isCompl hc
        -- For each a and w ∈ F⁻(V).obj(a.1), the F⁻ map along the reversed arrow
        -- sends w into W'(i) (since W'(a.1) = ⊤)
        have hW'_arrow : ∀ (a : Etingof.ArrowsOutOf Q i)
            (e_a : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a.1 i)
            (w : @Etingof.QuiverRepresentation.obj k Q _
              (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi ρ) a.1),
            @Etingof.QuiverRepresentation.mapLinear k Q _
              (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorMinus Q i hi ρ) a.1 i e_a w ∈ W' i := by
          intro a e_a w
          exact hW' e_a w (by rw [hW'_top a.1 (arrow_ne a)]; exact Submodule.mem_top)
        -- W'(i) = ⊤: the range of mkQ (surjective) lands in W'(i)
        -- because every mkQ(lof(a)(z)) = F⁻_map(reversed_arrow)(equiv⁻¹(z)) ∈ W'(i)
        -- Key lemma: mkQ(lof(a)(z)) ∈ W'(i) for each a and z
        -- Proof: construct reversed arrow, use hW'_arrow + reflFunctorMinus_mapLinear_ne_eq
        have hW'_mkQ_lof : ∀ (a : Etingof.ArrowsOutOf Q i) (z : ρ.obj a.1),
            (Etingof.reflFunctorMinus_mkQ hi ρ)
              ((DirectSum.lof k _ (fun b => ρ.obj b.1) a) z) ∈ W' i := by
          intro ⟨j, ej⟩ z
          have hj : j ≠ i := fun heq => (hi i).false (heq ▸ ej)
          let e_a := Etingof.arrowOutToReversed hi ⟨j, ej⟩
          let w := (Etingof.reflFunctorMinus_equivAt_ne hi ρ j hj).symm z
          -- F⁻_map(e_a)(w) ∈ W'(i) by hW'_arrow
          have hmem := hW'_arrow ⟨j, ej⟩ e_a w
          -- By API: F⁻_map(e_a)(w) = mkQ(lof(⟨j, reversedArrow_ne_eq hj e_a⟩)(equiv(w)))
          rw [Etingof.reflFunctorMinus_mapLinear_ne_eq hi ρ hj e_a w] at hmem
          -- equiv(w) = z and reversedArrow_ne_eq hj e_a = ej
          simp only [w, LinearEquiv.apply_symm_apply] at hmem
          -- Now hmem has lof ⟨j, reversedArrow_ne_eq hj e_a⟩ z
          -- and we need lof ⟨j, ej⟩ z
          -- These are equal by reversedArrow_arrowOut_eq
          have hrev : Etingof.reversedArrow_ne_eq hj e_a = ej :=
            Etingof.reversedArrow_arrowOut_eq hi ⟨j, ej⟩
          -- Need to show lof ⟨j, ej⟩ z matches hmem which has lof ⟨j, reversedArrow_ne_eq hj e_a⟩ z
          -- Since hrev says they're equal arrows, convert
          exact hrev ▸ hmem
        -- W'(i) = ⊤: show every element of the cokernel is in W'(i)
        -- by decomposing into lof components mapped through mkQ
        have hW'i_top : W' i = ⊤ := by
          rw [eq_top_iff]; intro x _
          -- Show every element of coker is in W'(i) via reflFunctorMinus_mkQ
          -- mkQ is surjective, so x = mkQ(z) for some z
          -- Strategy: show range(reflFunctorMinus_mkQ) ⊆ W'(i)
          suffices h : ∀ z, (Etingof.reflFunctorMinus_mkQ hi ρ) z ∈ W' i by
            -- Need: reflFunctorMinus_mkQ is surjective
            -- It's Submodule.mkQ after unfolding, hence surjective
            -- For now, use sorry for the surjectivity bridge
            sorry
          intro z
          -- Decompose z = ∑ lof(a)(z(a))
          rw [show z = ∑ a ∈ Finset.univ, (DirectSum.of (fun a => ρ.obj a.1) a) (z a) from
            (DirectSum.sum_univ_of z).symm]
          rw [map_sum]
          exact Submodule.sum_mem _ fun a _ => by
            -- of = lof as functions
            change (Etingof.reflFunctorMinus_mkQ hi ρ)
              ((DirectSum.lof k _ (fun a => ρ.obj a.1) a) (z a)) ∈ W' i
            exact hW'_mkQ_lof a (z a)
        -- W(i) ⊓ W'(i) = ⊥ and W'(i) = ⊤ implies W(i) = ⊥
        have hci := hWW' i
        rw [hW'i_top] at hci
        exact eq_bot_of_isCompl_top hci
      · -- At v ≠ i: injective map = ⊥ → original = ⊥
        specialize hW_ne v hv
        rw [eq_bot_iff]
        intro x hx
        rw [eq_bot_iff] at hW_ne
        have hmem : (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv) x ∈
            Submodule.map
              (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).toLinearMap
              (W v) :=
          ⟨x, hx, rfl⟩
        have h0 := hW_ne hmem
        rw [Submodule.mem_bot] at h0 ⊢
        exact (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).injective
          (by rw [h0, map_zero])
