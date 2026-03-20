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

/-- At v ≠ i, the linear equiv between F⁺ᵢ(ρ).obj v and ρ.obj v (the identity). -/
private noncomputable def reflFunctorPlus_equiv_ne
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

/-- Convert a reversed-quiver arrow between non-sink vertices back to original.
Uses match on the DecidableEq instance for clean definitional reduction. -/
private def reversedArrow_ne_ne
    {Q : Type*} [inst : DecidableEq Q] [Quiver Q] {i a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b) : a ⟶ b := by
  change @Etingof.ReversedAtVertexHom Q inst _ i a b at e
  unfold Etingof.ReversedAtVertexHom at e
  revert e
  exact match inst a i, inst b i with
  | .isTrue h, _ => absurd h ha
  | .isFalse _, .isTrue h => absurd h hb
  | .isFalse _, .isFalse _ => fun e => e

/-! ## Decidable instance helpers

`reflectionFunctorPlus` is defined using `Decidable.casesOn`, creating opaque type-level
terms. These helpers normalize `Decidable` instances to known constructors, enabling
`simp`-based reduction in proof contexts where `rw`/`generalize` fail due to dependent
type constraints.

**Known blocker**: Even with these helpers, `simp` cannot rewrite `inst a i` inside
`Decidable.rec` terms in the goal when the motive involves dependent types. A future
refactor of `reflectionFunctorPlus` to use explicit vertex-indexed data (avoiding
`Decidable.casesOn`) would resolve this. -/

/-- A `Decidable p` with proof of `¬p` must be `.isFalse`. Uses proof irrelevance. -/
private lemma decidable_eq_isFalse {p : Prop} (h : ¬p) (d : Decidable p) :
    d = .isFalse h := by
  cases d with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-- A `Decidable p` with proof of `p` must be `.isTrue`. Uses proof irrelevance. -/
private lemma decidable_eq_isTrue {p : Prop} (h : p) (d : Decidable p) :
    d = .isTrue h := by
  cases d with
  | isTrue _ => rfl
  | isFalse hp => exact absurd h hp

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

set_option maxHeartbeats 400000 in
-- reason: unfolding reflectionFunctorPlus + rewriting Decidable instances
/-- At non-sink vertices, the F⁺ᵢ map between a and b (both ≠ i) equals
the original ρ map, after transport through the equivAt_ne equivalences. -/
private theorem reflFunctorPlus_mapLinear_ne_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    (ρ : Etingof.QuiverRepresentation k Q) {a b : Q}
    (ha : a ≠ i) (hb : b ≠ i)
    (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b)
    (w : @Etingof.QuiverRepresentation.obj k Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ) a) :
    (Etingof.reflFunctorPlus_equivAt_ne hi ρ b hb)
      (@Etingof.QuiverRepresentation.mapLinear k Q _
        (Etingof.reversedAtVertex Q i)
        (Etingof.reflectionFunctorPlus Q i hi ρ) a b e w) =
    ρ.mapLinear (reversedArrow_ne_ne ha hb e)
      ((Etingof.reflFunctorPlus_equivAt_ne hi ρ a ha) w) := by
  exact Etingof.reflFunctorPlus_mapLinear_ne_ne hi ρ ha hb e w

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
      -- Helper: component membership from iSup of lof-images
      have comp_mem : ∀ (S : ∀ a : Etingof.ArrowsInto Q i, Submodule k (ρ.obj a.1))
          (y : DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1))
          (_ : y ∈ ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (S a))
          (a : Etingof.ArrowsInto Q i),
          DirectSum.component k _ (fun a => ρ.obj a.1) a y ∈ S a := by
        intro S y hy a
        refine Submodule.iSup_induction
          (fun b => Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) b) (S b))
          (motive := fun y =>
            DirectSum.component k _ (fun a => ρ.obj a.1) a y ∈ S a)
          hy ?_ ?_ ?_
        · intro b z hz
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hz
          simp only [DirectSum.component.of]
          split
          · next h => exact h ▸ hs
          · exact zero_mem _
        · exact zero_mem _
        · intro x' y' hx' hy'; rw [map_add]; exact add_mem hx' hy'
      -- Helper: kernel element from W(i) has val in iSup of lof-images
      have val_in_iSup : ∀ (W : ∀ v, Submodule k
            (@Etingof.QuiverRepresentation.obj k Q _
              (Etingof.reversedAtVertex Q i)
              (Etingof.reflectionFunctorPlus Q i hi ρ) v))
          (W_at : ∀ a : Etingof.ArrowsInto Q i, Submodule k (ρ.obj a.1))
          (_ : W_at = fun a => Submodule.map
            (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)).toLinearMap (W a.1))
          (_ : ∀ {a b} (e : @Quiver.Hom Q (Etingof.reversedAtVertex Q i) a b),
            ∀ x ∈ W a, @Etingof.QuiverRepresentation.mapLinear k Q _
              (Etingof.reversedAtVertex Q i) (Etingof.reflectionFunctorPlus Q i hi ρ)
              a b e x ∈ W b)
          (z : @Etingof.QuiverRepresentation.obj k Q _
            (Etingof.reversedAtVertex Q i)
            (Etingof.reflectionFunctorPlus Q i hi ρ) i)
          (_ : z ∈ W i),
          (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val ∈
            ⨆ a, Submodule.map (DirectSum.lof k _ (fun a => ρ.obj a.1) a) (W_at a) := by
        intro W W_at hW_at_def hWsub z hz
        suffices h : ∀ a : Etingof.ArrowsInto Q i,
            DirectSum.component k _ (fun a => ρ.obj a.1) a
              (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val ∈ W_at a by
          rw [show (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val =
            ∑ a ∈ (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val.support,
              DirectSum.of (fun a => ρ.obj a.1) a
                ((Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val a) from
            (DirectSum.sum_support_of _).symm]
          apply Submodule.sum_mem
          intro a _
          exact Submodule.mem_iSup_of_mem a (Submodule.mem_map.mpr ⟨_, h a, rfl⟩)
        intro a
        rw [hW_at_def]
        have hmap := hWsub (arrowsIntoReversed hi a) z hz
        have hcomp := reflFunctorPlus_map_from_sink_component hi ρ a (arrow_ne a) z
        -- hcomp : equivAt_ne (mapLinear ...) = component a (equivAt_eq z).val
        -- Need: ∃ w ∈ W a.1, equivAt_ne w = component a (equivAt_eq z).val
        -- The witness is mapLinear ... z, and the equality is hcomp
        exact ⟨_, hmap, hcomp⟩
      -- Helper: W₁_at/W₂_at are complementary at each arrow
      have hW_at_compl : ∀ a : Etingof.ArrowsInto Q i, IsCompl (W₁_at a) (W₂_at a) := by
        intro a
        simp only [W₁_at, W₂_at]
        exact (hcompl a.1).map
          (Submodule.orderIsoMapComap
            (Etingof.reflFunctorPlus_equivAt_ne hi ρ a.1 (arrow_ne a)))
      -- Prove IsCompl at vertex i for the φ-images
      set_option maxHeartbeats 800000 in
      have hU_compl_i : IsCompl (U₁ i) (U₂ i) := by
        simp only [U₁, U₂, dif_pos rfl]
        constructor
        · -- Disjoint
          rw [Submodule.disjoint_def]
          intro x hx1 hx2
          obtain ⟨y₁, hy₁, rfl⟩ := Submodule.mem_map.mp hx1
          obtain ⟨y₂, hy₂, hy₂eq⟩ := Submodule.mem_map.mp hx2
          have hker : y₁ - y₂ ∈ φ.ker := by
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hy₂eq.symm
          set zeq := (Etingof.reflFunctorPlus_equivAt_eq hi ρ).symm ⟨y₁ - y₂, hker⟩
          have hzeq_top : zeq ∈ (⊤ : Submodule k _) := Submodule.mem_top
          rw [← (hcompl i).2.eq_top, Submodule.mem_sup] at hzeq_top
          obtain ⟨z₁, hz₁, z₂, hz₂, hzsum⟩ := hzeq_top
          have hv₁ := val_in_iSup W₁ W₁_at rfl hW₁ z₁ hz₁
          have hv₂ := val_in_iSup W₂ W₂_at rfl hW₂ z₂ hz₂
          have hsum_val : y₁ - y₂ =
              (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val +
              (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val := by
            have h1 : zeq = z₁ + z₂ := hzsum.symm
            have h2 := congr_arg
              (fun z => (Etingof.reflFunctorPlus_equivAt_eq hi ρ z).val) h1
            simp only [map_add, Submodule.coe_add] at h2
            rw [← h2]
            -- zeq = equivAt_eq⁻¹ ⟨y₁ - y₂, hker⟩, so equivAt_eq(zeq) = ⟨y₁ - y₂, hker⟩
            simp only [zeq, LinearEquiv.apply_symm_apply]
          suffices y₁ = (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val by
            rw [this]; exact (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).property
          refine DFunLike.ext _ _ fun a => ?_
          have hca_y₁ := comp_mem W₁_at y₁ hy₁ a
          have hca_y₂ := comp_mem W₂_at y₂ hy₂ a
          have hca_z₁ := comp_mem W₁_at _ hv₁ a
          have hca_z₂ := comp_mem W₂_at _ hv₂ a
          have hcomp_eq : DirectSum.component k _ _ a y₁ -
              DirectSum.component k _ _ a y₂ =
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val +
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val := by
            have := congr_arg (DirectSum.component k _ (fun a => ρ.obj a.1) a) hsum_val
            simp only [map_sub, map_add] at this; exact this
          have hlhs : DirectSum.component k _ _ a y₁ -
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val ∈
              W₁_at a := sub_mem hca_y₁ hca_z₁
          have hrhs_eq : DirectSum.component k _ _ a y₁ -
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val =
              DirectSum.component k _ _ a y₂ +
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₂).val := by
            -- a - c₁ = b + c₂ from a - b = c₁ + c₂
            -- Rearrange: a - c₁ = (a - b) - c₁ + b = (c₁ + c₂) - c₁ + b = c₂ + b = b + c₂
            have := hcomp_eq
            -- this : comp y₁ - comp y₂ = comp z₁ + comp z₂
            -- Goal: comp y₁ - comp z₁ = comp y₂ + comp z₂
            rw [sub_eq_iff_eq_add] at this ⊢
            rw [this]; abel
          have hrhs : DirectSum.component k _ _ a y₁ -
              DirectSum.component k _ _ a (Etingof.reflFunctorPlus_equivAt_eq hi ρ z₁).val ∈
              W₂_at a := hrhs_eq ▸ add_mem hca_y₂ hca_z₂
          have hzero := (hW_at_compl a).1.eq_bot ▸
            (show _ ∈ W₁_at a ⊓ W₂_at a from ⟨hlhs, hrhs⟩)
          rw [Submodule.mem_bot] at hzero
          rw [sub_eq_zero] at hzero
          -- component a y₁ = component a z₁.val, convert to DFunLike equality
          exact hzero
        · -- Codisjoint
          rw [codisjoint_iff, ← Submodule.map_sup]
          rw [eq_top_iff]; intro x _
          obtain ⟨y, rfl⟩ := hsurj x
          refine Submodule.mem_map.mpr ⟨y, ?_, rfl⟩
          -- Need: y ∈ S₁ ⊔ S₂
          rw [Submodule.mem_sup]
          rw [show y = ∑ a ∈ y.support,
            DirectSum.of (fun a => ρ.obj a.1) a (y a) from
            (DirectSum.sum_support_of _).symm]
          have hdecomp : ∀ a : Etingof.ArrowsInto Q i, ∃ w₁ ∈ W₁_at a, ∃ w₂ ∈ W₂_at a,
              w₁ + w₂ = y a := by
            intro a
            have := (hW_at_compl a).2.eq_top
            exact Submodule.mem_sup.mp (this ▸ Submodule.mem_top)
          choose w₁_fn hw₁ w₂_fn hw₂ hsum using hdecomp
          refine ⟨∑ a ∈ y.support, DirectSum.lof k _ _ a (w₁_fn a), ?_,
                  ∑ a ∈ y.support, DirectSum.lof k _ _ a (w₂_fn a), ?_, ?_⟩
          · exact Submodule.sum_mem _ fun a _ =>
              Submodule.mem_iSup_of_mem a (Submodule.mem_map.mpr ⟨_, hw₁ a, rfl⟩)
          · exact Submodule.sum_mem _ fun a _ =>
              Submodule.mem_iSup_of_mem a (Submodule.mem_map.mpr ⟨_, hw₂ a, rfl⟩)
          · rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro a _
            rw [← map_add, DirectSum.lof_eq_of k, hsum a]
      have hU_compl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
        intro v
        by_cases hv : v = i
        · subst hv; exact hU_compl_i
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
  -- BLOCKED: Definition 6.6.4 (reflectionFunctorMinus) is mostly sorry'd.
  -- The proof would be dual to the sink case:
  -- By Prop 6.6.5_source: either V is simple at i (→ F⁻(V) = 0) or sourceMap injective
  -- In the injective case: F⁻(V) is indecomposable by the dual construction.
  sorry
