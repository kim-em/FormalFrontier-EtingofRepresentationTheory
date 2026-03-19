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
  -- BLOCKED: The Decidable.casesOn in reflectionFunctorPlus creates opaque type-level
  -- terms that rw/simp/generalize cannot rewrite due to dependent type constraints.
  -- The proper fix is to refactor reflectionFunctorPlus to avoid Decidable.casesOn
  -- (e.g., using a structure with explicit vertex-wise data instead of case-splitting).
  sorry

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
      -- Apply V's indecomposability
      have hindecomp := hρ.2 U₁ U₂ (sorry) (sorry) (sorry)
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
        subst hv
        sorry
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
