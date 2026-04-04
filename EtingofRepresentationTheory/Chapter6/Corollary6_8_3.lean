import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Proposition6_6_6
import EtingofRepresentationTheory.Chapter6.Proposition6_6_7
import EtingofRepresentationTheory.Chapter6.Proposition6_6_8
import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1
import EtingofRepresentationTheory.Chapter6.Lemma6_7_2
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Corollary 6.8.3: Dimension Vector Determines Indecomposable Representation

If V, V' are indecomposable representations of a Dynkin quiver Q with d(V) = d(V'),
then V ≅ V'.

The proof uses admissible orderings to ensure each vertex is a sink at the appropriate
step. At each sink, Proposition 6.6.5 determines whether the rep is simple or surjective.
Since both reps have the same dimension vector, they make the same choice. In the simple
case, `simpleAt_iso` gives the isomorphism. In the surjective case, we apply F⁺ and
recurse on the reversed quiver.

## Remaining sorry

The **recovery lemma** (F⁺(ρ₁) ≅ F⁺(ρ₂) → ρ₁ ≅ ρ₂ when both have surjective sink maps)
requires:
1. F⁻ functoriality: constructing F⁻(iso) from an iso between F⁺ outputs
2. Composition with Proposition 6.6.6 round-trip: ρ ≅ F⁻(F⁺(ρ))
-/

open scoped Matrix

section Helpers

/-- A Dynkin quiver (orientation of a Dynkin diagram) has no self-loops at any vertex. -/
private lemma Etingof.noSelfLoop_of_dynkin_orientation
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (p : Fin n) :
    IsEmpty (@Quiver.Hom (Fin n) Q p p) :=
  hOrient.1 p p (by rw [hDynkin.2.1 p]; omega)

end Helpers

section IsoComposition

/-- Inverse of a quiver representation isomorphism. -/
noncomputable def Etingof.QuiverRepresentation.Iso.symm
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂) :
    Etingof.QuiverRepresentation.Iso ρ₂ ρ₁ :=
  ⟨fun v => (f.equivAt v).symm,
   fun e x => by
     apply (f.equivAt _).injective
     rw [LinearEquiv.apply_symm_apply, f.naturality, LinearEquiv.apply_symm_apply]⟩

/-- Composition of quiver representation isomorphisms. -/
noncomputable def Etingof.QuiverRepresentation.Iso.trans
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentation.Iso ρ₂ ρ₃) :
    Etingof.QuiverRepresentation.Iso ρ₁ ρ₃ :=
  ⟨fun v => (f.equivAt v).trans (g.equivAt v),
   fun e x => by
     simp only [LinearEquiv.trans_apply, f.naturality, g.naturality]⟩

/-- Transport an isomorphism through a quiver instance equality. -/
noncomputable def Etingof.QuiverRepresentation.Iso.transport
    {k : Type*} [CommSemiring k] {Q : Type} [DecidableEq Q]
    {inst₁ inst₂ : @Quiver.{0, 0} Q} (h : inst₁ = inst₂)
    {ρ₁ ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₁}
    (f : @Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ ρ₂) :
    @Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) (h ▸ ρ₂) := by
  subst h; exact f

end IsoComposition

section SimpleAtIso

/-- Two representations that are simple at the same vertex are isomorphic. -/
private lemma Etingof.simpleAt_iso
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (p : Q)
    (hNoSelfLoop : IsEmpty (p ⟶ p))
    (h₁ : ρ₁.IsSimpleAt p)
    (h₂ : ρ₂.IsSimpleAt p) :
    Nonempty (Etingof.QuiverRepresentation.Iso ρ₁ ρ₂) := by
  have hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v) := by
    intro v
    by_cases hv : v = p
    · subst hv; rw [h₁.1, h₂.1]
    · rw [h₁.2 v hv, h₂.2 v hv]
  refine ⟨⟨fun v => LinearEquiv.ofFinrankEq _ _ (hdim v), fun {a b} e x => ?_⟩⟩
  by_cases ha : a = p <;> by_cases hb : b = p
  · subst ha; subst hb; exact (hNoSelfLoop.false e).elim
  · haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _
  · haveI : Subsingleton (ρ₁.obj a) := by
      have hfr := h₁.2 a ha
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp [map_zero]
  · haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _

/-- Two indecomposable representations with dimension vector equal to a simple root αₚ
are isomorphic. -/
private lemma Etingof.indecomposable_simpleRoot_iso
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : @Etingof.IsOrientationOf n Q adj)
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (p : Fin n)
    (hd₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = Etingof.simpleRoot n p v)
    (hd₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = Etingof.simpleRoot n p v) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) := by
  have hNoSelfLoop := Etingof.noSelfLoop_of_dynkin_orientation hDynkin hOrient p
  have h₁s : ρ₁.IsSimpleAt p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₁ p; simp [Etingof.simpleRoot] at this; omega
    · have := hd₁ j; simp [Etingof.simpleRoot, show p ≠ j from Ne.symm hj] at this; omega
  have h₂s : ρ₂.IsSimpleAt p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₂ p; simp [Etingof.simpleRoot] at this; omega
    · have := hd₂ j; simp [Etingof.simpleRoot, show p ≠ j from Ne.symm hj] at this; omega
  exact Etingof.simpleAt_iso ρ₁ ρ₂ p hNoSelfLoop h₁s h₂s

end SimpleAtIso

section ReflectionFunctorChain

/-- Walk through a vertex list with two indecomposable representations simultaneously.
Each vertex must be a sink at the appropriate step (admissible ordering property).
Since both representations have the same dimension vector, they make the same
"simple or surjective" choice at each vertex.

**Base case** (empty list): both have dim vector = simple root → isomorphic.

**Inductive step**: both are surjective at the sink → apply F⁺ → recurse on
reversed quiver → recover isomorphism via Prop 6.6.6 (round-trip theorem).

**Key sorry**: The recovery lemma (F⁺(ρ₁) ≅ F⁺(ρ₂) → ρ₁ ≅ ρ₂) requires
F⁻ functoriality + composing with the round-trip theorem. -/
private lemma Etingof.parallel_reduce_and_recover
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    (remaining : List (Fin n))
    {Q_cur : @Quiver.{0, 0} (Fin n)}
    (hOrient_cur : @Etingof.IsOrientationOf n Q_cur adj)
    (hSS_cur : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b))
    (hSinks : ∀ m (hm : m < remaining.length),
        @Etingof.IsSink (Fin n)
          (@Etingof.iteratedReversedAtVertices _ _ Q_cur (remaining.take m))
          (remaining.get ⟨m, hm⟩))
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q_cur)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : @Etingof.QuiverRepresentation.IsIndecomposable k _ _ Q_cur ρ₁)
    (h₂ : @Etingof.QuiverRepresentation.IsIndecomposable k _ _ Q_cur ρ₂)
    (d_cur : Fin n → ℤ)
    (hDim₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = d_cur v)
    (hDim₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = d_cur v)
    (p : Fin n)
    (hreflect : Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) remaining
        d_cur = Etingof.simpleRoot n p) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q_cur ρ₁ ρ₂) := by
  induction remaining generalizing Q_cur d_cur with
  | nil =>
    simp only [Etingof.iteratedSimpleReflection, List.foldl_nil] at hreflect
    exact Etingof.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ p
      (fun v => by rw [hDim₁]; exact congr_fun hreflect v)
      (fun v => by rw [hDim₂]; exact congr_fun hreflect v)
  | cons i rest ih =>
    -- i is a sink of Q_cur (from sinks condition at position 0)
    have hi_sink : @Etingof.IsSink (Fin n) Q_cur i := by
      have := hSinks 0 (by simp)
      simp only [List.take_zero, Etingof.iteratedReversedAtVertices] at this
      exact this
    -- Derive Fintype for ArrowsInto
    haveI : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_cur a b) := hSS_cur
    haveI : Fintype (@Etingof.ArrowsInto (Fin n) Q_cur i) :=
      Etingof.fintypeArrowsIntoOfSubsingleton i
    -- Both reps: either simple at i or surjective sink map (Prop 6.6.5)
    rcases @Etingof.Proposition6_6_5_sink k _ _ _ Q_cur ρ₁ i _ _ hi_sink h₁ with
      h₁_simple | h₁_surj
    · -- ρ₁ is simple at i → d_cur = simpleRoot i
      -- Then iteratedSimpleReflection (i :: rest) d_cur starts with sᵢ(d_cur)
      -- But if d_cur = simpleRoot i, then sᵢ(simpleRoot i) has a -1 entry, contradiction
      -- unless rest = [] and d_cur = simpleRoot p
      -- Actually: simple at i means d_cur = simpleRoot i, so p = i and the nil case applies
      have hd_simple : d_cur = Etingof.simpleRoot n i := by
        funext v
        by_cases hv : v = i
        · subst hv; rw [← hDim₁]; simp [Etingof.simpleRoot]
          exact_mod_cast h₁_simple.1
        · have h := hDim₁ v; have h2 := h₁_simple.2 v hv
          simp [Etingof.simpleRoot, Ne.symm hv] at h ⊢; omega
      -- ρ₂ also has dim vector = simpleRoot i, so also simple at i
      exact Etingof.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ i
        (fun v => by rw [hDim₁, hd_simple])
        (fun v => by rw [hDim₂, hd_simple])
    · -- ρ₁ has surjective sink map at i
      -- Since d(ρ₂) = d(ρ₁) = d_cur and both are indecomposable, ρ₂ also can't be simple at i
      -- (simple at i means d = simpleRoot i, but then ρ₁ would be simple too, contradiction)
      rcases @Etingof.Proposition6_6_5_sink k _ _ _ Q_cur ρ₂ i _ _ hi_sink h₂ with
        h₂_simple | h₂_surj
      · -- ρ₂ simple → d_cur = simpleRoot i → both have simpleRoot dim vector → iso
        have hd_simple₂ : d_cur = Etingof.simpleRoot n i := by
          funext v
          by_cases hv : v = i
          · subst hv; rw [← hDim₂]; simp [Etingof.simpleRoot]
            exact_mod_cast h₂_simple.1
          · have h := hDim₂ v; have h2 := h₂_simple.2 v hv
            simp [Etingof.simpleRoot, Ne.symm hv] at h ⊢; omega
        exact Etingof.indecomposable_simpleRoot_iso hDynkin hOrient_cur ρ₁ ρ₂ i
          (fun v => by rw [hDim₁, hd_simple₂])
          (fun v => by rw [hDim₂, hd_simple₂])
      · -- Both surjective: apply F⁺, recurse, recover via F⁻ + round-trip
        -- Prove sink subsingleton lemmas BEFORE Q_rev to avoid instance pollution
        have h₁_sink_ss_of_src :
            (∀ (a : Etingof.ArrowsInto (Fin n) i), Subsingleton (ρ₁.obj a.1)) →
            Subsingleton (ρ₁.obj i) := by
          intro hsrc_ss
          refine ⟨fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := h₁_surj a
          obtain ⟨y, rfl⟩ := h₁_surj b
          suffices x = y by rw [this]
          have : ∀ z : DirectSum (Etingof.ArrowsInto (Fin n) i) (fun a => ρ₁.obj a.1), z = 0 :=
            fun z => DFinsupp.ext (fun j => @Subsingleton.elim _ (hsrc_ss j) _ _)
          exact (this x).trans (this y).symm
        have h₂_sink_ss_of_src :
            (∀ (a : Etingof.ArrowsInto (Fin n) i), Subsingleton (ρ₂.obj a.1)) →
            Subsingleton (ρ₂.obj i) := by
          intro hsrc_ss
          refine ⟨fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := h₂_surj a
          obtain ⟨y, rfl⟩ := h₂_surj b
          suffices x = y by rw [this]
          have : ∀ z : DirectSum (Etingof.ArrowsInto (Fin n) i) (fun a => ρ₂.obj a.1), z = 0 :=
            fun z => DFinsupp.ext (fun j => @Subsingleton.elim _ (hsrc_ss j) _ _)
          exact (this x).trans (this y).symm
        let Q_rev := @Etingof.reversedAtVertex (Fin n) _ Q_cur i
        let ρ₁_plus := @Etingof.reflectionFunctorPlus k _ (Fin n) _ Q_cur i hi_sink ρ₁
        let ρ₂_plus := @Etingof.reflectionFunctorPlus k _ (Fin n) _ Q_cur i hi_sink ρ₂
        -- Subsingleton/Fintype on reversed quiver
        haveI hSS_rev : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_rev a b) :=
          fun a b => Etingof.subsingleton_hom_reversedAtVertex i a b
        haveI : Fintype (@Etingof.ArrowsInto (Fin n) Q_rev i) :=
          @Etingof.fintypeArrowsIntoOfSubsingleton _ Q_rev hSS_rev i
        haveI : ∀ (j : Fin n), Fintype (@Quiver.Hom (Fin n) Q_rev i j) :=
          fun j => @Etingof.fintypeHomOfSubsingleton _ Q_rev hSS_rev i j
        haveI : Fintype (@Etingof.ArrowsOutOf (Fin n) Q_rev i) := Sigma.instFintype
        -- Free/Finite for F⁺ outputs — use rw [hv] to avoid subst eliminating i
        haveI : ∀ v, Module.Free k (ρ₁_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_free_eq k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _
          · exact @Etingof.reflFunctorPlus_free_ne k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ v hv
        haveI : ∀ v, Module.Finite k (ρ₁_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_finite_eq k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _
          · exact @Etingof.reflFunctorPlus_finite_ne k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ v hv
        haveI : ∀ v, Module.Free k (ρ₂_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_free_eq k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _
          · exact @Etingof.reflFunctorPlus_free_ne k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ v hv
        haveI : ∀ v, Module.Finite k (ρ₂_plus.obj v) := fun v => by
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_finite_eq k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _
          · exact @Etingof.reflFunctorPlus_finite_ne k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ v hv
        -- F⁺ outputs are indecomposable (Prop 6.6.7 + not zero since surjective)
        have h₁_ind : @Etingof.QuiverRepresentation.IsIndecomposable k _ _ Q_rev ρ₁_plus := by
          rcases @Etingof.Proposition6_6_7_sink k _ _ _ Q_cur i hi_sink ρ₁ _ _ h₁ with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := h₁
            suffices hs : ∀ j, Subsingleton
                (@Etingof.QuiverRepresentation.obj k (Fin n) _ Q_cur ρ₁ j) from
              absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
            intro j
            by_cases hj : j = i
            · rw [hj]; exact h₁_sink_ss_of_src (fun ⟨m, e⟩ =>
                (@Etingof.reflFunctorPlus_equivAt_ne k _ (Fin n) _ Q_cur i hi_sink ρ₁ m
                  (fun h => (hi_sink m).false (h ▸ e))).toEquiv.subsingleton_congr.mp (h_zero m))
            · exact (@Etingof.reflFunctorPlus_equivAt_ne k _ (Fin n) _
                Q_cur i hi_sink ρ₁ j hj).toEquiv.subsingleton_congr.mp
                (h_zero j)
        have h₂_ind :
            @Etingof.QuiverRepresentation.IsIndecomposable
              k _ _ Q_rev ρ₂_plus := by
          rcases @Etingof.Proposition6_6_7_sink k _ _ _
            Q_cur i hi_sink ρ₂ _ _ h₂ with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := h₂
            suffices hs : ∀ j, Subsingleton
                (@Etingof.QuiverRepresentation.obj k (Fin n)
                  _ Q_cur ρ₂ j) from
              absurd (hs v)
                (not_subsingleton_iff_nontrivial.mpr hv)
            intro j
            by_cases hj : j = i
            · rw [hj]; exact h₂_sink_ss_of_src fun ⟨m, e⟩ =>
                let eq := @Etingof.reflFunctorPlus_equivAt_ne
                  k _ (Fin n) _ Q_cur i hi_sink ρ₂ m
                  (fun h => (hi_sink m).false (h ▸ e))
                eq.toEquiv.subsingleton_congr.mp (h_zero m)
            · have eq := @Etingof.reflFunctorPlus_equivAt_ne
                k _ (Fin n) _ Q_cur i hi_sink ρ₂ j hj
              exact eq.toEquiv.subsingleton_congr.mp
                (h_zero j)
        -- Orientation on reversed quiver
        have hOrient_rev : @Etingof.IsOrientationOf n Q_rev adj :=
          Etingof.reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hOrient_cur i
        -- Dim vector of F⁺ outputs = simpleReflection n A i d_cur
        set d_new := Etingof.simpleReflection n (Etingof.cartanMatrix n adj) i d_cur
        have hDim₁_plus : ∀ v, (Module.finrank k (ρ₁_plus.obj v) : ℤ) = d_new v := by
          intro v
          have h668 := @Etingof.Proposition6_6_8_sink k _
            (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _ h₁_surj v
          change (ρ₁_plus.finrankAt' k v : ℤ) = d_new v
          rw [h668]
          have hd_eq := funext hDim₁
          rw [hd_eq]
          have hbridge := @Etingof.simpleReflectionDimVector_eq_simpleReflection _ _
            hDynkin Q_cur hOrient_cur hSS_cur i hi_sink d_cur
          convert congr_fun hbridge v
        have hDim₂_plus : ∀ v, (Module.finrank k (ρ₂_plus.obj v) : ℤ) = d_new v := by
          intro v
          have h668 := @Etingof.Proposition6_6_8_sink k _
            (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _ h₂_surj v
          change (ρ₂_plus.finrankAt' k v : ℤ) = d_new v
          rw [h668]
          have hd_eq := funext hDim₂
          rw [hd_eq]
          have hbridge := @Etingof.simpleReflectionDimVector_eq_simpleReflection _ _
            hDynkin Q_cur hOrient_cur hSS_cur i hi_sink d_cur
          convert congr_fun hbridge v
        -- Sinks condition for rest on reversed quiver (definitional reduction)
        have hSinks_rest : ∀ m (hm : m < rest.length),
            @Etingof.IsSink (Fin n)
              (@Etingof.iteratedReversedAtVertices _ _ Q_rev (rest.take m))
              (rest.get ⟨m, hm⟩) := by
          intro m hm
          exact hSinks (m + 1) (by simp [List.length_cons]; omega)
        -- hreflect for rest on d_new
        have hreflect_rest : Etingof.iteratedSimpleReflection n
            (Etingof.cartanMatrix n adj) rest d_new = Etingof.simpleRoot n p := by
          rw [Etingof.iteratedSimpleReflection_cons] at hreflect
          exact hreflect
        -- Apply IH to F⁺ outputs on reversed quiver
        have h_iso_plus := @ih Q_rev hOrient_rev
          hSS_rev hSinks_rest ρ₁_plus ρ₂_plus _ _ _ _
          h₁_ind h₂_ind d_new hDim₁_plus hDim₂_plus
          hreflect_rest
        -- Recover ρ₁ ≅ ρ₂ via F⁻ functoriality + round-trip
        obtain ⟨iso_plus⟩ := h_iso_plus
        -- F⁻ applied to iso gives iso on double-reversed quiver
        have hi' := @Etingof.isSink_reversedAtVertex_isSource (Fin n) _ Q_cur i hi_sink
        obtain ⟨iso_dr⟩ := @Etingof.reflectionFunctorMinus_map_iso k _ (Fin n) _ Q_rev i hi'
          ρ₁_plus ρ₂_plus iso_plus _
        -- Transport iso_dr to Q_cur via reversedAtVertex_twice
        let h_eq := @Etingof.reversedAtVertex_twice (Fin n) _ Q_cur i
        let iso_transported := iso_dr.transport h_eq
        -- Round-trip isos: transport(F⁻(F⁺(ρ))) ≅ ρ
        obtain ⟨iso_rt₁⟩ := @Etingof.Proposition6_6_6_sink
          k _ (Fin n) _ Q_cur i hi_sink ρ₁ _ _ _ h₁_surj
        obtain ⟨iso_rt₂⟩ := @Etingof.Proposition6_6_6_sink
          k _ (Fin n) _ Q_cur i hi_sink ρ₂ _ _ _ h₂_surj
        -- Compose: ρ₁ ← transport(F⁻(F⁺(ρ₁))) ≅ transport(F⁻(F⁺(ρ₂))) → ρ₂
        exact ⟨@Etingof.QuiverRepresentation.Iso.trans k _ (Fin n) Q_cur _ _ _
          (@Etingof.QuiverRepresentation.Iso.symm k _ (Fin n) Q_cur _ _ iso_rt₁)
          (@Etingof.QuiverRepresentation.Iso.trans k _ (Fin n) Q_cur _ _ _
            iso_transported iso_rt₂)⟩

end ReflectionFunctorChain

section TitsFormBound

/-- The Tits form of the dimension vector of an indecomposable representation of a
Dynkin quiver satisfies B(d, d) ≤ 2. This follows from the stronger B = 2 exactly,
proved via Coxeter iteration in `CoxeterInfrastructure.lean`. -/
private lemma Etingof.indecomposable_titsForm_le_two
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((Etingof.cartanMatrix n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) ≤ 2 :=
  le_of_eq (Etingof.indecomposable_bilinearForm_eq_two hDynkin hOrient ρ hρ)

end TitsFormBound

set_option maxHeartbeats 800000 in
-- Coxeter iteration + admissible ordering search requires extra heartbeats
/-- Indecomposable representations of a Dynkin quiver are determined (up to isomorphism)
by their dimension vectors.
(Etingof Corollary 6.8.3) -/
theorem Etingof.Corollary6_8_3
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : ρ₁.IsIndecomposable)
    (h₂ : ρ₂.IsIndecomposable)
    (hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v)) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) := by
  -- Get admissible ordering
  obtain ⟨σ, hσ⟩ := Etingof.admissibleOrdering_exists hDynkin hOrient
  set A := Etingof.cartanMatrix n adj
  set d := fun v => (Module.finrank k (ρ₁.obj v) : ℤ) with hd_def
  set c := fun v => Etingof.iteratedSimpleReflection n A σ v
  -- d is nonneg and nonzero
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => Int.natCast_nonneg _
  have hd_nonzero : d ≠ 0 := by
    obtain ⟨⟨v, hv⟩, _⟩ := h₁
    intro h; have : d v = 0 := congr_fun h v
    simp only [d, Int.natCast_eq_zero] at this
    rw [Module.finrank_eq_zero_iff_of_free (R := k)] at this
    exact not_nontrivial_iff_subsingleton.mpr this hv
  -- Termination bound from generalized Lemma 6.7.2
  obtain ⟨N, i₀, hNeg⟩ := Etingof.generalized_Lemma6_7_2 hDynkin σ hσ.perm d hd_nonneg hd_nonzero
  -- Iterate: track one rep through rounds to find the vertex list
  -- We track ρ₁ to find where the dim vector reduces to a simple root.
  -- The full vertex list (with sinks condition) is then used with both ρ₁, ρ₂.
  -- Strengthened suffices: carry a representation through the iteration
  suffices ∀ (M : ℕ),
      Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) ∨
      ((∀ j, 0 ≤ c^[M] d j) ∧
       ∃ (ρ_M : @Etingof.QuiverRepresentation k (Fin n) _ Q),
         (∀ v, Module.Free k (ρ_M.obj v)) ∧
         (∀ v, Module.Finite k (ρ_M.obj v)) ∧
         ρ_M.IsIndecomposable ∧
         (∀ v, (Module.finrank k (ρ_M.obj v) : ℤ) = c^[M] d v)) by
    rcases this N with ⟨iso⟩ | ⟨hNN, _⟩
    · exact iso
    · exact absurd (hNN i₀) (not_le.mpr hNeg)
  intro M
  induction M with
  | zero =>
    right
    exact ⟨fun j => by simp only [Function.iterate_zero, id_eq]; exact hd_nonneg j,
           ρ₁, ‹_›, ‹_›, h₁,
           fun v => by simp only [Function.iterate_zero, id_eq, hd_def]⟩
  | succ M ih =>
    rcases ih with ⟨iso⟩ | ⟨hM_nonneg, ρ_M, hFree_M, hFinite_M, hIndecomp_M, hDimVec_M⟩
    · left; exact iso
    · -- Apply one_round_or_simpleRoot to ρ_M
      haveI : ∀ v, Module.Free k (ρ_M.obj v) := hFree_M
      haveI : ∀ v, Module.Finite k (ρ_M.obj v) := hFinite_M
      have hd_M : c^[M] d = fun v => (Module.finrank k (ρ_M.obj v) : ℤ) := by
        ext v; exact (hDimVec_M v).symm
      rcases Etingof.one_round_or_simpleRoot hDynkin hOrient σ hσ ρ_M hIndecomp_M
        (c^[M] d) hd_M with
        ⟨j, p₀, hj_le, hp₀⟩ | ⟨hnonneg, _, ρ', hFree', hFinite', hIndecomp', hDimVec'⟩
      · -- Simple root found at prefix j of round M
        left
        -- Build vertex list and call parallel_reduce_and_recover
        set vertices := (List.replicate M σ).flatten ++ σ.take j with hvertices_def
        have hSinks := Etingof.admissible_sinks_replicated Q σ hσ M j hj_le
        have hreflect : Etingof.iteratedSimpleReflection n A vertices d =
            Etingof.simpleRoot n p₀ := by
          rw [hvertices_def, Etingof.iteratedSimpleReflection_append,
              Etingof.iteratedSimpleReflection_replicate_eq_iterate]
          exact hp₀
        exact Etingof.parallel_reduce_and_recover hDynkin vertices hOrient
          ‹∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)› hSinks
          ρ₁ ρ₂ h₁ h₂ d (fun v => rfl)
          (fun v => by simp only [hd_def]; exact_mod_cast (hdim v).symm)
          p₀ hreflect
      · -- Full round: continue with new indecomposable rep
        right
        refine ⟨fun j => ?_, ρ', hFree', hFinite', hIndecomp', fun v => ?_⟩
        · rw [Function.iterate_succ', Function.comp_apply]; exact hnonneg j
        · rw [Function.iterate_succ', Function.comp_apply]; exact hDimVec' v

