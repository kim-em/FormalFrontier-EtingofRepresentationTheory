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
    · -- F⁺(V) is indecomposable: given complementary subreps W₁, W₂, show one is ⊥.
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
    (hρ : ρ.IsIndecomposable) :
    @Etingof.QuiverRepresentation.IsIndecomposable k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) ∨
    @Etingof.QuiverRepresentation.IsZero k _ Q
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) :=
  sorry
