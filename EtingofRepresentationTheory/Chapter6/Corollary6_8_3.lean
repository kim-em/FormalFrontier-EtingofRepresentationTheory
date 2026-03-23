import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Proposition6_6_6
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Corollary 6.8.3: Dimension Vector Determines Indecomposable Representation

If V, V' are indecomposable representations of a Dynkin quiver Q with d(V) = d(V'),
then V ≅ V'.

The proof: let i be minimal such that d(V⁽ⁱ⁾) = αₚ. Then d(V'⁽ⁱ⁾) = αₚ too,
so V⁽ⁱ⁾ = V'⁽ⁱ⁾. Both sequences satisfy surjectivity conditions, so applying
inverse functors gives V = V'.

Together with Corollary 6.8.2, this shows there are finitely many indecomposable
representations (one for each positive root).

## Mathlib correspondence

Requires Theorem 6.8.1, reflection functor invertibility (Proposition 6.6.6),
and quiver representation isomorphism. Not in Mathlib.

## Proof decomposition

The proof requires bridging integer-level dimension vector reflections (Theorem 6.8.1)
with representation-level reflection functors. The key missing infrastructure:

1. `simpleAt_iso`: Simple representations at the same vertex are isomorphic
2. `reflectionFunctors_reduce_to_simple`: Iterated reflection functors reduce an
   indecomposable representation to a simple one, following the reflection sequence
   from Theorem 6.8.1
3. Connecting the integer dimension vector to `Module.finrank` at each vertex
-/

open scoped Matrix

section Helpers

/-- A Dynkin quiver (orientation of a Dynkin diagram) has no self-loops at any vertex.
This follows because `IsDynkinDiagram` requires `adj i i = 0` and `IsOrientationOf`
requires no arrows when `adj i j ≠ 1`. -/
private lemma Etingof.noSelfLoop_of_dynkin_orientation
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (p : Fin n) :
    IsEmpty (@Quiver.Hom (Fin n) Q p p) :=
  hOrient.1 p p (by rw [hDynkin.2.1 p]; omega)

end Helpers

section SimpleAtIso

/-- Two representations that are simple at the same vertex are isomorphic.

If ρ₁ and ρ₂ are both simple at vertex p (meaning finrank 1 at p and finrank 0
elsewhere), then they are isomorphic as quiver representations.

The proof constructs pointwise linear equivalences:
- At p: both spaces are 1-dimensional, so a linear equivalence exists
- At j ≠ p: both spaces are 0-dimensional, so they are both trivial

Naturality follows because for any edge e : a ⟶ b, at least one of a, b differs
from p (assuming no self-loops, which holds for Dynkin quivers), making both
sides of the naturality square zero. -/
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
  -- Construct pointwise linear equivalences using equal finranks
  have hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v) := by
    intro v
    by_cases hv : v = p
    · subst hv; rw [h₁.1, h₂.1]
    · rw [h₁.2 v hv, h₂.2 v hv]
  -- Build the isomorphism
  refine ⟨⟨fun v => LinearEquiv.ofFinrankEq _ _ (hdim v), fun {a b} e x => ?_⟩⟩
  -- Naturality: for edge e : a ⟶ b, show equiv(ρ₁.map e x) = ρ₂.map e (equiv x)
  -- If a ≠ p, then ρ₁.obj a has finrank 0, so it's subsingleton, x = 0
  -- If b ≠ p, then both sides land in a subsingleton space
  by_cases ha : a = p <;> by_cases hb : b = p
  · -- a = p, b = p: self-loop case — vacuous since Dynkin quivers have no self-loops
    subst ha; subst hb; exact (hNoSelfLoop.false e).elim
  · -- a = p, b ≠ p: target space is zero-dimensional (subsingleton)
    haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _
  · -- a ≠ p, b = p: source space is zero-dimensional (subsingleton)
    haveI : Subsingleton (ρ₁.obj a) := by
      have hfr := h₁.2 a ha
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp [map_zero]
  · -- a ≠ p, b ≠ p: both sides in subsingleton space
    haveI : Subsingleton (ρ₂.obj b) := by
      have hfr := h₂.2 b hb
      exact Module.subsingleton_of_rank_zero
        (by rw [← @Module.finrank_eq_rank k]; exact_mod_cast hfr)
    exact Subsingleton.elim _ _

/-- An indecomposable representation whose dimension vector equals a simple root
is simple at the corresponding vertex.

If ρ is indecomposable and has finrank 1 at vertex p and finrank 0 at all other
vertices, then ρ.IsSimpleAt p. This is immediate from the definition. -/
private lemma Etingof.indecomposable_simpleRoot_isSimpleAt
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (p : Q)
    (hdim_p : Module.finrank k (ρ.obj p) = 1)
    (hdim_other : ∀ j, j ≠ p → Module.finrank k (ρ.obj j) = 0) :
    ρ.IsSimpleAt p :=
  ⟨hdim_p, hdim_other⟩

end SimpleAtIso

section ReflectionFunctorChain

/-- Two indecomposable representations with dimension vector equal to a simple root αₚ
are isomorphic, provided there are no self-loops at p.

This is the base case of the reflection functor chain: when d(V) = αₚ,
V has finrank 1 at p and 0 elsewhere (i.e., V is simple at p).
Two representations simple at the same vertex are isomorphic by `simpleAt_iso`. -/
private lemma Etingof.indecomposable_simpleRoot_iso
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (_hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (p : Fin n)
    (hNoSelfLoop : IsEmpty (@Quiver.Hom (Fin n) Q p p))
    (hd₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = Etingof.simpleRoot n p v)
    (hd₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = Etingof.simpleRoot n p v) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) := by
  -- Both are simple at p
  have h₁s : ρ₁.IsSimpleAt p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₁ p; simp [Etingof.simpleRoot] at this; omega
    · have := hd₁ j; simp [Etingof.simpleRoot, show p ≠ j from Ne.symm hj] at this; omega
  have h₂s : ρ₂.IsSimpleAt p := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := hd₂ p; simp [Etingof.simpleRoot] at this; omega
    · have := hd₂ j; simp [Etingof.simpleRoot, show p ≠ j from Ne.symm hj] at this; omega
  exact Etingof.simpleAt_iso ρ₁ ρ₂ p hNoSelfLoop h₁s h₂s

/-- Iterated reflection functors reduce an indecomposable representation to a simple
representation, following the reflection sequence from Theorem 6.8.1.

Given two indecomposable representations ρ₁, ρ₂ with the same dimension vector d,
and a sequence of vertices that reduces d to a simple root αₚ via iterated simple
reflections, we conclude ρ₁ ≅ ρ₂. The proof works by applying the corresponding
reflection functors to both representations, using Proposition 6.6.6 to recover.

## Proof structure

**Base case** (`vertices = []`): d is already a simple root αₚ. Both representations
are simple at p, so isomorphic by `simpleAt_iso`. ✓ Proved below.

**Inductive step** (`vertices = i :: rest`): Apply reflection functor F⁺ᵢ to both
representations. By Prop 6.6.7 they remain indecomposable, by Prop 6.6.8 their
dimension vectors transform by sᵢ, and by induction they're isomorphic on
`reversedAtVertex Q i`. Then Prop 6.6.6 recovers the isomorphism on Q.

## Remaining blockers

1. **Type-changing iteration**: Each reflection functor changes the quiver from Q
   to `reversedAtVertex Q i`, producing a chain of different Lean types. The
   induction hypothesis must apply to the reversed quiver, requiring a
   universally-quantified statement over all orientations of the same graph.

2. **Vertex-sink alignment**: The vertices from Theorem 6.8.1 (via `exists_good_vertex`)
   are chosen to reduce the integer dimension vector, but may not be sinks in the
   current quiver Q. The book's proof uses the Coxeter element ordering, which
   guarantees each vertex is a sink at the appropriate step. Aligning these two
   approaches requires Coxeter element infrastructure.

3. **`Proposition6_6_7_source` (sorry'd)**: Preserving indecomposability through
   source reflection functors is not yet proven (1 sorry in Proposition6_6_7.lean). -/
private lemma Etingof.reflectionFunctors_reduce_and_recover
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : ρ₁.IsIndecomposable)
    (h₂ : ρ₂.IsIndecomposable)
    (hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v))
    (vertices : List (Fin n)) (p : Fin n)
    (hreflect : Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices
        (fun v => (Module.finrank k (ρ₁.obj v) : ℤ)) = Etingof.simpleRoot n p) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) := by
  -- Base case: when vertices = [], d is already a simple root
  -- The inductive case requires type-changing iteration infrastructure (see blockers above)
  cases vertices with
  | nil =>
    -- vertices = [], so iteratedSimpleReflection ... [] d = d = simpleRoot n p
    simp only [Etingof.iteratedSimpleReflection, List.foldl_nil] at hreflect
    have hNoSelfLoop := Etingof.noSelfLoop_of_dynkin_orientation hDynkin hOrient p
    have hd₁ : ∀ v, (Module.finrank k (ρ₁.obj v) : ℤ) = Etingof.simpleRoot n p v :=
      fun v => congr_fun hreflect v
    have hd₂ : ∀ v, (Module.finrank k (ρ₂.obj v) : ℤ) = Etingof.simpleRoot n p v :=
      fun v => by rw [← hdim v]; exact hd₁ v
    exact Etingof.indecomposable_simpleRoot_iso hDynkin ρ₁ ρ₂ p hNoSelfLoop hd₁ hd₂
  | cons i rest =>
    -- Inductive case: apply reflection functor at vertex i, then recurse
    -- BLOCKED: requires type-changing iteration + vertex-sink alignment
    -- (see docstring for detailed blockers)
    sorry

end ReflectionFunctorChain

section TitsFormBound

/-- The Tits form of the dimension vector of an indecomposable representation of a
Dynkin quiver satisfies B(d, d) ≤ 2.

## Proof strategy (from the book)

The proof uses Ringel's homological formula for hereditary algebras:
  dim Hom(V, V) - dim Ext¹(V, V) = ½ B(d(V), d(V))

For V indecomposable over an algebraically closed field k:
  - dim End(V) = 1 by Schur's lemma (End(V) is a local algebra with
    End(V)/rad(End(V)) ≅ k, and for finite-dimensional indecomposables
    over algebraically closed fields, End(V) ≅ k)
  - dim Ext¹(V, V) ≥ 0

This gives ½ B(d, d) = 1 - dim Ext¹(V, V) ≤ 1, so B(d, d) ≤ 2.

## Blockers

1. **Ext groups**: No formalization of Ext¹ for quiver representations
   (or more generally for modules over path algebras) exists in this project
   or in Mathlib.

2. **Homological formula**: The identity relating Hom, Ext¹, and the Euler/Tits
   form requires the path algebra to be hereditary (global dimension ≤ 1),
   which requires showing quivers without oriented cycles have hereditary
   path algebras.

3. **Schur's lemma variant**: While Schur's lemma for simple modules is standard,
   the result that End(V) ≅ k for indecomposable finite-dimensional V over an
   algebraically closed field requires the Fitting lemma / Krull-Schmidt theory.

## Alternative approach (bypasses Ext entirely)

The book's proof of Corollary 6.8.2 proves B(d,d) = 2 (not just ≤ 2) by a
representation-level reduction: apply reflection functors along the Coxeter element
until reaching a simple representation, then use `iteratedSimpleReflection_preserves_bilinearForm`
to conclude B(d,d) = B(αₚ,αₚ) = 2. This approach requires the same Coxeter element
infrastructure as `reflectionFunctors_reduce_and_recover` (type-changing iteration,
vertex-sink alignment) but avoids Ext groups completely. If that infrastructure is
built, this lemma becomes a direct corollary and can be eliminated.

The Tits form of the dimension vector of an indecomposable representation of a
Dynkin quiver satisfies B(d, d) ≤ 2.

This follows from the stronger result `indecomposable_bilinearForm_eq_two` (B = 2 exactly),
proved via representation-level Coxeter iteration in `CoxeterInfrastructure.lean`.
The ≤ 2 form is kept for backward compatibility with the existing proof of `Corollary6_8_3`. -/
private lemma Etingof.indecomposable_titsForm_le_two
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (ρ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hρ : ρ.IsIndecomposable) :
    dotProduct (fun v => (Module.finrank k (ρ.obj v) : ℤ))
      ((Etingof.cartanMatrix n adj).mulVec (fun v => (Module.finrank k (ρ.obj v) : ℤ))) ≤ 2 :=
  le_of_eq (Etingof.indecomposable_bilinearForm_eq_two hDynkin hOrient ρ hρ)

end TitsFormBound

/-- Indecomposable representations of a Dynkin quiver are determined (up to isomorphism)
by their dimension vectors.

If two indecomposable representations ρ₁, ρ₂ of a quiver on Fin n (with Dynkin
adjacency matrix) have the same dimension at every vertex, then they are isomorphic
as quiver representations.
(Etingof Corollary 6.8.3) -/
theorem Etingof.Corollary6_8_3
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {k : Type*} [Field k]
    {Q : Quiver (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
    [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
    [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)]
    (h₁ : ρ₁.IsIndecomposable)
    (h₂ : ρ₂.IsIndecomposable)
    (hdim : ∀ v, Module.finrank k (ρ₁.obj v) = Module.finrank k (ρ₂.obj v)) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin n) Q ρ₁ ρ₂) := by
  -- Step 1: Extract the dimension vector as an integer-valued function
  let d : Fin n → ℤ := fun v => (Module.finrank k (ρ₁.obj v) : ℤ)
  -- Step 2: The dimension vector is non-negative
  have hd_pos : ∀ i, 0 ≤ d i := fun i => Int.natCast_nonneg _
  -- Step 3: The dimension vector is nonzero (since ρ₁ is indecomposable, some space is nontrivial)
  have hd_nonzero : d ≠ 0 := by
    obtain ⟨⟨v, hv⟩, _⟩ := h₁
    intro h
    have : d v = 0 := congr_fun h v
    simp only [d, Int.natCast_eq_zero] at this
    rw [Module.finrank_eq_zero_iff_of_free (R := k)] at this
    exact not_nontrivial_iff_subsingleton.mpr this hv
  -- Step 4: The dimension vector is a positive root (B(d,d) = 2)
  -- Lower bound: B(d,d) ≥ 2 from positive definiteness + evenness (Lemma 6.4.2)
  -- Upper bound: B(d,d) ≤ 2 from indecomposability (requires Ext group infrastructure)
  have hd_root : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2 := by
    have hlb : 2 ≤ dotProduct d ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d) :=
      Etingof.posdef_min_value hDynkin d hd_nonzero
    have hub : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) ≤ 2 :=
      Etingof.indecomposable_titsForm_le_two hDynkin hOrient ρ₁ h₁
    unfold Etingof.cartanMatrix at hub ⊢
    omega
  -- Step 5: By Theorem 6.8.1, there exists a sequence of reflections reducing d to a simple root
  obtain ⟨vertices, p, hreflect⟩ := Etingof.Theorem6_8_1 hDynkin d hd_pos hd_nonzero hd_root
  -- Step 6: Use the reflection functor chain to show ρ₁ ≅ ρ₂
  exact Etingof.reflectionFunctors_reduce_and_recover hDynkin hOrient ρ₁ ρ₂ h₁ h₂ hdim
    vertices p hreflect
