import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5

/-!
# Proposition 6.6.6: Inverse Relationship of Reflection Functors

(1) If φ : ⊕_{j→i} V_j → V_i is surjective, then F⁻ᵢ F⁺ᵢ V ≅ V.
(2) If ψ : V_i → ⊕_{i→j} V_j is injective, then F⁺ᵢ F⁻ᵢ V ≅ V.

The proof uses the homomorphism theorem: when φ is surjective, K = ker φ embeds
in ⊕V_j, and then (⊕V_j)/K ≅ Im φ = V_i.

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

section Reversal

/-- A sink in Q becomes a source in the reversed quiver Q̄ᵢ.
All arrows into i in Q̄ᵢ correspond to arrows out of i in Q, which are empty
since i is a sink. -/
theorem Etingof.isSink_reversedAtVertex_isSource
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) :
    @Etingof.IsSource Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i j i at e
  unfold Etingof.ReversedAtVertexHom at e
  by_cases hj : j = i
  · simp only [hj, ite_true] at e
    exact (hi i).false e
  · simp only [hj, ite_false, ite_true] at e
    exact (hi j).false e

/-- A source in Q becomes a sink in the reversed quiver Q̄ᵢ.
All arrows out of i in Q̄ᵢ correspond to arrows into i in Q, which are empty
since i is a source. -/
theorem Etingof.isSource_reversedAtVertex_isSink
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i) :
    @Etingof.IsSink Q (Etingof.reversedAtVertex Q i) i := by
  intro j
  constructor
  intro e
  change Etingof.ReversedAtVertexHom Q i i j at e
  unfold Etingof.ReversedAtVertexHom at e
  by_cases hj : j = i
  · simp only [hj, ite_true] at e
    exact (hi i).false e
  · simp only [ite_true, hj, ite_false] at e
    exact (hi j).false e

end Reversal

section Iso

/-- An isomorphism between two quiver representations on the same quiver.
Consists of pointwise linear equivalences that commute with the representation maps. -/
structure Etingof.QuiverRepresentation.Iso
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) : Type _ where
  /-- Pointwise linear equivalences between vertex spaces -/
  equivAt : ∀ v : Q, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- Naturality: the diagram commutes -/
  naturality : ∀ {a b : Q} (e : a ⟶ b) (x : ρ₁.obj a),
    (equivAt b) (ρ₁.mapLinear e x) = ρ₂.mapLinear e ((equivAt a) x)

/-- The double reversal at vertex i recovers the original quiver instance.
This enables transporting representations from (Q̄ᵢ)̄ᵢ back to Q. -/
@[ext]
private theorem Quiver.ext' {V : Type*} {inst₁ inst₂ : Quiver V}
    (h : ∀ a b, @Quiver.Hom V inst₁ a b = @Quiver.Hom V inst₂ a b) :
    inst₁ = inst₂ := by
  cases inst₁; cases inst₂
  congr 1; funext a b; exact h a b

private theorem Etingof.reversedAtVertex_twice
    (Q : Type*) [DecidableEq Q] [inst : Quiver Q] (i : Q) :
    @Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i = inst := by
  apply Quiver.ext'
  intro a b
  change @Etingof.ReversedAtVertexHom Q _ (Etingof.reversedAtVertex Q i) i a b = (a ⟶ b)
  unfold Etingof.ReversedAtVertexHom
  split_ifs with ha hb hb
  all_goals (simp only [Etingof.reversedAtVertex, Etingof.ReversedAtVertexHom])
  all_goals (split_ifs <;> first | rfl | subst_vars <;> rfl | exact absurd rfl ‹_›)

/-- Transport a representation from the double-reversed quiver (Q̄ᵢ)̄ᵢ back to Q.

Reversing all arrows at vertex i twice recovers the original quiver. Vertex spaces
are unchanged; maps are transported through the canonical arrow identification. -/
noncomputable def Etingof.QuiverRepresentation.transportReversedTwice
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q}
    (ρ : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i)) :
    Etingof.QuiverRepresentation k Q :=
  Etingof.reversedAtVertex_twice Q i ▸ ρ

/-- If we can construct a `QuiverRepresentation.Iso` between ρ₁ and ρ₂ on
quiver instance `inst₁`, this gives an Iso between `(h ▸ ρ₁)` and `(h ▸ ρ₂)` on `inst₂`.
This is the key lemma for handling the `Eq.mpr` from `transportReversedTwice`. -/
private noncomputable def Etingof.QuiverRepresentation.transport_iso
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q]
    {inst₁ inst₂ : Quiver Q} (h : inst₁ = inst₂)
    {ρ₁ ρ₂ : @Etingof.QuiverRepresentation k Q _ inst₁}
    (iso : @Etingof.QuiverRepresentation.Iso k _ Q inst₁ ρ₁ ρ₂) :
    @Etingof.QuiverRepresentation.Iso k _ Q inst₂ (h ▸ ρ₁) (h ▸ ρ₂) := by
  subst h; exact iso

end Iso

/-- If φ is surjective at a sink, then applying F⁻ᵢ after F⁺ᵢ recovers V
up to isomorphism of representations.

The composition F⁻ᵢ(F⁺ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 1) -/
theorem Etingof.Proposition6_6_6_sink
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
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
  -- Mathematical argument:
  -- F⁺ᵢ(V)_j = V_j for j ≠ i, F⁺ᵢ(V)_i = ker(φ)
  -- F⁻ᵢ(F⁺ᵢ(V))_j = V_j for j ≠ i, F⁻ᵢ(F⁺ᵢ(V))_i = coker(ker(φ) ↪ ⊕V_j)
  -- By the first isomorphism theorem: ⊕V_j / ker(φ) ≅ im(φ) = V_i (since φ surjective)
  --
  -- Technical blocker: `transportReversedTwice` uses `▸` (Eq.mpr) which creates opaque
  -- terms. Building the Iso requires relating `(h ▸ ρ_dr).obj v` to `ρ.obj v`, but
  -- the Eq.mpr prevents definitional reduction, and propositional transport triggers
  -- Lean 4's synthesis check when two different Quiver instances are in scope.
  -- Infrastructure for a potential resolution (transport_iso, reversedAtVertex_twice,
  -- `{}` field annotations for instAddCommMonoid/instModule) is in place.
  -- A full resolution likely requires making the Quiver parameter of
  -- QuiverRepresentation explicit (not instance) to avoid the synthesis check.
  sorry

/-- If ψ is injective at a source, then applying F⁺ᵢ after F⁻ᵢ recovers V
up to isomorphism of representations.

The composition F⁺ᵢ(F⁻ᵢ(V)) lives on the double-reversed quiver (Q̄ᵢ)̄ᵢ, which is
canonically identified with Q via `transportReversedTwice`. Under this identification,
the resulting representation is isomorphic to the original.

(Etingof Proposition 6.6.6, part 2) -/
theorem Etingof.Proposition6_6_6_source
    {k : Type*} [Field k]
    {Q : Type*} [DecidableEq Q] [inst : Quiver Q]
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
  -- Mathematical argument (dual of sink case):
  -- F⁻ᵢ(V)_j = V_j for j ≠ i, F⁻ᵢ(V)_i = coker(ψ) = ⊕V_j / im(ψ)
  -- F⁺ᵢ(F⁻ᵢ(V))_j = V_j for j ≠ i, F⁺ᵢ(F⁻ᵢ(V))_i = ker(⊕V_j → coker(ψ))
  -- When ψ is injective: 0 → V_i →ψ ⊕V_j → coker(ψ) → 0 is exact
  -- So ker(⊕V_j → coker(ψ)) = im(ψ) ≅ V_i
  --
  -- Same technical blocker as the sink case.
  sorry
