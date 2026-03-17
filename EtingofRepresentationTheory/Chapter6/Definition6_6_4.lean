import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_2
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Definition 6.6.4: Reflection Functor F⁻ᵢ (at a Source)

Let Q be a quiver and i ∈ Q be a source. Let ψ : V_i → ⊕_{i→j} V_j be the
canonical map. The reflection functor F⁻ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁻ᵢ(V)_k = V_k for k ≠ i
- F⁻ᵢ(V)_i = Coker(ψ) = (⊕_{i→j} V_j) / Im ψ

All maps now pointing into i are replaced by the compositions of the inclusions
V_k → ⊕_{i→j} V_j with the natural quotient map ⊕_{i→j} V_j → (⊕_{i→j} V_j)/Im ψ.

## Mathlib correspondence

BGP reflection functors are not in Mathlib. The cokernel-based construction uses
`Submodule.mkQ` for quotient maps and `LinearMap.range` for image.

The cokernel construction (quotient module) requires `AddCommGroup` and `Ring`
structure. The definition requires `[CommRing k]` and constructs compatible
`AddCommGroup` instances internally using scalar multiplication by `-1`.
-/

/-- The type indexing the direct sum for F⁻ᵢ: pairs (j, h) where h : i ⟶ j is an arrow
out of the source vertex i. -/
def Etingof.ArrowsOutOf (V : Type*) [Quiver V] (i : V) :=
  Σ (j : V), (i ⟶ j)

/-- Over a commutative ring, any `AddCommMonoid` module is actually an `AddCommGroup`,
with negation given by scalar multiplication by `-1`. The resulting `AddCommGroup`
extends the existing `AddCommMonoid` — no diamond.

This is the same construction as `addCommGroupOfField` (Proposition 6.6.5) but
generalized to `CommRing`. -/
private noncomputable def Etingof.addCommGroupOfRing {k : Type*} [CommRing k] {M : Type*}
    [inst : AddCommMonoid M] [Module k M] : AddCommGroup M :=
  { inst with
    neg := fun x => (-1 : k) • x
    zsmul := fun n x => (n : k) • x
    neg_add_cancel := fun a => by
      change (-1 : k) • a + a = 0
      nth_rw 2 [show a = (1 : k) • a from (one_smul k a).symm]
      rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul_zero' := fun a => by simp [zero_smul]
    zsmul_succ' := fun n a => by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    zsmul_neg' := fun n a => by
      simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_neg, smul_smul, neg_one_mul] }

/-- The reflection functor F⁻ᵢ at a source vertex i, sending representations of Q
to representations of Q̄ᵢ (the quiver with arrows at i reversed).

At vertex k ≠ i, F⁻ᵢ(ρ)_k = ρ_k (unchanged).
At vertex i, F⁻ᵢ(ρ)_i = coker(ψ) where ψ : ρ_i → ⊕_{i→j} ρ_j is the sum of
the representation maps ρ(h) for each arrow h : i → j.

The linear maps in the reversed quiver Q̄ᵢ are:
- For arrows not touching i: unchanged from ρ
- For arrows into i in Q̄ᵢ (= reversed arrows out of i in Q):
  ρ_j → ⊕_{i→j} ρ_j → coker(ψ) (inclusion then quotient)

(Etingof Definition 6.6.4) -/
noncomputable def Etingof.reflectionFunctorMinus
    {k : Type*} [CommRing k]
    (V : Type*) [inst : DecidableEq V] [Quiver V]
    (i : V) (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [Fintype (Etingof.ArrowsOutOf V i)] :
    @Etingof.QuiverRepresentation k V _ (Etingof.reversedAtVertex V i) := by
  classical
  -- Upgrade vertex modules to AddCommGroup (extends existing AddCommMonoid, no diamond)
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  -- The direct sum also gets AddCommGroup (extends its existing AddCommMonoid)
  letI instACG_DS : AddCommGroup (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  -- ψ : V_i → ⊕_{i→j} V_j, the canonical source map
  let ψ : ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) :=
    ∑ a : Etingof.ArrowsOutOf V i,
      (DirectSum.lof k (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1) a).comp (ρ.mapLinear a.2)
  -- Cokernel type: (⊕_{i→j} V_j) / Im(ψ)
  let CokerType := (DirectSum (Etingof.ArrowsOutOf V i) (fun a => ρ.obj a.1)) ⧸ LinearMap.range ψ
  -- Use Decidable.casesOn with the [DecidableEq V] instance to construct
  -- obj, AddCommMonoid, and Module coherently. All three fields share the same
  -- Decidable instance, so the type-level case-split computes correctly.
  let dp : ∀ v, Decidable (v = i) := fun v => inst v i
  let objAt : ∀ v, Decidable (v = i) → Type _ :=
    fun v d => @Decidable.casesOn _ (fun _ => Type _) d
      (fun _ => ρ.obj v) (fun _ => CokerType)
  let acmAt : ∀ v d, AddCommMonoid (objAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => AddCommMonoid (objAt v d)) d
      (fun _ => ρ.instAddCommMonoid v)
      (fun _ => Submodule.Quotient.addCommGroup (p := LinearMap.range ψ) |>.toAddCommMonoid)
  let modAt : ∀ v d, @Module k (objAt v d) _ (acmAt v d) :=
    fun v d => @Decidable.casesOn _ (fun d => @Module k (objAt v d) _ (acmAt v d)) d
      (fun _ => ρ.instModule v)
      (fun _ => Submodule.Quotient.module (LinearMap.range ψ))
  exact @Etingof.QuiverRepresentation.mk k V _ (Etingof.reversedAtVertex V i)
    (fun v => objAt v (dp v))
    (fun v => acmAt v (dp v))
    (fun v => modAt v (dp v))
    (fun {a b} (e : Etingof.ReversedAtVertexHom V i a b) => by
      change Etingof.ReversedAtVertexHom V i a b at e
      unfold Etingof.ReversedAtVertexHom at e
      by_cases ha : a = i
      · by_cases hb : b = i
        · -- a = i, b = i: self-loop; vacuous since i is a source (no arrows into i)
          simp only [ha, hb] at e; exact ((hi i).false e).elim
        · -- a = i, b ≠ i: arrow b → i in Q; vacuous since i is a source
          simp only [ha, hb, ite_true, ite_false] at e
          exact ((hi b).false e).elim
      · by_cases hb : b = i
        · -- a ≠ i, b = i: reversed arrow (i ⟶ a in Q), map is ρ_a → ⊕ → coker(ψ)
          simp only [ha, hb, ite_false, ite_true] at e
          -- Beta-reduce and generalize to make Decidable.casesOn reduce
          change objAt a (dp a) →ₗ[k] objAt b (dp b)
          revert e
          generalize dp a = da; generalize dp b = db
          cases da with
          | isTrue h => exact absurd h ha
          | isFalse _ =>
            cases db with
            | isFalse h => exact absurd hb h
            | isTrue _ =>
              intro e
              exact (Submodule.mkQ (LinearMap.range ψ)).comp
                (DirectSum.lof k (Etingof.ArrowsOutOf V i)
                  (fun a => ρ.obj a.1) ⟨a, e⟩)
        · -- a ≠ i, b ≠ i: unchanged arrow
          simp only [ha, hb] at e
          change objAt a (dp a) →ₗ[k] objAt b (dp b)
          revert e
          generalize dp a = da; generalize dp b = db
          cases da with
          | isTrue h => exact absurd h ha
          | isFalse _ =>
            cases db with
            | isTrue h => exact absurd h hb
            | isFalse _ =>
              intro e
              exact ρ.mapLinear e)
