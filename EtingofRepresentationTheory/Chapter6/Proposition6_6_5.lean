import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Proposition 6.6.5: Surjectivity/Injectivity at Sinks and Sources

Let Q be a quiver and V an indecomposable representation.

(1) If i is a sink, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    φ : ⊕_{j→i} V_j → V_i is surjective.

(2) If i is a source, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    ψ : V_i → ⊕_{i→j} V_j is injective.

The proof uses decomposition: if φ is not surjective, complement of Im(φ) gives a
direct sum decomposition, contradicting indecomposability unless V is the simple
representation at i.

## Mathlib correspondence

Requires quiver representation infrastructure (indecomposable representations,
dimension vectors). Not directly available in Mathlib.
-/

/-- Over a field, any `AddCommMonoid` module is actually an `AddCommGroup`, with negation
given by scalar multiplication by `-1`. This bridges `QuiverRepresentation` (which uses
`AddCommMonoid`) and APIs like `Submodule.exists_isCompl` (which require `AddCommGroup`).
The resulting `AddCommGroup` extends the existing `AddCommMonoid` — no diamond. -/
noncomputable def Etingof.addCommGroupOfField {k : Type*} [Field k] {M : Type*}
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

/-- Any submodule of a module over a field has a complement. This wraps
`Submodule.exists_isCompl` by constructing the required `AddCommGroup` instance. -/
private noncomputable def Etingof.existsIsCompl_repr
    {k : Type*} [Field k] {M : Type*} [AddCommMonoid M] [Module k M]
    (p : Submodule k M) : ∃ q : Submodule k M, IsCompl p q := by
  letI : AddCommGroup M := Etingof.addCommGroupOfField (k := k)
  exact Submodule.exists_isCompl p

/-- A quiver representation is **indecomposable** if it is nonzero and cannot be
written as a direct sum of two nonzero sub-representations. -/
def Etingof.QuiverRepresentation.IsIndecomposable
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W₁ W₂ : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.mapLinear e x ∈ W₁ b) →
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.mapLinear e x ∈ W₂ b) →
    (∀ v, IsCompl (W₁ v) (W₂ v)) →
    (∀ v, W₁ v = ⊥) ∨ (∀ v, W₂ v = ⊥)

/-- A quiver representation is the **simple representation at vertex i** if
the space at i is one-dimensional and all other spaces are zero. -/
def Etingof.QuiverRepresentation.IsSimpleAt
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] : Prop :=
  Module.finrank k (ρ.obj i) = 1 ∧ ∀ j, j ≠ i → Module.finrank k (ρ.obj j) = 0

/-- The canonical map ψ : V_i → ⊕_{i→j} V_j at a source vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sourceMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) := by
  classical
  exact ∑ a : Etingof.ArrowsOutOf Q i,
    (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a).comp (ρ.mapLinear a.2)

/-- For an indecomposable representation at a sink, either V is the simple
representation at i, or the canonical map ⊕_{j→i} V_j → V_i is surjective.
(Etingof Proposition 6.6.5, part 1)

The proof constructs complementary sub-representations from the range of the
sink map and uses indecomposability. See the module docstring for details. -/
theorem Etingof.Proposition6_6_5_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hi : Etingof.IsSink Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Surjective (ρ.sinkMap i) :=
  sorry

/-- For an indecomposable representation at a source, either V is the simple
representation at i, or the canonical map V_i → ⊕_{i→j} V_j is injective.
(Etingof Proposition 6.6.5, part 2)

The proof is dual to the sink case, using the kernel of the source map. -/
theorem Etingof.Proposition6_6_5_source
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hi : Etingof.IsSource Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Injective (ρ.sourceMap i) :=
  sorry
