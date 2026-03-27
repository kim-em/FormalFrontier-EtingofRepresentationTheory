import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Basic algebra existence

For a finite-dimensional algebra `A` over an algebraically closed field `k`,
there exists a basic algebra `B` that is Morita equivalent to `A`.

## Construction

1. `A` is Artinian, hence semiprimary: `A / rad(A)` is semisimple and `rad(A)`
   is nilpotent.
2. By Wedderburn–Artin, `A / rad(A) ≅ ∏ₜ Matₙₜ(Dₜ)` where `Dₜ` are division
   rings. Since `k` is algebraically closed, each `Dₜ = k`.
3. Extract one primitive idempotent `ē₁₁` per matrix block in `A / rad(A)`.
4. Lift these orthogonal idempotents to `A` using
   `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` (Corollary 9.1.3).
5. Set `e = ∑ eᵢ` and `B = eAe`. Then `B` is basic (each simple `B`-module
   is 1-dimensional over `k`) and Morita equivalent to `A` (via the
   progenerator `Ae`).

## Decomposition

The proof is decomposed into two helper lemmas:

* `exists_full_idempotent_basic_corner`: Existence of a full idempotent whose
  corner ring is basic. This uses Wedderburn–Artin over algebraically closed
  fields and idempotent lifting.

* `morita_equiv_of_full_idempotent`: The Morita equivalence between `A` and
  the corner ring `eAe` for a full idempotent `e` (one with `AeA = A`). This
  is the deep part of the proof, requiring construction of the functors
  `M ↦ eM` and `N ↦ Ae ⊗_{eAe} N` and verification they form an equivalence.
-/

universe u

namespace Etingof

/-! ## Full idempotent predicate -/

/-- An idempotent `e` in a ring `A` is **full** if the two-sided ideal it
generates is all of `A`, i.e., `AeA = A`. Full idempotents are precisely the
idempotents for which the corner ring `eAe` is Morita equivalent to `A`. -/
def IsFullIdempotent {A : Type*} [Ring A] (e : A) : Prop :=
  IsIdempotentElem e ∧ Ideal.span {a * e * b | (a : A) (b : A)} = ⊤

/-! ## Helper: Existence of full idempotent with basic corner ring

For a finite-dimensional algebra `A` over an algebraically closed field `k`,
there exists a full idempotent `e ∈ A` such that the corner ring `eAe` is basic.

Construction:
- A/Rad(A) is semisimple (Artinian + semiprimary)
- By Wedderburn–Artin: A/Rad(A) ≅ ∏ Mat_{n_i}(k)
- Pick one diagonal idempotent E_{11} per block → complete orthogonal system
- Lift to A via `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`
- Sum of lifted idempotents gives a full idempotent e
- eAe is basic: its simple modules correspond to k-lines (one per block) -/
private lemma exists_full_idempotent_basic_corner
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (e : A) (he : IsFullIdempotent e),
      @IsBasicAlgebra k _ (CornerRing (k := k) e) (CornerRing.instRing he.1)
        (CornerRing.instAlgebra he.1) := by
  sorry

/-! ## Corner module infrastructure for Morita equivalence

The "e-corner" of an A-module M is eM = {m ∈ M | e • m = m}. This has a natural
module structure over the corner ring eAe, and the assignment M ↦ eM is functorial. -/

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- The e-corner of a module M: the AddSubgroup {m ∈ M | e • m = m}. -/
private def eCorner {e : A} (_he : IsIdempotentElem e) (M : Type u)
    [AddCommGroup M] [Module A M] : AddSubgroup M where
  carrier := {m | e • m = m}
  zero_mem' := smul_zero e
  add_mem' {a b} ha hb := by change e • (a + b) = a + b; rw [smul_add, ha, hb]
  neg_mem' {a} ha := by change e • (-a) = -a; rw [smul_neg, ha]

/-- Elements of the e-corner satisfy e • m = m. -/
private lemma eCorner_prop {e : A} {he : IsIdempotentElem e} {M : Type u}
    [AddCommGroup M] [Module A M] (m : eCorner he M) : e • (m : M) = (m : M) :=
  m.prop

/-- Left multiplication by an element of eAe preserves the e-corner. -/
private lemma eCorner_smul_mem {e : A} (he : IsIdempotentElem e) {M : Type u}
    [AddCommGroup M] [Module A M] (r : CornerRing (k := k) e) (m : eCorner he M) :
    e • ((r : A) • (m : M)) = (r : A) • (m : M) := by
  rw [← mul_smul, cornerSubmodule_left_mul he r.prop]

/-- The CornerRing module structure on the e-corner. -/
private noncomputable def eCornerModule {e : A} (he : IsIdempotentElem e) (M : Type u)
    [AddCommGroup M] [Module A M] :
    letI := CornerRing.instRing (k := k) he
    Module (CornerRing (k := k) e) (eCorner he M) :=
  letI := CornerRing.instRing (k := k) he
  { smul := fun r m => ⟨(r : A) • (m : M), eCorner_smul_mem he r m⟩
    one_smul := fun m => Subtype.ext (show e • (m : M) = (m : M) from m.prop)
    mul_smul := fun r s m => Subtype.ext (mul_smul (r : A) (s : A) (m : M))
    smul_add := fun r m₁ m₂ => Subtype.ext (smul_add (r : A) (m₁ : M) (m₂ : M))
    smul_zero := fun r => Subtype.ext (smul_zero (r : A))
    add_smul := fun r s m => Subtype.ext (add_smul (r : A) (s : A) (m : M))
    zero_smul := fun m => Subtype.ext (zero_smul A (m : M)) }

/-- An A-linear map sends the e-corner of M to the e-corner of N. -/
private lemma eCorner_map_mem {e : A} (he : IsIdempotentElem e)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (m : eCorner he M) : e • f (m : M) = f (m : M) := by
  rw [← f.map_smul, eCorner_prop m]

open CategoryTheory

/-! ## Forward functor: M ↦ eM -/

/-- The forward functor of the Morita equivalence: M ↦ eM. -/
private noncomputable def cornerFunctor {e : A} (he : IsIdempotentElem e) :
    letI := CornerRing.instRing (k := k) he
    ModuleCat.{u} A ⥤ ModuleCat.{u} (CornerRing (k := k) e) :=
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
  { obj := fun M =>
      letI := eCornerModule (k := k) he M
      ModuleCat.of (CornerRing (k := k) e) (eCorner he M)
    map := fun {M N} f =>
      letI := eCornerModule (k := k) he M
      letI := eCornerModule (k := k) he N
      ModuleCat.ofHom
        { toFun := fun m => ⟨f.hom m.val, eCorner_map_mem he f.hom m⟩
          map_add' := fun m₁ m₂ => Subtype.ext (map_add f.hom m₁.val m₂.val)
          map_smul' := fun r m => Subtype.ext (by
            change f.hom ((r : A) • m.val) = (r : A) • f.hom m.val
            exact f.hom.map_smul r.val m.val) }
    map_id := fun M => by ext; rfl
    map_comp := fun f g => by ext; rfl }

/-! ## Fullness condition: AeM = M

When `e` is a full idempotent (`AeA = A`), every element of an `A`-module `M`
can be written as a sum of elements `a • (e • m)` for `a ∈ A, m ∈ M`.
This means every element lies in the A-span of `eM`. -/

/-- AeA = A implies 1 ∈ AeA, i.e., 1 = Σ aᵢ * e * bᵢ for some finite family. -/
private lemma one_mem_fullIdempotent_span {e : A} (he : IsFullIdempotent e) :
    (1 : A) ∈ Ideal.span {a * e * b | (a : A) (b : A)} := by
  rw [he.2]; exact Submodule.mem_top

/-- For a full idempotent e and any A-module M, every element lies in the
    A-span of eM = {e • n | n ∈ M}. -/
private lemma eCorner_spans {e : A} (he : IsFullIdempotent e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    m ∈ Submodule.span A (Set.range (fun n : M => e • n)) := by
  rw [show m = (1 : A) • m from (one_smul A m).symm]
  have h1 : (1 : A) ∈ Ideal.span {x | ∃ c d : A, c * e * d = x} := by
    rw [he.2]; exact Submodule.mem_top
  generalize (1 : A) = a at h1 ⊢
  induction h1 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, d, rfl⟩ := hx
    rw [mul_smul, mul_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨d • m, rfl⟩)
  | zero => simp
  | add x y _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ihx => rw [smul_assoc]; exact Submodule.smul_mem _ r ihx

/-- The corner functor is faithful when e is a full idempotent. -/
private lemma cornerFunctor_faithful {e : A} (he : IsFullIdempotent e) :
    letI := CornerRing.instRing (k := k) he.1
    (cornerFunctor (k := k) he.1).Faithful := by
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  constructor
  intro M N f g hfg
  ext m
  -- m is in the A-span of {e • n | n ∈ M} by fullness
  have hm := eCorner_spans he m
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    have hmem : e • (e • n) = e • n := by rw [← mul_smul, he.1.eq]
    exact congr_arg (fun φ => (φ ⟨e • n, hmem⟩ : eCorner he.1 N).val)
      (ModuleCat.hom_ext_iff.mp hfg)
  | zero => simp [map_zero]
  | add x y _ _ ihx ihy => simp [map_add, ihx, ihy]
  | smul a x _ ihx => simp [map_smul, ihx]

/-! ## Fullness of the corner functor -/

/-- The corner functor is full when `e` is a full idempotent: every eAe-linear
map `eM → eN` lifts to an A-linear map `M → N`. -/
private lemma cornerFunctor_full {e : A} (he : IsFullIdempotent e) :
    letI := CornerRing.instRing (k := k) he.1
    (cornerFunctor (k := k) he.1).Full := by
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  constructor
  intro M N φ
  sorry

/-! ## Essential surjectivity of the corner functor -/

private lemma cornerFunctor_essSurj {e : A} (he : IsFullIdempotent e) :
    letI := CornerRing.instRing (k := k) he.1
    (cornerFunctor (k := k) he.1).EssSurj := by
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he.1
  constructor
  intro N
  -- Extract carrier type and instances from the ModuleCat object
  let Nty : Type u := N
  letI : AddCommGroup Nty := N.isAddCommGroup
  letI : Module (CornerRing (k := k) e) Nty := N.isModule
  letI : Module k Nty := Module.compHom Nty (algebraMap k (CornerRing (k := k) e))
  -- Form the balanced tensor product A ⊗_{eAe} N
  -- T = A ⊗_k N with A-module structure via left multiplication
  letI : Module A (TensorProduct k A Nty) := TensorProduct.leftModule
  -- S = A-submodule generated by balanced relations {ar ⊗ n - a ⊗ rn | r ∈ eAe}
  let S : Submodule A (TensorProduct k A Nty) := Submodule.span A
    (Set.range fun (p : A × (CornerRing (k := k) e) × Nty) =>
      let ⟨a, r, n⟩ := p
      (a * (r : A)) ⊗ₜ[k] n - a ⊗ₜ[k] (r • n))
  -- Q = T/S has A-module structure
  let M : ModuleCat.{u} A := ModuleCat.of A (TensorProduct k A Nty ⧸ S)
  -- Claim: eM ≅ N as CornerRing-modules
  exact ⟨M, ⟨sorry⟩⟩

/-! ## Helper: Morita equivalence via full idempotent

For a ring `A` and a full idempotent `e` (i.e., `AeA = A`), `A` and `eAe` are
Morita equivalent. The corner functor `M ↦ eM` gives an equivalence of module
categories when `e` is full. -/
private lemma morita_equiv_of_full_idempotent
    {e : A} (he : IsFullIdempotent e) :
    @MoritaEquivalent A _ (CornerRing (k := k) e) (CornerRing.instRing he.1) := by
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  haveI hfull : (cornerFunctor (k := k) he.1).Full := cornerFunctor_full he
  haveI hfaith : (cornerFunctor (k := k) he.1).Faithful := cornerFunctor_faithful he
  haveI hesssurj : (cornerFunctor (k := k) he.1).EssSurj := cornerFunctor_essSurj he
  haveI : (cornerFunctor (k := k) he.1).IsEquivalence :=
    { faithful := hfaith, full := hfull, essSurj := hesssurj }
  exact ⟨(cornerFunctor (k := k) he.1).asEquivalence⟩

/-- **Basic algebra existence**: For a finite-dimensional algebra `A` over an
algebraically closed field `k`, there exists a basic algebra `B` (all simple
modules 1-dimensional) that is Morita equivalent to `A`.

This is the constructive core of Corollary 9.7.3(i). The witness `B` is
a corner ring `eAe` where `e` is a sum of lifted primitive idempotents,
one per isomorphism class of simple `A`-modules. -/
theorem exists_basic_morita_equivalent
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      IsBasicAlgebra k B ∧ MoritaEquivalent A B := by
  obtain ⟨e, he, hbasic⟩ := exists_full_idempotent_basic_corner k A
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he.1
  exact ⟨CornerRing (k := k) e,
    CornerRing.instRing he.1,
    CornerRing.instAlgebra he.1,
    CornerRing.instModuleFinite,
    hbasic,
    morita_equiv_of_full_idempotent he⟩

end Etingof
