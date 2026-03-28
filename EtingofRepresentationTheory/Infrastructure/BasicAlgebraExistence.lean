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
import Mathlib.RingTheory.Idempotents

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
  uses faithfulness (proven), fullness and essential surjectivity (both via the
  evaluation isomorphism `Ae ⊗_{eAe} eM ≅ M`) of the corner functor `M ↦ eM`.

## Proof status

Three sorrys remain, each requiring substantial algebraic infrastructure:

1. `exists_full_idempotent_basic_corner`: Decomposed into sub-steps (Artinian,
   Wedderburn–Artin, idempotent extraction, lifting, fullness + basicness).
   Steps 1-4 use available Mathlib infrastructure; steps 5-6 need manual work.

2. `cornerFunctor_full`: Requires constructing the lift of an eAe-linear map
   eM → eN to an A-linear map M → N. Standard proof goes through the
   evaluation isomorphism `Ae ⊗_{eAe} eM ≅ M`.

3. `cornerFunctor_essSurj`: Requires showing `e(A ⊗_{eAe} N) ≅ N`, the other
   direction of the evaluation isomorphism.
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

### Proof strategy (uses available Mathlib infrastructure)

1. `IsArtinianRing.of_finite k A` — A is Artinian
2. `IsSemiprimaryRing` instance (automatic from Artinian) — rad(A) nilpotent,
   A/rad(A) semisimple
3. `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` — Wedderburn–Artin
   decomposition of A/rad(A) ≅ ∏ Mₙᵢ(k)
4. Extract one diagonal idempotent E₁₁ per matrix block → complete orthogonal
   idempotents in A/rad(A)
5. `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` — lift to A
6. Sum of lifted idempotents is full (AeA = A) and eAe is basic -/
lemma exists_full_idempotent_basic_corner
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

/-! ## Corner projection helpers -/

/-- Composing e with itself gives the same action (idempotency on modules). -/
private lemma eCorner_smul_of_idem {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    e • (e • m) = e • m := by
  rw [← mul_smul, he.eq]

/-- The "projection" map m ↦ e•m lands in the e-corner. -/
private def toECorner {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    eCorner he M :=
  ⟨e • m, eCorner_smul_of_idem he m⟩

/-- The projection m ↦ e•m is additive. -/
private lemma toECorner_add {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m₁ m₂ : M) :
    toECorner he (m₁ + m₂) = toECorner he m₁ + toECorner he m₂ :=
  Subtype.ext (smul_add e m₁ m₂)

/-- Projection on elements already in eM is the identity. -/
private lemma toECorner_of_mem {e : A} {he : IsIdempotentElem e}
    {M : Type u} [AddCommGroup M] [Module A M] (m : eCorner he M) :
    toECorner he (m : M) = m :=
  Subtype.ext (eCorner_prop m)

/-- The projection interacts with eAe-multiplication:
    e • (r • m) = (r : A) • (e • m) when r ∈ eAe and m is any element. -/
private lemma toECorner_cornerRing_smul {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M]
    (r : CornerRing (k := k) e) (m : M) :
    toECorner he ((r : A) • m) =
      letI := eCornerModule (k := k) he M
      r • toECorner he m := by
  apply Subtype.ext
  change e • ((r : A) • m) = (r : A) • (e • m)
  rw [← mul_smul, ← mul_smul]
  congr 1
  rw [cornerSubmodule_left_mul he r.prop, cornerSubmodule_right_mul he r.prop]

/-! ## Fullness of the corner functor

The proof of fullness requires constructing, for each eAe-linear map φ : eM → eN,
an A-linear lift f : M → N. The standard approach uses the evaluation isomorphism
`Ae ⊗_{eAe} eM ≅ M`. Since AeA = A, every module element can be written as a
finite sum Σ aᵢ • (e • mᵢ), and the lift is determined by A-linearity and
agreement with φ on eM.

### Detailed proof strategy

The evaluation map `eval_M : Ae ⊗_{eAe} eM → M` sending `ae ⊗ m ↦ a · m` is an
isomorphism when e is full. Then:

* **Fullness**: `Hom_A(M, N) ≅ Hom_A(Ae ⊗ eM, Ae ⊗ eN) ≅ Hom_{eAe}(eM, eN)`
  via the tensor-hom adjunction.

* **Essential surjectivity**: For any eAe-module N, the A-module
  `M := A ⊗_{eAe} N` has `eM ≅ N` (by the evaluation isomorphism applied
  to `Ae ⊗_{eAe} N`).

Both proofs reduce to showing `eval_M` is an isomorphism:
- Surjectivity of eval_M follows from `eCorner_spans` (already proved).
- Injectivity of eval_M requires showing the balanced tensor product
  relations are the only kernel, which uses the fullness of e.
-/

private lemma cornerFunctor_full {e : A} (he : IsFullIdempotent e) :
    letI := CornerRing.instRing (k := k) he.1
    (cornerFunctor (k := k) he.1).Full := by
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  constructor
  intro M N φ
  -- Extract finite decomposition: 1 = Σ σ(a,b) • (a * e * b) from fullness
  have hspan : (1 : A) ∈ Submodule.span A (Set.range (fun p : A × A => p.1 * e * p.2)) := by
    suffices h : Submodule.span A (Set.range (fun p : A × A => p.1 * e * p.2)) = ⊤ from
      h ▸ Submodule.mem_top
    have : Set.range (fun p : A × A => p.1 * e * p.2) =
        {x | ∃ a b : A, a * e * b = x} := by
      ext x; constructor
      · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
      · rintro ⟨a, b, rfl⟩; exact ⟨⟨a, b⟩, rfl⟩
    rw [this]; exact he.2
  obtain ⟨σ, hσ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  -- hσ : σ.sum (fun p c => c • (p.1 * e * p.2)) = 1
  -- Note: Finsupp.sum σ g = ∑ p ∈ σ.support, g p (σ p)
  -- So hσ says: ∑ p ∈ σ.support, σ p • (p.1 * e * p.2) = 1
  -- i.e., ∑ p, (σ p * p.1) * e * p.2 = 1
  letI := eCornerModule (k := k) he.1 M
  letI := eCornerModule (k := k) he.1 N
  -- Define the lift: f(m) = ∑ p, (σ p * p.1) • ↑(φ (toECorner he.1 (p.2 • m)))
  let liftFun : M → N := fun m =>
    ∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m)) : eCorner he.1 N).val
  have lift_add : ∀ m₁ m₂ : M, liftFun (m₁ + m₂) = liftFun m₁ + liftFun m₂ := by
    intro m₁ m₂
    show (∑ p ∈ σ.support, (σ p * p.1) •
        (φ (toECorner he.1 (p.2 • (m₁ + m₂))) : eCorner he.1 N).val) =
      (∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m₁)) : eCorner he.1 N).val) +
      (∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m₂)) : eCorner he.1 N).val)
    rw [← Finset.sum_add_distrib]
    congr 1; ext p
    rw [smul_add, toECorner_add, map_add, AddSubgroup.coe_add, smul_add]
  -- Key identity: ∑ σ p * (p.1 * e * p.2) = 1
  have hσ1 : ∑ p ∈ σ.support, σ p * (p.1 * e * p.2) = 1 := by
    have := hσ; simp only [Finsupp.sum, smul_eq_mul] at this; exact this
  -- Coercion helper: (r •_{eAe} x : eCorner).val = (r : A) • (x : N)
  have coe_smul : ∀ (r : CornerRing (k := k) e) (x : eCorner he.1 N),
      ((r • x : eCorner he.1 N) : N) = (r : A) • (x : N) := fun _ _ => rfl
  -- Helper for the generator case: liftFun on e • n
  have lift_eCorner : ∀ (n : M),
      liftFun (e • n) = (φ (toECorner he.1 n) : eCorner he.1 N).val := by
    intro n
    show ∑ p ∈ σ.support, (σ p * p.1) •
        (φ (toECorner he.1 (p.2 • (e • n))) : eCorner he.1 N).val =
      (φ (toECorner he.1 n) : eCorner he.1 N).val
    -- toECorner(p.2 • (e • n)) = ⟨e * p.2 * e • (e • n), ...⟩ = (e*p.2*e) •_{eAe} toECorner(n)
    -- since e • (p.2 • (e • n)) = (e * p.2 * e) • n [using e²=e twice]
    -- and toECorner(n) = ⟨e • n, ...⟩
    have h1 : ∀ p : A × A, toECorner he.1 (p.2 • (e • n)) =
        (⟨e * p.2 * e, ⟨p.2, rfl⟩⟩ : CornerRing (k := k) e) • toECorner he.1 n := by
      intro p; apply Subtype.ext
      show e • (p.2 • (e • n)) = (e * p.2 * e) • (e • n)
      rw [mul_smul, mul_smul, eCorner_smul_of_idem he.1 n]
    simp only [← mul_smul]
    -- Sum: Σ σp * p.1 * (e * p.2 * e) = (Σ σp * (p.1 * e * p.2)) * e = 1 * e = e
    conv_lhs => arg 1; arg 2; ext p; rw [show σ p * p.1 * (e * p.2 * e) =
      σ p * (p.1 * e * p.2) * e by simp only [mul_assoc]]
    rw [← Finset.sum_mul, hσ1, one_mul]
    exact (φ (toECorner he.1 n)).prop
  have lift_smul : ∀ (r : A) (m : M), liftFun (r • m) = r • liftFun m := by
    -- Quantify r inside the induction so the smul case has IH for all r
    suffices key : ∀ m, m ∈ Submodule.span A (Set.range (fun n : M => e • n)) →
        ∀ r : A, liftFun (r • m) = r • liftFun m from
      fun r m => key m (eCorner_spans he m) r
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      intro r
      -- Goal: liftFun(r • (e • n)) = r • liftFun(e • n)
      rw [← mul_smul, lift_eCorner]
      -- Goal: liftFun((r * e) • n) = r • φ(toECorner n).val
      -- Expand liftFun from definition
      show ∑ p ∈ σ.support, (σ p * p.1) •
          (φ (toECorner he.1 (p.2 • ((r * e) • n))) : eCorner he.1 N).val =
        r • (φ (toECorner he.1 n) : eCorner he.1 N).val
      simp_rw [← mul_smul (α := A)]
      -- toECorner((p.2 * (r * e)) • n) = ⟨e*(p.2*r)*e, _⟩ •_{eAe} toECorner(n)
      have h_toE2 : ∀ p : A × A,
          toECorner he.1 ((p.2 * (r * e)) • n) =
            (⟨e * (p.2 * r) * e, ⟨p.2 * r, rfl⟩⟩ : CornerRing (k := k) e) •
              toECorner he.1 n := by
        intro p; apply Subtype.ext
        show e • ((p.2 * (r * e)) • n) = (e * (p.2 * r) * e) • (e • n)
        rw [← mul_smul, ← mul_smul]
        congr 1
        simp only [mul_assoc]
        rw [he.1.eq]
      simp only [h_toE2, map_smul, coe_smul, ← mul_smul, ← Finset.sum_smul]
      -- Sum: ∑ σ_p * p.1 * (e * (p.2 * r) * e) = r * e
      have hsum_eq : ∑ p ∈ σ.support, σ p * p.1 * (e * (p.2 * r) * e) = r * e := by
        have : ∀ p ∈ σ.support, σ p * p.1 * (e * (p.2 * r) * e) =
            σ p * (p.1 * e * p.2) * r * e := fun p _ => by simp only [mul_assoc]
        rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_mul, hσ1, one_mul]
      rw [hsum_eq, mul_smul, (φ (toECorner he.1 n)).prop]
    | zero =>
      intro r
      simp only [smul_zero]
      show ∑ p ∈ σ.support, (σ p * p.1) •
          (φ (toECorner he.1 (p.2 • (0 : M))) : eCorner he.1 N).val = 0
      simp [smul_zero, show toECorner he.1 (0 : M) = 0 from Subtype.ext (smul_zero e),
            map_zero]
    | add x y _ _ ihx ihy =>
      intro r
      rw [smul_add, lift_add, lift_add, ihx r, ihy r, smul_add]
    | smul a x _ ihx =>
      intro r
      -- liftFun(r • (a • x)) = liftFun((r*a) • x) = (r*a) • liftFun(x) = r • (a • liftFun(x))
      --                       = r • liftFun(a • x)
      rw [← mul_smul, ihx (r * a), mul_smul, ← ihx a]
  let f : M →ₗ[A] N :=
    { toFun := liftFun
      map_add' := lift_add
      map_smul' := lift_smul }
  refine ⟨ModuleCat.ofHom f, ?_⟩
  ext ⟨m, hm⟩
  -- hm : e smul m = m. Show f(m) = phi(m,hm) in eN.
  apply Subtype.ext
  show ∑ p ∈ σ.support, (σ p * p.1) •
      ((φ (toECorner he.1 (p.2 • m))) : eCorner he.1 N).val =
    (φ ⟨m, hm⟩ : eCorner he.1 N).val
  -- For m in eM: toECorner(b smul m) = (ebe) smul_{eAe} (m, hm)
  have htoE : ∀ p : A × A, toECorner he.1 (p.2 • m) =
      (⟨e * p.2 * e, ⟨p.2, rfl⟩⟩ : CornerRing (k := k) e) • ⟨m, hm⟩ := by
    intro p; apply Subtype.ext
    show e • (p.2 • m) = (e * p.2 * e) • m
    rw [mul_smul, mul_smul, hm]
  simp only [htoE, map_smul]
  simp only [show ∀ (r : CornerRing (k := k) e) (x : eCorner he.1 N),
      ((r • x : eCorner he.1 N) : N) = (r : A) • (x : N) from fun _ _ => rfl]
  simp only [← mul_smul, ← Finset.sum_smul]
  -- Sum collapses: sum(sigma(p) * p.1 * e * p.2 * e) = 1 * e = e
  conv_lhs => arg 1; arg 2; ext p; rw [show σ p * p.1 * (e * p.2 * e) =
    σ p * (p.1 * e * p.2) * e by simp only [mul_assoc]]
  rw [← Finset.sum_mul]
  have hσ2 : ∑ p ∈ σ.support, σ p * (p.1 * e * p.2) = 1 := by
    have := hσ; simp only [Finsupp.sum, smul_eq_mul] at this; exact this
  rw [hσ2, one_mul]
  exact (φ ⟨m, hm⟩).prop

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
  -- Forward: ⟨e • [a ⊗ n], _⟩ ↦ (eae-part of a) • n
  -- Inverse: n ↦ ⟨e • [e ⊗ n], _⟩
  exact ⟨M, ⟨sorry⟩⟩

/-! ## Helper: Morita equivalence via full idempotent

For a ring `A` and a full idempotent `e` (i.e., `AeA = A`), `A` and `eAe` are
Morita equivalent. The corner functor `M ↦ eM` gives an equivalence of module
categories when `e` is full. -/
lemma morita_equiv_of_full_idempotent
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
