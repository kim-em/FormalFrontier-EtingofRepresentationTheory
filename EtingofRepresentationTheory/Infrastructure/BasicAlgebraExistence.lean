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
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.Data.Matrix.Basis

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
/-! ### Helper lemmas for the main proof -/

/-- In `Mat_n(k)`, the matrix unit `E₀₀` generates the whole ring as a two-sided ideal.
Proof: `E_{r,s} = E_{r,0} · E_{0,0} · E_{0,s}`, so every matrix unit is in the ideal
of `E₀₀`, and every matrix is a sum of matrix units. -/
private lemma matrix_single_generates_ideal (k : Type u) [Field k]
    {n : ℕ} [NeZero n] :
    Ideal.span {a * Matrix.single (0 : Fin n) (0 : Fin n) (1 : k) * b |
      (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k)} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  -- Each matrix unit E_{r,s} = E_{r,0} · E_{0,0} · E_{0,s} is in the ideal of E₀₀.
  -- Every matrix x is a k-linear combination of matrix units.
  -- We show each scaled matrix unit c • E_{r,s} is in the ideal.
  -- c • E_{r,s} = (c • E_{r,0}) · E_{0,0} · E_{0,s}
  -- For each (r, s) entry of x, show that x r s • E_{r,s} is in the ideal.
  -- x r s • E_{r,s} = (x r s • E_{r,0}) · E_{0,0} · E_{0,s}, which is in the ideal of E₀₀.
  -- Then x = ∑ r s, x r s • E_{r,s} is in the ideal.
  -- We use that Matrix.single r s c · Matrix.single 0 0 1 · Matrix.single 0 s' 1
  -- follows from Matrix.single_mul_single_same.
  let I := Ideal.span {a * Matrix.single (0 : Fin n) (0 : Fin n) (1 : k) * b |
      (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k)}
  suffices h : ∀ (r s : Fin n) (c : k), Matrix.single r s c ∈ I by
    have hx : x = ∑ r, ∑ s, Matrix.single r s (x r s) := by
      ext i j
      simp only [Matrix.sum_apply]
      rw [Finset.sum_eq_single i
        (fun b _ hb => by simp [Matrix.single_apply, hb])
        (by simp)]
      rw [Finset.sum_eq_single j
        (fun b _ hb => by simp [Matrix.single_apply, hb])
        (by simp)]
      simp [Matrix.single_apply]
    rw [hx]
    exact Ideal.sum_mem _ fun r _ => Ideal.sum_mem _ fun s _ => h r s _
  intro r s c
  -- Matrix.single r s c = (Matrix.single r 0 c) · E₀₀ · (Matrix.single 0 s 1)
  have : Matrix.single r (0 : Fin n) c * Matrix.single 0 0 1 *
      Matrix.single (0 : Fin n) s 1 = Matrix.single r s c := by
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp [mul_one]
  rw [← this]
  exact Ideal.subset_span ⟨_, _, rfl⟩

/-- In a product of matrix algebras, the sum of matrix units E₁₁ in each factor
generates the whole product ring as a two-sided ideal. -/
private lemma pi_matrix_single_generates_ideal (k : Type u) [Field k]
    {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    let R := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k
    Ideal.span {a * (∑ i, (Pi.single i (Matrix.single 0 0 1) : R)) * b |
      (a : R) (b : R)} = ⊤ := by
  sorry

/-- The sum of orthogonal idempotents is idempotent. -/
private lemma isIdempotentElem_sum_orthogonal {R : Type*} [Ring R] {n : ℕ}
    {e : Fin n → R} (he : OrthogonalIdempotents e) :
    IsIdempotentElem (∑ i, e i) := by
  simp only [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum]
  rw [show ∑ i, e i = ∑ i, ∑ j, if i = j then e i else 0 by
    simp [Finset.sum_ite_eq]]
  rw [Finset.sum_comm]
  congr 1; ext j
  congr 1; ext i
  split_ifs with hij
  · subst hij; exact (he.idem _).eq
  · exact he.ortho hij

/-- For a finite-dimensional algebra over an algebraically closed field, the quotient
by the Jacobson radical is a semisimple finite-dimensional algebra, and by Wedderburn-Artin
it decomposes as a product of matrix algebras. This gives us orthogonal idempotents
(one primitive per block) which can be lifted to A. The sum is a full idempotent with
basic corner ring.

This is the key construction: we sorry the existence statement but decompose
the proof obligations clearly. -/
lemma exists_full_idempotent_basic_corner
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (e : A) (he : IsFullIdempotent e),
      @IsBasicAlgebra k _ (CornerRing (k := k) e) (CornerRing.instRing he.1)
        (CornerRing.instAlgebra he.1) := by
  -- Step 1: A is Artinian (finite-dim over a field)
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Step 2: A is semiprimary (automatic from Artinian)
  haveI : IsSemiprimaryRing A := inferInstance
  -- Step 3: A/J(A) is semisimple and finite-dimensional
  set J := Ring.jacobson A
  haveI : IsSemisimpleRing (A ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  -- Step 4: Wedderburn-Artin decomposition of A/J(A) ≅ ∏ Mat_{n_i}(k)
  -- The quotient algebra is finite-dimensional over k
  letI : Algebra k (A ⧸ J) := Ideal.Quotient.algebra k
  haveI : Module.Finite k (A ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k J).toLinearMap (Ideal.Quotient.mkₐ_surjective k J)
  obtain ⟨numBlocks, blockSize, hne, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ J)
  -- Step 5: Extract orthogonal idempotents E₁₁ in each block of the product
  -- In ∏ Mat_{n_i}(k), define ēᵢ = Pi.single i (Matrix.single 0 0 1)
  let ē : Fin numBlocks → (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k) :=
    fun i => Pi.single i (Matrix.single 0 0 1)
  -- These are orthogonal idempotents in the product
  have hē_orth : OrthogonalIdempotents ē := by
    constructor
    · intro i
      change ē i * ē i = ē i
      simp only [ē, ← Pi.single_mul]
      congr 1
      rw [Matrix.single_mul_single_same]
      simp
    · intro i j hij
      change ē i * ē j = 0
      simp only [ē]
      ext t : 1
      simp only [Pi.mul_apply, Pi.zero_apply]
      by_cases hi : i = t
      · subst hi
        simp [hij]
      · simp [hi]
  -- Transport to A/J(A) via the isomorphism
  let ē_AJ : Fin numBlocks → (A ⧸ J) := fun i => φ.symm (ē i)
  have hē_AJ_orth : OrthogonalIdempotents ē_AJ := by
    constructor
    · intro i
      change ē_AJ i * ē_AJ i = ē_AJ i
      simp only [ē_AJ, ← map_mul, hē_orth.idem i |>.eq]
    · intro i j hij
      change ē_AJ i * ē_AJ j = 0
      simp only [ē_AJ, ← map_mul, hē_orth.ortho hij, map_zero]
  -- Step 6: Lift to A using nilpotency of J
  have hJ_nil : IsNilpotent J := IsSemiprimaryRing.isNilpotent
  have hker_nil : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk J), IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨n, hn⟩ := hJ_nil
    exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hx⟩
  obtain ⟨e_lifted, he_orth, he_comp⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk J) hker_nil hē_AJ_orth
    (fun i => Ideal.Quotient.mk_surjective (ē_AJ i))
  -- Step 7: Set e = ∑ e_lifted i
  let e := ∑ i, e_lifted i
  have he_idem : IsIdempotentElem e := isIdempotentElem_sum_orthogonal he_orth
  -- Step 8: Show e is full (AeA = A) and eAe is basic
  -- Fullness: In A/J, the images ē_AJ i generate A/J as a two-sided ideal.
  -- Since J is nilpotent, this lifts to fullness in A.
  -- Basicness: eAe/rad(eAe) ≅ k^n (one copy per block), so all simple eAe-modules
  -- are 1-dimensional.
  -- Step 8a: Show that in A/J, the two-sided ideal generated by ē = ∑ ēᵢ is all of A/J.
  have he_quotient_image : ∀ i, Ideal.Quotient.mk J (e_lifted i) = ē_AJ i :=
    fun i => congr_fun he_comp i
  have he_image : Ideal.Quotient.mk J e = ∑ i, ē_AJ i := by
    simp only [e, map_sum, he_quotient_image]
  -- Key fact: in ∏ Mat_{n_i}(k), the two-sided ideal generated by ∑ E₁₁^(i) is the
  -- whole product because E_{rs}^(i) = E_{r0}^(i) · E₀₀^(i) · E_{0s}^(i).
  -- Therefore in A/J, the image of e generates A/J as a two-sided ideal.
  -- This means ∃ aₖ, bₖ such that ∑ aₖ · ē · bₖ = 1 in A/J,
  -- i.e., 1 - ∑ aₖ · e · bₖ ∈ J.
  -- Since J = Ring.jacobson A ⊆ jacobson ⊥, this element is in the Jacobson radical,
  -- so ∑ aₖ · e · bₖ is a unit. Since AeA contains this unit, AeA = ⊤.
  have he_full : IsFullIdempotent e := by
    constructor
    · exact he_idem
    · -- Strategy: Show 1 ∈ Ideal.span {a * e * b | a b}
      -- Step A: In A/J, the image of e generates the quotient as a two-sided ideal
      -- Step B: Lift to show AeA + J = A, i.e., ∃ x ∈ AeA with x ≡ 1 (mod J)
      -- Step C: x = 1 - j with j ∈ J ⊂ Ring.jacobson A, so x is a unit
      -- Step D: AeA contains a unit ⟹ AeA = ⊤
      -- For now, sorry the full argument. The key missing piece is showing
      -- that E₁₁ generates Mat_n(k) as a two-sided ideal.
      sorry
  have he_basic : @IsBasicAlgebra k _ (CornerRing (k := k) e)
      (CornerRing.instRing he_full.1) (CornerRing.instAlgebra he_full.1) := by
    sorry
  exact ⟨e, he_full, he_basic⟩

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
