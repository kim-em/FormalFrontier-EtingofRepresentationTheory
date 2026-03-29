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
import Mathlib.RingTheory.Jacobson.Ideal
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

Two sorrys remain:

1. `exists_full_idempotent_basic_corner`: Fullness (AeA = A) is proved. Basicness
   proof constructs ring hom π : eAe → k^numBlocks, proves ker π consists of
   nilpotent elements, and proves ker π annihilates simple modules.
   Remaining sorry: conclude finrank k M = 1 from the annihilation
   (needs Schur's lemma + IsAlgClosed + module transfer infrastructure).

2. `cornerFunctor_essSurj`: Requires showing `e(A ⊗_{eAe} N) ≅ N`, the other
   direction of the evaluation isomorphism.

`cornerFunctor_full` is now sorry-free (lift construction complete).
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
  intro R
  rw [eq_top_iff]
  intro x _
  let I := Ideal.span {a * (∑ j, (Pi.single j (Matrix.single 0 0 1) : R)) * b |
      (a : R) (b : R)}
  -- Key: Pi.single i m is in I for all i, m
  suffices hsingle : ∀ (i : Fin n) (m : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i m ∈ I from by
    rw [show x = ∑ i, Pi.single i (x i) from (Finset.univ_sum_single x).symm]
    exact Ideal.sum_mem _ fun i _ => hsingle i (x i)
  intro i m
  -- m is in Ideal.span {a * E₁₁ * b} in Mat_{d_i}(k)
  have hgen := matrix_single_generates_ideal k (n := d i)
  rw [eq_top_iff] at hgen
  have hm := hgen (Submodule.mem_top : m ∈ ⊤)
  -- Key: Pi.single i (a * E₁₁ * b) is in I, for any a, b in block i.
  -- This follows from: Pi.single i a * (∑ j, Pi.single j E₁₁) * Pi.single i b = Pi.single i (a * E₁₁ * b)
  -- by orthogonality of Pi.single at different indices.
  -- Since m ∈ Ideal.span {a * E₁₁ * b | a b} in the matrix ring, Pi.single i m ∈ I.
  -- Key helper: Pi.single i is a ring homomorphism (add, zero, mul)
  have single_add : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a + b) = (Pi.single i a : R) + Pi.single i b := by
    intro a b; ext t r s
    simp only [Pi.add_apply, Pi.single, Function.update, dite_apply, Pi.zero_apply,
      Matrix.zero_apply, Matrix.add_apply]
    split
    · next h => subst h; rfl
    · simp
  have single_mul : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a * b) = (Pi.single i a : R) * Pi.single i b := by
    intro a b; ext t r s
    simp only [Pi.mul_apply, Pi.single, Function.update, dite_apply, Pi.zero_apply,
      Matrix.zero_apply, Matrix.mul_apply]
    split
    · next h => subst h; rfl
    · simp
  -- Key: Pi.single i (a * E₁₁ * b) = (Pi.single i a) * (∑ j, E₁₁^j) * (Pi.single i b) ∈ I
  have hfgen : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a * Matrix.single 0 0 1 * b) ∈ I := by
    intro a b
    have hcalc : (Pi.single i a : R) * (∑ j, (Pi.single j (Matrix.single 0 0 (1 : k)) : R)) *
        (Pi.single i b : R) = Pi.single i (a * Matrix.single 0 0 1 * b) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single i]
      · -- single_mul for three factors
        ext t r s
        simp only [Pi.mul_apply, Pi.single, Function.update, dite_apply, Pi.zero_apply,
          Matrix.zero_apply, Matrix.mul_apply]
        split
        · next h => subst h; rfl
        · simp
      · intro j _ hj
        have : (Pi.single i a : R) * (Pi.single j (Matrix.single 0 0 (1 : k)) : R) = 0 := by
          ext t r s
          simp only [Pi.mul_apply, Pi.zero_apply, Pi.single, Function.update, dite_apply,
            Matrix.zero_apply, Matrix.mul_apply]
          split
          · next h => subst h; simp [dif_neg (Ne.symm hj)]
          · simp
        simp [this]
      · simp
    rw [← hcalc]
    exact Ideal.subset_span ⟨_, _, rfl⟩
  -- Since m is in the span of {a * E₁₁ * b}, Pi.single i m ∈ I by span induction
  have hpi : ∀ y, y ∈ Ideal.span {a * Matrix.single (0 : Fin (d i)) 0 (1 : k) * b |
      (a : Matrix _ _ k) (b : Matrix _ _ k)} → Pi.single i y ∈ I := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact hfgen a b
    | zero =>
      simp only [Pi.single_zero]
      exact I.zero_mem
    | add x y _ _ ihx ihy =>
      rw [single_add]; exact I.add_mem ihx ihy
    | smul r x _ ihx =>
      rw [show r • x = r * x from rfl, single_mul]
      exact I.mul_mem_left _ ihx
  exact hpi m hm

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
      -- Step A: In ∏ Mat_{n_i}(k), ∑ E₁₁ generates the whole ring
      have hpi := pi_matrix_single_generates_ideal k blockSize
      -- Step B: Transport through φ to A/J
      let ē_sum := ∑ i, ē_AJ i
      -- Key: φ.symm (∑ E₁₁) = ē_sum
      have hē_sum_eq : φ.symm (∑ i,
          (Pi.single i (Matrix.single 0 0 1) :
          (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k))) =
          ē_sum := by
        simp only [ē_sum, map_sum, ē_AJ, ē]
      have hAJ_gen : Ideal.span {a * ē_sum * b |
          (a : A ⧸ J) (b : A ⧸ J)} = ⊤ := by
        rw [eq_top_iff]; intro x _
        -- Pull back through φ.symm from the product ideal
        suffices key : ∀ y, y ∈ Ideal.span
            {a * (∑ i, (Pi.single i (Matrix.single 0 0 1) :
              (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k))) *
              b | (a : ∀ i, Matrix _ _ k) (b : ∀ i, Matrix _ _ k)} →
            φ.symm y ∈ Ideal.span
              {a * ē_sum * b | (a : A ⧸ J) (b : A ⧸ J)} by
          have := key (φ x) (hpi ▸ Submodule.mem_top)
          rwa [φ.symm_apply_apply] at this
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, b, rfl⟩ := hz
          rw [map_mul, map_mul, hē_sum_eq]
          exact Ideal.subset_span ⟨φ.symm a, φ.symm b, rfl⟩
        | zero => simp [Ideal.zero_mem]
        | add a b _ _ iha ihb => rw [map_add]; exact Ideal.add_mem _ iha ihb
        | smul r a _ iha =>
          change φ.symm (r * a) ∈ _
          rw [map_mul]; exact Ideal.mul_mem_left _ _ iha
      -- Step C: The image of e in A/J is ē_sum
      -- So AeA maps onto A/J, meaning AeA + J = A
      -- i.e., 1 ∈ AeA + J
      let I := Ideal.span {a * e * b | (a : A) (b : A)}
      -- The quotient image of I contains the quotient image of e
      have hI_image : ∀ (a b : A ⧸ J),
          a * ē_sum * b ∈ Ideal.map (Ideal.Quotient.mk J) I := by
        intro a b
        obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
        have : Ideal.Quotient.mk J a' * ē_sum * Ideal.Quotient.mk J b' =
            Ideal.Quotient.mk J (a' * e * b') := by
          rw [show ē_sum = Ideal.Quotient.mk J e from he_image.symm]
          simp [map_mul]
        rw [this]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a', b', rfl⟩)
      have hI_map_top : Ideal.map (Ideal.Quotient.mk J) I = ⊤ := by
        rw [eq_top_iff, ← hAJ_gen]
        exact Submodule.span_le.mpr fun _ ⟨a, b, h⟩ => h ▸ hI_image a b
      -- Step D: I ⊔ J = ⊤
      have hIJ_top : I ⊔ J = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [← Ideal.mem_quotient_iff_mem_sup]
        rw [hI_map_top]
        exact Submodule.mem_top
      -- Step E: 1 = x + j with x ∈ I, j ∈ J, so x = 1 - j and 1 - x ∈ J
      have h1_mem : (1 : A) ∈ I ⊔ J := hIJ_top ▸ Submodule.mem_top
      rw [Submodule.mem_sup] at h1_mem
      obtain ⟨x, hxI, j, hjJ, hxj⟩ := h1_mem
      -- x = 1 - j, and j ∈ J which is nilpotent, so j is nilpotent, so x is a unit
      have hx_unit : IsUnit x := by
        have hx_eq : x = 1 - j := by
          have h := hxj; rw [show x + j = 1 ↔ x = 1 - j from
            ⟨fun h => by rw [← h, add_sub_cancel_right],
             fun h => by rw [h, sub_add_cancel]⟩] at h; exact h
        rw [hx_eq]
        exact IsNilpotent.isUnit_one_sub
          (hker_nil j (by rwa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]))
      exact Ideal.eq_top_of_isUnit_mem I hxI hx_unit
  have he_basic : @IsBasicAlgebra k _ (CornerRing (k := k) e)
      (CornerRing.instRing he_full.1) (CornerRing.instAlgebra he_full.1) := by
    letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he_full.1
    letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he_full.1
    -- === Part A: φ(q(e)) = constant function E₁₁ ===
    have hφqe : φ (Ideal.Quotient.mk J e) =
        fun i => Matrix.single (0 : Fin (blockSize i)) 0 1 := by
      rw [he_image, map_sum]
      simp only [ē_AJ, ē, AlgEquiv.apply_symm_apply]
      exact Finset.univ_sum_single _
    -- === Part B: For x ∈ eAe, φ(q(x)) at each block is a scalar matrix ===
    have corner_scalar : ∀ (x : CornerRing (k := k) e) (i : Fin numBlocks),
        (φ (Ideal.Quotient.mk J (x : A))) i =
          Matrix.single 0 0 ((φ (Ideal.Quotient.mk J (x : A))) i 0 0) := by
      intro ⟨xval, hx⟩ i
      obtain ⟨a, ha⟩ := (mem_cornerSubmodule_iff e xval).mp hx
      have hq : Ideal.Quotient.mk J xval =
          Ideal.Quotient.mk J e * Ideal.Quotient.mk J a * Ideal.Quotient.mk J e := by
        simp only [← map_mul, ha]
      -- LHS and RHS both rewrite using hq, map_mul, hφqe
      -- Then E₁₁ * M * E₁₁ = single 0 0 (M 0 0) by single_mul_mul_single
      conv_lhs => rw [hq, map_mul, map_mul, hφqe]
      conv_rhs => rw [hq, map_mul, map_mul, hφqe]
      simp only [Pi.mul_apply, Matrix.single_mul_mul_single, one_mul, mul_one,
        Matrix.single_apply, ↓reduceIte, and_self, ite_true]
    -- === Part C: Ring hom π : eAe → Fin numBlocks → k ===
    let π : CornerRing (k := k) e →+* (Fin numBlocks → k) :=
    { toFun := fun x i => (φ (Ideal.Quotient.mk J (x : A))) i 0 0
      map_one' := by
        ext i; change (φ (Ideal.Quotient.mk J e)) i 0 0 = 1
        rw [hφqe]; simp [Matrix.single_apply]
      map_mul' := fun x y => by
        ext i; simp only [Pi.mul_apply]
        show (φ (Ideal.Quotient.mk J ((x : A) * (y : A)))) i 0 0 =
          (φ (Ideal.Quotient.mk J (x : A))) i 0 0 *
          (φ (Ideal.Quotient.mk J (y : A))) i 0 0
        have h1 : Ideal.Quotient.mk J ((x : A) * (y : A)) =
            Ideal.Quotient.mk J (x : A) * Ideal.Quotient.mk J (y : A) := map_mul _ _ _
        have h2 : φ (Ideal.Quotient.mk J (x : A) * Ideal.Quotient.mk J (y : A)) =
            φ (Ideal.Quotient.mk J (x : A)) * φ (Ideal.Quotient.mk J (y : A)) := map_mul _ _ _
        rw [h1, h2, Pi.mul_apply, corner_scalar x i, corner_scalar y i,
          Matrix.single_mul_single_same, Matrix.single_apply, Matrix.single_apply]
        simp [Matrix.single_apply]
      map_zero' := by ext i; simp [map_zero, Matrix.zero_apply]
      map_add' := fun x y => by ext i; simp [map_add, Matrix.add_apply] }
    -- === Part D: ker π ⊆ J (elements mapping to 0 in A/J) ===
    have hπ_ker_sub_J : ∀ (x : CornerRing (k := k) e),
        x ∈ RingHom.ker π → (x : A) ∈ J := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hblock : ∀ i, (φ (Ideal.Quotient.mk J (x : A))) i = 0 := by
        intro i; rw [corner_scalar x i]
        have hi : (φ (Ideal.Quotient.mk J (x : A))) i 0 0 = 0 := congr_fun hx i
        rw [hi]; ext r s; simp [Matrix.single_apply]
      have hq0 : Ideal.Quotient.mk J (x : A) = 0 :=
        φ.injective (funext hblock |>.trans (map_zero φ).symm)
      rwa [Ideal.Quotient.eq_zero_iff_mem] at hq0
    -- === Part E: elements of ker π are nilpotent in CornerRing ===
    have hπ_ker_nilpotent_elem : ∀ (x : CornerRing (k := k) e),
        x ∈ RingHom.ker π → IsNilpotent x := by
      intro x hx
      have hxJ := hπ_ker_sub_J x hx
      obtain ⟨n, hn⟩ := hJ_nil
      -- Use n+1 because (x^0).val = e ≠ 1 = x.val^0 in CornerRing
      refine ⟨n + 1, ?_⟩
      have hxn : (x : A) ^ n = 0 := Ideal.pow_eq_zero_of_mem hn le_rfl hxJ
      -- For m ≥ 1: (x ^ m : CornerRing).val = x.val ^ m (since mul in CornerRing = mul in A)
      have corner_pow : ∀ m, (x ^ (m + 1) : CornerRing (k := k) e).val =
          (x : A) ^ (m + 1) := by
        intro m; induction m with
        | zero => simp [pow_one]
        | succ m ih =>
          have step : (x ^ (m + 2) : CornerRing (k := k) e).val =
              (x ^ (m + 1) : CornerRing (k := k) e).val * (x : A) := by
            show (x ^ (m + 1) * x : CornerRing (k := k) e).val = _; rfl
          rw [step, ih, ← pow_succ]
      have hval : (x ^ (n + 1) : CornerRing (k := k) e).val = (0 : A) :=
        (corner_pow n).trans (by rw [pow_succ, hxn, zero_mul])
      exact Subtype.ext hval
    -- === Part F: ker π annihilates simple modules ===
    -- If a ∈ ker π and a•m ≠ 0, then by simplicity m = (ba)•m for some b,
    -- so m = (ba)^N•m = 0 (ba is nilpotent in ker π), contradiction.
    intro M _instACG _instMod _instSimple _instModk _instST
    have hker_ann : ∀ (a : CornerRing (k := k) e), a ∈ RingHom.ker π →
        ∀ (m : M), a • m = 0 := by
      intro a ha m
      by_contra h_ne
      -- a•m ≠ 0, so span = ⊤ by simplicity
      have hspan : Submodule.span (CornerRing (k := k) e) {a • m} = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top
          (Submodule.span (CornerRing (k := k) e) {a • m}) with h | h
        · have hmem : a • m ∈ (⊥ : Submodule (CornerRing (k := k) e) M) :=
            h ▸ Submodule.subset_span rfl
          rw [Submodule.mem_bot] at hmem; exact absurd hmem h_ne
        · exact h
      -- m ∈ span {a • m}, so m = b • (a • m) for some b
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
        (hspan ▸ (Submodule.mem_top : m ∈ ⊤))
      -- c = b * a ∈ ker π (ker is a left ideal)
      have hc_mem : b * a ∈ RingHom.ker π := by
        simp only [RingHom.mem_ker, map_mul, RingHom.mem_ker.mp ha, mul_zero]
      -- c is nilpotent
      obtain ⟨N, hN⟩ := hπ_ker_nilpotent_elem (b * a) hc_mem
      -- m = c • m implies m = c^n • m for all n, then specialize to N
      have hm_eq : (b * a) • m = m := by rw [mul_smul]; exact hb
      have hpow : ∀ n, m = (b * a) ^ n • m := by
        intro n; induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, mul_smul, hm_eq]; exact ih
      have := hpow N; rw [hN, zero_smul] at this
      exact h_ne (by rw [this, smul_zero])
    -- === Part G: finrank k M = 1 ===
    -- Mathematical argument (not yet formalized):
    -- (1) ker π annihilates M (proved above in hker_ann)
    -- (2) Since k^numBlocks is commutative and the action factors through π,
    --     for any r ∈ CornerRing, the map m ↦ r • m is a CornerRing-endomorphism of M:
    --     r(sm) = (rs)m and s(rm) = (sr)m agree since π(rs) = π(sr) in k^numBlocks.
    -- (3) By Schur's lemma (Module.End.instDivisionRing), End(M) is a division ring.
    -- (4) Since k is algebraically closed, algebraMap k End(M) is bijective
    --     (IsAlgClosed.algebraMap_bijective_of_isIntegral).
    -- (5) So every r ∈ CornerRing acts as a k-scalar on M.
    -- (6) For any nonzero m₀, every m ∈ M is c • m₀ for some c ∈ k.
    -- (7) By finrank_eq_one_iff_of_nonzero', finrank k M = 1.
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
    simp_rw [h1, map_smul, coe_smul, ← mul_smul, ← Finset.sum_smul]
    have hsum_e : ∑ p ∈ σ.support, σ p * p.1 * (e * p.2 * e) = e := by
      have : ∀ p ∈ σ.support, σ p * p.1 * (e * p.2 * e) =
          σ p * (p.1 * e * p.2) * e := fun p _ => by simp only [mul_assoc]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hσ1, one_mul]
    rw [hsum_e]
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
      have h0 : liftFun (0 : M) = 0 := by
        have h := lift_add (0 : M) 0; simp only [add_zero] at h
        -- h : liftFun 0 = liftFun 0 + liftFun 0
        have : liftFun (0 : M) + liftFun (0 : M) = liftFun (0 : M) + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel this
      rw [h0, smul_zero]
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
