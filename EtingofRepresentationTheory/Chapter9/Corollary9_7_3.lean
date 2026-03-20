import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Chapter9.MoritaStructural
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleModule.Rank

universe u v

/-!
# Corollary 9.7.3: Unique basic algebra

(i) Any finite abelian category 𝒞 over k is equivalent to the category of finite
dimensional modules over a unique (up to isomorphism) basic algebra B(𝒞).

(ii) Any finite dimensional algebra A over k is Morita equivalent to a unique
basic algebra B_A, and dim B_A ≤ dim A.

## Mathlib correspondence

Part (i) combines Theorem 9.6.4 (Morita equivalence via progenerator) with the
theory of basic algebras from §9.7.

Part (ii) uses the `Etingof.MoritaEquivalent` and `Etingof.IsBasicAlgebra`
definitions from this project.

## Proof status

Part (ii) (dimension bound) is proved using the Morita structural theorem
and corner ring theory.

Part (i) uniqueness is proved via a dimension argument: if B₁ and B₂ are
both basic and Morita equivalent to A, then by MoritaStructural each embeds
as a corner ring of the other, forcing equal dimensions, hence the corner
rings are the full algebras.

Part (i) existence remains sorry'd pending construction of the basic algebra
from Wedderburn-Artin decomposition and idempotent lifting.
-/

variable (k : Type u) [Field k]

/-! ## Helper lemmas for MoritaEquivalent -/

/-- Morita equivalence is reflexive. -/
lemma Etingof.MoritaEquivalent.refl (A : Type u) [Ring A] : Etingof.MoritaEquivalent A A :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- Morita equivalence is symmetric. -/
lemma Etingof.MoritaEquivalent.symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : Etingof.MoritaEquivalent A B) : Etingof.MoritaEquivalent B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Morita equivalence is transitive. -/
lemma Etingof.MoritaEquivalent.trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : Etingof.MoritaEquivalent A B) (h₂ : Etingof.MoritaEquivalent B C) :
    Etingof.MoritaEquivalent A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

/-! ## Helper lemmas for IsBasicAlgebra -/

/-- A field k is a basic algebra over itself: every simple k-module is 1-dimensional. -/
lemma Etingof.isBasicAlgebra_field : Etingof.IsBasicAlgebra k k := by
  intro M _ hModA hSimp hModK hST
  -- The two Module k M instances (from A = k and from the explicit k-module) must agree
  -- via the IsScalarTower k k M condition
  have : hModA = hModK := by
    ext c m
    have h := hST.1 c (1 : k) m
    simp only [smul_eq_mul, mul_one, one_smul] at h
    exact h
  subst this
  exact isSimpleModule_iff_finrank_eq_one.mp hSimp

/-! ## Helper lemmas for corner ring uniqueness argument -/

/-- When the corner submodule has the same finrank as the ambient algebra, the
idempotent must be the identity. -/
private lemma Etingof.idempotent_eq_one_of_cornerSubmodule_eq_top
    {A : Type u} [Ring A] [Algebra k A]
    {e : A} (he : IsIdempotentElem e) (htop : Etingof.cornerSubmodule (k := k) e = ⊤) :
    e = 1 := by
  have h1 : (1 : A) ∈ Etingof.cornerSubmodule (k := k) e := htop ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Etingof.mem_cornerSubmodule_iff e 1).mp h1
  -- From ha: e * a * e = 1
  -- e * 1 = e, so e = e * (e * a * e) = (e * e) * a * e = e * a * e = 1
  have step1 : e * (e * a * e) = e * e * (a * e) := by
    rw [mul_assoc e a e, ← mul_assoc e e (a * e)]
  have step2 : e * e * (a * e) = e * (a * e) := by
    rw [he.eq]
  have step3 : e * (a * e) = e * a * e := by
    rw [mul_assoc]
  calc e = e * 1 := (mul_one e).symm
    _ = e * (e * a * e) := by rw [ha]
    _ = e * (a * e) := by rw [step1, step2]
    _ = e * a * e := step3
    _ = 1 := ha

/-- When e = 1, the corner ring CornerRing(A, 1) is isomorphic to A as a k-algebra. -/
private noncomputable def Etingof.cornerRingAlgEquivOfUnit
    {A : Type u} [Ring A] [Algebra k A] (he : IsIdempotentElem (1 : A)) :
    @AlgEquiv k (Etingof.CornerRing (k := k) (1 : A)) A _
      (Etingof.CornerRing.instRing he).toSemiring _
      (@Etingof.CornerRing.instAlgebra k _ A _ _ 1 he) _ := by
  letI : Ring (Etingof.CornerRing (k := k) (1 : A)) := Etingof.CornerRing.instRing he
  letI : Algebra k (Etingof.CornerRing (k := k) (1 : A)) :=
    @Etingof.CornerRing.instAlgebra k _ A _ _ 1 he
  have hmem : ∀ a : A, a ∈ Etingof.cornerSubmodule (k := k) (1 : A) := fun a =>
    (Etingof.mem_cornerSubmodule_iff 1 a).mpr ⟨a, by simp⟩
  exact {
    toFun := fun x => (x : A)
    invFun := fun a => ⟨a, hmem a⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun r => by
      -- algebraMap k (CornerRing 1) r = r • 1_corner, coercion to A gives r • 1
      -- algebraMap k A r = r • 1
      simp only [Algebra.algebraMap_eq_smul_one]
      rfl
  }

/-! ## Main results -/

/-- **Corollary 9.7.3(i)**: Any finite-dimensional algebra A over k is Morita equivalent
to some basic algebra B. That is, there exists a basic k-algebra B such that the module
categories of A and B are equivalent.
(Etingof Corollary 9.7.3(i), algebra version) -/
theorem Etingof.Corollary_9_7_3_i
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Etingof.MoritaEquivalent A B := by
  -- Requires: Wedderburn-Artin (Theorem 3.5.4, proved) + idempotent lifting
  -- (Corollary 9.1.3, proved) + showing the resulting corner ring is basic and
  -- Morita equivalent to A. The construction is: extract primitive idempotents
  -- from A/Rad(A) ≅ ∏ End(Vᵢ), lift to A, sum to get e, then B = eAe.
  sorry

/-- **Corollary 9.7.3(i), uniqueness**: The basic algebra B from part (i) is unique
up to isomorphism. If B₁ and B₂ are both basic algebras that are Morita equivalent
to A, then B₁ ≅ B₂ as k-algebras.
(Etingof Corollary 9.7.3(i), uniqueness) -/
theorem Etingof.Corollary_9_7_3_i_unique
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : Etingof.IsBasicAlgebra k B₁) (_hB₂ : Etingof.IsBasicAlgebra k B₂)
    (h₁ : Etingof.MoritaEquivalent A B₁) (h₂ : Etingof.MoritaEquivalent A B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  -- B₁ and B₂ are both Morita equivalent to A, hence to each other.
  have hMor : Etingof.MoritaEquivalent B₁ B₂ := h₁.symm.trans h₂
  -- By the Morita structural theorem: B₂ ≅ e₁(B₁)e₁ for some idempotent e₁ ∈ B₁
  obtain ⟨e₁, he₁, ⟨φ₁⟩⟩ := @Etingof.MoritaStructural k _ B₁ _ _ B₂ _ _ hMor
  -- And B₁ ≅ e₂(B₂)e₂ for some idempotent e₂ ∈ B₂
  obtain ⟨e₂, he₂, ⟨φ₂⟩⟩ := @Etingof.MoritaStructural k _ B₂ _ _ B₁ _ _ hMor.symm
  -- Set up instances for corner rings
  letI : Ring (Etingof.CornerRing (k := k) e₁) := Etingof.CornerRing.instRing he₁
  letI : Algebra k (Etingof.CornerRing (k := k) e₁) := Etingof.CornerRing.instAlgebra he₁
  letI : Ring (Etingof.CornerRing (k := k) e₂) := Etingof.CornerRing.instRing he₂
  letI : Algebra k (Etingof.CornerRing (k := k) e₂) := Etingof.CornerRing.instAlgebra he₂
  -- Dimension argument: finrank B₂ ≤ finrank B₁ and finrank B₁ ≤ finrank B₂
  have hle₁ : Module.finrank k B₂ ≤ Module.finrank k B₁ := by
    calc Module.finrank k B₂
        = Module.finrank k (Etingof.CornerRing (k := k) e₁) :=
          LinearEquiv.finrank_eq φ₁.toLinearEquiv
      _ ≤ Module.finrank k B₁ := Etingof.CornerRing.finrank_le
  have hle₂ : Module.finrank k B₁ ≤ Module.finrank k B₂ := by
    calc Module.finrank k B₁
        = Module.finrank k (Etingof.CornerRing (k := k) e₂) :=
          LinearEquiv.finrank_eq φ₂.toLinearEquiv
      _ ≤ Module.finrank k B₂ := Etingof.CornerRing.finrank_le
  -- cornerSubmodule e₁ has full rank in B₁
  have heq : Module.finrank k (Etingof.CornerRing (k := k) e₁) = Module.finrank k B₁ := by
    linarith [LinearEquiv.finrank_eq φ₁.toLinearEquiv]
  -- So cornerSubmodule e₁ = ⊤ and e₁ = 1
  have htop : Etingof.cornerSubmodule (k := k) e₁ = ⊤ :=
    Submodule.eq_top_of_finrank_eq heq
  have he₁_eq : e₁ = 1 :=
    Etingof.idempotent_eq_one_of_cornerSubmodule_eq_top (k := k) he₁ htop
  -- Rewrite e₁ = 1 everywhere
  subst he₁_eq
  -- After subst, he₁ : IsIdempotentElem 1 and φ₁ : B₂ ≃ₐ CornerRing(B₁, 1)
  -- Compose: B₂ ≅ₐ CornerRing(B₁, 1) ≅ₐ B₁
  exact ⟨(φ₁.trans (Etingof.cornerRingAlgEquivOfUnit (k := k) he₁)).symm⟩

/-- **Corollary 9.7.3(ii)**: For any finite-dimensional algebra A over k, its basic
algebra B_A satisfies dim_k B_A ≤ dim_k A.
(Etingof Corollary 9.7.3(ii)) -/
theorem Etingof.Corollary_9_7_3_ii
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (_hB : Etingof.IsBasicAlgebra k B) (hMor : Etingof.MoritaEquivalent A B) :
    Module.finrank k B ≤ Module.finrank k A := by
  -- By the Morita structural theorem, B ≅ eAe for some idempotent e : A.
  -- Then dim B = dim(eAe) ≤ dim A.
  obtain ⟨e, he, ⟨φ⟩⟩ := @Etingof.MoritaStructural k _ A _ _ B _ _ hMor
  letI : Ring (Etingof.CornerRing (k := k) e) := Etingof.CornerRing.instRing he
  letI : Algebra k (Etingof.CornerRing (k := k) e) := Etingof.CornerRing.instAlgebra he
  calc Module.finrank k B
      = Module.finrank k (Etingof.CornerRing (k := k) e) :=
        LinearEquiv.finrank_eq φ.toLinearEquiv
    _ ≤ Module.finrank k A := Etingof.CornerRing.finrank_le
