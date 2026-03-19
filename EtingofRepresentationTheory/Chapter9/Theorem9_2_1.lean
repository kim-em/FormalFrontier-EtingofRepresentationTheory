import EtingofRepresentationTheory.Chapter9.Definition9_2_2
import EtingofRepresentationTheory.Chapter9.Corollary9_1_3
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Idempotents

/-!
# Theorem 9.2.1: Classification of indecomposable projective modules

Let A be a finite dimensional algebra over a field k. Let M₁, …, Mₘ be the irreducible
representations of A. Then:

(i) For each i there exists a unique (up to isomorphism) indecomposable finitely generated
projective module Pᵢ, called the **projective cover** of Mᵢ, such that
dim Hom_A(Pᵢ, Mⱼ) = δᵢⱼ.

(ii) A ≅ ⊕ᵢ (dim Mᵢ) · Pᵢ (as A-modules).

(iii) Any indecomposable finitely generated projective A-module is isomorphic to some Pᵢ.

## Mathlib correspondence

Uses Krull–Schmidt theorem (partially in Mathlib), Nakayama's lemma
(`Ideal.eq_top_of_isUnit_of_forall_mem`), and lifting of idempotents.

## Formalization approach

The three parts are stated as separate theorems sharing common hypotheses:
a finite-dimensional algebra A over a field k, with a finite indexing type ι for the
isomorphism classes of simple modules, and a family of simple modules indexed by ι.

Part (i) is an existence statement producing the projective covers — it only requires
that the Mᵢ are pairwise non-isomorphic.
Parts (ii) and (iii) additionally require that the Mᵢ exhaust all simple A-modules
(up to isomorphism), since the decomposition of A and the completeness of the
classification both fail if some simple modules are missing from the family.
-/

open scoped DirectSum

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]

/-! ### Helper lemmas for the projective cover construction

The proof of Theorem 9.2.1(i) proceeds by:
1. A is artinian → A is semiprimary → A/Rad(A) is semisimple, Rad(A) nilpotent
2. Construct complete orthogonal idempotents in A/Rad(A) corresponding to simple modules
3. Lift to A via Corollary 9.1.3
4. Left ideals A·eᵢ are projective (direct summands of A)
5. Hom_A(A·eᵢ, M_j) ≅ eᵢ·M_j, with dim = δᵢⱼ
6. A·eᵢ is indecomposable (primitive idempotent)
-/

namespace Etingof.Theorem921

/-- The k-linear endomorphism `m ↦ a • m` on an A-module M. -/
noncomputable def smulEnd (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [SMulCommClass A k M] (a : A) : M →ₗ[k] M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := smul_comm a c m

/-- The range of `smulEnd M a` is the k-submodule `{a • m : m ∈ M}` of M. -/
noncomputable def smulRange (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [SMulCommClass A k M] (a : A) : Submodule k M :=
  LinearMap.range (smulEnd (k := k) (A := A) M a)

/-- For a finite-dimensional algebra A over k with pairwise non-isomorphic simple modules
M₁, ..., Mₘ, there exist orthogonal idempotents e₁, ..., eₘ in A (one per iso class of
simple modules) such that eᵢ acts as a rank-1 projection on Mᵢ and as zero on Mⱼ for
j ≠ i. These are lifted from the Wedderburn-Artin decomposition of A/Rad(A).

Proof sketch:
1. A is artinian → IsSemiprimaryRing A → IsSemisimpleRing (A ⧸ Ring.jacobson A)
2. A/Rad(A) ≅ ∏ Mat_{nᵢ}(Dᵢ) by Wedderburn-Artin
3. Simple A-modules = simple A/Rad(A)-modules (Rad acts by 0 on simples)
4. Each Wedderburn block corresponds to one iso class of simples
5. Pick rank-1 diagonal idempotents E₁₁ in each block
6. Lift from A/Rad(A) to A using Corollary 9.1.3 -/
lemma exists_orthogonal_idempotents_for_simples
    [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) :
    ∃ (e : ι → A),
      (∀ i, IsIdempotentElem (e i)) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∑ i, e i = 1) ∧
      (∀ i j, Module.finrank k (smulRange (k := k) (A := A) (M j) (e i)) =
        if i = j then 1 else 0) := by
  sorry

/-- The left ideal A·e for an idempotent e is a projective A-module.
This follows from A = A·e ⊕ A·(1-e), so A·e is a direct summand of the free module A. -/
lemma leftIdeal_projective (e : A) (he : IsIdempotentElem e) :
    Module.Projective A ↥(Submodule.span A ({e} : Set A)) := by
  -- Ae is a direct summand of A via a ↦ a*e. Since A is free over itself, Ae is projective.
  set S := Submodule.span A ({e} : Set A) with hS_def
  have he_mem : ∀ a : A, a * e ∈ S :=
    fun a => Submodule.smul_mem _ a (Submodule.subset_span rfl)
  -- The retraction: a ↦ a * e ∈ Ae
  let retr : A →ₗ[A] S :=
    { toFun := fun a => ⟨a * e, he_mem a⟩
      map_add' := fun x y => by ext; simp [add_mul]
      map_smul' := fun r x => by ext; simp [mul_assoc] }
  -- retr ∘ incl = id (because (a*e)*e = a*e for a*e ∈ Ae)
  have h_split : retr.comp S.subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.subtype_apply, retr]
    congr 1
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    simp [mul_assoc, IsIdempotentElem.eq he]
  exact Module.Projective.of_split S.subtype retr h_split

/-- The left ideal A·e for an idempotent e in a finite-dimensional algebra is
finite as an A-module (it is a submodule of A which is finite over A). -/
lemma leftIdeal_finite (e : A) :
    Module.Finite A ↥(Submodule.span A ({e} : Set A)) :=
  inferInstance

/-- A left ideal A·e is indecomposable if the Hom dimension property holds:
dim Hom(Ae, Mⱼ) = 0 for all j except exactly one j = i₀ where it equals 1.
The argument: if Ae = Q₁ ⊕ Q₂, then Hom(Ae, Mⱼ) = Hom(Q₁, Mⱼ) ⊕ Hom(Q₂, Mⱼ),
so dim Hom(Ae, Mⱼ) = dim Hom(Q₁, Mⱼ) + dim Hom(Q₂, Mⱼ). Since dim = 1 for j = i₀,
one of Q₁ or Q₂ has Hom = 0 to all simples, hence is zero (by Nakayama). -/
lemma leftIdeal_indecomposable_of_hom_delta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (e : A) (he : IsIdempotentElem e)
    (i₀ : ι) (hdim : ∀ j, Module.finrank k (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M j) =
      if i₀ = j then 1 else 0) :
    Etingof.IsIndecomposable A ↥(Submodule.span A ({e} : Set A)) := by
  sorry

/-- The finrank of the Hom space from the left ideal A·e to a module M equals
the finrank of the image eM = range(e • · : M → M).

This is the standard isomorphism Hom_A(Ae, M) ≅ eM given by φ ↦ φ(e) with
inverse m ↦ (ae ↦ am). -/
lemma finrank_hom_leftIdeal_eq
    (e : A) (he : IsIdempotentElem e)
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [SMulCommClass A k M] :
    Module.finrank k (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M) =
    Module.finrank k ↥(smulRange (k := k) (A := A) M e) := by
  -- The isomorphism Hom_A(Ae, M) ≅ eM is given by:
  -- Forward: φ ↦ φ(e)  (this lands in eM since e·φ(e) = φ(e²) = φ(e))
  -- Backward: m ∈ eM ↦ (x ↦ x • m)  (A-linear: (rx)•m = r•(x•m))
  -- The backward map works because for m ∈ eM, e•m = m, so the
  -- A-module map x ↦ x•m restricts correctly to Ae.
  set S := Submodule.span A ({e} : Set A) with hS_def
  have he_mem_S : e ∈ S := Submodule.subset_span rfl
  -- Construct the k-linear equivalence
  -- Forward map: φ ↦ φ(e) (evaluation at e)
  have hfwd_mem : ∀ (φ : S →ₗ[A] M), φ ⟨e, he_mem_S⟩ ∈ smulRange (k := k) (A := A) M e := by
    intro φ
    refine ⟨φ ⟨e, he_mem_S⟩, ?_⟩
    show e • φ ⟨e, he_mem_S⟩ = φ ⟨e, he_mem_S⟩
    rw [← φ.map_smul]; congr 1
    exact Subtype.ext (IsIdempotentElem.eq he)
  -- Backward map: m ∈ eM ↦ (⟨x, _⟩ ↦ x • m) where x acts on m via the A-module structure
  -- This is A-linear because (a • x) • m = a • (x • m) by module associativity
  have hbwd_map_smul : ∀ (m : M) (a : A) (x : S), (a • x.1) • m = a • (x.1 • m) := by
    intro m a x; rw [smul_eq_mul, mul_smul]
  -- Construct the k-linear equivalence
  let equiv : (S →ₗ[A] M) ≃ₗ[k] ↥(smulRange (k := k) (A := A) M e) :=
    { toFun := fun φ => ⟨φ ⟨e, he_mem_S⟩, hfwd_mem φ⟩
      invFun := fun ⟨m, hm⟩ =>
        { toFun := fun ⟨x, _⟩ => x • m
          map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => by simp [add_smul]
          map_smul' := fun a ⟨x, _⟩ => by simp [mul_smul] }
      left_inv := by
        intro φ; ext ⟨x, hx⟩
        -- Need: x • φ(e) = φ(x)
        -- x ∈ Ae means x = a • e for some a
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        -- Goal: (a • e) • φ(e) = φ(⟨a • e, _⟩)
        -- (a • e) • φ(e) = φ(a • e) by A-linearity and idempotency
        have he_act : (e : A) • φ ⟨e, he_mem_S⟩ = φ ⟨e, he_mem_S⟩ := by
          conv_rhs => rw [show (⟨e, he_mem_S⟩ : S) = e • ⟨e, he_mem_S⟩ from
            Subtype.ext (IsIdempotentElem.eq he).symm]
          exact (φ.map_smul e ⟨e, he_mem_S⟩).symm
        change (a • e : A) • φ ⟨e, he_mem_S⟩ = φ ⟨a • e, _⟩
        conv_rhs => rw [show (⟨a • e, _⟩ : S) = a • ⟨e, he_mem_S⟩ from rfl]
        rw [φ.map_smul, smul_eq_mul, mul_smul, he_act]
      right_inv := by
        intro ⟨m, hm⟩
        -- Need: e • m = m, which follows from m ∈ eM (m = e • m₀ for some m₀)
        obtain ⟨m₀, hm₀⟩ := hm
        -- hm₀ : e • m₀ = m, so e • m = e • (e • m₀) = (e*e) • m₀ = e • m₀ = m
        apply Subtype.ext
        show (e : A) • m = m
        rw [← hm₀]
        show e • (e • m₀) = e • m₀
        rw [← mul_smul, IsIdempotentElem.eq he]
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by
        ext; rfl }
  exact equiv.finrank_eq

end Etingof.Theorem921

/-- **Theorem 9.2.1(i)**: Existence of projective covers with the Kronecker delta Hom property.

For each simple module Mᵢ over a finite-dimensional algebra A, there exists an indecomposable
finitely generated projective module Pᵢ such that dim Hom_A(Pᵢ, Mⱼ) = δᵢⱼ.

More precisely: given a finite family of pairwise non-isomorphic simple A-modules `M`,
for each index `i` there exists a type `P i` carrying the structure of an indecomposable
projective A-module, together with a proof that dim_k Hom_A(P i, M j) = if i = j then 1 else 0.
(Etingof Theorem 9.2.1(i)) -/
theorem Etingof.Theorem_9_2_1_i
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) :
    ∃ (P : ι → Type*)
      (_ : ∀ i, AddCommGroup (P i))
      (_ : ∀ i, Module A (P i))
      (_ : ∀ i, Module k (P i))
      (_ : ∀ i, IsScalarTower k A (P i))
      (_ : ∀ i, SMulCommClass A k (P i))
      (_ : ∀ i, Module.Projective A (P i))
      (_ : ∀ i, Module.Finite A (P i))
      (_ : ∀ i, Etingof.IsIndecomposable A (P i)),
      ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0 := by
  -- Step 1: A is artinian (finite-dimensional algebra over a field)
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  -- The full assembly proof has a universe issue: the existential introduces a fresh
  -- universe variable for P, but our construction lives in A's universe.
  -- This is resolved by the `exists_orthogonal_idempotents_for_simples` helper
  -- which provides idempotents e_i, and defining P i = Submodule.span A {e_i}.
  -- The helper lemmas leftIdeal_projective, leftIdeal_finite, leftIdeal_indecomposable_of_hom_delta,
  -- and finrank_hom_leftIdeal_eq provide all remaining properties.
  sorry

/-- **Theorem 9.2.1(ii)**: Decomposition of the algebra as a module.

The algebra A, viewed as a left module over itself, decomposes as A ≅ ⊕ᵢ (dim Mᵢ) · Pᵢ.
That is, if `P` is the family of projective covers from part (i), then A is isomorphic
as an A-module to the direct sum over `i` of `(finrank k (M i))` copies of `P i`.
(Etingof Theorem 9.2.1(ii)) -/
theorem Etingof.Theorem_9_2_1_ii
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type*) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) :
    Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i) := by
  sorry

/-- **Theorem 9.2.1(iii)**: Completeness of the projective cover classification.

Any indecomposable finitely generated projective A-module is isomorphic to some Pᵢ.
This follows from the decomposition of A: any indecomposable projective must appear as
a direct summand of A (since A is projective and decomposes into the Pᵢ by part (ii)),
so by Krull–Schmidt it must be isomorphic to one of them.
(Etingof Theorem 9.2.1(iii)) -/
theorem Etingof.Theorem_9_2_1_iii
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type*) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type*) [AddCommGroup Q] [Module A Q]
    [Module.Projective A Q] [Module.Finite A Q] (hQ_indec : Etingof.IsIndecomposable A Q) :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by
  sorry
