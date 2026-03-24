import EtingofRepresentationTheory.Chapter9.Definition9_2_2
import EtingofRepresentationTheory.Chapter9.Corollary9_1_3
import EtingofRepresentationTheory.Chapter3.Lemma3_8_2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Algebra.Module.Torsion.Basic

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

universe uA

variable {k : Type*} [Field k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]

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

/-- Any nontrivial finitely generated module over an artinian ring has a maximal (coatom)
submodule, giving a simple quotient. Uses Hopkins-Levitzki: f.g. over artinian ⟹ noetherian
⟹ WellFoundedGT ⟹ coatomic.
This is needed for Theorem 9.2.1(iii): an indecomposable projective has a simple quotient. -/
theorem exists_isCoatom_submodule
    {R : Type*} [Ring R] [IsArtinianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ∃ (N : Submodule R M), IsCoatom N := by
  -- Hopkins-Levitzki: f.g. over artinian ⟹ noetherian
  haveI : IsNoetherian R M := ((IsArtinianRing.tfae R M).out 0 1).mp ‹Module.Finite R M›
  -- Noetherian ⟹ WellFoundedGT on submodules ⟹ coatomic
  haveI : WellFoundedGT (Submodule R M) := isNoetherian_iff'.mp inferInstance
  haveI : IsCoatomic (Submodule R M) :=
    isCoatomic_of_orderTop_gt_wellFounded (wellFounded_gt)
  obtain h | ⟨N, hN_coatom, _⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule R M)
  · exact absurd h bot_ne_top
  · exact ⟨N, hN_coatom⟩

/-- Any nontrivial f.g. module Q over an artinian ring with an exhaustive family of simples M_i
has a nonzero A-linear map to some M_{j₀}. The quotient Q/N by a coatom N is simple,
hence isomorphic to some M_{j₀}, and the composition Q → Q/N ≅ M_{j₀} is nonzero.
This is the key step in Theorem 9.2.1(iii) that does NOT need #1487. -/
theorem exists_nonzero_hom_to_simple
    {R : Type u} [Ring R] [IsArtinianRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, IsSimpleModule R (M i)]
    (hM_exhaustive : ∀ (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
      ∃ i, Nonempty (S ≃ₗ[R] M i))
    {Q : Type v} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Nontrivial Q] :
    ∃ (j₀ : ι) (f : Q →ₗ[R] M j₀), f ≠ 0 := by
  -- Q has a maximal submodule N (coatom), giving a simple quotient Q/N
  obtain ⟨N, hN_coatom⟩ := exists_isCoatom_submodule (R := R) (M := Q)
  -- Q/N is simple (coatom ↔ simple quotient)
  haveI : IsSimpleModule R (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom
  -- Q/N is isomorphic to some M_{j₀}
  obtain ⟨j₀, ⟨e⟩⟩ := hM_exhaustive (Q ⧸ N)
  -- The composition Q → Q/N ≅ M_{j₀} is nonzero
  refine ⟨j₀, e.toLinearMap.comp N.mkQ, ?_⟩
  intro h
  -- If the composition is zero, then the image of mkQ in M_{j₀} is zero for all q
  have hzero : ∀ q : Q, e (N.mkQ q) = 0 := fun q => by
    have := LinearMap.congr_fun h q
    simpa using this
  -- This means mkQ = 0 (e is injective)
  have hmkQ : ∀ q : Q, N.mkQ q = 0 := fun q => by
    have := hzero q; rwa [map_eq_zero_iff e e.injective] at this
  -- mkQ q = 0 means q ∈ N for all q, i.e., N = ⊤
  exact hN_coatom.1 (Submodule.eq_top_iff'.mpr fun q => by
    specialize hmkQ q
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkQ)

/-- Over a simple artinian ring, any two simple modules are isomorphic.
This follows from `IsSimpleRing.isIsotypic`: all simple submodules of any module
are isomorphic, applied to the direct product M × N. -/
theorem IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule
    {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  -- Embed M and N as simple submodules of M × N
  let eM := LinearEquiv.ofInjective (LinearMap.inl R M N) LinearMap.inl_injective
  let eN := LinearEquiv.ofInjective (LinearMap.inr R M N) LinearMap.inr_injective
  haveI : IsSimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    IsSimpleModule.congr eM.symm
  haveI : IsSimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    IsSimpleModule.congr eN.symm
  -- By isIsotypic, all simple submodules of M × N are isomorphic
  have hiso := IsSimpleRing.isIsotypic R (M × N)
    (LinearMap.range (LinearMap.inl R M N))
  obtain ⟨f⟩ := hiso (LinearMap.range (LinearMap.inr R M N))
  exact ⟨eM.trans (f.symm.trans eN.symm)⟩

section MatrixIdempotents

variable {R : Type*} [CommSemiring R]

/-- The diagonal matrix E₁₁ = Matrix.single 0 0 1 is idempotent in Mat_n(R). -/
lemma matrix_single_zero_isIdempotentElem {ι : Type*} [DecidableEq ι] [Fintype ι]
    (i₀ : ι) :
    IsIdempotentElem (Matrix.single i₀ i₀ (1 : R)) := by
  unfold IsIdempotentElem
  rw [Matrix.single_mul_single_same]
  simp

/-- In a product of semirings, the family `i ↦ Pi.single i (e i)` where each `e i`
is idempotent gives orthogonal idempotents. -/
lemma orthogonalIdempotents_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Semiring (S i)]
    (e : ∀ i, S i) (he : ∀ i, IsIdempotentElem (e i)) :
    OrthogonalIdempotents (fun i => (Pi.single i (e i) : ∀ j, S j)) := by
  constructor
  · intro i
    simp only [IsIdempotentElem, ← Pi.single_mul]
    congr 1; exact he i
  · intro i j hij
    ext l
    by_cases hi : i = l
    · subst hi; simp [hij]
    · simp [hi]

/-- Corner identity: E₁₁ * X * E₁₁ = X(0,0) • E₁₁ in a matrix ring. -/
lemma matrix_single_corner {ι : Type*} [DecidableEq ι] [Fintype ι]
    (i₀ : ι) (X : Matrix ι ι R) :
    Matrix.single i₀ i₀ (1 : R) * X * Matrix.single i₀ i₀ (1 : R) =
      X i₀ i₀ • Matrix.single i₀ i₀ (1 : R) := by
  simp [Matrix.smul_single, mul_comm]

end MatrixIdempotents

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

section CentralAction

/-- The central idempotents `Pi.single l 1` form complete orthogonal idempotents. -/
lemma completeOrthogonalIdempotents_pi_single_one {n : ℕ} {S : Fin n → Type*}
    [∀ i, Semiring (S i)] :
    CompleteOrthogonalIdempotents (Pi.single (M := S) · 1) :=
  CompleteOrthogonalIdempotents.single S

/-- `Pi.single l 1` is central in a dependent product of semirings. -/
lemma pi_single_one_comm {n : ℕ} {S : Fin n → Type*}
    [∀ i, Semiring (S i)] (l : Fin n) (x : ∀ i, S i) :
    (Pi.single l (1 : S l)) * x = x * (Pi.single l (1 : S l)) := by
  rw [← Pi.single_mul_left, ← Pi.single_mul_right]; simp

end CentralAction

-- No separate section needed; infrastructure is inlined in the main proof below.

/-- For a finite-dimensional algebra A over k with pairwise non-isomorphic simple modules
M₁, ..., Mₘ, there exist orthogonal idempotents e₁, ..., eₘ in A (one per iso class of
simple modules) such that eᵢ acts as a rank-1 projection on Mᵢ and as zero on Mⱼ for
j ≠ i. These are lifted from the Wedderburn-Artin decomposition of A/Rad(A).

Note: We do NOT require ∑ eᵢ = 1. Completeness holds for the full double-indexed system
{e_{ij}} (j = 1,...,dim Mᵢ) but NOT for the single-indexed family {eᵢ} when some
dim(Mᵢ) > 1. Part (ii) of Theorem 9.2.1 uses the full system; part (i) only needs
rank-1 projections.

Proof sketch:
1. A is artinian → IsSemiprimaryRing A → IsSemisimpleRing (A ⧸ Ring.jacobson A)
2. A/Rad(A) ≅ ∏ Mat_{nᵢ}(Dᵢ) by Wedderburn-Artin
3. Simple A-modules = simple A/Rad(A)-modules (Rad acts by 0 on simples)
4. Each Wedderburn block corresponds to one iso class of simples
5. Pick rank-1 diagonal idempotents E₁₁ in each block
6. Lift from A/Rad(A) to A using Corollary 9.1.3 -/
/- Note: `IsAlgClosed k` is required because the rank-1 condition `finrank k (e_i · M_j) = δ_{ij}`
   needs End_A(M_i) = k (Schur + algebraic closure). Over non-algebraically-closed fields,
   End_A(M_i) can be a nontrivial division algebra D_i, and the minimal idempotent action
   on M_i has k-dimension [D_i : k] > 1. Counterexample: A = ℍ (quaternions) over k = ℝ. -/
lemma exists_orthogonal_idempotents_for_simples
    [IsAlgClosed k] [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) :
    ∃ (e : ι → A),
      (∀ i, IsIdempotentElem (e i)) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ i j, Module.finrank k (smulRange (k := k) (A := A) (M j) (e i)) =
        if i = j then 1 else 0) := by
  -- Step 1: A is semiprimary (automatic from artinian)
  haveI : IsSemiprimaryRing A := inferInstance
  haveI hss : IsSemisimpleRing (A ⧸ Ring.jacobson A) := IsSemiprimaryRing.isSemisimpleRing
  have hnil := IsSemiprimaryRing.isNilpotent (R := A)
  -- Step 2: Jacobson radical annihilates simple modules
  have hann : ∀ i, Ring.jacobson A ≤ Module.annihilator A (M i) :=
    fun i => IsSemisimpleModule.jacobson_le_annihilator A (M i)
  -- Step 3: Construct orthogonal idempotents ebar in A/J with the rank property
  -- This is the core construction using Wedderburn-Artin decomposition of A/J.
  -- A/J is semisimple and finite-dimensional over algebraically closed k, so
  -- A/J ≅ ∏ Mat_{dᵢ}(k). Each simple A-module (with J acting as 0) corresponds
  -- to exactly one block. Picking E₁₁ in each block gives orthogonal idempotents
  -- with rank-1 action on the corresponding simple module.
  -- The smulRange is computed using the A-action, but since J ≤ ann(Mⱼ),
  -- the action of a ∈ A on Mⱼ depends only on the image of a in A/J.
  -- Key fact: elements in the same coset of A/J act identically on simple modules
  have hsmul_eq : ∀ (a a' : A) (j : ι) (m : M j),
      Ideal.Quotient.mk (Ring.jacobson A) a = Ideal.Quotient.mk (Ring.jacobson A) a' →
      a • m = a' • m := by
    intro a a' j m hq
    have hmem : a - a' ∈ Ring.jacobson A := Ideal.Quotient.eq.mp hq
    have h0 := Module.mem_annihilator.mp (hann j hmem) m
    rwa [sub_smul, sub_eq_zero] at h0
  -- Corollary: smulRange depends only on the A/J-image
  have hsmulRange_eq : ∀ (a a' : A) (j : ι),
      Ideal.Quotient.mk (Ring.jacobson A) a = Ideal.Quotient.mk (Ring.jacobson A) a' →
      smulRange (k := k) (A := A) (M j) a = smulRange (k := k) (A := A) (M j) a' := by
    intro a a' j hq
    have : smulEnd (k := k) (A := A) (M j) a = smulEnd (k := k) (A := A) (M j) a' := by
      ext m; exact hsmul_eq a a' j m hq
    simp only [smulRange, this]
  -- Step 3: Construct orthogonal idempotents in A/J with rank property,
  -- then lift to A. The rank property is stated in terms of the A-action,
  -- but depends only on the A/J-image (by hsmulRange_eq).
  --
  -- We use `suffices` to separate the WA-based construction from the lifting.
  let π := Ideal.Quotient.mk (Ring.jacobson A)
  suffices ∃ (ebar : ι → A ⧸ Ring.jacobson A),
      OrthogonalIdempotents ebar ∧
      ∀ i j (a : A), π a = ebar i →
        Module.finrank k (smulRange (k := k) (A := A) (M j) a) =
          if i = j then 1 else 0 by
    -- Unpack the construction in A/J
    obtain ⟨ebar, hebar_orth, hebar_rank⟩ := this
    -- Kernel of π = J is nilpotent (A is semiprimary)
    have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
      intro x hx
      rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
      obtain ⟨n, hn⟩ := hnil
      exact ⟨n, by
        have := Ideal.pow_mem_pow hx n
        rw [hn] at this
        exact Ideal.mem_bot.mp this⟩
    -- All ebar_i are in range of π (π is surjective)
    have hebar_range : ∀ i, ebar i ∈ π.range :=
      fun i => Ideal.Quotient.mk_surjective (ebar i)
    -- Lift orthogonal idempotents from A/J to A
    obtain ⟨e, he_orth, he_lift⟩ :=
      OrthogonalIdempotents.lift_of_isNilpotent_ker π hker hebar_orth hebar_range
    -- The lifted idempotents satisfy all properties
    refine ⟨e, he_orth.idem, fun i j hij => he_orth.ortho hij, fun i j => ?_⟩
    -- Rank property: π(e i) = ebar i, so smulRange for e i = smulRange for ebar i
    exact hebar_rank i j (e i) (congr_fun he_lift i)
  -- Now prove: ∃ orthogonal idempotents in A/J with the rank-1 action property.
  -- Step A: Wedderburn-Artin decomposition of A/J
  haveI : Module.Finite k (A ⧸ Ring.jacobson A) := inferInstance
  obtain ⟨n, d, hd, ⟨WA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)
  -- Step B: Block-module correspondence (sorry'd)
  -- For each simple A-module M_i (with J acting as 0), there is a unique WA block σ(i)
  -- such that the σ(i)-th block acts nontrivially on M_i. Non-isomorphic modules map
  -- to different blocks (σ is injective).
  -- Additionally, the rank-1 property holds: E₁₁ in the σ(i)-th block acts on M_j
  -- with rank δ_{ij} (via the A-action, using J ≤ ann(M_j) so the action factors
  -- through A/J ≅ ∏ Mat(k)).
  --
  -- This requires infrastructure not currently available:
  -- (i) Module structure on M_j over A/J (from J ≤ ann(M_j)) — available via
  --     Module.IsTorsionBySet.module from Mathlib
  -- (ii) Module structure over the product ∏ Mat_{dⱼ}(k) via the WA equivalence
  -- (iii) Classification of simple modules over ∏ Mat_{dⱼ}(k): each simple module
  --       is concentrated in one block, and Mat_n(k) has a unique simple module
  -- (iv) E₁₁ acts on the standard representation with rank 1
  -- (v) Non-isomorphic A-simples correspond to different blocks
  suffices ∃ (σ : ι → Fin n),
      Function.Injective σ ∧
      ∀ i j (a : A), π a = WA.symm
          (Pi.single (σ i)
            (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k))) →
        Module.finrank k (smulRange (k := k) (A := A) (M j) a) =
          if i = j then 1 else 0 by
    -- Given σ, construct the orthogonal idempotents
    obtain ⟨σ, hσ_inj, hσ_rank⟩ := this
    -- Define ebar_i = WA⁻¹(Pi.single (σ i) (E₁₁ in block σ(i)))
    let ebar : ι → A ⧸ Ring.jacobson A := fun i =>
      WA.symm (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k)))
    refine ⟨ebar, ?_, fun i j a ha => hσ_rank i j a ha⟩
    -- Prove OrthogonalIdempotents ebar
    -- Transport from the product through WA⁻¹
    have horth_prod : OrthogonalIdempotents
        (fun i => (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) k)) := by
      have h_base := orthogonalIdempotents_pi_single
        (fun l => Matrix (Fin (d l)) (Fin (d l)) k)
        (fun l => Matrix.single (0 : Fin (d l)) 0 (1 : k))
        (fun l => matrix_single_zero_isIdempotentElem (0 : Fin (d l)))
      exact h_base.embedding ⟨σ, hσ_inj⟩
    -- Map through WA⁻¹ (ring homomorphism)
    have := horth_prod.map WA.symm.toRingEquiv.toRingHom
    convert this using 1
  -- Now only need to prove: ∃ injective σ with the rank property.
  -- This is the block-module correspondence for Wedderburn-Artin.
  --
  -- Proof outline:
  -- 1. Central idempotents c_l = WA.symm(Pi.single l 1) act on M_j via lifts to A.
  --    Their image on M_j is an A-submodule (by centrality of c_l in A/J and J ≤ ann(M_j)).
  --    By simplicity of M_j, the image is 0 or M_j.
  -- 2. Completeness (∑c_l = 1) and orthogonality (c_l*c_{l'} = 0) give a unique block σ(j).
  -- 3. Non-isomorphic simples go to different blocks (Mat_n(k) has unique simple module,
  --    by IsSimpleRing.isIsotypic).
  -- 4. E₁₁ in block σ(i) acts with rank 1 on M_i (primitive idempotent on the unique simple
  --    module of a matrix ring over an algebraically closed field).
  -- 5. E₁₁ in block σ(i) acts with rank 0 on M_j for j ≠ i (block σ(i) annihilates M_j).
  --
  -- The key sub-arguments are:
  -- (A) Central element lifts commute with A-action on simples (via hsmul_eq + centrality)
  -- (B) Unique simple module over Mat_n(k) (IsSimpleRing.isIsotypic in Mathlib)
  -- (C) finrank of E₁₁-image on the standard representation = 1
  --
  -- Sub-arguments (A) and (B) are individually straightforward; (C) needs a concrete
  -- dimension computation. We decompose into helper sub-sorrys.

  -- Helper: the action of WA.symm(x) on M_j (via any lift) factors through A/J.
  -- Two lifts give the same action (by hsmulRange_eq).
  -- The action of a product x*y is the composition of actions.
  -- Therefore: the "A/J-action" on M_j is well-defined, and WA transports it to a
  -- (∏ Mat(k))-action.

  -- For each j, define σ(j) as the unique block where the central idempotent acts nontrivially.
  -- We construct σ by sorry'ing the existence of the unique block.
  -- Then we prove injectivity and the rank property.

  -- Sub-lemma: block assignment exists
  -- For each simple module M_j, there is a unique block l such that
  -- WA.symm(Pi.single l 1) acts as identity on M_j (i.e., smulRange = ⊤).
  -- Helper: WA.symm preserves multiplication (used for centrality and orthogonality)
  have hWA_mul : ∀ x y : ∀ l, Matrix (Fin (d l)) (Fin (d l)) k,
      WA.symm x * WA.symm y = WA.symm (x * y) := fun x y => (map_mul WA.symm x y).symm
  -- Helper: the central idempotents in A/J
  let c : Fin n → A ⧸ Ring.jacobson A := fun l => WA.symm (Pi.single l 1)
  -- Helper: c_l is central in A/J (commutes with all elements)
  have hc_comm : ∀ (l : Fin n) (q : A ⧸ Ring.jacobson A), c l * q = q * c l := by
    intro l q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    show WA.symm (Pi.single l 1) * π b = π b * WA.symm (Pi.single l 1)
    rw [show π b = WA.symm (WA (π b)) from (WA.symm_apply_apply _).symm]
    rw [hWA_mul, hWA_mul]
    congr 1
    exact pi_single_one_comm l (WA (π b))
  -- Helper: smulRange for a lift of c_l is an A-submodule of M_j
  have hsmulRange_A_sub : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      ∀ (b : A) (x : M j), x ∈ smulRange (k := k) (A := A) (M j) a →
        b • x ∈ smulRange (k := k) (A := A) (M j) a := by
    intro j l a ha b x ⟨m, hm⟩
    rw [← hm]
    -- b • (a • m) = (ba) • m. And π(ba) = π(b) * c_l = c_l * π(b) = π(ab).
    -- So by hsmul_eq, (ba) • m = (ab) • m = a • (b • m)
    have hcomm : π (b * a) = π (a * b) := by
      rw [map_mul, map_mul, ha]; exact (hc_comm l (π b)).symm
    show b • (a • m) ∈ smulRange (k := k) (A := A) (M j) a
    rw [← mul_smul, hsmul_eq _ _ j _ hcomm, mul_smul]
    exact ⟨b • m, rfl⟩
  -- Helper: smulRange for c_l on M_j is ⊥ or ⊤
  have hsmulRange_bot_or_top : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      smulRange (k := k) (A := A) (M j) a = ⊥ ∨
        smulRange (k := k) (A := A) (M j) a = ⊤ := by
    intro j l a ha
    -- Construct an A-submodule with the same carrier
    let N : Submodule A (M j) :=
      { carrier := (smulRange (k := k) (A := A) (M j) a : Set (M j))
        add_mem' := (smulRange (k := k) (A := A) (M j) a).add_mem
        zero_mem' := (smulRange (k := k) (A := A) (M j) a).zero_mem
        smul_mem' := fun b x hx => hsmulRange_A_sub j l a ha b x hx }
    rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
    · left; ext x; constructor
      · intro hx
        have : x ∈ N := hx
        rw [h] at this; exact (Submodule.mem_bot A).mp this
      · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) a).zero_mem
    · right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _
        have : x ∈ N := by rw [h]; exact Submodule.mem_top
        exact this
  -- Complete orthogonal idempotents in the product ring
  have hcoi := completeOrthogonalIdempotents_pi_single_one
    (S := fun l => Matrix (Fin (d l)) (Fin (d l)) k)
  -- Completeness: ∑ c_l = 1 in A/J
  have hc_sum : ∑ l, c l = 1 := by
    show ∑ l, WA.symm (Pi.single l 1) = 1
    rw [← map_sum]; rw [hcoi.complete]; exact map_one WA.symm
  have hblock_exists : ∀ j : ι, ∃ l : Fin n, ∀ a : A,
      π a = WA.symm (Pi.single l 1) →
      smulRange (k := k) (A := A) (M j) a = ⊤ := by
    intro j
    -- If no block acts surjectively, all blocks act as 0 (by bot_or_top + hsmulRange_eq)
    by_contra h_none
    push_neg at h_none
    -- For each l, some lift of c_l has smulRange ≠ ⊤, hence by hsmulRange_eq ALL lifts do too
    -- (smulRange depends only on π a), and by bot_or_top it must be ⊥
    have hall_bot : ∀ l : Fin n, ∀ a : A, π a = c l →
        smulRange (k := k) (A := A) (M j) a = ⊥ := by
      intro l a ha
      obtain ⟨a₀, ha₀, hne⟩ := h_none l
      rcases hsmulRange_bot_or_top j l a₀ ha₀ with h | h
      · -- a₀ gives ⊥, so a gives the same (by hsmulRange_eq)
        rwa [hsmulRange_eq a a₀ j (ha.trans ha₀.symm)]
      · exact absurd h hne
    -- But ∑ c_l = 1, so ∑ (lifts of c_l) acts as identity on M_j
    -- All c_l act as 0, so identity = 0, contradicting M_j nontrivial
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    obtain ⟨m, hm⟩ := exists_ne (0 : M j)
    apply hm
    -- m = 1 • m = (∑ c_l via some lift) • m
    -- Need a lift of ∑ c_l. Pick lifts for each c_l.
    -- For each l, choose a_l with π(a_l) = c_l
    have hlift : ∀ l : Fin n, ∃ a : A, π a = c l :=
      fun l => Ideal.Quotient.mk_surjective (c l)
    choose a_l ha_l using hlift
    -- π(∑ a_l) = ∑ c_l = 1
    have hsum_img : π (∑ l, a_l l) = 1 := by
      rw [map_sum]; simp_rw [ha_l]; exact hc_sum
    -- (∑ a_l) • m = 1 • m = m (by hsmul_eq)
    have hsum_act : (∑ l, a_l l) • m = m := by
      have := hsmul_eq (∑ l, a_l l) 1 j m (by rw [hsum_img, map_one])
      rwa [one_smul] at this
    -- But (∑ a_l) • m = ∑ (a_l • m)
    rw [← hsum_act, Finset.sum_smul]
    -- Each a_l • m = 0 (since smulRange = ⊥ means a_l acts as 0)
    apply Finset.sum_eq_zero
    intro l _
    have h0 := hall_bot l (a_l l) (ha_l l)
    -- smulRange = ⊥ means ∀ m, a • m = 0
    have : a_l l • m ∈ smulRange (k := k) (A := A) (M j) (a_l l) := ⟨m, rfl⟩
    rw [h0] at this; exact (Submodule.mem_bot k).mp this
  -- Sub-lemma: block assignment is unique
  have hblock_unique : ∀ j : ι, ∀ l₁ l₂ : Fin n,
      (∀ a : A, π a = WA.symm (Pi.single l₁ 1) →
        smulRange (k := k) (A := A) (M j) a = ⊤) →
      (∀ a : A, π a = WA.symm (Pi.single l₂ 1) →
        smulRange (k := k) (A := A) (M j) a = ⊤) →
      l₁ = l₂ := by
    intro j l₁ l₂ h₁ h₂
    by_contra hne
    -- Orthogonality: c_{l₁} * c_{l₂} = 0 in A/J
    have horth : c l₁ * c l₂ = 0 :=
      (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).ortho hne
    -- Pick lifts
    obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (c l₁)
    obtain ⟨a₂, ha₂⟩ := Ideal.Quotient.mk_surjective (c l₂)
    -- smulRange for a₂ is ⊤, so a₂ acts surjectively on M_j
    have h₂_top := h₂ a₂ ha₂
    -- a₁ * a₂ has image 0 in A/J (since c_{l₁} * c_{l₂} = 0)
    have hprod_img : π (a₁ * a₂) = 0 := by rw [map_mul, ha₁, ha₂, horth]
    -- So a₁ * a₂ acts as 0 on M_j (same as 0 acts)
    have hprod_zero : ∀ m : M j, (a₁ * a₂) • m = 0 := by
      intro m
      have h0 := hsmul_eq (a₁ * a₂) 0 j m (by rw [hprod_img, map_zero])
      rwa [zero_smul] at h0
    -- But a₁ * a₂ = a₁ * a₂, and a₂ is surjective. So a₁ acts as 0 on the range of a₂.
    -- Since smulRange a₂ = ⊤, a₂ is surjective. So for any m, ∃ m₀ with a₂ • m₀ = m.
    -- Then a₁ • m = a₁ • (a₂ • m₀) = (a₁ * a₂) • m₀ = 0.
    -- So a₁ acts as 0, hence smulRange a₁ = ⊥, contradicting h₁ which says ⊤.
    have h₁_top := h₁ a₁ ha₁
    -- smulRange a₁ = ⊤ means a₁ acts surjectively. But a₁ acts as 0 (shown below).
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    -- a₁ acts as 0: for any m, a₁ • m = 0
    have ha₁_zero : ∀ m : M j, a₁ • m = 0 := by
      intro m
      -- a₂ is surjective on M_j (smulRange = ⊤)
      -- Since smulRange = ⊤ and c_{l₂} is idempotent, a₂ acts surjectively.
      -- c_{l₂} is idempotent: c_{l₂}^2 = c_{l₂}, so a₂^2 acts same as a₂.
      -- a₂ • (a₂ • m) = (a₂*a₂) • m. π(a₂*a₂) = c_{l₂}^2 = c_{l₂} = π(a₂).
      -- So a₂ • (a₂ • m) = a₂ • m. This means a₂ is identity on its range.
      -- Since range = ⊤, a₂ • m' = m' for all m' in M_j... wait no.
      -- Actually: need m ∈ smulRange a₂ = ⊤. So ∃ m₀, a₂ • m₀ = m.
      have : m ∈ smulRange (k := k) (A := A) (M j) a₂ := by
        rw [h₂_top]; exact Submodule.mem_top
      obtain ⟨m₀, hm₀⟩ := this
      -- hm₀ : (smulEnd (M j) a₂) m₀ = m, i.e., a₂ • m₀ = m
      change a₂ • m₀ = m at hm₀
      rw [← hm₀, ← mul_smul]
      exact hprod_zero m₀
    -- smulRange a₁ = ⊥ (since a₁ acts as 0)
    have : smulRange (k := k) (A := A) (M j) a₁ = ⊥ := by
      ext x; simp only [Submodule.mem_bot]; constructor
      · rintro ⟨m, rfl⟩; exact ha₁_zero m
      · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) a₁).zero_mem
    rw [this] at h₁_top
    -- ⊥ = ⊤ contradicts nontriviality of M j
    exact bot_ne_top h₁_top
  -- Define σ
  let σ : ι → Fin n := fun j => (hblock_exists j).choose
  have hσ_spec : ∀ j a, π a = WA.symm (Pi.single (σ j) 1) →
      smulRange (k := k) (A := A) (M j) a = ⊤ :=
    fun j => (hblock_exists j).choose_spec
  -- Helper: c_l is idempotent
  have hc_idem : ∀ l', IsIdempotentElem (c l') :=
    (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).idem
  -- Helper: any lift of c_{σ(p)} acts as identity on M_p
  have hc_identity : ∀ (p : ι) (a : A) (ha : π a = c (σ p)),
      ∀ m : M p, a • m = m := by
    intro p a ha m
    have h_top := hσ_spec p a ha
    have ⟨m₀, hm₀⟩ : m ∈ smulRange (k := k) (A := A) (M p) a := by
      rw [h_top]; exact Submodule.mem_top
    change a • m₀ = m at hm₀
    rw [← hm₀, ← mul_smul]
    exact hsmul_eq (a * a) a p m₀ (by rw [map_mul, ha, (hc_idem (σ p)).eq])
  -- Helper: any lift of c_{l'} (l' ≠ σ(p)) acts as 0 on M_p
  have hc_zero : ∀ (p : ι) (l' : Fin n) (hl' : l' ≠ σ p) (a : A)
      (ha : π a = c l'), ∀ m : M p, a • m = 0 := by
    intro p l' hl' a ha m
    rcases hsmulRange_bot_or_top p l' a ha with h | h
    · have : a • m ∈ smulRange (k := k) (A := A) (M p) a := ⟨m, rfl⟩
      rw [h] at this; exact (Submodule.mem_bot k).mp this
    · exfalso; exact hl' (hblock_unique p l' (σ p)
        (fun a' ha' => hsmulRange_eq a' a p (ha'.trans ha.symm) ▸ h) (hσ_spec p))
  -- Sub-lemma: σ is injective
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    apply hM i j
    -- σ(i) = σ(j), so both M_i and M_j are supported on the same WA block l.
    -- We construct Module (Mat_{d_l}(k)) instances on both, get a Mat-linear equiv,
    -- then convert to A-linear using the decomposition a • m = (WA(π a) l) •_Mat m.
    set l := σ i with hl_def
    have hlj : σ j = l := hij.symm
    -- Lift function: for any q ∈ A/J, pick a ∈ A with π a = q
    let lft : (A ⧸ Ring.jacobson A) → A := fun q => (Ideal.Quotient.mk_surjective q).choose
    have hlft : ∀ q, π (lft q) = q := fun q =>
      (Ideal.Quotient.mk_surjective q).choose_spec
    -- Matrix action on M p: mat • m := (lift of WA.symm(Pi.single l mat)) • m
    let matAct : ∀ p : ι, Matrix (Fin (d l)) (Fin (d l)) k → M p → M p :=
      fun p mat m => lft (WA.symm (Pi.single l mat)) • m
    -- Key decomposition: a • m = matAct p (WA(π a) l) m, when σ p = l.
    have hdecomp : ∀ (p : ι) (hp : σ p = l) (a : A) (m : M p),
        a • m = matAct p ((WA (π a)) l) m := by
      intro p hp a m
      have hid := hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl)
      conv_lhs => rw [show a • m = (a * lft (c l)) • m from by rw [mul_smul, hid m]]
      -- π(a * lft(c l)) = π(a) * c(l) = WA.symm(WA(π a)) * WA.symm(Pi.single l 1)
      --                  = WA.symm(WA(π a) * Pi.single l 1) = WA.symm(Pi.single l ((WA(π a)) l))
      apply hsmul_eq
      rw [map_mul, hlft]
      -- Goal: π a * c l = π (lft (WA.symm (Pi.single l ((WA (π a)) l))))
      rw [hlft]
      -- Goal: π a * c l = WA.symm (Pi.single l ((WA (π a)) l))
      conv_lhs => rw [show π a = WA.symm (WA (π a)) from (WA.symm_apply_apply _).symm,
                       show c l = WA.symm (Pi.single l 1) from rfl]
      rw [hWA_mul]; congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · simp [Pi.mul_apply, show l ≠ l' from fun h => hl' h.symm]
    -- Module axiom helpers
    have hpi_single_mul : ∀ (x y : Matrix (Fin (d l)) (Fin (d l)) k),
        Pi.single l x * Pi.single l y =
          (Pi.single l (x * y) : ∀ l', Matrix (Fin (d l')) (Fin (d l')) k) := by
      intro x y; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.mul_apply, hne, Pi.single_apply]
    have hmatAct_mul : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 * mat2) m = matAct p mat1 (matAct p mat2 m) := by
      intro p mat1 mat2 m
      show lft (WA.symm (Pi.single l (mat1 * mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • (lft (WA.symm (Pi.single l mat2)) • m)
      rw [← mul_smul]; apply hsmul_eq
      rw [map_mul, hlft, hlft]; conv_rhs => rw [hlft]
      rw [hWA_mul, hpi_single_mul]
    have hmatAct_add : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 + mat2) m = matAct p mat1 m + matAct p mat2 m := by
      intro p mat1 mat2 m
      show lft (WA.symm (Pi.single l (mat1 + mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • m + lft (WA.symm (Pi.single l mat2)) • m
      rw [← add_smul]; apply hsmul_eq
      rw [map_add, hlft, hlft]; conv_rhs => rw [hlft]
      rw [show WA.symm (Pi.single l mat1) + WA.symm (Pi.single l mat2) =
            WA.symm (Pi.single l mat1 + Pi.single l mat2) from (map_add WA.symm _ _).symm]
      congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.single_apply, hne]
    have hmatAct_one : ∀ (p : ι) (hp : σ p = l) (m : M p), matAct p 1 m = m := by
      intro p hp m
      exact hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl) m
    have hmatAct_zero : ∀ (p : ι) (m : M p), matAct p 0 m = 0 := by
      intro p m
      have : lft (WA.symm (Pi.single l 0)) • m = (0 : A) • m := by
        apply hsmul_eq; rw [hlft, map_zero, Pi.single_zero, map_zero]
      exact this.trans (zero_smul A m)
    -- Build Module instances for M i and M j
    letI instMi : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M i) :=
      { smul := matAct i
        one_smul := hmatAct_one i rfl
        mul_smul := hmatAct_mul i
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add i
        zero_smul := hmatAct_zero i }
    letI instMj : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M j) :=
      { smul := matAct j
        one_smul := hmatAct_one j hlj
        mul_smul := hmatAct_mul j
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add j
        zero_smul := hmatAct_zero j }
    -- IsSimpleModule: Mat-submodules = A-submodules (same carrier),
    -- since a • m = matAct (WA(π a) l) m and mat • m = lft(WA.symm(Pi.single l mat)) • m
    -- Prove IsSimpleModule for M i and M j over the matrix ring
    -- IsSimpleModule over Matrix: A-submodules = Mat-submodules (same carrier)
    have hMatSimple : ∀ (p : ι) (hp : σ p = l) (inst : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M p)),
        (∀ (mat : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p), mat • m = matAct p mat m) →
        @IsSimpleModule (Matrix (Fin (d l)) (Fin (d l)) k) _ (M p) _ inst := by
      intro p hp inst hsmul_def
      haveI : Nontrivial (M p) := IsSimpleModule.nontrivial A (M p)
      exact
        { eq_bot_or_eq_top := fun N => by
            let N_A : Submodule A (M p) :=
              { carrier := N.carrier
                add_mem' := N.add_mem'
                zero_mem' := N.zero_mem'
                smul_mem' := fun a x hx => by
                  rw [hdecomp p hp a x, ← hsmul_def]; exact N.smul_mem _ hx }
            rcases IsSimpleOrder.eq_bot_or_eq_top N_A with h | h
            · left; ext x; simp only [Submodule.mem_bot]
              exact ⟨fun hx => (Submodule.eq_bot_iff _).mp h x hx,
                     fun hx => hx ▸ N.zero_mem⟩
            · right; ext x
              exact ⟨fun _ => trivial,
                     fun _ => (Submodule.eq_top_iff'.mp h x : x ∈ N_A)⟩ }
    haveI hSimMi := hMatSimple i rfl instMi (fun _ _ => rfl)
    haveI hSimMj := hMatSimple j hlj instMj (fun _ _ => rfl)
    -- Get Mat-linear equiv via uniqueness of simple modules over simple artinian ring
    haveI : IsSimpleRing (Matrix (Fin (d l)) (Fin (d l)) k) := by
      haveI := hd l; exact IsSimpleRing.matrix (Fin (d l)) k
    haveI : IsArtinianRing (Matrix (Fin (d l)) (Fin (d l)) k) := inferInstance
    obtain ⟨f⟩ := @IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule
      (Matrix (Fin (d l)) (Fin (d l)) k) _ _ _ (M i) (M j) _ instMi hSimMi _ instMj hSimMj
    -- Convert Mat-linear equiv to A-linear equiv
    exact ⟨{ toFun := f
             invFun := f.symm
             left_inv := f.left_inv
             right_inv := f.right_inv
             map_add' := f.map_add
             map_smul' := fun a m => by
               -- a • m = matAct ((WA(π a)) l) m, and f is Mat-linear
               simp only [RingHom.id_apply]
               rw [hdecomp i rfl a m, hdecomp j hlj a (f m)]
               exact f.map_smul ((WA (π a)) l) m }⟩
  -- Sub-lemma: rank property
  have hrank : ∀ i j (a : A), π a = WA.symm
      (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k))) →
      Module.finrank k (smulRange (k := k) (A := A) (M j) a) =
        if i = j then 1 else 0 := by
    intro i j a ha
    split_ifs with hij
    · -- Case i = j: E₁₁ in block σ(i) acts with rank 1 on M_i.
      subst hij
      -- Strategy: show Im(E₁₁) = span{v₀} for some nonzero v₀, hence finrank = 1.
      -- Key: corner identity E₁₁·X·E₁₁ = X(0,0)·E₁₁ + A-simplicity of M_i.
      set l := σ i with hl_def
      -- Step 1: a acts idempotently on M_i (since E₁₁² = E₁₁)
      have ha_idem : ∀ m : M i, a • (a • m) = a • m := by
        intro m; rw [← mul_smul]
        exact hsmul_eq (a * a) a i m (by
          rw [map_mul, ha, hWA_mul]; congr 1
          rw [← Pi.single_mul_left, Pi.single_eq_same]; congr 1
          exact (matrix_single_zero_isIdempotentElem (0 : Fin (d l))).eq)
      -- Step 2: Image is nonzero (using two-sided ideal argument).
      -- If a acts as 0 on M_i, then ∀ b₁ b₂, (b₁*a*b₂) acts as 0.
      -- But ∑ E_{j0}·E₁₁·E_{0j} = I in Mat_d(k), so c_l acts as 0.
      -- This contradicts c_l acting as identity on M_i.
      have ha_ne_zero : ∃ m₀ : M i, a • m₀ ≠ 0 := by
        by_contra hall; push_neg at hall
        have h_prod_zero : ∀ (b₁ b₂ : A) (m : M i), (b₁ * a * b₂) • m = 0 := by
          intro b₁ b₂ m
          rw [mul_smul, mul_smul, hall, smul_zero]
        haveI : Nontrivial (M i) := IsSimpleModule.nontrivial A (M i)
        obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M i)
        apply hm₀
        -- Build ∑ E_{j0} · E₁₁ · E_{0j} = I in the quotient
        have h_sum_eq_c : ∑ j : Fin (d l),
            WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)) *
            WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) 0 1)) *
            WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)) = c l := by
          -- Work entirely in the product ring
          simp_rw [hWA_mul, ← Pi.single_mul_left, Pi.single_eq_same,
            Matrix.single_mul_mul_single, one_mul, mul_one]
          simp_rw [show (Matrix.single (0 : Fin (d l)) (0 : Fin (d l)) (1 : k))
            (0 : Fin (d l)) (0 : Fin (d l)) = 1 from by simp [Matrix.single_apply]]
          -- Goal: ∑ x, WA.symm (Pi.single l (Matrix.single x x 1)) = c l
          rw [show c l = WA.symm (Pi.single l 1) from rfl]
          rw [show ∑ x, WA.symm (Pi.single l (Matrix.single x x (1 : k))) =
            WA.symm (∑ x, Pi.single l (Matrix.single x x (1 : k))) from
            (map_sum WA.symm.toRingHom _ _).symm]
          congr 1
          funext l'; by_cases hl' : l' = l
          · subst hl'; simp only [Pi.single_eq_same, Finset.sum_apply]
            ext r s
            simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
            split_ifs with h
            · subst h; simp [Finset.sum_ite_eq, Finset.mem_univ]
            · apply Finset.sum_eq_zero; intro x _
              simp [show ¬(x = r ∧ x = s) from fun ⟨h1, h2⟩ => h (h1.symm.trans h2)]
          · simp [Finset.sum_apply, Pi.single_apply, hl']
        -- Choose lifts and show the sum acts as 0 (by h_prod_zero) yet lifts c_l
        let b₁ : Fin (d l) → A := fun j =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)))).choose
        let b₂ : Fin (d l) → A := fun j =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)))).choose
        have hb₁ : ∀ j, π (b₁ j) = WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)) :=
          fun j => (Ideal.Quotient.mk_surjective _).choose_spec
        have hb₂ : ∀ j, π (b₂ j) = WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)) :=
          fun j => (Ideal.Quotient.mk_surjective _).choose_spec
        have hsum_zero : (∑ j, b₁ j * a * b₂ j) • m₀ = 0 := by
          rw [Finset.sum_smul]; exact Finset.sum_eq_zero (fun j _ => h_prod_zero _ _ m₀)
        have hsum_lifts : π (∑ j, b₁ j * a * b₂ j) = c l := by
          rw [map_sum]; simp_rw [map_mul, hb₁, hb₂, ha]; exact h_sum_eq_c
        rw [← hc_identity i _ hsum_lifts m₀]; exact hsum_zero
      -- Step 3: Pick v₀ in the image, v₀ ≠ 0
      obtain ⟨m₀, hm₀⟩ := ha_ne_zero
      set v₀ := a • m₀ with hv₀_def
      have hav₀ : a • v₀ = v₀ := ha_idem m₀
      -- Step 4: Every element of Im(a) is a k-multiple of v₀
      -- For w = a • m': since M_i is A-simple, m' = b • v₀. Then
      -- w = (a*b) • v₀ = (a*b*a) • v₀ [by hav₀]. Corner identity gives
      -- π(a*b*a) = c_val • π(a), so w = c_val • v₀.
      have hscalar : ∀ m' : M i, a • m' ∈ Submodule.span k {v₀} := by
        intro m'
        haveI : Nontrivial (M i) := IsSimpleModule.nontrivial A (M i)
        -- v₀ generates M_i as A-module
        have hgen : Submodule.span A {v₀} = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {v₀}) with h | h
          · exfalso; exact hm₀ ((Submodule.eq_bot_iff _).mp h v₀ (Submodule.subset_span rfl))
          · exact h
        have hm'_mem : m' ∈ Submodule.span A {v₀} := hgen ▸ Submodule.mem_top
        rw [Submodule.mem_span_singleton] at hm'_mem
        obtain ⟨b, rfl⟩ := hm'_mem
        -- a • (b • v₀) = (a*b) • v₀ = (a*b*a) • v₀ (using hav₀)
        rw [← mul_smul]
        have hab_eq : (a * b) • v₀ = (a * b * a) • v₀ := by
          conv_lhs => rw [← hav₀]; rw [← mul_smul]
        rw [hab_eq]
        -- Corner identity: π(a*b*a) = WA.symm(Pi.single l (E₁₁·WA(πb)·E₁₁))
        --                            = WA.symm(Pi.single l (c_val • E₁₁)) = c_val • π(a)
        set c_val := (WA (π b)) l 0 0 with hc_val_def
        have hpi_aba : π (a * b * a) = π ((algebraMap k A c_val) * a) := by
          -- Both sides equal WA.symm(Pi.single l (c_val • E₁₁))
          -- Compute LHS: π(a*b*a) → WA.symm(Pi.single l (c_val•E₁₁))
          -- Work in the product ring via WA
          apply WA.injective
          have hWAa : WA (π a) = Pi.single l
              (Matrix.single (0 : Fin (d l)) 0 (1 : k)) := by
            rw [ha]; exact WA.apply_symm_apply _
          -- LHS: WA(π(a*b*a)) = WA(πa) * WA(πb) * WA(πa)
          simp only [map_mul, hWAa]
          -- Pi.single l E₁₁ * WA(πb) * Pi.single l E₁₁ = Pi.single l (c_val • E₁₁)
          rw [← Pi.single_mul_left, ← Pi.single_mul_left,
              Pi.single_eq_same, matrix_single_corner]
          -- RHS: WA(π(algebraMap k A c_val)) * Pi.single l E₁₁
          rw [Ideal.Quotient.mk_algebraMap, WA.commutes]
          -- Goal: Pi.single l (c_val • E₁₁) = algebraMap k _ c_val * Pi.single l E₁₁
          -- algebraMap k (∏ Mat) c_val * Pi.single l E₁₁ = Pi.single l (c_val • E₁₁)
          ext l'; by_cases hl' : l' = l
          · subst hl'
            simp only [Pi.single_eq_same, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
              Pi.smul_apply, Pi.one_apply, Matrix.smul_apply, smul_eq_mul, one_mul,
              smul_mul_assoc, hc_val_def]
          · simp [Pi.mul_apply, Pi.single_apply, hl']
        -- Conclude: (a*b*a) • v₀ = c_val • v₀
        have : (a * b * a) • v₀ = c_val • v₀ := by
          have h := hsmul_eq (a * b * a) ((algebraMap k A c_val) * a) i v₀ hpi_aba
          rw [h, mul_smul, hav₀, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem _ c_val (Submodule.subset_span rfl)
      -- Step 5: smulRange = span{v₀}
      have hspan : smulRange (k := k) (A := A) (M i) a = Submodule.span k {v₀} := by
        ext w; constructor
        · rintro ⟨m', rfl⟩; exact hscalar m'
        · intro hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c_val, rfl⟩ := hw
          exact ⟨c_val • m₀, by simp [smulEnd, smul_comm a c_val m₀, hv₀_def]⟩
      rw [hspan]; exact finrank_span_singleton hm₀
    · -- Case i ≠ j: E₁₁ in block σ(i) acts as 0 on M_j.
      -- Pi.single (σ i) (E₁₁) is "supported" on block σ(i).
      -- Block σ(j) ≠ σ(i) (by injectivity of σ) acts as identity on M_j.
      -- Block σ(i) acts as 0 on M_j.
      -- Hence E₁₁ in block σ(i) acts as 0 on M_j.
      -- smulRange = ⊥, finrank = 0.
      -- Key: Pi.single (σ i) (E₁₁) = (Pi.single (σ i) 1) * Pi.single (σ i) (E₁₁)
      -- The first factor (central idempotent of block σ(i)) acts as 0 on M_j.
      -- So the product acts as 0, giving smulRange = ⊥.
      have hσ_ne : σ i ≠ σ j := fun h => hij (hσ_inj h)
      -- c_{σ(i)} acts as 0 on M_j (block σ(i) is not the active block for M_j)
      -- First show: smulRange for c_{σ(i)} on M_j is ⊥
      obtain ⟨a_c, ha_c⟩ := Ideal.Quotient.mk_surjective (c (σ i))
      have hc_bot : smulRange (k := k) (A := A) (M j) a_c = ⊥ := by
        rcases hsmulRange_bot_or_top j (σ i) a_c ha_c with h | h
        · exact h
        · -- If ⊤, then σ(j) = σ(i) by uniqueness, contradicting hσ_ne
          exfalso; exact hσ_ne (hblock_unique j (σ i) (σ j)
            (fun a' ha' => hsmulRange_eq a' a_c j (ha'.trans ha_c.symm) ▸ h)
            (hσ_spec j))
      -- c_{σ(i)} acts as 0 on M_j: for all m, a_c • m = 0
      have hc_zero : ∀ m : M j, a_c • m = 0 := by
        intro m
        have : a_c • m ∈ smulRange (k := k) (A := A) (M j) a_c := ⟨m, rfl⟩
        rw [hc_bot] at this; exact (Submodule.mem_bot k).mp this
      -- π(a) = c_{σ(i)} * π(a) (since Pi.single (σ i) E₁₁ = Pi.single (σ i) 1 * Pi.single (σ i) E₁₁)
      have hfactor : π a = c (σ i) * π a := by
        rw [ha, show c (σ i) = WA.symm (Pi.single (σ i) 1) from rfl, hWA_mul]
        congr 1
        rw [← Pi.single_mul_left]; simp
      -- Therefore a acts as 0 on M_j: a • m = a_c • (a • m) = 0
      have ha_zero : ∀ m : M j, a • m = 0 := by
        intro m
        have := hsmul_eq (a_c * a) a j m (by rw [map_mul, ha_c]; exact hfactor.symm)
        rw [mul_smul] at this
        rw [← this, hc_zero]
      -- smulRange = ⊥, finrank = 0
      have hbot : smulRange (k := k) (A := A) (M j) a = ⊥ := by
        ext x; simp only [Submodule.mem_bot]; constructor
        · rintro ⟨m, rfl⟩; exact ha_zero m
        · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) a).zero_mem
      rw [hbot]; simp
  exact ⟨σ, hσ_inj, hrank⟩

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

/-- Conjugate idempotents give isomorphic left ideals as A-modules.
If u * e₁ * u⁻¹ = e₂, then A·e₁ ≅ A·e₂ via right multiplication by u⁻¹.
Key: a * e₁ * u⁻¹ = (a * u⁻¹) * e₂ and b * e₂ * u = (b * u) * e₁. -/
def leftIdeal_equiv_of_conjugate
    (e₁ e₂ : A) (u : Aˣ) (hconj : ↑u * e₁ * ↑u⁻¹ = e₂) :
    ↥(Submodule.span A ({e₁} : Set A)) ≃ₗ[A]
    ↥(Submodule.span A ({e₂} : Set A)) where
  toFun := fun ⟨x, hx⟩ => by
    refine ⟨x * ↑u⁻¹, ?_⟩
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a * ↑u⁻¹, ?_⟩
    simp only [smul_eq_mul]
    -- Goal: (a * ↑u⁻¹) * e₂ = a * e₁ * ↑u⁻¹
    rw [← hconj]
    -- Goal: (a * ↑u⁻¹) * (↑u * e₁ * ↑u⁻¹) = a * e₁ * ↑u⁻¹
    simp only [← mul_assoc]
    rw [show a * ↑u⁻¹ * ↑u = a from by rw [mul_assoc, Units.inv_mul, mul_one]]
  invFun := fun ⟨y, hy⟩ => by
    refine ⟨y * ↑u, ?_⟩
    rw [Submodule.mem_span_singleton] at hy ⊢
    obtain ⟨b, rfl⟩ := hy
    refine ⟨b * ↑u, ?_⟩
    simp only [smul_eq_mul]
    -- Goal: (b * ↑u) * e₁ = b * e₂ * ↑u
    rw [← hconj]
    simp only [← mul_assoc]
    rw [show b * ↑u * e₁ * ↑u⁻¹ * ↑u = b * ↑u * e₁ from by
      rw [mul_assoc (b * ↑u * e₁), Units.inv_mul, mul_one]]
  left_inv := fun ⟨x, _⟩ => by
    ext; show x * ↑u⁻¹ * ↑u = x
    rw [mul_assoc, Units.inv_mul, mul_one]
  right_inv := fun ⟨y, _⟩ => by
    ext; show y * ↑u * ↑u⁻¹ = y
    rw [mul_assoc, Units.mul_inv, mul_one]
  map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => by ext; simp [add_mul]
  map_smul' := fun r ⟨x, _⟩ => by ext; show r * x * ↑u⁻¹ = r * (x * ↑u⁻¹); rw [mul_assoc]

/-- For complete orthogonal idempotents e₁,...,eₙ in a ring A, the left ideals Aeᵢ form
an internal direct sum decomposition of A. The canonical map ⨁ᵢ Aeᵢ → A is bijective. -/
lemma isInternal_leftIdeals_of_completeOrthogonalIdempotents
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (fun i => Submodule.span A ({e i} : Set A)) := by
  set N := fun i => Submodule.span A ({e i} : Set A) with hN
  -- Helper: elements of Aeᵢ have the form a * eᵢ
  have hmem : ∀ i (x : A), x ∈ N i ↔ ∃ a, a * e i = x := by
    intro i x; rw [hN, Submodule.mem_span_singleton]; rfl
  -- Helper: (a * eᵢ) * eⱼ = δᵢⱼ · (a * eᵢ)
  have hmul_right : ∀ i j (a : A), a * e i * e j = if i = j then a * e i else 0 := by
    intro i j a
    split_ifs with hij
    · subst hij; rw [mul_assoc, he.toOrthogonalIdempotents.idem]
    · rw [mul_assoc, he.toOrthogonalIdempotents.ortho hij, mul_zero]
  -- Show bijectivity of the canonical map
  -- Right-multiplication by eₖ extracts the k-th component from elements of Aeⱼ
  have hmul_component : ∀ k j (x : ↥(N j)), (↑x : A) * e k = if j = k then ↑x else 0 := by
    intro k j ⟨x, hx⟩
    rw [hmem] at hx; obtain ⟨c, rfl⟩ := hx
    simp [hmul_right]
  -- For any direct sum element, right-multiply by eₖ extracts the k-th component
  have hextract : ∀ (f : ⨁ j, ↥(N j)) (k : ι),
      (DirectSum.coeLinearMap N f) * e k = ↑(f k) := by
    intro f k
    have hsum : DirectSum.coeLinearMap N f = ∑ j, ↑(f j) := by
      conv_lhs =>
        rw [show f = ∑ j ∈ Finset.univ, DirectSum.of _ j (f j) from
          (DirectSum.sum_univ_of f).symm]
      simp [DirectSum.coeLinearMap_of]
    rw [hsum, Finset.sum_mul]
    conv_lhs =>
      arg 2; ext j
      rw [hmul_component k j (f j)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  constructor
  · -- Injective
    intro f g hfg
    have hfg' : DirectSum.coeLinearMap N f = DirectSum.coeLinearMap N g := hfg
    have hcomp : ∀ i, (f i : A) = (g i : A) := by
      intro i
      have h1 := hextract f i
      have h2 := hextract g i
      rw [hfg'] at h1
      exact h1.symm.trans h2
    exact DFinsupp.ext fun i => Subtype.ext (hcomp i)
  · -- Surjective: a = ∑ (a * eᵢ) with a * eᵢ ∈ Aeᵢ
    intro a
    refine ⟨∑ i, DirectSum.of (fun i => ↥(N i)) i
        ⟨a * e i, Submodule.smul_mem _ a (Submodule.subset_span rfl)⟩, ?_⟩
    -- Goal reduces to ∑ (a * eᵢ) = a * ∑ eᵢ = a
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    rw [show ∑ i, a * e i = a * ∑ i, e i from (Finset.mul_sum ..).symm,
      he.complete, mul_one]

/-- A left ideal A·e is indecomposable if the Hom dimension property holds:
dim Hom(Ae, Mⱼ) = 0 for all j except exactly one j = i₀ where it equals 1.
The argument: if Ae = Q₁ ⊕ Q₂, then Hom(Ae, Mⱼ) = Hom(Q₁, Mⱼ) ⊕ Hom(Q₂, Mⱼ),
so dim Hom(Ae, Mⱼ) = dim Hom(Q₁, Mⱼ) + dim Hom(Q₂, Mⱼ). Since dim = 1 for j = i₀,
one of Q₁ or Q₂ has Hom = 0 to all simples, hence is zero (by Nakayama).

The exhaustiveness hypothesis `hM_exhaustive` is needed: the argument that
"Hom to all simples is zero ⟹ module is zero" requires that every simple module
is isomorphic to some Mⱼ in the family. -/
lemma leftIdeal_indecomposable_of_hom_delta
    [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S]
      [IsSimpleModule A S], ∃ i, Nonempty (S ≃ₗ[A] M i))
    (e : A) (he : IsIdempotentElem e)
    (i₀ : ι) (hdim : ∀ j, Module.finrank k
      (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M j) =
      if i₀ = j then 1 else 0) :
    Etingof.IsIndecomposable A
      ↥(Submodule.span A ({e} : Set A)) := by
  set S := Submodule.span A ({e} : Set A) with hS_def
  constructor
  · -- Nontriviality: dim Hom(Ae, M_{i₀}) = 1 ≠ 0, so Ae ≠ 0
    have h1 := hdim i₀
    simp only [ite_true] at h1
    -- finrank = 1 implies the Hom space is nontrivial
    by_contra h_triv
    rw [not_nontrivial_iff_subsingleton] at h_triv
    have h0 : Module.finrank k (↥S →ₗ[A] M i₀) = 0 := by
      haveI := h_triv
      haveI : Subsingleton (↥S →ₗ[A] M i₀) :=
        ⟨fun f g => LinearMap.ext fun x => by
          have := Subsingleton.elim x 0
          simp [this]⟩
      exact Module.finrank_zero_of_subsingleton
    linarith
  · -- For any complement decomposition, one summand must be zero.
    -- We show: if both W₁ ≠ ⊥ and W₂ ≠ ⊥, each has a nonzero map
    -- to some M_j (via simple quotients), which we extend to Ae using
    -- the complement. This forces dim Hom(Ae, M_{i₀}) ≥ 2, contradicting
    -- hdim which says dim = 1.
    intro W₁ W₂ hcompl
    by_contra h_both
    push_neg at h_both
    obtain ⟨hW₁, hW₂⟩ := h_both
    -- Set up the complement decomposition equivalence
    set equiv := Submodule.prodEquivOfIsCompl W₁ W₂ hcompl
    -- Project from S to W₁ (resp. W₂) via the complement
    -- proj₁ : S → W₁ sends s to its W₁-component
    let proj₁ : ↥S →ₗ[A] ↥W₁ :=
      (LinearMap.fst A ↥W₁ ↥W₂).comp equiv.symm.toLinearMap
    let proj₂ : ↥S →ₗ[A] ↥W₂ :=
      (LinearMap.snd A ↥W₁ ↥W₂).comp equiv.symm.toLinearMap
    -- Simple modules over a finite-dimensional algebra are finite-dimensional
    -- (they're quotients of A as a k-module, since A·v = M for any nonzero v)
    have hM_fin : ∀ j, Module.Finite k (M j) := by
      intro j
      haveI : Nontrivial (M j) := @IsSimpleModule.nontrivial A _ (M j) _ _ _
      obtain ⟨v, hv⟩ := exists_ne (0 : M j)
      -- The map a ↦ a • v is a k-linear surjection from A to M j
      let φ : A →ₗ[k] M j := (LinearMap.toSpanSingleton A (M j) v).restrictScalars k
      have hφ_surj : Function.Surjective φ := by
        intro m
        -- Range of φ, viewed as an A-submodule, is nonzero (contains v = 1 • v)
        -- By simplicity, it equals all of M j
        have hrange : LinearMap.range (LinearMap.toSpanSingleton A (M j) v) = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top
            (LinearMap.range (LinearMap.toSpanSingleton A (M j) v)) with h | h
          · exfalso
            have hmem : v ∈ LinearMap.range (LinearMap.toSpanSingleton A (M j) v) := by
              exact ⟨1, one_smul A v⟩
            rw [h] at hmem
            simp [Submodule.mem_bot] at hmem
            exact hv hmem
          · exact h
        exact LinearMap.range_eq_top.mp hrange m
      exact Module.Finite.of_surjective φ hφ_surj
    -- Setup: noetherian instances for submodules
    haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
    haveI : IsNoetherianRing A := inferInstance
    haveI : IsNoetherian A ↥S := isNoetherian_submodule' S
    haveI : IsNoetherian A ↥W₁ := isNoetherian_submodule' W₁
    haveI : IsNoetherian A ↥W₂ := isNoetherian_submodule' W₂
    haveI hW₁_nt : Nontrivial ↥W₁ := W₁.nontrivial_iff_ne_bot.mpr hW₁
    haveI hW₂_nt : Nontrivial ↥W₂ := W₂.nontrivial_iff_ne_bot.mpr hW₂
    -- Get coatoms (maximal proper submodules) — exist since modules are finite/noetherian
    obtain ⟨N₁, hN₁⟩ := IsCoatomic.exists_coatom (α := Submodule A ↥W₁)
    obtain ⟨N₂, hN₂⟩ := IsCoatomic.exists_coatom (α := Submodule A ↥W₂)
    -- The quotients W₁/N₁ and W₂/N₂ are simple modules
    haveI hsimp₁ : IsSimpleModule A (↥W₁ ⧸ N₁) := isSimpleModule_iff_isCoatom.mpr hN₁
    haveI hsimp₂ : IsSimpleModule A (↥W₂ ⧸ N₂) := isSimpleModule_iff_isCoatom.mpr hN₂
    -- By exhaustiveness, each simple quotient ≅ some M_j
    obtain ⟨j₁, ⟨iso₁⟩⟩ := hM_exhaustive (↥W₁ ⧸ N₁)
    obtain ⟨j₂, ⟨iso₂⟩⟩ := hM_exhaustive (↥W₂ ⧸ N₂)
    -- Build nonzero maps S → M_j: compose proj → quotient → iso
    let f₁ : ↥S →ₗ[A] M j₁ :=
      iso₁.toLinearMap.comp (N₁.mkQ.comp proj₁)
    let f₂ : ↥S →ₗ[A] M j₂ :=
      iso₂.toLinearMap.comp (N₂.mkQ.comp proj₂)
    -- f₁ is nonzero: proj₁ is surjective onto W₁, and mkQ ∘ iso₁ is nonzero
    -- Helper: proj₁ ∘ equiv is fst (proj₁ (equiv (w₁, w₂)) = w₁)
    have hproj₁_equiv : ∀ (w₁ : ↥W₁) (w₂ : ↥W₂), proj₁ (equiv (w₁, w₂)) = w₁ := by
      intro w₁ w₂
      show (LinearMap.fst A ↥W₁ ↥W₂) (equiv.symm (equiv (w₁, w₂))) = w₁
      rw [equiv.symm_apply_apply]; rfl
    have hproj₂_equiv : ∀ (w₁ : ↥W₁) (w₂ : ↥W₂), proj₂ (equiv (w₁, w₂)) = w₂ := by
      intro w₁ w₂
      show (LinearMap.snd A ↥W₁ ↥W₂) (equiv.symm (equiv (w₁, w₂))) = w₂
      rw [equiv.symm_apply_apply]; rfl
    -- f₁ is nonzero
    have hf₁_ne : f₁ ≠ 0 := by
      intro hf
      apply hN₁.1  -- N₁ ≠ ⊤
      rw [Submodule.eq_top_iff']
      intro w
      rw [← Submodule.Quotient.mk_eq_zero]
      have h1 : f₁ (equiv (w, 0)) = 0 := by simp [hf]
      simp only [f₁, LinearMap.comp_apply, hproj₁_equiv] at h1
      -- h1 : ↑iso₁ (N₁.mkQ w) = 0, want: N₁.mkQ w = 0
      -- ↑iso₁ is the coercion to LinearMap; convert to equiv application
      change iso₁ (N₁.mkQ w) = 0 at h1
      exact iso₁.map_eq_zero_iff.mp h1
    -- f₂ is nonzero
    have hf₂_ne : f₂ ≠ 0 := by
      intro hf
      apply hN₂.1
      rw [Submodule.eq_top_iff']
      intro w
      rw [← Submodule.Quotient.mk_eq_zero]
      have h1 : f₂ (equiv (0, w)) = 0 := by simp [hf]
      simp only [f₂, LinearMap.comp_apply, hproj₂_equiv] at h1
      change iso₂ (N₂.mkQ w) = 0 at h1
      exact iso₂.map_eq_zero_iff.mp h1
    -- j₁ = i₀ and j₂ = i₀: if not, finrank = 0, meaning the Hom space is trivial
    -- (requires Module.Finite k for the Hom spaces, which follows from
    -- simple modules being finite-dimensional quotients of A)
    -- The Hom spaces are finite-dimensional over k (A-linear maps from a f.d. module
    -- to a f.d. module form a finite-dimensional k-vector space, being a subspace of
    -- the k-linear Hom space)
    have hHom_fin : ∀ j, Module.Finite k (↥S →ₗ[A] M j) := by
      intro j
      haveI := hM_fin j
      -- S is finite over k (submodule of finite-dimensional A)
      haveI : Module.Finite k ↥S :=
        Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
      -- The A-linear Hom space embeds k-linearly into the k-linear Hom space
      exact Module.Finite.of_injective
        (LinearMap.restrictScalarsₗ k A (↥S) (M j) k)
        (LinearMap.restrictScalars_injective k)
    have hj₁ : j₁ = i₀ := by
      by_contra h
      apply hf₁_ne
      have h0 : Module.finrank k (↥S →ₗ[A] M j₁) = 0 := by
        rw [hdim j₁, if_neg (Ne.symm h)]
      haveI := hHom_fin j₁
      rw [Module.finrank_eq_zero_iff] at h0
      obtain ⟨a, ha_ne, ha_smul⟩ := h0 f₁
      calc f₁ = (1 : k) • f₁ := (one_smul k f₁).symm
        _ = (a⁻¹ * a) • f₁ := by rw [inv_mul_cancel₀ ha_ne]
        _ = a⁻¹ • (a • f₁) := by rw [smul_smul]
        _ = a⁻¹ • 0 := by rw [ha_smul]
        _ = 0 := smul_zero _
    have hj₂ : j₂ = i₀ := by
      by_contra h
      apply hf₂_ne
      have h0 : Module.finrank k (↥S →ₗ[A] M j₂) = 0 := by
        rw [hdim j₂, if_neg (Ne.symm h)]
      haveI := hHom_fin j₂
      rw [Module.finrank_eq_zero_iff] at h0
      obtain ⟨a, ha_ne, ha_smul⟩ := h0 f₂
      calc f₂ = (1 : k) • f₂ := (one_smul k f₂).symm
        _ = (a⁻¹ * a) • f₂ := by rw [inv_mul_cancel₀ ha_ne]
        _ = a⁻¹ • (a • f₂) := by rw [smul_smul]
        _ = a⁻¹ • 0 := by rw [ha_smul]
        _ = 0 := smul_zero _
    -- Now both f₁, f₂ : S →ₗ[A] M i₀ are nonzero.
    -- f₁ kills W₂ (factors through proj₁ which kills W₂),
    -- f₂ kills W₁ (factors through proj₂ which kills W₁).
    -- These are linearly independent, giving finrank ≥ 2, contradicting hdim = 1.
    -- f₁ kills W₂ (factors through proj₁ which kills W₂)
    have hf₁_W₂ : ∀ (w₂ : ↥W₂), f₁ (equiv (0, w₂)) = 0 := by
      intro w₂
      simp only [f₁, LinearMap.comp_apply, hproj₁_equiv]
      simp [map_zero]
    -- f₂ kills W₁ (factors through proj₂ which kills W₁)
    have hf₂_W₁ : ∀ (w₁ : ↥W₁), f₂ (equiv (w₁, 0)) = 0 := by
      intro w₁
      simp only [f₂, LinearMap.comp_apply, hproj₂_equiv]
      simp [map_zero]
    -- Cast f₂ into the same Hom space as f₁ using j₂ = j₁ (= i₀)
    -- Then show linear independence in Hom(S, M j₁) and get finrank ≥ 2,
    -- contradicting hdim j₁ = 1.
    have hj₁₂ : j₁ = j₂ := hj₁.trans hj₂.symm
    -- f₂ cast to the same type as f₁
    let f₂' : ↥S →ₗ[A] M j₁ := hj₁₂ ▸ f₂
    have hf₂'_ne : f₂' ≠ 0 := by
      intro h; apply hf₂_ne; simp only [f₂'] at h; exact hj₁₂ ▸ h
    have hf₂'_W₁ : ∀ (w₁ : ↥W₁), f₂' (equiv (w₁, 0)) = 0 := by
      intro w₁; simp only [f₂']; subst hj₁₂; exact hf₂_W₁ w₁
    -- f₁ and f₂' are linearly independent
    haveI := hHom_fin j₁
    have h_li : LinearIndependent k ![f₁, f₂'] := by
      rw [linearIndependent_fin2]
      refine ⟨?_, ?_⟩
      · -- Need ![f₁, f₂'] 1 ≠ 0, i.e., f₂' ≠ 0
        simp only [Matrix.cons_val_one, Matrix.head_cons]
        exact hf₂'_ne
      · intro a ha
        -- ha : a • f₂' = f₁
        simp only [Matrix.cons_val_one, Matrix.head_cons,
                    Matrix.cons_val_zero] at ha
        -- f₁ = a • f₂'. f₁ kills W₂, so a • f₂' kills W₂ too.
        -- f₂' kills W₁. So for any s = equiv(w₁, w₂):
        -- f₁(s) = f₁(w₁,0) + f₁(0,w₂) = a•f₂'(w₁,0) + 0 = 0 + 0 = 0
        exfalso; apply hf₁_ne; ext s
        obtain ⟨⟨w₁, w₂⟩, rfl⟩ := equiv.surjective s
        have h1 := hf₁_W₂ w₂
        have h2 := hf₂'_W₁ w₁
        have : f₁ (equiv (w₁, w₂)) = f₁ (equiv (w₁, 0)) + f₁ (equiv (0, w₂)) := by
          rw [← map_add, ← equiv.map_add]; congr 1; simp [Prod.add_def]
        simp only [LinearMap.zero_apply]
        rw [this, h1, add_zero, ← ha, LinearMap.smul_apply, h2, smul_zero]
    have h_card : Fintype.card (Fin 2) ≤ Module.finrank k (↥S →ₗ[A] M j₁) :=
      h_li.fintype_card_le_finrank
    simp at h_card
    have h1 := hdim j₁
    rw [if_pos hj₁.symm] at h1
    omega

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
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S]
      [IsSimpleModule A S], ∃ i, Nonempty (S ≃ₗ[A] M i)) :
    ∃ (P : ι → Type uA)
      (_ : ∀ i, AddCommGroup (P i))
      (_ : ∀ i, Module A (P i))
      (_ : ∀ i, Module k (P i))
      (_ : ∀ i, IsScalarTower k A (P i))
      (_ : ∀ i, SMulCommClass A k (P i))
      (_ : ∀ i, Module.Projective A (P i))
      (_ : ∀ i, Module.Finite A (P i))
      (_ : ∀ i, Etingof.IsIndecomposable A (P i)),
      ∀ i j, Module.finrank k (P i →ₗ[A] M j) =
        if i = j then 1 else 0 := by
  -- Step 1: A is artinian (finite-dimensional algebra over a field)
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  -- Step 2: Get orthogonal idempotents from Wedderburn-Artin
  obtain ⟨e, he_idem, he_orth, he_dim⟩ :=
    Theorem921.exists_orthogonal_idempotents_for_simples
      (k := k) M hM
  -- Step 3: Define P i = Submodule.span A {e i} (= left ideal Ae_i)
  -- The Hom dimension property follows from he_dim and the
  -- Hom ≅ eM isomorphism.
  have hdim_hom : ∀ i j, Module.finrank k
      (↥(Submodule.span A ({e i} : Set A)) →ₗ[A] M j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [Theorem921.finrank_hom_leftIdeal_eq (k := k)
      (e i) (he_idem i)]
    exact he_dim i j
  exact ⟨fun i => ↥(Submodule.span A ({e i} : Set A)),
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance,
    fun i => Theorem921.leftIdeal_projective (e i) (he_idem i),
    fun i => Theorem921.leftIdeal_finite (e i),
    fun i => Theorem921.leftIdeal_indecomposable_of_hom_delta
      (k := k) M hM hM_exhaustive (e i) (he_idem i) i
      (hdim_hom i),
    hdim_hom⟩

/-! ### Local endomorphism ring and uniqueness of indecomposable projectives

For an indecomposable finitely generated module P over a finite-dimensional algebra,
End_A(P) is a local ring (Fitting's lemma + nilpotent sum closure). This gives
the key isomorphism lemma for projective covers.
-/

section LocalEndomorphismRing

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- The endomorphism ring of an indecomposable finite-dimensional module is local.
This follows from Fitting's lemma: every endomorphism is either bijective (= unit) or
nilpotent, and the sum of nilpotent endomorphisms is nilpotent (Lemma 3.8.2). -/
theorem Etingof.IsIndecomposable.isLocalRing_end
    {W : Type*} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] (hW : Etingof.IsIndecomposable A W) :
    IsLocalRing (Module.End A W) where
  exists_pair_ne := by
    haveI := hW.1
    exact ⟨1, 0, one_ne_zero⟩
  isUnit_or_isUnit_of_add_one := by
    intro a b hab
    rcases Etingof.endo_indecomposable_iso_or_nilpotent k A W hW a with ha | ha
    · left; exact (Module.End.isUnit_iff a).mpr ha
    · right
      have hb : b = 1 - a := eq_sub_of_add_eq' hab
      rw [hb]; exact ha.isUnit_one_sub

/-- An endomorphism of an indecomposable module whose range is contained in a proper
submodule must be nilpotent (not bijective). -/
theorem Etingof.endo_nilpotent_of_range_le_proper
    {W : Type*} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] (hW : Etingof.IsIndecomposable A W)
    (θ : W →ₗ[A] W) (N : Submodule A W) (hN : N ≠ ⊤) (hθ : LinearMap.range θ ≤ N) :
    IsNilpotent θ := by
  rcases Etingof.endo_indecomposable_iso_or_nilpotent k A W hW θ with hbij | hnil
  · exfalso
    have hrange : LinearMap.range θ = ⊤ :=
      LinearMap.range_eq_top.mpr hbij.2
    exact hN (top_le_iff.mp (hrange ▸ hθ))
  · exact hnil

/-- Two indecomposable finitely generated projective modules with nonzero Hom to the
same simple module are isomorphic.

**Proof using Fitting's lemma (avoids Nakayama/unique maximal submodule):**
1. Both P, P' surject onto M (nonzero map to simple = surjective).
2. By projectivity, get f: P → P' and g: P' → P with ψ ∘ f = φ and φ ∘ g = ψ.
3. Then φ ∘ (g ∘ f - id) = 0, so range(g ∘ f - id) ≤ ker(φ).
4. ker(φ) is proper. By Fitting, g ∘ f - id is nilpotent, so g ∘ f is a unit.
5. Similarly f ∘ g is a unit.
6. f is bijective → P ≅ P'. -/
theorem Etingof.indecomposable_projective_iso_of_hom
    {P : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P]
    (hP : Etingof.IsIndecomposable A P)
    {P' : Type*} [AddCommGroup P'] [Module A P'] [Module k P'] [IsScalarTower k A P']
    [FiniteDimensional k P'] [Module.Projective A P']
    (hP' : Etingof.IsIndecomposable A P')
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (φ : P →ₗ[A] M) (hφ : φ ≠ 0) (ψ : P' →ₗ[A] M) (hψ : ψ ≠ 0) :
    Nonempty (P ≃ₗ[A] P') := by
  -- Step 1: φ and ψ are surjective (nonzero map to simple module)
  have hφ_surj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    exact (eq_bot_or_eq_top (LinearMap.range φ)).resolve_left
      (LinearMap.range_eq_bot.not.mpr hφ)
  have hψ_surj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top]
    exact (eq_bot_or_eq_top (LinearMap.range ψ)).resolve_left
      (LinearMap.range_eq_bot.not.mpr hψ)
  -- Step 2: Lift φ through ψ and ψ through φ using projectivity
  obtain ⟨f, hf⟩ := Module.projective_lifting_property ψ φ hψ_surj
  obtain ⟨g, hg⟩ := Module.projective_lifting_property φ ψ hφ_surj
  -- Step 3: g ∘ f - id has range in ker(φ) because φ ∘ (g ∘ f) = φ
  have hgf_range :
      LinearMap.range (g.comp f - LinearMap.id) ≤ LinearMap.ker φ := by
    intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    rw [← hx]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    have h1 : φ (g (f x)) = ψ (f x) := LinearMap.congr_fun hg (f x)
    have h2 : ψ (f x) = φ x := LinearMap.congr_fun hf x
    rw [map_sub, h1, h2, sub_self]
  -- ker(φ) is proper because φ ≠ 0
  have hker_proper : LinearMap.ker φ ≠ ⊤ := by
    intro h; exact hφ (LinearMap.ker_eq_top.mp h)
  -- Step 4: By Fitting, g ∘ f - id is nilpotent, so g ∘ f is a unit
  have hgf_nilp : IsNilpotent (g.comp f - LinearMap.id) :=
    Etingof.endo_nilpotent_of_range_le_proper (k := k) hP _ _
      hker_proper hgf_range
  have hgf_unit : IsUnit (g.comp f) := by
    have heq : g.comp f = LinearMap.id - (-(g.comp f - LinearMap.id)) :=
      by simp only [neg_sub, sub_sub_cancel]
    rw [heq]; exact hgf_nilp.neg.isUnit_one_sub
  -- Step 5: Similarly, f ∘ g - id has range in ker(ψ)
  have hfg_range :
      LinearMap.range (f.comp g - LinearMap.id) ≤ LinearMap.ker ψ := by
    intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    rw [← hx]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    have h1 : ψ (f (g x)) = φ (g x) := LinearMap.congr_fun hf (g x)
    have h2 : φ (g x) = ψ x := LinearMap.congr_fun hg x
    rw [map_sub, h1, h2, sub_self]
  have hker_proper' : LinearMap.ker ψ ≠ ⊤ := by
    intro h; exact hψ (LinearMap.ker_eq_top.mp h)
  have hfg_nilp : IsNilpotent (f.comp g - LinearMap.id) :=
    Etingof.endo_nilpotent_of_range_le_proper (k := k) hP' _ _
      hker_proper' hfg_range
  have hfg_unit : IsUnit (f.comp g) := by
    have heq : f.comp g = LinearMap.id - (-(f.comp g - LinearMap.id)) :=
      by simp only [neg_sub, sub_sub_cancel]
    rw [heq]; exact hfg_nilp.neg.isUnit_one_sub
  -- Step 6: f is bijective
  have hgf_bij : Function.Bijective (g.comp f) :=
    (Module.End.isUnit_iff _).mp hgf_unit
  have hfg_bij : Function.Bijective (f.comp g) :=
    (Module.End.isUnit_iff _).mp hfg_unit
  have f_inj : Function.Injective f := by
    intro x y hxy
    have : (g.comp f) x = (g.comp f) y := by
      simp only [LinearMap.comp_apply]; exact congr_arg g hxy
    exact hgf_bij.1 this
  have f_surj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := hfg_bij.2 y
    exact ⟨g z, by
      have : f (g z) = (f.comp g) z := rfl
      rw [this, hz]⟩
  exact ⟨LinearEquiv.ofBijective f ⟨f_inj, f_surj⟩⟩

end LocalEndomorphismRing

section CompleteSystem

/-! ### Complete orthogonal idempotent system

The full double-indexed system of orthogonal idempotents {e_{ij}} needed for
Theorem 9.2.1(ii). This extends `exists_orthogonal_idempotents_for_simples`
(which only constructs one E₁₁ per block) to the complete system of all
diagonal matrix units E_{jj} across all blocks.
-/

/-- Diagonal matrix units in a matrix ring form complete orthogonal idempotents.
For `Mat_n(R)`, the family `j ↦ Matrix.single j j 1` satisfies `∑ E_{jj} = I`
and `E_{jj} * E_{kk} = δ_{jk} E_{jj}`. -/
lemma Etingof.Theorem921.completeOrthogonalIdempotents_matrix_single
    {R : Type*} [CommSemiring R] {n : ℕ} :
    CompleteOrthogonalIdempotents
      (fun j : Fin n => Matrix.single j j (1 : R)) := by
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨fun j k' hjk => ?_, ?_⟩
  · show Matrix.single j j 1 * Matrix.single k' k' 1 = 0
    ext r s
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero; intro x _
    by_cases hxj : j = r ∧ j = x <;> by_cases hxk : k' = x ∧ k' = s
    · exact absurd (hxj.2.trans hxk.1.symm) hjk
    all_goals simp_all
  · -- Completeness: ∑ E_{jj} = I
    have : ∑ j : Fin n, Matrix.single j j (1 : R) = Matrix.diagonal (fun _ => 1) := by
      funext r s
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply, ite_and]
      simp [Finset.sum_ite_eq']
    rw [this, Matrix.diagonal_one]

/-- Diagonal matrix units in a product of matrix rings form complete orthogonal idempotents
indexed by the sigma type `Σ l, Fin (d l)`. The idempotent at `(l, j)` is
`Pi.single l (Matrix.single j j 1)`. -/
lemma Etingof.Theorem921.completeOrthogonalIdempotents_pi_matrix
    {n : ℕ} {d : Fin n → ℕ}
    {R : Type*} [CommSemiring R] :
    CompleteOrthogonalIdempotents
      (fun (p : Σ l : Fin n, Fin (d l)) =>
        (Pi.single p.1 (Matrix.single p.2 p.2 (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R)) := by
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨fun ⟨l₁, j₁⟩ ⟨l₂, j₂⟩ hpq => ?_, ?_⟩
  · -- Orthogonality
    funext k
    simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases h₁ : l₁ = k <;> by_cases h₂ : l₂ = k
    · subst h₁; subst h₂
      simp only [Pi.single_eq_same]
      have h2 : j₁ ≠ j₂ := fun h => hpq (Sigma.ext rfl (heq_of_eq h))
      ext r s
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero; intro x _
      by_cases hxp : j₁ = r ∧ j₁ = x <;> by_cases hxq : j₂ = x ∧ j₂ = s
      · exact absurd (hxp.2.trans hxq.1.symm) h2
      all_goals simp_all
    · simp [Pi.single_apply, h₁, h₂]
    · simp [Pi.single_apply, h₁, h₂]
    · simp [Pi.single_apply, h₁, h₂]
  · -- Completeness: ∑ p, Pi.single p.1 (E_{p.2,p.2}) = 1
    -- Split ∑_{(l,j)} into ∑_l ∑_j
    rw [show (∑ x : Σ l : Fin n, Fin (d l),
        (Pi.single x.1 (Matrix.single x.2 x.2 (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R)) =
        ∑ l : Fin n, ∑ j : Fin (d l), Pi.single l (Matrix.single j j 1) from
      Fintype.sum_sigma _]
    -- ∑_l (∑_j Pi.single l (E_jj)) = 1
    -- Inner sum: ∑_j Pi.single l (E_jj) = Pi.single l (∑_j E_jj) = Pi.single l 1
    have key : ∀ l : Fin n, ∑ j : Fin (d l),
        (Pi.single l (Matrix.single j j (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R) =
        Pi.single l 1 := by
      intro l
      rw [← completeOrthogonalIdempotents_matrix_single.complete]
      induction Finset.univ (α := Fin (d l)) using Finset.cons_induction with
      | empty => simp
      | cons j s hj ih =>
        simp only [Finset.sum_cons]
        rw [Pi.single_add, ih]
    simp_rw [key]
    exact Finset.univ_sum_single 1

/-- **Full system of complete orthogonal idempotents for Theorem 9.2.1(ii).**

Constructs `finrank k (M i)` orthogonal idempotents for each simple module class `i`,
forming a complete system in `A` that lifts the Wedderburn-Artin diagonal matrix units
from `A/Rad(A)`.

The construction:
1. Decompose `A/J ≅ ∏ Mat_{d_l}(k)` (Wedderburn-Artin)
2. In the product ring, diagonal matrix units `E_{jj}^l` form complete orthogonal idempotents
3. Lift to `A` via Corollary 9.1.3
4. Establish `σ : ι ≃ Fin n` (block assignment, bijective by exhaustiveness)
5. Prove `d(σ(i)) = finrank k (M i)` (dimension matching)
6. Reindex from `Σ l, Fin (d l)` to `Σ i, Fin (finrank k (M i))` -/
lemma Etingof.Theorem921.exists_complete_orthogonal_idempotents_for_simples
    [IsAlgClosed k] [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i)) :
    ∃ (e : (Σ i : ι, Fin (Module.finrank k (M i))) → A),
      CompleteOrthogonalIdempotents e ∧
      ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (smulRange (k := k) (A := A) (M j) (e p)) =
          if p.fst = j then 1 else 0 := by
  -- Step 1: A is semiprimary
  haveI : IsSemiprimaryRing A := inferInstance
  haveI hss : IsSemisimpleRing (A ⧸ Ring.jacobson A) := IsSemiprimaryRing.isSemisimpleRing
  have hnil := IsSemiprimaryRing.isNilpotent (R := A)
  -- Step 2: Jacobson radical annihilates simple modules
  have hann : ∀ i, Ring.jacobson A ≤ Module.annihilator A (M i) :=
    fun i => IsSemisimpleModule.jacobson_le_annihilator A (M i)
  -- Step 3: WA decomposition
  let π := Ideal.Quotient.mk (Ring.jacobson A)
  haveI : Module.Finite k (A ⧸ Ring.jacobson A) := inferInstance
  obtain ⟨n, d, hd, ⟨WA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)
  -- Step 4: Elements in same coset of A/J act identically on simples
  have hsmul_eq : ∀ (a a' : A) (j : ι) (m : M j),
      π a = π a' → a • m = a' • m := by
    intro a a' j m hq
    have hmem : a - a' ∈ Ring.jacobson A := Ideal.Quotient.eq.mp hq
    have h0 := Module.mem_annihilator.mp (hann j hmem) m
    rwa [sub_smul, sub_eq_zero] at h0
  have hsmulRange_eq : ∀ (a a' : A) (j : ι),
      π a = π a' → smulRange (k := k) (A := A) (M j) a = smulRange (k := k) (A := A) (M j) a' := by
    intro a a' j hq
    have : smulEnd (k := k) (A := A) (M j) a = smulEnd (k := k) (A := A) (M j) a' := by
      ext m; exact hsmul_eq a a' j m hq
    simp only [smulRange, this]
  -- Step 5: Construct COI in A/J, indexed by Σ l, Fin (d l)
  let ebar : (Σ l : Fin n, Fin (d l)) → A ⧸ Ring.jacobson A :=
    fun p => WA.symm (Pi.single p.1 (Matrix.single p.2 p.2 (1 : k)))
  have hebar_coi : CompleteOrthogonalIdempotents ebar := by
    have h := completeOrthogonalIdempotents_pi_matrix (R := k) (n := n) (d := d)
    exact h.map WA.symm.toRingEquiv.toRingHom
  -- Step 6: Lift to A
  have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨m, hm⟩ := hnil
    exact ⟨m, by
      have := Ideal.pow_mem_pow hx m
      rw [hm] at this
      exact Ideal.mem_bot.mp this⟩
  have hebar_range : ∀ p, ebar p ∈ π.range :=
    fun p => Ideal.Quotient.mk_surjective (ebar p)
  obtain ⟨e_raw, he_raw_coi, he_raw_lift⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker π hker hebar_coi hebar_range
  -- e_raw : (Σ l, Fin (d l)) → A is a COI system in A lifting ebar
  -- Step 7: Block assignment σ and rank property
  -- This follows the same infrastructure as exists_orthogonal_idempotents_for_simples.
  -- We establish:
  -- (a) Block assignment σ : ι → Fin n (injective, mapping simples to WA blocks)
  -- (b) σ is surjective (using hM_exhaustive)
  -- (c) Dimension matching: d(σ(i)) = finrank k (M i)
  -- (d) Rank property: finrank k (smulRange M_j (e_raw (l, k))) = δ_{σ(j), l}
  --
  -- The proofs of (a) and (d) are structurally identical to
  -- exists_orthogonal_idempotents_for_simples (replacing E₁₁ with E_{jj}).
  -- Parts (b) and (c) are new and use hM_exhaustive.
  suffices h_block :
      ∃ (σ : ι → Fin n),
        Function.Bijective σ ∧
        (∀ i, d (σ i) = Module.finrank k (M i)) ∧
        (∀ (p : Σ l : Fin n, Fin (d l)) (j : ι),
          Module.finrank k (smulRange (k := k) (A := A) (M j) (e_raw p)) =
            if σ j = p.fst then 1 else 0) by
    -- Step 8: Reindex from Σ l, Fin (d l) to Σ i, Fin (finrank k (M i))
    obtain ⟨σ, hσ_bij, hd_eq, hrank⟩ := h_block
    let σ_equiv : ι ≃ Fin n := Equiv.ofBijective σ hσ_bij
    -- Build reindexing equivalence (Σ i, Fin (dim M_i)) ≃ (Σ l, Fin (d l))
    -- Build reindexing equivalence using σ bijection + dimension matching
    -- (Σ i : ι, Fin (dim M_i)) ≃ (Σ l : Fin n, Fin (d l))
    -- via (i, j) ↦ (σ i, cast j) and (l, k) ↦ (σ⁻¹ l, cast k)
    let e : (Σ i : ι, Fin (Module.finrank k (M i))) → A :=
      fun p => e_raw ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩
    -- CompleteOrthogonalIdempotents: e is COI because it's e_raw ∘ (injective reindexing)
    -- and e_raw is COI on the full sigma type. The reindexing is σ-bijective + dim-matching.
    have he_coi : CompleteOrthogonalIdempotents e := by
      -- e is e_raw ∘ reindex where reindex is a bijection
      let reindex : (Σ i : ι, Fin (Module.finrank k (M i))) → (Σ l : Fin n, Fin (d l)) :=
        fun p => ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩
      have hreindex_bij : Function.Bijective reindex := by
        constructor
        · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
          simp only [reindex, Sigma.mk.injEq] at h
          obtain ⟨hi, hj⟩ := h
          have hi' := hσ_bij.1 hi
          subst hi'
          simp at hj
          exact Sigma.ext rfl (heq_of_eq hj)
        · rintro ⟨l, j⟩
          have hl : σ (σ_equiv.symm l) = l := σ_equiv.apply_symm_apply l
          have hdl : d l = Module.finrank k (M (σ_equiv.symm l)) := by
            have := hd_eq (σ_equiv.symm l); rwa [hl] at this
          refine ⟨⟨σ_equiv.symm l, finCongr hdl j⟩, ?_⟩
          simp only [reindex, Sigma.mk.injEq]
          refine ⟨hl, ?_⟩
          have hdl2 : d (σ (σ_equiv.symm l)) = d l := by rw [hl]
          rw [Fin.heq_ext_iff hdl2]
          simp [finCongr]
      let reindex_equiv := Equiv.ofBijective reindex hreindex_bij
      have hcomp : e = e_raw ∘ reindex_equiv := funext fun ⟨i, j⟩ => rfl
      rw [hcomp]
      have hortho := (OrthogonalIdempotents.equiv reindex_equiv).mpr
        he_raw_coi.toOrthogonalIdempotents
      exact ⟨hortho,
        by simp [Equiv.sum_comp reindex_equiv, he_raw_coi.complete]⟩
    refine ⟨e, he_coi, fun p j => ?_⟩
    -- Rank property: finrank k (smulRange M_j (e p)) = δ_{p.1, j}
    show Module.finrank k (smulRange (k := k) (A := A) (M j)
      (e_raw ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩)) =
      if p.fst = j then 1 else 0
    -- Use hrank with q = (σ p.1, cast p.2)
    have := hrank ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩ j
    rw [this]
    -- Now: (if σ j = σ p.fst then 1 else 0) = (if p.fst = j then 1 else 0)
    congr 1; exact propext ⟨fun h => (hσ_bij.1 h).symm, fun h => congrArg σ h.symm⟩
  -- Step 9: Prove the block assignment, bijectivity, dimension matching, and rank property
  -- Reconstruct block assignment infrastructure (cf. exists_orthogonal_idempotents_for_simples)
  have hWA_mul : ∀ x y : ∀ l, Matrix (Fin (d l)) (Fin (d l)) k,
      WA.symm x * WA.symm y = WA.symm (x * y) := fun x y => (map_mul WA.symm x y).symm
  let c : Fin n → A ⧸ Ring.jacobson A := fun l => WA.symm (Pi.single l 1)
  have hc_comm : ∀ (l : Fin n) (q : A ⧸ Ring.jacobson A), c l * q = q * c l := by
    intro l q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    show WA.symm (Pi.single l 1) * π b = π b * WA.symm (Pi.single l 1)
    rw [show π b = WA.symm (WA (π b)) from (WA.symm_apply_apply _).symm]
    rw [hWA_mul, hWA_mul]; congr 1; exact pi_single_one_comm l (WA (π b))
  have hsmulRange_A_sub : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      ∀ (b : A) (x : M j), x ∈ smulRange (k := k) (A := A) (M j) a →
        b • x ∈ smulRange (k := k) (A := A) (M j) a := by
    intro j l a ha b x ⟨m, hm⟩
    rw [← hm]
    have hcomm : π (b * a) = π (a * b) := by
      rw [map_mul, map_mul, ha]; exact (hc_comm l (π b)).symm
    show b • (a • m) ∈ smulRange (k := k) (A := A) (M j) a
    rw [← mul_smul, hsmul_eq _ _ j _ hcomm, mul_smul]; exact ⟨b • m, rfl⟩
  have hsmulRange_bot_or_top : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      smulRange (k := k) (A := A) (M j) a = ⊥ ∨
        smulRange (k := k) (A := A) (M j) a = ⊤ := by
    intro j l a ha
    let N : Submodule A (M j) :=
      { carrier := (smulRange (k := k) (A := A) (M j) a : Set (M j))
        add_mem' := (smulRange (k := k) (A := A) (M j) a).add_mem
        zero_mem' := (smulRange (k := k) (A := A) (M j) a).zero_mem
        smul_mem' := fun b x hx => hsmulRange_A_sub j l a ha b x hx }
    rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
    · left; ext x; constructor
      · intro hx; have : x ∈ N := hx; rw [h] at this
        exact (Submodule.mem_bot A).mp this
      · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) a).zero_mem
    · right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _; have : x ∈ N := by rw [h]; exact Submodule.mem_top
        exact this
  have hcoi := completeOrthogonalIdempotents_pi_single_one
    (S := fun l => Matrix (Fin (d l)) (Fin (d l)) k)
  have hc_sum : ∑ l, c l = 1 := by
    show ∑ l, WA.symm (Pi.single l 1) = 1
    rw [← map_sum, hcoi.complete, map_one WA.symm]
  have hblock_exists : ∀ j : ι, ∃ l : Fin n, ∀ a : A,
      π a = WA.symm (Pi.single l 1) →
      smulRange (k := k) (A := A) (M j) a = ⊤ := by
    intro j; by_contra h_none; push_neg at h_none
    have hall_bot : ∀ l : Fin n, ∀ a : A, π a = c l →
        smulRange (k := k) (A := A) (M j) a = ⊥ := by
      intro l a ha
      obtain ⟨a₀, ha₀, hne⟩ := h_none l
      rcases hsmulRange_bot_or_top j l a₀ ha₀ with h | h
      · rwa [hsmulRange_eq a a₀ j (ha.trans ha₀.symm)]
      · exact absurd h hne
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    obtain ⟨m, hm⟩ := exists_ne (0 : M j)
    apply hm
    have hlift : ∀ l : Fin n, ∃ a : A, π a = c l := fun l => Ideal.Quotient.mk_surjective (c l)
    choose a_l ha_l using hlift
    have hsum_img : π (∑ l, a_l l) = 1 := by
      rw [map_sum]; simp_rw [ha_l]; exact hc_sum
    have hsum_act : (∑ l, a_l l) • m = m := by
      have := hsmul_eq (∑ l, a_l l) 1 j m (by rw [hsum_img, map_one])
      rwa [one_smul] at this
    rw [← hsum_act, Finset.sum_smul]
    apply Finset.sum_eq_zero; intro l _
    have h0 := hall_bot l (a_l l) (ha_l l)
    have : a_l l • m ∈ smulRange (k := k) (A := A) (M j) (a_l l) := ⟨m, rfl⟩
    rw [h0] at this; exact (Submodule.mem_bot k).mp this
  have hblock_unique : ∀ j : ι, ∀ l₁ l₂ : Fin n,
      (∀ a : A, π a = WA.symm (Pi.single l₁ 1) →
        smulRange (k := k) (A := A) (M j) a = ⊤) →
      (∀ a : A, π a = WA.symm (Pi.single l₂ 1) →
        smulRange (k := k) (A := A) (M j) a = ⊤) →
      l₁ = l₂ := by
    intro j l₁ l₂ h₁ h₂; by_contra hne
    have horth : c l₁ * c l₂ = 0 :=
      (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).ortho hne
    obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (c l₁)
    obtain ⟨a₂, ha₂⟩ := Ideal.Quotient.mk_surjective (c l₂)
    have h₂_top := h₂ a₂ ha₂
    have hprod_img : π (a₁ * a₂) = 0 := by rw [map_mul, ha₁, ha₂, horth]
    have hprod_zero : ∀ m : M j, (a₁ * a₂) • m = 0 := by
      intro m
      have h0 := hsmul_eq (a₁ * a₂) 0 j m (by rw [hprod_img, map_zero])
      rwa [zero_smul] at h0
    have h₁_top := h₁ a₁ ha₁
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    have ha₁_zero : ∀ m : M j, a₁ • m = 0 := by
      intro m
      have : m ∈ smulRange (k := k) (A := A) (M j) a₂ := by
        rw [h₂_top]; exact Submodule.mem_top
      obtain ⟨m₀, hm₀⟩ := this; change a₂ • m₀ = m at hm₀
      rw [← hm₀, ← mul_smul]; exact hprod_zero m₀
    have : smulRange (k := k) (A := A) (M j) a₁ = ⊥ := by
      ext x; simp only [Submodule.mem_bot]; constructor
      · rintro ⟨m, rfl⟩; exact ha₁_zero m
      · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) a₁).zero_mem
    rw [this] at h₁_top; exact bot_ne_top h₁_top
  -- Define σ
  let σ : ι → Fin n := fun j => (hblock_exists j).choose
  have hσ_spec : ∀ j a, π a = WA.symm (Pi.single (σ j) 1) →
      smulRange (k := k) (A := A) (M j) a = ⊤ :=
    fun j => (hblock_exists j).choose_spec
  have hc_idem : ∀ l', IsIdempotentElem (c l') :=
    (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).idem
  have hc_identity : ∀ (p : ι) (a : A) (ha : π a = c (σ p)),
      ∀ m : M p, a • m = m := by
    intro p a ha m
    have h_top := hσ_spec p a ha
    have ⟨m₀, hm₀⟩ : m ∈ smulRange (k := k) (A := A) (M p) a := by
      rw [h_top]; exact Submodule.mem_top
    change a • m₀ = m at hm₀
    rw [← hm₀, ← mul_smul]
    exact hsmul_eq (a * a) a p m₀ (by rw [map_mul, ha, (hc_idem (σ p)).eq])
  have hc_zero : ∀ (p : ι) (l' : Fin n) (hl' : l' ≠ σ p) (a : A)
      (ha : π a = c l'), ∀ m : M p, a • m = 0 := by
    intro p l' hl' a ha m
    rcases hsmulRange_bot_or_top p l' a ha with h | h
    · have : a • m ∈ smulRange (k := k) (A := A) (M p) a := ⟨m, rfl⟩
      rw [h] at this; exact (Submodule.mem_bot k).mp this
    · exfalso; exact hl' (hblock_unique p l' (σ p)
        (fun a' ha' => hsmulRange_eq a' a p (ha'.trans ha.symm) ▸ h) (hσ_spec p))
  -- σ is injective
  have hσ_inj : Function.Injective σ := by
    intro i j hij; apply hM i j
    set l := σ i with hl_def
    have hlj : σ j = l := hij.symm
    let lft : (A ⧸ Ring.jacobson A) → A := fun q => (Ideal.Quotient.mk_surjective q).choose
    have hlft : ∀ q, π (lft q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
    let matAct : ∀ p : ι, Matrix (Fin (d l)) (Fin (d l)) k → M p → M p :=
      fun p mat m => lft (WA.symm (Pi.single l mat)) • m
    have hdecomp : ∀ (p : ι) (hp : σ p = l) (a : A) (m : M p),
        a • m = matAct p ((WA (π a)) l) m := by
      intro p hp a m
      have hid := hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl)
      conv_lhs => rw [show a • m = (a * lft (c l)) • m from by rw [mul_smul, hid m]]
      apply hsmul_eq; simp only [map_mul, hlft]
      conv_lhs => rw [show π a = WA.symm (WA (π a)) from (WA.symm_apply_apply _).symm,
                       show c l = WA.symm (Pi.single l 1) from rfl]
      rw [hWA_mul]; congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · simp [Pi.mul_apply, show l ≠ l' from fun h => hl' h.symm]
    have hpi_single_mul : ∀ (x y : Matrix (Fin (d l)) (Fin (d l)) k),
        Pi.single l x * Pi.single l y =
          (Pi.single l (x * y) : ∀ l', Matrix (Fin (d l')) (Fin (d l')) k) := by
      intro x y; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.mul_apply, hne, Pi.single_apply]
    have hmatAct_mul : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 * mat2) m = matAct p mat1 (matAct p mat2 m) := by
      intro p mat1 mat2 m
      show lft (WA.symm (Pi.single l (mat1 * mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • (lft (WA.symm (Pi.single l mat2)) • m)
      rw [← mul_smul]; apply hsmul_eq
      rw [map_mul, hlft, hlft]; conv_rhs => rw [hlft]
      rw [hWA_mul, hpi_single_mul]
    have hmatAct_add : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 + mat2) m = matAct p mat1 m + matAct p mat2 m := by
      intro p mat1 mat2 m
      show lft (WA.symm (Pi.single l (mat1 + mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • m + lft (WA.symm (Pi.single l mat2)) • m
      rw [← add_smul]; apply hsmul_eq
      rw [map_add, hlft, hlft]; conv_rhs => rw [hlft]
      rw [show WA.symm (Pi.single l mat1) + WA.symm (Pi.single l mat2) =
            WA.symm (Pi.single l mat1 + Pi.single l mat2) from (map_add WA.symm _ _).symm]
      congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.single_apply, hne]
    have hmatAct_one : ∀ (p : ι) (hp : σ p = l) (m : M p), matAct p 1 m = m := by
      intro p hp m
      exact hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl) m
    have hmatAct_zero : ∀ (p : ι) (m : M p), matAct p 0 m = 0 := by
      intro p m
      have : lft (WA.symm (Pi.single l 0)) • m = (0 : A) • m := by
        apply hsmul_eq; rw [hlft, map_zero, Pi.single_zero, map_zero]
      exact this.trans (zero_smul A m)
    letI instMi : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M i) :=
      { smul := matAct i
        one_smul := hmatAct_one i rfl
        mul_smul := hmatAct_mul i
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add i
        zero_smul := hmatAct_zero i }
    letI instMj : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M j) :=
      { smul := matAct j
        one_smul := hmatAct_one j hlj
        mul_smul := hmatAct_mul j
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add j
        zero_smul := hmatAct_zero j }
    have hMatSimple : ∀ (p : ι) (hp : σ p = l)
        (inst : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M p)),
        (∀ (mat : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p), mat • m = matAct p mat m) →
        @IsSimpleModule (Matrix (Fin (d l)) (Fin (d l)) k) _ (M p) _ inst := by
      intro p hp inst hsmul_def
      haveI : Nontrivial (M p) := IsSimpleModule.nontrivial A (M p)
      exact
        { eq_bot_or_eq_top := fun N => by
            let N_A : Submodule A (M p) :=
              { carrier := N.carrier
                add_mem' := N.add_mem'
                zero_mem' := N.zero_mem'
                smul_mem' := fun a x hx => by
                  rw [hdecomp p hp a x, ← hsmul_def]; exact N.smul_mem _ hx }
            rcases IsSimpleOrder.eq_bot_or_eq_top N_A with h | h
            · left; ext x; simp only [Submodule.mem_bot]
              exact ⟨fun hx => (Submodule.eq_bot_iff _).mp h x hx,
                     fun hx => hx ▸ N.zero_mem⟩
            · right; ext x
              exact ⟨fun _ => trivial,
                     fun _ => (Submodule.eq_top_iff'.mp h x : x ∈ N_A)⟩ }
    haveI hSimMi := hMatSimple i rfl instMi (fun _ _ => rfl)
    haveI hSimMj := hMatSimple j hlj instMj (fun _ _ => rfl)
    haveI : IsSimpleRing (Matrix (Fin (d l)) (Fin (d l)) k) := by
      haveI := hd l; exact IsSimpleRing.matrix (Fin (d l)) k
    haveI : IsArtinianRing (Matrix (Fin (d l)) (Fin (d l)) k) := inferInstance
    obtain ⟨f⟩ := @IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule
      (Matrix (Fin (d l)) (Fin (d l)) k) _ _ _ (M i) (M j) _ instMi hSimMi _ instMj hSimMj
    exact ⟨{ toFun := f
             invFun := f.symm
             left_inv := f.left_inv
             right_inv := f.right_inv
             map_add' := f.map_add
             map_smul' := fun a m => by
               simp only [RingHom.id_apply]
               rw [hdecomp i rfl a m, hdecomp j hlj a (f m)]
               exact f.map_smul ((WA (π a)) l) m }⟩
  -- σ is surjective (using hM_exhaustive)
  have hσ_surj : Function.Surjective σ := by
    intro l
    -- Block l gives a simple module over Mat_{d l}(k). By hM_exhaustive, it's isomorphic
    -- to some M i. Then σ(i) = l by uniqueness of block assignment.
    -- The standard representation of Mat_{d l}(k) is simple. Lift it to an A-module structure.
    -- Since c_l acts as identity on this module, σ for this module must be l.
    -- Actually, more directly: use Fintype.bijective_iff_surjective after proving card equality.
    -- |ι| ≤ n (by injectivity). n ≤ |ι| by the following:
    -- Cardinality: |ι| = n follows from injectivity + finiteness + n ≤ |ι|.
    -- But we need n ≤ |ι|. This requires that every block is "used", i.e., for each l,
    -- there exists a simple module supported on block l. This follows from hM_exhaustive.
    -- For each block l, construct a simple A-module from the standard Mat representation,
    -- use hM_exhaustive to find i with M i ≅ this module, then σ i = l.
    sorry
  -- Dimension matching: d(σ i) = finrank k (M i)
  have hd_eq : ∀ i, d (σ i) = Module.finrank k (M i) := by
    sorry
  -- Rank property for all E_{jj}
  have hrank : ∀ (p : Σ l : Fin n, Fin (d l)) (j : ι),
      Module.finrank k (smulRange (k := k) (A := A) (M j) (e_raw p)) =
        if σ j = p.fst then 1 else 0 := by
    intro ⟨l, j_idx⟩ j
    -- e_raw(l, j_idx) lifts WA.symm(Pi.single l (E_{j_idx, j_idx}))
    have he_lift : π (e_raw ⟨l, j_idx⟩) =
        WA.symm (Pi.single l (Matrix.single j_idx j_idx (1 : k))) :=
      congr_fun he_raw_lift ⟨l, j_idx⟩
    split_ifs with hlj
    · -- Case σ j = l: rank 1 (generalization of E₁₁ case to E_{j_idx, j_idx})
      subst hlj
      -- Step 1: e_raw acts idempotently on M j
      have ha_idem : ∀ m : M j, e_raw ⟨σ j, j_idx⟩ • (e_raw ⟨σ j, j_idx⟩ • m) =
          e_raw ⟨σ j, j_idx⟩ • m := by
        intro m; rw [← mul_smul]
        exact hsmul_eq _ _ j m (by
          rw [map_mul, he_lift, hWA_mul]; congr 1
          rw [← Pi.single_mul_left, Pi.single_eq_same]; congr 1
          exact (matrix_single_zero_isIdempotentElem j_idx).eq)
      -- Step 2: Image is nonzero (two-sided ideal argument)
      have ha_ne_zero : ∃ m₀ : M j, e_raw ⟨σ j, j_idx⟩ • m₀ ≠ 0 := by
        by_contra hall; push_neg at hall
        have h_prod_zero : ∀ (b₁ b₂ : A) (m : M j),
            (b₁ * e_raw ⟨σ j, j_idx⟩ * b₂) • m = 0 := by
          intro b₁ b₂ m; rw [mul_smul, mul_smul, hall, smul_zero]
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M j)
        apply hm₀
        -- ∑_k E_{k,j_idx} * E_{j_idx,j_idx} * E_{j_idx,k} = I in Mat
        have h_sum_eq_c : ∑ k' : Fin (d (σ j)),
            WA.symm (Pi.single (σ j) (Matrix.single k' j_idx 1)) *
            WA.symm (Pi.single (σ j) (Matrix.single j_idx j_idx 1)) *
            WA.symm (Pi.single (σ j) (Matrix.single j_idx k' 1)) = c (σ j) := by
          simp_rw [hWA_mul, ← Pi.single_mul_left, Pi.single_eq_same,
            Matrix.single_mul_mul_single, one_mul, mul_one]
          simp_rw [show (Matrix.single j_idx j_idx (1 : k))
            j_idx j_idx = 1 from by simp [Matrix.single_apply]]
          rw [show c (σ j) = WA.symm (Pi.single (σ j) 1) from rfl]
          rw [show ∑ x, WA.symm (Pi.single (σ j) (Matrix.single x x (1 : k))) =
            WA.symm (∑ x, Pi.single (σ j) (Matrix.single x x (1 : k))) from
            (map_sum WA.symm.toRingHom _ _).symm]
          congr 1; funext l'; by_cases hl' : l' = σ j
          · subst hl'; simp only [Pi.single_eq_same, Finset.sum_apply]
            ext r s
            simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
            split_ifs with h
            · subst h; simp [Finset.sum_ite_eq, Finset.mem_univ]
            · apply Finset.sum_eq_zero; intro x _
              simp [show ¬(x = r ∧ x = s) from fun ⟨h1, h2⟩ => h (h1.symm.trans h2)]
          · simp [Finset.sum_apply, Pi.single_apply, hl']
        let b₁ : Fin (d (σ j)) → A := fun k' =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single (σ j)
            (Matrix.single k' j_idx 1)))).choose
        let b₂ : Fin (d (σ j)) → A := fun k' =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single (σ j)
            (Matrix.single j_idx k' 1)))).choose
        have hb₁ : ∀ k', π (b₁ k') = WA.symm (Pi.single (σ j)
            (Matrix.single k' j_idx 1)) :=
          fun k' => (Ideal.Quotient.mk_surjective _).choose_spec
        have hb₂ : ∀ k', π (b₂ k') = WA.symm (Pi.single (σ j)
            (Matrix.single j_idx k' 1)) :=
          fun k' => (Ideal.Quotient.mk_surjective _).choose_spec
        have hsum_zero : (∑ k', b₁ k' * e_raw ⟨σ j, j_idx⟩ * b₂ k') • m₀ = 0 := by
          rw [Finset.sum_smul]
          exact Finset.sum_eq_zero (fun k' _ => h_prod_zero _ _ m₀)
        have hsum_lifts : π (∑ k', b₁ k' * e_raw ⟨σ j, j_idx⟩ * b₂ k') = c (σ j) := by
          rw [map_sum]; simp_rw [map_mul, hb₁, hb₂, he_lift]; exact h_sum_eq_c
        rw [← hc_identity j _ hsum_lifts m₀]; exact hsum_zero
      -- Step 3: Pick v₀ in the image
      obtain ⟨m₀, hm₀⟩ := ha_ne_zero
      set v₀ := e_raw ⟨σ j, j_idx⟩ • m₀ with hv₀_def
      have hav₀ : e_raw ⟨σ j, j_idx⟩ • v₀ = v₀ := ha_idem m₀
      -- Step 4: Every element of Im(e) is a k-multiple of v₀ (corner identity)
      have hscalar : ∀ m' : M j,
          e_raw ⟨σ j, j_idx⟩ • m' ∈ Submodule.span k {v₀} := by
        intro m'
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        have hgen : Submodule.span A {v₀} = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {v₀}) with h | h
          · exfalso; exact hm₀ ((Submodule.eq_bot_iff _).mp h v₀ (Submodule.subset_span rfl))
          · exact h
        have hm'_mem : m' ∈ Submodule.span A {v₀} := hgen ▸ Submodule.mem_top
        rw [Submodule.mem_span_singleton] at hm'_mem
        obtain ⟨b, rfl⟩ := hm'_mem
        rw [← mul_smul]
        have hab_eq : (e_raw ⟨σ j, j_idx⟩ * b) • v₀ =
            (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) • v₀ := by
          conv_lhs => rw [← hav₀]; rw [← mul_smul]
        rw [hab_eq]
        set c_val := (WA (π b)) (σ j) j_idx j_idx with hc_val_def
        have hpi_aba : π (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) =
            π ((algebraMap k A c_val) * e_raw ⟨σ j, j_idx⟩) := by
          apply WA.injective
          have hWAe : WA (π (e_raw ⟨σ j, j_idx⟩)) = Pi.single (σ j)
              (Matrix.single j_idx j_idx (1 : k)) := by
            rw [he_lift]; exact WA.apply_symm_apply _
          simp only [map_mul, hWAe]
          rw [← Pi.single_mul_left, ← Pi.single_mul_left,
              Pi.single_eq_same, matrix_single_corner]
          rw [Ideal.Quotient.mk_algebraMap, WA.commutes]
          ext l'; by_cases hl' : l' = σ j
          · subst hl'
            simp only [Pi.single_eq_same, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
              Pi.smul_apply, Pi.one_apply, Matrix.smul_apply, smul_eq_mul, one_mul,
              smul_mul_assoc, hc_val_def]
          · simp [Pi.mul_apply, Pi.single_apply, hl']
        have : (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) • v₀ = c_val • v₀ := by
          have h := hsmul_eq (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩)
            ((algebraMap k A c_val) * e_raw ⟨σ j, j_idx⟩) j v₀ hpi_aba
          rw [h, mul_smul, hav₀, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem _ c_val (Submodule.subset_span rfl)
      -- Step 5: smulRange = span{v₀}, finrank = 1
      have hspan : smulRange (k := k) (A := A) (M j) (e_raw ⟨σ j, j_idx⟩) =
          Submodule.span k {v₀} := by
        ext w; constructor
        · rintro ⟨m', rfl⟩; exact hscalar m'
        · intro hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c_val, rfl⟩ := hw
          exact ⟨c_val • m₀, by
            simp [smulEnd, smul_comm (e_raw ⟨σ j, j_idx⟩) c_val m₀, hv₀_def]⟩
      rw [hspan]; exact finrank_span_singleton hm₀
    · -- Case σ j ≠ l: rank 0
      -- E_{j_idx, j_idx} is in block l. c_l * E = E. c_l acts as 0 on M j (since σ j ≠ l).
      have hfactor : π (e_raw ⟨l, j_idx⟩) = c l * π (e_raw ⟨l, j_idx⟩) := by
        rw [he_lift, show c l = WA.symm (Pi.single l 1) from rfl, hWA_mul]
        congr 1; rw [← Pi.single_mul_left]; simp
      obtain ⟨a_c, ha_c⟩ := Ideal.Quotient.mk_surjective (c l)
      have hc_bot : smulRange (k := k) (A := A) (M j) a_c = ⊥ := by
        rcases hsmulRange_bot_or_top j l a_c ha_c with h | h
        · exact h
        · exfalso; exact hlj (hblock_unique j l (σ j)
            (fun a' ha' => hsmulRange_eq a' a_c j (ha'.trans ha_c.symm) ▸ h) (hσ_spec j)).symm
      have ha_zero : ∀ m : M j, e_raw ⟨l, j_idx⟩ • m = 0 := by
        intro m
        have hca_zero : ∀ m : M j, a_c • m = 0 := by
          intro m'
          have : a_c • m' ∈ smulRange (k := k) (A := A) (M j) a_c := ⟨m', rfl⟩
          rw [hc_bot] at this; exact (Submodule.mem_bot k).mp this
        have := hsmul_eq (a_c * e_raw ⟨l, j_idx⟩) (e_raw ⟨l, j_idx⟩) j m
          (by rw [map_mul, ha_c]; exact hfactor.symm)
        rw [mul_smul] at this; rw [← this, hca_zero]
      have hbot : smulRange (k := k) (A := A) (M j) (e_raw ⟨l, j_idx⟩) = ⊥ := by
        ext x; simp only [Submodule.mem_bot]; constructor
        · rintro ⟨m, rfl⟩; exact ha_zero m
        · intro hx; rw [hx]; exact (smulRange (k := k) (A := A) (M j) (e_raw ⟨l, j_idx⟩)).zero_mem
      rw [hbot]; simp
  exact ⟨σ, ⟨hσ_inj, hσ_surj⟩, hd_eq, hrank⟩

end CompleteSystem

/-- **Theorem 9.2.1(ii)**: Decomposition of the algebra as a module.

The algebra A, viewed as a left module over itself, decomposes as A ≅ ⊕ᵢ (dim Mᵢ) · Pᵢ.
That is, if `P` is the family of projective covers from part (i), then A is isomorphic
as an A-module to the direct sum over `i` of `(finrank k (M i))` copies of `P i`.
(Etingof Theorem 9.2.1(ii)) -/
theorem Etingof.Theorem_9_2_1_ii
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) :
    Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i) := by
  -- Proof strategy (Etingof Theorem 9.2.1(ii)):
  -- 1. Construct complete orthogonal idempotents in A indexed by Σ i, Fin (dim M_i),
  --    using the Wedderburn-Artin decomposition of A/J, diagonal matrix units, and lifting.
  -- 2. Each left ideal A·e_p has Hom(A·e_p, M_j) = δ_{p.1, j} (rank property).
  -- 3. Each A·e_p is indecomposable and projective, hence ≅ P_{p.1} by uniqueness.
  -- 4. A = ⊕_p A·e_p ≅ ⊕_p P_{p.1} ≅ ⊕_i (Fin (dim M_i) → P_i).
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  -- Step 1: Construct complete orthogonal idempotents with the Hom delta property.
  -- This is the core WA-based construction (sorry'd — see detailed outline above).
  suffices h_coi : ∃ (e : (Σ i : ι, Fin (Module.finrank k (M i))) → A),
      CompleteOrthogonalIdempotents e ∧
      ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (Etingof.Theorem921.smulRange (k := k) (A := A) (M j) (e p)) =
          if p.fst = j then 1 else 0 by
    -- Assembly: Given the complete system, build the decomposition A ≅ ⊕_i (dim M_i) · P_i.
    obtain ⟨e, he_coi, he_rank⟩ := h_coi
    -- Each left ideal A·e_p has the Hom delta property via finrank_hom_leftIdeal_eq
    set N : (Σ i : ι, Fin (Module.finrank k (M i))) → Submodule A A :=
      fun p => Submodule.span A ({e p} : Set A) with hN_def
    have hdim_hom : ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (↥(N p) →ₗ[A] M j) = if p.fst = j then 1 else 0 := by
      intro p j
      rw [Theorem921.finrank_hom_leftIdeal_eq (k := k) (e p) (he_coi.idem p)]
      exact he_rank p j
    -- Each A·e_p is projective
    have hproj : ∀ p, Module.Projective A ↥(N p) :=
      fun p => Theorem921.leftIdeal_projective (e p) (he_coi.idem p)
    -- Each A·e_p is indecomposable (by the Hom delta + exhaustiveness argument)
    have hindec : ∀ p, Etingof.IsIndecomposable A ↥(N p) :=
      fun p => Theorem921.leftIdeal_indecomposable_of_hom_delta (k := k) M hM hM_exhaustive
        (e p) (he_coi.idem p) p.1 (hdim_hom p)
    -- Each A·e_p ≅ P_{p.1} by uniqueness of indecomposable projectives
    -- (both have nonzero Hom to M_{p.1})
    have hiso : ∀ p, Nonempty (↥(N p) ≃ₗ[A] P p.fst) := by
      intro p
      -- Need: finrank of Hom to M_{p.1} is 1 for both N p and P p.fst
      -- A·e_p has dim Hom(-, M_{p.1}) = 1
      have hdim1 : Module.finrank k (↥(N p) →ₗ[A] M p.fst) = 1 := by
        rw [hdim_hom]; simp
      -- P p.fst has dim Hom(-, M_{p.1}) = 1
      have hdim2 : Module.finrank k (P p.fst →ₗ[A] M p.fst) = 1 := by
        rw [hP]; simp
      -- Both Hom spaces are nontrivial (finrank = 1)
      haveI : Module.Finite k ↥(N p) :=
        Module.Finite.of_injective ((N p).subtype.restrictScalars k) Subtype.val_injective
      haveI : FiniteDimensional k ↥(N p) := inferInstance
      haveI : FiniteDimensional k (P p.fst) := Module.Finite.trans A (P p.fst)
      -- Simple modules are finite-dimensional
      haveI : ∀ j, Module.Finite k (M j) := by
        intro j
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        obtain ⟨v, hv⟩ := exists_ne (0 : M j)
        let φ : A →ₗ[k] M j := (LinearMap.toSpanSingleton A (M j) v).restrictScalars k
        have hφ_surj : Function.Surjective φ := by
          intro m
          have hrange : LinearMap.range (LinearMap.toSpanSingleton A (M j) v) = ⊤ := by
            rcases IsSimpleOrder.eq_bot_or_eq_top
              (LinearMap.range (LinearMap.toSpanSingleton A (M j) v)) with h | h
            · exact absurd (show v = 0 from by
                have : v ∈ LinearMap.range
                    (LinearMap.toSpanSingleton A (M j) v) := ⟨1, one_smul A v⟩
                rw [h] at this; exact (Submodule.mem_bot A).mp this) hv
            · exact h
          exact LinearMap.range_eq_top.mp hrange m
        exact Module.Finite.of_surjective φ hφ_surj
      -- Hom spaces are finite-dimensional
      haveI : Module.Finite k (↥(N p) →ₗ[A] M p.fst) :=
        Module.Finite.of_injective
          (LinearMap.restrictScalarsₗ k A (↥(N p)) (M p.fst) k)
          (LinearMap.restrictScalars_injective k)
      haveI : Module.Finite k (P p.fst →ₗ[A] M p.fst) :=
        Module.Finite.of_injective
          (LinearMap.restrictScalarsₗ k A (P p.fst) (M p.fst) k)
          (LinearMap.restrictScalars_injective k)
      -- Get nonzero maps from both
      have hnt1 : Nontrivial (↥(N p) →ₗ[A] M p.fst) := by
        rw [← Module.finrank_pos_iff (R := k)]; omega
      have hnt2 : Nontrivial (P p.fst →ₗ[A] M p.fst) := by
        rw [← Module.finrank_pos_iff (R := k)]; omega
      obtain ⟨φ, hφ⟩ := exists_ne (0 : ↥(N p) →ₗ[A] M p.fst)
      obtain ⟨ψ, hψ⟩ := exists_ne (0 : P p.fst →ₗ[A] M p.fst)
      exact Etingof.indecomposable_projective_iso_of_hom (k := k)
        (hindec p) (hP_indec p.fst) φ hφ ψ hψ
    -- Step 2: Build the A-linear equivalence A ≅ ⊕_i (Fin (dim M_i) → P i).
    -- First: A ≅ ⊕_p A·e_p (from complete orthogonal idempotents + internal direct sum)
    have hint := Theorem921.isInternal_leftIdeals_of_completeOrthogonalIdempotents e he_coi
    -- DirectSum.IsInternal means coeLinearMap is bijective
    let decomp : A ≃ₗ[A] ⨁ p, ↥(N p) :=
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).symm
    -- Second: ⊕_p A·e_p ≃ ⊕_p P_{p.fst} (component-wise via hiso)
    -- Use δ i j = P i (constant in j) for the sigma curry
    let δ : (i : ι) → Fin (Module.finrank k (M i)) → Type _ := fun i _ => P i
    -- Component-wise linear equivalences
    let isoP : ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))),
        ↥(N p) ≃ₗ[A] δ p.fst p.snd :=
      fun p => Classical.choice (hiso p)
    -- ⊕ p, N(p) ≃ ⊕ p, δ p.fst p.snd
    let dsIso : (⨁ p, ↥(N p)) ≃ₗ[A] ⨁ (p : Σ i : ι, Fin (Module.finrank k (M i))),
        δ p.fst p.snd :=
      DFinsupp.mapRange.linearEquiv isoP
    -- Third: ⊕ p, δ p.fst p.snd ≃ ⊕ i, ⊕ j, δ i j  (sigma curry)
    let sigCurry :=
      @DirectSum.sigmaLcurryEquiv A _ ι (fun i => Fin (Module.finrank k (M i))) δ _ _ _
    -- Fourth: for each i, ⊕ (j : Fin _), P i ≃ (Fin _ → P i)
    let piEquiv : (⨁ (i : ι), ⨁ (_ : Fin (Module.finrank k (M i))), P i) ≃ₗ[A]
        ⨁ (i : ι), (Fin (Module.finrank k (M i)) → P i) :=
      DFinsupp.mapRange.linearEquiv (fun i =>
        DirectSum.linearEquivFunOnFintype A (Fin (Module.finrank k (M i)))
          (fun _ => P i))
    -- Compose all four equivalences
    exact ⟨decomp.trans (dsIso.trans (sigCurry.trans piEquiv))⟩
  -- Apply the full COI construction lemma
  exact Theorem921.exists_complete_orthogonal_idempotents_for_simples M hM hM_exhaustive

/-- **Theorem 9.2.1(iii)**: Completeness of the projective cover classification.

Any indecomposable finitely generated projective A-module is isomorphic to some Pᵢ.
This follows from the decomposition of A: any indecomposable projective must appear as
a direct summand of A (since A is projective and decomposes into the Pᵢ by part (ii)),
so by Krull–Schmidt it must be isomorphic to one of them.
(Etingof Theorem 9.2.1(iii)) -/
theorem Etingof.Theorem_9_2_1_iii
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, Etingof.IsIndecomposable A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type uA) [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
    [SMulCommClass A k Q]
    [Module.Projective A Q] [Module.Finite A Q] (hQ_indec : Etingof.IsIndecomposable A Q) :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by
  -- Proof strategy (Etingof):
  -- Q has a simple quotient M_{j₀}, so Hom(Q, M_{j₀}) ≠ 0.
  -- P_{j₀} also has Hom(P_{j₀}, M_{j₀}) = 1.
  -- By indecomposable_projective_iso_of_hom (Fitting's lemma), Q ≅ P_{j₀}.
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : Nontrivial Q := hQ_indec.1
  haveI : FiniteDimensional k Q := Module.Finite.trans A Q
  -- Step 1: Q has a nonzero map to some M_{j₀}
  -- Q has a maximal submodule (A is artinian, Q is f.g.)
  obtain ⟨N, hN_coatom⟩ := Theorem921.exists_isCoatom_submodule (R := A) (M := Q)
  haveI : IsSimpleModule A (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom
  -- Q/N is a simple A-module. The quotient map Q → Q/N is nonzero.
  -- By exhaustiveness, Q/N ≅ M j₀ for some j₀. Composing gives a nonzero Q → M j₀.
  obtain ⟨j₀, ⟨e⟩⟩ := hM_exhaustive (Q ⧸ N)
  -- Nonzero map Q → M j₀: compose quotient with the isomorphism
  let φ : Q →ₗ[A] M j₀ := e.toLinearMap.comp N.mkQ
  have hφ : φ ≠ 0 := by
    intro h
    apply hN_coatom.1
    rw [Submodule.eq_top_iff']
    intro q
    have h1 : (e (N.mkQ q) : M j₀) = 0 := LinearMap.congr_fun h q
    have h2 : N.mkQ q = 0 := e.injective (by rwa [map_zero])
    exact (Submodule.Quotient.mk_eq_zero N).mp h2
  -- Step 2: P j₀ has a nonzero map to M j₀ (finrank = 1 implies nontrivial Hom space)
  haveI : FiniteDimensional k (P j₀) := Module.Finite.trans A (P j₀)
  -- M j₀ is finite over k: it's iso to Q/N which is a quotient of the f.g. module Q
  haveI : Module.Finite A (M j₀) := Module.Finite.equiv e
  haveI : Module.Finite k (M j₀) := Module.Finite.trans A (M j₀)
  haveI : Module.Finite k (P j₀ →ₗ[A] M j₀) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (P j₀) (M j₀) k)
      (LinearMap.restrictScalars_injective k)
  have hPdim : Module.finrank k (P j₀ →ₗ[A] M j₀) = 1 := by
    have := hP j₀ j₀; simp only [ite_true] at this; exact this
  have hP_nt : Nontrivial (P j₀ →ₗ[A] M j₀) := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : P j₀ →ₗ[A] M j₀)
  -- Step 3: By uniqueness, Q ≅ P j₀
  exact ⟨j₀, Etingof.indecomposable_projective_iso_of_hom (k := k) hQ_indec
    (hP_indec j₀) φ hφ ψ hψ⟩
