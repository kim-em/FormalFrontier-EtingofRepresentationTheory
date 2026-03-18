import EtingofRepresentationTheory.Chapter9.Theorem9_2_1
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Proposition 9.2.3: Hom from projective cover computes Jordan–Hölder multiplicity

Let N be a finite dimensional A-module. Then dim Hom_A(Pᵢ, N) = [N : Mᵢ], the multiplicity
of Mᵢ in the Jordan–Hölder series of N.

## Proof sketch

Use the fact that Hom(Pᵢ, −) is exact (since Pᵢ is projective) and that
dim Hom(Pᵢ, Mⱼ) = δᵢⱼ. By induction on the length of a composition series of N.

## Formalization approach

The Jordan–Hölder multiplicity-counting function is not yet available in Mathlib as a
standalone definition. We define `compositionFactorMultiplicity` to count how many
successive quotients in a composition series are A-linearly isomorphic to a given
simple module. By the Jordan–Hölder theorem, this count is independent of the choice
of series.

The theorem then states that `dim_k Hom_A(Pᵢ, N)` equals this count for the simple
module Mᵢ, given the Kronecker delta property `dim Hom(Pᵢ, Mⱼ) = δᵢⱼ` from
Theorem 9.2.1(i).
-/

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]

/-- The multiplicity of a simple module `S` as a composition factor in a composition
series `s` of the submodule lattice of `N`.

Counts the number of indices `l` in the series where the successive quotient
`s(l+1) / s(l)` is A-linearly isomorphic to `S`.

The successive quotient at index `l` is modeled as `(s l.succ) ⧸ (s l).comap (s l.succ).subtype`,
following Mathlib's `JordanHolderModule` convention. -/
noncomputable def Etingof.compositionFactorMultiplicity
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : CompositionSeries (Submodule A N))
    (S : Type*) [AddCommGroup S] [Module A S] : ℕ :=
  @Finset.card _ (@Finset.filter _ (fun l : Fin s.length =>
      Nonempty ((↥(s l.succ) ⧸ (s (Fin.castSucc l)).comap (s l.succ).subtype) ≃ₗ[A] S))
    (fun _ => Classical.dec _) Finset.univ)

section Helpers

/-- When `⊥ = ⊤` in the submodule lattice of N, N is the zero module and all Hom spaces
from any module into N have dimension 0. -/
theorem finrank_hom_of_bot_eq_top
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module F P] [IsScalarTower F R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N]
    (h : (⊥ : Submodule R N) = ⊤) :
    Module.finrank F (P →ₗ[R] N) = 0 := by
  haveI : Subsingleton N := by
    rw [subsingleton_iff]
    intro a b
    have ha : a ∈ (⊤ : Submodule R N) := Submodule.mem_top
    have hb : b ∈ (⊤ : Submodule R N) := Submodule.mem_top
    rw [← h] at ha hb
    simp only [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI : Subsingleton (P →ₗ[R] N) := ⟨fun f g => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  exact Module.finrank_zero_of_subsingleton

/-- For a projective module P over a ring R and a submodule N' of an R-module N, the
dimension of Hom(P, N) decomposes as dim Hom(P, N') + dim Hom(P, N/N').

This follows from the short exact sequence 0 → N' → N → N/N' → 0: Hom(P, −) is
left exact for any P, and right exact when P is projective (every map P → N/N' lifts
to P → N). Together these give the dimension formula. -/
theorem finrank_hom_additive_of_projective
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [Module F P] [IsScalarTower F R P] [SMulCommClass R F P]
    [Module.Finite F P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N] [SMulCommClass R F N]
    [Module.Finite F N]
    (N' : Submodule R N) :
    Module.finrank F (P →ₗ[R] N) =
      Module.finrank F (P →ₗ[R] N') + Module.finrank F (P →ₗ[R] (N ⧸ N')) := by
  -- Post-composition with mkQ gives ψ : Hom(P,N) →ₗ[F] Hom(P, N/N')
  let ψ : (P →ₗ[R] N) →ₗ[F] (P →ₗ[R] (N ⧸ N')) :=
    { toFun := fun f => N'.mkQ.comp f
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  -- ψ is surjective by projectivity of P
  have hψ_surj : Function.Surjective ψ := by
    intro g
    obtain ⟨h, hh⟩ := Module.projective_lifting_property N'.mkQ g N'.mkQ_surjective
    exact ⟨h, LinearMap.ext fun p => by
      show N'.mkQ (h p) = g p
      exact congr_fun (congr_arg DFunLike.coe hh) p⟩
  -- Pre-composition with subtype gives ι : Hom(P,N') →ₗ[F] Hom(P,N)
  let ι : (P →ₗ[R] N') →ₗ[F] (P →ₗ[R] N) :=
    { toFun := fun f => N'.subtype.comp f
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  -- range ι = ker ψ (exactness of Hom(P, −) applied to 0 → N' → N → N/N' → 0)
  have hι_range : LinearMap.range ι = LinearMap.ker ψ := by
    ext f
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext p
      show N'.mkQ (N'.subtype (g p)) = 0
      simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, (g p).2]
    · intro hf
      refine ⟨{ toFun := fun p => ⟨f p, ?_⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
      · have : (ψ f) p = 0 := LinearMap.ext_iff.mp hf p
        simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply] at this
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      · intro x y; ext; simp
      · intro r x; ext; simp
      · ext p; simp [ι]
  -- ι is injective
  have hι_inj : Function.Injective ι := by
    intro f g hfg
    ext p
    have := LinearMap.ext_iff.mp hfg p
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply] at this
    exact this
  -- Apply rank-nullity: finrank(range ψ) + finrank(ker ψ) = finrank(source)
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  -- finrank(range ψ) = finrank(codomain) by surjectivity
  rw [LinearMap.range_eq_top.mpr hψ_surj, finrank_top] at hrn
  -- finrank(ker ψ) = finrank(range ι) = finrank(Hom(P,N'))
  rw [← hι_range, LinearEquiv.finrank_eq (LinearEquiv.ofInjective ι hι_inj).symm] at hrn
  linarith

/-- The composition factor multiplicity of a series `s` decomposes as the multiplicity
of the truncated series `s.eraseLast` plus 1 or 0 depending on whether the last
composition factor is isomorphic to S. -/
theorem Etingof.compositionFactorMultiplicity_eraseLast
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : CompositionSeries (Submodule A N))
    (hs : 0 < s.length)
    (S : Type*) [AddCommGroup S] [Module A S] :
    Etingof.compositionFactorMultiplicity s S =
      Etingof.compositionFactorMultiplicity s.eraseLast S +
      @ite ℕ (Nonempty ((↥(s.last) ⧸
          (s.eraseLast.last).comap (s.last).subtype) ≃ₗ[A] S))
        (Classical.dec _) 1 0 := by
  -- Proof by induction on composition series length
  unfold Etingof.compositionFactorMultiplicity;
  rw [ Finset.card_filter, Finset.card_filter ];
  rcases s with ⟨ ⟨ l, hl ⟩ ⟩ ; aesop;
  erw [ Fin.sum_univ_castSucc ] ; aesop;

/-- The dimension of Hom from a module into `↥(⊤ : Submodule R N)` equals the dimension
of Hom into `N` itself, via the canonical equivalence `↥⊤ ≃ N`. -/
theorem finrank_hom_submodule_top
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module F P] [IsScalarTower F R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N] :
    Module.finrank F (P →ₗ[R] (⊤ : Submodule R N)) = Module.finrank F (P →ₗ[R] N) := by
  apply LinearEquiv.finrank_eq
  exact
  { toFun := fun f => Submodule.topEquiv.toLinearMap.comp f
    invFun := fun f => (Submodule.topEquiv.symm.toLinearMap.comp f : P →ₗ[R] (⊤ : Submodule R N))
    left_inv := fun f => by ext x; simp [Submodule.topEquiv]
    right_inv := fun f => by ext x; simp [Submodule.topEquiv]
    map_add' := fun f g => by ext; simp
    map_smul' := fun c f => by ext; simp }

end Helpers

/-- **Proposition 9.2.3**: The dimension of Hom_A(Pᵢ, N) equals the Jordan–Hölder
multiplicity of Mᵢ in N.

Let A be a finite-dimensional algebra over a field k, let M₁, …, Mₘ be the simple
A-modules, and let P₁, …, Pₘ be their projective covers (from Theorem 9.2.1). For any
finite-dimensional A-module N and any composition series `s` of N (with `s.head = ⊥`
and `s.last = ⊤`), the dimension `dim_k Hom_A(Pᵢ, N)` equals the number of composition
factors of `s` that are A-linearly isomorphic to Mᵢ.

The proof proceeds by induction on the composition length of N:
- Base case: N is simple, so N ≅ Mⱼ for some j, and dim Hom(Pᵢ, Mⱼ) = δᵢⱼ by
  Theorem 9.2.1(i).
- Inductive step: given a short exact sequence 0 → N' → N → N/N' → 0 with
  shorter composition series, use exactness of Hom(Pᵢ, −) (since Pᵢ is projective)
  to get dim Hom(Pᵢ, N) = dim Hom(Pᵢ, N') + dim Hom(Pᵢ, N/N''), and multiplicities
  are additive on short exact sequences.

(Etingof Proposition 9.2.3) -/
theorem Etingof.projective_cover_hom_multiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    [∀ i, Etingof.IsIndecomposableModule A (P i)]
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (N : Type*) [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] [SMulCommClass A k N]
    [Module.Finite k N]
    (hM_complete : ∀ (S T : Submodule A N), S ⋖ T →
      ∃ j, Nonempty ((↥T ⧸ S.comap T.subtype) ≃ₗ[A] M j))
    (s : CompositionSeries (Submodule A N))
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    ∀ i, Module.finrank k (P i →ₗ[A] N) =
      Etingof.compositionFactorMultiplicity s (M i) := by
  -- We prove a generalized statement: for any submodule N' with a composition series
  -- from ⊥ to N', the Hom dimension equals the composition factor multiplicity.
  -- This generalization is needed because the inductive step works with a proper
  -- submodule of N, not N itself.
  suffices gen : ∀ (N' : Submodule A N)
      (s : CompositionSeries (Submodule A N))
      (_ : s.head = ⊥) (_ : s.last = N'),
      ∀ i, Module.finrank k (P i →ₗ[A] N') =
        Etingof.compositionFactorMultiplicity s (M i) by
    intro i
    rw [← finrank_hom_submodule_top (R := A) (F := k)]
    exact gen ⊤ s hs_head hs_last i
  -- Induction on the length of the composition series
  intro N' s' hs'_head hs'_last
  induction hn : s'.length generalizing N' s' with
  | zero =>
    intro i
    have hN'_bot : N' = ⊥ := by
      rw [← hs'_last, ← hs'_head]
      simp only [RelSeries.head, RelSeries.last, Fin.last]
      congr 1; ext; omega
    subst hN'_bot
    have lhs_zero : Module.finrank k (P i →ₗ[A] (⊥ : Submodule A N)) = 0 := by
      apply finrank_hom_of_bot_eq_top (R := A) (F := k)
      ext ⟨x, hx⟩
      simp only [Submodule.mem_bot, Submodule.mem_top, iff_true]
      have := hx
      simp only [Submodule.mem_bot] at this
      exact Subtype.ext this
    have rhs_zero : Etingof.compositionFactorMultiplicity s' (M i) = 0 := by
      unfold Etingof.compositionFactorMultiplicity
      have : Finset.univ (α := Fin s'.length) = ∅ := by
        rw [Finset.univ_eq_empty_iff]; exact hn ▸ Fin.isEmpty
      simp [this]
    rw [lhs_zero, rhs_zero]
  | succ n ih =>
    intro i
    -- Decompose the multiplicity: factors of s' = factors of s'.eraseLast + last factor
    rw [Etingof.compositionFactorMultiplicity_eraseLast s' (by omega) (M i)]
    -- Apply the IH to the truncated series
    set N'' := s'.eraseLast.last
    have h_el_head : s'.eraseLast.head = ⊥ := by
      rw [RelSeries.head_eraseLast]; exact hs'_head
    have h_el_len : s'.eraseLast.length = n := by simp [hn]
    rw [← ih N'' s'.eraseLast h_el_head rfl h_el_len i]
    -- Apply Hom additivity: finrank(P i →ₗ N') = finrank(P i →ₗ N'') + finrank(P i →ₗ N'/N'')
    -- N'' is a submodule of N' since the series is increasing
    -- The submodule of ↥N' corresponding to N'' is N''.comap N'.subtype
    subst hs'_last
    set Q := Submodule.comap (s'.last).subtype N'' with hQ_def
    -- P i is finite-dimensional over k (from Module.Finite A (P i) and Module.Finite k A)
    haveI : Module.Finite k (P i) := Module.Finite.trans A (P i)
    -- ↥(s'.last) is finite-dimensional over k (k-subspace of finite-dim N)
    haveI : Module.Finite k ↥(s'.last) :=
      FiniteDimensional.finiteDimensional_submodule ((s'.last).restrictScalars k)
    -- N'' ≤ s'.last from the composition series
    have hN''_le : N'' ≤ s'.last :=
      (s'.eraseLast_last_rel_last (by omega)).le
    -- ↥Q ≃ₗ[k] ↥N'' via comapSubtypeEquivOfLe
    have e := Submodule.comapSubtypeEquivOfLe hN''_le
    have hQ_eq : Module.finrank k (P i →ₗ[A] ↥Q) = Module.finrank k (P i →ₗ[A] ↥N'') := by
      apply LinearEquiv.finrank_eq
      exact LinearEquiv.mk
        { toFun := fun f => (e.toLinearMap).comp f
          map_add' := fun f g => by simp [LinearMap.comp_add]
          map_smul' := fun c f => by simp [LinearMap.comp_smul] }
        (fun f => (e.symm.toLinearMap).comp f)
        (fun f => by simp)
        (fun f => by simp)
    -- Apply Hom additivity for projective modules
    have haddit := finrank_hom_additive_of_projective
      (R := A) (F := k) (P := P i) (N := ↥(s'.last)) Q
    rw [haddit, hQ_eq]
    -- Suffices to show finrank(P i →ₗ S) = ite (Nonempty (S ≃ₗ M i)) 1 0
    -- where S = ↥(s'.last) ⧸ Q is the last composition factor
    congr 1
    set S := (↥(s'.last) ⧸ Q)
    split
    · -- Case: S ≅ M i → finrank = 1
      rename_i h
      obtain ⟨iso⟩ := h
      -- Construct k-linear equiv Hom(P i, S) ≃ₗ[k] Hom(P i, M i)
      have hom_equiv : Module.finrank k (P i →ₗ[A] S) = Module.finrank k (P i →ₗ[A] M i) := by
        apply LinearEquiv.finrank_eq
        exact LinearEquiv.mk
          { toFun := fun f => iso.toLinearMap.comp f
            map_add' := fun f g => by simp [LinearMap.comp_add]
            map_smul' := fun c f => by simp [LinearMap.comp_smul] }
          (fun f => iso.symm.toLinearMap.comp f)
          (fun f => by simp)
          (fun f => by simp)
      rw [hom_equiv, hP i i, if_pos rfl]
    · -- Case: S ≇ M i → finrank = 0
      rename_i h
      -- S is simple (composition factor from CovBy step)
      have hcovby : N'' ⋖ s'.last := s'.eraseLast_last_rel_last (by omega)
      haveI : IsSimpleModule A (↥(s'.last) ⧸ Q) :=
        (covBy_iff_quot_is_simple hN''_le).mp hcovby
      -- S ≅ M j for some j (completeness of simple modules)
      obtain ⟨j, ⟨iso_j'⟩⟩ := hM_complete N'' s'.last hcovby
      -- Convert iso_j' to use Q (definitionally equal but Lean needs the rewrite)
      have iso_j : S ≃ₗ[A] M j := by
        change (↥(s'.last) ⧸ Q) ≃ₗ[A] M j
        rw [hQ_def]; exact iso_j'
      -- j ≠ i (otherwise S ≅ M j ≅ M i, contradicting h)
      have hji : j ≠ i := by
        intro hji; subst hji; exact h ⟨iso_j⟩
      -- finrank(P i →ₗ S) = finrank(P i →ₗ M j) = 0
      have hom_equiv : Module.finrank k (P i →ₗ[A] S) = Module.finrank k (P i →ₗ[A] M j) := by
        apply LinearEquiv.finrank_eq
        exact LinearEquiv.mk
          { toFun := fun f => iso_j.toLinearMap.comp f
            map_add' := fun f g => by simp [LinearMap.comp_add]
            map_smul' := fun c f => by simp [LinearMap.comp_smul] }
          (fun f => iso_j.symm.toLinearMap.comp f)
          (fun f => by simp)
          (fun f => by simp)
      rw [hom_equiv, hP i j, if_neg (Ne.symm hji)]
