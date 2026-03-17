import EtingofRepresentationTheory.Chapter9.Theorem9_2_1
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.SimpleModule.Basic

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
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N] [SMulCommClass R F N]
    [Module.Finite F N]
    (N' : Submodule R N) :
    Module.finrank F (P →ₗ[R] N) =
      Module.finrank F (P →ₗ[R] N') + Module.finrank F (P →ₗ[R] (N ⧸ N')) := by
  sorry

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
  sorry

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
    -- Now need: finrank(P i →ₗ N') = finrank(P i →ₗ N'') + finrank(P i →ₗ last_factor)
    -- This follows from the Hom additivity for projective modules
    -- and the identification of the last factor with the quotient N'/N''
    sorry
