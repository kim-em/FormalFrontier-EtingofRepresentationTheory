import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.6.2: Linear Independence of Characters

(i) Characters of (distinct) irreducible finite dimensional representations of A are
    linearly independent.

(ii) If A is a finite dimensional semisimple algebra, then these characters form a basis
     of (A/[A,A])*.

The proof of (i) uses the density theorem: the surjectivity of the combined representation
map ensures that traces of distinct irreducibles can be independently varied.

The proof of (ii) shows that [Mat_d(k), Mat_d(k)] = sl_d(k) (traceless matrices),
so A/[A,A] ≅ k^r for semisimple A = ⊕ Mat_{dᵢ}(k), and r linearly independent
characters on an r-dimensional space form a basis.
-/

open Module in
/-- The character of a finite-dimensional module V over a k-algebra A, defined as
the trace of the action map: χ_V(a) = tr(ρ_V(a)). -/
noncomputable def Etingof.character (k : Type*) (A : Type*) (V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Free k V] [Module.Finite k V] :
    Dual k A :=
  (LinearMap.trace k V).comp (Algebra.lsmul k k V : A →ₐ[k] End k V).toLinearMap

open Module in
/-- Characters of distinct irreducible representations are linearly independent.
Etingof Theorem 3.6.2(i). -/
theorem Etingof.characters_linearly_independent (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => Etingof.character k A (V i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- hg : ∑ j, g j • character k A (V j) = 0
  -- The hypothesis evaluated at any a ∈ A gives ∑ j, g j * χⱼ(a) = 0
  have hga : ∀ a : A, ∑ j, g j * Etingof.character k A (V j) a = 0 := by
    intro a
    have := LinearMap.congr_fun hg a
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    exact this
  -- By density theorem part 2, the map A → ∏ End(Vᵢ) is surjective
  have hsurj := Etingof.density_theorem_part2 k A ι V h_noniso
  -- For V i, construct an endomorphism with trace 1 using a basis
  classical
  haveI : Nontrivial (V i) := IsSimpleModule.nontrivial A (V i)
  let b := Module.Free.chooseBasis k (V i)
  have hne_idx : Nonempty (Module.Free.ChooseBasisIndex k (V i)) := by
    rw [← not_isEmpty_iff]
    intro h
    have : finrank k (V i) = 0 := by simp [finrank_eq_card_chooseBasisIndex, Fintype.card_eq_zero]
    have : 0 < finrank k (V i) := Module.finrank_pos
    omega
  let idx := hne_idx.some
  -- The rank-1 endomorphism b.coord idx ⊗ b idx has trace 1
  -- Use density to find a : A mapping to this on V i and 0 on V j for j ≠ i
  let target : ∀ j, Module.End k (V j) := fun j =>
    if h : j = i then h ▸ (dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx)) else 0
  obtain ⟨a, ha⟩ := hsurj target
  -- Evaluate at a: only the i-th term survives with trace 1
  have h0 := hga a
  -- Rewrite using ha: ρⱼ(a) = target j
  have hρ : ∀ j, (Algebra.lsmul k k (V j) : A →ₐ[k] Module.End k (V j)) a = target j := by
    intro j; exact congr_fun ha j
  -- Unfold character and rewrite ρⱼ(a) = target j
  simp only [Etingof.character, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h0
  -- Rewrite each ρⱼ(a) to target j, then the sum simplifies:
  -- target j = 0 for j ≠ i (trace 0), target i has trace 1
  have htarget_ne : ∀ j, j ≠ i → target j = 0 := by
    intro j hj; simp [target, hj]
  have htarget_eq : target i = dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx) := by
    simp [target]
  have htr_target_i : LinearMap.trace k (V i) (target i) = 1 := by
    rw [htarget_eq, LinearMap.trace_eq_contract_apply]
    simp [contractLeft, Basis.coord]
  have htr_ne : ∀ j, j ≠ i → LinearMap.trace k (V j) (target j) = 0 := by
    intro j hj; rw [htarget_ne j hj, map_zero]
  -- Rewrite the sum: separate i-th term, zero out the rest
  have hsum : ∑ j, g j * LinearMap.trace k (V j) (target j) =
      g i * LinearMap.trace k (V i) (target i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_eq_zero (fun j hj => by rw [htr_ne j (Finset.ne_of_mem_erase hj), mul_zero])]
    ring
  -- Now use hρ to rewrite h0 term by term
  have h0' : ∑ j, g j * LinearMap.trace k (V j) (target j) = 0 := by
    have : ∀ j, LinearMap.trace k (V j) ((Algebra.lsmul k k (V j) : A →ₐ[k] _) a) =
        LinearMap.trace k (V j) (target j) := fun j => congrArg _ (hρ j)
    simp only [this] at h0; exact h0
  rw [hsum, htr_target_i, mul_one] at h0'
  exact h0'

open Module in
/-- For a semisimple algebra, characters of irreducibles span the space of tracial
linear functionals (those f with f(ab) = f(ba)), hence form a basis of (A/[A,A])*.
Combined with part (i), this gives a basis.
Etingof Theorem 3.6.2(ii). -/
theorem Etingof.characters_basis_semisimple (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    ∀ f : Dual k A, (∀ a b : A, f (a * b) = f (b * a)) →
      f ∈ Submodule.span k (Set.range (fun i => Etingof.character k A (V i))) := by
  sorry
