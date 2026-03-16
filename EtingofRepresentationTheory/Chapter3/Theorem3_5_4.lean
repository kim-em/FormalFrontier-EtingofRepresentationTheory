import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import EtingofRepresentationTheory.Chapter3.Definition3_5_1

/-!
# Theorem 3.5.4: Structure of Finite Dimensional Algebras Modulo Radical

A finite dimensional algebra A has only finitely many irreducible representations Vᵢ
up to isomorphism. These representations are finite dimensional, and

  A / Rad(A) ≅ ⊕ᵢ End(Vᵢ).
-/

set_option linter.unusedFintypeInType false in
/-- A finite dimensional algebra over an algebraically closed field has finitely many
irreducible representations. Given a complete set of pairwise nonisomorphic irreducibles,
A/Rad(A) is isomorphic to the product of their endomorphism algebras.
Etingof Theorem 3.5.4. -/
theorem Etingof.structure_mod_radical (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    Nonempty ((A ⧸ Etingof.Radical A) ≃ₐ[k] (∀ i, Module.End k (V i))) := by
  sorry
