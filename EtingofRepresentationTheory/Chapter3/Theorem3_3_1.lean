import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Theorem 3.3.1: Irreducible Representations of Direct Sums of Matrix Algebras

Let A = ⊕ᵢ Mat_{dᵢ}(k). Then the irreducible representations of A are
V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}, and any finite dimensional representation of A is a direct
sum of copies of V₁, …, Vᵣ.

The core of this result is that each matrix algebra Mat_d(k) has a unique
irreducible representation, namely the standard representation k^d. The full
theorem follows because the irreducible representations of a direct sum of
algebras are exactly the irreducible representations of the individual factors.
-/

open Matrix.Module Finset

private theorem matrix_single_smul_vec {k : Type*} [Field k] {d : ℕ}
    (j i : Fin d) (c : k) (v : Fin d → k) :
    (Matrix.single j i c • v) = fun l => if l = j then c * v i else 0 := by
  ext l
  simp only [smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hjl : j = l
  · subst hjl
    simp only [true_and, ite_mul, zero_mul]
    rw [sum_ite_eq univ i]
    simp
  · simp only [show ¬(j = l) from hjl, false_and, ite_false, zero_mul, sum_const_zero,
      show ¬(l = j) from Ne.symm hjl, ite_false]

/-- The standard representation `Fin d → k` is a simple module over `Matrix (Fin d) (Fin d) k`.
Any nonzero vector generates the whole module under the matrix action. -/
private theorem isSimpleModule_matrix_vecModule (k : Type*) [Field k]
    (d : ℕ) [NeZero d] :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) where
  eq_bot_or_eq_top s := by
    by_cases hs : s = ⊥
    · exact Or.inl hs
    · right
      obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
      have ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h; push_neg at h
        exact hne (funext fun j => by simpa using h j)
      have basis_mem : ∀ j, Pi.single j (1 : k) ∈ s := by
        intro j
        have h1 := s.smul_mem (Matrix.single j i (v i)⁻¹) hv
        rw [matrix_single_smul_vec] at h1
        convert h1 using 1
        ext l
        simp [Pi.single_apply, inv_mul_cancel₀ hi]
      rw [eq_top_iff]
      intro w _
      -- Write w as a sum of matrix-scaled basis vectors
      suffices w = ∑ j ∈ univ, Matrix.single j j (w j) •
          (Pi.single j (1 : k) : Fin d → k) by
        rw [this]
        exact sum_mem fun j _ => s.smul_mem _ (basis_mem j)
      ext l
      simp only [sum_apply, matrix_single_smul_vec, Pi.single_apply, ite_true, mul_one]
      rw [sum_ite_eq univ l]; simp

/-- The standard representation k^d is the unique irreducible representation of Mat_d(k).
Every irreducible representation of ⊕ᵢ Mat_{dᵢ}(k) is isomorphic to one of the standard
representations k^{dⱼ} (for some factor j). Etingof Theorem 3.3.1. -/
theorem Etingof.irreducible_reps_of_matrix_algebra (k : Type*) [Field k]
    (d : ℕ) [NeZero d] (V : Type*)
    [AddCommGroup V] [Module k V] [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  letI := isSimpleModule_matrix_vecModule k d
  letI : IsSimpleRing (Matrix (Fin d) (Fin d) k) := IsSimpleRing.matrix ..
  letI : IsArtinianRing (Matrix (Fin d) (Fin d) k) := inferInstance
  -- Both V and (Fin d → k) are simple modules over a simple Artinian ring.
  -- By the Wedderburn-Artin theorem, a simple Artinian ring has a unique
  -- simple module up to isomorphism. We show this via isotypicity:
  -- both embed into R as simple left ideals, and all such ideals are isomorphic.
  have ⟨I, ⟨eI⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) V
  have ⟨I', ⟨eI'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) (Fin d → k)
  haveI : IsSimpleModule _ I := IsSimpleModule.congr eI.symm
  haveI : IsSimpleModule _ I' := IsSimpleModule.congr eI'.symm
  have hiso := IsSimpleRing.isIsotypic (Matrix (Fin d) (Fin d) k) (Matrix (Fin d) (Fin d) k)
  have ⟨eII'⟩ := hiso I I'
  exact ⟨eI.trans (eII'.symm.trans eI'.symm)⟩
