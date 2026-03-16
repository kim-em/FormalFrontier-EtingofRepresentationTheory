import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Theorem 3.2.2: The Density Theorem

(i) Let V be an irreducible finite dimensional representation of A over an algebraically
closed field k. Then the map ρ : A → End V is surjective.

(ii) Let V = V₁ ⊕ ⋯ ⊕ Vᵣ, where Vᵢ are irreducible pairwise nonisomorphic finite
dimensional representations of A. Then the map ⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ) is surjective.
-/

open Module in
/-- The density theorem, part (i): For an irreducible finite dimensional representation
over an algebraically closed field, the representation map A → End(V) is surjective.
Etingof Theorem 3.2.2(i). -/
theorem Etingof.density_theorem_part1 (k : Type*) (A : Type*) (V : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] End k V) := by
  intro f
  -- By Schur's lemma over algebraically closed k, End_A(V) ≅ k
  have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k
  -- Every k-linear endomorphism is End_A(V)-linear since End_A(V) = k
  have g_smul : ∀ (c : End A V) (v : V), f (c • v) = c • f v := by
    intro c v
    obtain ⟨t, ht⟩ := hbij.2 c
    have hc : ∀ w, c w = t • w := fun w => by simp [← ht]
    simp only [End.smul_def, hc, map_smul]
  -- Lift f to an End_A(V)-linear endomorphism
  let g : End (End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := g_smul }
  -- V is finite over End_A(V) since End_A(V) = k and V is finite-dimensional over k
  haveI : Module.Finite (End A V) V :=
    Module.Finite.of_restrictScalars_finite k (End A V) V
  -- Apply the Jacobson density theorem
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) g
  -- Both Algebra.lsmul and toModuleEnd send a to (v ↦ a • v)
  exact ⟨a, LinearMap.ext fun v => show a • v = f v from congr($(ha) v)⟩

/-- The density theorem, part (ii): For a direct sum of pairwise nonisomorphic irreducible
representations, the combined representation map is surjective.
Etingof Theorem 3.2.2(ii). -/
theorem Etingof.density_theorem_part2 (k : Type*) (A : Type*) (ι : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Function.Surjective
      (fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] Module.End k (V i)) a :
        A → ∀ i, Module.End k (V i)) := by
  sorry
