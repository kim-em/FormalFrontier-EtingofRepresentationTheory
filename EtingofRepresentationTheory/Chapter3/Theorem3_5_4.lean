import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Pi
import EtingofRepresentationTheory.Chapter3.Definition3_5_1
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2
import EtingofRepresentationTheory.Chapter3.Proposition3_5_3

/-!
# Theorem 3.5.4: Structure of Finite Dimensional Algebras Modulo Radical

A finite dimensional algebra A has only finitely many irreducible representations Vᵢ
up to isomorphism. These representations are finite dimensional, and

  A / Rad(A) ≅ ⊕ᵢ End(Vᵢ).
-/

universe u in
set_option linter.unusedFintypeInType false in
/-- A finite dimensional algebra over an algebraically closed field has finitely many
irreducible representations. Given a complete set of pairwise nonisomorphic irreducibles,
A/Rad(A) is isomorphic to the product of their endomorphism algebras.
Etingof Theorem 3.5.4. -/
theorem Etingof.structure_mod_radical (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    Nonempty ((A ⧸ Etingof.Radical A) ≃ₐ[k] (∀ i, Module.End k (V i))) := by
  -- SMulCommClass needed for Algebra.lsmul
  haveI : ∀ i, SMulCommClass A k (V i) := fun i =>
    { smul_comm := fun a c v => smul_algebra_smul_comm c a v }
  -- The combined representation algebra homomorphism
  let φ : A →ₐ[k] (∀ i, Module.End k (V i)) :=
    Pi.algHom k (fun i => Module.End k (V i)) (fun i => Algebra.lsmul k k (V i))
  -- φ is surjective by the density theorem
  have hφ_surj : Function.Surjective φ :=
    Etingof.density_theorem_part2 k A ι V h_noniso
  -- Rad(A) ≤ ker(φ): elements of the radical annihilate all simple modules
  have hrad_le_ker : Etingof.Radical A ≤ RingHom.ker φ.toRingHom := by
    intro a ha
    rw [RingHom.mem_ker]
    ext i : 1
    -- Need: (Algebra.lsmul k k (V i)) a = 0, i.e., ∀ v, a • v = 0
    ext v : 1
    -- a ∈ Rad(A) = Ideal.jacobson ⊥ = Ring.jacobson A. V i is simple hence semisimple.
    -- The Jacobson radical annihilates all semisimple modules.
    change a • v = 0
    have ha' : a ∈ Ring.jacobson A := by rwa [← Ideal.jacobson_bot]
    have h_le := IsSemisimpleModule.jacobson_le_annihilator (R := A) (M := V i)
    exact Module.mem_annihilator.mp (h_le ha') v
  -- ker(φ) ≤ Rad(A): elements acting by 0 on all V_i are in the radical
  have hker_le_rad : RingHom.ker φ.toRingHom ≤ Etingof.Radical A := by
    -- For each maximal left ideal J, A/J is a simple A-module, hence ≅ some V_j.
    -- If a ∈ ker φ, then a annihilates V_j, hence annihilates A/J, so a ∈ J.
    -- Thus a ∈ ⋂ maximal ideals = Rad A.
    intro a ha
    show a ∈ Etingof.Radical A
    unfold Etingof.Radical
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    simp only [Ideal.mem_sInf, Set.mem_setOf_eq]
    intro J hJ
    -- A ⧸ J is a simple A-module
    haveI : IsSimpleModule A (A ⧸ J) := by
      rwa [isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    -- A ⧸ J has the necessary instances for h_complete
    haveI : FiniteDimensional k (A ⧸ J) :=
      Module.Finite.of_surjective ((Submodule.mkQ J).restrictScalars k)
        (Submodule.Quotient.mk_surjective _)
    -- By completeness, A ⧸ J ≅ V j for some j
    obtain ⟨j, ⟨e⟩⟩ := h_complete (A ⧸ J)
    -- a ∈ ker φ means a acts as 0 on V j
    have ha_ker : a ∈ RingHom.ker φ.toRingHom := ha
    rw [RingHom.mem_ker] at ha_ker
    have ha_Vj : ∀ v : V j, a • v = 0 := by
      intro v
      have := congr_fun ha_ker j
      exact LinearMap.congr_fun this v
    -- Transport: a acts as 0 on A ⧸ J via the isomorphism
    have ha_quot : ∀ x : A ⧸ J, a • x = 0 := by
      intro x
      have : a • (e x) = 0 := ha_Vj (e x)
      rw [← e.map_smul] at this
      exact e.injective (by rwa [map_zero])
    -- a • (1 : A) ∈ J, i.e., a ∈ J
    have h1 : a • (Submodule.Quotient.mk (p := J) (1 : A) : A ⧸ J) = 0 := ha_quot _
    rwa [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      Submodule.Quotient.mk_eq_zero] at h1
  -- ker(φ) = Rad(A)
  have hker_eq : RingHom.ker φ.toRingHom = Etingof.Radical A :=
    le_antisymm hker_le_rad hrad_le_ker
  -- Compose: A/Rad(A) ≅ A/ker(φ) ≅ ∏ End(V_i)
  exact ⟨(Ideal.quotientEquivAlgOfEq k hker_eq.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ_surj)⟩
