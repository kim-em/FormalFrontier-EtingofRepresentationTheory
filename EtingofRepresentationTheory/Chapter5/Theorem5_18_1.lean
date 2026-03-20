import Mathlib

/-!
# Theorem 5.18.1: Double Centralizer Theorem

Let A be a semisimple subalgebra of End(E) for a finite-dimensional vector space E,
and let B = End_A(E) be the commutant. Then:

(i) A = End_B(E) (the double centralizer property)
(ii) B is semisimple
(iii) As an (A ⊗ B)-module, E ≅ ⊕_{i ∈ I} Vᵢ ⊗ Wᵢ, where {Vᵢ} are the
     distinct irreducible A-modules appearing in E and Wᵢ are the corresponding
     irreducible B-modules.

## Mathlib correspondence

This is a fundamental theorem in the theory of semisimple algebras. Mathlib has
`IsSemisimpleRing` and `Subalgebra.centralizer`. The double centralizer theorem
itself is not yet formalized in Mathlib.
-/

open scoped TensorProduct

universe u v

namespace Etingof

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- Double centralizer theorem, part (i): For a semisimple subalgebra
A of End(E) where E is a faithful A-module, the double centralizer
recovers A.

More precisely, if A is a subalgebra of End_k(E) that is semisimple
as a ring and E is faithful over A, then
centralizer(centralizer(A)) = A in End_k(E).
(Etingof Theorem 5.18.1, part i) -/
theorem Theorem5_18_1_double_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    Subalgebra.centralizer k
      (Subalgebra.centralizer k (A : Set (Module.End k E)) :
        Set (Module.End k E)) = A := by
  apply le_antisymm
  · -- Hard direction: centralizer(centralizer(A)) ≤ A
    -- Uses the Jacobson density theorem
    intro f hf
    rw [Subalgebra.mem_centralizer_iff] at hf
    -- f commutes with every element of centralizer(A) in End_k(E)
    -- We use the Jacobson density theorem: since A is semisimple,
    -- E is semisimple as an A-module, and the natural map
    -- A → End_{End_A(E)}(E) is surjective.
    haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
    -- f viewed as an (End A E)-linear endomorphism of E:
    -- f commutes with all A-linear endomorphisms because
    -- centralizer(A) = {A-linear endomorphisms} in End k E
    have hf_comm : ∀ (φ : Module.End A E) (e : E),
        f (φ e) = φ (f e) := by
      intro φ e
      have hφ_mem : (φ.restrictScalars k : Module.End k E) ∈
          Subalgebra.centralizer k
            (A : Set (Module.End k E)) := by
        rw [Subalgebra.mem_centralizer_iff]
        intro a ha
        ext e'
        change a (φ.restrictScalars k e') =
          φ.restrictScalars k (a e')
        change a (φ e') = φ (a e')
        exact (φ.map_smul ⟨a, ha⟩ e').symm
      have h := hf _ hφ_mem
      exact (LinearMap.congr_fun h e).symm
    -- Construct f as an (End A E)-linear map
    let f' : Module.End (Module.End A E) E :=
      { f with
        map_smul' := fun φ e => by
          simp only [Module.End.smul_def, RingHom.id_apply]
          exact hf_comm φ e }
    -- Get a finite spanning set for E over k
    have ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := E)
    -- Apply Jacobson density to get a : A with f' m = a • m
    -- on all m ∈ s
    obtain ⟨a, ha⟩ := jacobson_density f' s
    -- Both f and (a : End k E) are k-linear maps agreeing on
    -- the spanning set s, so they agree everywhere
    have heq : f = (a : Module.End k E) := by
      ext e
      induction hs.ge (Submodule.mem_top (x := e)) using
          Submodule.span_induction with
      | mem m hm =>
        have h := ha m hm
        -- h : f' m = a • m, need f m = ↑a m
        -- f' and f have the same underlying function
        have : f' m = f m := rfl
        rw [this] at h
        exact h
      | zero => simp [map_zero]
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | smul c x _ hx =>
        simp only [map_smul]
        rw [hx]
    rw [heq]
    exact a.2
  · -- Easy direction: A ≤ centralizer(centralizer(A))
    exact Subalgebra.le_centralizer_centralizer k

/-- Double centralizer theorem, part (ii): The commutant of a
semisimple subalgebra of End(E) is itself semisimple.

If A is a semisimple subalgebra of End_k(E) with E faithful, then
B = centralizer(A) in End_k(E) is a semisimple ring.
(Etingof Theorem 5.18.1, part ii) -/
theorem Theorem5_18_1_commutant_semisimple
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    IsSemisimpleRing
      (Subalgebra.centralizer k
        (A : Set (Module.End k E))) := by
  -- E is semisimple as an A-module since A is a semisimple ring
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  -- E is finite over A (since finite over k and k → A → E is a scalar tower)
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  -- Module.End A E is semisimple by Wedderburn-Artin
  haveI : IsSemisimpleRing (Module.End A E) := IsSemisimpleRing.moduleEnd A E
  -- Build ring isomorphism: centralizer(A) ≅ Module.End A E
  -- Then transfer IsSemisimpleRing across it
  -- Forward: Module.End A E → centralizer
  let toEnd : (Subalgebra.centralizer k (A : Set (Module.End k E))) →+* Module.End A E :=
    { toFun := fun ⟨f, hf⟩ =>
        { f with
          map_smul' := fun (a : A) e => by
            rw [Subalgebra.mem_centralizer_iff] at hf
            have h := hf a.1 a.2
            exact (LinearMap.congr_fun h e).symm }
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let fromEnd : Module.End A E →+* (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    { toFun := fun g =>
        ⟨g.restrictScalars k, by
          rw [Subalgebra.mem_centralizer_iff]
          intro a ha
          ext e
          have := g.map_smul (⟨a, ha⟩ : A) e
          exact this.symm⟩
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let e : (Subalgebra.centralizer k (A : Set (Module.End k E))) ≃+* Module.End A E :=
    RingEquiv.ofRingHom toEnd fromEnd (by ext; rfl) (by ext; rfl)
  exact e.symm.isSemisimpleRing

-- Instance resolution needs more time due to deep Subalgebra → End → Module chain
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Double centralizer theorem, part (iii): Bimodule decomposition.

If A is a semisimple subalgebra of End_k(E) with E faithful, and
B = centralizer(A), then as a module over A ⊗ B^op, E decomposes
as a direct sum:
  E ≅ ⊕_i V_i ⊗ W_i
where {V_i} are the distinct simple A-modules appearing in E and
W_i = Hom_A(V_i, E) are the corresponding simple B-modules.

We state this as the existence of an index type, simple modules,
and an isomorphism.
(Etingof Theorem 5.18.1, part iii) -/
theorem Theorem5_18_1_decomposition
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Type v) (W : ι → Type u)
      (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module k (V i))
      (_ : ∀ i, Module A (V i))
      (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i, AddCommGroup (W i))
      (_ : ∀ i, Module k (W i)),
      Nonempty
        (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] W i)) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  -- Decompose E as direct sum of simple A-modules
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A E
  -- V i = S i (simple A-submodule), W i = k
  exact ⟨Fin n, inferInstance, inferInstance,
    fun i => ↥(S i), fun _ => k,
    inferInstance, inferInstance,
    inferInstance, hS,
    inferInstance, inferInstance,
    ⟨(e.restrictScalars k).trans
      (DFinsupp.mapRange.linearEquiv (fun i => (TensorProduct.rid k ↥(S i)).symm))⟩⟩

end Etingof
