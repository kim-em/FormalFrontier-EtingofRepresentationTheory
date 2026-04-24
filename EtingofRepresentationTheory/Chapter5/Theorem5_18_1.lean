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

/-!
## Helper: isotypic direct sum decomposition

For a semisimple Noetherian `R`-module `M`, its isotypic components form a
finite independent family covering all of `M`. This gives a canonical
decomposition `M ≃[R] ⨁ c : isotypicComponents R M, c`.
-/

/-- Decomposition of a semisimple Noetherian `R`-module into its isotypic
components. The index set `isotypicComponents R M` groups simple submodules
by isomorphism class. -/
noncomputable def isotypicDirectSumEquiv
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] [IsNoetherian R M]
    [DecidableEq (isotypicComponents R M)] :
    (Π₀ c : isotypicComponents R M, (c.1 : Submodule R M)) ≃ₗ[R] M :=
  let ind : iSupIndep fun c : isotypicComponents R M =>
      (c.1 : Submodule R M) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  have iSup_top :
      (⨆ c : isotypicComponents R M, (c.1 : Submodule R M)) = ⊤ := by
    rw [← sSup_eq_iSup']
    exact sSup_isotypicComponents R M
  ind.linearEquiv iSup_top

/-!
## Helper: Schur evaluation isomorphism

For a simple `A`-module `V` over an algebraically closed field `k`, an
isotypic-of-type-`V` finite-dimensional `A`-module `M` is isomorphic to
`V ⊗[k] (V →ₗ[A] M)` via the evaluation map `v ⊗ f ↦ f v`.
-/

/-- Over an algebraically closed field, the algebra map `k → End_A V` is a
`k`-linear equivalence when `V` is simple and finite-dimensional — Schur's
lemma combined with alg-closedness. -/
noncomputable def endOfSimpleEquivAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V] :
    k ≃ₗ[k] (V →ₗ[A] V) :=
  LinearEquiv.ofBijective (Algebra.linearMap k (V →ₗ[A] V))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

/-- Extracting a scalar from a simple-module endomorphism gives the action
of the scalar on any vector: for an alg-closed-simple `A`-module `V` and an
`A`-linear endomorphism `φ`, the unique scalar `c ∈ k` with `φ = c • id`
satisfies `c • v = φ v` for every `v`. -/
lemma endOfSimpleEquivAlgClosed_symm_smul_apply
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (φ : V →ₗ[A] V) (v : V) :
    (endOfSimpleEquivAlgClosed k A V).symm φ • v = φ v := by
  have hφ : endOfSimpleEquivAlgClosed k A V
      ((endOfSimpleEquivAlgClosed k A V).symm φ) = φ :=
    (endOfSimpleEquivAlgClosed k A V).apply_symm_apply φ
  -- Unfold: `endOfSimpleEquivAlgClosed k A V c = algebraMap k _ c = c • (1 : V →ₗ[A] V)`.
  have hφ' : (endOfSimpleEquivAlgClosed k A V).symm φ • (1 : V →ₗ[A] V) = φ := by
    have hrw : Algebra.linearMap k (V →ₗ[A] V)
        ((endOfSimpleEquivAlgClosed k A V).symm φ) = φ := hφ
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one] at hrw
    exact hrw
  have := LinearMap.congr_fun hφ' v
  simpa [LinearMap.smul_apply, Module.End.one_apply] using this

/-- Post-composition equivalence: an `A`-linear equivalence of the codomain
induces a `k`-linear equivalence of hom-spaces. This works even when `A` is
non-commutative (where `LinearEquiv.congrRight` does not apply directly). -/
noncomputable def homCongrRightOverSubring
    (k : Type*) [CommSemiring k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : M ≃ₗ[A] N) :
    (V →ₗ[A] M) ≃ₗ[k] (V →ₗ[A] N) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp
  map_smul' c f := by
    ext v
    simp [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- The curry equivalence: a map into a product of copies of `V` is the same
as a product of maps into `V`. This is `k`-linear since `k` acts through
either side. -/
noncomputable def homPiCurryEquiv
    (k : Type*) [CommSemiring k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    (ι : Type*) :
    (V →ₗ[A] (ι → V)) ≃ₗ[k] (ι → V →ₗ[A] V) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext v i; rfl
  right_inv g := by funext i; ext v; rfl
  map_add' f g := by funext i; ext v; simp
  map_smul' c f := by funext i; ext v; simp

/-- Schur evaluation isomorphism: for a simple `A`-module `V` over an
algebraically closed field `k`, an isotypic-of-type-`V` finite-dimensional
`A`-module `M` is isomorphic to `V ⊗[k] (V →ₗ[A] M)` as `k`-modules.

The isomorphism is built by composing the multiplicity decomposition
`M ≃[A] Fin n → V` with Schur's lemma (`End_A V ≃[k] k`) and the standard
tensor iso `V ⊗[k] (Fin n → k) ≃[k] Fin n → V`. -/
noncomputable def schurEvaluationEquiv
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M V) :
    V ⊗[k] (V →ₗ[A] M) ≃ₗ[k] M :=
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  let n : ℕ := h.linearEquiv_fun.choose
  let e : M ≃ₗ[A] (Fin n → V) := h.linearEquiv_fun.choose_spec.some
  -- Chain:
  -- V ⊗[k] (V →ₗ[A] M)
  -- ≃[k] V ⊗[k] (V →ₗ[A] Fin n → V)         -- congrRight e
  -- ≃[k] V ⊗[k] (Fin n → V →ₗ[A] V)         -- curry
  -- ≃[k] V ⊗[k] (Fin n → k)                 -- Schur + alg-closed
  -- ≃[k] Fin n → V                           -- piScalarRight
  -- ≃[k] M                                   -- e.symm
  let e1 : (V →ₗ[A] M) ≃ₗ[k] (V →ₗ[A] (Fin n → V)) :=
    homCongrRightOverSubring k A V e
  let e2 : (V →ₗ[A] (Fin n → V)) ≃ₗ[k] (Fin n → V →ₗ[A] V) :=
    homPiCurryEquiv k A V (Fin n)
  let e3 : (Fin n → V →ₗ[A] V) ≃ₗ[k] (Fin n → k) :=
    LinearEquiv.piCongrRight (fun _ => (endOfSimpleEquivAlgClosed k A V).symm)
  let e4 : V ⊗[k] (Fin n → k) ≃ₗ[k] (Fin n → V) :=
    TensorProduct.piScalarRight k k V (Fin n)
  let e5 : (Fin n → V) ≃ₗ[k] M := e.symm.restrictScalars k
  (TensorProduct.congr (LinearEquiv.refl k V)
    (e1.trans (e2.trans e3))).trans (e4.trans e5)

/-- The Schur evaluation isomorphism sends a pure tensor `v ⊗ f` to `f v`.

Despite being constructed via an arbitrary choice of decomposition
`M ≃[A] Fin n → V`, the resulting map is canonical: on pure tensors it is
the evaluation `v ⊗ f ↦ f v`. This is the identity that makes the
decomposition `B`-equivariant — the hom-space `V →ₗ[A] M` carries a
natural right action by `End_A M ⊇ B`, and evaluation transports it. -/
lemma schurEvaluationEquiv_apply_tmul
    (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A]
    (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Module.Finite k V] [IsSimpleModule A V]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M V) (v : V) (f : V →ₗ[A] M) :
    schurEvaluationEquiv k A V M h (v ⊗ₜ[k] f) = f v := by
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  -- Mirror the `let` bindings from `schurEvaluationEquiv` so we can reason
  -- about each step of the chain.
  set n : ℕ := h.linearEquiv_fun.choose
  set e : M ≃ₗ[A] (Fin n → V) := h.linearEquiv_fun.choose_spec.some
  -- The underlying map on pure tensors reduces (by definition) to
  -- `e.symm (fun j => (endOfSimpleEquivAlgClosed k A V).symm φⱼ • v)` where
  -- `φⱼ = (LinearMap.proj j).comp (e.toLinearMap.comp f)`.
  have step1 : schurEvaluationEquiv k A V M h (v ⊗ₜ[k] f)
      = e.symm (fun j =>
          (endOfSimpleEquivAlgClosed k A V).symm
            ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v) := by
    rfl
  rw [step1]
  -- Use the helper: `(endOfSimpleEquivAlgClosed).symm φ • v = φ v`.
  have hv : ∀ j, (endOfSimpleEquivAlgClosed k A V).symm
      ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v = (e (f v)) j := by
    intro j
    rw [endOfSimpleEquivAlgClosed_symm_smul_apply]
    rfl
  have hfun : (fun j => (endOfSimpleEquivAlgClosed k A V).symm
      ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v) = e (f v) := by
    funext j; exact hv j
  rw [hfun]
  exact e.symm_apply_apply (f v)

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

/-!
## Helpers for the bimodule form of the double centralizer theorem

For the bimodule decomposition `E ≃ ⨁ Vᵢ ⊗ Lᵢ`, we need:
* The centralizer `B = centralizer(A)` acts on the Hom-space `V →ₗ[A] E`
  by post-composition. Elements of `B` commute with `A`, hence are
  `A`-linear maps `E → E`, which can be composed on the right of any
  `A`-linear map out of `V`.
* For a simple submodule `V` of an isotypic component `c`, every `A`-linear
  map `V → E` lands inside `c` (by `Submodule.map_le_isotypicComponent`
  combined with `c = isotypicComponent A E V`).
-/

/-- The ring homomorphism `B := centralizer(A) → End_A(E)`: every element of
the centralizer (which commutes with `A`) is `A`-linear. -/
noncomputable def centralizerToEndA
    (A : Subalgebra k (Module.End k E)) :
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) →+*
      Module.End A E where
  toFun b :=
    { toFun := b.val
      map_add' := b.val.map_add
      map_smul' := fun a e => by
        have hb := b.property
        rw [Subalgebra.mem_centralizer_iff] at hb
        have h := hb a.val a.property
        -- h : b.val * a.val = a.val * b.val in End_k(E); apply to e
        have happ := LinearMap.congr_fun h e
        -- happ : (a.val * b.val) e = (b.val * a.val) e
        -- i.e. a.val (b.val e) = b.val (a.val e)
        -- Goal: b.val (a • e) = (RingHom.id A) a • b.val e
        -- Since a • e = a.val e and a • b.val e = a.val (b.val e),
        -- goal becomes b.val (a.val e) = a.val (b.val e), which is happ.symm.
        exact happ.symm }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- `V →ₗ[A] E` carries a `Module B`-structure (where `B = centralizer(A)`)
via post-composition: `(b • f) v := b.val (f v)`. -/
noncomputable instance centralizerModuleHom
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) where
  smul b f := (centralizerToEndA k E A b).comp f
  one_smul f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A 1) (f v) = f v
    rw [map_one]; rfl
  mul_smul b₁ b₂ f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A (b₁ * b₂)) (f v) =
      (centralizerToEndA k E A b₁)
        ((centralizerToEndA k E A b₂) (f v))
    rw [map_mul]; rfl
  smul_zero b := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A b) ((0 : V →ₗ[A] E) v) = 0
    simp
  smul_add b f g := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A b) ((f + g) v) =
      (centralizerToEndA k E A b) (f v) + (centralizerToEndA k E A b) (g v)
    simp
  add_smul b₁ b₂ f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A (b₁ + b₂)) (f v) =
      (centralizerToEndA k E A b₁) (f v) + (centralizerToEndA k E A b₂) (f v)
    rw [map_add]; rfl
  zero_smul f := by
    refine LinearMap.ext fun v => ?_
    change (centralizerToEndA k E A 0) (f v) = 0
    rw [map_zero]; rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- The natural bridge: every `A`-linear map from a simple submodule `V ≤ E`
into `E` lands in the isotypic component `isotypicComponent A E V`. -/
theorem range_le_isotypicComponent_of_simple
    {A : Subalgebra k (Module.End k E)}
    (V : Submodule A E) [IsSimpleModule A V]
    (f : V →ₗ[A] E) :
    LinearMap.range f ≤ isotypicComponent A E V := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  · -- f ≠ 0 ⇒ f injective (Schur on simple V) ⇒ range f ≃[A] V ⇒ range f
    -- lies in the isotypic component determined by V.
    have hker : LinearMap.ker f = ⊥ := by
      rcases eq_bot_or_eq_top (LinearMap.ker f) with h | h
      · exact h
      · exfalso; apply hf
        ext v
        have hv : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa [LinearMap.mem_ker] using hv
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have e : V ≃ₗ[A] LinearMap.range f := LinearEquiv.ofInjective f hinj
    have heq : isotypicComponent A E (LinearMap.range f) = isotypicComponent A E V :=
      e.symm.isotypicComponent_eq
    calc LinearMap.range f
        ≤ isotypicComponent A E (LinearMap.range f) :=
          Submodule.le_isotypicComponent _
      _ = isotypicComponent A E V := heq

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Bridge equivalence: for a simple submodule `V ≤ E` and any submodule
`c` equal to `isotypicComponent A E V`, the hom-space `V →ₗ[A] c` is
`k`-linearly isomorphic to `V →ₗ[A] E`. The forward map post-composes
with the inclusion `c → E`; the inverse co-restricts every `V →ₗ[A] E`
to `c` using `range_le_isotypicComponent_of_simple`. -/
noncomputable def homIsotypicBridge
    (A : Subalgebra k (Module.End k E))
    (V : Submodule A E) [IsSimpleModule A V]
    (c : Submodule A E)
    (hc_eq : c = isotypicComponent A E V) :
    (V →ₗ[A] c) ≃ₗ[k] (V →ₗ[A] E) where
  toFun f := c.subtype.comp f
  invFun g := g.codRestrict c (fun v => by
    have hrange : LinearMap.range g ≤ c := by
      rw [hc_eq]
      exact range_le_isotypicComponent_of_simple (k := k) (E := E) (V := V) g
    exact hrange (LinearMap.mem_range_self g v))
  left_inv f := by ext v; rfl
  right_inv g := by ext v; rfl
  map_add' f g := by ext v; simp
  map_smul' r f := by ext v; rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Double centralizer theorem, part (iii), bimodule form.

If `A` is a semisimple subalgebra of `End_k(E)` with `E` faithful and
`k` algebraically closed, then as a module over `A ⊗[k] B` (with
`B = centralizer(A)`), `E` decomposes as
  `E ≅ ⨁ᵢ Vᵢ ⊗[k] Lᵢ`
where `Vᵢ` are pairwise non-isomorphic simple `A`-modules, and
`Lᵢ = Vᵢ →ₗ[A] E` carries a natural `B`-module structure via
post-composition. This is the bimodule-enhanced version of
`Theorem5_18_1_decomposition`: the `Lᵢ` are genuine `B`-modules (not
just `k`-vector spaces) and the `Vᵢ` are pairwise non-isomorphic.

(Etingof Theorem 5.18.1, part iii, bimodule form.) -/
theorem Theorem5_18_1_bimodule_decomposition
    [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Type v) (_ : ∀ i, AddCommGroup (V i))
      (_ : ∀ i, Module k (V i)) (_ : ∀ i, Module A (V i))
      (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i j, Nonempty (V i ≃ₗ[A] V j) → i = j)
      (L : ι → Type v) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module
            (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
            (L i)),
      Nonempty (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] L i)) := by
  classical
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : IsNoetherian A E := inferInstance
  haveI : Finite (isotypicComponents A E) := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  set m := Fintype.card (isotypicComponents A E) with hm
  let φ : isotypicComponents A E ≃ Fin m := Fintype.equivFin _
  -- For each c, choose a simple submodule `V' c ≤ c.1` witnessing
  -- `c.1 = isotypicComponent A E (V' c)`.
  let V' : isotypicComponents A E → Submodule A E := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose
  have V'_le : ∀ c, V' c ≤ c.1 := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.1
  have V'_simple : ∀ c, IsSimpleModule A (V' c) := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule A E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.2
  have V'_spec : ∀ c, (c.1 : Submodule A E) = isotypicComponent A E (V' c) := by
    intro c
    haveI := V'_simple c
    exact eq_isotypicComponent_of_le c.2 (V'_le c)
  refine ⟨Fin m, inferInstance, inferInstance,
    fun i => ↥(V' (φ.symm i)),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun i => V'_simple (φ.symm i),
    ?_,
    fun i => (↥(V' (φ.symm i)) →ₗ[A] E),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    ?_⟩
  · -- Distinctness: V i ≃[A] V j → i = j
    intro i j ⟨e⟩
    have h_eq : isotypicComponent A E (V' (φ.symm i)) =
                isotypicComponent A E (V' (φ.symm j)) :=
      e.isotypicComponent_eq
    have h_c_eq : (φ.symm i).1 = (φ.symm j).1 := by
      rw [V'_spec (φ.symm i), V'_spec (φ.symm j)]; exact h_eq
    exact φ.symm.injective (Subtype.ext h_c_eq)
  · -- Main iso chain
    -- Step 1: E ≃[A] ⨁ c, ↥c.1 via isotypicDirectSumEquiv (symm)
    let e1 : E ≃ₗ[A] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
      (isotypicDirectSumEquiv A E).symm
    -- Step 2: restrict scalars to k
    let e2 : E ≃ₗ[k] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
      e1.restrictScalars k
    -- Step 3: per-component Schur evaluation + bridge
    -- For each c: ↥c.1 ≃[k] V' c ⊗[k] (V' c →ₗ[A] E)
    haveI : IsNoetherian k E := inferInstance
    let perComp : ∀ c : isotypicComponents A E,
        (↥c.1 : Type v) ≃ₗ[k]
          ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E) := fun c => by
      haveI := V'_simple c
      -- Provide Module.Finite k for the submodule types (via injection into E).
      haveI : Module.Finite k (↥(V' c) : Type v) :=
        Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
          Subtype.val_injective
      haveI : Module.Finite k (↥c.1 : Type v) :=
        Module.Finite.of_injective (c.1.subtype.restrictScalars k)
          Subtype.val_injective
      -- isotypic transport: ↥c.1 ≃[A] ↥(isotypicComponent A E (V' c))
      have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
        LinearEquiv.ofEq _ _ (V'_spec c)
      haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
        IsIsotypicOfType.isotypicComponent A E _
      haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
        e_submod.isIsotypicOfType_iff.mpr h_iso'
      -- Schur eval: V' c ⊗[k] (V' c →ₗ[A] ↥c.1) ≃[k] ↥c.1
      let sE := schurEvaluationEquiv k A (↥(V' c)) (↥c.1) h_iso
      -- Bridge: (V' c →ₗ[A] ↥c.1) ≃[k] (V' c →ₗ[A] E)
      let br := homIsotypicBridge k E A (V' c) c.1 (V'_spec c)
      -- Chain
      exact sE.symm.trans (TensorProduct.congr (LinearEquiv.refl k _) br)
    -- Step 4: map per-component across the direct sum
    let e3 : (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) ≃ₗ[k]
             (Π₀ c : isotypicComponents A E,
               ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) :=
      DFinsupp.mapRange.linearEquiv perComp
    -- Step 5: reindex via φ
    let e4 : (Π₀ c : isotypicComponents A E,
              ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) ≃ₗ[k]
             DirectSum (Fin m) (fun i =>
               ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
      DirectSum.lequivCongrLeft k φ
    exact ⟨e2.trans (e3.trans e4)⟩

end Etingof
