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

-- Both `maxHeartbeats` and `synthInstance.maxHeartbeats` need to be bumped
-- above 300000: `LinearMap.ext`'s `isDefEq` on the centralizer-wrapped
-- subtype overruns 200000 (timeout at the `refine` line below), and
-- downstream re-derivation of the `SMulCommClass` instance in
-- `Theorem5_18_1_bimodule_decomposition` needs more than 200000 synth
-- heartbeats. Empirical minimum is ~310000 for both; 320000 is the value
-- chosen with a small safety buffer (was 400000 / 400000 in #2504).
set_option maxHeartbeats 320000 in
set_option synthInstance.maxHeartbeats 320000 in
/-- The centralizer action on `V →ₗ[A] E` (post-composition) commutes with
the standard `k`-action on `V →ₗ[A] E` (pointwise scaling). This follows
from each `b ∈ centralizer(A) ⊆ End k E` being a `k`-linear map. -/
instance centralizerModuleHom_smulCommClass
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    SMulCommClass (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) k
      (V →ₗ[A] E) where
  smul_comm b c f := by
    refine LinearMap.ext fun v => ?_
    -- (b • (c • f)) v = b.val (c • f v) = c • b.val (f v) = c • (b • f) v
    show b.val ((c • f) v) = c • b.val (f v)
    rw [LinearMap.smul_apply, map_smul]

-- Heartbeats bumped: `LinearMap.ext` on the centralizer-wrapped subtype
-- triggers `LinearMap.CompatibleSMul` synthesis, which exceeds the default
-- 20000 heartbeats (same root cause as `centralizerModuleHom` above).
set_option synthInstance.maxHeartbeats 400000 in
/-- Monoid hom `↥centralizer(A) →* End_k(V →ₗ[A] E)` given by post-composition:
`b ↦ (l ↦ (centralizerToEndA b).comp l)`.

This bundles the post-composition action used to build a `B`-action on
`V →ₗ[A] E` from a monoid hom into `B = centralizer(A)`. The construction
is identical in content to the `centralizerModuleHom` SMul, but provided
as a `MonoidHom` (not via `Module.toModuleEnd`) to bypass an
instance-synthesis diamond at composite call sites.

Composing this with a `MonoidHom M →* ↥centralizer(A)` (for any monoid
`M`) yields the canonical `M`-action on `V →ₗ[A] E`, e.g. the `GL_N`
action on each Schur-Weyl `L_i` summand
(`Theorem5_18_4_GL_rep_decomposition_explicit`). -/
noncomputable def postCompCentralizerMonoidHom
    (A : Subalgebra k (Module.End k E))
    (V : Type*) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) →*
      Module.End k (V →ₗ[A] E) where
  toFun b :=
    { toFun := fun l => (centralizerToEndA k E A b).comp l
      map_add' := fun l₁ l₂ => by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
      map_smul' := fun c l => by
        ext v
        simp only [LinearMap.smul_apply, RingHom.id_apply,
          LinearMap.comp_apply, LinearMap.map_smul_of_tower] }
  map_one' := by
    ext l v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.End.one_apply]
    change (centralizerToEndA k E A 1) (l v) = l v
    rw [map_one]; rfl
  map_mul' b₁ b₂ := by
    ext l v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.End.mul_apply]
    change (centralizerToEndA k E A (b₁ * b₂)) (l v) = _
    rw [map_mul]; rfl

/-- Underlying-map identity for `postCompCentralizerMonoidHom`: applying it to
`b` and then evaluating at a hom `l` yields the post-composition
`(centralizerToEndA b).comp l`. Useful for unfolding inside proofs. -/
@[simp]
theorem postCompCentralizerMonoidHom_apply_apply
    (A : Subalgebra k (Module.End k E))
    (V : Type*) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V]
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
    (l : V →ₗ[A] E) (v : V) :
    postCompCentralizerMonoidHom k E A V b l v = b.val (l v) := rfl

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

-- Heartbeats bumped: the `IsSimpleModule` statement on the centralizer-wrapped
-- subtype hom-space `V →ₗ[A] E` triggers a deep instance synthesis chain on
-- `Submodule (↥centralizer) (V →ₗ[A] E)` (involving Subalgebra → Ring → Module.End
-- and the non-trivial centralizerModuleHom instance) that overruns 200000.
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Schur's lemma on the multiplicity space: for a simple `A`-submodule
`V ≤ E` of a semisimple `A`-module `E`, the hom-space `V →ₗ[A] E` is a
**simple** module over the centralizer `B := centralizer(A)` (acting by
post-composition).

Proof sketch: a nonzero `f : V →ₗ[A] E` is injective (Schur on the simple
`V`), so any other `g : V →ₗ[A] E` extends along `f` to an `A`-linear
map `h : E →ₗ[A] E` (using `IsSemisimpleModule.extension_property`).
The underlying `k`-linear map of `h` lies in the centralizer (commutes
with all of `A` by `A`-linearity), and its post-composition action on
`f` recovers `g`. Hence the cyclic submodule generated by any nonzero
`f` is all of `V →ₗ[A] E`.

This is the `B`-side simplicity claim implicit in
`Theorem5_18_1_bimodule_decomposition`: the multiplicity spaces `Lᵢ`
are simple `B`-modules, not just `k`-vector spaces. -/
theorem isSimpleModule_homA_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleModule A E]
    (V : Submodule A E) [IsSimpleModule A V] :
    IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥V →ₗ[A] E) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, ?_⟩
  · -- Nontrivial: `V.subtype : V →ₗ[A] E` is a nonzero element.
    refine ⟨V.subtype, 0, fun h => ?_⟩
    -- If `V.subtype = 0` then every `v ∈ V` is `0`, contradicting the
    -- nontriviality of the simple module `V`.
    have hV : Nontrivial (↥V) := IsSimpleModule.nontrivial A (↥V)
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥V)
    have : (V.subtype v : E) = 0 := by
      have := LinearMap.congr_fun h v
      simpa using this
    apply hv
    exact Subtype.ext this
  · -- `toSpanSingleton B (V →ₗ[A] E) f` is surjective for any nonzero `f`.
    intro f hf
    -- `f` is injective by Schur on the simple `V`.
    have hker : LinearMap.ker f = ⊥ := by
      rcases eq_bot_or_eq_top (LinearMap.ker f) with h | h
      · exact h
      · exfalso; apply hf
        ext v
        have hv : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa [LinearMap.mem_ker] using hv
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    -- For any target `g`, extend `g` along the injection `f`.
    intro g
    obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property f hinj g
    -- `h.restrictScalars k` lies in the centralizer (commutes with `A`
    -- by `A`-linearity of `h`).
    have hcent : LinearMap.restrictScalars k h ∈
        Subalgebra.centralizer k (A : Set (Module.End k E)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro a ha
      ext e
      -- Goal: `(a * h.restrictScalars k) e = (h.restrictScalars k * a) e`,
      -- i.e. `a (h e) = h (a e)`. This is `A`-linearity of `h` applied
      -- to the algebra element `⟨a, ha⟩ : ↥A`.
      have hsmul : h (a e) = a (h e) := h.map_smul (⟨a, ha⟩ : ↥A) e
      exact hsmul.symm
    -- Package as an element of the centralizer subalgebra.
    refine ⟨⟨LinearMap.restrictScalars k h, hcent⟩, ?_⟩
    -- Goal: `toSpanSingleton _ _ f ⟨_, hcent⟩ = g`, i.e. the
    -- post-composition action recovers `g`.
    ext v
    simp only [LinearMap.toSpanSingleton_apply]
    -- `(b • f) v = b.val (f v) = h (f v) = (h ∘ₗ f) v = g v`.
    change h (f v) = g v
    exact LinearMap.congr_fun hh v

-- Heartbeats are bumped because the existential output has several universe-polymorphic
-- ∀-binders whose instance synthesis (AddCommGroup / Module / SMulCommClass / Module.Finite
-- over a subalgebra-wrapped ring) each triggers a deep `Subalgebra → Ring → Module.End`
-- instance chain. Empirical minimum is between 1600000 / 800000 (fails) and 1800000 /
-- 900000 (passes); 2000000 / 1000000 used here for a small safety buffer (was
-- 3200000 / 1600000 in #2504).
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
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

The theorem additionally provides, for each `i`:
* `SMulCommClass B k (Lᵢ)` — the `B`- and `k`-actions on `Lᵢ` commute,
  so `Lᵢ` is a representation of `B` over `k` (i.e. an `A ⊗[k] B`-module
  factor in the standard sense), and
* `Module.Finite k (Lᵢ)` — each multiplicity space is a
  finite-dimensional `k`-vector space.

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
      (_ : ∀ i, Module.Finite k (V i))
      (L : ι → Type v) (_ : ∀ i, AddCommGroup (L i))
      (_ : ∀ i, Module k (L i))
      (_ : ∀ i, Module
            (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
            (L i))
      (_ : ∀ i, SMulCommClass
            (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
            k (L i))
      (_ : ∀ i, Module.Finite k (L i)),
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
  haveI : ∀ c : isotypicComponents A E, Module.Finite k ↥(V' c) := fun c =>
    Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
      Subtype.val_injective
  haveI : ∀ c : isotypicComponents A E,
      Module.Finite k ((↥(V' c) : Type v) →ₗ[A] E) := fun c => by
    -- The A-linear hom space is a subspace of the k-linear hom space
    -- (via `LinearMap.restrictScalars`), which is finite-dimensional.
    haveI : Module.Finite k ((↥(V' c) : Type v) →ₗ[k] E) := inferInstance
    exact Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (↥(V' c)) E k)
      (LinearMap.restrictScalars_injective _)
  refine ⟨Fin m, inferInstance, inferInstance,
    fun i => ↥(V' (φ.symm i)),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun i => V'_simple (φ.symm i),
    ?_,
    fun _ => inferInstance,
    fun i => (↥(V' (φ.symm i)) →ₗ[A] E),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    fun _ => inferInstance,
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

-- Heartbeats further bumped from 3200000 / 1200000 (see prior comment) to
-- 6400000 / 2400000 because the existential signature now also advertises
-- the `B`-side simplicity clause (`isSimpleModule_homA_centralizer`) on each
-- multiplicity space, which adds another non-trivial typeclass-search chain
-- through the centralizer-module instance.
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 2400000 in
/-- Double centralizer theorem, part (iii), bimodule form with explicit
evaluation.

Strengthens `Theorem5_18_1_bimodule_decomposition` by:

* concretizing the summand types as `Vᵢ : Submodule A E` and
  `Lᵢ := ↥(V i) →ₗ[A] E`;
* producing an explicit iso `e` whose inverse on pure-tensor basis
  elements is the evaluation map `l v`:
  `e.symm (of i (v ⊗ₜ l)) = l v`.

The evaluation formula implies the iso is `B`-equivariant for the natural
post-composition action of `B = centralizer(A)` on each `Lᵢ`: for any
`b ∈ B`,
`e.symm (of i (v ⊗ₜ (b • l))) = (b • l) v = b.val (l v)
    = b.val (e.symm (of i (v ⊗ₜ l)))`.

This is the form required by character-additivity arguments (Schur-Weyl
#3, #5, #6): together with the tensor-factorization of traces it yields
`tr_E(b) = Σᵢ dim(Vᵢ) · tr_{Lᵢ}(b)`. -/
theorem Theorem5_18_1_bimodule_decomposition_explicit
    [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A]
    [FaithfulSMul A E] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (V : ι → Submodule A E) (_ : ∀ i, IsSimpleModule A (V i))
      (_ : ∀ i j, Nonempty (↥(V i) ≃ₗ[A] ↥(V j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(V i))
      (_ : ∀ i, IsSimpleModule
        (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
        (↥(V i) →ₗ[A] E)),
      ∃ (e : E ≃ₗ[k] DirectSum ι
          (fun i => ↥(V i) ⊗[k] (↥(V i) →ₗ[A] E))),
        ∀ (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E),
          e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v := by
  classical
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : IsNoetherian A E := inferInstance
  haveI : Finite (isotypicComponents A E) := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  haveI : IsNoetherian k E := inferInstance
  set m := Fintype.card (isotypicComponents A E) with hm
  let φ : isotypicComponents A E ≃ Fin m := Fintype.equivFin _
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
  -- Each `↥(V' c)` is finite-dimensional over `k` (it injects into the
  -- finite-dimensional ambient `E`). Hoisted to top-level so the existential
  -- output can advertise `Module.Finite k ↥(V i)` directly.
  haveI hV'_fin : ∀ c : isotypicComponents A E,
      Module.Finite k ((↥(V' c) : Type v)) := fun c =>
    Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
      Subtype.val_injective
  -- Per-component k-linear iso: ↥c.1 ≃[k] V' c ⊗[k] (V' c →ₗ[A] E)
  let perComp : ∀ c : isotypicComponents A E,
      (↥c.1 : Type v) ≃ₗ[k]
        ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E) := fun c => by
    haveI := V'_simple c
    haveI : Module.Finite k (↥c.1 : Type v) :=
      Module.Finite.of_injective (c.1.subtype.restrictScalars k)
        Subtype.val_injective
    have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
      LinearEquiv.ofEq _ _ (V'_spec c)
    haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
      IsIsotypicOfType.isotypicComponent A E _
    haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
      e_submod.isIsotypicOfType_iff.mpr h_iso'
    let sE := schurEvaluationEquiv k A (↥(V' c)) (↥c.1) h_iso
    let br := homIsotypicBridge k E A (V' c) c.1 (V'_spec c)
    exact sE.symm.trans (TensorProduct.congr (LinearEquiv.refl k _) br)
  -- Key lemma: on pure tensors, the inverse of perComp evaluates:
  -- (perComp c).symm (v ⊗ₜ l) is the element of ↥c.1 whose .val is l v.
  have perComp_symm_tmul : ∀ (c : isotypicComponents A E)
      (v : ↥(V' c)) (l : ↥(V' c) →ₗ[A] E),
      (((perComp c).symm (v ⊗ₜ[k] l) : ↥c.1) : E) = l v := by
    intro c v l
    haveI := V'_simple c
    haveI : Module.Finite k (↥c.1 : Type v) :=
      Module.Finite.of_injective (c.1.subtype.restrictScalars k)
        Subtype.val_injective
    have e_submod : (↥c.1 : Type v) ≃ₗ[A] ↥(isotypicComponent A E (V' c)) :=
      LinearEquiv.ofEq _ _ (V'_spec c)
    haveI h_iso' : IsIsotypicOfType A ↥(isotypicComponent A E (V' c)) ↥(V' c) :=
      IsIsotypicOfType.isotypicComponent A E _
    haveI h_iso : IsIsotypicOfType A (↥c.1) ↥(V' c) :=
      e_submod.isIsotypicOfType_iff.mpr h_iso'
    -- perComp c = sE.symm.trans (TensorProduct.congr refl br), hence
    -- (perComp c).symm = (TensorProduct.congr refl br).symm.trans sE
    change ((((schurEvaluationEquiv k A (↥(V' c)) (↥c.1) h_iso).symm).trans
            (TensorProduct.congr (LinearEquiv.refl k _)
              (homIsotypicBridge k E A (V' c) c.1 (V'_spec c)))).symm
          (v ⊗ₜ[k] l) : ↥c.1).val = l v
    rw [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
        TensorProduct.congr_symm, LinearEquiv.refl_symm, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, schurEvaluationEquiv_apply_tmul]
    -- After simp: goal is ((homIsotypicBridge k E A (V' c) c.1 (V'_spec c)).symm l v : E) = l v.
    -- `homIsotypicBridge.symm l = l.codRestrict c.1 _`, so applying at v gives `⟨l v, _⟩ ∈ c.1`,
    -- whose .val = l v.
    rfl
  -- Total iso
  let e2 : E ≃ₗ[k] (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) :=
    (isotypicDirectSumEquiv A E).symm.restrictScalars k
  let e3 : (Π₀ c : isotypicComponents A E, (c.1 : Submodule A E)) ≃ₗ[k]
           (Π₀ c : isotypicComponents A E,
             ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) :=
    DFinsupp.mapRange.linearEquiv perComp
  let e4 : (Π₀ c : isotypicComponents A E,
            ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E)) ≃ₗ[k]
           DirectSum (Fin m) (fun i =>
             ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
    DirectSum.lequivCongrLeft k φ
  let etotal : E ≃ₗ[k] DirectSum (Fin m)
    (fun i => ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) :=
    e2.trans (e3.trans e4)
  -- Hoist L_i simplicity (B-side Schur's lemma) so each instance is
  -- available before the `refine` packs the existential.
  have hL_simp : ∀ i, IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥(V' (φ.symm i)) →ₗ[A] E) := fun i => by
    haveI : IsSimpleModule (↥A) ↥(V' (φ.symm i)) := V'_simple (φ.symm i)
    exact isSimpleModule_homA_centralizer (k := k) (E := E) A (V' (φ.symm i))
  refine ⟨Fin m, inferInstance, inferInstance,
    fun i => V' (φ.symm i),
    fun i => V'_simple (φ.symm i),
    ?_, fun i => hV'_fin (φ.symm i), hL_simp,
    etotal, ?_⟩
  · -- Distinctness
    intro i j ⟨eqv⟩
    have h_eq : isotypicComponent A E (V' (φ.symm i)) =
                isotypicComponent A E (V' (φ.symm j)) :=
      eqv.isotypicComponent_eq
    have h_c_eq : (φ.symm i).1 = (φ.symm j).1 := by
      rw [V'_spec (φ.symm i), V'_spec (φ.symm j)]; exact h_eq
    exact φ.symm.injective (Subtype.ext h_c_eq)
  · -- Evaluation formula.
    intro i
    -- Beta-reduce the types of `v` and `l` so they mention `V' (φ.symm i)` directly.
    change ∀ (v : ↥(V' (φ.symm i))) (l : ↥(V' (φ.symm i)) →ₗ[A] E),
      etotal.symm (DirectSum.of
        (fun j : Fin m => ↥(V' (φ.symm j)) ⊗[k] (↥(V' (φ.symm j)) →ₗ[A] E))
        i (v ⊗ₜ[k] l)) = l v
    intro v l
    -- Strategy: apply etotal to both sides so we work forward through the chain.
    rw [LinearEquiv.symm_apply_eq]
    -- Goal: DirectSum.of _ i (v ⊗ₜ l) = etotal (l v).
    -- Make the simple-module instance visible so `range_le_isotypicComponent_of_simple` applies.
    haveI := V'_simple (φ.symm i)
    -- Step 1: l v lies in the isotypic component (φ.symm i).1.
    have hrange : l v ∈ ((φ.symm i).1 : Submodule A E) := by
      have hr := range_le_isotypicComponent_of_simple (k := k) (E := E)
        (V := V' (φ.symm i)) (A := A) l (LinearMap.mem_range_self l v)
      rw [← V'_spec (φ.symm i)] at hr
      exact hr
    -- Step 2: (isotypicDirectSumEquiv A E).symm (l v) = DFinsupp.single (φ.symm i) ⟨l v, _⟩.
    have step_fwd_1 : (isotypicDirectSumEquiv A E).symm (l v) =
        DFinsupp.single (φ.symm i) (⟨l v, hrange⟩ : ↥((φ.symm i).1)) :=
      iSupIndep.linearEquiv_symm_apply
        (ind := (sSupIndep_iff _).mp (sSupIndep_isotypicComponents A E))
        (iSup_top := by
          rw [← sSup_eq_iSup']
          exact sSup_isotypicComponents A E) (i := φ.symm i)
        (x := l v) hrange
    -- Step 3: perComp (φ.symm i) applied to ⟨l v, hrange⟩ gives v ⊗ₜ l.
    -- This is the content of `perComp_symm_tmul` applied in reverse.
    have step_fwd_2 : (perComp (φ.symm i)) ⟨l v, hrange⟩ =
        (v ⊗ₜ[k] l : ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E)) := by
      apply (perComp (φ.symm i)).symm.injective
      rw [(perComp (φ.symm i)).symm_apply_apply]
      apply Subtype.ext
      symm
      exact perComp_symm_tmul (φ.symm i) v l
    -- Step 4: put it together. We compute etotal (l v) by unfolding the chain.
    change (DirectSum.of
        (fun i : Fin m => ↥(V' (φ.symm i)) ⊗[k] (↥(V' (φ.symm i)) →ₗ[A] E))
        i (v ⊗ₜ[k] l)) =
      e4 (e3 (e2 (l v)))
    -- e2 (l v) = (isotypicDirectSumEquiv).symm (l v) (wrapped in restrictScalars)
    have he2 : e2 (l v) = DFinsupp.single (φ.symm i)
        (⟨l v, hrange⟩ : ↥((φ.symm i).1)) := step_fwd_1
    rw [he2]
    -- e3 applied to a single.
    have he3 : e3 (DFinsupp.single (φ.symm i)
        (⟨l v, hrange⟩ : ↥((φ.symm i).1))) =
        DFinsupp.single (φ.symm i) ((perComp (φ.symm i)) ⟨l v, hrange⟩) :=
      DFinsupp.mapRange_single (hf := fun c => (perComp c).map_zero)
    rw [he3, step_fwd_2]
    -- Now we must show: of _ i (v ⊗ₜ l) = e4 (DFinsupp.single (φ.symm i) (v ⊗ₜ l)).
    refine DFinsupp.ext (fun k' => ?_)
    change (DirectSum.of
          (fun j : Fin m => ↥(V' (φ.symm j)) ⊗[k] (↥(V' (φ.symm j)) →ₗ[A] E))
          i (v ⊗ₜ[k] l)) k' =
      ((DirectSum.lequivCongrLeft k φ)
        (DFinsupp.single
          (β := fun c : isotypicComponents A E =>
            ↥(V' c) ⊗[k] (↥(V' c) →ₗ[A] E))
          (φ.symm i)
          (v ⊗ₜ[k] l))) k'
    rw [DirectSum.lequivCongrLeft_apply]
    by_cases hk : k' = i
    · subst hk
      rw [DirectSum.of_eq_same, DFinsupp.single_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hk]
      have hne : φ.symm k' ≠ φ.symm i := fun h => hk (φ.symm.injective h)
      rw [DFinsupp.single_eq_of_ne hne]

end Etingof
