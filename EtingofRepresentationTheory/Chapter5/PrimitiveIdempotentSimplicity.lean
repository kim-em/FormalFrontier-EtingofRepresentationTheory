import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_1

/-!
# Image of a primitive idempotent is simple over the centralizer

Let `A ⊆ End_k E` be a subalgebra, `B = centralizer(A)`, and `c ∈ A` with
`c² = α • c` for some `α ≠ 0` (so `e := α⁻¹ • c` is a true idempotent).
Suppose the action of `c` on the bimodule decomposition
`E ≃[k] ⨁ᵢ ↥(S i) ⊗ L i` (with `L i := ↥(S i) →ₗ[A] E`) factors per-block
as `(f i) ⊗ id`, with `f i = 0` for all blocks except a unique `iLam`,
and `f iLam = α • π` for a rank-1 projection `π`.

Then the image `LinearMap.range c.val` is a simple `B`-module, isomorphic
to `L iLam`.

This is the abstract algebraic step (C-4a-ii) of the Schur-Weyl `L_i`
simplicity proof. The hypothesis package matches the conclusions of:
* sub-α (`youngSym_block_factorization`, #2655) — block factorization,
* sub-β (off-block vanishing, #2656),
* sub-γ (rank-1 scaled projection on the special block, #2657).

When all three are composed with this theorem, one obtains
`IsSimpleModule B (range c.val)` purely from semisimple bimodule
structure, character orthogonality, and the rank-1 hypothesis.
-/

open scoped TensorProduct

universe u v

namespace Etingof

/-! ## Helper: rank-1 idempotent has a fixed basis vector -/

/-- A rank-1 idempotent `π : V →ₗ[k] V` admits a nonzero `v₀` with
`π v₀ = v₀` (necessarily a basis of `range π`). -/
lemma rank_one_idempotent_basis_vec
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (π : V →ₗ[k] V) (hπ_idem : π * π = π)
    (hπ_rank : Module.finrank k (LinearMap.range π) = 1) :
    ∃ v₀ : V, v₀ ≠ 0 ∧ π v₀ = v₀ ∧
      LinearMap.range π = Submodule.span k {v₀} := by
  classical
  -- The range is a 1-dim k-submodule; `Module.Finite k ↥(range π)` follows
  -- from `finrank_eq_one`.
  haveI : Module.Finite k (LinearMap.range π) :=
    Module.finite_of_finrank_pos (by rw [hπ_rank]; exact Nat.one_pos)
  -- Pick a basis of `range π` of length 1.
  let b : Module.Basis (Fin 1) k (LinearMap.range π) :=
    Module.finBasisOfFinrankEq k _ hπ_rank
  refine ⟨(b 0 : V), ?_, ?_, ?_⟩
  · -- v₀ ≠ 0
    intro h
    have : (b 0 : LinearMap.range π) = 0 := Subtype.ext h
    exact b.ne_zero 0 this
  · -- π v₀ = v₀: uses idempotence and `v₀ ∈ range π`.
    have hv0 : (b 0 : V) ∈ LinearMap.range π := (b 0).property
    obtain ⟨w, hw⟩ := hv0
    rw [← hw]
    exact LinearMap.congr_fun hπ_idem w
  · -- range π = span k {v₀}: range π is 1-dimensional with basis b 0, so its
    -- span (in V) equals the singleton span.
    have hb_span : (Submodule.span k ({(b 0 : LinearMap.range π)} :
        Set (LinearMap.range π))) = ⊤ := by
      rw [← b.span_eq]
      congr; ext x
      simp [Set.range_unique]
    -- Transfer to V via the inclusion.
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      have hxr : (⟨π y, ⟨y, rfl⟩⟩ : LinearMap.range π) ∈
          (Submodule.span k ({(b 0 : LinearMap.range π)} :
            Set (LinearMap.range π))) := by
        rw [hb_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_singleton] at hxr
      obtain ⟨c, hc⟩ := hxr
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      have hval := congrArg ((↑) : LinearMap.range π → V) hc
      simp only [SetLike.val_smul] at hval
      rw [hval, hy]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (b 0).property

/-! ## Helper: tensor product factorization through a 1-dim factor -/

/-- For `π : V →ₗ[k] V` whose range is `span k {v₀}`, every element in the
image of `π ⊗ id : V ⊗ L → V ⊗ L` factors as `v₀ ⊗ l₀` for some `l₀ : L`. -/
lemma tensor_through_rank_one
    {k : Type*} [Field k] {V L : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup L] [Module k L]
    (π : V →ₗ[k] V) (v₀ : V)
    (hv₀ : LinearMap.range π = Submodule.span k {v₀})
    (ξ : V ⊗[k] L) :
    ∃ l₀ : L, (TensorProduct.map π LinearMap.id) ξ = v₀ ⊗ₜ[k] l₀ := by
  classical
  induction ξ using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v l =>
    have hπv : π v ∈ Submodule.span k ({v₀} : Set V) := by
      rw [← hv₀]; exact LinearMap.mem_range_self π v
    rw [Submodule.mem_span_singleton] at hπv
    obtain ⟨c, hc⟩ := hπv
    refine ⟨c • l, ?_⟩
    rw [TensorProduct.map_tmul, LinearMap.id_apply, ← hc, TensorProduct.smul_tmul]
  | add ξ₁ ξ₂ ih₁ ih₂ =>
    obtain ⟨l₁, h₁⟩ := ih₁
    obtain ⟨l₂, h₂⟩ := ih₂
    refine ⟨l₁ + l₂, ?_⟩
    rw [map_add, h₁, h₂, ← TensorProduct.tmul_add]

/-! ## Helper: extending a per-block hypothesis to all of a block -/

-- Heartbeats bumped: the goal mentions `↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)` whose
-- `Module k` / `Zero` / `Add` instance synthesis traverses
-- `Subalgebra → Subsemiring → Submodule → Module` chains and overruns the
-- default 20000 / 200000 budget. The `add` case of the induction triggers
-- `Add (DirectSum ι _)` synthesis which is particularly expensive.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- The per-pure-tensor block factorization `c.val ∘ e.symm ∘ of i =
of i ∘ (f i ⊗ id)` extends k-linearly to all of `↥(S i) ⊗ L i`.

Proven by induction on the tensor: both sides agree on `0`, on pure tensors
(by `hf_block`), and respect addition. -/
lemma block_factorization_extended
    {k : Type u} [Field k]
    {E : Type v} [AddCommGroup E] [Module k E]
    {A : Subalgebra k (Module.End k E)}
    (c : ↥A)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule A E)
    (e : E ≃ₗ[k] DirectSum ι (fun i =>
      ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)))
    (f : ∀ i, ↥(S i) →ₗ[k] ↥(S i))
    (hf_block : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e (c.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[k] l))
    (i : ι) (ξ : ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)) :
    e (c.val (e.symm (DirectSum.of _ i ξ))) =
      DirectSum.of _ i (TensorProduct.map (f i) LinearMap.id ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul v l =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hf_block i v l]
  | add ξ₁ ξ₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

/-! ## Lifting `c.val` to a `B`-linear endomorphism -/

variable {k : Type u} [Field k]
variable {E : Type v} [AddCommGroup E] [Module k E]
variable {A : Subalgebra k (Module.End k E)}

/-- Any `c ∈ A`, as an element of `End_k E`, commutes with every `b` in the
centralizer `B = centralizer(A)`. -/
lemma cval_commute_centralizer (c : ↥A)
    (b : ↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :
    c.val * b.val = b.val * c.val := by
  have hb := b.property
  rw [Subalgebra.mem_centralizer_iff] at hb
  exact hb _ c.property

/-- An element `c ∈ A` viewed as a `B`-linear endomorphism of `E`. -/
noncomputable def cBLinear (c : ↥A) :
    E →ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] E where
  toFun := c.val
  map_add' := c.val.map_add
  map_smul' b x := by
    -- Goal: c.val (b • x) = b • c.val x. Both sides reduce by `Subalgebra.smul_def`.
    change c.val (b.val x) = b.val (c.val x)
    -- `cval_commute_centralizer c b : c.val * b.val = b.val * c.val`,
    -- and `(f * g) x = f (g x)` for End_k E.
    exact LinearMap.congr_fun (cval_commute_centralizer c b) x

@[simp]
lemma cBLinear_apply (c : ↥A) (x : E) : cBLinear c x = c.val x := rfl

/-- The image of `c.val : E →ₗ[k] E` packaged as a `B`-submodule. The carrier
equals `LinearMap.range c.val` (as a `Submodule k E`). -/
noncomputable def imageSubmoduleB (c : ↥A) :
    Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E :=
  LinearMap.range (cBLinear c)

@[simp]
lemma mem_imageSubmoduleB (c : ↥A) (x : E) :
    x ∈ imageSubmoduleB c ↔ x ∈ LinearMap.range (c.val : Module.End k E) := by
  simp [imageSubmoduleB, LinearMap.mem_range, cBLinear]

/-! ## Main theorem -/

variable [Module.Finite k E]

-- Heartbeats bumped: the existential signature mentions
-- `↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)` plus the centralizer-`Module` chain on
-- `imageSubmoduleB c`. Each instance synthesis traverses a deep
-- `Subalgebra → Subsemiring → Submodule → Module` chain, overrunning the
-- defaults at the type-checking phase.
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Image of a primitive idempotent is simple over the centralizer.**

Setup: `A ⊆ End_k E` a subalgebra, `B = centralizer(A)`, `c ∈ A` with
`c² = α • c` and `α ≠ 0`. Given a `k`-linear bimodule decomposition
`e : E ≃ ⨁ᵢ ↥(S i) ⊗[k] L i` with the evaluation formula
`e.symm (of i (v ⊗ₜ l)) = l v`, suppose the action of `c` factors per-block
as `(f i) ⊗ id_{L i}`, with `f i = 0` for `i ≠ iLam` and
`f iLam = α • π` for a rank-1 idempotent `π`.

Then the image `LinearMap.range c.val` is simple as a `B`-module.

The conclusion is packaged as `IsSimpleModule ↥B ↥(imageSubmoduleB c)` —
the underlying carrier of `imageSubmoduleB c` equals `range c.val`
(`mem_imageSubmoduleB`). -/
theorem image_of_primitive_idempotent_isSimple_centralizer
    [IsSemisimpleModule A E]
    (c : ↥A) (α : k) (hα : α ≠ 0) (_hc_sq : c * c = α • c)
    {ι : Type} [DecidableEq ι]
    (S : ι → Submodule A E)
    (e : E ≃ₗ[k] DirectSum ι (fun i =>
      ↥(S i) ⊗[k] (↥(S i) →ₗ[A] E)))
    (he_eval : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v)
    (iLam : ι) (hSiLam_simple : IsSimpleModule A ↥(S iLam))
    (f : ∀ i, ↥(S i) →ₗ[k] ↥(S i))
    (hf_block : ∀ (i : ι) (v : ↥(S i)) (l : ↥(S i) →ₗ[A] E),
      e (c.val (e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)))) =
        DirectSum.of _ i (f i v ⊗ₜ[k] l))
    (hf_zero : ∀ i, i ≠ iLam → f i = 0)
    (π : ↥(S iLam) →ₗ[k] ↥(S iLam))
    (hπ_idem : π * π = π)
    (hπ_rank : Module.finrank k (LinearMap.range π) = 1)
    (hπ_special : f iLam = α • π) :
    IsSimpleModule
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      ↥(imageSubmoduleB c) := by
  -- Proof outline (deferred to follow-up issue):
  --
  -- 1. Extract `v₀ ∈ ↥(S iLam)` with `v₀ ≠ 0`, `π v₀ = v₀`,
  --    `range π = span k {v₀}` via `rank_one_idempotent_basis_vec`.
  -- 2. Define `Φ : (↥(S iLam) →ₗ[A] E) →ₗ[k] E` by `Φ l := l v₀`.
  -- 3. Show `Φ` is `B`-equivariant: `Φ (b • l) = b.val (Φ l)`
  --    (via `centralizerModuleHom`'s SMul = post-composition).
  -- 4. Show `Φ l ∈ imageSubmoduleB c` for all `l`: compute
  --    `c.val (l v₀) = α • l v₀` by combining `he_eval`, `hf_block iLam v₀ l`,
  --    `hπ_special`, and `hπv₀`. Then `l v₀ = c.val (α⁻¹ • l v₀)`.
  -- 5. Show every `c.val y ∈ imageSubmoduleB c` lies in `range Φ`:
  --    decompose `e y = ∑ᵢ of i ((e y) i)`, push `c.val` through using
  --    `block_factorization_extended` and `hf_zero`, leaving only the
  --    `iLam` summand `of iLam ((α • π ⊗ id) ((e y) iLam))`. Apply
  --    `tensor_through_rank_one` to factor this as `of iLam (v₀ ⊗ (α • l₀))`,
  --    then `e.symm` to recover `c.val y = (α • l₀) v₀ = Φ (α • l₀)`.
  -- 6. Show `Φ` is injective: `Φ l = 0 ⇒ l v₀ = 0`; since `↥(S iLam)` is
  --    a simple `A`-module, `ker l ∈ {⊥, ⊤}`; `v₀ ≠ 0 ∧ v₀ ∈ ker l`
  --    forces `ker l = ⊤`, i.e. `l = 0`.
  -- 7. Build `Φ' : (↥(S iLam) →ₗ[A] E) →ₗ[B] ↥(imageSubmoduleB c)` by
  --    co-restricting `Φ` to its image, then `Ψ := LinearEquiv.ofBijective`.
  -- 8. Conclude via `IsSimpleModule.congr Ψ.symm` and
  --    `isSimpleModule_homA_centralizer A (S iLam)`.
  --
  -- Status: a full draft of the body was attempted in this PR but failed
  -- on a typeclass-instance diamond — the local `haveI : Module ↥B
  -- (↥(S iLam) →ₗ[A] E)` is not def-equal to the global
  -- `centralizerModuleHom` instance returned by
  -- `isSimpleModule_homA_centralizer`, and removing the `haveI` causes
  -- auto-synthesis of the same instance to time out at >4M heartbeats.
  -- The full WIP body is preserved as a `/- ... -/` block below.
  sorry

/-
WIP body of `image_of_primitive_idempotent_isSimple_centralizer`. Compiles
the structural steps but blocked on the `Module ↥B (↥(S iLam) →ₗ[A] E)`
instance-diamond described in the comment above. Follow-up issue should:
* Either expose `centralizerModuleHom` more carefully (e.g. as a non-class
  `def` returning a `Module` value, then `letI` it in once at the top),
* Or refactor `isSimpleModule_homA_centralizer` to not infer the Module
  instance (taking it as an explicit hypothesis).

```
classical
haveI hSiLam_simple' : IsSimpleModule (↥A) ↥(S iLam) := hSiLam_simple
haveI : IsSimpleOrder (Submodule (↥A) ↥(S iLam)) :=
  hSiLam_simple'.toIsSimpleOrder
set β : ι → Type _ :=
  fun j => ↥(S j) ⊗[k] (↥(S j) →ₗ[A] E) with hβ
have hπ_rank' : Module.finrank k (LinearMap.range π) = 1 := hπ_rank
obtain ⟨v₀, hv₀_ne, hπv₀, hrange_π⟩ :=
  rank_one_idempotent_basis_vec (k := k) (V := ↥(S iLam))
    π hπ_idem hπ_rank'
let Φ : (↥(S iLam) →ₗ[A] E) →ₗ[k] E :=
  { toFun := fun l => l v₀
    map_add' := fun l₁ l₂ => by simp
    map_smul' := fun r l => by simp }
have hΦ_equiv : ∀ b : ↥(Subalgebra.centralizer k
    (A : Set (Module.End k E))), ∀ l, Φ (b • l) = b.val (Φ l) := by
  intro b l
  change (b • l) v₀ = b.val (l v₀)
  rfl
have hΦ_in_range : ∀ l : ↥(S iLam) →ₗ[A] E, Φ l ∈ imageSubmoduleB c := by
  intro l
  rw [mem_imageSubmoduleB]
  refine ⟨α⁻¹ • l v₀, ?_⟩
  rw [c.val.map_smul]
  have hlv0 : l v₀ = e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)) := by
    rw [he_eval]
  have hcomp : c.val (l v₀) = α • l v₀ := by
    rw [hlv0]
    have happly_e : e (c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)))) =
        DirectSum.of β iLam (f iLam v₀ ⊗ₜ[k] l) := hf_block iLam v₀ l
    have hα_block : e (c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)))) =
        α • DirectSum.of β iLam (v₀ ⊗ₜ[k] l) := by
      rw [happly_e, hπ_special, LinearMap.smul_apply, hπv₀,
        ← TensorProduct.smul_tmul', map_smul]
    have happly_e_symm : c.val (e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l))) =
        α • e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] l)) := by
      have h := congrArg e.symm hα_block
      rw [LinearEquiv.symm_apply_apply,
        e.symm.map_smul α (DirectSum.of β iLam (v₀ ⊗ₜ[k] l))] at h
      exact h
    rw [happly_e_symm, ← hlv0]
  rw [hcomp, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rfl
have hΦ_surj_on_image : ∀ y : E,
    ∃ l₀ : ↥(S iLam) →ₗ[A] E, c.val y = Φ l₀ := by
  intro y
  obtain ⟨l₀_pre, hl₀_pre⟩ := tensor_through_rank_one π v₀ hrange_π
    ((e y) iLam)
  refine ⟨α • l₀_pre, ?_⟩
  have h_e_decomp : e y = ∑ i ∈ (e y).support, DirectSum.of β i ((e y) i) := by
    rw [DirectSum.sum_support_of]
  have h_apply_c : e (c.val y) =
      ∑ i ∈ (e y).support,
        e (c.val (e.symm (DirectSum.of β i ((e y) i)))) := by
    conv_lhs => rw [show y = e.symm (e y) from (e.symm_apply_apply y).symm,
      h_e_decomp]
    rw [map_sum, map_sum, map_sum]
  have h_block : ∀ i, e (c.val (e.symm (DirectSum.of β i ((e y) i)))) =
      DirectSum.of β i (TensorProduct.map (f i) LinearMap.id ((e y) i)) :=
    fun i => block_factorization_extended c S e f hf_block i ((e y) i)
  have h_block_zero : ∀ i, i ≠ iLam →
      e (c.val (e.symm (DirectSum.of β i ((e y) i)))) = 0 := by
    intro i hi
    rw [h_block, hf_zero i hi]
    simp
  have h_e_cy : e (c.val y) =
      DirectSum.of β iLam
        (TensorProduct.map (f iLam) LinearMap.id ((e y) iLam)) := by
    rw [h_apply_c]
    by_cases hsupp : iLam ∈ (e y).support
    · rw [Finset.sum_eq_single iLam ?_ ?_]
      · exact h_block iLam
      · intros j _ hj; exact h_block_zero j hj
      · intro h; exact (h hsupp).elim
    · have hzero : (e y) iLam = 0 := DFinsupp.notMem_support_iff.mp hsupp
      rw [hzero]
      simp
      apply Finset.sum_eq_zero
      intros j hj
      apply h_block_zero
      intro hji; exact hsupp (hji ▸ hj)
  have h_factor : TensorProduct.map (f iLam) LinearMap.id ((e y) iLam) =
      v₀ ⊗ₜ[k] (α • l₀_pre) := by
    rw [hπ_special]
    have : TensorProduct.map (α • π) LinearMap.id ((e y) iLam) =
        α • TensorProduct.map π LinearMap.id ((e y) iLam) := by
      rw [show (α • π : ↥(S iLam) →ₗ[k] ↥(S iLam)) =
            α • (π : ↥(S iLam) →ₗ[k] ↥(S iLam)) from rfl]
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
    rw [this, hl₀_pre]
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
  rw [h_factor] at h_e_cy
  have h_cy : c.val y = e.symm (DirectSum.of β iLam (v₀ ⊗ₜ[k] (α • l₀_pre))) := by
    have h := congrArg e.symm h_e_cy
    simp only [LinearEquiv.symm_apply_apply] at h
    exact h
  rw [h_cy, he_eval]
  rfl
have hΦ_inj : Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro l hl
  show (l : ↥(S iLam) →ₗ[A] E) = 0
  have hker : v₀ ∈ LinearMap.ker l := by
    change l v₀ = 0; exact hl
  rcases (eq_bot_or_eq_top (LinearMap.ker l)) with h | h
  · exfalso; apply hv₀_ne
    have : v₀ ∈ (⊥ : Submodule A ↥(S iLam)) := h ▸ hker
    simpa using this
  · ext v
    have hv : v ∈ LinearMap.ker l := h ▸ Submodule.mem_top
    change l v = 0
    simpa [LinearMap.mem_ker] using hv
let Φ' : (↥(S iLam) →ₗ[A] E) →ₗ[↥(Subalgebra.centralizer k
    (A : Set (Module.End k E)))] ↥(imageSubmoduleB c) :=
  { toFun := fun l => ⟨Φ l, hΦ_in_range l⟩
    map_add' := fun l₁ l₂ => by ext; show Φ (l₁ + l₂) = Φ l₁ + Φ l₂; rw [map_add]
    map_smul' := fun b l => by
      ext
      show Φ (b • l) = b • (Φ l : E)
      rw [hΦ_equiv]; rfl }
have hΦ'_surj : Function.Surjective Φ' := by
  rintro ⟨z, hz⟩
  rw [mem_imageSubmoduleB, LinearMap.mem_range] at hz
  obtain ⟨y, hy⟩ := hz
  obtain ⟨l₀, hl₀⟩ := hΦ_surj_on_image y
  refine ⟨l₀, ?_⟩
  ext
  show Φ l₀ = z
  rw [← hy]; exact hl₀.symm
have hΦ'_inj : Function.Injective Φ' := by
  rw [injective_iff_map_eq_zero]
  intro l hl
  apply hΦ_inj
  have : (Φ' l : E) = 0 := by
    rw [hl]; rfl
  exact this
let Ψ : (↥(S iLam) →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k
    (A : Set (Module.End k E)))] ↥(imageSubmoduleB c) :=
  LinearEquiv.ofBijective Φ' ⟨hΦ'_inj, hΦ'_surj⟩
haveI hL_simp : IsSimpleModule
    (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
    (↥(S iLam) →ₗ[A] E) :=
  isSimpleModule_homA_centralizer (k := k) (E := E) A (S iLam)
exact IsSimpleModule.congr Ψ.symm
```
-/

end Etingof
