import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialTensorBridge
import EtingofRepresentationTheory.Chapter5.Definition5_23_1

/-!
# Polynomial GL_N-rep embedding into a tensor power (Schur-Weyl #2b)

Etingof §5.23. A finite-dimensional polynomial GL_N-representation `M` whose
matrix coefficients are homogeneous polynomials of degree `n` in the matrix
entries `g_ij` admits a `k`-linear injection into `(V^⊗n)^m` for some `m`,
where `V := Fin N → k`.

The construction uses
`Etingof.PolynomialTensorBridge.homogeneousPolyToTensor` (Schur-Weyl #2a) to
realize each matrix-coefficient polynomial as an element of
`V^⊗n ⊗ (V^*)^⊗n`, then splits off the `(V^*)^⊗n` factor via the standard
basis to land in `(V^⊗n)^m`.

## Status

This file lands the **injection** part of the deliverable from issue #2478:
`polynomialRep_embeds_in_tensorPower_inj` exhibits `m`, the linear map `φ`,
and proves injectivity. **GL_N-equivariance** of `φ` is deferred to a sibling
issue, since the equivariance proof requires equivariance of the underlying
bridge `homogeneousPolyToTensor` for the right-translation action on
polynomials versus `g ↦ g^⊗n ⊗ 1` on the tensor target — itself a substantial
chunk that the bridge file (`Chapter5/PolynomialTensorBridge.lean`) explicitly
defers.

## Main result

* `Etingof.PolynomialRepEmbedding.polynomialRep_embeds_in_tensorPower_inj` —
  the linear injection of a hom-degree-`n` polynomial GL_N-rep into
  `(V^⊗n)^m`.
-/

open scoped TensorProduct
open MvPolynomial

namespace Etingof

namespace PolynomialRepEmbedding

universe u

open PolynomialTensorBridge

variable (k : Type u) [Field k] (N n : ℕ)

/-- Splitting the right `(V^*)^⊗n` factor of `V^⊗n ⊗ (V^*)^⊗n` via the
standard basis: `V^⊗n ⊗ (V^*)^⊗n ≃ₗ[k] (Fin n → Fin N) → V^⊗n`. The
GL_N-action on `(V^*)^⊗n` is *not* used here; we are merely splitting the
target of the bridge into a `Fin (N^n)`-indexed direct sum of `V^⊗n`-copies. -/
noncomputable def splitDualBasis :
    PolyTensorTgt k N n ≃ₗ[k] ((Fin n → Fin N) → TensorPower k (StdV k N) n) :=
  let bDual : Module.Basis (Fin n → Fin N) k
      (TensorPower k (Module.Dual k (StdV k N)) n) :=
    Basis.piTensorProduct (fun _ : Fin n => stdDualBasis k N)
  LinearEquiv.lTensor _ bDual.equivFun ≪≫ₗ
    TensorProduct.piScalarRight k k _ (Fin n → Fin N)

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The matrix coefficient polynomial for row `a` of `x ∈ M`, in basis `b`,
given polynomial witnesses `P a c`: `x ↦ Σ_c (b.coord c x) • P a c`. -/
noncomputable def matrixCoeffPoly {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) :
    M →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  ∑ c : Fin d, LinearMap.smulRight (b.coord c) (P a c)

@[simp]
lemma matrixCoeffPoly_apply {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a x = ∑ c : Fin d, (b.coord c x) • P a c := by
  unfold matrixCoeffPoly
  rw [LinearMap.sum_apply]
  rfl

/-- A `k`-linear combination of homogeneous degree-`n` polynomials is itself
homogeneous of degree `n`. -/
lemma matrixCoeffPoly_mem_homogeneous {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a x ∈
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n := by
  rw [matrixCoeffPoly_apply]
  refine Submodule.sum_mem _ ?_
  intro c _
  exact Submodule.smul_mem _ _ (hhom a c)

/-- For a single endomorphism `T : M →ₗ[k] M` whose matrix coefficients in
basis `b` agree with `MvPolynomial.eval s ∘ P` (at a fixed evaluation `s`),
evaluating the matrix-coefficient polynomial at `s` recovers the row-`a`
coordinate of `T x`. This is the matrix-coefficient identity on the level of
generic `x`, deduced from the case `x = b c` via `k`-linearity. -/
lemma eval_matrixCoeffPoly {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (T : M →ₗ[k] M) (s : Fin N × Fin N → k)
    (hP : ∀ a c, b.coord a (T (b c)) = MvPolynomial.eval s (P a c))
    (a : Fin d) (x : M) :
    MvPolynomial.eval s (matrixCoeffPoly k N b P a x) = b.coord a (T x) := by
  classical
  rw [matrixCoeffPoly_apply, map_sum]
  -- T x = Σ_c (b.coord c x) • b c
  have hx_repr : x = ∑ c : Fin d, b.coord c x • b c := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Module.Basis.coord_apply]
  -- b.coord a (T x) = Σ_c (b.coord c x) * b.coord a (T (b c))
  conv_rhs => rw [hx_repr, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  -- LHS term: eval s ((b.coord c x) • P a c) = (b.coord c x) * eval s (P a c)
  rw [MvPolynomial.smul_eval]
  -- RHS term: b.coord a (T ((b.coord c x) • b c)) =
  --   (b.coord c x) * b.coord a (T (b c))
  rw [show T ((b.coord c) x • b c) = (b.coord c) x • T (b c) from
        T.map_smul _ _,
      show (b.coord a) ((b.coord c) x • T (b c)) =
             (b.coord c) x • (b.coord a) (T (b c)) from
        (b.coord a).map_smul _ _,
      smul_eq_mul, hP]

/-- Bridge each row `a` of the matrix-coefficient polynomial to
`V^⊗n ⊗ (V^*)^⊗n` via `homogeneousPolyToTensor` (Schur-Weyl #2a). -/
noncomputable def polyTensorRow {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) :
    M →ₗ[k] PolyTensorTgt k N n :=
  (homogeneousPolyToTensor k N n).comp <|
    LinearMap.codRestrict
      (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
      (matrixCoeffPoly k N b P a)
      (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)

lemma polyTensorRow_eq_zero_iff {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    polyTensorRow k N n b P hhom a x = 0 ↔ matrixCoeffPoly k N b P a x = 0 := by
  unfold polyTensorRow
  rw [LinearMap.comp_apply,
    show ((homogeneousPolyToTensor k N n)
            (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (matrixCoeffPoly k N b P a)
              (matrixCoeffPoly_mem_homogeneous k N n b P hhom a) x) = 0) ↔
          (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (matrixCoeffPoly k N b P a)
              (matrixCoeffPoly_mem_homogeneous k N n b P hhom a) x = 0) from
      ⟨fun h => (homogeneousPolyToTensor_injective k N n)
        (h.trans (map_zero _).symm),
       fun h => h ▸ map_zero _⟩]
  -- Now: codRestrict ... x = 0 ↔ matrixCoeffPoly ... x = 0
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Subtype.val h
    simpa [LinearMap.codRestrict] using this
  · apply Subtype.ext
    simpa [LinearMap.codRestrict] using h

/-- The bundled embedding: `M →ₗ[k] (Fin d × (Fin n → Fin N)) → V^⊗n`. -/
noncomputable def polyTensorBundle {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) :
    M →ₗ[k] (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) :=
  LinearMap.pi fun p =>
    ((LinearMap.proj p.2 : ((Fin n → Fin N) → TensorPower k (StdV k N) n) →ₗ[k]
        TensorPower k (StdV k N) n).comp
      ((splitDualBasis k N n).toLinearMap.comp
        (polyTensorRow k N n b P hhom p.1)))

lemma polyTensorBundle_apply {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    polyTensorBundle k N n b P hhom x p =
      (splitDualBasis k N n) (polyTensorRow k N n b P hhom p.1 x) p.2 := by
  rfl

/-- **Polynomial GL_N-rep embeds in tensor power** (Etingof §5.23,
Schur-Weyl #2b — injection part).

A finite-dimensional polynomial GL_N-representation `M`, presented by a basis
and matrix-coefficient polynomial witnesses that are homogeneous of degree `n`
in the matrix entries `g_ij` (with no `det⁻¹` factor), admits a `k`-linear
injection into `(V^⊗n)^m` for some `m`, where `V := Fin N → k`.

The construction is via the bridge `homogeneousPolyToTensor` from Schur-Weyl
#2a: each row `a` of the matrix-coefficient polynomial of `x ∈ M` is a
homogeneous degree-`n` polynomial; bridge it to `V^⊗n ⊗ (V^*)^⊗n`, then split
off the dual factor via the standard basis to land in
`(Fin n → Fin N) → V^⊗n`. Bundle over the `Fin d`-many basis indices.

GL_N-equivariance of the embedding is **not** stated here; it is deferred to a
sibling issue together with equivariance of the underlying bridge.

(Etingof Definition 5.23.1 + Theorem 5.23.2 setup. Issue #2478.) -/
theorem polynomialRep_embeds_in_tensorPower_inj
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : IsAlgebraicRepresentation N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ := by
  classical
  obtain ⟨d, b, P, hhom, hP⟩ := hpoly
  -- Re-index Fin d × (Fin n → Fin N) ≃ Fin m
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) ≃ₗ[k]
        (Fin m → TensorPower k (StdV k N) n) :=
    LinearEquiv.piCongrLeft k (fun _ : Fin m => TensorPower k (StdV k N) n) e
  let φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n) :=
    reindex.toLinearMap.comp (polyTensorBundle k N n b P hhom)
  refine ⟨m, φ, ?_⟩
  -- Injectivity: kernel of φ is trivial.
  rw [show Function.Injective φ ↔ Function.Injective (polyTensorBundle k N n b P hhom) from
    by simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- hx : polyTensorBundle ... x = 0 (function on Fin d × (Fin n → Fin N))
  -- For each (a, j), polyTensorBundle x (a, j) = 0.
  have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
      polyTensorBundle k N n b P hhom x p = 0 :=
    fun p => congrFun hx p
  -- For each a, splitDualBasis (polyTensorRow a x) = 0 (function on (Fin n → Fin N)).
  have hx_split : ∀ a : Fin d,
      (splitDualBasis k N n) (polyTensorRow k N n b P hhom a x) = 0 := by
    intro a
    funext j
    have := hx_pt (a, j)
    rw [polyTensorBundle_apply] at this
    simpa using this
  -- splitDualBasis is a LinearEquiv; hence polyTensorRow a x = 0 for each a.
  have hx_row : ∀ a : Fin d, polyTensorRow k N n b P hhom a x = 0 :=
    fun a => (splitDualBasis k N n).map_eq_zero_iff.mp (hx_split a)
  -- Hence matrixCoeffPoly k N b P a x = 0 for each a.
  have hx_poly : ∀ a : Fin d, matrixCoeffPoly k N b P a x = 0 :=
    fun a => (polyTensorRow_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
  -- Translate to: ρ g x has zero coordinates in basis b, for every g.
  have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
      b.coord a (ρ g x) = 0 := by
    intro g a
    have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a' c') := by
      intro a' c'
      have h := hP g a' c'
      rwa [Module.Basis.coord_apply]
    have h := eval_matrixCoeffPoly k N b P (ρ g)
      (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
    rw [hx_poly a, map_zero] at h
    exact h.symm
  -- Hence ρ g x = 0 for every g.
  have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
    intro g
    apply b.repr.injective
    ext a
    rw [LinearEquiv.map_zero, Finsupp.zero_apply]
    have := hcoord_zero g a
    rwa [Module.Basis.coord_apply] at this
  -- Set g = 1: ρ 1 x = x via ρ.map_one, hence x = 0.
  have hone : ρ 1 = LinearMap.id := ρ.map_one
  have h := hρ_zero 1
  rw [hone, LinearMap.id_apply] at h
  exact h

/-! ## GL_N-equivariance of the embedding -/

/-- `splitDualBasis` intertwines the `g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`
with the pointwise `PiTensorProduct.map g.toLin'` action on each
`V^⊗n`-coordinate. -/
lemma splitDualBasis_tgtGLAction (g : Matrix (Fin N) (Fin N) k)
    (z : PolyTensorTgt k N n) (j : Fin n → Fin N) :
    splitDualBasis k N n (PolynomialTensorBridge.tgtGLAction k N n g z) j =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)
        (splitDualBasis k N n z j) := by
  classical
  -- Prove the underlying LinearMap equality by TensorProduct.ext.
  suffices h :
      ((LinearMap.proj j : ((Fin n → Fin N) → TensorPower k (StdV k N) n) →ₗ[k]
              TensorPower k (StdV k N) n).comp
          (splitDualBasis k N n).toLinearMap).comp
        (PolynomialTensorBridge.tgtGLAction k N n g) =
        (PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)).comp
          ((LinearMap.proj j).comp (splitDualBasis k N n).toLinearMap) by
    have := congrArg (fun f => f z) h
    simpa using this
  apply TensorProduct.ext'
  intro u v
  simp only [LinearMap.comp_apply, splitDualBasis, PolynomialTensorBridge.tgtGLAction,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.lTensor_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, LinearMap.proj_apply, map_smul]

/-- **Matrix-coefficient polynomial equivariance.** Given the polynomial matrix-
coefficient multiplicativity hypothesis `hP_mul`, the matrix-coefficient
polynomial of `ρ g x` equals the right-translation of the matrix-coefficient
polynomial of `x` by `g`. -/
lemma matrixCoeffPoly_polyRightTransl {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a (ρ g x) =
      PolynomialTensorBridge.polyRightTransl k N
        (g : Matrix (Fin N) (Fin N) k) (matrixCoeffPoly k N b P a x) := by
  classical
  -- Abbreviations.
  set eg : MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
    PolynomialTensorBridge.polyRightTransl k N (g : Matrix (Fin N) (Fin N) k) with hegd
  set eval_g : MvPolynomial (Fin N × Fin N) k → k :=
    fun p => MvPolynomial.eval
      (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p with hevalg
  -- Key identity: b.coord c' (ρ g x) = Σ_c (b.coord c x) * eval_g (P c' c).
  have hrepr : ∀ c' : Fin d,
      b.coord c' (ρ g x) = ∑ c : Fin d, b.coord c x * eval_g (P c' c) := by
    intro c'
    have hx : x = ∑ c : Fin d, b.coord c x • b c := by
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Module.Basis.coord_apply]
    conv_lhs => rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [(ρ g).map_smul, (b.coord c').map_smul, smul_eq_mul]
    congr 1
    have := hP g c' c
    rwa [Module.Basis.coord_apply]
  -- Both sides expand as Σ_c b.coord c x • eg(P a c).
  have hLHS :
      matrixCoeffPoly k N b P a (ρ g x) =
        ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [matrixCoeffPoly_apply]
    simp_rw [hrepr]
    -- Σ_{c'} (Σ_c a_c * e_{c',c}) • P a c' = Σ_c a_c • (Σ_{c'} e_{c',c} • P a c')
    have hswap :
        (∑ c' : Fin d, (∑ c : Fin d, b.coord c x * eval_g (P c' c)) • P a c') =
          (∑ c : Fin d, b.coord c x • (∑ c' : Fin d, eval_g (P c' c) • P a c')) := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← smul_smul, ← mul_smul, mul_comm]
    rw [hswap]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [hP_mul g a c]
  have hRHS : eg (matrixCoeffPoly k N b P a x) =
      ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [matrixCoeffPoly_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
  rw [hLHS, hRHS]

/-- Equivariance of `polyTensorRow`: right-translation on the polynomial side
matches `tgtGLAction` on the tensor side. -/
lemma polyTensorRow_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    polyTensorRow k N n b P hhom a (ρ g x) =
      PolynomialTensorBridge.tgtGLAction k N n (g : Matrix (Fin N) (Fin N) k)
        (polyTensorRow k N n b P hhom a x) := by
  unfold polyTensorRow
  simp only [LinearMap.comp_apply]
  -- After codRestrict, the subtypes carry matrixCoeffPoly. Push through the equality.
  have hmc := matrixCoeffPoly_polyRightTransl k N b P ρ hP hP_mul g a x
  have heq :
      (LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
          (matrixCoeffPoly k N b P a)
          (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) (ρ g x) =
      ⟨PolynomialTensorBridge.polyRightTransl k N (g : Matrix (Fin N) (Fin N) k)
          ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (matrixCoeffPoly k N b P a)
            (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) x).val,
       PolynomialTensorBridge.polyRightTransl_isHomogeneous (k := k) (N := N) (m := n)
         (g : Matrix (Fin N) (Fin N) k)
         ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (matrixCoeffPoly k N b P a)
            (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) x).property⟩ := by
    apply Subtype.ext
    simpa [LinearMap.codRestrict] using hmc
  rw [heq,
    PolynomialTensorBridge.homogeneousPolyToTensor_equivariant (k := k) (N := N) (n := n)
      (g := (g : Matrix (Fin N) (Fin N) k))]

/-- Equivariance of `polyTensorBundle` on each coordinate. -/
lemma polyTensorBundle_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    polyTensorBundle k N n b P hhom (ρ g x) p =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (polyTensorBundle k N n b P hhom x p) := by
  rw [polyTensorBundle_apply, polyTensorBundle_apply,
    polyTensorRow_equivariant (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul g p.1 x,
    splitDualBasis_tgtGLAction k N n (g : Matrix (Fin N) (Fin N) k)
      (polyTensorRow k N n b P hhom p.1 x) p.2]

/-- **Polynomial GL_N-rep embeds equivariantly into a tensor power**
(Etingof §5.23, Schur-Weyl #2b — full version with equivariance).

The upgraded form of `polynomialRep_embeds_in_tensorPower_inj`: in addition to
exhibiting an injective `k`-linear embedding `φ : M → (V^⊗n)^m`, the embedding
is `GL_N`-equivariant — it intertwines the representation `ρ` on `M` with the
tensor-power action `g ↦ PiTensorProduct.map (g^⊗n)` on each coordinate of the
target.

The equivariance requires, in addition to the matrix-coefficient evaluation
hypothesis `hP`, the **polynomial matrix-coefficient multiplicativity**
hypothesis `hP_mul` asserting the polynomial-level identity
`polyRightTransl g (P a c') = Σ_c eval g (P c c') • P a c`. This identity
holds at the evaluation level for all `g ∈ GL_N` (by `ρ.map_mul` and the
polynomial-matrix-coefficient setup), and from `[CharZero k]` (hence
`Infinite k`) one can derive the polynomial-level statement via the
determinant/funext trick. We take it as a hypothesis here to keep the bundle
focused on the equivariance assembly; the derivation is deferred to a
follow-up.

(Etingof Definition 5.23.1 + Theorem 5.23.2 setup. Issue #2537 / #2527 Part B.) -/
theorem polynomialRep_embeds_in_tensorPower
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : IsAlgebraicRepresentation N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
           PolynomialTensorBridge.polyRightTransl k N
               (g : Matrix (Fin N) (Fin N) k) (P a c') =
             ∑ c, MvPolynomial.eval
                    (fun ij : Fin N × Fin N =>
                      (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
                    (P c c') • P a c)) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  classical
  obtain ⟨d, b, P, hhom, hP, hP_mul⟩ := hpoly
  -- Unpack and keep the explicit φ so we can also state equivariance.
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) ≃ₗ[k]
        (Fin m → TensorPower k (StdV k N) n) :=
    LinearEquiv.funCongrLeft k (TensorPower k (StdV k N) n) e.symm
  let φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n) :=
    reindex.toLinearMap.comp (polyTensorBundle k N n b P hhom)
  refine ⟨m, φ, ?_, ?_⟩
  · -- Injectivity: identical to `polynomialRep_embeds_in_tensorPower_inj`.
    rw [show Function.Injective φ ↔
          Function.Injective (polyTensorBundle k N n b P hhom) from by
      simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
        polyTensorBundle k N n b P hhom x p = 0 :=
      fun p => congrFun hx p
    have hx_split : ∀ a : Fin d,
        (splitDualBasis k N n) (polyTensorRow k N n b P hhom a x) = 0 := by
      intro a
      funext j
      have := hx_pt (a, j)
      rw [polyTensorBundle_apply] at this
      simpa using this
    have hx_row : ∀ a : Fin d, polyTensorRow k N n b P hhom a x = 0 :=
      fun a => (splitDualBasis k N n).map_eq_zero_iff.mp (hx_split a)
    have hx_poly : ∀ a : Fin d, matrixCoeffPoly k N b P a x = 0 :=
      fun a => (polyTensorRow_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
    have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
        b.coord a (ρ g x) = 0 := by
      intro g a
      have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
            (P a' c') := by
        intro a' c'
        have h := hP g a' c'
        rwa [Module.Basis.coord_apply]
      have h := eval_matrixCoeffPoly k N b P (ρ g)
        (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
      rw [hx_poly a, map_zero] at h
      exact h.symm
    have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
      intro g
      apply b.repr.injective
      ext a
      rw [LinearEquiv.map_zero, Finsupp.zero_apply]
      have := hcoord_zero g a
      rwa [Module.Basis.coord_apply] at this
    have hone : ρ 1 = LinearMap.id := ρ.map_one
    have h := hρ_zero 1
    rw [hone, LinearMap.id_apply] at h
    exact h
  · -- Equivariance: φ (ρ g x) i = PiTensorProduct.map g.toLin' (φ x i).
    intro g x i
    -- reindex is funCongrLeft e.symm, so evaluation at i gives the value at e.symm i.
    change polyTensorBundle k N n b P hhom (ρ g x) (e.symm i) =
      PiTensorProduct.map (fun _ => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (polyTensorBundle k N n b P hhom x (e.symm i))
    exact polyTensorBundle_equivariant (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul
      g x (e.symm i)

end PolynomialRepEmbedding

end Etingof
