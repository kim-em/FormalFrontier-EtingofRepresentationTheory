import Mathlib

/-!
# Infrastructure: Wedderburn-Artin Decomposition for Group Algebras

This file connects Mathlib's Wedderburn-Artin theorem to the representation theory
of finite groups. For a finite group G over an algebraically closed field k with
char(k) ∤ |G|, we establish:

1. `MonoidAlgebra k G` is a finite-dimensional semisimple k-algebra
2. By Wedderburn-Artin, `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`
3. The dimension formula `|G| = Σ i, (d i)²`
4. The number of components `n` corresponds to the number of isomorphism classes
   of simple `FDRep k G` objects

## References

- Etingof, *Introduction to Representation Theory*, Theorem 4.1.1
- Mathlib: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
- Mathlib: `Rep.equivalenceModuleMonoidAlgebra`
-/

open CategoryTheory

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

/-! ### Finite-dimensionality and semisimplicity of k[G] -/

omit [Fintype G] in
noncomputable instance MonoidAlgebra.instFiniteDimensional [Finite G] :
    FiniteDimensional k (MonoidAlgebra k G) :=
  inferInstance

omit [Fintype G] in
instance MonoidAlgebra.instIsSemisimpleRing [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

/-! ### Wedderburn-Artin decomposition -/

omit [Fintype G] in
/-- The Wedderburn-Artin decomposition of `k[G]`: there exist `n` matrix blocks of sizes
`d i` such that `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`.
This is a direct application of `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`. -/
theorem MonoidAlgebra.wedderburnArtin [Finite G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    (F := k) (R := MonoidAlgebra k G)

/-! ### IrrepDecomp structure -/

/-- Bundled Wedderburn-Artin decomposition data for the group algebra `k[G]`.
Packages the number of irreducible representations `n`, their dimensions `d`,
and the algebra isomorphism. -/
structure IrrepDecomp (k G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] where
  /-- Number of isomorphism classes of irreducible representations -/
  n : ℕ
  /-- Dimensions of the irreducible representations -/
  d : Fin n → ℕ
  /-- Each dimension is positive -/
  d_pos : ∀ i, NeZero (d i)
  /-- The Wedderburn-Artin algebra isomorphism -/
  iso : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k

/-- Existence of the irreducible decomposition. -/
noncomputable def IrrepDecomp.mk' [NeZero (Nat.card G : k)] :
    IrrepDecomp k G := by
  choose n d hd he using MonoidAlgebra.wedderburnArtin (k := k) (G := G)
  exact ⟨n, d, hd, he.some⟩

/-! ### Dimension formula -/

omit [IsAlgClosed k] [Group G] in
/-- The dimension of `k[G]` equals `|G|`. -/
theorem MonoidAlgebra.finrank_eq_card :
    Module.finrank k (MonoidAlgebra k G) = Fintype.card G := by
  change Module.finrank k (G →₀ k) = _
  simp

omit [IsAlgClosed k] [Group G] [Fintype G] in
/-- The dimension of a product of matrix algebras is the sum of squares of the sizes. -/
theorem finrank_pi_matrix (n : ℕ) (d : Fin n → ℕ) :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) =
      ∑ i, (d i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  congr 1
  ext i
  simp [Module.finrank_matrix, Fintype.card_fin, sq]

/-- **Sum-of-squares formula**: `|G| = Σ i, (d i)²` where `d i` are the dimensions of the
irreducible representations of G. This is the key dimension identity from Theorem 4.1.1(ii). -/
theorem IrrepDecomp.sum_sq_eq_card [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∑ i, (D.d i) ^ 2 = Fintype.card G := by
  have hfr := MonoidAlgebra.finrank_eq_card (k := k) (G := G)
  have hiso := D.iso.toLinearEquiv.finrank_eq
  rw [hfr] at hiso
  rw [finrank_pi_matrix] at hiso
  omega

/-! ### Helper lemmas for FDRep connection -/

/-- Column vectors `Fin n → k` form a simple module over `Matrix (Fin n) (Fin n) k`.
For any nonzero vector `w`, the orbit `Mat_n(k) · w` spans all of `k^n`. -/
instance Matrix.instIsSimpleModule {k : Type*} [Field k] (n : ℕ) [NeZero n] :
    IsSimpleModule (Matrix (Fin n) (Fin n) k) (Fin n → k) where
  eq_bot_or_eq_top m := by
    by_cases hm : m = ⊥
    · left; exact hm
    · right; rw [Submodule.eq_top_iff']
      intro v
      obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra h; push_neg at h; exact hwne (funext h)
      -- For any target v, construct M with M.mulVec w = v
      let M : Matrix (Fin n) (Fin n) k := fun j l => if l = i then v j * (w i)⁻¹ else 0
      have : M.mulVec w = v := by
        ext j; simp only [Matrix.mulVec, M, dotProduct]; simp [mul_assoc, inv_mul_cancel₀ hi]
      rw [← this]; exact m.smul_mem M hw

/-- If `f : R →+* S` is surjective and `M` is a simple `S`-module, then `M` is a simple
`R`-module via `Module.compHom`. R-submodules equal S-submodules since every S-scalar
is in the image of `f`. -/
lemma IsSimpleModule.compHom {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) [hM : IsSimpleModule S M] :
    @IsSimpleModule R _ M _ (Module.compHom M f) := by
  letI : Module R M := Module.compHom M f
  have key : ∀ m : Submodule R M, m = ⊥ ∨ m = ⊤ := by
    intro m
    let m' : Submodule S M := {
      toAddSubmonoid := m.toAddSubmonoid
      smul_mem' := fun s x hx => by obtain ⟨r, rfl⟩ := hf s; exact m.smul_mem r hx
    }
    have hcarrier : ∀ x, x ∈ m' ↔ x ∈ m := fun _ => Iff.rfl
    cases hM.eq_bot_or_eq_top m' with
    | inl h =>
      left; ext x; constructor
      · intro hx; have := (hcarrier x).mpr hx; rw [h] at this; simpa using this
      · intro hx; simp at hx; rw [hx]; exact m.zero_mem'
    | inr h =>
      right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _; exact (hcarrier x).mp (h ▸ Submodule.mem_top)
  haveI : Nontrivial (Submodule R M) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    obtain ⟨a, b, hab⟩ := @IsSimpleModule.nontrivial S _ M _ _ hM
    have ha : a ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    have hb : b ∈ (⊥ : Submodule R M) := by rw [h]; exact trivial
    simp at ha hb; exact hab (ha ▸ hb.symm)
  exact { eq_bot_or_eq_top := key }

/-! ### Column vector representations -/

/-- The projection ring homomorphism from `k[G]` to the i-th matrix factor
of the Wedderburn-Artin decomposition. -/
noncomputable def IrrepDecomp.projRingHom [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    MonoidAlgebra k G →+* Matrix (Fin (D.d i)) (Fin (D.d i)) k :=
  (Pi.evalRingHom (fun i => Matrix (Fin (D.d i)) (Fin (D.d i)) k) i).comp
    D.iso.toRingEquiv.toRingHom

/-- The projection to the i-th factor is surjective (since `D.iso` is an isomorphism). -/
lemma IrrepDecomp.projRingHom_surjective [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Function.Surjective (D.projRingHom i) := by
  intro M
  exact ⟨D.iso.symm (Pi.single i M), by simp [projRingHom, Pi.evalRingHom, Pi.single]⟩

/-- The column vector representation: `G` acts on `Fin (D.d i) → k` via the i-th matrix factor
of the Wedderburn-Artin decomposition. -/
noncomputable def IrrepDecomp.columnRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Representation k G (Fin (D.d i) → k) where
  toFun g := Matrix.mulVecLin (D.projRingHom i (MonoidAlgebra.of k G g))
  map_one' := by rw [map_one, map_one, Matrix.mulVecLin_one]; rfl
  map_mul' g h := by rw [map_mul, map_mul, Matrix.mulVecLin_mul]; rfl

/-- The column vector FDRep: the i-th irreducible representation of G. -/
noncomputable def IrrepDecomp.columnFDRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : FDRep k G :=
  FDRep.of (D.columnRep i)

/-- The dimension of the i-th column vector representation equals `D.d i`. -/
lemma IrrepDecomp.finrank_columnFDRep [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Module.finrank k (D.columnFDRep i) = D.d i := by
  simp [columnFDRep, FDRep.of]

/-! ### Bridge: IsSimpleModule → Simple (FDRep) -/

/-- A full faithful functor preserving monomorphisms reflects Simple objects. -/
private lemma Simple.of_full_faithful_preservesMono {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- The projection ring homomorphism commutes with scalar multiplication. -/
private lemma IrrepDecomp.projRingHom_smul [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n)
    (r : k) (a : MonoidAlgebra k G) :
    D.projRingHom i (r • a) = r • D.projRingHom i a := by
  simp [IrrepDecomp.projRingHom]

/-- The k[G]-module action on column vectors factors through the matrix ring. -/
private lemma IrrepDecomp.asModule_smul_eq_mulVec [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n)
    (a : MonoidAlgebra k G) (v : (D.columnRep i).asModule) :
    (D.columnRep i).asModuleEquiv (a • v) =
      (D.projRingHom i a).mulVec ((D.columnRep i).asModuleEquiv v) := by
  simp only [Representation.asModuleEquiv_map_smul]
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    simp [Representation.asAlgebraHom, MonoidAlgebra.lift_apply,
          Finsupp.sum_single_index, IrrepDecomp.columnRep]
  | hadd a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Matrix.add_mulVec, ha, hb]
  | hsmul r a ha =>
    simp only [map_smul, LinearMap.smul_apply, ha]
    rw [D.projRingHom_smul i r a, Matrix.smul_mulVec r]

/-- The column vector representation's asModule is a simple k[G]-module. -/
noncomputable instance IrrepDecomp.isSimpleModule_columnRep_asModule [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    IsSimpleModule (MonoidAlgebra k G) (D.columnRep i).asModule := by
  haveI := D.d_pos i
  haveI : Nontrivial (D.columnRep i).asModule := by
    change Nontrivial (Fin (D.d i) → k); infer_instance
  rw [isSimpleModule_iff]
  exact IsSimpleOrder.mk fun m => by
    let m' : Submodule (Matrix (Fin (D.d i)) (Fin (D.d i)) k) (Fin (D.d i) → k) :=
      { carrier := { w | (D.columnRep i).asModuleEquiv.symm w ∈ m }
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at *; exact m.add_mem ha hb
        zero_mem' := by simp [m.zero_mem]
        smul_mem' := fun M w hw => by
          simp only [Set.mem_setOf_eq] at *
          change (D.columnRep i).asModuleEquiv.symm (M.mulVec w) ∈ m
          obtain ⟨a, ha⟩ := D.projRingHom_surjective i M
          have heq : M.mulVec w = (D.columnRep i).asModuleEquiv
              (a • (D.columnRep i).asModuleEquiv.symm w) := by
            rw [D.asModule_smul_eq_mulVec, ha]; simp
          rw [heq, LinearEquiv.symm_apply_apply]
          exact m.smul_mem a hw }
    cases (Matrix.instIsSimpleModule (D.d i)).eq_bot_or_eq_top m' with
    | inl h =>
      left; ext x
      simp only [Submodule.mem_bot]
      constructor
      · intro hx
        have : (D.columnRep i).asModuleEquiv x ∈ m'.carrier := by simpa using hx
        rw [h] at this; simp at this
        exact (D.columnRep i).asModuleEquiv.injective this
      · intro hx; rw [hx]; exact m.zero_mem
    | inr h =>
      right; ext x
      simp only [Submodule.mem_top, iff_true]
      have : (D.columnRep i).asModuleEquiv x ∈ m'.carrier := by rw [h]; exact Submodule.mem_top
      simpa using this

/-- If `ρ.asModule` is simple over k[G], then `FDRep.of ρ` is Simple in FDRep k G. -/
private noncomputable instance FDRep.simple_of_isSimpleModule_asModule [NeZero (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra k G) ρ.asModule)
    exact simple_of_isSimpleModule
  haveI : Simple ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    Simple.of_full_faithful_preservesMono E.functor _
  exact Simple.of_full_faithful_preservesMono (forget₂ (FDRep k G) (Rep k G)) _

/-! ### Equivariance and central idempotent machinery -/

/-- G-equivariance of a k-linear map extends to k[G]-equivariance for the projRingHom action. -/
private lemma equivariant_ext [NeZero (Nat.card G : k)] (D : IrrepDecomp k G) (i j : Fin D.n)
    (f : (Fin (D.d i) → k) →ₗ[k] (Fin (D.d j) → k))
    (hf : ∀ g : G, ∀ v, f ((D.projRingHom i (MonoidAlgebra.of k G g)).mulVec v) =
      (D.projRingHom j (MonoidAlgebra.of k G g)).mulVec (f v))
    (a : MonoidAlgebra k G) (v : Fin (D.d i) → k) :
    f ((D.projRingHom i a).mulVec v) = (D.projRingHom j a).mulVec (f v) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact hf g v
  | hadd a b ha hb =>
    simp only [map_add, Matrix.add_mulVec, f.map_add, ha, hb]
  | hsmul r a ha =>
    rw [D.projRingHom_smul i, D.projRingHom_smul j,
        Matrix.smul_mulVec r, f.map_smul, ha, Matrix.smul_mulVec r]

/-- The linear equiv from an FDRep iso is G-equivariant w.r.t. the projRingHom action. -/
private lemma IrrepDecomp.isoToLinearEquiv_equivariant [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i j : Fin D.n)
    (f : D.columnFDRep i ≅ D.columnFDRep j) (g : G) (v : Fin (D.d i) → k) :
    FDRep.isoToLinearEquiv f ((D.projRingHom i (MonoidAlgebra.of k G g)).mulVec v) =
      (D.projRingHom j (MonoidAlgebra.of k G g)).mulVec (FDRep.isoToLinearEquiv f v) := by
  have key := LinearMap.ext_iff.mp (FDRep.Iso.conj_ρ f g) (FDRep.isoToLinearEquiv f v)
  simp [LinearEquiv.conj_apply] at key
  exact key.symm

/-! ### Connection to FDRep -/

/-- The number of Wedderburn-Artin components equals the number of isomorphism classes
of simple `FDRep k G` objects. -/
theorem IrrepDecomp.n_eq_card_simples [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∃ (V : Fin D.n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) := by
  refine ⟨D.columnFDRep, ?_, ?_, ?_⟩
  · intro i
    exact FDRep.simple_of_isSimpleModule_asModule (D.columnRep i)
  · -- Injectivity: central idempotent argument
    intro i j ⟨f⟩
    by_contra hij
    let φ := FDRep.isoToLinearEquiv f
    have hext := equivariant_ext D i j φ.toLinearMap
      (D.isoToLinearEquiv_equivariant i j f)
    let e := D.iso.symm (Pi.single i (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k))
    have h_ei : D.projRingHom i e = 1 := by
      simp [e, IrrepDecomp.projRingHom, Pi.evalRingHom, Pi.single, Function.update]
    have h_ej : D.projRingHom j e = 0 := by
      simp [e, IrrepDecomp.projRingHom, Pi.evalRingHom, Pi.single, Function.update, Ne.symm hij]
    have hzero : ∀ v : Fin (D.d i) → k, φ.toLinearMap v = 0 := by
      intro v; have := hext e v; rw [h_ei, h_ej] at this
      simp [Matrix.one_mulVec, Matrix.zero_mulVec] at this; exact this
    haveI := D.d_pos i
    have hne : (fun (_ : Fin (D.d i)) => (1 : k)) ≠ 0 := by
      intro h; exact one_ne_zero (congr_fun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩)
    exact hne (φ.injective ((hzero _).trans (map_zero φ.toLinearMap).symm))
  · intro W hW; sorry

/-- Each dimension `d i` in the Wedderburn-Artin decomposition equals the
`Module.finrank k` of the corresponding irreducible representation. -/
theorem IrrepDecomp.d_eq_finrank [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∀ i, D.d i = Module.finrank k (V i) := by
  sorry
