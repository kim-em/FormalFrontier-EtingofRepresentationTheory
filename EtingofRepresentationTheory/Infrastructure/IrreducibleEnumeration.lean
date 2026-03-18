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

/-- Column FDReps are simple. -/
theorem IrrepDecomp.columnFDRep_simple [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : Simple (D.columnFDRep i) :=
  FDRep.simple_of_isSimpleModule_asModule (D.columnRep i)

/-- Column FDReps are pairwise non-isomorphic. -/
theorem IrrepDecomp.columnFDRep_injective [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i j : Fin D.n)
    (h : Nonempty ((D.columnFDRep i) ≅ (D.columnFDRep j))) : i = j := by
  obtain ⟨f⟩ := h
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

/-! ### Central idempotent machinery for surjectivity -/

/-- The central idempotent `e_i := D.iso.symm (Pi.single i 1)` in k[G]. -/
private noncomputable def IrrepDecomp.centralIdem [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : MonoidAlgebra k G :=
  D.iso.symm (Pi.single i 1)

/-- In the product ring, `Pi.single i 1 * Pi.single i 1 = Pi.single i 1`. -/
private lemma pi_single_sq {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, MulZeroOneClass (R i)] (i : ι) :
    Pi.single (M := R) i 1 * Pi.single i 1 = Pi.single i 1 := by
  funext j; simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]

/-- Central idempotents are idempotent: `e_i * e_i = e_i`. -/
private lemma IrrepDecomp.centralIdem_sq [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    D.centralIdem i * D.centralIdem i = D.centralIdem i := by
  simp only [centralIdem, ← map_mul]; congr 1; exact pi_single_sq i

/-- In the product ring, `∑ i, Pi.single i 1 = 1`. -/
private lemma pi_single_sum {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, AddCommMonoid (R i)] [∀ i, One (R i)] :
    ∑ i, Pi.single (M := R) i 1 = 1 := by
  funext j; simp only [Finset.sum_apply, Pi.one_apply]
  rw [show ∀ (s : Finset ι), ∑ i ∈ s, Pi.single (M := R) i 1 j =
    ∑ i ∈ s, if i = j then (1 : R j) else 0 from fun s => by
    congr 1; ext i; by_cases h : i = j
    · subst h; simp [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]]
  · simp

/-- Central idempotents sum to 1. -/
private lemma IrrepDecomp.centralIdem_sum [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∑ i, D.centralIdem i = 1 := by
  simp only [centralIdem, ← map_sum, ← map_one D.iso.symm]; congr 1; exact pi_single_sum

/-- In the product ring, `Pi.single i 1` commutes with everything. -/
private lemma pi_single_central {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : ι → Type*} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (a : ∀ j, R j) : Pi.single (M := R) i 1 * a = a * Pi.single i 1 := by
  funext j; simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm h)]; simp

/-- Central idempotents commute with all elements of k[G]. -/
private lemma IrrepDecomp.centralIdem_comm [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) (a : MonoidAlgebra k G) :
    D.centralIdem i * a = a * D.centralIdem i := by
  apply D.iso.injective
  simp only [centralIdem, map_mul, AlgEquiv.apply_symm_apply]
  exact pi_single_central i (D.iso a)

/-- The action of e_i on W via the representation's algebra hom commutes with W.ρ g. -/
private lemma IrrepDecomp.centralIdemAction_comm [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (W : FDRep k G) (i : Fin D.n) (g : G) :
    (Representation.asAlgebraHom W.ρ (D.centralIdem i)).comp (W.ρ g) =
    (W.ρ g).comp (Representation.asAlgebraHom W.ρ (D.centralIdem i)) := by
  have hg : (W.ρ g : W →ₗ[k] W) = Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) := by
    ext v; simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  ext v; simp only [LinearMap.comp_apply, hg]
  have := congr_arg (fun a => Representation.asAlgebraHom W.ρ a v)
    (D.centralIdem_comm i (MonoidAlgebra.of k G g))
  simp only [map_mul] at this
  exact this

/-- The FDRep endomorphism from a central idempotent action. -/
private noncomputable def IrrepDecomp.centralIdemEndo [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (W : FDRep k G) (i : Fin D.n) : W ⟶ W where
  hom := FGModuleCat.ofHom (Representation.asAlgebraHom W.ρ (D.centralIdem i))
  comm h := by
    have heq := D.centralIdemAction_comm W i h
    ext v
    exact LinearMap.congr_fun heq v

/-- The identity matrix is the sum of diagonal matrix units. -/
private lemma Matrix.one_eq_sum_single (n : ℕ) [NeZero n] :
    (1 : Matrix (Fin n) (Fin n) k) = ∑ j, Matrix.single j j (1 : k) := by
  ext p q; simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply]
  by_cases h : p = q
  · subst h
    convert (Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : k))).symm using 1
    · simp
    · congr 1; ext x; by_cases hx : x = p <;> simp_all
  · convert (Finset.sum_eq_zero (fun c _ => ?_)).symm
    · simp [h]
    · simp only [ite_eq_right_iff]; rintro ⟨rfl, rfl⟩; exact absurd rfl h

/-- Matrix product `M * single j j₀ 1` equals ∑_a M a j • single a j₀ 1. -/
private lemma Matrix.mul_single_eq_sum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (j j₀ : Fin n) :
    M * Matrix.single j j₀ (1 : k) =
      ∑ a, M a j • Matrix.single a j₀ (1 : k) := by
  ext p q; simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply,
    Pi.smul_apply, smul_ite, smul_zero, smul_eq_mul, mul_one, mul_ite, mul_zero]
  -- LHS: ∑ x, if j = x ∧ j₀ = q then M p x else 0
  -- RHS: ∑ x, M x j * if x = p ∧ j₀ = q then 1 else 0
  -- Both evaluate to: if j₀ = q then M p j else 0
  trans (if j₀ = q then M p j else 0)
  · convert Finset.sum_ite_eq Finset.univ j
      (fun x => if j₀ = q then M p x else 0) using 1
    · congr 1; ext x
      by_cases hx : j = x <;> by_cases hq : j₀ = q <;> simp [hx, hq]
    · simp
  · symm; convert Finset.sum_ite_eq' Finset.univ p
      (fun a => if j₀ = q then M a j else 0) using 1
    · congr 1; ext x
      by_cases hxp : x = p <;> by_cases hq : j₀ = q <;> simp [hxp, hq]
    · simp

set_option maxHeartbeats 400000 in
/-- Every simple FDRep is isomorphic to some column FDRep (Wedderburn surjectivity). -/
theorem IrrepDecomp.columnFDRep_surjective [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (W : FDRep k G) (hW : Simple W) :
    ∃ i, Nonempty (W ≅ D.columnFDRep i) := by
  -- Step 1: Each centralIdemEndo is a scalar by Schur's lemma
  have hschur : ∀ i : Fin D.n, ∃ c : k,
      c • 𝟙 W = D.centralIdemEndo W i := fun i =>
    endomorphism_simple_eq_smul_id k (D.centralIdemEndo W i)
  choose c hc using hschur
  -- Step 2: Each c_i satisfies c_i² = c_i (idempotent)
  have hc_idem : ∀ i, c i * c i = c i := by
    intro i
    -- centralIdemEndo ≫ centralIdemEndo = centralIdemEndo (from centralIdem_sq)
    have hendo_sq : D.centralIdemEndo W i ≫ D.centralIdemEndo W i = D.centralIdemEndo W i := by
      ext v
      change Representation.asAlgebraHom W.ρ (D.centralIdem i)
        (Representation.asAlgebraHom W.ρ (D.centralIdem i) v) =
        Representation.asAlgebraHom W.ρ (D.centralIdem i) v
      conv_lhs =>
        rw [show Representation.asAlgebraHom W.ρ (D.centralIdem i)
          (Representation.asAlgebraHom W.ρ (D.centralIdem i) v) =
          (Representation.asAlgebraHom W.ρ (D.centralIdem i * D.centralIdem i)) v from by
            rw [map_mul]; rfl]
      rw [D.centralIdem_sq]
    -- Work pointwise: endo(v) = c_i • v, endo(endo(v)) = endo(v)
    -- So c_i • (c_i • v) = c_i • v, giving (c_i² - c_i) • v = 0 for all v
    -- endo acts as c_i • id on W, so endo(w) = c_i • w for all w
    have hcv : ∀ w : W.V, (D.centralIdemEndo W i).hom.hom w = c i • w := by
      intro w
      have := congr_fun (congr_arg (fun f => f.hom.hom) (hc i).symm) w
      simpa using this
    have hpt : ∀ v : W.V,
        (c i * c i - c i) • v = 0 := by
      intro v
      -- endo(endo(v)) = endo(v) from hendo_sq
      have hsqv := congr_fun (congr_arg (fun f => f.hom.hom) hendo_sq) v
      -- hsqv : endo(endo(v)) = endo(v)
      -- rewrite both sides using hcv
      -- Simplify hsqv to nested application, then rewrite with hcv
      change (D.centralIdemEndo W i).hom.hom
          ((D.centralIdemEndo W i).hom.hom v) =
          (D.centralIdemEndo W i).hom.hom v at hsqv
      simp only [hcv, smul_smul] at hsqv
      -- hsqv : (c i * c i) • v = c i • v
      have : (c i * c i - c i) • v = 0 := by rw [sub_smul, hsqv, sub_self]
      exact this
    -- If c_i² ≠ c_i, then (c_i² - c_i) is a nonzero scalar annihilating all of W
    by_contra hne
    have hne' : c i * c i - c i ≠ 0 := sub_ne_zero.mpr hne
    -- This means all v = 0, so W is zero, contradicting Simple
    have : ∀ v : W.V, v = 0 := by
      intro v
      have := hpt v
      rwa [smul_eq_zero, or_iff_right hne'] at this
    -- If all vectors are 0, then 𝟙 W = 0, contradicting simplicity
    exact id_nonzero W (by ext v; simp [this v])
  -- Step 3: ∑ c_i = 1
  have hc_sum : ∑ i, c i = 1 := by
    -- endo acts as c_i • id on W
    have hcv' : ∀ (i : Fin D.n) (w : W.V),
        (D.centralIdemEndo W i).hom.hom w = c i • w := by
      intro j w
      have := congr_fun (congr_arg (fun f => f.hom.hom) (hc j).symm) w
      simpa using this
    -- For any v: (∑ c_i) • v = ∑ c_i • v = ∑ e_i(v) = (∑ e_i)(v) = id(v) = v
    have hsum_pt : ∀ v : W.V, (∑ i, c i) • v = v := by
      intro v
      -- (∑ c_i) • v = ∑ c_i • v = ∑ e_i(v) = v
      rw [Finset.sum_smul]
      -- ∑ c_i • v = ∑ e_i(v), since e_i(v) = c_i • v
      have : ∑ i, c i • v = ∑ i, Representation.asAlgebraHom W.ρ (D.centralIdem i) v :=
        Finset.sum_congr rfl (fun i _ => (hcv' i v).symm)
      rw [this]
      -- ∑ e_i(v) = (∑ e_i)(v) = asAlgebraHom(1)(v) = v
      rw [← LinearMap.sum_apply, ← map_sum, D.centralIdem_sum]
      simp [Representation.asAlgebraHom_single, MonoidAlgebra.one_def]
    -- Extract scalar: (∑ c_i - 1) • v = 0 for all v
    by_contra hne
    have hne' : ∑ i, c i - 1 ≠ 0 := sub_ne_zero.mpr hne
    have : ∀ v : W.V, v = 0 := by
      intro v
      have h := hsum_pt v
      have h2 : (∑ i, c i - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
      rwa [smul_eq_zero, or_iff_right hne'] at h2
    exact id_nonzero W (by ext v; simp [this v])
  -- Step 4: Find i₀ with c_{i₀} = 1
  have hc_01 : ∀ i, c i = 0 ∨ c i = 1 := by
    intro i
    have h := hc_idem i
    have h2 : c i * (c i - 1) = 0 := by
      have : c i * (c i - 1) = c i * c i - c i := by ring
      rw [this, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; exact h3
    · right; exact sub_eq_zero.mp h3
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, c i₀ = 1 := by
    by_contra h; push_neg at h
    have hall : ∀ i, c i = 0 := fun i => (hc_01 i).resolve_right (h i)
    rw [show ∑ i, c i = ∑ i, (0 : k) from Finset.sum_congr rfl (fun i _ => hall i),
      Finset.sum_const_zero] at hc_sum
    exact one_ne_zero hc_sum.symm
  -- Step 5: Construct isomorphism W ≅ columnFDRep i₀
  -- centralIdem i₀ acts as id on W, so W is a module over the i₀-th Wedderburn block
  -- This gives W ≅ columnFDRep i₀
  refine ⟨i₀, ?_⟩
  -- centralIdemEndo W i₀ = 𝟙 W
  have hid : D.centralIdemEndo W i₀ = 𝟙 W := by
    have := (hc i₀).symm; rwa [hi₀, one_smul] at this
  -- Pointwise: e_{i₀} acts as identity on W
  have hid_pt : ∀ w : W,
      Representation.asAlgebraHom W.ρ (D.centralIdem i₀) w = w := by
    intro w
    have := congr_arg (fun f => f.hom.hom w) hid
    simpa [centralIdemEndo] using this
  -- Key algebraic identity: e_{i₀} * a = iso.symm (Pi.single i₀ (projRingHom i₀ a))
  have heidem_mul : ∀ a : MonoidAlgebra k G,
      D.centralIdem i₀ * a = D.iso.symm (Pi.single i₀ (D.projRingHom i₀ a)) := by
    intro a
    apply D.iso.injective
    simp only [AlgEquiv.apply_symm_apply]
    ext j
    simp only [centralIdem, map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply]
    by_cases h : i₀ = j
    · subst h; simp [Pi.single_eq_same, projRingHom, Pi.evalRingHom]
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  -- The k[G]-action on W factors through projRingHom i₀
  have hfactor : ∀ (a : MonoidAlgebra k G) (w : W),
      Representation.asAlgebraHom W.ρ a w =
      Representation.asAlgebraHom W.ρ (D.iso.symm (Pi.single i₀ (D.projRingHom i₀ a))) w := by
    intro a w
    rw [← heidem_mul, map_mul]
    change Representation.asAlgebraHom W.ρ a w =
      Representation.asAlgebraHom W.ρ (D.centralIdem i₀)
        (Representation.asAlgebraHom W.ρ a w)
    rw [hid_pt]
  -- Use Schur's lemma: construct a nonzero FDRep morphism columnFDRep i₀ ⟶ W
  -- Then isIso_of_hom_simple gives the isomorphism
  haveI := D.d_pos i₀
  haveI := D.columnFDRep_simple i₀
  -- W is nontrivial (from Simple)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W.V, w₀ ≠ 0 := by
    by_contra h; push_neg at h
    exact id_nonzero W (by ext v; simp [h v])
  -- Helper: projRingHom i₀ inverts iso.symm ∘ Pi.single i₀
  have hproj_single : ∀ X : Matrix (Fin (D.d i₀)) (Fin (D.d i₀)) k,
      D.projRingHom i₀ (D.iso.symm (Pi.single i₀ X)) = X := by
    intro X; simp [projRingHom, Pi.evalRingHom, Pi.single]
  -- Find j₀ such that some diagonal matrix unit doesn't kill w₀
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (D.d i₀),
      Representation.asAlgebraHom W.ρ
        (D.iso.symm (Pi.single i₀ (Matrix.single j₀ j₀ (1 : k)))) w₀ ≠ 0 := by
    by_contra h; push_neg at h
    apply hw₀; rw [← hid_pt w₀]
    have : D.centralIdem i₀ =
        ∑ j, D.iso.symm (Pi.single i₀ (Matrix.single j j (1 : k))) := by
      apply D.iso.injective; rw [map_sum]
      simp only [centralIdem, AlgEquiv.apply_symm_apply]
      conv_lhs => rw [Matrix.one_eq_sum_single (D.d i₀) (k := k)]
      ext l; simp only [Finset.sum_apply]
      by_cases hl : i₀ = l
      · subst hl; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne (Ne.symm hl)]
    rw [this, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero (fun j _ => h j)
  -- Define φ j = action of matrix unit E_{j,j₀} on w₀
  set φ : Fin (D.d i₀) → W.V :=
    fun j => Representation.asAlgebraHom W.ρ
      (D.iso.symm (Pi.single i₀ (Matrix.single j j₀ (1 : k)))) w₀
  -- Key equivariance: W.ρ g (φ j) = ∑ a, M a j • φ a
  have hphi_equivar : ∀ (g : G) (j : Fin (D.d i₀)),
      W.ρ g (φ j) = ∑ a, (D.projRingHom i₀ (MonoidAlgebra.of k G g)) a j • φ a := by
    intro g j
    set M := D.projRingHom i₀ (MonoidAlgebra.of k G g)
    -- W.ρ g (φ j) = asAlgebraHom (of g) (φ j)
    have hρ_eq : W.ρ g (φ j) =
        Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) (φ j) := by
      rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul]
    rw [hρ_eq, show Representation.asAlgebraHom W.ρ (MonoidAlgebra.of k G g) (φ j) =
      Representation.asAlgebraHom W.ρ
        (MonoidAlgebra.of k G g * D.iso.symm (Pi.single i₀ (Matrix.single j j₀ 1))) w₀ from by
          rw [map_mul]; rfl]
    rw [hfactor, show D.projRingHom i₀ (MonoidAlgebra.of k G g *
        D.iso.symm (Pi.single i₀ (Matrix.single j j₀ (1 : k)))) =
      M * Matrix.single j j₀ 1 from by rw [map_mul, hproj_single]]
    rw [Matrix.mul_single_eq_sum]
    -- Use linearity: the composition asAlgebraHom ∘ iso.symm ∘ Pi.single i₀ is linear
    -- So distributing over ∑ and • works step by step
    show (Representation.asAlgebraHom W.ρ)
      (D.iso.symm (Pi.single i₀ (∑ a, M a j • Matrix.single a j₀ (1 : k)))) w₀ =
      ∑ a, M a j • (Representation.asAlgebraHom W.ρ)
        (D.iso.symm (Pi.single i₀ (Matrix.single a j₀ 1))) w₀
    -- Define the linear map: X ↦ asAlgebraHom(iso.symm(Pi.single i₀ X)) w₀
    let L : Matrix (Fin (D.d i₀)) (Fin (D.d i₀)) k →ₗ[k] W.V :=
      { toFun := fun X => (Representation.asAlgebraHom W.ρ)
          (D.iso.symm (Pi.single i₀ X)) w₀
        map_add' := fun X Y => by
          simp only [Pi.single_add, map_add, map_add, LinearMap.add_apply]
        map_smul' := fun r X => by
          simp only [Pi.single_smul (f := fun i => Matrix (Fin (D.d i)) (Fin (D.d i)) k),
            map_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
    change L (∑ a, M a j • Matrix.single a j₀ 1) = ∑ a, M a j • L (Matrix.single a j₀ 1)
    rw [map_sum]; congr 1; ext a; rw [map_smul]
  -- Construct the FDRep morphism: f(v) = ∑_j v_j • φ_j
  let fHom : D.columnFDRep i₀ ⟶ W :=
    { hom := FGModuleCat.ofHom
        { toFun := fun v => ∑ j, v j • φ j
          map_add' := fun v w => by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          map_smul' := fun r v => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [Finset.smul_sum]; congr 1; ext j; rw [smul_smul] }
      comm := fun g => by
        ext v
        -- Goal: f(ρ_col(g)(v)) = W.ρ g (f(v))
        show ∑ j, ((D.columnRep i₀) g v) j • φ j = W.ρ g (∑ j, v j • φ j)
        -- RHS: distribute W.ρ g over the sum
        rw [map_sum]; simp_rw [map_smul]
        -- Rewrite W.ρ g (φ j) using hphi_equivar
        simp_rw [hphi_equivar g]
        -- columnRep g = mulVecLin (projRingHom (of g))
        -- (columnRep g v) j = ∑ a, M j a * v a  where M = projRingHom (of g)
        -- Need: ∑ j, (∑ a, M j a * v a) • φ j = ∑ x, v x • ∑ a, M a x • φ a
        -- This is just rearranging a double sum
        -- columnRep is definitionally mulVec, so we can just use show
        -- after hphi_equivar, LHS has columnRep and RHS has expanded form
        -- Goal: ∑ j, (columnRep i₀ g v) j • φ j = ∑ x, v x • ∑ a, M a x • φ a
        -- columnRep g v j = ∑ a, M j a * v a  by definition
        simp_rw [show ∀ j, ((D.columnRep i₀) g v) j =
          ∑ a, (D.projRingHom i₀ (MonoidAlgebra.of k G g)) j a * v a from fun j => rfl]
        -- Distribute (∑ a, c a) • x = ∑ a, c a • x on LHS
        conv_lhs => arg 2; ext x; rw [Finset.sum_smul]
        -- RHS: distribute v x • over the inner sum, combine smul
        conv_rhs => arg 2; ext x; rw [Finset.smul_sum]; arg 2; ext a; rw [smul_smul]
        rw [Finset.sum_comm]
        congr 1; ext x; congr 1; ext a; ring }
  -- fHom is nonzero: f(e_{j₀}) = φ j₀ ≠ 0
  have hfHom_ne : fHom ≠ 0 := by
    intro h
    apply hj₀
    -- If fHom = 0, then φ j₀ = 0 (since fHom(e_{j₀}) = φ j₀)
    -- fHom = 0 means the underlying hom is 0
    have h2 : ∀ v : Fin (D.d i₀) → k, ∑ j, v j • φ j = 0 := by
      intro v
      have := congr_arg (fun (f : D.columnFDRep i₀ ⟶ W) => f.hom.hom v) h
      simpa [fHom] using this
    specialize h2 (Pi.single (M := fun _ => k) j₀ 1)
    -- φ j₀ = ∑ j, (Pi.single j₀ 1) j • φ j  (only j₀ term survives)
    have hs : ∑ j, (Pi.single (M := fun _ => k) j₀ 1) j • φ j = φ j₀ := by
      rw [show ∑ j, (Pi.single (M := fun _ => k) j₀ 1) j • φ j =
        ∑ j, if j = j₀ then φ j else 0 from by
          congr 1; ext j; by_cases hj : j = j₀ <;> simp [Pi.single_apply, hj]]
      rw [Finset.sum_ite_eq']; simp
    rw [hs] at h2; exact h2
  -- By Schur's lemma, a nonzero morphism between simples is an isomorphism
  haveI : IsIso fHom := isIso_of_hom_simple hfHom_ne
  exact ⟨(asIso fHom).symm⟩

/-- The number of Wedderburn-Artin components equals the number of isomorphism classes
of simple `FDRep k G` objects. -/
theorem IrrepDecomp.n_eq_card_simples [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∃ (V : Fin D.n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :=
  ⟨D.columnFDRep, D.columnFDRep_simple, D.columnFDRep_injective, D.columnFDRep_surjective⟩

/-- Each dimension `d i` in the Wedderburn-Artin decomposition equals the
`Module.finrank k` of the corresponding irreducible representation.

**WARNING**: This statement is likely incorrect as written. It claims `D.d i = finrank k (V i)`
for an *arbitrary* complete set `V` of non-isomorphic simples, but `V` could list them in a
different order than `D.columnFDRep`. The correct statement should involve a permutation:
`∃ σ : Equiv.Perm (Fin D.n), ∀ i, D.d (σ i) = finrank k (V i)`.
Downstream uses in `RegularCharacter.lean` and `Theorem5_1_5.lean` should be updated
to work with the permuted version (sums over permutations are equal). -/
theorem IrrepDecomp.d_eq_finrank [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∀ i, D.d i = Module.finrank k (V i) := by
  intro i
  -- V i is simple, so by columnFDRep_surjective, V i ≅ columnFDRep j for some j
  obtain ⟨j, ⟨eVj⟩⟩ := D.columnFDRep_surjective (V i) (hV i)
  -- columnFDRep i is simple, so by hsurj, columnFDRep i ≅ V j' for some j'
  obtain ⟨j', ⟨eCj'⟩⟩ := hsurj (D.columnFDRep i) (D.columnFDRep_simple i)
  -- By the iso V i ≅ columnFDRep j, finrank k (V i) = D.d j
  have hfr : Module.finrank k (V i) = D.d j := by
    rw [← D.finrank_columnFDRep j]
    exact LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv eVj)
  -- By the iso columnFDRep i ≅ V j', finrank k (V j') = D.d i
  have hfr' : Module.finrank k (V j') = D.d i := by
    rw [← D.finrank_columnFDRep i]
    exact (LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv eCj')).symm
  -- The bijection σ : i ↦ j (where V i ≅ columnFDRep j) gives finrank k (V i) = D.d (σ i).
  -- We need D.d i = D.d (σ i), i.e. σ = id on d values. This does NOT follow for general V:
  -- V could be a permutation of columnFDRep that swaps blocks of different sizes.
  -- The theorem statement needs to be corrected to use an explicit permutation σ.
  sorry
