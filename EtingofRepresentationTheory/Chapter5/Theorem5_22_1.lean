import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.PermDiagonalTrace
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Theorem 5.22.1: Weyl Character Formula for GL(V)

## Construction

The Schur module `L_λ` is the image of the Young symmetrizer `c_λ` acting
on the tensor power `(k^N)^{⊗n}` where `n = ∑ λᵢ`. The GL_N(k)-action
on this image comes from the diagonal action `g ↦ g⊗g⊗…⊗g`, which
commutes with the symmetric group action (hence with `c_λ`), so the image
is GL_N-stable.
-/

open MvPolynomial Finset CategoryTheory

noncomputable section

namespace Etingof

/-! ### Weight to partition conversion -/

/-- Convert a weight vector `lam : Fin N → ℕ` to a partition of `∑ i, lam i`. -/
def weightToPartition (N : ℕ) (lam : Fin N → ℕ) :
    Nat.Partition (∑ i, lam i) where
  parts := (Finset.univ.val.map lam).filter (0 < ·)
  parts_pos hi := (Multiset.mem_filter.mp hi).2
  parts_sum := by
    have h_filt : ∀ (s : Multiset ℕ), (s.filter (0 < ·)).sum = s.sum := by
      intro s
      induction s using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.filter_cons]
        split
        · simp [Multiset.sum_cons, ih]
        · rename_i h; push_neg at h; simp [Nat.le_zero.mp h, ih]
    rw [h_filt]
    simp [Finset.sum]

/-! ### Young symmetrizer over a general field -/

/-- The Young symmetrizer `c_λ = a_λ · b_λ` in `k[S_n]`, over a general field `k`. -/
def YoungSymmetrizerK (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  (∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val) *
  (∑ g : (RowSubgroup n la), MonoidAlgebra.of k _ g.val)

/-! ### Young symmetrizer over ℤ and scalar transfer -/

/-- The Young symmetrizer over ℤ. This is the "universal" version from which both
`YoungSymmetrizer` (over ℂ) and `YoungSymmetrizerK` (over k) are obtained via base change. -/
def YoungSymmetrizerZ (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  (∑ g : (ColumnSubgroup n la),
    (↑(Equiv.Perm.sign g.val) : ℤ) • MonoidAlgebra.of ℤ _ g.val) *
  (∑ g : (RowSubgroup n la), MonoidAlgebra.of ℤ _ g.val)

/-- Base change maps `of ℤ g` to `of k g`. -/
private theorem mapRange_of {G : Type*} [Monoid G] (R : Type*) [CommRing R]
    (f : ℤ →+* R) (g : G) :
    MonoidAlgebra.mapRangeRingHom G f (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of R G g := by
  change MonoidAlgebra.mapRangeRingHom G f (Finsupp.single g 1) = Finsupp.single g 1
  rw [MonoidAlgebra.mapRangeRingHom_single, map_one]

/-- `YoungSymmetrizerK k` is the image of `YoungSymmetrizerZ` under the base change `ℤ → k`. -/
theorem YoungSymmetrizerK_eq_mapRange (k : Type*) [CommRing k] (n : ℕ)
    (la : Nat.Partition n) :
    YoungSymmetrizerK k n la =
      MonoidAlgebra.mapRangeRingHom _ (Int.castRingHom k) (YoungSymmetrizerZ n la) := by
  classical
  simp only [YoungSymmetrizerK, YoungSymmetrizerZ, map_mul, map_sum, map_zsmul,
    mapRange_of, ← Int.cast_smul_eq_zsmul k]

/-- The ℂ Young symmetrizer is the image of `YoungSymmetrizerZ` under base change `ℤ → ℂ`. -/
theorem YoungSymmetrizer_eq_mapRange (n : ℕ) (la : Nat.Partition n) :
    YoungSymmetrizer n la =
      MonoidAlgebra.mapRangeRingHom _ (Int.castRingHom ℂ) (YoungSymmetrizerZ n la) := by
  classical
  simp only [YoungSymmetrizer, RowSymmetrizer, ColumnAntisymmetrizer, YoungSymmetrizerZ,
    map_mul, map_sum, map_zsmul, mapRange_of, ← Int.cast_smul_eq_zsmul ℂ]

private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  simp only [Nat.Partition.sortedParts]
  have := la.parts_sum
  have h1 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
  have h2 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ).sum =
      (la.parts.sort (· ≥ ·)).sum := Multiset.sum_coe _
  linarith [h2.symm.trans (congrArg Multiset.sum h1)]

/-- If σ preserves both rows and columns, then σ = 1. -/
theorem row_col_preserving_eq_one (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (hrow : σ ∈ RowSubgroup n la) (hcol : σ ∈ ColumnSubgroup n la) :
    σ = 1 := by
  ext k : 1
  have hr := hrow k
  have hc := hcol k
  simp only [Equiv.Perm.one_apply]
  have hk_lt : k.val < la.sortedParts.sum := by
    rw [sortedParts_sum]; exact k.isLt
  have hσk_lt : (σ k).val < la.sortedParts.sum := by
    rw [sortedParts_sum]; exact (σ k).isLt
  exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts
    (σ k).val k.val hσk_lt hk_lt hr hc)

/-- The coefficient of `YoungSymmetrizerZ` at the identity permutation is 1. -/
theorem YoungSymmetrizerZ_apply_one (n : ℕ) (la : Nat.Partition n) :
    YoungSymmetrizerZ n la 1 = 1 := by
  classical
  -- Transfer to ℂ where we can compute directly
  have hinj : Function.Injective (Int.castRingHom ℂ : ℤ →+* ℂ) := Int.cast_injective
  apply hinj
  -- (Int.castRingHom ℂ) (cZ 1) = (mapRange cZ)(1) = (YoungSymmetrizer)(1)
  rw [show (Int.castRingHom ℂ) (YoungSymmetrizerZ n la 1) =
      (MonoidAlgebra.mapRangeRingHom _ (Int.castRingHom ℂ) (YoungSymmetrizerZ n la)) 1
    from (MonoidAlgebra.mapRangeRingHom_apply (Int.castRingHom ℂ) _ _).symm]
  rw [← YoungSymmetrizer_eq_mapRange, (Int.castRingHom ℂ).map_one]
  -- YoungSymmetrizer = RowSymmetrizer * ColumnAntisymmetrizer
  simp only [YoungSymmetrizer, RowSymmetrizer, ColumnAntisymmetrizer]
  -- Distribute the product of sums
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, Finset.mul_sum]
  -- Unfold of to single, then simplify multiplication of singles
  have hof : ∀ (g : Equiv.Perm (Fin n)),
      (MonoidAlgebra.of ℂ _ g : MonoidAlgebra ℂ _) = Finsupp.single g 1 := fun _ => rfl
  simp_rw [hof, MonoidAlgebra.single_mul_single, mul_one]
  -- Push smul inside the inner sum
  simp_rw [Finset.smul_sum]
  -- Goal: (∑ q ∑ p, (sign q) • single (q*p) 1)(1) = 1
  rw [Finset.sum_apply']
  conv_lhs => arg 2; ext k; rw [Finset.sum_apply']
  simp only [MonoidAlgebra.smul_apply, smul_eq_mul, MonoidAlgebra.single_apply,
    mul_ite, mul_one, mul_zero]
  -- ∑_q ∑_p, if q * p = 1 then (sign q : ℂ) else 0 = 1
  rw [Fintype.sum_eq_single ⟨1, (ColumnSubgroup n la).one_mem⟩]
  · rw [Fintype.sum_eq_single ⟨1, (RowSubgroup n la).one_mem⟩]
    · simp [Equiv.Perm.sign_one]
    · intro ⟨p, hp⟩ hne
      rw [if_neg]
      intro hp1
      exact hne (Subtype.ext (by simpa using hp1))
  · intro ⟨q, hq⟩ hne
    apply Fintype.sum_eq_zero
    intro ⟨p, hp⟩
    rw [if_neg]
    intro hqp
    have heq : q = p⁻¹ := mul_eq_one_iff_eq_inv.mp hqp
    have hq_in_P : q ∈ RowSubgroup n la := heq ▸ (RowSubgroup n la).inv_mem hp
    exact hne (Subtype.ext (row_col_preserving_eq_one n la q hq_in_P hq))

/-- The Young symmetrizer over any CharZero ring satisfies c² = α·c for some scalar α.
The scalar is the image of an integer, obtained by transferring the identity from ℂ
(Lemma 5.13.3) via the injective map ℤ → ℂ. -/
theorem YoungSymmetrizerK_sq_scalar (k : Type*) [CommRing k] [CharZero k]
    (n : ℕ) (la : Nat.Partition n) :
    ∃ α : k, YoungSymmetrizerK k n la * YoungSymmetrizerK k n la =
      α • YoungSymmetrizerK k n la := by
  -- Get the identity over ℂ
  obtain ⟨α_ℂ, hα⟩ := Lemma5_13_3 n la
  -- Key elements
  set cZ := YoungSymmetrizerZ n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℂ := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  set φ_k := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom k)
  -- Relations to base change
  have h_ℂ : YoungSymmetrizer n la = φ_ℂ cZ := YoungSymmetrizer_eq_mapRange n la
  have h_k : YoungSymmetrizerK k n la = φ_k cZ := YoungSymmetrizerK_eq_mapRange k n la
  -- cZ(1) = 1
  have hcZ1 : cZ 1 = 1 := YoungSymmetrizerZ_apply_one n la
  -- From Lemma5_13_3, derive the identity in mapRange form
  have hmul : φ_ℂ (cZ * cZ) = α_ℂ • φ_ℂ cZ := by
    rw [map_mul]; exact h_ℂ ▸ hα
  -- Evaluating at identity: α_ℂ = Int.cast β
  have hα_eq : α_ℂ = (β : ℂ) := by
    have h1 := Finsupp.ext_iff.mp hmul 1
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℂ] at h1
    exact h1.symm
  -- Therefore: for all σ, (cZ * cZ)(σ) = β * cZ(σ)  (by injectivity of ℤ → ℂ)
  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := Finsupp.ext_iff.mp hmul σ
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hα_eq, φ_ℂ] at h1
    -- h1 : (↑((cZ * cZ) σ) : ℂ) = ↑β * ↑(cZ σ)
    have h2 : ((cZ * cZ) σ : ℂ) = ((β * cZ σ : ℤ) : ℂ) := by push_cast; exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2
    -- Need to show (cZ * cZ) σ = (β • cZ) σ
    rw [MonoidAlgebra.smul_apply, smul_eq_mul, h3]
  -- Map to k: cK² = (β : k) • cK
  exact ⟨(β : k), by
    rw [h_k, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul k]⟩

/-! ### Young symmetrizer endomorphism on tensor power -/

/-- The Young symmetrizer `c_λ` lifted to an endomorphism of `V^{⊗n}`. -/
def youngSymEndomorphism (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Module.End k (TensorPower k (Fin N → k) (∑ i, lam i)) :=
  symGroupAlgHom k (Fin N → k) (∑ i, lam i)
    (YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam))

/-! ### GL_N representation on tensor power -/

/-- The diagonal action of `GL_N(k)` on `V^{⊗n}`: `g` acts as `g ⊗ g ⊗ … ⊗ g`.
The representation map sends `g ∈ GL_N(k)` to the linear endomorphism
`PiTensorProduct.map (fun _ => g.val.mulVecLin)`. -/
def glTensorRep (k : Type*) [Field k] (N n : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (TensorPower k (Fin N → k) n) where
  toFun g := PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
  map_one' := by
    classical
    change PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) =
      LinearMap.id
    have : (fun _ : Fin n => Matrix.mulVecLin (R := k) (1 : Matrix _ _ k)) =
        (fun _ : Fin n => (LinearMap.id : (Fin N → k) →ₗ[k] (Fin N → k))) :=
      funext fun _ => Matrix.mulVecLin_one
    rw [this, PiTensorProduct.map_id]
  map_mul' g₁ g₂ := by
    classical
    change PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin g₁.val)) ∘ₗ
      (PiTensorProduct.map (fun _ : Fin n => Matrix.mulVecLin g₂.val))
    have : (fun _ : Fin n => Matrix.mulVecLin (R := k) (g₁.val * g₂.val)) =
        (fun _ : Fin n => (Matrix.mulVecLin g₁.val).comp (Matrix.mulVecLin g₂.val)) :=
      funext fun _ => Matrix.mulVecLin_mul g₁.val g₂.val
    rw [this, PiTensorProduct.map_comp]

/-! ### GL action commutes with Young symmetrizer -/

/-- The GL_N diagonal action commutes with the Young symmetrizer endomorphism.
The GL action commutes with each permutation operator σ ∈ S_n by
`symGroupAction_comm_diagonalAction`, hence with any element of k[S_n],
hence with the Young symmetrizer. -/
theorem glTensor_comm_youngSym (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    glTensorRep k N (∑ i, lam i) g ∘ₗ youngSymEndomorphism k N lam =
    youngSymEndomorphism k N lam ∘ₗ glTensorRep k N (∑ i, lam i) g := by
  set n := ∑ i, lam i
  set V := Fin N → k
  set f : V →ₗ[k] V := Matrix.mulVecLin g.val
  -- The Young symmetrizer endomorphism is in symGroupImage (range of symGroupAlgHom)
  have h_sym : (youngSymEndomorphism k N lam : Module.End k (TensorPower k V n)) ∈
      (symGroupImage k V n : Set (Module.End k (TensorPower k V n))) := by
    rw [← symGroupAlgHom_range k V n]
    exact ⟨_, rfl⟩
  -- The GL tensor action is in diagonalActionImage (generated by PiTensorProduct.map f)
  have h_diag : (glTensorRep k N n g : Module.End k (TensorPower k V n)) ∈
      (diagonalActionImage k V n : Set (Module.End k (TensorPower k V n))) := by
    apply Algebra.subset_adjoin
    exact ⟨f, rfl⟩
  -- By diagonalActionImage_le_centralizer_symGroupImage, diagonal elements
  -- commute with all symmetric group elements
  have hcent := diagonalActionImage_le_centralizer_symGroupImage k V n h_diag
  rw [Subalgebra.mem_centralizer_iff] at hcent
  -- Get commutativity: young * g_tensor = g_tensor * young
  exact (hcent _ h_sym).symm

/-- The image of the Young symmetrizer is GL_N-stable. -/
theorem glTensorRep_mem_range (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (v : TensorPower k (Fin N → k) (∑ i, lam i))
    (hv : v ∈ LinearMap.range (youngSymEndomorphism k N lam)) :
    (glTensorRep k N (∑ i, lam i) g) v ∈ LinearMap.range (youngSymEndomorphism k N lam) := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨(glTensorRep k N (∑ i, lam i) g) w,
    (LinearMap.ext_iff.mp (glTensor_comm_youngSym k N lam g) w).symm⟩

/-! ### Schur module construction -/

/-- The Schur module as a submodule of `V^{⊗n}`: the image of the Young symmetrizer. -/
def SchurModuleSubmodule (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Submodule k (TensorPower k (Fin N → k) (∑ i, lam i)) :=
  LinearMap.range (youngSymEndomorphism k N lam)

/-- The GL_N(k) representation restricted to the Schur module submodule.
The representation sends `g` to the restriction of `g^{⊗n}` to the image
of the Young symmetrizer, which is stable because GL_N commutes with S_n. -/
def schurModuleRep (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (SchurModuleSubmodule k N lam) where
  toFun g := (glTensorRep k N (∑ i, lam i) g).restrict
    (p := SchurModuleSubmodule k N lam) (q := SchurModuleSubmodule k N lam)
    (fun v hv => glTensorRep_mem_range k N lam g v hv)
  map_one' := by
    ext ⟨v, hv⟩
    simp only [LinearMap.restrict_coe_apply]
    exact LinearMap.ext_iff.mp (map_one (glTensorRep k N _)) v
  map_mul' g₁ g₂ := by
    ext ⟨v, hv⟩
    -- After ext, both sides coerce to elements of TensorPower via restrict_coe_apply
    have h_mul := LinearMap.ext_iff.mp (map_mul (glTensorRep k N (∑ i, lam i)) g₁ g₂) v
    -- h_mul : (glTensorRep (g₁ * g₂)) v = (glTensorRep g₁ * glTensorRep g₂) v
    --       = (glTensorRep g₁) ((glTensorRep g₂) v)
    -- Goal: coercion of restrict(g₁*g₂) = coercion of (restrict(g₁) * restrict(g₂))
    simp only [LinearMap.restrict_coe_apply, Module.End.mul_apply] at h_mul ⊢
    exact h_mul

/-- The Schur module submodule is finite-dimensional. -/
instance schurModuleSubmodule_finite (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ) :
    Module.Finite k (SchurModuleSubmodule k N lam) :=
  inferInstance

/-- The Schur module `L_λ`: the irreducible polynomial representation of `GL_N(k)`
with highest weight `λ = (λ₁ ≥ ⋯ ≥ λ_N ≥ 0)`.

Constructed as the image of the Young symmetrizer `c_λ` acting on the tensor
power `(k^N)^{⊗n}` where `n = ∑ λᵢ`. The `GL_N(k)`-action is the restriction
of the diagonal action `g ↦ g^{⊗n}`, which commutes with the `S_n`-action
(and hence with `c_λ`), making the image `GL_N`-stable. -/
def SchurModule (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ) (lam : Fin N → ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (schurModuleRep k N lam)

/-! ### Diagonal torus and weight spaces -/

/-- The diagonal matrix in `GL_N(k)` with `t` at position `(i,i)` and `1` elsewhere.
This embeds a single coordinate of the maximal torus `(k×)^N ↪ GL_N(k)`. -/
noncomputable def diagUnit (k : Type*) [Field k] (N : ℕ) (i : Fin N) (t : kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (Function.update 1 i (t : k))
  inv := Matrix.diagonal (Function.update 1 i ((t⁻¹ : kˣ) : k))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext j
    by_cases h : j = i
    · subst h; simp [Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext j
    by_cases h : j = i
    · subst h; simp [Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne h]

/-- The weight space `M_μ` for weight `μ : Fin N → ℕ` in a `GL_N(k)`-representation `M`.
This is the subspace of `M` where the diagonal matrix with `t` at position `i`
acts as scalar multiplication by `t ^ μ i`, for each `i` and all `t ∈ k×`. -/
noncomputable def glWeightSpace (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) : Submodule k M :=
  ⨅ (i : Fin N) (t : kˣ),
    LinearMap.ker (M.ρ (diagUnit k N i t) - ((t : k) ^ μ i) • LinearMap.id)

/-! ### Diagonal matrices commute -/

/-- Diagonal matrices with entries modified at different positions commute. -/
theorem diagUnit_comm (k : Type*) [Field k] (N : ℕ) (i₁ : Fin N) (t₁ : kˣ)
    (i₂ : Fin N) (t₂ : kˣ) :
    diagUnit k N i₁ t₁ * diagUnit k N i₂ t₂ = diagUnit k N i₂ t₂ * diagUnit k N i₁ t₁ := by
  ext : 1
  change (diagUnit k N i₁ t₁).val * (diagUnit k N i₂ t₂).val =
    (diagUnit k N i₂ t₂).val * (diagUnit k N i₁ t₁).val
  simp only [diagUnit, Matrix.diagonal_mul_diagonal, mul_comm]

/-- The representation of two diagUnit elements commutes. -/
theorem rep_diagUnit_commute (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (i₁ : Fin N) (t₁ : kˣ) (i₂ : Fin N) (t₂ : kˣ) :
    Commute (M.ρ (diagUnit k N i₁ t₁)) (M.ρ (diagUnit k N i₂ t₂)) := by
  change M.ρ (diagUnit k N i₁ t₁) * M.ρ (diagUnit k N i₂ t₂) =
    M.ρ (diagUnit k N i₂ t₂) * M.ρ (diagUnit k N i₁ t₁)
  rw [← map_mul, ← map_mul, diagUnit_comm]

/-! ### Weight space is contained in eigenspace -/

/-- The weight space is contained in the maximal generalized eigenspace of each
torus operator. Proved by extracting the (i, t) component from the iInf. -/
theorem glWeightSpace_le_maxGenEigenspace (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (i : Fin N) (t : kˣ) :
    glWeightSpace k N M μ ≤
      Module.End.maxGenEigenspace (M.ρ (diagUnit k N i t)) ((t : k) ^ μ i) := by
  intro v hv
  -- Extract the (i, t) component: v ∈ ker(ρ(diagUnit i t) - t^(μ i) • id)
  have h1 : glWeightSpace k N M μ ≤ ⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ i
  have h2 : ⨅ (s : kˣ),
      LinearMap.ker (M.ρ (diagUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) ≤
      LinearMap.ker (M.ρ (diagUnit k N i t) - ((t : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ t
  have hker := LinearMap.mem_ker.mp (h2 (h1 hv))
  -- hker says (ρ(diagUnit i t) - t^(μ i) • id) v = 0, so ρ(diagUnit i t) v = t^(μ i) • v
  have hev : (M.ρ (diagUnit k N i t)) v = ((t : k) ^ μ i) • v := by
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hker
  -- This means v is an eigenvector, hence in the maxGenEigenspace
  exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hev)

/-! ### Finiteness of weight support -/

/-- In an algebraically closed field (hence infinite), for any n ≥ 1 there exists
a unit t such that t^n ≠ 1. -/
theorem exists_unit_pow_ne_one (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ) (hn : n ≥ 1) :
    ∃ t : kˣ, (t : k) ^ n ≠ 1 := by
  by_contra h; push_neg at h
  -- Every nonzero element of k is a root of X^n - C 1
  have hp_ne : (Polynomial.X ^ n - Polynomial.C (1 : k)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by omega) 1
  -- The roots of X^n - 1 form a finite set
  have hfin : {a : k | a ^ n = 1}.Finite := by
    apply ((Polynomial.X ^ n - Polynomial.C (1 : k)).rootSet_finite k).subset
    intro a (ha : a ^ n = 1)
    rw [Polynomial.mem_rootSet]
    exact ⟨hp_ne, by simp [ha]⟩
  -- But every nonzero element of k satisfies x^n = 1
  have hsub : {a : k | a ≠ 0} ⊆ {a : k | a ^ n = 1} :=
    fun a ha => by simpa using h (Units.mk0 a ha)
  -- The set of nonzero elements is infinite (k is algebraically closed hence infinite)
  have hinf : Set.Infinite {a : k | a ≠ 0} := by
    rw [show {a : k | a ≠ 0} = ({0} : Set k)ᶜ from by ext; simp]
    exact (Set.finite_singleton _).infinite_compl
  exact hinf.not_finite (hfin.subset hsub)

/-- In an algebraically closed (hence infinite) field, distinct natural number exponents
give distinct power functions: if a ≠ b, there exists t ∈ kˣ with t^a ≠ t^b. -/
theorem exists_unit_pow_ne (k : Type*) [Field k] [IsAlgClosed k] {a b : ℕ} (hab : a ≠ b) :
    ∃ t : kˣ, (t : k) ^ a ≠ (t : k) ^ b := by
  -- Reduce to the case a > b
  suffices ∀ {a b : ℕ}, a > b → ∃ t : kˣ, (t : k) ^ a ≠ (t : k) ^ b from by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · obtain ⟨t, ht⟩ := this h; exact ⟨t, ht.symm⟩
    · exact this h
  intro a b h
  obtain ⟨t, ht⟩ := exists_unit_pow_ne_one k (a - b) (by omega)
  refine ⟨t, fun heq => ht ?_⟩
  have hne : (t : k) ^ b ≠ 0 := pow_ne_zero _ (Units.ne_zero t)
  have : (t : k) ^ (a - b) * (t : k) ^ b = 1 * (t : k) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel h.le, heq, one_mul]
  exact mul_right_cancel₀ hne this

/-- The set of weights with nonzero weight space is finite for any finite-dimensional
`GL_N(k)`-representation. -/
theorem glWeightSpace_finite_support (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    { μ : Fin N →₀ ℕ | glWeightSpace k N M (fun i => μ i) ≠ ⊥ }.Finite := by
  -- Define the family of operators indexed by (Fin N × kˣ)
  set f : Fin N × kˣ → Module.End k M := fun p => M.ρ (diagUnit k N p.1 p.2) with hf_def
  -- The operators commute, so they satisfy the MapsTo condition
  have h_comm : ∀ (p₁ p₂ : Fin N × kˣ), Commute (f p₁) (f p₂) :=
    fun p₁ p₂ => rep_diagUnit_commute k N M p₁.1 p₁.2 p₂.1 p₂.2
  have h_mapsTo : ∀ (p₁ p₂ : Fin N × kˣ) (φ : k),
      Set.MapsTo (f p₁)
        ((f p₂).maxGenEigenspace φ) ((f p₂).maxGenEigenspace φ) :=
    fun p₁ p₂ φ => Module.End.mapsTo_maxGenEigenspace_of_comm (h_comm p₂ p₁) φ
  -- By Pi.lean, the simultaneous maximal generalized eigenspaces are independent
  have h_indep := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo
  -- By Noetherian, only finitely many are nonzero
  have h_fin := Submodule.finite_ne_bot_of_iSupIndep h_indep
  -- The weight space for μ is contained in the simultaneous maxGenEigenspace for χ_μ
  -- where χ_μ(i, t) = t^(μ i)
  -- Define the eigenvalue map
  set χ : (Fin N →₀ ℕ) → (Fin N × kˣ → k) :=
    fun μ p => (p.2 : k) ^ (μ p.1) with hχ_def
  -- Show the map is injective
  have h_inj : Function.Injective χ := by
    intro μ₁ μ₂ heq
    ext i
    by_contra hi
    obtain ⟨t, ht⟩ := exists_unit_pow_ne k hi
    exact ht (congr_fun heq (i, t))
  -- Show glWeightSpace μ ≤ ⨅ p, maxGenEigenspace(f p, χ μ p)
  have h_le : ∀ (μ : Fin N →₀ ℕ),
      glWeightSpace k N M (fun i => μ i) ≤
        ⨅ (p : Fin N × kˣ), (f p).maxGenEigenspace (χ μ p) := by
    intro μ
    apply le_iInf
    intro ⟨i, t⟩
    exact glWeightSpace_le_maxGenEigenspace k N M (fun j => μ j) i t
  -- If glWeightSpace μ ≠ ⊥, then the simultaneous maxGenEigenspace is also ≠ ⊥
  refine (h_fin.preimage h_inj.injOn).subset ?_
  intro μ hμ
  simp only [Set.mem_setOf_eq] at hμ
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact fun h => hμ (eq_bot_iff.mpr (h ▸ h_le μ))

/-! ### Formal character -/

/-- The formal character of a finite-dimensional polynomial `GL_N(k)`-representation,
as a polynomial in `N` variables over `ℚ`.

For a representation `M`, the formal character is `∑_μ (dim M_μ) · x^μ` where
`M_μ` is the weight space for weight `μ` under the diagonal torus action.
The sum ranges over the finitely many weights with nonzero weight space. -/
noncomputable def formalCharacter (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    MvPolynomial (Fin N) ℚ :=
  have hfin : { μ : Fin N →₀ ℕ |
      glWeightSpace k N M (fun i => μ i) ≠ ⊥ }.Finite :=
    glWeightSpace_finite_support k N M
  hfin.toFinset.sum fun μ =>
    (Module.finrank k (glWeightSpace k N M (fun i => μ i)) : ℚ) •
      MvPolynomial.monomial μ 1

variable (k : Type*) [Field k] [IsAlgClosed k]

/-! ### Coefficient extraction for formal character -/

/-- The coefficient of `x^μ` in the formal character equals the dimension of the weight space. -/
theorem formalCharacter_coeff (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N →₀ ℕ) :
    (formalCharacter k N M).coeff μ =
      (Module.finrank k (glWeightSpace k N M (fun i => μ i)) : ℚ) := by
  unfold formalCharacter
  have key : ∀ (S : Finset (Fin N →₀ ℕ)) (c : (Fin N →₀ ℕ) → ℚ),
      (S.sum fun ν => c ν • MvPolynomial.monomial ν (1 : ℚ)).coeff μ =
        if μ ∈ S then c μ else 0 := by
    intro S c
    simp only [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    split_ifs with h
    · rw [Finset.sum_eq_single μ]
      · simp
      · intro ν _ hne; exact if_neg hne
      · intro h'; exact absurd h h'
    · exact Finset.sum_eq_zero fun ν hν => by
        rw [if_neg]; exact fun heq => h (heq ▸ hν)
  rw [key]
  split_ifs with hmem
  · rfl
  · have hbot : glWeightSpace k N M (fun i => μ i) = ⊥ := by
      by_contra h
      exact hmem ((glWeightSpace_finite_support k N M).mem_toFinset.mpr h)
    rw [hbot]; simp

/-! ### The Vandermonde determinant is nonzero -/

/-- The alternant determinant with Vandermonde exponents is associated to the product of
linear factors `∏_{i<j} (X_j - X_i)`. -/
private theorem alternant_det_associated_prod' (N : ℕ) :
    Associated (alternantMatrix N (vandermondeExps N)).det
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) := by
  have h1 : alternantMatrix N (vandermondeExps N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, vandermondeExps, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]
  have hu : IsUnit (↑↑(@Fin.revPerm N).sign : MvPolynomial (Fin N) ℚ) :=
    (Units.map (algebraMap ℤ (MvPolynomial (Fin N) ℚ)).toMonoidHom
      (@Fin.revPerm N).sign).isUnit
  exact (associated_isUnit_mul_left_iff hu).mpr (Associated.refl _)

/-- The Vandermonde determinant is nonzero in `MvPolynomial (Fin N) ℚ`. -/
theorem alternantMatrix_vandermondeExps_det_ne_zero (N : ℕ) :
    (alternantMatrix N (vandermondeExps N)).det ≠ (0 : MvPolynomial (Fin N) ℚ) := by
  obtain ⟨u, hu⟩ := alternant_det_associated_prod' N
  intro h
  have hprod : ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
    intro heq
    -- X_j - X_i = 0 would mean X_j = X_i, but they are distinct variables
    have : (MvPolynomial.eval (fun k : Fin N => if k = j then (1 : ℚ) else 0))
        (MvPolynomial.X j - MvPolynomial.X i) = 0 :=
      congr_arg _ heq |>.trans (map_zero _)
    simp [hij.symm] at this
  exact hprod (by rw [← hu, h, zero_mul])

/-! ### Helper lemma for the Weyl character formula -/

/- **Core identity**: The formal character of the Schur module equals the Schur polynomial.

This is the central content of the Weyl character formula:
  `ch(L_λ) = s_λ(x₁, …, x_N)`

## Proof strategy (via trace on tensor power)

1. **Scalar idempotent**: The Young symmetrizer `c_λ ∈ ℚ[S_n]` satisfies `c_λ² = α · c_λ`
   for some nonzero `α : ℚ`. This follows from the sandwich property
   `a_λ · x · b_λ = ℓ(x) · c_λ` (Lemma 5.13.1, currently proved over ℂ,
   needs generalization to ℚ).

2. **Trace formula**: Since `(1/α) · c_λ` is an idempotent projector onto `Im(c_λ) = L_λ`,
   `ch(L_λ) = (1/α) · ∑_{π ∈ S_n} c_λ(π) · permTracePoly(N, π)`
   where `permTracePoly(N, π)` is the power-sum product for π's cycle type
   (`permTracePoly_eq_powerSumCycleProduct`, proved in PermDiagonalTrace.lean).

3. **Character orthogonality**: Group the sum by conjugacy class (= cycle type μ),
   apply the Frobenius formula (`Proposition5_21_1`, proved), and use
   character orthogonality for S_n to collapse the sum:
   `∑_π c_λ(π) · permTracePoly(N, π) = α · s_λ(x)`

4. **Cancel α**: Combine steps 2-3 to get `ch(L_λ) = (1/α) · α · s_λ = s_λ`.

**Key dependencies**:
- `permTracePoly_eq_powerSumCycleProduct` (proved)
- `Proposition5_21_1` (Frobenius formula, proved)
- Lemma 5.13.1 sandwich property over ℚ (not yet generalized from ℂ)
- Character orthogonality for S_n (not yet formalized) -/

/-! #### Young symmetrizer endomorphism: idempotent property -/

/-- The Young symmetrizer endomorphism satisfies `E² = α • E` over any field k. -/
theorem youngSymEndomorphism_sq_scalar (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k)
    (hα_sq : YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam)) :
    youngSymEndomorphism k N lam * youngSymEndomorphism k N lam =
      α • youngSymEndomorphism k N lam := by
  unfold youngSymEndomorphism
  rw [← map_mul, hα_sq, map_smul]

/-- The SchurModuleSubmodule equals the range of `youngSymEndomorphism` composed with itself
(up to scalar), since E² = α • E means im(E) = im(E²) = im(α • E). -/
theorem youngSymEndomorphism_range_eq_sq_range (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam)) :
    SchurModuleSubmodule k N lam = LinearMap.range (youngSymEndomorphism k N lam *
      youngSymEndomorphism k N lam) := by
  unfold SchurModuleSubmodule
  rw [show youngSymEndomorphism k N lam * youngSymEndomorphism k N lam =
    α • youngSymEndomorphism k N lam from youngSymEndomorphism_sq_scalar k N lam α hα_sq]
  ext v; simp [LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨α⁻¹ • w, by rw [map_smul, smul_comm, inv_smul_smul₀ hα]⟩
  · rintro ⟨w, rfl⟩; exact ⟨α • w, by rw [map_smul]⟩

/-- On the image of the Young symmetrizer, the endomorphism acts as scalar multiplication
by α. That is, for v ∈ im(E), E(v) = α • v. -/
theorem youngSymEndomorphism_apply_on_range (k : Type*) [Field k] (N : ℕ) (lam : Fin N → ℕ)
    (α : k)
    (hα_sq : YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK k (∑ i, lam i) (weightToPartition N lam))
    (v : TensorPower k (Fin N → k) (∑ i, lam i))
    (hv : v ∈ SchurModuleSubmodule k N lam) :
    youngSymEndomorphism k N lam v = α • v := by
  obtain ⟨w, rfl⟩ := hv
  show (youngSymEndomorphism k N lam * youngSymEndomorphism k N lam) w = α • youngSymEndomorphism k N lam w
  rw [youngSymEndomorphism_sq_scalar k N lam α hα_sq]
  rfl

/-! #### Step 1: Formal character via trace of Young symmetrizer

The Schur module `L_λ = Im(c_λ)` where `c_λ² = α · c_λ`. So `(1/α) · c_λ` is
an idempotent projector, and the formal character equals the trace of this
projector against the diagonal GL action:

  `ch(L_λ) = (1/α) · ∑_{σ ∈ S_n} c_λ(σ) · Tr(σ acting on V^{⊗n} restricted to diagonal)`

where the trace of σ acting on `V^{⊗n}` restricted to a diagonal matrix `diag(x₁,…,x_N)`
gives `permTracePoly N σ`. -/

/-- The normalized Young symmetrizer `α⁻¹ • E` is an idempotent projection
onto the Schur module submodule. -/
private theorem youngSymEndomorphism_normalized_isProj
    (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (α : k') (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam)) :
    LinearMap.IsProj (SchurModuleSubmodule k' N lam) (α⁻¹ • youngSymEndomorphism k' N lam) where
  map_mem x := by
    simp only [LinearMap.smul_apply, SchurModuleSubmodule, LinearMap.mem_range]
    exact ⟨α⁻¹ • x, by rw [map_smul]⟩
  map_id x hx := by
    simp only [LinearMap.smul_apply]
    rw [youngSymEndomorphism_apply_on_range k' N lam α hα_sq x hx]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

/-- The normalized Young symmetrizer is idempotent. -/
private theorem youngSymEndomorphism_normalized_isIdempotent
    (k' : Type*) [Field k'] (N : ℕ) (lam : Fin N → ℕ)
    (α : k') (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK k' (∑ i, lam i) (weightToPartition N lam)) :
    IsIdempotentElem (α⁻¹ • youngSymEndomorphism k' N lam) :=
  (youngSymEndomorphism_normalized_isProj k' N lam α hα hα_sq).isIdempotentElem

/-- The trace of the normalized Young symmetrizer on V⊗n equals the dimension of the
Schur module. This follows from `IsProj.trace`. -/
private theorem trace_normalized_youngSym_eq_finrank
    (N : ℕ) (lam : Fin N → ℕ)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam)) :
    LinearMap.trace ℚ _ (α⁻¹ • youngSymEndomorphism ℚ N lam) =
      (Module.finrank ℚ (SchurModuleSubmodule ℚ N lam) : ℚ) :=
  (youngSymEndomorphism_normalized_isProj ℚ N lam α hα hα_sq).trace

/-! #### Tensor weight infrastructure for the coefficient identity -/

/-- The weight of a tensor basis element `f : Fin n → Fin N`: counts how many times
each color `i : Fin N` appears in the coloring `f`. -/
private def tensorWeight (N : ℕ) {n : ℕ} (f : Fin n → Fin N) : Fin N →₀ ℕ where
  toFun i := (Finset.univ.filter (fun j => f j = i)).card
  support := Finset.univ.filter (fun i => 0 < (Finset.univ.filter (fun j => f j = i)).card)
  mem_support_toFun i := by simp [Finset.card_pos, Finset.filter_nonempty_iff]

/-- The monomial `∏_j X_{f(j)}` equals `X^{tensorWeight f}`. -/
private lemma prod_X_eq_monomial_tensorWeight (N : ℕ) {n : ℕ} (f : Fin n → Fin N) :
    ∏ j : Fin n, (MvPolynomial.X (f j) : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.monomial (tensorWeight N f) 1 := by
  -- ∏_j X_{f(j)} = ∏_{i : Fin N} X_i ^ #{j : f(j) = i}
  rw [← Finset.prod_fiberwise_of_maps_to (g := f) (fun _ _ => Finset.mem_univ _)]
  -- Within each fiber, X(f j) = X i since f j = i
  have hfiber : ∀ i ∈ Finset.univ (α := Fin N),
      ∏ j ∈ Finset.univ.filter (fun k => f k = i),
        (MvPolynomial.X (f j) : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.X i ^ (Finset.univ.filter (fun k => f k = i)).card := by
    intro i _
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
        Finset.prod_const]
  rw [Finset.prod_congr rfl hfiber]
  -- Goal: ∏ i, X i ^ card(filter(f = i)) = monomial (tensorWeight N f) 1
  symm
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [tensorWeight]

/-- The coefficient of `x^μ` in a monomial `x^w` is `1` if `w = μ` and `0` otherwise. -/
private lemma coeff_monomial_one (N : ℕ) (w μ : Fin N →₀ ℕ) :
    (MvPolynomial.monomial w (1 : ℚ)).coeff μ = if w = μ then 1 else 0 := by
  simp [MvPolynomial.coeff_monomial]

/-- The coefficient of `x^μ` in `permTracePoly N σ` equals the number of `σ`-fixed
colorings `f : Fin n → Fin N` with `tensorWeight N f = μ`. -/
private lemma permTracePoly_coeff_eq_card (N : ℕ) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (μ : Fin N →₀ ℕ) :
    (permTracePoly N σ).coeff μ =
      ((Finset.univ.filter fun f : Fin n → Fin N =>
        (∀ j, f (σ j) = f j) ∧ tensorWeight N f = μ).card : ℚ) := by
  unfold permTracePoly
  rw [MvPolynomial.coeff_sum]
  -- Each summand contributes 1 if weight = μ, else 0
  simp_rw [prod_X_eq_monomial_tensorWeight, coeff_monomial_one]
  -- ∑_{f ∈ fixed} (if weight(f) = μ then 1 else 0) = #{f ∈ fixed : weight(f) = μ}
  rw [Finset.sum_boole, Nat.cast_inj]
  -- LHS: (fixed.filter(weight = μ)).card, RHS: (univ.filter(fixed ∧ weight = μ)).card
  rw [Finset.filter_filter]

/-- **Weight space dimension = trace formula**: The finrank of the `k`-weight space
of the Schur module equals the ℚ-valued normalized trace on the tensor weight subspace.

This encapsulates the following chain of reasoning:
(a) Standard tensor basis elements `e_f` are eigenvectors for the diagonal torus with
    eigenvalue `t^(#{j : f(j) = i})` for `diagUnit(i, t)`.
(b) The weight-`μ` subspace of `V^{⊗n}` is `span{e_f : tensorWeight f = μ}`.
(c) The Young symmetrizer `E` preserves weight spaces (it commutes with the torus).
(d) `(1/α)E` restricted to the weight-`μ` subspace is an `IsProj` onto the weight-`μ`
    subspace of `L_λ = Im(E)`.
(e) By `IsProj.trace`, `finrank(Im) = tr((1/α)E|_{W_μ})`.
(f) `tr((1/α)E|_{W_μ}) = (1/α) · ∑_σ c_λ(σ) · #{f : weight(f) = μ, f ∘ σ = f}` by
    linearity and the fact that σ acts as a permutation matrix on the standard basis.
(g) Base change: `finrank_k = finrank_ℚ` because the Young symmetrizer is defined
    over ℤ and the rank of an integer matrix is field-independent in char 0. -/
private lemma finrank_weight_eq_card_sum
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam))
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) : ℚ) =
      α⁻¹ * ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) *
          ((Finset.univ.filter fun f : Fin (∑ i, lam i) → Fin N =>
            (∀ j, f (σ j) = f j) ∧ tensorWeight N f = μ).card : ℚ) := by
  sorry

/-- **Key coefficient identity**: the weight space dimension of `L_λ` at weight `μ` equals
the trace formula coefficient `α⁻¹ · ∑_σ c_λ(σ) · [x^μ](permTracePoly N σ)`.

Proved by combining `finrank_weight_eq_card_sum` (trace formula) with
`permTracePoly_coeff_eq_card` (coefficient = counting). -/
private theorem weight_trace_coefficient_identity
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam))
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) : ℚ) =
      α⁻¹ * ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) *
          (permTracePoly N σ).coeff μ := by
  rw [finrank_weight_eq_card_sum k N lam hlam α hα hα_sq μ]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (permTracePoly_coeff_eq_card N σ μ).symm

/-- **Trace formula**: The formal character of the Schur module equals
`α⁻¹ · ∑_{σ ∈ S_n} c_λ(σ) · permTracePoly(N, σ)`.

Proved by reducing to the coefficient-level identity
`weight_trace_coefficient_identity`, which equates the weight space dimension
to the normalized trace formula coefficient. -/
theorem formalCharacter_schurModule_eq_sum_permTracePoly
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam)) :
    formalCharacter k N (SchurModule k N lam) =
      α⁻¹ • ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
        (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) •
          permTracePoly N σ := by
  ext μ
  rw [formalCharacter_coeff]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_sum]
  exact weight_trace_coefficient_identity k N lam hlam α hα hα_sq μ

/-! #### Bridge: cycle type partition and power sum connection -/

/-- The full cycle type of σ forms a partition of n. -/
noncomputable def fullCycleTypePartition {n : ℕ} (σ : Equiv.Perm (Fin n)) : Nat.Partition n where
  parts := fullCycleType n σ
  parts_pos hi := fullCycleType_pos σ _ hi
  parts_sum := fullCycleType_sum n σ

/-- `powerSumCycleProduct` equals `psumPart` of the full cycle type partition. -/
theorem powerSumCycleProduct_eq_psumPart {n : ℕ} (N : ℕ) (σ : Equiv.Perm (Fin n)) :
    powerSumCycleProduct N σ = MvPolynomial.psumPart (Fin N) ℚ (fullCycleTypePartition σ) := by
  unfold powerSumCycleProduct MvPolynomial.psumPart fullCycleTypePartition
  rfl

/-- Convert a weight `lam : Fin N → ℕ` with `Antitone lam` to a `BoundedPartition`. -/
def weightToBP (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    BoundedPartition N (∑ i, lam i) where
  parts := lam
  decreasing := hlam
  sum_eq := rfl

/-! #### Helper: trace of multiplication in group algebra -/

set_option maxHeartbeats 800000 in
/-- The trace of left multiplication by `c` in `MonoidAlgebra ℚ G` equals `|G| · c(1)`. -/
private theorem monoidAlgebra_trace_mulLeft_eq'
    {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (c : MonoidAlgebra ℚ G) :
    LinearMap.trace ℚ _ (LinearMap.mulLeft ℚ c) =
      Fintype.card G * c 1 := by
  set b := MonoidAlgebra.basis G ℚ
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ σ : G, b.repr (LinearMap.mulLeft ℚ c (b σ)) σ = c 1 := by
    intro σ
    rw [LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]
    have hrepr : ∀ (x : MonoidAlgebra ℚ G) (g : G), b.repr x g = x g := fun _ _ => rfl
    rw [hrepr, MonoidAlgebra.mul_single_apply, mul_one, mul_inv_cancel]
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option maxHeartbeats 800000 in
/-- The scalar `α` from `c_λ² = α · c_λ` is nonzero. If `α = 0` then `c² = 0`,
so left multiplication by `c` is nilpotent with trace 0, but the trace equals `n!`. -/
theorem YoungSymmetrizerK_sq_scalar_ne_zero
    (n : ℕ) (la : Nat.Partition n)
    (α : ℚ)
    (hα_sq : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    α ≠ 0 := by
  intro h0
  rw [h0, zero_smul] at hα_sq
  set c := YoungSymmetrizerK ℚ n la with hc_def
  have hnil : IsNilpotent (LinearMap.mulLeft ℚ c) := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    change (LinearMap.mulLeft ℚ c) ((LinearMap.mulLeft ℚ c) x) = 0
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, hα_sq, zero_mul]
  have htr_nil := LinearMap.isNilpotent_trace_of_isNilpotent hnil
  rw [isNilpotent_iff_eq_zero] at htr_nil
  rw [monoidAlgebra_trace_mulLeft_eq'] at htr_nil
  have hone : c 1 = 1 := by
    rw [hc_def, YoungSymmetrizerK_eq_mapRange ℚ n la]
    simp [MonoidAlgebra.mapRangeRingHom_apply, YoungSymmetrizerZ_apply_one]
  rw [hone, mul_one] at htr_nil
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (by rwa [Fintype.card_perm, Fintype.card_fin] at htr_nil)

/-! #### Inlined trace-Kronecker identity for the bridge

We inline the key parts of the `youngSym_trace_kronecker` proof here
to avoid circular imports (YoungSymTraceKronecker.lean imports this file). -/

/-- Coefficient transfer: ℚ and ℂ Young symmetrizer coefficients agree under cast. -/
private lemma youngSym_coeff_cast' (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (YoungSymmetrizerK ℚ n la σ : ℂ) = YoungSymmetrizer n la σ := by
  rw [YoungSymmetrizerK_eq_mapRange ℚ n la, YoungSymmetrizer_eq_mapRange n la]
  simp only [MonoidAlgebra.mapRangeRingHom_apply]
  exact_mod_cast rfl

/-- Transfer `c² = α·c` from ℚ to ℂ via the ℤ base change. -/
private lemma youngSym_sq_ℂ' (n : ℕ) (la : Nat.Partition n)
    (α : ℚ) (hα : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    YoungSymmetrizer n la * YoungSymmetrizer n la = (α : ℂ) • YoungSymmetrizer n la := by
  set cZ := YoungSymmetrizerZ n la
  set β : ℤ := (cZ * cZ) 1
  set φ_ℚ := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
  set φ_ℂ := MonoidAlgebra.mapRangeRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℂ)
  have h_ℚ : YoungSymmetrizerK ℚ n la = φ_ℚ cZ := YoungSymmetrizerK_eq_mapRange ℚ n la
  have h_ℂ : YoungSymmetrizer n la = φ_ℂ cZ := YoungSymmetrizer_eq_mapRange n la
  have hcZ1 : cZ 1 = 1 := YoungSymmetrizerZ_apply_one n la
  have hmul_ℚ : φ_ℚ (cZ * cZ) = α • φ_ℚ cZ := by rw [map_mul]; exact h_ℚ ▸ hα
  have hα_eq : α = (β : ℚ) := by
    have h1 := Finsupp.ext_iff.mp hmul_ℚ 1
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hcZ1, map_one, mul_one, φ_ℚ] at h1
    exact h1.symm
  have hZ : cZ * cZ = β • cZ := by
    ext σ
    have h1 := Finsupp.ext_iff.mp hmul_ℚ σ
    simp only [MonoidAlgebra.mapRangeRingHom_apply, MonoidAlgebra.smul_apply,
      smul_eq_mul, hα_eq, φ_ℚ] at h1
    have h2 : ((cZ * cZ) σ : ℚ) = ((β * cZ σ : ℤ) : ℚ) := by push_cast; exact h1
    have h3 : (cZ * cZ) σ = β * cZ σ := Int.cast_injective h2
    rw [MonoidAlgebra.smul_apply, smul_eq_mul, h3]
  rw [h_ℂ, ← map_mul, hZ, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1; exact_mod_cast hα_eq.symm

/-- Left multiplication on the Specht module. -/
private def mulLeftOnSpecht' (n : ℕ) (c : SymGroupAlgebra n) (la' : Nat.Partition n) :
    ↥(SpechtModule n la') →ₗ[ℂ] ↥(SpechtModule n la') where
  toFun v := ⟨c * ↑v, (SpechtModule n la').smul_mem c v.prop⟩
  map_add' a b := Subtype.ext (mul_add c ↑a ↑b)
  map_smul' r v := Subtype.ext (Algebra.mul_smul_comm r c ↑v)

private lemma mulLeftOnSpecht_of' (n : ℕ) (la' : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    mulLeftOnSpecht' n (MonoidAlgebra.of ℂ _ σ) la' = spechtModuleAction n la' σ := by
  ext ⟨m, hm⟩; rfl

private noncomputable def mulLeftOnSpechtLinear' (n : ℕ) (la' : Nat.Partition n) :
    SymGroupAlgebra n →ₗ[ℂ] (↥(SpechtModule n la') →ₗ[ℂ] ↥(SpechtModule n la')) where
  toFun c := mulLeftOnSpecht' n c la'
  map_add' a b := by ext ⟨m, hm⟩; simp [mulLeftOnSpecht', add_mul]
  map_smul' r c := by ext ⟨m, hm⟩; simp [mulLeftOnSpecht']

/-- Trace linearity: ∑_σ c(σ) · χ_{V}(σ) = trace of left mult by c on V. -/
private lemma sum_coeff_char_eq_trace' (n : ℕ) (la' : Nat.Partition n) (c : SymGroupAlgebra n) :
    ∑ σ : Equiv.Perm (Fin n), c σ * spechtModuleCharacter n la' σ =
      LinearMap.trace ℂ _ (mulLeftOnSpecht' n c la') := by
  symm
  have key : (LinearMap.trace ℂ _) (mulLeftOnSpecht' n c la') =
      ∑ σ ∈ c.support, c σ * spechtModuleCharacter n la' σ := by
    have hlin : mulLeftOnSpecht' n c la' = (mulLeftOnSpechtLinear' n la') c := rfl
    rw [hlin]
    simp_rw [spechtModuleCharacter, ← mulLeftOnSpecht_of' n la']
    have hc : c = ∑ σ ∈ c.support, c σ • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ := by
      conv_lhs => rw [← Finsupp.sum_single c]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [MonoidAlgebra.of_apply, Finsupp.smul_single', mul_one]
    conv_lhs => rw [show (mulLeftOnSpechtLinear' n la') c =
        (mulLeftOnSpechtLinear' n la')
          (∑ σ ∈ c.support, c σ • MonoidAlgebra.of ℂ _ σ) from by rw [← hc]]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]; rfl
  rw [key]
  apply Finset.sum_subset (Finset.subset_univ c.support)
  intro σ _ hσ
  have : c σ = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hσ
  simp [this]

/-- Off-diagonal: c_λ acts as 0 on V_{λ'} when λ ≠ λ'. -/
private lemma mulLeft_youngSym_zero_of_ne' (n : ℕ) (la la' : Nat.Partition n) (hne : la ≠ la') :
    mulLeftOnSpecht' n (YoungSymmetrizer n la) la' = 0 := by
  by_contra hT
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : SpechtModule n la',
      mulLeftOnSpecht' n (YoungSymmetrizer n la) la' w₀ ≠ 0 := by
    by_contra hall; push_neg at hall; exact hT (LinearMap.ext hall)
  set φ : SpechtModule n la →ₗ[SymGroupAlgebra n] SpechtModule n la' :=
    { toFun := fun v => ⟨(v : SymGroupAlgebra n) * (w₀ : SymGroupAlgebra n),
        (SpechtModule n la').smul_mem (v : SymGroupAlgebra n) w₀.prop⟩
      map_add' := fun a b => Subtype.ext (add_mul (a : SymGroupAlgebra n) b w₀)
      map_smul' := fun a v => Subtype.ext (mul_assoc a (v : SymGroupAlgebra n) w₀) }
  have hφ_ne : φ ≠ 0 := by
    intro h; apply hw₀
    have : φ ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h) ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩
    simp only [mulLeftOnSpecht', LinearMap.coe_mk, AddHom.coe_mk] at this ⊢; exact this
  haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la) :=
    Theorem5_12_2_irreducible n la
  haveI : IsSimpleModule (SymGroupAlgebra n) (SpechtModule n la') :=
    Theorem5_12_2_irreducible n la'
  have hφ_bij := LinearMap.bijective_of_ne_zero hφ_ne
  exact (Theorem5_12_2_distinct n la la' hne).false (LinearEquiv.ofBijective φ hφ_bij)

/-- Identity coefficient of c_ℂ is 1. -/
private lemma youngSym_coeff_one' (n : ℕ) (la : Nat.Partition n) :
    (YoungSymmetrizer n la : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) 1 = 1 := by
  rw [YoungSymmetrizer_eq_mapRange]
  simp [MonoidAlgebra.mapRangeRingHom_apply, YoungSymmetrizerZ_apply_one]

/-- Sandwich proportionality: c * v = ((c * v)(1)) • c for v ∈ V_λ. -/
private lemma mul_mem_specht_proportional' (n : ℕ) (la : Nat.Partition n)
    (v : ↥(SpechtModule n la)) :
    YoungSymmetrizer n la * v.val =
      (YoungSymmetrizer n la * v.val) 1 • YoungSymmetrizer n la := by
  classical
  set c := YoungSymmetrizer n la
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.prop
  rw [smul_eq_mul] at ha
  obtain ⟨ℓ, hℓ⟩ := Etingof.Lemma5_13_1 n la
  have h_sandwich : ∀ x,
      c * x * c = ℓ (RowSymmetrizer n la * (x * ColumnAntisymmetrizer n la)) • c := by
    intro x
    change ColumnAntisymmetrizer n la * RowSymmetrizer n la * x *
        (ColumnAntisymmetrizer n la * RowSymmetrizer n la) = _
    rw [show ColumnAntisymmetrizer n la * RowSymmetrizer n la * x *
          (ColumnAntisymmetrizer n la * RowSymmetrizer n la) =
        ColumnAntisymmetrizer n la * (RowSymmetrizer n la * x * ColumnAntisymmetrizer n la) *
          RowSymmetrizer n la from by simp only [mul_assoc]]
    rw [hℓ, show c = YoungSymmetrizer n la from rfl]; simp only [YoungSymmetrizer, mul_assoc]
  have hsand := h_sandwich a
  conv_lhs at hsand => rw [mul_assoc]
  conv_lhs => rw [show v.val = a * c from ha.symm, hsand]
  conv_rhs => rw [show v.val = a * c from ha.symm, hsand]
  congr 1; rw [Finsupp.smul_apply, smul_eq_mul, youngSym_coeff_one', mul_one]

/-- Diagonal case: trace of c_λ on V_λ equals α. -/
private lemma trace_mulLeft_youngSym_eq' (n : ℕ) (la : Nat.Partition n)
    (α : ℂ) (_hα_ne : α ≠ 0)
    (hα_sq : YoungSymmetrizer n la * YoungSymmetrizer n la = α • YoungSymmetrizer n la) :
    LinearMap.trace ℂ _ (mulLeftOnSpecht' n (YoungSymmetrizer n la) la) = α := by
  set c := YoungSymmetrizer n la with hc_def
  set V := SpechtModule n la
  set T := mulLeftOnSpecht' n c la
  have hc_mem : c ∈ V := Submodule.subset_span rfl
  set e : V := ⟨c, hc_mem⟩
  let ι : ℂ →ₗ[ℂ] V := LinearMap.lsmul ℂ V |>.flip e
  let π : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => (c * v.val) 1
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun r x => by
        change (c * (r • x.val)) 1 = r * (c * x.val) 1
        rw [Algebra.mul_smul_comm, Finsupp.smul_apply, smul_eq_mul] }
  have hT_eq : T = ι.comp π := by
    apply LinearMap.ext; intro ⟨v, hv⟩; apply Subtype.ext
    exact mul_mem_specht_proportional' n la ⟨v, hv⟩
  rw [hT_eq, LinearMap.trace_comp_comm']
  have h_comp : π.comp ι = α • LinearMap.id := by
    apply LinearMap.ext; intro x
    change (c * (x • c)) 1 = α * x
    rw [Algebra.mul_smul_comm, Finsupp.smul_apply, smul_eq_mul]
    rw [hα_sq, Finsupp.smul_apply, smul_eq_mul, youngSym_coeff_one', mul_one, mul_comm]
  rw [h_comp]; simp [map_smul, LinearMap.trace_id, Module.finrank_self]

/-- Young symmetrizer trace Kronecker (inlined version):
`∑_σ c_λ(σ) · χ_{V_{λ'}}(σ) = α · δ_{λ,λ'}`. -/
private theorem youngSym_trace_kronecker' (n : ℕ) (la la' : Nat.Partition n)
    (α : ℚ) (hα_sq : YoungSymmetrizerK ℚ n la * YoungSymmetrizerK ℚ n la =
      α • YoungSymmetrizerK ℚ n la) :
    ∑ σ : Equiv.Perm (Fin n),
      (YoungSymmetrizerK ℚ n la σ : ℂ) * spechtModuleCharacter n la' σ =
      if la = la' then (α : ℂ) else 0 := by
  conv_lhs => arg 2; ext σ; rw [youngSym_coeff_cast']
  have hα_ℂ := youngSym_sq_ℂ' n la α hα_sq
  have hα_ne : (α : ℂ) ≠ 0 := by exact_mod_cast YoungSymmetrizerK_sq_scalar_ne_zero n la α hα_sq
  rw [sum_coeff_char_eq_trace']
  split_ifs with h
  · subst h; exact trace_mulLeft_youngSym_eq' n la (α : ℂ) hα_ne hα_ℂ
  · rw [mulLeft_youngSym_zero_of_ne' n la la' h, map_zero]

/-! #### Bridge: charValue ↔ spechtModuleCharacter

The Frobenius character formula (Theorem 5.15.1) connects the polynomial
coefficient definition (`charValue` over ℚ with N variables) to the trace
definition (`spechtModuleCharacter` over ℂ with n variables). For N = n,
the connection is exact. For general N, stability of symmetric functions
ensures the character value is independent of the number of variables.

**Key identity chain (for N = n):**
1. `alternantDet n = sign(rev) · ∏_{i<j}(x_j - x_i)` (Vandermonde identity)
2. `charValue = coeff_{λ+ρ}(sign(rev) · vandermonde · psumPart)`
3. Theorem 5.15.1: `sign(rev) · χ = coeff_{λ+ρ}(vandermonde · cyclePsum)`
4. Therefore `charValue = sign(rev)² · χ = χ` since `sign(rev)² = 1`. -/

/-- For antitone `f : Fin n → ℕ`, the sorted parts of `weightToPartition n f` match `f`
at each position. Since `f` is already weakly decreasing, `sort (· ≥ ·)` of the
positive-value multiset gives back the positive values of `f` in order, and `getD`
extends with zeros matching the zero tail of `f`. -/
private lemma sortedParts_getD_eq_of_antitone
    (n : ℕ) (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    ((weightToPartition n f).sortedParts.getD i.val 0 : ℕ) = f i := by
  unfold Nat.Partition.sortedParts weightToPartition
  simp only [Fin.univ_val_map]
  -- Goal: ((↑(List.ofFn f)).filter (0 < ·)).sort (· ≥ ·) |>.getD i.val 0 = f i
  -- Step 1: The filtered list is already sorted (since f is antitone)
  have h_sorted : ((List.ofFn f).filter (0 < ·)).SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    exact List.Pairwise.filter _ (List.sortedGE_ofFn_iff.mpr hf).pairwise
  -- Step 2: sort of a sorted coe is the original list
  -- sort_eq says ↑(sort (↑l) r) = ↑l as multisets
  -- pairwise_sort says sort result is pairwise
  -- eq_of_sortedGE + perm gives list equality
  have h_sort_eq : ((↑(List.ofFn f) : Multiset ℕ).filter (0 < ·)).sort (· ≥ ·) =
      (List.ofFn f).filter (0 < ·) := by
    rw [Multiset.filter_coe]
    have h_perm : ((↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)).Perm
        ((List.ofFn f).filter (0 < ·)) :=
      Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
    have h_sort_sorted : (↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)
        |>.SortedGE := by
      rw [List.sortedGE_iff_pairwise]
      exact Multiset.pairwise_sort _ _
    exact h_perm.eq_of_sortedGE h_sort_sorted h_sorted
  rw [h_sort_eq]
  -- Step 3: getD on filtered list equals f i
  -- For antitone f, positive elements form a prefix of List.ofFn f
  -- Key: filter keeps a prefix, and getD extends with 0
  -- We prove: for antitone f, (ofFn f).filter (0 < ·) = (ofFn f).take k
  -- where k = #{j | 0 < f j}
  -- Then getD i 0 of take k = f i (either i < k and we get f i, or i ≥ k and f i = 0)
  suffices h_filter_eq : ∀ (m : ℕ) (g : Fin m → ℕ), Antitone g →
      ∀ j : Fin m, ((List.ofFn g).filter (0 < ·)).getD j.val 0 = g j by
    exact h_filter_eq n f hf i
  intro m g hg j
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ]
    by_cases hg0 : 0 < g 0
    · -- g 0 > 0, so it passes filter
      simp only [List.filter_cons, decide_eq_true_eq.mpr hg0, ↓reduceIte]
      cases j using Fin.cases with
      | zero => simp [List.getD]
      | succ j' =>
        simp only [List.getD]
        have hgs : Antitone (g ∘ Fin.succ) :=
          fun a b hab => hg (show Fin.succ a ≤ Fin.succ b from Fin.succ_le_succ_iff.mpr hab)
        exact ih (g ∘ Fin.succ) hgs j'
    · -- g 0 = 0
      push_neg at hg0
      have hg0' : g 0 = 0 := Nat.le_zero.mp hg0
      simp only [List.filter_cons, show decide (0 < g 0) = false from
        decide_eq_false (not_lt.mpr hg0), Bool.false_eq_true, ↓reduceIte]
      -- Since g is antitone and g 0 = 0, all g j = 0
      have hall : ∀ k : Fin (m + 1), g k = 0 :=
        fun k => Nat.le_zero.mp (hg0' ▸ hg (Fin.zero_le k))
      -- filter on tail is empty (all values are 0)
      have h_empty : List.filter (fun x => decide (0 < x))
          (List.ofFn (fun i : Fin m => g i.succ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx
        simp [hall k.succ]
      rw [h_empty]; simp [hall j]

/-- The alternant determinant with Vandermonde exponents equals `sign(revPerm)` times the
Vandermonde product. (Local copy; the canonical version is in FrobeniusCharacterBridge.) -/
private theorem alternantDet_eq_sign_mul_vandermondeProd' (N : ℕ) :
    (alternantMatrix N (vandermondeExps N)).det =
      ((Equiv.Perm.sign (@Fin.revPerm N) : ℤ) : MvPolynomial (Fin N) ℚ) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) := by
  have h1 : alternantMatrix N (vandermondeExps N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, vandermondeExps, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]

/-- The shifted exponent vector for a BoundedPartition n n equals the Nat.Partition.toFinsupp
plus the rho shift, connecting `charValue`'s exponent to Theorem 5.15.1's exponent. -/
private lemma shiftedExps_eq_toFinsupp_add_rhoShift
    (n : ℕ) (bp : BoundedPartition n n) :
    Finsupp.equivFunOnFinite.symm (shiftedExps n bp.parts) =
      Nat.Partition.toFinsupp (bp.sum_eq ▸ weightToPartition n bp.parts) + rhoShift n := by
  -- The ▸ transport doesn't change sortedParts
  have h_sorted : (bp.sum_eq ▸ weightToPartition n bp.parts).sortedParts =
      (weightToPartition n bp.parts).sortedParts := by
    -- ▸ on Nat.Partition transports along the sum proof but doesn't change parts/sortedParts
    have : ∀ (m k : ℕ) (h : m = k) (p : Nat.Partition m), (h ▸ p).sortedParts = p.sortedParts := by
      intro m k h p; subst h; rfl
    exact this _ _ bp.sum_eq _
  ext i
  simp only [Finsupp.coe_add, Pi.add_apply,
    Nat.Partition.toFinsupp, rhoShift, shiftedExps,
    Finsupp.coe_equivFunOnFinite_symm, h_sorted]
  congr 1
  exact (sortedParts_getD_eq_of_antitone n bp.parts bp.decreasing i).symm

/-- Base change: `map (algebraMap ℚ ℂ)` sends `psumPart ℚ μ` to `psumPart ℂ μ`. -/
private lemma map_psumPart (n : ℕ) (μ : Nat.Partition n) :
    MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.psumPart (Fin n) ℚ μ) =
      MvPolynomial.psumPart (Fin n) ℂ μ := by
  simp only [MvPolynomial.psumPart, MvPolynomial.psum]
  rw [map_multiset_prod]
  congr 1
  rw [Multiset.map_map]
  congr 1; ext m
  rw [Function.comp_apply, map_sum]
  congr 1; ext i
  simp [map_pow, MvPolynomial.map_X]

/-- `psumPart ℂ (fullCycleTypePartition σ)` equals `cycleTypePsumProduct n σ`. -/
private lemma psumPart_fullCycleType_eq_cycleTypePsumProduct
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.psumPart (Fin n) ℂ (fullCycleTypePartition σ) =
      cycleTypePsumProduct n σ := by
  rw [cycleTypePsumProduct_eq_fullCycleType]
  simp only [MvPolynomial.psumPart, fullCycleTypePartition]

/-- The Vandermonde product over ℚ maps to the Vandermonde product over ℂ under base change. -/
private lemma map_vandermondeProd (n : ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ)
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) =
      vandermondePoly n := by
  simp only [vandermondePoly, map_prod, map_sub, MvPolynomial.map_X]

set_option maxHeartbeats 800000 in
/-- **Frobenius character formula bridge (N = n case)**: For `BoundedPartition n n`,
`charValue` cast to ℂ equals `spechtModuleCharacter`.

Proof: Using `alternantDet = sign(rev) · ∏(Xj-Xi)` and Theorem 5.15.1
`sign(rev) · χ = coeff(∏(Xj-Xi) · cyclePsum)`, we get
`charValue = sign(rev) · coeff(·) = sign(rev)² · χ = χ`. -/
private lemma charValue_eq_spechtModuleCharacter_of_eq
    (n : ℕ) (bp : BoundedPartition n n) (σ : Equiv.Perm (Fin n)) :
    (charValue n bp (fullCycleTypePartition σ) : ℂ) =
      spechtModuleCharacter n (bp.sum_eq ▸ weightToPartition n bp.parts) σ := by
  set la : Nat.Partition n := bp.sum_eq ▸ weightToPartition n bp.parts
  set μ := fullCycleTypePartition σ
  set e := Finsupp.equivFunOnFinite.symm (shiftedExps n bp.parts)
  set s := (Equiv.Perm.sign (@Fin.revPerm n) : ℤ)
  -- Step 1: charValue cast to ℂ = coeff of mapped polynomial
  have hcast : (charValue n bp μ : ℂ) =
      MvPolynomial.coeff e (MvPolynomial.map (algebraMap ℚ ℂ)
        ((alternantMatrix n (vandermondeExps n)).det *
          MvPolynomial.psumPart (Fin n) ℚ μ)) := by
    show (algebraMap ℚ ℂ) (charValue n bp μ) = _
    rw [charValue, MvPolynomial.coeff_map]
  rw [hcast]
  -- Step 2: Rewrite alternant as sign(rev) * vandermonde product
  rw [alternantDet_eq_sign_mul_vandermondeProd' n]
  -- Step 3: Reassociate multiplication
  rw [show ((s : MvPolynomial (Fin n) ℚ) *
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) *
    MvPolynomial.psumPart (Fin n) ℚ μ =
    (s : MvPolynomial (Fin n) ℚ) *
    ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) *
    MvPolynomial.psumPart (Fin n) ℚ μ) from by ring]
  -- Step 4: Apply base change ℚ → ℂ
  rw [map_mul, map_mul, map_psumPart, map_vandermondeProd]
  rw [show MvPolynomial.map (algebraMap ℚ ℂ) (s : MvPolynomial (Fin n) ℚ) =
    (s : MvPolynomial (Fin n) ℂ) from by simp only [map_intCast]]
  -- Step 5: Factor out the integer constant from coeff
  -- Int cast in MvPolynomial factors through C
  have hint : (s : MvPolynomial (Fin n) ℂ) = MvPolynomial.C (s : ℂ) := by
    simp only [MvPolynomial.C_apply, Finsupp.single_zero]
    rfl
  rw [hint, MvPolynomial.C_mul', MvPolynomial.coeff_smul, smul_eq_mul]
  -- Step 6: Match the exponent vectors
  rw [show e = Nat.Partition.toFinsupp la + rhoShift n from
    shiftedExps_eq_toFinsupp_add_rhoShift n bp]
  -- Step 7: Replace psumPart with cycleTypePsumProduct
  rw [psumPart_fullCycleType_eq_cycleTypePsumProduct]
  -- Step 8: Apply Theorem 5.15.1
  have h515 := Theorem5_15_1 n la σ
  rw [← h515, zsmul_eq_mul, ← mul_assoc]
  -- s * s = 1 for sign values (sign is ±1, so sign² = 1)
  have hs : (s : ℂ) * (s : ℂ) = 1 := by
    have h1 := Int.units_mul_self (Equiv.Perm.sign (@Fin.revPerm n))
    -- h1 : sign * sign = 1 as ℤˣ, need to cast to ℂ
    have h2 : (s : ℤ) * (s : ℤ) = 1 := by
      show (↑(Equiv.Perm.sign Fin.revPerm) : ℤ) * ↑(Equiv.Perm.sign Fin.revPerm) = ↑(1 : ℤˣ)
      rw [← Units.val_mul, h1]
    exact_mod_cast h2
  rw [hs, one_mul]

/-- Construct the canonical `BoundedPartition n n` from the sorted parts of an antitone
weight function, by padding with zeros to length n. -/
-- Helper: sum of getD over Fin n equals list sum when length ≤ n
private lemma sum_getD_eq_sum (l : List ℕ) (n : ℕ) (hlen : l.length ≤ n) :
    ∑ i : Fin n, l.getD i.val 0 = l.sum := by
  induction n generalizing l with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (by omega : l.length = 0)
    subst this; rfl
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    cases l with
    | nil => simp [ih [] (Nat.zero_le _)]
    | cons a t =>
      simp only [List.getD_cons_zero, List.sum_cons, Fin.val_zero]
      congr 1
      have hstep : ∀ i : Fin n, (a :: t).getD i.succ.val 0 = t.getD i.val 0 := by
        intro ⟨i, _⟩; simp [List.getD_cons_succ]
      simp_rw [hstep]
      exact ih t (by simpa using hlen)

-- Helper: getD on a list with Pairwise (· ≥ ·) is antitone
private lemma getD_antitone_of_pairwise (l : List ℕ) (h : l.Pairwise (· ≥ ·)) :
    Antitone (fun i : Fin n => l.getD i.val 0) := by
  intro i j hij
  show l.getD j.val 0 ≤ l.getD i.val 0
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · by_cases hj : j.val < l.length
    · have hi : i.val < l.length := by omega
      rw [List.getD_eq_getElem (hn := hj), List.getD_eq_getElem (hn := hi)]
      exact List.pairwise_iff_get.mp h ⟨i.val, hi⟩ ⟨j.val, hj⟩ hlt
    · rw [List.getD_eq_default (hn := by omega)]
      exact Nat.zero_le _

private def canonicalBP (N n : ℕ) (bp : BoundedPartition N n) : BoundedPartition n n where
  parts := fun i => (bp.sum_eq ▸ weightToPartition N bp.parts).sortedParts.getD i.val 0
  decreasing := by
    set l := (bp.sum_eq ▸ weightToPartition N bp.parts).sortedParts
    exact getD_antitone_of_pairwise l (Multiset.pairwise_sort _ _)
  sum_eq := by
    set la := (bp.sum_eq ▸ weightToPartition N bp.parts)
    set l := la.sortedParts
    have hpos : ∀ x ∈ l, 0 < x := by
      intro x hx
      apply la.parts_pos
      have h_sort := Multiset.sort_eq (r := (· ≥ ·)) la.parts
      rw [show la.parts.sort (· ≥ ·) = l from rfl] at h_sort
      exact h_sort ▸ Multiset.mem_coe.mpr hx
    have hlen : l.length ≤ n := by
      have hsum : l.sum = n := sortedParts_sum n la
      suffices h : ∀ (m : List ℕ), (∀ x ∈ m, 0 < x) → m.length ≤ m.sum by
        linarith [h l hpos]
      intro m hm
      induction m with
      | nil => exact Nat.zero_le _
      | cons a t iht =>
        simp only [List.length_cons, List.sum_cons]
        have ha := hm a (by simp)
        have := iht (fun x hx => hm x (by simp [hx]))
        omega
    rw [sum_getD_eq_sum l n hlen, sortedParts_sum]

/-- The canonical BP has the same underlying partition (weightToPartition) as the original. -/
private lemma canonicalBP_weightToPartition (N n : ℕ) (bp : BoundedPartition N n) :
    ((canonicalBP N n bp).sum_eq ▸ weightToPartition n (canonicalBP N n bp).parts :
      Nat.Partition n) =
    (bp.sum_eq ▸ weightToPartition N bp.parts : Nat.Partition n) := by
  set la := (bp.sum_eq ▸ weightToPartition N bp.parts)
  set l := la.sortedParts
  have hrec : ∀ (m k : ℕ) (h : m = k) (p : Nat.Partition m), (h ▸ p).parts = p.parts := by
    intros m k h p; subst h; rfl
  apply Nat.Partition.ext
  rw [hrec _ _ (canonicalBP N n bp).sum_eq, hrec _ _ bp.sum_eq]
  -- Goal: (wtp n canonical.parts).parts = (wtp N bp.parts).parts
  -- RHS = la.parts by unfolding. LHS needs work.
  -- All elements of l are positive
  have hpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    exact la.parts_pos ((Multiset.sort_eq (r := (· ≥ ·)) la.parts) ▸
      Multiset.mem_coe.mpr hx)
  -- l.length ≤ n
  have hlen : l.length ≤ n := by
    have hsum : l.sum = n := sortedParts_sum n la
    suffices hl : ∀ (m : List ℕ), (∀ x ∈ m, 0 < x) → m.length ≤ m.sum by linarith [hl l hpos]
    intro m hm; induction m with
    | nil => exact Nat.zero_le _
    | cons a t ih =>
      simp only [List.length_cons, List.sum_cons]
      have := hm a (by simp); have := ih (fun x hx => hm x (by simp [hx])); omega
  -- Show LHS.parts = la.parts
  -- LHS.parts = filter(>0) from map(canonical.parts) over Fin n
  -- canonical.parts i = l.getD i 0, so the map is [l.getD 0 0, ..., l.getD (n-1) 0]
  -- Filtering zeros gives the positive elements of l = la.parts
  suffices h_lhs : (weightToPartition n (canonicalBP N n bp).parts).parts = la.parts by
    rw [h_lhs]; rw [show la.parts = (weightToPartition N bp.parts).parts from
      (hrec _ _ bp.sum_eq (weightToPartition N bp.parts)).symm ▸ rfl]
  -- Unfold to multiset operations
  show (Finset.univ.val.map (fun i : Fin n => l.getD i.val 0)).filter (0 < ·) = la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe]
  -- Show filter(>0) ofFn(getD) = l as lists (↑ gives la.parts by sort_eq)
  suffices h : (List.ofFn (fun i : Fin n => l.getD i.val 0)).filter (fun x => decide (0 < x)) = l by
    rw [h]; exact Multiset.sort_eq _ _
  -- Prove by induction on n, generalizing l
  suffices key : ∀ (m : ℕ) (ll : List ℕ), (∀ x ∈ ll, 0 < x) → ll.length ≤ m →
      (List.ofFn (fun i : Fin m => ll.getD i.val 0)).filter (fun x => decide (0 < x)) = ll by
    exact key n l hpos hlen
  intro m; induction m with
  | zero => intro ll _ hlen; simp [List.eq_nil_of_length_eq_zero (by omega : ll.length = 0)]
  | succ m ih =>
    intro ll hll hlen
    simp only [List.ofFn_succ, Fin.val_zero, List.filter_cons]
    cases ll with
    | nil =>
      simp only [List.getD_nil, List.ofFn_const, List.filter_replicate,
        show ¬ decide (0 < 0) = true from by simp]
      simp
    | cons a t =>
      simp only [List.getD_cons_zero]
      have ha : 0 < a := hll a (by simp)
      rw [show decide (0 < a) = true from decide_eq_true ha]
      simp only [ite_true]
      congr 1
      -- The remaining terms: filter on ofFn(fun i => (a::t).getD i.succ 0)
      -- = filter on ofFn(fun i => t.getD i 0) by List.getD_cons_succ
      show (List.ofFn (fun i : Fin m => t.getD i.val 0)).filter (fun x => decide (0 < x)) = t
      exact ih t (fun x hx => hll x (by simp [hx]))
        (by simp only [List.length_cons] at hlen; omega)

/-- Dropping the last part from a BoundedPartition when it's zero. -/
private def BoundedPartition.dropLast (N n : ℕ) (bp : BoundedPartition (N + 1) n)
    (h0 : bp.parts (Fin.last N) = 0) : BoundedPartition N n where
  parts i := bp.parts (i.castSucc)
  decreasing i j hij := bp.decreasing (Fin.castSucc_le_castSucc_iff.mpr hij)
  sum_eq := by
    have hsplit : ∑ i : Fin (N + 1), bp.parts i =
        (∑ i : Fin N, bp.parts i.castSucc) + bp.parts (Fin.last N) :=
      Fin.sum_univ_castSucc bp.parts
    rw [h0, add_zero] at hsplit
    linarith [bp.sum_eq]

/-- **Key reduction**: If the last part of a bounded partition is 0, then `charValue` at
`N+1` variables equals `charValue` at `N` variables with the last part dropped.

**Proof outline** (setting x_N = 0 in the (N+1)-variable formula):
1. The (N+1)×(N+1) alternant matrix with last row (0,...,0,1) has determinant
   equal to ∏x_i · Δ_N (cofactor expansion, then factor x_i from each row).
2. psumPart in N+1 vars with x_N=0 = psumPart in N vars.
3. The shifted exponents at N+1 are the N-variable shifted exponents shifted +1
   (plus a 0 at position N), so multiplying by ∏x_i exactly compensates.

The restriction algebra homomorphism that sets the last variable to 0:
sends `x_i ↦ x_i` for `i < N` and `x_N ↦ 0`. -/
private noncomputable def restrictLastVar (N : ℕ) :
    MvPolynomial (Fin (N + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun i : Fin (N + 1) =>
    if h : i.val < N then MvPolynomial.X (⟨i.val, h⟩ : Fin N) else 0)

/-- Coefficient extraction through restriction: evaluating at x_N = 0 and extracting
coefficient at `e` gives the coefficient of the original polynomial at `e` extended
with 0 at position N. -/
private lemma coeff_restrictLastVar (N : ℕ) (p : MvPolynomial (Fin (N + 1)) ℚ)
    (e : Fin N →₀ ℕ) :
    (restrictLastVar N p).coeff e =
      p.coeff (Finsupp.equivFunOnFinite.symm (fun i : Fin (N + 1) =>
        if h : i.val < N then e ⟨i.val, h⟩ else 0)) := by
  sorry

/-- Setting x_N = 0 in the (N+1)-variable Vandermonde determinant gives
∏_{i : Fin N} x_i · Δ_N. -/
private lemma restrictLastVar_alternantDet (N : ℕ) :
    restrictLastVar N (alternantMatrix (N + 1) (vandermondeExps (N + 1))).det =
      (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) *
        (alternantMatrix N (vandermondeExps N)).det := by
  sorry

/-- Setting x_N = 0 in psum gives psum in N variables:
`psum(Fin(N+1), k) = ∑_{i<N} X_i^k + X_N^k`, setting X_N = 0 drops last term. -/
private lemma restrictLastVar_psum (N k : ℕ) :
    restrictLastVar N (MvPolynomial.psum (Fin (N + 1)) ℚ k) =
      MvPolynomial.psum (Fin N) ℚ k := by
  sorry

/-- Setting x_N = 0 in psumPart: since psumPart is a product of psum's,
this follows from `restrictLastVar_psum` and multiplicativity of `AlgHom`. -/
private lemma restrictLastVar_psumPart {n : ℕ} (N : ℕ) (μ : Nat.Partition n) :
    restrictLastVar N (MvPolynomial.psumPart (Fin (N + 1)) ℚ μ) =
      MvPolynomial.psumPart (Fin N) ℚ μ := by
  sorry

/-- Coefficient shifting: coeff_{e+1}(∏x_i · p) = coeff_e(p), where +1 means
adding 1 to every exponent component. -/
private lemma prod_X_eq_monomial_ones (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Finsupp.equivFunOnFinite]

private lemma coeff_prod_X_mul (N : ℕ) (p : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    ((∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) * p).coeff
      (e + Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)) = p.coeff e := by
  set ones := Finsupp.equivFunOnFinite.symm (fun _ : Fin N => 1)
  rw [prod_X_eq_monomial_ones, add_comm]
  rw [MvPolynomial.coeff_monomial_mul, one_mul]

private lemma charValue_remove_trailing_zero (N n : ℕ)
    (bp : BoundedPartition (N + 1) n)
    (h0 : bp.parts (Fin.last N) = 0) (μ : Nat.Partition n) :
    charValue (N + 1) bp μ = charValue N (bp.dropLast N n h0) μ := by
  sorry

/-- If `N > n` then an antitone partition of `n` into `N` parts has last part 0. -/
private lemma bp_trailing_zero_of_gt (N n : ℕ) (bp : BoundedPartition N n)
    (hN : N > n) :
    bp.parts (⟨N - 1, by omega⟩ : Fin N) = 0 := by
  by_contra h
  have hpos : 0 < bp.parts ⟨N - 1, by omega⟩ := Nat.pos_of_ne_zero h
  have hall : ∀ i : Fin N, 1 ≤ bp.parts i := fun i => by
    have hi := i.isLt
    have hle : i ≤ ⟨N - 1, by omega⟩ := by exact Fin.mk_le_mk.mpr (by omega)
    exact le_trans hpos (bp.decreasing hle)
  have hge : N ≤ ∑ i : Fin N, bp.parts i :=
    le_trans (by simp) (Finset.sum_le_sum fun i _ => hall i)
  linarith [bp.sum_eq]

/-- Two antitone sequences with the same sum and the same weightToPartition
are pointwise equal. (Moved here for use in charValue_stability.) -/
private lemma antitone_eq_of_filter_pos_eq'
    (N : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (h : (Finset.univ.val.map lam).filter (0 < ·) =
         (Finset.univ.val.map lam').filter (0 < ·)) :
    lam = lam' := by
  have h_full : Finset.univ.val.map lam = Finset.univ.val.map lam' := by
    apply Multiset.ext'; intro a
    by_cases ha : 0 < a
    · have := congr_arg (Multiset.count a) h
      rwa [Multiset.count_filter_of_pos ha, Multiset.count_filter_of_pos ha] at this
    · push_neg at ha; obtain rfl := Nat.le_zero.mp ha
      have hc : (Finset.univ.val.map lam).card = (Finset.univ.val.map lam').card := by simp
      have hfc := congr_arg Multiset.card h
      have key : ∀ (m : Multiset ℕ), Multiset.count 0 m = m.card - (m.filter (0 < ·)).card := by
        intro m
        have h_split := congr_arg Multiset.card (Multiset.filter_add_not (0 < ·) m)
        rw [Multiset.card_add] at h_split
        rw [Multiset.count_eq_card_filter_eq]
        have : Multiset.filter (fun a => 0 = a) m = Multiset.filter (fun a => ¬ 0 < a) m := by
          congr 1; ext a; simp [eq_comm]
        rw [this]; omega
      rw [key, key]; omega
  simp only [Fin.univ_val_map] at h_full
  have h_perm := Multiset.coe_eq_coe.mp h_full
  exact List.ofFn_injective
    (h_perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.mpr hlam) (List.sortedGE_ofFn_iff.mpr hlam'))

private lemma weightToPartition_eq_iff'
    (N n : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (hsum : ∑ i, lam i = n) (hsum' : ∑ i, lam' i = n) :
    (hsum ▸ weightToPartition N lam : Nat.Partition n) =
      (hsum' ▸ weightToPartition N lam') ↔ lam = lam' := by
  constructor
  · intro h
    apply antitone_eq_of_filter_pos_eq' N lam lam' hlam hlam'
    have h1 := congr_arg Nat.Partition.parts h
    have hrec : ∀ (m k : ℕ) (heq : m = k) (p : Nat.Partition m),
        (heq ▸ p).parts = p.parts := by
      intros m k heq p; subst heq; rfl
    rw [hrec _ _ hsum, hrec _ _ hsum'] at h1
    exact h1
  · intro h; subst h; rfl

/-- `charValue N bp μ` reduces to `charValue n (canonicalBP N n bp) μ` by
repeatedly removing trailing zeros. -/
private lemma charValue_reduce_to_canonical (N n : ℕ) (bp : BoundedPartition N n)
    (μ : Nat.Partition n) :
    charValue N bp μ = charValue n (canonicalBP N n bp) μ := by
  sorry

/-- Stability of charValue: the value is independent of the number of variables N,
depending only on the partition (nonzero parts). This is the standard fact that
symmetric function coefficients in the alternant expansion are stable under
change of the number of variables.

**Proof**: Both sides reduce to `charValue n (canonicalBP)` via trailing-zero removal.
The canonical BPs have the same parts by the hypothesis on partitions. -/
private lemma charValue_stability
    (N₁ N₂ n : ℕ) (bp₁ : BoundedPartition N₁ n) (bp₂ : BoundedPartition N₂ n)
    (h : (bp₁.sum_eq ▸ weightToPartition N₁ bp₁.parts : Nat.Partition n) =
         (bp₂.sum_eq ▸ weightToPartition N₂ bp₂.parts : Nat.Partition n))
    (μ : Nat.Partition n) :
    charValue N₁ bp₁ μ = charValue N₂ bp₂ μ := by
  rw [charValue_reduce_to_canonical N₁ n bp₁ μ,
      charValue_reduce_to_canonical N₂ n bp₂ μ]
  -- The canonical BPs have the same underlying partition, hence same parts
  -- (antitone at same size n + same multiset of nonzero parts → same function)
  have h_canon₁ := canonicalBP_weightToPartition N₁ n bp₁
  have h_canon₂ := canonicalBP_weightToPartition N₂ n bp₂
  -- The canonical BPs must be equal since their partitions agree
  suffices h_eq : canonicalBP N₁ n bp₁ = canonicalBP N₂ n bp₂ by rw [h_eq]
  have h_same : ((canonicalBP N₁ n bp₁).sum_eq ▸
      weightToPartition n (canonicalBP N₁ n bp₁).parts : Nat.Partition n) =
    ((canonicalBP N₂ n bp₂).sum_eq ▸
      weightToPartition n (canonicalBP N₂ n bp₂).parts : Nat.Partition n) := by
    rw [h_canon₁, h_canon₂, h]
  have h_parts : (canonicalBP N₁ n bp₁).parts = (canonicalBP N₂ n bp₂).parts :=
    (weightToPartition_eq_iff' n n _ _ (canonicalBP N₁ n bp₁).decreasing
      (canonicalBP N₂ n bp₂).decreasing _ _).mp h_same
  exact match canonicalBP N₁ n bp₁, canonicalBP N₂ n bp₂, h_parts with
    | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/-- The Frobenius character formula bridge: `charValue` equals `spechtModuleCharacter`
(after casting ℚ → ℂ). This bridges the polynomial coefficient definition used in
the Weyl character formula with the trace definition used in Specht module theory.

For general N, this reduces to the N = n case via `charValue_stability`. -/
private lemma charValue_eq_spechtModuleCharacter
    (N : ℕ) (n : ℕ) (lam' : BoundedPartition N n) (σ : Equiv.Perm (Fin n)) :
    (charValue N lam' (fullCycleTypePartition σ) : ℂ) =
      spechtModuleCharacter n (lam'.sum_eq ▸ weightToPartition N lam'.parts) σ := by
  -- Reduce to N = n case via stability
  set bp_n := canonicalBP N n lam'
  have hstab := charValue_stability N n n lam' bp_n
    (by rw [canonicalBP_weightToPartition]) (fullCycleTypePartition σ)
  rw [hstab]
  -- Apply the N = n bridge
  have hbridge := charValue_eq_spechtModuleCharacter_of_eq n bp_n σ
  rw [hbridge]
  -- Show the transported partitions match
  congr 1
  exact canonicalBP_weightToPartition N n lam'

/-- Two antitone sequences with the same sum and the same weightToPartition
are pointwise equal. (The multiset of nonzero parts, being sorted by
antitonicity, uniquely determines the sequence once padded with zeros.) -/
private lemma antitone_eq_of_filter_pos_eq
    (N : ℕ) (lam lam' : Fin N → ℕ)
    (hlam : Antitone lam) (hlam' : Antitone lam')
    (h : (Finset.univ.val.map lam).filter (0 < ·) =
         (Finset.univ.val.map lam').filter (0 < ·)) :
    lam = lam' := by
  -- Step 1: Full multisets are equal (positive filters equal + same card → full equal)
  have h_full : Finset.univ.val.map lam = Finset.univ.val.map lam' := by
    apply Multiset.ext'; intro a
    by_cases ha : 0 < a
    · have := congr_arg (Multiset.count a) h
      rwa [Multiset.count_filter_of_pos ha, Multiset.count_filter_of_pos ha] at this
    · push_neg at ha; obtain rfl := Nat.le_zero.mp ha
      have hc : (Finset.univ.val.map lam).card = (Finset.univ.val.map lam').card := by simp
      have hfc := congr_arg Multiset.card h
      have key : ∀ (m : Multiset ℕ), Multiset.count 0 m = m.card - (m.filter (0 < ·)).card := by
        intro m
        have h_split := congr_arg Multiset.card (Multiset.filter_add_not (0 < ·) m)
        rw [Multiset.card_add] at h_split
        rw [Multiset.count_eq_card_filter_eq]
        have : Multiset.filter (fun a => 0 = a) m = Multiset.filter (fun a => ¬ 0 < a) m := by
          congr 1; ext a; simp [eq_comm]
        rw [this]; omega
      rw [key, key]; omega
  -- Step 2: Antitone functions with equal value multisets are equal.
  -- For antitone f, List.ofFn f is SortedGE. Two SortedGE lists that are
  -- permutations (= equal multisets) are equal.
  simp only [Fin.univ_val_map] at h_full
  have h_perm := Multiset.coe_eq_coe.mp h_full
  exact List.ofFn_injective
    (h_perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.mpr hlam) (List.sortedGE_ofFn_iff.mpr hlam'))

private lemma weightToPartition_eq_iff
    (N n : ℕ) (lam lam' : Fin N → ℕ)
    (_hlam : Antitone lam) (_hlam' : Antitone lam')
    (hsum : ∑ i, lam i = n) (hsum' : ∑ i, lam' i = n) :
    (hsum ▸ weightToPartition N lam : Nat.Partition n) =
      (hsum' ▸ weightToPartition N lam') ↔ lam = lam' := by
  constructor
  · intro h
    apply antitone_eq_of_filter_pos_eq N lam lam' _hlam _hlam'
    have h1 := congr_arg Nat.Partition.parts h
    have hrec : ∀ (m k : ℕ) (heq : m = k) (p : Nat.Partition m),
        (heq ▸ p).parts = p.parts := by
      intros m k heq p; subst heq; rfl
    rw [hrec _ _ hsum, hrec _ _ hsum'] at h1
    exact h1
  · intro h; subst h; rfl

/-! #### Character orthogonality for the Young symmetrizer -/

/-- **Character orthogonality for the Young symmetrizer**: The Young-symmetrizer-weighted
sum of character values gives `α` for the matching partition and `0` otherwise.

This is the key identity: ∑_σ c_λ(σ) · χ_{λ'}(σ) = α · δ_{λ,λ'}

Proved by bridging `charValue` (polynomial coefficient over ℚ) to
`spechtModuleCharacter` (trace over ℂ) via the Frobenius character formula,
then applying `youngSym_trace_kronecker` and using injectivity of ℚ → ℂ. -/
theorem youngSym_charValue_orthogonality
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam))
    (lam' : BoundedPartition N (∑ i, lam i)) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) *
        charValue N lam' (fullCycleTypePartition σ) =
      if lam'.parts = lam then α else 0 := by
  -- Prove the ℂ version using the trace Kronecker identity, then cast back to ℚ
  set la'_np : Nat.Partition (∑ i, lam i) := lam'.sum_eq ▸ weightToPartition N lam'.parts
  -- The trace Kronecker identity over ℂ
  have h_trace := youngSym_trace_kronecker' (∑ i, lam i) (weightToPartition N lam)
    la'_np α hα_sq
  -- Bridge: charValue cast to ℂ equals spechtModuleCharacter
  have h_bridge : ∀ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (charValue N lam' (fullCycleTypePartition σ) : ℂ) =
        spechtModuleCharacter (∑ i, lam i) la'_np σ :=
    fun σ => charValue_eq_spechtModuleCharacter N (∑ i, lam i) lam' σ
  -- Match the if-conditions: (la = la'_np) ↔ (lam'.parts = lam)
  have h_cond : (weightToPartition N lam = la'_np) ↔ (lam'.parts = lam) := by
    rw [weightToPartition_eq_iff N (∑ i, lam i) lam lam'.parts hlam lam'.decreasing rfl lam'.sum_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  -- Combine: compute the ℂ version and cast back
  have h_ℂ : ∀ σ, (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℂ) *
      (charValue N lam' (fullCycleTypePartition σ) : ℂ) =
      (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℂ) *
        spechtModuleCharacter (∑ i, lam i) la'_np σ := by
    intro σ; congr 1; exact h_bridge σ
  have h_sum : (∑ σ, (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) *
      charValue N lam' (fullCycleTypePartition σ) : ℂ) =
      if lam'.parts = lam then (α : ℂ) else 0 := by
    push_cast [Finset.sum_comm]
    simp_rw [h_ℂ, h_trace]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (h_cond.mp h1) h2
    · exact absurd (h_cond.mpr h2) h1
    · rfl
  have hinj := (algebraMap ℚ ℂ).injective
  apply hinj
  convert h_sum using 1
  · push_cast; rfl
  · split_ifs <;> simp

/-! #### Step 2: Young symmetrizer weighted sum of permTracePoly equals α · schurPoly

This is the combinatorial/representation-theoretic identity: grouping the sum
`∑_σ c_λ(σ) · permTracePoly(N, σ)` by conjugacy class (= cycle type) and
applying the Frobenius formula (Proposition 5.21.1) plus character orthogonality
for S_n yields `α · s_λ(x)`. -/

set_option maxHeartbeats 1600000 in -- Frobenius + orthogonality proof needs extended heartbeats
/-- **Frobenius + orthogonality**: The Young-symmetrizer-weighted sum of
permutation trace polynomials equals `α · schurPoly N lam`. -/
theorem sum_youngSym_permTracePoly_eq_alpha_schurPoly
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (_hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam)) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) •
        permTracePoly N σ = α • schurPoly N lam := by
  set n := ∑ i, lam i with hn
  set la := weightToPartition N lam
  set c := YoungSymmetrizerK ℚ n la
  set Δ := (alternantMatrix N (vandermondeExps N)).det
  set F := ∑ σ : Equiv.Perm (Fin n), (c σ : ℚ) • permTracePoly N σ
  -- Cancel the Vandermonde determinant (nonzero in MvPolynomial integral domain)
  have hΔ : Δ ≠ 0 := alternantMatrix_vandermondeExps_det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [smul_mul_assoc, schurPoly_mul_vandermonde]
  -- Goal: F * Δ = α • (alternantMatrix N (shiftedExps N lam)).det
  -- Show F * Δ - α • A_{λ+δ} = 0 by the antisymmetric basis argument
  rw [← sub_eq_zero]
  apply antisym_eq_zero
  · -- F * Δ - α • A_{λ+δ} is antisymmetric
    intro σ
    rw [map_sub, smul_sub]
    congr 1
    · -- F * Δ is antisymmetric: F is symmetric, Δ is antisymmetric
      rw [map_mul, rename_alternant_det]
      -- Goal: (rename σ) F * (sign σ • Δ) = sign σ • (F * Δ)
      have hF_sym : (MvPolynomial.rename σ) F = F := by
        simp only [F, map_sum]
        apply Finset.sum_congr rfl
        intro τ _
        rw [AlgHom.map_smul_of_tower]
        congr 1
        rw [permTracePoly_eq_powerSumCycleProduct N τ, powerSumCycleProduct_eq_psumPart N τ]
        exact (psumPart_isSymmetric N (fullCycleTypePartition τ)) σ
      rw [hF_sym, mul_comm F (Equiv.Perm.sign σ • Δ), smul_mul_assoc, mul_comm]
    · -- α • A_{λ+δ} is antisymmetric
      rw [AlgHom.map_smul_of_tower, rename_alternant_det, smul_comm]
  · -- All alternant coefficients of F * Δ - α • A_{λ+δ} are zero
    intro e he
    rw [MvPolynomial.coeff_sub]
    -- Coefficient of A_{λ+δ} at strictly anti e
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    -- Goal now has: α * coeff e (alternantMatrix N (shiftedExps N lam)).det
    -- Need to change shiftedExps N lam to shiftedExps N (weightToBP N lam hlam).parts
    change MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) -
      α * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (alternantMatrix N (shiftedExps N (weightToBP N lam hlam).parts)).det = 0
    rw [alternant_coeff_kronecker (shiftedExps_strictAnti (weightToBP N lam hlam)) he]
    -- Coefficient of F * Δ at e
    -- F * Δ = ∑_σ c(σ) • (permTracePoly σ * Δ)
    -- The coefficient is ∑_σ c(σ) * coeff_e(Δ * permTracePoly σ)
    -- = ∑_σ c(σ) * charValue(N, lam', type(σ))  when e = shiftedExps N lam'.parts
    -- By character orthogonality, this equals α if lam' = lam, 0 otherwise
    -- We need to handle two cases:
    -- (a) e = shiftedExps N lam'.parts for some BP lam'
    -- (b) e does not come from any BP (wrong total degree)
    show MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) -
      α * (if shiftedExps N (weightToBP N lam hlam).parts = e then 1 else 0) = 0
    -- Compute F * Δ coefficient using linearity
    have hF_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (F * Δ) =
        ∑ σ : Equiv.Perm (Fin n),
          (c σ : ℚ) * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (Δ * permTracePoly N σ) := by
      show MvPolynomial.coeff _ (F * Δ) = _
      simp only [F, Finset.sum_mul, MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl; intro σ _
      rw [smul_mul_assoc, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm (permTracePoly N σ) Δ]
    rw [hF_coeff]
    -- Replace permTracePoly by psumPart and use charValue definition
    conv_lhs =>
      arg 1; arg 2; ext σ
      rw [permTracePoly_eq_powerSumCycleProduct N σ, powerSumCycleProduct_eq_psumPart N σ]
    -- Now the sum is ∑_σ c(σ) * charValue(N, ?, type(σ))
    -- Handle degree case: if e doesn't come from a BP, both sides are 0
    by_cases hbp : ∃ lam' : BoundedPartition N n, shiftedExps N lam'.parts = e
    · -- Case (a): e = shiftedExps N lam'.parts for some BP
      obtain ⟨lam', hlam'⟩ := hbp
      -- The coefficient is charValue by definition
      have h_cv : ∀ σ,
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (Δ * MvPolynomial.psumPart (Fin N) ℚ (fullCycleTypePartition σ)) =
          charValue N lam' (fullCycleTypePartition σ) := by
        intro σ; rw [← hlam']; rfl
      simp_rw [h_cv]
      -- Apply character orthogonality
      have horth := youngSym_charValue_orthogonality N lam hlam α hα_sq lam'
      rw [horth]
      -- Now need: if (lam'.parts = lam) then α else 0 -
      --           α * if (shiftedExps N (weightToBP N lam hlam).parts = e) then 1 else 0 = 0
      simp only [weightToBP]
      by_cases heq : lam'.parts = lam
      · -- lam' matches lam
        rw [if_pos heq, if_pos (by rw [← hlam']; congr 1; exact heq.symm), mul_one, sub_self]
      · -- lam' doesn't match lam
        rw [if_neg heq]
        rw [if_neg (by intro h; exact heq (by
          have : shiftedExps N lam = e := h
          have : shiftedExps N lam = shiftedExps N lam'.parts := this.trans hlam'.symm
          funext j; have := congr_fun this j; simp [shiftedExps] at this; omega))]
        simp
    · -- Case (b): e doesn't come from any BP → coefficient is 0 by homogeneity
      -- The if-condition is false since shiftedExps lam IS a BP
      have hne : shiftedExps N (weightToBP N lam hlam).parts ≠ e := by
        intro h; exact hbp ⟨weightToBP N lam hlam, h⟩
      rw [if_neg hne, mul_zero, sub_zero]
      -- Each coeff_e(Δ * psumPart σ) = 0 since e doesn't come from any BP
      -- The antisymmetric polynomial Δ * psumPart σ has nonzero coefficients only at
      -- strictly anti exponents of the form shiftedExps N lam'.parts
      apply Finset.sum_eq_zero; intro σ _
      suffices h : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          (Δ * MvPolynomial.psumPart (Fin N) ℚ (fullCycleTypePartition σ)) = 0 by
        rw [h, mul_zero]
      -- By homogeneity: if coeff ≠ 0 then ∑ e_j = ∑ vandermondeExps_j + n,
      -- then exists_bp_of_strictAnti_sum gives a BP. Contradicts hbp.
      by_contra h'
      have h'' : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
          (Δ * MvPolynomial.psumPart (Fin N) ℚ (fullCycleTypePartition σ)) ≠ 0 := by
        exact fun heq => h' heq
      have hF := (alternant_isHomogeneous (vandermondeExps N)).mul
        (psumPart_isHomogeneous N (fullCycleTypePartition σ))
      have hd := hF h''
      have hweight : Finsupp.weight (1 : Fin N → ℕ) (Finsupp.equivFunOnFinite.symm e) =
          ∑ j : Fin N, e j := by
        simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      rw [hweight] at hd
      obtain ⟨lam', hlam'⟩ := exists_bp_of_strictAnti_sum e he (by exact_mod_cast hd)
      exact hbp ⟨lam', hlam'⟩

/-- **Weyl character formula (polynomial level)**: The formal character of the Schur module
`L_λ` equals the Schur polynomial `S_λ(x₁, …, x_N)`.

Proved by combining the trace formula (Step 1) with the Frobenius-orthogonality
identity (Step 2) and cancelling the scalar `α`. -/
theorem formalCharacter_schurModule_eq_schurPoly
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N lam) = schurPoly N lam := by
  -- Get the scalar α from c_λ² = α · c_λ
  obtain ⟨α, hα_sq⟩ := YoungSymmetrizerK_sq_scalar ℚ (∑ i, lam i) (weightToPartition N lam)
  have hα : α ≠ 0 :=
    YoungSymmetrizerK_sq_scalar_ne_zero _ (weightToPartition N lam) α hα_sq
  -- Step 1: ch(L_λ) = α⁻¹ · ∑_σ c_λ(σ) · permTracePoly(N, σ)
  rw [formalCharacter_schurModule_eq_sum_permTracePoly k N lam hlam α hα hα_sq]
  -- Step 2: ∑_σ c_λ(σ) · permTracePoly(N, σ) = α · s_λ
  rw [sum_youngSym_permTracePoly_eq_alpha_schurPoly N lam hlam α hα hα_sq]
  -- Cancel: α⁻¹ · (α · s_λ) = s_λ
  rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

/-! ### Weight multiplicity equals Schur polynomial coefficient -/

/-- **Core Weyl character formula (polynomial level)**: The formal character of the Schur
module `L_λ`, when multiplied by the Vandermonde determinant, equals the alternant determinant
with shifted exponents `λ + δ`.

`ch(L_λ) · Δ = A_{λ+δ}`, where `Δ = det(x_i^{N-1-j})` and
`A_{λ+δ} = det(x_i^{λ_j+N-1-j})`. -/
theorem formalCharacter_schurModule_mul_vandermonde
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N lam) * (alternantMatrix N (vandermondeExps N)).det =
      (alternantMatrix N (shiftedExps N lam)).det := by
  rw [formalCharacter_schurModule_eq_schurPoly k N lam hlam, schurPoly_mul_vandermonde]

/-- **Key helper**: The dimension of the weight space for weight `μ` in the Schur module `L_λ`
equals the coefficient of `x^μ` in the Schur polynomial `S_λ`.

This is the core content of the Weyl character formula at the coefficient level:
`dim(L_λ)_μ = [x^μ] S_λ(x)`. -/
theorem schurModule_weight_eq_schurPoly_coeff
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (μ : Fin N →₀ ℕ) :
    (Module.finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) : ℚ) =
      (schurPoly N lam).coeff μ := by
  -- Reduce to the polynomial-level equality: formalCharacter = schurPoly
  have h_poly : formalCharacter k N (SchurModule k N lam) = schurPoly N lam := by
    -- Both polynomials satisfy p * Δ = A_{λ+δ}. Since Δ ≠ 0 in the integral domain
    -- MvPolynomial (Fin N) ℚ, they must be equal.
    have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
    apply mul_right_cancel₀ hΔ
    rw [formalCharacter_schurModule_mul_vandermonde k N lam hlam,
        schurPoly_mul_vandermonde]
  rw [← formalCharacter_coeff, h_poly]

/-- **Weyl character formula for GL(V)**: the formal character of the Schur module
`L_λ` equals the Schur polynomial `S_λ(x₁, …, x_N)`.
(Etingof Theorem 5.22.1) -/
theorem Theorem5_22_1
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N lam) = schurPoly N lam := by
  ext μ
  rw [formalCharacter_coeff, schurModule_weight_eq_schurPoly_coeff k N lam hlam]

end Etingof
