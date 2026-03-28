import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.PermDiagonalTrace

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
  (∑ g : (RowSubgroup n la), MonoidAlgebra.of k _ g.val) *
  (∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val)

/-! ### Young symmetrizer over ℤ and scalar transfer -/

/-- The Young symmetrizer over ℤ. This is the "universal" version from which both
`YoungSymmetrizer` (over ℂ) and `YoungSymmetrizerK` (over k) are obtained via base change. -/
def YoungSymmetrizerZ (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  (∑ g : (RowSubgroup n la), MonoidAlgebra.of ℤ _ g.val) *
  (∑ g : (ColumnSubgroup n la),
    (↑(Equiv.Perm.sign g.val) : ℤ) • MonoidAlgebra.of ℤ _ g.val)

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
  simp_rw [Finset.mul_sum, mul_smul_comm]
  -- Unfold of to single, then simplify multiplication of singles
  have hof : ∀ (g : Equiv.Perm (Fin n)),
      (MonoidAlgebra.of ℂ _ g : MonoidAlgebra ℂ _) = Finsupp.single g 1 := fun _ => rfl
  simp_rw [hof, MonoidAlgebra.single_mul_single, mul_one]
  -- Goal: (∑ p ∑ q, (sign q) • single (p*q) 1)(1) = 1
  rw [Finset.sum_apply']
  conv_lhs => arg 2; ext k; rw [Finset.sum_apply']
  simp only [MonoidAlgebra.smul_apply, smul_eq_mul, MonoidAlgebra.single_apply,
    mul_ite, mul_one, mul_zero]
  -- ∑_p ∑_q, if p * q = 1 then (sign q : ℂ) else 0 = 1
  rw [Fintype.sum_eq_single ⟨1, (RowSubgroup n la).one_mem⟩]
  · rw [Fintype.sum_eq_single ⟨1, (ColumnSubgroup n la).one_mem⟩]
    · simp [Equiv.Perm.sign_one]
    · intro ⟨q, hq⟩ hne
      rw [if_neg]
      intro hq1
      exact hne (Subtype.ext (by simpa using hq1))
  · intro ⟨p, hp⟩ hne
    apply Fintype.sum_eq_zero
    intro ⟨q, hq⟩
    rw [if_neg]
    intro hpq
    have heq : p = q⁻¹ := mul_eq_one_iff_eq_inv.mp hpq
    have hp_in_Q : p ∈ ColumnSubgroup n la := heq ▸ (ColumnSubgroup n la).inv_mem hq
    exact hne (Subtype.ext (row_col_preserving_eq_one n la p hp hp_in_Q))

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

/-! #### Step 1: Formal character via trace of Young symmetrizer

The Schur module `L_λ = Im(c_λ)` where `c_λ² = α · c_λ`. So `(1/α) · c_λ` is
an idempotent projector, and the formal character equals the trace of this
projector against the diagonal GL action:

  `ch(L_λ) = (1/α) · ∑_{σ ∈ S_n} c_λ(σ) · Tr(σ acting on V^{⊗n} restricted to diagonal)`

where the trace of σ acting on `V^{⊗n}` restricted to a diagonal matrix `diag(x₁,…,x_N)`
gives `permTracePoly N σ`. -/

/-- **Trace formula**: The formal character of the Schur module equals
`α⁻¹ · ∑_{σ ∈ S_n} c_λ(σ) · permTracePoly(N, σ)`.

This follows from `L_λ = Im(c_λ)` where `(1/α) · c_λ` is an idempotent
projector onto `L_λ`, and the trace of a projector gives the character
of its image. The trace of each permutation σ acting on the tensor power
`V^{⊗n}` evaluated on diagonal matrices gives `permTracePoly N σ`. -/
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
  sorry

/-! #### Step 2: Young symmetrizer weighted sum of permTracePoly equals α · schurPoly

This is the combinatorial/representation-theoretic identity: grouping the sum
`∑_σ c_λ(σ) · permTracePoly(N, σ)` by conjugacy class (= cycle type) and
applying the Frobenius formula (Proposition 5.21.1) plus character orthogonality
for S_n yields `α · s_λ(x)`. -/

/-- **Frobenius + orthogonality**: The Young-symmetrizer-weighted sum of
permutation trace polynomials equals `α · schurPoly N lam`.

Proof strategy: Group the sum by conjugacy class (= cycle type μ ⊢ n).
For each conjugacy class, `permTracePoly` is constant (= power sum product `p_μ`
by `permTracePoly_eq_powerSumCycleProduct`). The coefficient becomes
`∑_{σ of type μ} c_λ(σ)`, which is the character `χ^λ(μ)` of `S_n` at μ
times the size of the conjugacy class divided by appropriate normalization.
By the Frobenius formula (`Proposition5_21_1`), `s_λ = ∑_μ (1/z_μ) χ^λ(μ) p_μ`.
Character orthogonality for `S_n` then collapses the sum to `α · s_λ`. -/
theorem sum_youngSym_permTracePoly_eq_alpha_schurPoly
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (α : ℚ) (hα : α ≠ 0)
    (hα_sq : YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) *
      YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) =
      α • YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam)) :
    ∑ σ : Equiv.Perm (Fin (∑ i, lam i)),
      (YoungSymmetrizerK ℚ (∑ i, lam i) (weightToPartition N lam) σ : ℚ) •
        permTracePoly N σ = α • schurPoly N lam := by
  sorry

set_option maxHeartbeats 800000 in
/-- The trace of left multiplication by `c` in `MonoidAlgebra ℚ G` equals `|G| · c(1)`. -/
private theorem monoidAlgebra_trace_mulLeft_eq
    {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (c : MonoidAlgebra ℚ G) :
    LinearMap.trace ℚ _ (LinearMap.mulLeft ℚ c) =
      Fintype.card G * c 1 := by
  set b := MonoidAlgebra.basis G ℚ
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  have hdiag : ∀ σ : G, b.repr (LinearMap.mulLeft ℚ c (b σ)) σ = c 1 := by
    intro σ
    -- b.repr is identity, b σ = single σ 1, (c * single σ 1)(σ) = c(σσ⁻¹) = c(1)
    rw [LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]
    -- b.repr is identity for MonoidAlgebra.basis
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
  -- c² = 0, so left multiplication by c is nilpotent
  have hnil : IsNilpotent (LinearMap.mulLeft ℚ c) := by
    refine ⟨2, LinearMap.ext fun x => ?_⟩
    change (LinearMap.mulLeft ℚ c) ((LinearMap.mulLeft ℚ c) x) = 0
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, hα_sq, zero_mul]
  -- Nilpotent trace is nilpotent, hence 0 in ℚ (reduced ring)
  have htr_nil := LinearMap.isNilpotent_trace_of_isNilpotent hnil
  rw [isNilpotent_iff_eq_zero] at htr_nil
  -- But trace = n! · c(1) = n!
  rw [monoidAlgebra_trace_mulLeft_eq] at htr_nil
  have hone : c 1 = 1 := by
    rw [hc_def, YoungSymmetrizerK_eq_mapRange ℚ n la]
    simp [MonoidAlgebra.mapRangeRingHom_apply, YoungSymmetrizerZ_apply_one]
  rw [hone, mul_one] at htr_nil
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (by rwa [Fintype.card_perm, Fintype.card_fin] at htr_nil)

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
