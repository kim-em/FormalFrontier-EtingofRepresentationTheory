import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Corollary 4.2.2: Number of Irreducible Representations

The number of isomorphism classes of irreducible representations of G equals
the number of conjugacy classes of G (assuming k is algebraically closed and
char(k) does not divide |G|).

## Proof strategy

We use the center dimension argument:
1. dim center(k[G]) = |ConjClasses G| (class sums form a basis)
2. dim center(∏ Mat(dᵢ, k)) = n (one scalar per block)
3. The Wedderburn iso k[G] ≃ₐ ∏ Mat preserves centers
4. Therefore n = |ConjClasses G|
-/

open FDRep CategoryTheory

universe u

section CenterDimension

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [NeZero (Nat.card G : k)]

/-! #### Helper: characterize center of MonoidAlgebra -/

/-- Central elements of `MonoidAlgebra k G` have conjugation-invariant coefficients. -/
private lemma center_coeff_conj_invariant
    {a : MonoidAlgebra k G} (ha : a ∈ Subalgebra.center k (MonoidAlgebra k G))
    (g h : G) : a (g * h * g⁻¹) = a h := by
  rw [Subalgebra.mem_center_iff] at ha
  have key := congr_fun (congr_arg (⇑) (ha (MonoidAlgebra.of k G g))) (g * h)
  simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk,
    MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
    one_mul, mul_one, inv_mul_cancel_left] at key
  exact key.symm

/-- Elements with conjugation-invariant coefficients are central in `MonoidAlgebra k G`. -/
private lemma mem_center_of_conj_invariant (a : MonoidAlgebra k G)
    (ha : ∀ g h : G, a (g * h * g⁻¹) = a h) :
    a ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    ext x
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply,
      MonoidAlgebra.mul_single_apply, one_mul, mul_one]
    -- Need: a (g⁻¹ * x) = a (x * g⁻¹)
    -- ha g⁻¹ (x * g⁻¹) : a (g⁻¹ * (x * g⁻¹) * (g⁻¹)⁻¹) = a (x * g⁻¹)
    -- LHS simplifies to a (g⁻¹ * x) by group
    have h1 := ha g⁻¹ (x * g⁻¹)
    simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h1
    exact h1
  | hadd b₁ b₂ hb₁ hb₂ =>
    rw [mul_add, add_mul, hb₁, hb₂]
  | hsmul r b hb =>
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hb]

/-! #### Dimension of center(MonoidAlgebra k G) = |ConjClasses G| -/

/-- The center of `MonoidAlgebra k G` has `finrank` equal to `card (ConjClasses G)`. -/
private lemma finrank_center_monoidAlgebra :
    Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Fintype.card (ConjClasses G) := by
  -- Forward map: center → (ConjClasses G → k)
  let fwd : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k] (ConjClasses G → k) :=
    { toFun := fun a C => (a : MonoidAlgebra k G) (Quotient.out C)
      map_add' := fun _ _ => funext fun _ => Finsupp.add_apply _ _ _
      map_smul' := fun _ _ => funext fun _ => Finsupp.smul_apply _ _ _ }
  -- Backward map: (ConjClasses G → k) → center
  let bwd : (ConjClasses G → k) →ₗ[k] ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
    { toFun := fun f => ⟨Finsupp.onFinset Finset.univ
          (fun g => f (ConjClasses.mk g)) (fun _ _ => Finset.mem_univ _),
        mem_center_of_conj_invariant _ (fun g h => by
          simp only [Finsupp.onFinset_apply]
          congr 1
          rw [ConjClasses.mk_eq_mk_iff_isConj]
          exact isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩
      map_add' := fun f₁ f₂ => Subtype.ext (Finsupp.ext fun g => by
        simp [Finsupp.onFinset_apply])
      map_smul' := fun r f => Subtype.ext (Finsupp.ext fun g => by
        simp [Finsupp.onFinset_apply]) }
  -- Round trips
  have hfb : ∀ f, fwd (bwd f) = f := fun f => funext fun C => by
    simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
    congr 1; exact Quotient.out_eq C
  have hbf : ∀ a : ↥(Subalgebra.center k (MonoidAlgebra k G)), bwd (fwd a) = a :=
    fun ⟨a, ha⟩ => by
    ext g
    simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
    -- Need: a (Quotient.out (ConjClasses.mk g)) = a g
    have hconj : IsConj (Quotient.out (ConjClasses.mk g) : G) g := by
      have h := Quotient.out_eq (ConjClasses.mk g)
      rw [ConjClasses.quotient_mk_eq_mk] at h
      exact ConjClasses.mk_eq_mk_iff_isConj.mp h
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [show a (Quotient.out (ConjClasses.mk g)) =
        a (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
      (center_coeff_conj_invariant ha c _).symm, hc]
  -- Combine into LinearEquiv
  have e : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k] (ConjClasses G → k) :=
    { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
  have : Module.finrank k (ConjClasses G → k) = Fintype.card (ConjClasses G) :=
    Module.finrank_fintype_fun_eq_card k
  linarith [e.finrank_eq]

/-! #### Dimension of center(∏ Mat(d_i, k)) = n -/

/-- The center of a product of matrix algebras has finrank equal to the number of factors. -/
private lemma finrank_center_pi_matrix (D : IrrepDecomp k G) :
    Module.finrank k ↥(Subalgebra.center k
      (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)) = D.n := by
  -- Abbreviation for the pi type
  let PiMat := (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)
  -- Forward: extract (0,0) entry from each block
  let fwd : ↥(Subalgebra.center k PiMat) →ₗ[k] (Fin D.n → k) :=
    { toFun := fun a i =>
        haveI := D.d_pos i
        (a : PiMat) i ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
          ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  -- Backward: embed scalars as scalar matrices
  let bwd_fun : (Fin D.n → k) → PiMat :=
    fun c i => c i • (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k)
  have bwd_mem : ∀ c, bwd_fun c ∈ Subalgebra.center k PiMat := fun c => by
    rw [Subalgebra.mem_center_iff]; intro N; ext i : 1
    change N i * (c i • 1) = (c i • 1) * N i
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  let bwd : (Fin D.n → k) →ₗ[k] ↥(Subalgebra.center k PiMat) :=
    { toFun := fun c => ⟨bwd_fun c, bwd_mem c⟩
      map_add' := fun c₁ c₂ => by
        apply Subtype.ext; funext i
        change (c₁ i + c₂ i) • (1 : Matrix _ _ k) = _
        rw [add_smul]; rfl
      map_smul' := fun r c => by
        apply Subtype.ext; funext i
        change (r * c i) • (1 : Matrix _ _ k) = _
        rw [mul_smul]; rfl }
  -- Forward ∘ backward = id
  have hfb : ∀ c, fwd (bwd c) = c := fun c => funext fun i => by
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    simp [Matrix.smul_apply]
  -- Backward ∘ forward = id
  have hbf : ∀ x : ↥(Subalgebra.center k PiMat), bwd (fwd x) = x := fun ⟨f, hf⟩ => by
    apply Subtype.ext; ext i a b
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    -- f i is central in its matrix block
    have hfc : f i ∈ Subalgebra.center k (Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
      rw [Subalgebra.mem_center_iff]; intro M
      have hf' : ∀ b : PiMat, b * f = f * b := Subalgebra.mem_center_iff.mp hf
      have h := hf' (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M)
      -- Evaluate h at component i
      have lhs : (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M * f) i =
          M * f i := by rw [Pi.mul_apply, Pi.single_eq_same]
      have rhs : (f * Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M) i =
          f i * M := by rw [Pi.mul_apply, Pi.single_eq_same]
      rw [show M * f i = (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M * f) i
        from lhs.symm, h, rhs]
    -- Center of matrix algebra = ⊥ by IsCentral, so f i is a scalar matrix
    rw [Algebra.IsCentral.center_eq_bot] at hfc
    rw [Algebra.mem_bot] at hfc
    obtain ⟨c, hc⟩ := Set.mem_range.mp hfc
    have hfi : f i = c • (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
      rw [← hc, Algebra.algebraMap_eq_smul_one]
    rw [hfi]; simp [Matrix.smul_apply, Matrix.one_apply]
  -- Combine
  have e : ↥(Subalgebra.center k PiMat) ≃ₗ[k] (Fin D.n → k) :=
    { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
  have : Module.finrank k (Fin D.n → k) = D.n := by
    rw [Module.finrank_fintype_fun_eq_card k, Fintype.card_fin]
  linarith [e.finrank_eq]

/-! #### AlgEquiv preserves center finrank -/

/-- An algebra isomorphism restricts to a linear equivalence on centers. -/
private noncomputable def AlgEquiv.centerLinearEquiv
    {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    ↥(Subalgebra.center R A) ≃ₗ[R] ↥(Subalgebra.center R B) where
  toFun := fun ⟨a, ha⟩ => ⟨e a, by
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro b; obtain ⟨a', rfl⟩ := e.surjective b
    simp [← map_mul, ha a']⟩
  invFun := fun ⟨b, hb⟩ => ⟨e.symm b, by
    rw [Subalgebra.mem_center_iff] at hb ⊢
    intro a; apply e.injective
    simp [map_mul, hb (e a)]⟩
  left_inv := by intro ⟨a, _⟩; ext; simp
  right_inv := by intro ⟨b, _⟩; ext; simp
  map_add' := by intro ⟨a, _⟩ ⟨b, _⟩; ext; simp [map_add]
  map_smul' := by intro r ⟨a, _⟩; ext; simp [Algebra.smul_def, map_mul]

/-! #### Combine: n = |ConjClasses G| -/

/-- The number of Wedderburn blocks equals the number of conjugacy classes. -/
private theorem IrrepDecomp.n_eq_card_conjClasses' (D : IrrepDecomp k G) :
    D.n = Fintype.card (ConjClasses G) := by
  have h1 := (AlgEquiv.centerLinearEquiv D.iso).finrank_eq
  have h2 := finrank_center_pi_matrix D
  have h3 := finrank_center_monoidAlgebra (k := k) (G := G)
  linarith

end CenterDimension

/-- The number of isomorphism classes of irreducible representations equals the number
of conjugacy classes: there exist exactly `Fintype.card (ConjClasses G)` pairwise
non-isomorphic simple representations, and every simple representation is isomorphic
to one of them. (Etingof Corollary 4.2.2) -/
theorem Etingof.Corollary4_2_2
    {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {k : Type u} [Field k] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      n = Fintype.card (ConjClasses G) := by
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero
  let D := IrrepDecomp.mk' (k := k) (G := G)
  obtain ⟨V, hsimp, hinj, hsurj⟩ := D.n_eq_card_simples
  exact ⟨D.n, V, hsimp, hinj, hsurj, D.n_eq_card_conjClasses'⟩
