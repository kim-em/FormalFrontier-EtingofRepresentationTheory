import Mathlib
import EtingofRepresentationTheory.Chapter4.Definition4_10_1
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Chapter4.Lemma4_10_3

/-!
# Theorem 4.10.2: Factorization of the Frobenius Determinant

The Frobenius determinant factors as:
$$\det X_G = \prod_{j=1}^{r} P_j(\mathbf{x})^{\deg P_j}$$
where P₁, …, Pᵣ are pairwise non-proportional irreducible polynomials over ℂ,
and r is the number of conjugacy classes (= number of irreducible representations).

The factor Pⱼ corresponds to the j-th irreducible representation Vⱼ of G, with
deg Pⱼ = dim Vⱼ. The proof uses the Artin–Wedderburn decomposition of ℂ[G] and
the multiplicativity of determinants.

## Mathlib correspondence

Not in Mathlib. This is Frobenius's original factorization theorem connecting the
group determinant to representation theory.
-/

universe u

open MvPolynomial Matrix Finset

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]

/-! ### Block polynomial definition -/

/-- The block polynomial for the i-th Wedderburn component: the determinant of
the matrix ∑_g x_g · ρ_i(g), where ρ_i is the i-th irreducible representation.
This is a polynomial of degree d_i in the variables {x_g : g ∈ G}. -/
noncomputable def IrrepDecomp.blockPoly [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : MvPolynomial G k :=
  det (of fun (a b : Fin (D.d i)) =>
    ∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g)

/-! ### Helper lemmas for the factorization proof -/

section NormHelpers

variable (R : Type*) [CommRing R]

/-- The algebra norm of an element in a product of algebras equals the product of
the norms of the components. Uses the fact that left multiplication is block diagonal
in the product basis. -/
private lemma Algebra.norm_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  -- Induction on ι via Fintype.induction_empty_option
  apply Fintype.induction_empty_option
    (P := fun (ι : Type _) [Fintype ι] => ∀ (A : ι → Type _) [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (x : ∀ i, A i),
        Algebra.norm R x = ∏ i, Algebra.norm R (x i))
  · -- of_equiv case
    intro α β hβ e IH A hRingA hAlgA hFreeA hFiniteA x
    let eA : (∀ i : α, A (e i)) ≃ₐ[R] (∀ i : β, A i) := AlgEquiv.piCongrLeft R A e
    have hkey : Algebra.norm R (eA.symm x) = Algebra.norm R x :=
      Algebra.norm_eq_of_algEquiv eA.symm x
    have hval : eA.symm x = fun i => x (e i) := by
      ext i
      rw [show (eA.symm x) i = ((Equiv.piCongrLeft (fun j => A j) e).symm x) i from rfl]
      rw [Equiv.piCongrLeft_symm_apply]
    rw [← hkey, hval]
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [IH (A := fun i => A (e i)) (x := fun i => x (e i))]
    exact Fintype.prod_equiv e (fun i => Algebra.norm R (x (e i)))
      (fun i => Algebra.norm R (x i)) (fun i => rfl)
  · -- h_empty case: PEmpty
    intro A _ _ _ _ x
    simp only [Fintype.prod_empty]
    have hx : x = 1 := by ext i; exact PEmpty.elim i
    rw [hx, map_one]
  · -- h_option case: Option ι'
    intro ι' _ IH A _ _ _ _ x
    haveI : DecidableEq ι' := Classical.decEq ι'
    -- Build AlgEquiv for (∀ i : Option ι', A i) ≃ₐ[R] A none × (∀ i, A (some i))
    let e : (∀ i : Option ι', A i) ≃ₐ[R] A none × (∀ i, A (some i)) :=
      { RingEquiv.piOptionEquivProd with
        commutes' := fun r => by
          ext i
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd] }
    have hstep : Algebra.norm R (e x) = Algebra.norm R x := Algebra.norm_eq_of_algEquiv e x
    have IHsome := IH (A := fun i => A (some i))
    -- norm of a product ring is the product of norms (for specific pair type)
    have norm_pair : Algebra.norm R (e x) = Algebra.norm R (e x).1 * Algebra.norm R (e x).2 := by
      simp only [Algebra.norm_apply]
      rw [show Algebra.lmul R (A none × (∀ i, A (some i))) (e x) =
          LinearMap.prodMap (Algebra.lmul R (A none) (e x).1)
            (Algebra.lmul R (∀ i, A (some i)) (e x).2) from ?hlmul]
      · exact LinearMap.det_prodMap _ _
      case hlmul =>
        apply LinearMap.ext; intro ⟨a, b⟩
        simp only [Algebra.coe_lmul_eq_mul, LinearMap.prodMap_apply]; rfl
    rw [← hstep]
    rw [norm_pair]
    simp only [show (e x).1 = x none from rfl, show (e x).2 = fun i => x (some i) from rfl]
    rw [IHsome, Fintype.prod_option]

/-- The algebra norm of a matrix `M : Matrix (Fin n) (Fin n) R` (viewed as an element
of the matrix algebra over R) equals `det(M) ^ n`. Left multiplication by M on Mat(n,R)
acts as M on each column independently, giving `M ⊗ₖ 1` whose determinant is `det(M)^n`. -/
private lemma Algebra.norm_matrix {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) R) :
    Algebra.norm R M = M.det ^ n := by
  open Kronecker in
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R (Fin n) (Fin n))]
  have hkron : Algebra.leftMulMatrix (Matrix.stdBasis R (Fin n) (Fin n)) M =
      M ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.kroneckerMap_apply, Matrix.one_apply,
               Matrix.stdBasis_eq_single]
    have hmul : M * Matrix.single i₂ j₂ (1 : R) =
        Matrix.of (fun r c => M r i₂ * if c = j₂ then 1 else 0) := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single i₂]
      · simp [eq_comm]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [hmul]
    simp [Matrix.stdBasis, Equiv.sigmaEquivProd_symm_apply, Pi.basis_repr, Pi.basisFun_repr,
          Matrix.ofLinearEquiv]
  open Kronecker in
  rw [hkron, Matrix.det_kronecker, Matrix.det_one, Fintype.card_fin, one_pow, mul_one]

end NormHelpers

/-! ### Helper lemmas for factorization proof -/

/-- The left multiplication matrix of `a : MonoidAlgebra k G` in the Finsupp basis
has `(g, h)` entry `a (g * h⁻¹)`. -/
private lemma leftMulMatrix_monoidAlgebra_entry
    (a : MonoidAlgebra k G) (g h : G) :
    Algebra.leftMulMatrix (Finsupp.basisSingleOne (R := k)) a g h =
      a (g * h⁻¹) := by
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Finsupp.basisSingleOne_repr,
    Finsupp.coe_basisSingleOne]
  exact (a.mul_single_apply_aux
    (fun m' _ => eq_mul_inv_iff_mul_eq.symm)).trans (mul_one _)

/-- The projection ring homomorphism commutes with scalar multiplication. -/
private lemma IrrepDecomp.projRingHom_smul' [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n)
    (r : k) (a : MonoidAlgebra k G) :
    D.projRingHom i (r • a) = r • D.projRingHom i a := by
  simp [IrrepDecomp.projRingHom]

/-- The Frobenius determinant equals the product of block polynomials raised to their
respective dimensions. -/
private lemma IrrepDecomp.frobeniusDet_eq_prod [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    Etingof.FrobeniusDeterminant k G = ∏ i : Fin D.n, D.blockPoly i ^ D.d i := by
  -- Use funext: reduce to showing equality for all evaluations σ : G → k
  haveI : Infinite k := IsAlgClosed.instInfinite
  apply MvPolynomial.funext
  intro σ
  -- Define the group algebra element corresponding to σ
  set a : MonoidAlgebra k G := ∑ s : G, σ s • MonoidAlgebra.of k G s with ha_def
  -- Evaluate LHS: det of group matrix
  have hLHS : MvPolynomial.eval σ (Etingof.FrobeniusDeterminant k G) =
      (Matrix.of fun g h : G => σ (g * h⁻¹)).det := by
    unfold Etingof.FrobeniusDeterminant
    rw [RingHom.map_det]
    congr 1; ext g h; simp [Matrix.map, Matrix.of_apply, MvPolynomial.eval_X]
  -- Evaluate RHS: product of block determinants
  have hRHS : MvPolynomial.eval σ (∏ i : Fin D.n, D.blockPoly i ^ D.d i) =
      ∏ i : Fin D.n, (MvPolynomial.eval σ (D.blockPoly i)) ^ D.d i := by
    rw [map_prod]; congr 1; ext i; rw [map_pow]
  -- Each blockPoly evaluates to det of projRingHom i a
  have hblock_eq : ∀ i : Fin D.n, MvPolynomial.eval σ (D.blockPoly i) =
      (D.projRingHom i a).det := by
    intro i
    unfold IrrepDecomp.blockPoly
    rw [RingHom.map_det]
    congr 1
    funext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [ha_def, map_sum]
    simp only [D.projRingHom_smul' i, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro g _; ring
  -- The LHS matrix det equals Algebra.norm k a
  have hLHS_eq : (Matrix.of fun g h : G => σ (g * h⁻¹)).det = Algebra.norm k a := by
    rw [Algebra.norm_eq_matrix_det (Finsupp.basisSingleOne (R := k))]
    congr 1
    funext g h
    rw [of_apply, leftMulMatrix_monoidAlgebra_entry]
    change σ (g * h⁻¹) = (∑ s : G, σ s • MonoidAlgebra.of k G s : MonoidAlgebra k G) (g * h⁻¹)
    rw [Finsupp.finset_sum_apply]
    simp [MonoidAlgebra.of_apply, Finsupp.smul_apply, Finsupp.single_apply]
  -- Chain the equalities
  rw [hLHS, hRHS]
  simp_rw [hblock_eq]
  rw [hLHS_eq]
  -- Now: Algebra.norm k a = ∏ i, (projRingHom i a).det ^ d i
  rw [show Algebra.norm k a = Algebra.norm k (D.iso a) from
    (Algebra.norm_eq_of_algEquiv D.iso a).symm]
  rw [Algebra.norm_pi k]
  congr 1; ext i
  haveI := D.d_pos i
  rw [Algebra.norm_matrix k]
  -- D.iso a i = projRingHom i a: handled by congr
  congr 2

/-- Each block polynomial is irreducible. The proof uses Lemma 4.10.3 (the generic
determinant is irreducible) combined with surjectivity of the Wedderburn projection
(which ensures the linear substitution defining the block polynomial is surjective,
preserving irreducibility). -/
private lemma IrrepDecomp.blockPoly_irreducible [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Irreducible (D.blockPoly i) := by
  sorry

/-- Block polynomials for different Wedderburn components are not associated.
If d_i ≠ d_j, they have different total degrees. If d_i = d_j, they involve
different linear combinations of variables (by the injectivity of column FDReps). -/
private lemma IrrepDecomp.blockPoly_not_associated [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i j : Fin D.n) (hij : i ≠ j) :
    ¬Associated (D.blockPoly i) (D.blockPoly j) := by
  sorry

/-- The total degree of the i-th block polynomial equals d_i. Each entry of the
representation matrix is a linear polynomial in the x_g, so det has degree ≤ d_i.
For ≥ d_i, evaluation at x₁=t, xg=0 gives det(tI)=t^{d_i}. -/
private lemma IrrepDecomp.blockPoly_totalDegree [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    (D.blockPoly i).totalDegree = D.d i := by
  apply le_antisymm
  · -- ≤ d_i: det of matrix with degree-1 entries
    unfold blockPoly
    let M := of fun (a b : Fin (D.d i)) =>
      ∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g
    show (det M).totalDegree ≤ D.d i
    rw [det_apply]
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le
    intro σ _
    have hsmul : (Equiv.Perm.sign σ • ∏ a, M (σ a) a).totalDegree =
        (∏ a, M (σ a) a).totalDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · simp [h]
      · simp [h, totalDegree_neg]
    rw [hsmul]
    calc (∏ a, M (σ a) a).totalDegree
        ≤ ∑ a, (M (σ a) a).totalDegree := totalDegree_finset_prod _ _
      _ ≤ ∑ _a : Fin (D.d i), 1 := by
          apply Finset.sum_le_sum; intro a _
          show (∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) (σ a) a) *
            X g).totalDegree ≤ 1
          apply (totalDegree_finset_sum _ _).trans
          apply Finset.sup_le; intro g _
          calc MvPolynomial.totalDegree (C _ * X g)
              ≤ MvPolynomial.totalDegree (C _) +
                MvPolynomial.totalDegree (X g) := totalDegree_mul _ _
            _ = 0 + 1 := by rw [totalDegree_C, totalDegree_X]
            _ = 1 := by ring
      _ = D.d i := by simp
  · -- ≥ d_i: blockPoly is homogeneous of degree d_i and nonzero
    -- Step 1: each entry is homogeneous of degree 1
    have hentry : ∀ (a b : Fin (D.d i)),
        (∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) *
          X g).IsHomogeneous 1 :=
      fun a b => IsHomogeneous.sum _ _ _ fun g _ =>
        (MvPolynomial.isHomogeneous_C (σ := G)
          (D.projRingHom i (MonoidAlgebra.of k G g) a b)).mul
          (MvPolynomial.isHomogeneous_X (R := k) g)
    -- Step 2: blockPoly is homogeneous of degree d_i
    have hhom : (D.blockPoly i).IsHomogeneous (D.d i) := by
      unfold blockPoly; rw [det_apply]
      apply IsHomogeneous.sum; intro σ _
      have hprod : IsHomogeneous (∏ a : Fin (D.d i),
          of (fun a b => ∑ g : G,
            C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g)
          (σ a) a) (∑ _a : Fin (D.d i), 1) := by
        apply IsHomogeneous.prod; intro a _
        exact hentry (σ a) a
      simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at hprod
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hprod
      · simp only [h, Units.smul_def] at *
        rw [show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul]
        exact (homogeneousSubmodule G k (D.d i)).neg_mem hprod
    -- Step 3: blockPoly is nonzero (eval at x₁=1, rest=0 gives det(I)=1)
    have hne : D.blockPoly i ≠ 0 := by
      intro h
      have heval : MvPolynomial.eval
          (fun g => if g = (1 : G) then (1 : k) else 0) (D.blockPoly i) = 1 := by
        unfold blockPoly
        rw [show MvPolynomial.eval _ (det _) = det
          ((MvPolynomial.eval _).mapMatrix _) from RingHom.map_det _ _]
        have hmat : (MvPolynomial.eval
            (fun g => if g = (1 : G) then (1 : k) else 0)).mapMatrix
            (of fun a b => ∑ g : G,
              C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g) =
            (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
          ext a b
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply,
            map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
            one_apply]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
          have : D.projRingHom i (MonoidAlgebra.of k G 1) = 1 := by
            have h1 : MonoidAlgebra.of k G (1 : G) = 1 := map_one _
            rw [h1, map_one]
          rw [this]; simp [one_apply]
        rw [hmat, det_one]
      rw [h, map_zero] at heval; exact one_ne_zero heval.symm
    -- Step 4: combine
    exact (hhom.totalDegree hne).symm.le

/-- The number of Wedderburn-Artin components equals the number of conjugacy classes.
Proof: dim center(k[G]) = |ConjClasses G| (class functions) and
dim center(∏ Mat(d_i,k)) = n (scalar matrices), and the Wedderburn iso preserves centers. -/
private lemma IrrepDecomp.n_eq_card_conjClasses [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    D.n = Fintype.card (ConjClasses G) := by
  sorry

/-! ### Main theorem -/

/-- The Frobenius determinant factors into r pairwise non-associated irreducible polynomials,
each raised to the power of its total degree, where r equals the number of conjugacy classes.
Specifically, det(X_G) = ∏_{j=1}^{r} P_j^(deg P_j), where the P_j are irreducible and
pairwise non-proportional, and the total degree satisfies Σ (deg P_j)² = |G|.
(Etingof Theorem 4.10.2) -/
theorem Etingof.Theorem4_10_2
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : k)] :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial G k),
      (∀ j, Irreducible (P j)) ∧
      (∀ i j, i ≠ j → ¬Associated (P i) (P j)) ∧
      Etingof.FrobeniusDeterminant k G = ∏ j : Fin r, P j ^ (P j).totalDegree ∧
      r = Fintype.card (ConjClasses G) := by
  -- Derive NeZero from Invertible
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero
  -- Get the Wedderburn-Artin decomposition
  let D := IrrepDecomp.mk' (k := k) (G := G)
  -- Provide witnesses and proofs
  refine ⟨D.n, D.blockPoly, D.blockPoly_irreducible, D.blockPoly_not_associated,
    ?_, D.n_eq_card_conjClasses⟩
  -- Show: FrobeniusDeterminant = ∏ blockPoly ^ totalDegree
  conv_lhs => rw [D.frobeniusDet_eq_prod]
  congr 1; ext i
  rw [D.blockPoly_totalDegree i]
