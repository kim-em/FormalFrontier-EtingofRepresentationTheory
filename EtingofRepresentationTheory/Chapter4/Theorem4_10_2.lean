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

/-! ### Helper lemmas (sorry'd — these are the core mathematical content) -/

/-- The Frobenius determinant equals the product of block polynomials raised to their
respective dimensions. This follows from the Wedderburn decomposition: the matrix
(x_{gh⁻¹}) represents left multiplication by ∑ x_g · g on k[G], which under the
Wedderburn iso becomes block diagonal with blocks ∑ x_g · ρ_i(g), each appearing
d_i times. The determinant of a block diagonal matrix is the product of block
determinants. -/
private lemma IrrepDecomp.frobeniusDet_eq_prod [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    Etingof.FrobeniusDeterminant k G = ∏ i : Fin D.n, D.blockPoly i ^ D.d i := by
  sorry

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
