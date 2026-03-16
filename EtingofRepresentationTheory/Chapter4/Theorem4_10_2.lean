import Mathlib
import EtingofRepresentationTheory.Chapter4.Definition4_10_1

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
  sorry
