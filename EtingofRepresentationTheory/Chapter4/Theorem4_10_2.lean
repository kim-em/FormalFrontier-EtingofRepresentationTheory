import Mathlib

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

/-- The Frobenius determinant factors into irreducible polynomials, one for each
irreducible representation, with multiplicity equal to the dimension.
(Etingof Theorem 4.10.2) -/
theorem Etingof.Theorem4_10_2
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    -- det X_G = ∏ⱼ Pⱼ^(deg Pⱼ) with r factors
    True := by  -- TODO: needs Frobenius determinant definition and irreducibility API
  sorry
