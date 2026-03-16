import Mathlib

/-!
# Definition 4.10.1: Frobenius Determinant (Group Determinant)

The **Frobenius determinant** (or **group determinant**) of a finite group G is
det(X_G), where X_G is the |G| × |G| matrix with entries (X_G)_{i,j} = x_{gᵢgⱼ⁻¹},
and x_g are formal variables indexed by group elements.

This is a polynomial of degree |G| in the variables {x_g : g ∈ G}.

## Mathlib correspondence

Not in Mathlib. Needs a custom definition using `Matrix.det` and `MvPolynomial`.
The group determinant is related to the group algebra and its representations via
the factorization theorem (Theorem 4.10.2).
-/

/-- The Frobenius determinant (group determinant) of a finite group G.
This is the determinant of the matrix X_G with entries x_{gᵢgⱼ⁻¹}.
(Etingof Definition 4.10.1) -/
noncomputable def Etingof.FrobeniusDeterminant
    (k : Type*) (G : Type*) [CommRing k] [Group G] [Fintype G] [DecidableEq G] :
    MvPolynomial G k :=
  Matrix.det (Matrix.of fun (g h : G) => (MvPolynomial.X (g * h⁻¹) : MvPolynomial G k))
