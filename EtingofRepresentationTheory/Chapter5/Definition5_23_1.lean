import Mathlib

/-!
# Definition 5.23.1: Algebraic Representation of GL(V)

A finite dimensional representation Y of GL(V) is **algebraic** (or rational,
or polynomial) if its matrix elements are polynomial functions of the entries
of g, g⁻¹, for g ∈ GL(V) — i.e., belong to k[gᵢⱼ][1/det(g)].

## Mathlib correspondence

- `Matrix.GeneralLinearGroup (Fin n) k` for GL_n(k)
- `MvPolynomial` for multivariate polynomials over k
- `Basis.repr` for matrix coefficients of the representation
-/

/-- The type of variables for the coordinate ring of GL_n:
matrix entries (Fin n × Fin n) together with one extra variable
representing 1/det(g). -/
abbrev Etingof.GLCoordVars (n : ℕ) := (Fin n × Fin n) ⊕ Unit

/-- Evaluate a polynomial in `k[Xᵢⱼ, D]` at a matrix g ∈ GL_n(k),
substituting Xᵢⱼ ↦ gᵢⱼ and D ↦ det(g)⁻¹. -/
noncomputable def Etingof.evalAtGL {k : Type*} [Field k] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : MvPolynomial (Etingof.GLCoordVars n) k) : k :=
  MvPolynomial.eval
    (Sum.elim (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
              (fun _ => ((g : Matrix (Fin n) (Fin n) k).det)⁻¹))
    p

/-- A finite-dimensional representation ρ of GL_n(k) on Y is **algebraic**
(also called rational or polynomial) if there exists a basis of Y such that
all matrix coefficients of ρ(g) are polynomial functions of the matrix entries
gᵢⱼ and det(g)⁻¹.

Concretely: there exist polynomials Pₐ_c ∈ k[Xᵢⱼ, D] (where Xᵢⱼ are
variables for the n² matrix entries and D represents 1/det) such that
for all g ∈ GL_n(k), the (a,c)-th matrix coefficient of ρ(g) equals
Pₐ_c(gᵢⱼ, det(g)⁻¹).

(Etingof Definition 5.23.1) -/
def Etingof.IsAlgebraicRepresentation
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (Etingof.GLCoordVars n) k),
    ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (ρ g (b c)) a = Etingof.evalAtGL g (P a c)
