import Mathlib

/-!
# Corollary 5.15.4: Cauchy Identity

The Cauchy identity states:

  det(1/(1 - xᵢyⱼ))_{1≤i,j≤N} = Σ_{σ ∈ S_N} (-1)^σ / ∏_j (1 - xⱼ · y_{σ(j)})

This is a power series identity in the variables x₁,...,xₙ, y₁,...,yₙ.
A key consequence is that the coefficient of x^{λ+ρ} · y^{λ+ρ} on the
right-hand side equals 1.

## Mathlib correspondence

This is a classical identity in combinatorial algebra. Uses multivariate
formal power series (`MvPowerSeries`) and `Matrix.det`.
-/

open Finset Equiv.Perm MvPowerSeries

noncomputable section

namespace Etingof

variable (N : ℕ) (k : Type*) [Field k]

/-- The variables for the Cauchy identity: `N` x-variables and `N` y-variables,
indexed by `Fin N ⊕ Fin N` (left = x, right = y). -/
abbrev CauchyVars (N : ℕ) := Fin N ⊕ Fin N

/-- The `(i,j)`-th entry of the Cauchy matrix: the formal power series `1/(1 - xᵢ yⱼ)`
in `2N` variables. This is the geometric series `∑_{n≥0} (xᵢ yⱼ)^n`. -/
noncomputable def cauchyMatrixEntry (i j : Fin N) :
    MvPowerSeries (CauchyVars N) k :=
  MvPowerSeries.invOfUnit
    (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j))
    1  -- invertible as a power series since constant term is 1

/-- The Cauchy matrix: the `N × N` matrix whose `(i,j)`-th entry is `1/(1 - xᵢ yⱼ)`.
-/
noncomputable def cauchyMatrix :
    Matrix (Fin N) (Fin N) (MvPowerSeries (CauchyVars N) k) :=
  Matrix.of (fun i j => cauchyMatrixEntry N k i j)

/-- The right-hand side of the Cauchy identity:
`Σ_{σ ∈ S_N} (-1)^σ / ∏_j (1 - xⱼ · y_{σ(j)})`. -/
noncomputable def cauchyRHS :
    MvPowerSeries (CauchyVars N) k :=
  ∑ σ : Equiv.Perm (Fin N),
    (MvPowerSeries.C (Int.cast (Equiv.Perm.sign σ : ℤ) : k)) *
      ∏ j : Fin N,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
          1

/-- **Corollary 5.15.4** (Cauchy identity): The determinant of the matrix
`(1/(1 - xᵢ yⱼ))_{i,j}` equals `Σ_{σ ∈ S_N} (-1)^σ / ∏_j (1 - xⱼ · y_{σ(j)})`.

This is a formal power series identity in `2N` variables `x₁,...,x_N, y₁,...,y_N`.
(Etingof Corollary 5.15.4) -/
theorem Corollary5_15_4
    (N : ℕ) :
    (cauchyMatrix N k).det = cauchyRHS N k := by
  simp only [Matrix.det_apply', cauchyRHS, cauchyMatrix, Matrix.of_apply, cauchyMatrixEntry]
  -- LHS: ∑ σ, ↑↑(sign σ) * ∏ i, invOfUnit(1 - x_{σ i} y_i) 1
  -- RHS: ∑ σ, C ↑↑(sign σ) * ∏ j, invOfUnit(1 - x_j y_{σ j}) 1
  -- Reindex the sum by σ ↦ σ⁻¹
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin N)))
  intro σ
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  · -- ↑↑(sign σ) = C ↑↑(sign σ) : intCast factors through C
    exact (map_intCast (MvPowerSeries.C (σ := CauchyVars N) (R := k)) _).symm
  · -- ∏ i, invOfUnit(1 - x_{σ i} y_i) = ∏ j, invOfUnit(1 - x_j y_{σ⁻¹ j})
    -- Reindex product by j = σ i
    exact Fintype.prod_equiv σ _ _ (fun i => by simp)

end Etingof
