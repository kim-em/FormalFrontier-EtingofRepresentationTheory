import Mathlib

/-!
# Definition 5.12.1: Partitions, Young Diagrams, Young Tableaux

A **partition** λ of n is a sequence λ₁ ≥ λ₂ ≥ ... ≥ λ_p > 0 with λ₁ + ... + λ_p = n.

A **Young diagram** of λ is a collection of n unit squares arranged in p left-aligned
rows, with λᵢ squares in row i.

A **Young tableau** of shape λ is a filling of the Young diagram with numbers 1, ..., n.

The **row subgroup** P_λ ⊂ S_n consists of permutations preserving each row.
The **column subgroup** Q_λ ⊂ S_n consists of permutations preserving each column.

The **Young symmetrizer** c_λ = a_λ · b_λ where:
- a_λ = Σ_{g ∈ P_λ} g
- b_λ = Σ_{g ∈ Q_λ} sign(g) · g

## Mathlib correspondence

Mathlib has `Nat.Partition`, `YoungDiagram`, and `SemistandardYoungTableau`.
Standard Young tableaux, row/column subgroups, and Young symmetrizers need custom definitions.
-/

/-- A standard Young tableau of shape λ is a filling of a Young diagram with 1..n
such that entries increase along rows and down columns. (Etingof Definition 5.12.1) -/
def Etingof.StandardYoungTableau (n : ℕ) (la : Nat.Partition n) : Type :=
  sorry

/-- The row subgroup P_λ of S_n: permutations preserving each row of
the Young diagram. (Etingof Definition 5.12.1) -/
def Etingof.RowSubgroup (n : ℕ) (la : Nat.Partition n) : Subgroup (Equiv.Perm (Fin n)) :=
  sorry

/-- The column subgroup Q_λ of S_n: permutations preserving each column of
the Young diagram. (Etingof Definition 5.12.1) -/
def Etingof.ColumnSubgroup (n : ℕ) (la : Nat.Partition n) : Subgroup (Equiv.Perm (Fin n)) :=
  sorry

/-- The Young symmetrizer c_λ = a_λ · b_λ in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1) -/
noncomputable def Etingof.YoungSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  sorry
