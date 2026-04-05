import Mathlib

/-!
# Definition 5.12.1: Partitions, Young Diagrams, Young Tableaux

A **partition** λ of n is a sequence λ₁ ≥ λ₂ ≥ ... ≥ λ_p > 0 with λ₁ + ... + λ_p = n.

A **Young diagram** of λ is a collection of n unit squares arranged in p left-aligned
rows, with λᵢ squares in row i.

A **Young tableau** of shape λ is a filling of the Young diagram with numbers 1, ..., n.

The **row subgroup** P_λ ⊂ S_n consists of permutations preserving each row.
The **column subgroup** Q_λ ⊂ S_n consists of permutations preserving each column.

The **Young symmetrizer** c_λ = b_λ · a_λ where:
- a_λ = Σ_{g ∈ P_λ} g
- b_λ = Σ_{g ∈ Q_λ} sign(g) · g

## Mathlib correspondence

Mathlib has `Nat.Partition`, `YoungDiagram`, and `SemistandardYoungTableau`.
Standard Young tableaux, row/column subgroups, and Young symmetrizers need custom definitions.
-/

namespace Etingof

/-- Given a list of row lengths and a position k, return the row index
in the canonical (left-to-right, top-to-bottom) filling of the Young diagram. -/
def rowOfPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then 0 else 1 + rowOfPos ps (k - p)

/-- Given a list of row lengths and a position k, return the column index
in the canonical (left-to-right, top-to-bottom) filling of the Young diagram. -/
def colOfPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then k else colOfPos ps (k - p)

/-- The sorted (descending) parts of a partition, as a list of row lengths. -/
noncomputable def _root_.Nat.Partition.sortedParts {n : ℕ} (la : Nat.Partition n) : List ℕ :=
  la.parts.sort (· ≥ ·)

/-- A standard Young tableau of shape λ is a filling of a Young diagram with 0..n-1
such that entries increase along rows and down columns. (Etingof Definition 5.12.1)

Concretely: a bijection from cells of the diagram to `Fin n`, strictly increasing
along rows and down columns. A cell (i, j) is valid when i < number of rows and
j < length of row i (using the canonical descending-sorted parts). -/
noncomputable def StandardYoungTableau (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := la.sortedParts
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n //
    Function.Bijective f ∧
    (∀ c₁ c₂ : Cell, c₁.1.1 = c₂.1.1 → c₁.1.2 < c₂.1.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂ : Cell, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 → f c₁ < f c₂) }

/-- The row subgroup P_λ of S_n: permutations preserving each row of
the Young diagram. (Etingof Definition 5.12.1)

Two positions i, j ∈ Fin n are in the same row when `rowOfPos parts i = rowOfPos parts j`
where `parts` are the descending-sorted parts and `rowOfPos` computes the row index
in the canonical left-to-right, top-to-bottom filling. -/
noncomputable def RowSubgroup (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    rowOfPos la.sortedParts (σ k).val = rowOfPos la.sortedParts k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm

/-- The column subgroup Q_λ of S_n: permutations preserving each column of
the Young diagram. (Etingof Definition 5.12.1)

Two positions i, j ∈ Fin n are in the same column when `colOfPos parts i = colOfPos parts j`
where `parts` are the descending-sorted parts and `colOfPos` computes the column index
in the canonical left-to-right, top-to-bottom filling. -/
noncomputable def ColumnSubgroup (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    colOfPos la.sortedParts (σ k).val = colOfPos la.sortedParts k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm

/-- The row symmetrizer a_λ = ∑_{g ∈ P_λ} g in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1) -/
noncomputable def RowSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  ∑ g : (RowSubgroup n la), MonoidAlgebra.of ℂ _ g.val

/-- The column antisymmetrizer b_λ = ∑_{g ∈ Q_λ} sign(g) · g in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1) -/
noncomputable def ColumnAntisymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ g.val

/-- The Young symmetrizer c_λ = a_λ · b_λ in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1)

Here a_λ = ∑_{g ∈ P_λ} g and b_λ = ∑_{g ∈ Q_λ} sign(g) · g,
where P_λ is the row subgroup and Q_λ is the column subgroup.

**Convention**: We use c_λ = a_λ · b_λ (row × column) following James,
"The Representation Theory of the Symmetric Groups". This convention
gives left P_λ absorption: of(p) · c_λ = c_λ for p ∈ P_λ, which is
needed for the straightening lemma in the polytabloid basis proof. -/
noncomputable def YoungSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  RowSymmetrizer n la * ColumnAntisymmetrizer n la

/-! ## Helper lemmas for rowOfPos and colOfPos -/

-- colOfPos is bounded by the row width for valid positions
theorem colOfPos_lt_getD (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    colOfPos parts k < parts.getD (rowOfPos parts k) 0 := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [rowOfPos, colOfPos]
    split_ifs with hlt
    · rw [List.getD_cons_zero]; omega
    · have hk' : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      show colOfPos ps (k - p) < (p :: ps).getD (1 + rowOfPos ps (k - p)) 0
      rw [show 1 + rowOfPos ps (k - p) = rowOfPos ps (k - p) + 1 from by omega,
          List.getD_cons_succ]
      exact ih (k - p) hk'

-- (rowOfPos, colOfPos) is injective on valid positions
theorem rowOfPos_colOfPos_injective (parts : List ℕ) (k₁ k₂ : ℕ)
    (hk₁ : k₁ < parts.sum) (hk₂ : k₂ < parts.sum)
    (hrow : rowOfPos parts k₁ = rowOfPos parts k₂)
    (hcol : colOfPos parts k₁ = colOfPos parts k₂) : k₁ = k₂ := by
  induction parts generalizing k₁ k₂ with
  | nil => simp [List.sum_nil] at hk₁
  | cons p ps ih =>
    simp only [rowOfPos, colOfPos] at hrow hcol
    by_cases h₁ : k₁ < p <;> by_cases h₂ : k₂ < p
    · simp [h₁, h₂] at hcol; exact hcol
    · simp only [h₁, ite_true, h₂, ite_false] at hrow; omega
    · simp only [h₁, ite_false, h₂, ite_true] at hrow; omega
    · simp only [h₁, ite_false, h₂] at hrow hcol
      have hk₁' : k₁ - p < ps.sum := by simp [List.sum_cons] at hk₁; omega
      have hk₂' : k₂ - p < ps.sum := by simp [List.sum_cons] at hk₂; omega
      have : k₁ - p = k₂ - p := ih (k₁ - p) (k₂ - p) hk₁' hk₂' (by omega) hcol
      omega

-- For a valid cell (r, c), there exists a position with that row and column
theorem exists_pos_of_cell (parts : List ℕ) (r c : ℕ)
    (hr : c < parts.getD r 0) :
    ∃ k, k < parts.sum ∧ rowOfPos parts k = r ∧ colOfPos parts k = c := by
  induction parts generalizing r with
  | nil => simp [List.getD] at hr
  | cons p ps ih =>
    cases r with
    | zero =>
      rw [List.getD_cons_zero] at hr
      exact ⟨c, by simp [List.sum_cons]; omega,
        by simp [rowOfPos]; omega, by simp [colOfPos]; omega⟩
    | succ r =>
      rw [List.getD_cons_succ] at hr
      obtain ⟨k, hk, hrow, hcol⟩ := ih r hr
      exact ⟨p + k, by simp [List.sum_cons]; omega,
        by simp [rowOfPos]; omega,
        by simp [colOfPos]; omega⟩

end Etingof
