import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.PolytabloidBasis

/-!
# Tabloid Module Infrastructure

This file defines the **tabloid type**, **T-relative column subgroup**, and
**dominance order** needed for the polytabloid linear independence proof.

A tabloid is a left P_λ-coset of S_n: two permutations give the same tabloid iff their
"row assignments" agree (same entries in each row). The row assignment of a permutation
σ sends entry k to row rowOfPos(σ(k)).

## Main definitions

* `Etingof.TabloidSetoid` — the equivalence relation σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ
* `Etingof.Tabloid` — the quotient type (left P_λ cosets)
* `Etingof.sytToTabloid` — maps an SYT to its tabloid
* `Etingof.RelColumnSubgroup` — C_T = σ_T⁻¹ Q_λ σ_T (entry-level column stabilizer of T)
* `Etingof.tabloidDominance` — dominance partial order on tabloids

## Main results

* `Etingof.sytToTabloid_injective` — different SYTs give different tabloids
* `Etingof.RowSubgroup_inter_ColumnSubgroup` — P_λ ∩ Q_λ = {1}
* `Etingof.ColumnSubgroup_ne_tabloid` — non-identity column perms change tabloid

## Convention note

The T-relative column subgroup C_T = σ_T⁻¹ Q_λ σ_T (NOT σ_T Q_λ σ_T⁻¹). This is
the entry-level column stabilizer: π ∈ C_T iff π preserves the column sets of T.
Explicitly, for entry e, col_T(π(e)) = col_T(e) where col_T(e) = colOfPos(σ_T(e)).

The polytabloid expansion in the tabloid module is:
  e_T ↝ |P_λ| · Σ_{q ∈ Q_λ} sign(q) · toTabloid(q⁻¹ · σ_T)
where q⁻¹ · σ_T gives the tabloid {π · T} for π = σ_T⁻¹ q σ_T ∈ C_T.

## References

* James, "The Representation Theory of the Symmetric Groups", Chapter 3
-/

namespace Etingof

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}

/-! ### Tabloid equivalence relation -/

/-- Two permutations give the same tabloid (row assignment) iff they differ by a
left multiplication from the row subgroup: σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ.

This captures: entry k is in row rowOfPos(σ₁(k)) = rowOfPos(σ₂(k)) for all k. -/
def TabloidSetoid (n : ℕ) (la : Nat.Partition n) :
    Setoid (Equiv.Perm (Fin n)) where
  r σ₁ σ₂ := σ₁ * σ₂⁻¹ ∈ RowSubgroup n la
  iseqv := {
    refl := fun σ => by
      show σ * σ⁻¹ ∈ RowSubgroup n la
      rw [mul_inv_cancel]
      exact (RowSubgroup n la).one_mem
    symm := fun {σ₁ σ₂} h => by
      show σ₂ * σ₁⁻¹ ∈ RowSubgroup n la
      have : σ₂ * σ₁⁻¹ = (σ₁ * σ₂⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
      rw [this]
      exact (RowSubgroup n la).inv_mem h
    trans := fun {σ₁ σ₂ σ₃} h₁₂ h₂₃ => by
      show σ₁ * σ₃⁻¹ ∈ RowSubgroup n la
      have key : σ₁ * σ₃⁻¹ = (σ₁ * σ₂⁻¹) * (σ₂ * σ₃⁻¹) := by
        group
      rw [key]
      exact (RowSubgroup n la).mul_mem h₁₂ h₂₃
  }

/-- A tabloid of shape λ is a left P_λ-coset of S_n: an equivalence class of
permutations under the relation σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ. -/
def Tabloid (n : ℕ) (la : Nat.Partition n) :=
  Quotient (TabloidSetoid n la)

noncomputable instance : Fintype (Tabloid n la) := by
  haveI : DecidableRel (TabloidSetoid n la).r := Classical.decRel _
  unfold Tabloid
  exact Quotient.fintype (TabloidSetoid n la)

/-- The tabloid of a permutation σ: its left P_λ-coset. -/
def toTabloid (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    Tabloid n la :=
  Quotient.mk (TabloidSetoid n la) σ

/-- Two permutations give the same tabloid iff they differ by a row permutation. -/
theorem toTabloid_eq_iff (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    toTabloid n la σ₁ = toTabloid n la σ₂ ↔ σ₁ * σ₂⁻¹ ∈ RowSubgroup n la :=
  Quotient.eq (r := TabloidSetoid n la)

/-- Two permutations give the same tabloid iff they have the same row assignment:
for all entries k, the row of k is the same. -/
theorem toTabloid_eq_iff_rowAssign (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    toTabloid n la σ₁ = toTabloid n la σ₂ ↔
      ∀ k : Fin n, rowOfPos la.sortedParts (σ₁ k).val =
                    rowOfPos la.sortedParts (σ₂ k).val := by
  rw [toTabloid_eq_iff]
  constructor
  · intro h k
    have hmem := h (σ₂ k)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply,
               Equiv.Perm.inv_apply_self] at hmem
    exact hmem
  · intro h k
    show rowOfPos la.sortedParts ((σ₁ * σ₂⁻¹) k).val = rowOfPos la.sortedParts k.val
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h (σ₂⁻¹ k)]
    congr 1
    exact congrArg Fin.val (Equiv.apply_symm_apply σ₂ k)

/-! ### SYT to tabloid map -/

/-- The row of entry k in SYT T (via the canonical filling). -/
def sytRowOfEntry (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la)
    (k : Fin n) : ℕ :=
  rowOfPos la.sortedParts (sytPerm n la T k).val

/-- The tabloid associated to a standard Young tableau T: the left P_λ-coset of σ_T. -/
def sytToTabloid (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    Tabloid n la :=
  toTabloid n la (sytPerm n la T)

/-- In a standard tableau, entries in the same row are ordered by their column positions:
if entries k₁ and k₂ are in the same row and k₁ has a strictly smaller column index
(both measured via sytPerm and canonical row/col functions), then k₁ < k₂. -/
private theorem syt_entry_lt_of_col_lt (T : StandardYoungTableau n la) (k₁ k₂ : Fin n)
    (hrow : rowOfPos la.sortedParts (sytPerm n la T k₁).val =
            rowOfPos la.sortedParts (sytPerm n la T k₂).val)
    (hcol : colOfPos la.sortedParts (sytPerm n la T k₁).val <
            colOfPos la.sortedParts (sytPerm n la T k₂).val) :
    k₁ < k₂ := by
  set e := Equiv.ofBijective T.val T.prop.1
  -- Key identity: e.symm k = (canonicalFilling n la) (sytPerm n la T k)
  have hcell : ∀ k : Fin n, e.symm k = (canonicalFilling n la) (sytPerm n la T k) := by
    intro k
    simp only [e, sytPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  -- Same row for the cells
  have hrow' : (e.symm k₁).val.1 = (e.symm k₂).val.1 := by
    rw [hcell k₁, hcell k₂]; exact hrow
  -- k₁'s column < k₂'s column for the cells
  have hcol' : (e.symm k₁).val.2 < (e.symm k₂).val.2 := by
    rw [hcell k₁, hcell k₂]; exact hcol
  -- Apply standard row-increasing property
  have h := T.prop.2.1 (e.symm k₁) (e.symm k₂) hrow' hcol'
  -- T.val (e.symm kᵢ) = kᵢ by definition of e
  rwa [show T.val (e.symm k₁) = k₁ from e.apply_symm_apply k₁,
       show T.val (e.symm k₂) = k₂ from e.apply_symm_apply k₂] at h

/-- Different standard Young tableaux give different tabloids.

Proof: if T₁ and T₂ have the same row assignment for all entries, then within each
row the entries are sorted in the same increasing order (by standardness of both T₁
and T₂), so the fillings are identical. The proof proceeds by strong induction on
entry values: for the smallest entry where the tableaux disagree, one can find a
strictly smaller entry at the same position in the other tableau, contradicting
minimality. -/
theorem sytToTabloid_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (sytToTabloid n la) := by
  intro T₁ T₂ h
  rw [sytToTabloid, sytToTabloid, toTabloid_eq_iff_rowAssign] at h
  apply sytPerm_injective n la
  -- Prove ∀ k, sytPerm T₁ k = sytPerm T₂ k by strong induction on k.val
  suffices ∀ (m : ℕ) (k : Fin n), k.val = m → sytPerm n la T₁ k = sytPerm n la T₂ k by
    exact Equiv.ext (fun k => this k.val k rfl)
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hkm
    have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
    -- Suffices: colOfPos agrees (rowOfPos already agrees by h)
    suffices hcol : colOfPos la.sortedParts (sytPerm n la T₁ k).val =
                    colOfPos la.sortedParts (sytPerm n la T₂ k).val by
      exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts
        (sytPerm n la T₁ k).val (sytPerm n la T₂ k).val
        (by omega) (by omega) (h k) hcol)
    -- Prove colOfPos equal by contradiction
    by_contra hcol_ne
    rcases lt_or_gt_of_ne hcol_ne with hlt | hlt
    · -- Case: col(sytPerm T₁ k) < col(sytPerm T₂ k)
      -- k' := (sytPerm T₂)⁻¹(sytPerm T₁ k) is in same row with smaller column in T₂
      set k' := (sytPerm n la T₂).symm (sytPerm n la T₁ k)
      have hk'_eq : sytPerm n la T₂ k' = sytPerm n la T₁ k :=
        (sytPerm n la T₂).apply_symm_apply (sytPerm n la T₁ k)
      -- k' < k by standard property of T₂
      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₂ k' k
          (by simp only [hk'_eq]; exact h k)
          (by simp only [hk'_eq]; exact hlt)
      -- By IH: sytPerm T₁ k' = sytPerm T₂ k'
      have hih := ih k'.val (by omega) k' rfl
      -- So sytPerm T₁ k' = sytPerm T₂ k' = sytPerm T₁ k, contradicting injectivity
      exact absurd ((sytPerm n la T₁).injective (by rw [hih, hk'_eq])) (ne_of_lt hk'_lt)
    · -- Case: col(sytPerm T₁ k) > col(sytPerm T₂ k) — symmetric with T₁
      set k' := (sytPerm n la T₁).symm (sytPerm n la T₂ k)
      have hk'_eq : sytPerm n la T₁ k' = sytPerm n la T₂ k :=
        (sytPerm n la T₁).apply_symm_apply (sytPerm n la T₂ k)
      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₁ k' k
          (by simp only [hk'_eq]; exact (h k).symm)
          (by simp only [hk'_eq]; exact hlt)
      have hih := ih k'.val (by omega) k' rfl
      exact absurd ((sytPerm n la T₂).injective (by rw [← hih, hk'_eq])) (ne_of_lt hk'_lt)

/-! ### Row-column subgroup intersection -/

/-- In a Young diagram, each cell is uniquely determined by its (row, column) pair.
Therefore, a permutation that preserves both rows and columns must be the identity:
P_λ ∩ Q_λ = {1}. -/
theorem RowSubgroup_inter_ColumnSubgroup (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hrow : σ ∈ RowSubgroup n la)
    (hcol : σ ∈ ColumnSubgroup n la) : σ = 1 := by
  ext k
  simp only [Equiv.Perm.one_apply]
  have hr : rowOfPos la.sortedParts (σ k).val = rowOfPos la.sortedParts k.val := hrow k
  have hc : colOfPos la.sortedParts (σ k).val = colOfPos la.sortedParts k.val := hcol k
  have hsum : la.sortedParts.sum = n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
    rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]
  have hk : k.val < la.sortedParts.sum := by omega
  have hsk : (σ k).val < la.sortedParts.sum := by omega
  exact rowOfPos_colOfPos_injective la.sortedParts (σ k).val k.val hsk hk hr hc

/-! ### T-relative column subgroup -/

/-- The column stabilizer of T: C_T = σ_T⁻¹ Q_λ σ_T.

An element π ∈ C_T preserves T's column structure at the entry level: for every
entry e, the column of π(e) in T equals the column of e in T.

Concretely, π ∈ C_T iff π = σ_T⁻¹ q σ_T for some q ∈ Q_λ, where σ_T = sytPerm T.

Note: this uses conjugation by σ_T⁻¹ (not σ_T). The key identity is:
  col_T(π(e)) = colOfPos(σ_T(π(e)))
and π = σ_T⁻¹ q σ_T gives σ_T π σ_T⁻¹ = q ∈ Q_λ (column-preserving on positions). -/
def RelColumnSubgroup (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) : Subgroup (Equiv.Perm (Fin n)) :=
  (ColumnSubgroup n la).map (MulAut.conj (sytPerm n la T)⁻¹).toMonoidHom

theorem mem_RelColumnSubgroup_iff (T : StandardYoungTableau n la)
    (π : Equiv.Perm (Fin n)) :
    π ∈ RelColumnSubgroup n la T ↔
      ∃ q ∈ ColumnSubgroup n la,
        π = (sytPerm n la T)⁻¹ * q * sytPerm n la T := by
  simp only [RelColumnSubgroup, Subgroup.mem_map, MulAut.conj_apply,
             MulEquiv.coe_toMonoidHom, inv_inv]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

/-- The position-level column perm corresponding to an entry-level column perm:
if π ∈ C_T then q = σ_T π σ_T⁻¹ ∈ Q_λ. -/
theorem sytPerm_conj_mem_ColumnSubgroup (T : StandardYoungTableau n la)
    (π : Equiv.Perm (Fin n)) (hπ : π ∈ RelColumnSubgroup n la T) :
    sytPerm n la T * π * (sytPerm n la T)⁻¹ ∈ ColumnSubgroup n la := by
  rw [mem_RelColumnSubgroup_iff] at hπ
  obtain ⟨q, hq, rfl⟩ := hπ
  group
  exact hq

/-! ### Polytabloid tabloid expansion -/

/-- The tabloid of q⁻¹ · σ_T represents {π · T} where π = σ_T⁻¹ q σ_T ∈ C_T.
For q = 1 (π = 1), this is the tabloid of T. -/
theorem toTabloid_inv_mul_sytPerm_one (T : StandardYoungTableau n la) :
    toTabloid n la (1⁻¹ * sytPerm n la T) = sytToTabloid n la T := by
  simp [sytToTabloid]

/-- A non-identity position-level column perm changes the tabloid of σ_T.

If q ∈ Q_λ and q ≠ 1, then toTabloid(q⁻¹ · σ_T) ≠ toTabloid(σ_T).
The proof reduces to q ∉ P_λ, which follows from P_λ ∩ Q_λ = {1}. -/
theorem ColumnSubgroup_ne_tabloid (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) (hne : q ≠ 1) :
    toTabloid n la (q⁻¹ * sytPerm n la T) ≠ sytToTabloid n la T := by
  rw [Ne, sytToTabloid, toTabloid_eq_iff]
  intro hmem
  -- hmem : q⁻¹ * σ_T * σ_T⁻¹ ∈ P_λ, i.e., q⁻¹ ∈ P_λ
  simp only [mul_assoc, mul_inv_cancel, mul_one] at hmem
  have : q⁻¹ = 1 := RowSubgroup_inter_ColumnSubgroup n la q⁻¹ hmem
    ((ColumnSubgroup n la).inv_mem hq)
  exact hne (inv_eq_one.mp this)

/-! ### Dominance order on tabloids -/

/-- The number of entries ≤ k in the first i rows of the tabloid defined by σ.
This is the fundamental quantity for the dominance partial order.

For tabloid σ, this counts |{e ∈ Fin n : e ≤ k ∧ rowOfPos(σ(e)) < i}|. -/
def tabloidCumulCount (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun e : Fin n =>
    e ≤ k ∧ rowOfPos la.sortedParts (σ e).val < i).card

/-- The cumulative count is well-defined on tabloids: if σ₁ and σ₂ define the same
tabloid (same row assignments), they have the same cumulative counts. -/
theorem tabloidCumulCount_eq_of_toTabloid_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : toTabloid n la σ₁ = toTabloid n la σ₂) (k : Fin n) (i : ℕ) :
    tabloidCumulCount la σ₁ k i = tabloidCumulCount la σ₂ k i := by
  rw [toTabloid_eq_iff_rowAssign] at h
  simp only [tabloidCumulCount]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro ⟨hle, hrow⟩
  · exact ⟨hle, (h e) ▸ hrow⟩
  · exact ⟨hle, (h e) ▸ hrow⟩

/-- Tabloid t₁ dominates tabloid t₂ if for all thresholds k and row counts i,
the number of small entries (≤ k) in the first i rows of t₁ is at least
that of t₂. -/
def tabloidDominates (la : Nat.Partition n) (σ₁ σ₂ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k : Fin n, ∀ i : ℕ,
    tabloidCumulCount la σ₂ k i ≤ tabloidCumulCount la σ₁ k i

/-- Strict dominance: t₁ strictly dominates t₂ if t₁ dominates t₂ and they differ. -/
def tabloidStrictDominates (la : Nat.Partition n) (σ₁ σ₂ : Equiv.Perm (Fin n)) : Prop :=
  tabloidDominates la σ₁ σ₂ ∧ toTabloid n la σ₁ ≠ toTabloid n la σ₂

/-- Dominance is reflexive. -/
theorem tabloidDominates_refl (σ : Equiv.Perm (Fin n)) :
    tabloidDominates la σ σ :=
  fun _ _ => le_refl _

/-- Dominance is transitive. -/
theorem tabloidDominates_trans {σ₁ σ₂ σ₃ : Equiv.Perm (Fin n)}
    (h₁₂ : tabloidDominates la σ₁ σ₂) (h₂₃ : tabloidDominates la σ₂ σ₃) :
    tabloidDominates la σ₁ σ₃ :=
  fun k i => le_trans (h₂₃ k i) (h₁₂ k i)

/-- Dominance is well-defined on tabloids: if σ₁ ~ σ₁' and σ₂ ~ σ₂', then
dominance is preserved. -/
theorem tabloidDominates_congr {σ₁ σ₁' σ₂ σ₂' : Equiv.Perm (Fin n)}
    (h₁ : toTabloid n la σ₁ = toTabloid n la σ₁')
    (h₂ : toTabloid n la σ₂ = toTabloid n la σ₂')
    (hdom : tabloidDominates la σ₁ σ₂) :
    tabloidDominates la σ₁' σ₂' := by
  intro k i
  rw [← tabloidCumulCount_eq_of_toTabloid_eq σ₂ σ₂' h₂,
      ← tabloidCumulCount_eq_of_toTabloid_eq σ₁ σ₁' h₁]
  exact hdom k i

/-! ### Last-letter total order -/

/-- The row assignment vector of a tabloid, as a function Fin n → ℕ.
This is the key comparison function: the last-letter order compares these
vectors lexicographically from the largest entry down. -/
def tabloidRowVec (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℕ :=
  fun k => rowOfPos la.sortedParts (σ k).val

/-- The row vector is well-defined on tabloids. -/
theorem tabloidRowVec_eq_of_toTabloid_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : toTabloid n la σ₁ = toTabloid n la σ₂) :
    tabloidRowVec la σ₁ = tabloidRowVec la σ₂ := by
  rw [toTabloid_eq_iff_rowAssign] at h
  ext k; exact h k

/-- Two permutations with the same row vector give the same tabloid. -/
theorem toTabloid_eq_of_tabloidRowVec_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : tabloidRowVec la σ₁ = tabloidRowVec la σ₂) :
    toTabloid n la σ₁ = toTabloid n la σ₂ := by
  rw [toTabloid_eq_iff_rowAssign]
  intro k; exact congr_fun h k

/-! ### Column-increasing property of standard tableaux -/

/-- In a standard tableau, entries in the same column are ordered by their row positions:
if entries k₁ and k₂ are in the same column and k₁ has a strictly smaller row index,
then k₁ < k₂. This is the column-increasing property. -/
private theorem syt_entry_lt_of_row_lt (T : StandardYoungTableau n la) (k₁ k₂ : Fin n)
    (hcol : colOfPos la.sortedParts (sytPerm n la T k₁).val =
            colOfPos la.sortedParts (sytPerm n la T k₂).val)
    (hrow : rowOfPos la.sortedParts (sytPerm n la T k₁).val <
            rowOfPos la.sortedParts (sytPerm n la T k₂).val) :
    k₁ < k₂ := by
  set e := Equiv.ofBijective T.val T.prop.1
  have hcell : ∀ k : Fin n, e.symm k = (canonicalFilling n la) (sytPerm n la T k) := by
    intro k
    simp only [e, sytPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  -- Same column for the cells
  have hcol' : (e.symm k₁).val.2 = (e.symm k₂).val.2 := by
    rw [hcell k₁, hcell k₂]; exact hcol
  -- k₁'s row < k₂'s row for the cells
  have hrow' : (e.symm k₁).val.1 < (e.symm k₂).val.1 := by
    rw [hcell k₁, hcell k₂]; exact hrow
  -- Apply standard column-increasing property
  have h := T.prop.2.2 (e.symm k₁) (e.symm k₂) hcol' hrow'
  rwa [show T.val (e.symm k₁) = k₁ from e.apply_symm_apply k₁,
       show T.val (e.symm k₂) = k₂ from e.apply_symm_apply k₂] at h

/-! ### Column permutations decrease dominance -/

/-- Within a column of a standard tableau, entries in earlier rows (smaller row index)
have smaller values. Consequence: the entries in the first i rows of a column are
exactly the smallest entries of that column. -/
private theorem syt_col_entry_le_of_row_le (T : StandardYoungTableau n la)
    (e₁ e₂ : Fin n)
    (hcol : colOfPos la.sortedParts (sytPerm n la T e₁).val =
            colOfPos la.sortedParts (sytPerm n la T e₂).val)
    (hrow : rowOfPos la.sortedParts (sytPerm n la T e₁).val ≤
            rowOfPos la.sortedParts (sytPerm n la T e₂).val) :
    e₁ ≤ e₂ := by
  rcases eq_or_lt_of_le hrow with hr | hr
  · -- Same row and same column in T implies same position, hence same entry
    have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
    have h₁ : (sytPerm n la T e₁).val < la.sortedParts.sum := by omega
    have h₂ : (sytPerm n la T e₂).val < la.sortedParts.sum := by omega
    have := rowOfPos_colOfPos_injective la.sortedParts
      (sytPerm n la T e₁).val (sytPerm n la T e₂).val h₁ h₂ hr hcol
    have := (sytPerm n la T).injective (Fin.ext this)
    omega
  · exact le_of_lt (syt_entry_lt_of_row_lt T e₁ e₂ hcol hr)

/-- Abstract counting lemma: for a finset B ⊆ A, filtering B by P gives at most
min(|B|, |filter P A|) elements. -/
private theorem card_filter_le_min {α : Type*}
    (A B : Finset α) (hB : B ⊆ A) (P : α → Prop) [DecidablePred P] :
    (B.filter P).card ≤ min B.card (A.filter P).card :=
  le_min (Finset.card_filter_le B P)
    (Finset.card_le_card (Finset.filter_subset_filter P hB))

/-- Within a column of a standard tableau, entry order implies row order.
This is the converse of `syt_col_entry_le_of_row_le`: if e₁ ≤ e₂ and they
are in the same column, then row(σ e₁) ≤ row(σ e₂). -/
private theorem syt_row_le_of_entry_le (T : StandardYoungTableau n la)
    (e₁ e₂ : Fin n)
    (hcol : colOfPos la.sortedParts (sytPerm n la T e₁).val =
            colOfPos la.sortedParts (sytPerm n la T e₂).val)
    (hle : e₁ ≤ e₂) :
    rowOfPos la.sortedParts (sytPerm n la T e₁).val ≤
    rowOfPos la.sortedParts (sytPerm n la T e₂).val := by
  by_contra h
  push_neg at h
  have := syt_entry_lt_of_row_lt T e₂ e₁ hcol.symm h
  omega

/-- A single column transposition preserves dominance: if positions p₁ and p₂ are in the
same column with row(p₁) < row(p₂), and σ assigns a smaller entry to p₁ than p₂
(column-increasing property), then σ dominates (swap p₁ p₂) * σ. -/
private theorem swap_column_dominance (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n) (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow_lt : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hentry : σ.symm p₁ < σ.symm p₂) :
    tabloidDominates la σ (Equiv.swap p₁ p₂ * σ) := by
  intro k i
  simp only [tabloidCumulCount, Equiv.Perm.coe_mul, Function.comp_apply]
  -- The swap changes σ(e) to swap(p₁,p₂)(σ(e)):
  --   If σ(e) = p₁: goes to p₂ (row increases)
  --   If σ(e) = p₂: goes to p₁ (row decreases)
  --   Otherwise: unchanged
  -- Let e₁ = σ⁻¹(p₁), e₂ = σ⁻¹(p₂). Then e₁ < e₂ by hentry.
  -- After swap: e₁ is at row(p₂), e₂ is at row(p₁)
  set e₁ := σ.symm p₁
  set e₂ := σ.symm p₂
  -- The only entries affected are e₁ and e₂
  -- For threshold k and row bound i, analyze cases:
  -- If row(p₁) ≥ i: no entry was in early rows at either p₁ or p₂, so no change.
  --   (Before: e₁ at row(p₁) ≥ i, e₂ at row(p₂) > row(p₁) ≥ i. After: swapped but both ≥ i.)
  -- If row(p₂) < i: both were in early rows, both still in early rows. No change.
  -- If row(p₁) < i ≤ row(p₂): e₁ was in early rows (row p₁ < i), now at row p₂ ≥ i (leaves).
  --   e₂ was not in early rows (row p₂ ≥ i), now at row p₁ < i (enters).
  --   Net: lose 1 from e₁ ≤ k, gain 1 from e₂ ≤ k.
  --   Since e₁ < e₂: if e₂ ≤ k then e₁ ≤ k, so net ≤ 0. If e₂ > k: lose ≤ 1 if e₁ ≤ k, gain 0.
  --   Either way: new count ≤ old count.
  -- All other entries: unchanged.
  by_cases hi₁ : rowOfPos la.sortedParts p₁.val < i
  · by_cases hi₂ : rowOfPos la.sortedParts p₂.val < i
    · -- Both in early rows: swap doesn't change which entries are in rows < i
      apply Finset.card_le_card
      intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨hle, hrow⟩
      refine ⟨hle, ?_⟩
      by_cases he₁ : σ e = p₁
      · rw [he₁]; exact hi₁
      · by_cases he₂ : σ e = p₂
        · rw [he₂]; exact hi₂
        · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at hrow; exact hrow
    · -- row(p₁) < i ≤ row(p₂): the interesting case
      push_neg at hi₂
      -- Count the difference: at most -1 for e₁ leaving, +1 for e₂ entering
      -- If e₁ > k: both e₁, e₂ > k, no change for threshold k
      -- If e₁ ≤ k and e₂ > k: lose 1 (net -1), new ≤ old ✓
      -- If e₁ ≤ k and e₂ ≤ k: lose 1 gain 1 (net 0) ✓
      -- For entries other than e₁, e₂: swap doesn't change their position
      -- Formalize: show the new filter is contained in old filter + possibly {e₂}
      -- and old filter ⊇ new filter ∖ {e₂} ∪ {e₁}
      -- Simplify: directly compare cardinalities
      -- The filters differ only on e₁ and e₂:
      --   e₁: old row = p₁ (< i) ✓, new row = p₂ (≥ i) ✗
      --   e₂: old row = p₂ (≥ i) ✗, new row = p₁ (< i) ✓
      --   others: same
      -- So |new| = |old| - (1 if e₁ ≤ k else 0) + (1 if e₂ ≤ k else 0)
      -- Since e₁ < e₂: if e₂ ≤ k then e₁ ≤ k, so net = 0.
      -- If e₂ > k and e₁ ≤ k: net = -1. If e₂ > k and e₁ > k: net = 0.
      -- In all cases net ≤ 0.
      suffices h : ∀ e : Fin n, e ≠ e₁ → e ≠ e₂ →
          (rowOfPos la.sortedParts (Equiv.swap p₁ p₂ (σ e)).val < i ↔
           rowOfPos la.sortedParts (σ e).val < i) by
        -- Use injection via Equiv.swap e₁ e₂ to map new_filter into old_filter
        rw [← Finset.card_image_of_injective _ (Equiv.swap e₁ e₂).injective]
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        obtain ⟨e', ⟨hle', hrow'⟩, rfl⟩ := he
        -- e' is in new_filter, need swap(e₁,e₂)(e') in old_filter
        by_cases hee₁ : e' = e₁
        · -- e' = e₁: new row = swap(p₁,p₂)(σ e₁) = swap(p₁,p₂)(p₁) = p₂, row(p₂) ≥ i
          exfalso; subst hee₁
          have : σ e₁ = p₁ := σ.apply_symm_apply p₁
          rw [this, Equiv.swap_apply_left] at hrow'; omega
        · by_cases hee₂ : e' = e₂
          · -- e' = e₂: swap e₁ e₂ maps e₂ to e₁
            subst hee₂
            rw [Equiv.swap_apply_right]
            have hσe₁ : σ e₁ = p₁ := σ.apply_symm_apply p₁
            rw [hσe₁]
            exact ⟨le_of_lt (lt_of_lt_of_le hentry hle'), hi₁⟩
          · -- e' ≠ e₁, e₂: swap is identity, use h to transfer row condition
            rw [Equiv.swap_apply_of_ne_of_ne hee₁ hee₂]
            exact ⟨hle', (h e' hee₁ hee₂).mp hrow'⟩
      -- Prove the "rest unchanged" fact
      intro e hne₁ hne₂
      have : σ e ≠ p₁ := fun h => hne₁ (σ.injective (h ▸ (σ.apply_symm_apply p₁).symm))
      have : σ e ≠ p₂ := fun h => hne₂ (σ.injective (h ▸ (σ.apply_symm_apply p₂).symm))
      rw [Equiv.swap_apply_of_ne_of_ne ‹σ e ≠ p₁› ‹σ e ≠ p₂›]
  · -- row(p₁) ≥ i: both positions have row ≥ i, swap irrelevant for rows < i
    push_neg at hi₁
    apply Finset.card_le_card
    intro e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨hle, hrow⟩
    refine ⟨hle, ?_⟩
    by_cases he₁ : σ e = p₁
    · exfalso; rw [he₁, Equiv.swap_apply_left] at hrow; omega
    · by_cases he₂ : σ e = p₂
      · exfalso; rw [he₂, Equiv.swap_apply_right] at hrow; omega
      · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at hrow; exact hrow

theorem column_perm_dominance (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) :
    tabloidDominates la (sytPerm n la T) (q⁻¹ * sytPerm n la T) := by
  set σ := sytPerm n la T with hσ_def
  have hq_inv : ∀ p : Fin n, colOfPos la.sortedParts (q⁻¹ p).val =
      colOfPos la.sortedParts p.val := (ColumnSubgroup n la).inv_mem hq
  have hq_fwd : ∀ p : Fin n, colOfPos la.sortedParts (q p).val =
      colOfPos la.sortedParts p.val := hq
  intro k i
  simp only [tabloidCumulCount, Equiv.Perm.coe_mul, Function.comp_apply]
  set A := Finset.univ.filter (fun e : Fin n =>
    e ≤ k ∧ rowOfPos la.sortedParts (σ e).val < i)
  set B := Finset.univ.filter (fun e : Fin n =>
    e ≤ k ∧ rowOfPos la.sortedParts (q⁻¹ (σ e)).val < i)
  set ecol : Fin n → ℕ := fun e => colOfPos la.sortedParts (σ e).val
  -- Reduce to per-column inequality via sum decomposition
  suffices hcol : ∀ c, (B.filter (fun e => ecol e = c)).card ≤
      (A.filter (fun e => ecol e = c)).card by
    have hmaps : ∀ (S : Finset (Fin n)), (S : Set (Fin n)).MapsTo ecol
        (↑(Finset.univ.image ecol)) :=
      fun _ e _ => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
    rw [Finset.card_eq_sum_card_fiberwise (hmaps B),
        Finset.card_eq_sum_card_fiberwise (hmaps A)]
    exact Finset.sum_le_sum (fun c _ => hcol c)
  intro c
  -- Per column c: case split on whether all entries ≤ k in col c have row < i
  by_cases hall : ∀ e : Fin n, ecol e = c → e ≤ k →
      rowOfPos la.sortedParts (σ e).val < i
  · -- Case 1: all entries ≤ k in col c have row < i.
    -- A_c = {ecol=c ∧ e≤k}, and B_c ⊆ A_c.
    have hAeq : A.filter (fun e => ecol e = c) =
        Finset.univ.filter (fun e : Fin n => e ≤ k ∧ ecol e = c) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
      exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩,
             fun ⟨h1, h2⟩ => ⟨⟨h1, hall e h2 h1⟩, h2⟩⟩
    rw [hAeq]
    apply Finset.card_le_card
    intro e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
    exact fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩
  · -- Case 2: some entry e₀ ≤ k in col c has row ≥ i.
    -- By SYT monotonicity, row < i in col c implies ≤ k.
    push_neg at hall
    obtain ⟨e₀, hecol₀, hle₀, hrow₀⟩ := hall
    have hrow_imp : ∀ e : Fin n, ecol e = c →
        rowOfPos la.sortedParts (σ e).val < i → e ≤ k := by
      intro e hec hri
      by_contra hgt; push_neg at hgt
      have he₀_le : e₀ ≤ e := by omega
      have hcol_eq : colOfPos la.sortedParts (sytPerm n la T e₀).val =
          colOfPos la.sortedParts (sytPerm n la T e).val := by
        change ecol e₀ = ecol e; rw [hecol₀, hec]
      have hrow_le := syt_row_le_of_entry_le T e₀ e hcol_eq he₀_le
      simp only [← hσ_def] at hrow_le; omega
    -- A_c = {ecol=c ∧ row(σ·)<i} since ≤k is automatic
    have hAeq : A.filter (fun e => ecol e = c) =
        Finset.univ.filter (fun e : Fin n =>
          rowOfPos la.sortedParts (σ e).val < i ∧ ecol e = c) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h2, h3⟩,
             fun ⟨h1, h2⟩ => ⟨⟨hrow_imp e h2 h1, h1⟩, h2⟩⟩
    rw [hAeq]
    -- |B_c| ≤ |{ecol=c, row(q⁻¹(σ·))<i}| = |{ecol=c, row(σ·)<i}| = |A_c|
    calc (B.filter (fun e => ecol e = c)).card
        ≤ (Finset.univ.filter (fun e : Fin n =>
            rowOfPos la.sortedParts (q⁻¹ (σ e)).val < i ∧ ecol e = c)).card := by
          apply Finset.card_le_card
          intro e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
          exact fun ⟨⟨_, h2⟩, h3⟩ => ⟨h2, h3⟩
      _ = (Finset.univ.filter (fun e : Fin n =>
            rowOfPos la.sortedParts (σ e).val < i ∧ ecol e = c)).card := by
          -- Bijection: ψ(e) = σ⁻¹(q⁻¹(σ e)) maps LHS→RHS,
          --            ψ⁻¹(e) = σ⁻¹(q(σ e)) maps RHS→LHS
          apply Finset.card_nbij'
            (fun e => σ.symm ((q : Equiv.Perm (Fin n))⁻¹ (σ e)))
            (fun e => σ.symm (q (σ e)))
          · -- ψ maps {row(q⁻¹(σ·))<i, ecol=c} into {row(σ·)<i, ecol=c}
            intro e he
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at he ⊢
            refine ⟨?_, ?_⟩
            · -- row(σ(σ⁻¹(q⁻¹(σ e)))) = row(q⁻¹(σ e)) < i
              simp only [Equiv.apply_symm_apply]; exact he.1
            · -- ecol(σ⁻¹(q⁻¹(σ e))) = col(q⁻¹(σ e)) = col(σ e) = c
              show ecol (σ.symm ((q : Equiv.Perm (Fin n))⁻¹ (σ e))) = c
              simp only [ecol, Equiv.apply_symm_apply, hq_inv]; exact he.2
          · -- ψ⁻¹ maps {row(σ·)<i, ecol=c} into {row(q⁻¹(σ·))<i, ecol=c}
            intro e he
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at he ⊢
            refine ⟨?_, ?_⟩
            · -- row(q⁻¹(σ(σ⁻¹(q(σ e))))) = row(q⁻¹(q(σ e))) = row(σ e) < i
              rw [Equiv.apply_symm_apply]
              change rowOfPos la.sortedParts (q.symm (q (σ e))).val < i
              rw [Equiv.symm_apply_apply]; exact he.1
            · -- ecol(σ⁻¹(q(σ e))) = col(q(σ e)) = col(σ e) = c
              show ecol (σ.symm (q (σ e))) = c
              simp only [ecol, Equiv.apply_symm_apply, hq_fwd]; exact he.2
          · -- Left inverse: ψ⁻¹(ψ(e)) = e
            intro e _
            dsimp only
            rw [Equiv.apply_symm_apply, Equiv.Perm.apply_inv_self,
                Equiv.symm_apply_apply]
          · -- Right inverse: ψ(ψ⁻¹(e)) = e
            intro e _
            dsimp only
            rw [Equiv.apply_symm_apply, Equiv.Perm.inv_apply_self,
                Equiv.symm_apply_apply]

/-- A non-identity column permutation strictly decreases dominance: for q ∈ Q_λ
with q ≠ 1, the tabloid of σ_T strictly dominates the tabloid of q⁻¹ · σ_T.
This is the key lemma for polytabloid linear independence. -/
theorem column_perm_strict_dominance (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) (hne : q ≠ 1) :
    tabloidStrictDominates la (sytPerm n la T) (q⁻¹ * sytPerm n la T) :=
  ⟨column_perm_dominance T q hq,
   (ColumnSubgroup_ne_tabloid T q hq hne).symm⟩

/-! ### Tabloid projection linear map -/

/-- The tabloid projection linear map: sends an element of the group algebra to the
formal sum of its tabloid indicators. Concretely, sends `single σ 1` to
`single (toTabloid σ) 1`, extended by linearity.

This is the quotient map π : ℂ[S_n] → ℂ[S_n/P_λ] = M^λ (tabloid module). -/
def tabloidProjection (n : ℕ) (la : Nat.Partition n) :
    SymGroupAlgebra n →ₗ[ℂ] (Tabloid n la →₀ ℂ) where
  toFun a := a.sum (fun σ c => c • Finsupp.single (toTabloid n la σ) 1)
  map_add' a b := by
    apply Finsupp.sum_add_index
    · intro σ; simp
    · intro σ c₁ c₂; simp [add_smul]
  map_smul' r a := by
    simp only [RingHom.id_apply]
    rw [Finsupp.sum_smul_index (fun σ => by simp)]
    simp only [Finsupp.sum, Finset.smul_sum, smul_smul]

/-- The tabloid projection of a basis element `single σ 1` is `single (toTabloid σ) 1`. -/
theorem tabloidProjection_single (σ : Equiv.Perm (Fin n)) :
    tabloidProjection n la (Finsupp.single σ 1) = Finsupp.single (toTabloid n la σ) 1 := by
  simp [tabloidProjection, Finsupp.sum_single_index]

/-- Evaluate tabloidProjection at a specific tabloid: it sums the coefficients of all
permutations in that tabloid's P_λ-coset. -/
theorem tabloidProjection_apply [DecidableEq (Tabloid n la)]
    (a : SymGroupAlgebra n) (t : Tabloid n la) :
    (tabloidProjection n la a) t =
      a.sum (fun σ c => if toTabloid n la σ = t then c else 0) := by
  simp only [tabloidProjection, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro σ _
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs with h
  · simp [h]
  · simp [h]

/-! ### Left P_λ-coset preservation -/

/-- For p ∈ P_λ, left-multiplying by p preserves tabloids: toTabloid(p * σ) = toTabloid(σ).
This is because the tabloid equivalence uses LEFT P_λ-cosets: σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ. -/
theorem toTabloid_rowPerm_mul (p σ : Equiv.Perm (Fin n))
    (hp : p ∈ RowSubgroup n la) :
    toTabloid n la (p * σ) = toTabloid n la σ := by
  rw [toTabloid_eq_iff]
  show p * σ * σ⁻¹ ∈ RowSubgroup n la
  rw [mul_assoc, mul_inv_cancel]
  exact hp

/-! ### Dominance well-definedness on tabloids -/

/-- Dominance is well-defined with respect to tabloid equivalence on the right. -/
theorem tabloidDominates_of_toTabloid_eq_right {σ₁ σ₂ σ₂' : Equiv.Perm (Fin n)}
    (hdom : tabloidDominates la σ₁ σ₂)
    (h : toTabloid n la σ₂ = toTabloid n la σ₂') :
    tabloidDominates la σ₁ σ₂' :=
  tabloidDominates_congr rfl h hdom

/-- Dominance is well-defined with respect to tabloid equivalence on the left. -/
theorem tabloidDominates_of_toTabloid_eq_left {σ₁ σ₁' σ₂ : Equiv.Perm (Fin n)}
    (hdom : tabloidDominates la σ₁ σ₂)
    (h : toTabloid n la σ₁ = toTabloid n la σ₁') :
    tabloidDominates la σ₁' σ₂ :=
  tabloidDominates_congr h rfl hdom

end

end Etingof
