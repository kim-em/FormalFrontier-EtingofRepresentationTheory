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

/-- If σ₁ dominates σ₂ dominates σ₃ and toTabloid(σ₁) = toTabloid(σ₃),
then toTabloid(σ₂) = toTabloid(σ₃). This is a "squeeze" lemma:
equal cumulative counts at the endpoints force equal counts in the middle. -/
theorem tabloidDominates_antisymm_toTabloid {σ₁ σ₂ σ₃ : Equiv.Perm (Fin n)}
    (h₁₂ : tabloidDominates la σ₁ σ₂) (h₂₃ : tabloidDominates la σ₂ σ₃)
    (heq : toTabloid n la σ₁ = toTabloid n la σ₃) :
    toTabloid n la σ₂ = toTabloid n la σ₃ := by
  -- Squeeze: count(σ₃) ≤ count(σ₂) ≤ count(σ₁) = count(σ₃), so count(σ₂) = count(σ₃)
  have hcount : ∀ k : Fin n, ∀ i : ℕ,
      tabloidCumulCount la σ₂ k i = tabloidCumulCount la σ₃ k i := by
    intro k i
    have h1 := h₁₂ k i
    have h2 := h₂₃ k i
    have h3 := tabloidCumulCount_eq_of_toTabloid_eq σ₁ σ₃ heq k i
    omega
  -- Equal cumulative counts imply equal row assignments
  rw [toTabloid_eq_iff_rowAssign]
  intro k
  by_contra hne
  -- Either row(σ₂(k)) < row(σ₃(k)) or row(σ₃(k)) < row(σ₂(k))
  have hlt : rowOfPos la.sortedParts (σ₂ k).val <
      rowOfPos la.sortedParts (σ₃ k).val := by
    rcases Nat.lt_or_ge (rowOfPos la.sortedParts (σ₂ k).val)
        (rowOfPos la.sortedParts (σ₃ k).val) with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with heq' | hlt'
      · exact absurd heq'.symm hne
      · -- row(σ₃(k)) < row(σ₂(k)): derive contradiction using symmetric argument
        -- count(σ₂, k, row(σ₂(k))) should include entry k for σ₃ but not σ₂
        -- This contradicts hcount. We'll prove it below, so for now use the
        -- general argument in the reverse direction.
        exfalso
        -- At i = row(σ₂(k)): σ₃ counts entry k (row(σ₃(k)) < row(σ₂(k)))
        -- but σ₂ does not (row(σ₂(k)) = row(σ₂(k)), not <)
        set r' := rowOfPos la.sortedParts (σ₂ k).val
        rcases k with ⟨_ | m', hk'⟩
        · -- k = 0
          have : tabloidCumulCount la σ₃ ⟨0, hk'⟩ r' = 1 := by
            simp only [tabloidCumulCount]
            rw [show (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨0, hk'⟩ ∧ rowOfPos la.sortedParts (σ₃ e).val < r') =
              {⟨0, hk'⟩} from by
              ext ⟨e, he⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
              constructor
              · intro ⟨hle, _⟩; omega
              · intro heq'; subst heq'; exact ⟨le_refl _, hlt'⟩]
            exact Finset.card_singleton _
          have : tabloidCumulCount la σ₂ ⟨0, hk'⟩ r' = 0 := by
            simp only [tabloidCumulCount]
            apply Finset.card_eq_zero.mpr
            rw [Finset.filter_eq_empty_iff]
            intro ⟨e, he⟩ _
            simp only [not_and, Fin.mk_le_mk]
            intro hle hrow
            have : e = 0 := by omega
            subst this; exact Nat.lt_irrefl _ hrow
          linarith [hcount ⟨0, hk'⟩ r']
        · -- k = m'+1
          have hm' : m' < n := by omega
          have h2d : tabloidCumulCount la σ₃ ⟨m' + 1, hk'⟩ r' =
              tabloidCumulCount la σ₃ ⟨m', hm'⟩ r' + 1 := by
            simp only [tabloidCumulCount]
            rw [show (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨m' + 1, hk'⟩ ∧ rowOfPos la.sortedParts (σ₃ e).val < r') =
              (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨m', hm'⟩ ∧ rowOfPos la.sortedParts (σ₃ e).val < r') ∪
              {⟨m' + 1, hk'⟩} from by
              ext ⟨e, he⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_union, Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
              constructor
              · intro ⟨hle, hrow⟩
                by_cases heq' : e = m' + 1
                · right; exact heq'
                · left; exact ⟨by omega, hrow⟩
              · intro hh
                rcases hh with ⟨hle, hrow⟩ | heq'
                · exact ⟨by omega, hrow⟩
                · subst heq'; exact ⟨le_refl _, hlt'⟩]
            rw [Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]
              intro ⟨e, he⟩ hmem hsing
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Fin.mk_le_mk] at hmem
              simp only [Finset.mem_singleton, Fin.ext_iff] at hsing
              omega)]
            simp
          have h3d : tabloidCumulCount la σ₂ ⟨m' + 1, hk'⟩ r' =
              tabloidCumulCount la σ₂ ⟨m', hm'⟩ r' := by
            simp only [tabloidCumulCount]
            congr 1; ext ⟨e, he⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk]
            constructor
            · intro ⟨hle, hrow⟩
              constructor
              · by_contra hgt; push_neg at hgt
                have : e = m' + 1 := by omega
                subst this; exact Nat.lt_irrefl _ hrow
              · exact hrow
            · intro ⟨hle, hrow⟩; exact ⟨by omega, hrow⟩
          linarith [hcount ⟨m' + 1, hk'⟩ r', hcount ⟨m', hm'⟩ r']
  -- row(σ₂(k)) < row(σ₃(k))
  set r := rowOfPos la.sortedParts (σ₃ k).val
  rcases k with ⟨_ | m, hk⟩
  · -- k = 0: count(σ, 0, r) counts only entry 0
    have h2 : tabloidCumulCount la σ₂ ⟨0, hk⟩ r = 1 := by
      simp only [tabloidCumulCount]
      rw [show (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨0, hk⟩ ∧ rowOfPos la.sortedParts (σ₂ e).val < r) =
        {⟨0, hk⟩} from by
        ext ⟨e, he⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.mk_le_mk, Fin.ext_iff]
        constructor
        · intro ⟨hle, _⟩; omega
        · intro heq; subst heq; exact ⟨le_refl _, hlt⟩]
      exact Finset.card_singleton _
    have h3 : tabloidCumulCount la σ₃ ⟨0, hk⟩ r = 0 := by
      simp only [tabloidCumulCount]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro ⟨e, he⟩ _
      simp only [not_and, Fin.mk_le_mk]
      intro hle hrow
      have : e = 0 := by omega
      subst this; exact Nat.lt_irrefl _ hrow
    linarith [hcount ⟨0, hk⟩ r]
  · -- k = m+1: use predecessor count at ⟨m, _⟩
    have hm : m < n := by omega
    -- count(σ₂, m+1, r) = count(σ₂, m, r) + 1 (entry m+1 contributes since row < r)
    have h2_diff : tabloidCumulCount la σ₂ ⟨m + 1, hk⟩ r =
        tabloidCumulCount la σ₂ ⟨m, hm⟩ r + 1 := by
      simp only [tabloidCumulCount]
      rw [show (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨m + 1, hk⟩ ∧ rowOfPos la.sortedParts (σ₂ e).val < r) =
        (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨m, hm⟩ ∧ rowOfPos la.sortedParts (σ₂ e).val < r) ∪ {⟨m + 1, hk⟩} from by
        ext ⟨e, he⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
        constructor
        · intro ⟨hle, hrow⟩
          by_cases heq : e = m + 1
          · right; exact heq
          · left; exact ⟨by omega, hrow⟩
        · intro h
          rcases h with ⟨hle, hrow⟩ | heq
          · exact ⟨by omega, hrow⟩
          · subst heq; exact ⟨le_refl _, hlt⟩]
      rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]
        intro ⟨e, he⟩ hmem hsing
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk] at hmem
        simp only [Finset.mem_singleton, Fin.ext_iff] at hsing
        omega)]
      simp
    -- count(σ₃, m+1, r) = count(σ₃, m, r) (entry m+1 does NOT contribute since row = r)
    have h3_diff : tabloidCumulCount la σ₃ ⟨m + 1, hk⟩ r =
        tabloidCumulCount la σ₃ ⟨m, hm⟩ r := by
      simp only [tabloidCumulCount]
      congr 1; ext ⟨e, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk]
      constructor
      · intro ⟨hle, hrow⟩
        constructor
        · by_contra hgt; push_neg at hgt
          have : e = m + 1 := by omega
          subst this; exact Nat.lt_irrefl _ hrow
        · exact hrow
      · intro ⟨hle, hrow⟩; exact ⟨by omega, hrow⟩
    linarith [hcount ⟨m + 1, hk⟩ r, hcount ⟨m, hm⟩ r]

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

/-! ### Polytabloid dominance for linear independence -/

/-- Helper: the total number of entries in the first i rows is the same for any
permutation of shape λ (it equals Σ_{r<i} λ_r, the number of cells in the first i rows). -/
private theorem tabloidCumulCount_full (σ : Equiv.Perm (Fin n)) (i : ℕ) (hn : 0 < n) :
    tabloidCumulCount la σ ⟨n - 1, by omega⟩ i =
    (Finset.univ.filter fun pos : Fin n =>
      rowOfPos la.sortedParts pos.val < i).card := by
  simp only [tabloidCumulCount]
  apply Finset.card_nbij' (fun e => σ e) (fun p => σ.symm p)
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact he.2
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨?_, by rwa [Equiv.apply_symm_apply]⟩
    change (σ.symm p).val ≤ n - 1
    omega
  · intro e _; exact σ.symm_apply_apply e
  · intro p _; exact σ.apply_symm_apply p

/-! ### Note on the group algebra vs tabloid module approach

The group algebra polytabloid `polytabloid n la T` (in `PolytabloidBasis.lean`)
and the tabloid polytabloid `polytabloidTab T` (below) have different supports:
the group algebra polytabloid sums over P_λ × Q_λ coset representatives,
while the tabloid polytabloid sums over Q_λ alone. The group algebra coefficient
at a permutation σ can be nonzero even when the tabloid coefficient at
`toTabloid σ` is zero (since different P_λ coset representatives can cancel).

A dominance theorem for the group algebra polytabloid (analagous to
`polytabloidTab_coeff_dominance` below) would require a novel combinatorial
argument handling both row and column permutations simultaneously. Per-column
dominance fails for the row-permutation component.

The correct proof of polytabloid linear independence is via the tabloid module:
`polytabloidTab_linearIndependent` below uses `polytabloidTab_coeff_self` (which
IS true at the tabloid level) and `polytabloidTab_coeff_dominance`. The group
algebra version (`polytabloid_linearIndependent` in `PolytabloidBasis.lean`)
requires a transfer argument from the tabloid module.
-/

/-- In any finset with a dominance-like relation, a nonempty subset has a maximal
element. We use a Nat-valued measure and strong induction. -/
private lemma exists_dominance_maximal
    (S : Finset (StandardYoungTableau n la))
    (f : StandardYoungTableau n la → ℂ) (T₀ : StandardYoungTableau n la)
    (hT₀ : T₀ ∈ S) (hfT₀ : f T₀ ≠ 0) :
    ∃ T₁ ∈ S, f T₁ ≠ 0 ∧
      ∀ T' ∈ S, f T' ≠ 0 →
        tabloidDominates la (sytPerm n la T') (sytPerm n la T₁) →
        sytToTabloid n la T' = sytToTabloid n la T₁ := by
  -- Measure: for each T, count how many T' ∈ S with f(T') ≠ 0 that strictly
  -- dominate T. A maximal T has no such T', giving an empty "badSet".
  classical
  -- Define: "badSet T" = {T' ∈ S | f(T') ≠ 0 ∧ T' strictly dominates T}
  -- If badSet T₀ = ∅, T₀ is maximal. Otherwise pick T₁ ∈ badSet T₀ and recurse.
  suffices hmain : ∀ (m : ℕ) (T : StandardYoungTableau n la),
      T ∈ S → f T ≠ 0 →
      (S.filter fun T' => f T' ≠ 0 ∧
        tabloidStrictDominates la (sytPerm n la T') (sytPerm n la T)).card = m →
      ∃ T₁ ∈ S, f T₁ ≠ 0 ∧ ∀ T' ∈ S, f T' ≠ 0 →
        tabloidDominates la (sytPerm n la T') (sytPerm n la T₁) →
        sytToTabloid n la T' = sytToTabloid n la T₁ by
    exact hmain _ T₀ hT₀ hfT₀ rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro T hTS hfT hcard
  -- Check if T is already maximal
  by_cases hmax : ∀ T' ∈ S, f T' ≠ 0 →
      tabloidDominates la (sytPerm n la T') (sytPerm n la T) →
      sytToTabloid n la T' = sytToTabloid n la T
  · exact ⟨T, hTS, hfT, hmax⟩
  · -- T is not maximal: there exists T' with f(T') ≠ 0 that strictly dominates T
    push_neg at hmax
    obtain ⟨T', hT'S, hfT', hdom, hne_tab⟩ := hmax
    -- T' strictly dominates T
    have hstrict : tabloidStrictDominates la (sytPerm n la T') (sytPerm n la T) :=
      ⟨hdom, fun h => hne_tab (toTabloid_eq_of_tabloidRowVec_eq _ _
        (tabloidRowVec_eq_of_toTabloid_eq _ _ h))⟩
    apply ih (S.filter fun T'' => f T'' ≠ 0 ∧
        tabloidStrictDominates la (sytPerm n la T'') (sytPerm n la T')).card
    · -- Strict decrease: badSet(T') ⊊ badSet(T)
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · -- T' is in badSet(T) but not in badSet(T')
        refine ⟨T', ?_, ?_⟩
        · simp only [Finset.mem_filter]
          exact ⟨hT'S, hfT', hstrict⟩
        · simp only [Finset.mem_filter]
          simp only [not_and]
          intro _ _ hsd
          exact hsd.2 rfl
      · -- badSet(T') ⊆ badSet(T)
        intro T'' hT''
        simp only [Finset.mem_filter] at hT'' ⊢
        refine ⟨hT''.1, hT''.2.1, ?_⟩
        exact ⟨tabloidDominates_trans hT''.2.2.1 hstrict.1,
          fun heq =>
            -- If toTabloid(T'') = toTabloid(T), then T'' dom T' dom T and
            -- tabloidCumulCount matches at T'' and T (same tabloid).
            -- So T' is squeezed: all cumulative counts match, giving same tabloid.
            -- tabloidDominates_antisymm_toTabloid gives toTabloid T' = toTabloid T
            hstrict.2 (tabloidDominates_antisymm_toTabloid
              hT''.2.2.1 hstrict.1 heq)⟩
    · exact hT'S
    · exact hfT'
    · rfl

/-! ### Tabloid representation (free ℂ-module on tabloids)

The tabloid representation M^λ is the free ℂ-module with basis indexed by tabloids.
Polytabloids live naturally in M^λ, avoiding the definitional mismatch that occurs
when trying to define them in the group algebra ℂ[S_n]. -/

/-- The tabloid representation M^λ: formal ℂ-linear combinations of tabloids. -/
abbrev TabloidRepresentation (n : ℕ) (la : Nat.Partition n) :=
  Finsupp (Tabloid n la) ℂ

/-- The polytabloid e_T in the tabloid module:
  e_T = Σ_{q ∈ Q_λ} sign(q) · {q⁻¹ · σ_T}
where {·} denotes a basis element (single tabloid) in M^λ.

Different q ∈ Q_λ give different tabloids (since P_λ ∩ Q_λ = {1}),
so the polytabloid has exactly |Q_λ| nonzero coefficients, each ±1. -/
noncomputable def polytabloidTab (T : StandardYoungTableau n la) :
    TabloidRepresentation n la :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ q : ↥(ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      Finsupp.single (toTabloid n la (q.val⁻¹ * sytPerm n la T)) 1

/-- Different column permutations give different tabloids when applied to σ_T.
This is the key injectivity lemma for the polytabloid coefficient computation. -/
private theorem toTabloid_inv_mul_injective (T : StandardYoungTableau n la)
    (q₁ q₂ : ↥(ColumnSubgroup n la))
    (h : toTabloid n la (q₁.val⁻¹ * sytPerm n la T) =
         toTabloid n la (q₂.val⁻¹ * sytPerm n la T)) :
    q₁ = q₂ := by
  rw [toTabloid_eq_iff] at h
  -- h : q₁⁻¹ σ_T * (q₂⁻¹ σ_T)⁻¹ ∈ P_λ, i.e., q₁⁻¹ q₂ ∈ P_λ
  have h' : q₁.val⁻¹ * q₂.val ∈ RowSubgroup n la := by
    convert h using 1; group
  have := RowSubgroup_inter_ColumnSubgroup n la (q₁.val⁻¹ * q₂.val) h'
    ((ColumnSubgroup n la).mul_mem
      ((ColumnSubgroup n la).inv_mem q₁.prop) q₂.prop)
  exact Subtype.ext (eq_of_inv_mul_eq_one this)

/-- The coefficient of tabloid {T} (= toTabloid(σ_T)) in polytabloid e_T is 1.

Only q = 1 contributes to this tabloid: for q ≠ 1, the tabloid
toTabloid(q⁻¹ · σ_T) ≠ toTabloid(σ_T) by ColumnSubgroup_ne_tabloid. -/
theorem polytabloidTab_coeff_self (T : StandardYoungTableau n la) :
    polytabloidTab T (sytToTabloid n la T) = 1 := by
  classical
  simp only [polytabloidTab, sytToTabloid]
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single (⟨1, (ColumnSubgroup n la).one_mem⟩ :
      ↥(ColumnSubgroup n la))]
  · -- q = 1: sign(1) * single(σ_T)(toTabloid(σ_T)) = 1
    simp [Equiv.Perm.sign_one]
  · -- q ≠ 1: toTabloid(q⁻¹ σ_T) ≠ toTabloid(σ_T), so coefficient is 0
    intro q _ hq
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have hne : (q : Equiv.Perm (Fin n)) ≠ 1 := fun h => hq (Subtype.ext h)
    have := ColumnSubgroup_ne_tabloid T q.val q.prop hne
    simp only [sytToTabloid] at this
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- If the coefficient of a tabloid t in e_T is nonzero, then {T} dominates t.

Specifically, if polytabloidTab T evaluates to nonzero at toTabloid(σ), then
σ_T dominates σ in the tabloid dominance order. This follows because the
support of e_T consists of tabloids {q⁻¹ · σ_T} for q ∈ Q_λ, and
column_perm_dominance shows σ_T dominates each q⁻¹ · σ_T. -/
theorem polytabloidTab_coeff_dominance (T : StandardYoungTableau n la)
    (σ : Equiv.Perm (Fin n))
    (hne : polytabloidTab T (toTabloid n la σ) ≠ 0) :
    tabloidDominates la (sytPerm n la T) σ := by
  classical
  simp only [polytabloidTab] at hne
  rw [Finsupp.finset_sum_apply] at hne
  -- Some term in the sum is nonzero
  obtain ⟨q, _, hq_term⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at hq_term
  split_ifs at hq_term with heq
  · -- toTabloid(q⁻¹ σ_T) = toTabloid(σ)
    -- By column_perm_dominance: σ_T dominates q⁻¹ σ_T
    have hdom := column_perm_dominance T q.val q.prop
    -- By tabloidDominates_congr: σ_T dominates σ (same tabloid as q⁻¹ σ_T)
    exact tabloidDominates_congr rfl heq hdom
  · simp at hq_term

/-- Variant: if e_{T₁} has nonzero coefficient at the tabloid of T₂,
then T₁'s tabloid dominates T₂'s tabloid. -/
theorem polytabloidTab_syt_dominance (T₁ T₂ : StandardYoungTableau n la)
    (hne : polytabloidTab T₁ (sytToTabloid n la T₂) ≠ 0) :
    tabloidDominates la (sytPerm n la T₁) (sytPerm n la T₂) :=
  polytabloidTab_coeff_dominance T₁ (sytPerm n la T₂) hne

/-! ### Linear independence of polytabloids in the tabloid module -/

/-- Auxiliary: if Σ f(T) · e_T = 0 in M^λ, then for any dominance-maximal T₀
with f(T₀) ≠ 0, we get a contradiction. -/
private lemma polytabloidTab_coeff_zero_of_maximal
    (S : Finset (StandardYoungTableau n la))
    (f : StandardYoungTableau n la → ℂ)
    (hf : ∑ t ∈ S, f t • polytabloidTab t = 0)
    (T₀ : StandardYoungTableau n la) (hT₀ : T₀ ∈ S)
    (hmax : ∀ T' ∈ S, f T' ≠ 0 →
      tabloidDominates la (sytPerm n la T') (sytPerm n la T₀) →
      sytToTabloid n la T' = sytToTabloid n la T₀) :
    f T₀ = 0 := by
  classical
  -- Evaluate at the tabloid of T₀
  have heval : (∑ t ∈ S, f t • polytabloidTab t) (sytToTabloid n la T₀) = 0 := by
    rw [hf]; rfl
  rw [Finsupp.finset_sum_apply] at heval
  simp only [Finsupp.smul_apply, smul_eq_mul] at heval
  -- Split off the T₀ term
  rw [← Finset.add_sum_erase S _ hT₀] at heval
  -- e_{T₀} at tabloid {T₀} = 1
  rw [polytabloidTab_coeff_self, mul_one] at heval
  -- Show all other terms vanish
  suffices hrest : ∀ T' ∈ S.erase T₀,
      f T' * polytabloidTab T' (sytToTabloid n la T₀) = 0 by
    rw [Finset.sum_eq_zero hrest, add_zero] at heval; exact heval
  intro T' hT'
  have hT'S : T' ∈ S := Finset.mem_of_mem_erase hT'
  have hne_T : T' ≠ T₀ := Finset.ne_of_mem_erase hT'
  by_cases hfT' : f T' = 0
  · rw [hfT', zero_mul]
  by_cases hcoeff : polytabloidTab T' (sytToTabloid n la T₀) = 0
  · rw [hcoeff, mul_zero]
  · -- Nonzero coefficient ⟹ T' dominates T₀
    have hdom := polytabloidTab_syt_dominance T' T₀ hcoeff
    -- By maximality, tabloid(T') = tabloid(T₀)
    have htab_eq := hmax T' hT'S hfT' hdom
    -- But different SYTs have different tabloids
    exact absurd (sytToTabloid_injective n la htab_eq) hne_T

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in M^λ.

This is the correct statement: polytabloids are linearly independent in the
tabloid module, where the definition is sound (unlike in ℂ[S_n] where
polytabloid_mem_spechtModule is false). The proof uses dominance triangularity:
the "tabloid coefficient matrix" is unitriangular with respect to the
dominance order on tabloids. -/
theorem polytabloidTab_linearIndependent :
    LinearIndependent ℂ (fun T : StandardYoungTableau n la => polytabloidTab T) := by
  rw [linearIndependent_iff']
  intro S f hf T hT
  by_contra hfT
  obtain ⟨T₀, hT₀, hfT₀, hmax⟩ := exists_dominance_maximal S f T hT hfT
  exact hfT₀ (polytabloidTab_coeff_zero_of_maximal S f hf T₀ hT₀ hmax)

-- Note: polytabloid_linearIndependent' (group algebra version) was removed because
-- it depended on the false polytabloid_self_coeff. The correct proof is
-- polytabloidTab_linearIndependent above. The group algebra version
-- (polytabloid_linearIndependent in PolytabloidBasis.lean) remains sorry'd pending
-- a transfer argument from the tabloid module.

end

end Etingof
