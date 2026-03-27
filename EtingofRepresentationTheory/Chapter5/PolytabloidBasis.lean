import Mathlib
import EtingofRepresentationTheory.Chapter5.SYTFintype
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2

/-!
# Polytabloid Basis Infrastructure

This file provides the definitions and key lemmas needed for the polytabloid basis
of the Specht module V_λ = ℂ[S_n] · c_λ.

## Main definitions

* `Etingof.Cell` — the cell type of a Young diagram (pairs (i,j) in the diagram)
* `Etingof.canonicalFilling` — the bijection `Fin n ≃ Cell n la` filling left-to-right,
  top-to-bottom
* `Etingof.sytPerm` — the permutation σ_T ∈ S_n associated to a standard Young tableau T
* `Etingof.polytabloid` — the polytabloid e_T = σ_T · c_λ ∈ V_λ

## Main results

* `Etingof.polytabloid_mem_spechtModule` — polytabloids lie in the Specht module
* `Etingof.polytabloid_linearIndependent` — polytabloids are linearly independent (sorry)
* `Etingof.perm_mul_youngSymmetrizer_mem_span_polytabloids` — straightening lemma
  (proved via WF induction on column inversions; depends on two sorry'd helpers)
* `Etingof.polytabloid_span` — polytabloids span the Specht module (proved from straightening)
* `Etingof.finrank_spechtModule_eq_card_syt` — dim V_λ = |SYT(λ)| (proved from independence + span)

## References

* Etingof, Theorem 5.17.1
* James, "The Representation Theory of the Symmetric Groups"
-/

namespace Etingof

noncomputable section

/-! ### Cell type abbreviation -/

/-- The cell type of a Young diagram: pairs (i, j) with i < number of rows and
j < length of row i. -/
abbrev Cell (n : ℕ) (la : Nat.Partition n) :=
  { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 }

/-! ### Helper lemmas for canonical filling -/

/-- The sorted parts of a partition of n sum to n. -/
private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]

/-- rowOfPos returns a value less than the list length for valid positions. -/
theorem rowOfPos_lt_length (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    rowOfPos parts k < parts.length := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [rowOfPos, List.length_cons]
    split_ifs with h
    · omega
    · have : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      have := ih _ this
      omega

/-- The canonical filling maps position k to a valid cell. -/
theorem canonicalFilling_valid (n : ℕ) (la : Nat.Partition n) (k : Fin n) :
    rowOfPos la.sortedParts k.val < la.sortedParts.length ∧
    colOfPos la.sortedParts k.val < la.sortedParts.getD (rowOfPos la.sortedParts k.val) 0 := by
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  have hk : k.val < la.sortedParts.sum := by omega
  exact ⟨rowOfPos_lt_length la.sortedParts k.val hk,
         colOfPos_lt_getD la.sortedParts k.val hk⟩

/-! ### Canonical filling equivalence -/

/-- The canonical filling: position k ↦ cell (rowOfPos parts k, colOfPos parts k).
This fills the Young diagram left-to-right, top-to-bottom. -/
def canonicalFillingFun (n : ℕ) (la : Nat.Partition n) : Fin n → Cell n la :=
  fun k => ⟨(rowOfPos la.sortedParts k.val, colOfPos la.sortedParts k.val),
            canonicalFilling_valid n la k⟩

/-- The canonical filling is injective. -/
theorem canonicalFillingFun_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (canonicalFillingFun n la) := by
  intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h
  simp only [canonicalFillingFun, Subtype.mk.injEq, Prod.mk.injEq] at h
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  apply Fin.ext
  exact rowOfPos_colOfPos_injective la.sortedParts k₁ k₂
    (by omega) (by omega) h.1 h.2

/-- The canonical filling is surjective. -/
theorem canonicalFillingFun_surjective (n : ℕ) (la : Nat.Partition n) :
    Function.Surjective (canonicalFillingFun n la) := by
  intro ⟨⟨r, c⟩, hr, hc⟩
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  obtain ⟨k, hk, hrow, hcol⟩ := exists_pos_of_cell la.sortedParts r c hc
  exact ⟨⟨k, by omega⟩, Subtype.ext (Prod.ext hrow hcol)⟩

/-- The canonical filling as an equivalence `Fin n ≃ Cell n la`. -/
def canonicalFilling (n : ℕ) (la : Nat.Partition n) : Fin n ≃ Cell n la :=
  Equiv.ofBijective (canonicalFillingFun n la)
    ⟨canonicalFillingFun_injective n la, canonicalFillingFun_surjective n la⟩

/-! ### Permutation associated to a standard Young tableau -/

/-- The permutation σ_T ∈ S_n associated to a standard Young tableau T.
Defined so that σ_T maps each position in the canonical filling to the
entry that T assigns to the corresponding cell.

Concretely: if the canonical filling puts position k at cell c, and T
assigns entry T(c) to cell c, then σ_T(k) = T(c).

The inverse direction: σ_T⁻¹ takes an entry value back to its canonical position. -/
def sytPerm (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective T.val T.prop.1).symm.trans (canonicalFilling n la).symm

/-- Distinct standard Young tableaux give distinct permutations. -/
theorem sytPerm_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (sytPerm n la) := by
  intro T₁ T₂ h
  have key : T₁.val = T₂.val := by
    funext c
    -- sytPerm is canonical⁻¹ ∘ (ofBijective T.val)⁻¹
    -- If they agree, then T₁.val = T₂.val
    have h_at := Equiv.ext_iff.mp h (T₁.val c)
    simp only [sytPerm, Equiv.trans_apply] at h_at
    -- h_at involves (ofBijective T₁.val).symm (T₁.val c) which equals c
    have he₁ : (Equiv.ofBijective T₁.val T₁.prop.1).symm (T₁.val c) = c :=
      (Equiv.ofBijective T₁.val T₁.prop.1).symm_apply_apply c
    rw [he₁] at h_at
    have h2 : c = (Equiv.ofBijective T₂.val T₂.prop.1).symm (T₁.val c) :=
      (canonicalFilling n la).symm.injective h_at
    set e₂ := Equiv.ofBijective T₂.val T₂.prop.1
    calc T₁.val c
        = e₂ (e₂.symm (T₁.val c)) :=
          (e₂.apply_symm_apply (T₁.val c)).symm
      _ = e₂ c := by rw [← h2]
      _ = T₂.val c := rfl
  exact Subtype.ext key

/-! ### Polytabloid construction -/

/-- The polytabloid e_T ∈ ℂ[S_n] associated to a standard Young tableau T.
Defined as σ_T · c_λ (left multiplication by the SYT permutation in the
group algebra). This element lies in V_λ = ℂ[S_n] · c_λ by construction. -/
def polytabloid (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    SymGroupAlgebra n :=
  MonoidAlgebra.of ℂ _ (sytPerm n la T) * YoungSymmetrizer n la

/-- The polytabloid e_T lies in the Specht module V_λ = ℂ[S_n] · c_λ. -/
theorem polytabloid_mem_spechtModule (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) :
    polytabloid n la T ∈ SpechtModule n la := by
  unfold polytabloid SpechtModule
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- The polytabloid for the canonical filling equals c_λ (Young symmetrizer). -/
theorem polytabloid_canonical (n : ℕ) (la : Nat.Partition n)
    (T₀ : StandardYoungTableau n la)
    (hT₀ : sytPerm n la T₀ = 1) :
    polytabloid n la T₀ = YoungSymmetrizer n la := by
  simp only [polytabloid, hT₀, MonoidAlgebra.of_apply]
  exact one_mul _

/-! ### Polytabloid as element of the Specht module -/

/-- The polytabloid e_T as an element of the Specht module (subtype). -/
def polytabloidInSpecht (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    SpechtModule n la :=
  ⟨polytabloid n la T, polytabloid_mem_spechtModule n la T⟩

/-! ### Polytabloid basis properties -/

/-- The map from standard Young tableaux to polytabloids in V_λ. -/
def polytabloidMap (n : ℕ) (la : Nat.Partition n) :
    StandardYoungTableau n la → SpechtModule n la :=
  polytabloidInSpecht n la

/-! ### Infrastructure for the linear independence proof -/

/-- A permutation in both the row and column subgroups must be the identity.
This is because (rowOfPos, colOfPos) is injective on valid positions. -/
private theorem row_col_inter_trivial' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hrow : σ ∈ RowSubgroup n la) (hcol : σ ∈ ColumnSubgroup n la) :
    σ = 1 := by
  ext k
  simp only [Equiv.Perm.one_apply]
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  have hk : k.val < la.sortedParts.sum := by rw [hsum]; exact k.isLt
  have hσk : (σ k).val < la.sortedParts.sum := by rw [hsum]; exact (σ k).isLt
  exact rowOfPos_colOfPos_injective la.sortedParts
    (σ k).val k.val hσk hk (hrow k) (hcol k)

/-- The ColumnAntisymmetrizer is zero at permutations outside Q_λ. -/
private lemma columnAntisymmetrizer_apply_not_mem' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∉ ColumnSubgroup n la) :
    (ColumnAntisymmetrizer n la : SymGroupAlgebra n) σ = 0 := by
  classical
  simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  change ((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
    (Finsupp.single (q : Equiv.Perm (Fin n)) (1 : ℂ))) σ = 0
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  split_ifs with h
  · exact absurd (h ▸ q.prop) hσ
  · ring

/-- The coefficient of the identity permutation in the Young symmetrizer is 1.
Uses P_λ ∩ Q_λ = {id}. -/
private lemma youngSymmetrizer_one_coeff (n : ℕ) (la : Nat.Partition n) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) 1 = 1 := by
  classical
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.sum_mul]
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.single_mul_apply, one_mul, mul_one]
  -- Goal: ∑ p : RowSubgroup, (ColumnAntisymmetrizer)(p⁻¹) = 1
  rw [Finset.sum_eq_single (⟨1, (RowSubgroup n la).one_mem⟩ : ↑(RowSubgroup n la))]
  · -- p = 1: ColumnAntisymmetrizer(1⁻¹) = ColumnAntisymmetrizer(1)
    simp only [inv_one]
    -- ColumnAntisymmetrizer at 1 ∈ Q_λ gives sign(1) = 1
    simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single (⟨1, (ColumnSubgroup n la).one_mem⟩ : ↑(ColumnSubgroup n la))]
    · simp [Equiv.Perm.sign_one]
    · intro q _ hq
      change ((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
        (Finsupp.single (q : Equiv.Perm (Fin n)) (1 : ℂ))) 1 = 0
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      have : (q : Equiv.Perm (Fin n)) ≠ 1 := fun h => hq (Subtype.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- p ≠ 1: ColumnAntisymmetrizer(p⁻¹) = 0 because p⁻¹ ∉ Q_λ
    intro p _ hp
    have hp_ne : (p : Equiv.Perm (Fin n)) ≠ 1 := fun h => hp (Subtype.ext h)
    apply columnAntisymmetrizer_apply_not_mem'
    intro hcol
    exact hp_ne (row_col_inter_trivial' n la p.val p.prop
      ((ColumnSubgroup n la).inv_mem_iff.mp hcol))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Evaluation formula: the coefficient of σ in a polytabloid e_T = σ_T · c_λ. -/
private lemma polytabloid_apply (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) (σ : Equiv.Perm (Fin n)) :
    (polytabloid n la T : SymGroupAlgebra n) σ =
      (YoungSymmetrizer n la : SymGroupAlgebra n) ((sytPerm n la T)⁻¹ * σ) := by
  unfold polytabloid
  simp only [MonoidAlgebra.of_apply]
  rw [MonoidAlgebra.single_mul_apply, one_mul]

/-- The coefficient of σ_T in polytabloid e_T is 1. This is the diagonal
entry of the evaluation matrix. -/
private lemma polytabloid_self_coeff (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) :
    (polytabloid n la T : SymGroupAlgebra n) (sytPerm n la T) = 1 := by
  rw [polytabloid_apply, inv_mul_cancel, youngSymmetrizer_one_coeff]

/-! ### Support characterization of the Young symmetrizer

The Young symmetrizer c_λ = a_λ · b_λ = (Σ_{p ∈ P_λ} p) · (Σ_{q ∈ Q_λ} sign(q) · q).
Since P_λ ∩ Q_λ = {id} (proved as `row_col_inter_trivial'`), the map (p,q) ↦ p*q is
injective from P_λ × Q_λ to S_n. Therefore:
- c_λ(g) = 0 if g ∉ P_λ · Q_λ
- c_λ(p*q) = sign(q) for the unique decomposition g = p*q

This is the "support characterization" used in the dominance triangularity analysis.
-/

/-- The coefficient of p ∈ P_λ in the Young symmetrizer equals 1.
This follows from a_λ(p) = 1 for all p ∈ P_λ, and the unique PQ decomposition
p = p · id with id ∈ Q_λ. -/
private lemma youngSymmetrizer_rowPerm_coeff (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) p = 1 := by
  classical
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.sum_mul]
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.single_mul_apply, one_mul]
  -- c_λ(p) = Σ_{r ∈ P_λ} b_λ(r⁻¹ * p). Only r = p contributes (giving b_λ(1) = 1).
  rw [Finset.sum_eq_single (⟨p, hp⟩ : ↑(RowSubgroup n la))]
  · -- r = p: b_λ(p⁻¹ * p) = b_λ(1)
    simp only [inv_mul_cancel]
    simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single (⟨1, (ColumnSubgroup n la).one_mem⟩ : ↑(ColumnSubgroup n la))]
    · simp [Equiv.Perm.sign_one]
    · intro q _ hq
      change ((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
        (Finsupp.single (q : Equiv.Perm (Fin n)) (1 : ℂ))) 1 = 0
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      have : (q : Equiv.Perm (Fin n)) ≠ 1 := fun h => hq (Subtype.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- r ≠ p: b_λ(r⁻¹ * p) = 0 because r⁻¹ * p ∉ Q_λ
    intro r _ hr
    have hr_ne : (r : Equiv.Perm (Fin n)) ≠ p := fun h => hr (Subtype.ext h)
    apply columnAntisymmetrizer_apply_not_mem'
    intro hcol
    have : (r : Equiv.Perm (Fin n))⁻¹ * p = 1 := by
      apply row_col_inter_trivial' n la
      · exact (RowSubgroup n la).mul_mem ((RowSubgroup n la).inv_mem r.prop) hp
      · exact hcol
    exact hr_ne (mul_left_cancel (a := (r : Equiv.Perm (Fin n))⁻¹)
      (by rw [this, inv_mul_cancel]))
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Tabloid projection for linear independence

The correct proof of polytabloid linear independence uses the **tabloid basis**,
not direct evaluation at σ_T. A tabloid is a row-equivalence class of fillings:
two fillings are equivalent if they have the same set of entries in each row.

**Key facts:**
1. The polytabloid e_T = σ_T · c_λ, when projected to the tabloid module,
   equals {T} + (strictly lower tabloids in dominance order).
2. Different standard Young tableaux give different tabloids.
3. The "tabloid projection matrix" is therefore unitriangular.

The tabloid projection of e_{T'} onto the tabloid {T} is:
  tabProj_T(e_{T'}) = Σ_{p ∈ P_λ} e_{T'}(σ_T · p) / |P_λ|

**Note**: The earlier `exists_maximal_for_eval` approach (evaluating only at σ_T)
is INCORRECT — the evaluation matrix M[T,T'] = c_λ(σ_T⁻¹ · σ_{T'}) can be
nonzero in both directions for distinct T, T'. For example, with λ = (2,1,1)
and n = 4, the SYTs T₂ = [[0,2],[1],[3]] and T₃ = [[0,3],[1],[2]] satisfy
σ_{T₂}⁻¹ · σ_{T₃} = σ_{T₃}⁻¹ · σ_{T₂} = (23) ∈ Q_λ, giving c_λ((23)) = -1
in both directions. The tabloid projection approach is needed instead.

**Infrastructure required** (not yet formalized):
- Tabloid module M_λ = ℂ[S_n / P_λ] with basis indexed by tabloids
- Dominance order on tabloids (partial order on unordered row partitions)
- Proof that b_λ applied to a tabloid gives a signed sum of dominated tabloids
- For q ∈ Q_λ \ {id}: the tabloid σ · q · P_λ is strictly dominated by σ · P_λ
  (column permutations decrease dominance)
-/

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in V_λ.

**Correct proof strategy** (via tabloid basis triangularity):

The proof uses the **tabloid module** M_λ = ℂ[S_n / P_λ], whose basis is indexed by
tabloids (row-equivalence classes of fillings). A tabloid {T} groups all fillings with
the same set of entries in each row.

Key steps:
1. e_T = σ_T · a_λ · b_λ. In the tabloid module, σ_T · a_λ projects to |P_λ| · {T}.
2. Multiplying by b_λ = Σ_{q ∈ Q_λ} sign(q) · q gives:
   e_T (in tabloid basis) = {T} + Σ_{tabloid S < {T}} a_S · {S}
   where the sum is over strictly dominated tabloids (James, Chapter 3).
3. Different SYTs give different tabloids (since standardness forces row entries to be sorted).
4. The tabloid expansion matrix is unitriangular → polytabloids are linearly independent.

**Note**: The earlier `exists_maximal_for_eval` approach (evaluating only at σ_T) was
INCORRECT. The evaluation matrix M[T,T'] = c_λ(σ_T⁻¹ · σ_{T'}) can be nonzero in
both directions for distinct T, T'. Counterexample: λ = (2,1,1), n = 4, with
T₂ = [[0,2],[1],[3]] and T₃ = [[0,3],[1],[2]]: σ_{T₂}⁻¹ · σ_{T₃} = (23) ∈ Q_λ,
so c_λ((23)) = -1 ≠ 0, and similarly in the reverse direction.

**Infrastructure required** (not yet formalized):
- Tabloid module M_λ = ℂ[S_n / P_λ] with basis indexed by tabloids
- Dominance order on tabloids (partial order)
- Column permutations decrease dominance: for q ∈ Q_λ \ {id}, the tabloid
  σ · q · P_λ is strictly dominated by σ · P_λ
- Different standard Young tableaux give different tabloids

See also `youngSymmetrizer_rowPerm_coeff` which proves c_λ(p) = 1 for p ∈ P_λ,
a key building block for the tabloid projection diagonal entry. -/
theorem polytabloid_linearIndependent (n : ℕ) (la : Nat.Partition n) :
    LinearIndependent ℂ (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n)) := by
  sorry

/-! ### Straightening infrastructure: row absorption and column inversions -/

/-- Left multiplication by a row permutation is absorbed by the Young symmetrizer:
of(p) · c_λ = c_λ for p ∈ P_λ. This follows from of(p) · a_λ = a_λ. -/
private theorem of_row_mul_youngSymmetrizer' (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ _ p * YoungSymmetrizer n la = YoungSymmetrizer n la := by
  unfold YoungSymmetrizer
  rw [← mul_assoc, of_row_mul_RowSymmetrizer p hp]

/-- The number of "column inversions" in the filling defined by σ. -/
private def columnInvCount' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun pp : Fin n × Fin n =>
    colOfPos la.sortedParts pp.1.val = colOfPos la.sortedParts pp.2.val ∧
    rowOfPos la.sortedParts pp.1.val < rowOfPos la.sortedParts pp.2.val ∧
    σ.symm pp.2 < σ.symm pp.1).card

/-- A filling is column-standard if all columns are increasing. -/
private def isColumnStandard' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p₁ p₂ : Fin n,
    colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val →
    rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val →
    σ.symm p₁ < σ.symm p₂

/-- Row-sorting a column-standard filling produces a standard Young tableau.
Given a column-standard σ, there exists p ∈ P_λ such that sytPerm T = σ * p
for some SYT T. -/
private theorem column_standard_coset_has_syt' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    ∃ T : StandardYoungTableau n la,
      ∃ p ∈ RowSubgroup n la, sytPerm n la T = σ * p := by
  sorry

/-- A column-standard filling gives a standard polytabloid. -/
private theorem column_standard_in_span' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        (polytabloidInSpecht n la T : SymGroupAlgebra n))) := by
  obtain ⟨T, p, hp, hperm⟩ := column_standard_coset_has_syt' n la σ hcs
  have hσ : σ = sytPerm n la T * p⁻¹ := by rw [hperm]; group
  rw [hσ, map_mul, mul_assoc,
      of_row_mul_youngSymmetrizer' n la p⁻¹ ((RowSubgroup n la).inv_mem hp)]
  exact Submodule.subset_span ⟨T, rfl⟩

/-- Garnir reduction: for a non-column-standard filling, of(σ) · c_λ
can be expressed as a combination of of(τᵢ) · c_λ with fewer column inversions. -/
private theorem garnir_reduction' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (h : ¬ isColumnStandard' n la σ) :
    ∃ (S : Finset (Equiv.Perm (Fin n))) (c : Equiv.Perm (Fin n) → ℂ),
      (∀ τ ∈ S, columnInvCount' n la τ < columnInvCount' n la σ) ∧
      MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la =
        S.sum (fun τ => c τ • (MonoidAlgebra.of ℂ _ τ * YoungSymmetrizer n la)) := by
  sorry

/-- **Straightening lemma**: any permutation applied to the Young symmetrizer
lies in the ℂ-span of standard polytabloids.

Proved by well-founded induction on column inversions:
- Base case (0 inversions): σ is column-standard → row-sort within right
  P_λ-coset to get an SYT, using row absorption of c_λ.
- Inductive step: Garnir reduction expresses σ · c_λ as a combination
  of terms with fewer column inversions. -/
theorem perm_mul_youngSymmetrizer_mem_span_polytabloids (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        (polytabloidInSpecht n la T : SymGroupAlgebra n))) := by
  induction h : columnInvCount' n la σ using Nat.strongRecOn generalizing σ with
  | ind m ih =>
  by_cases hcs : isColumnStandard' n la σ
  · exact column_standard_in_span' n la σ hcs
  · obtain ⟨S, c, hlt, heq⟩ := garnir_reduction' n la σ hcs
    rw [heq]
    apply Submodule.sum_mem
    intro τ hτ
    apply Submodule.smul_mem
    exact ih (columnInvCount' n la τ) (h ▸ hlt τ hτ) τ rfl

/-- The polytabloids {e_T : T ∈ SYT(λ)} span V_λ.

**Proof structure:**
1. (⊆) Each polytabloid is in V_λ by `polytabloid_mem_spechtModule`
2. (⊇) Any element of V_λ = ℂ[Sₙ] · cλ is an A-linear combination of cλ,
   hence a ℂ-linear combination of {σ · cλ : σ ∈ Sₙ}. By the straightening
   lemma, each σ · cλ is in the ℂ-span of standard polytabloids. -/
theorem polytabloid_span (n : ℕ) (la : Nat.Partition n) :
    Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n))) =
    (SpechtModule n la).restrictScalars ℂ := by
  apply le_antisymm
  · -- (⊆) Each polytabloid is in V_λ
    rw [Submodule.span_le]
    rintro x ⟨T, rfl⟩
    exact polytabloid_mem_spechtModule n la T
  · -- (⊇) V_λ ⊆ ℂ-span of standard polytabloids
    -- Every element of V_λ is a * c_λ for some a ∈ ℂ[S_n].
    -- Write a = Σ a(σ) · σ, then a * c_λ = Σ a(σ) · (σ * c_λ).
    -- By the straightening lemma, each σ * c_λ is in the ℂ-span.
    intro x hx
    -- Convert from restrictScalars to SpechtModule membership
    have hx' : x ∈ SpechtModule n la := hx
    rw [SpechtModule, Submodule.mem_span_singleton] at hx'
    obtain ⟨a, rfl⟩ := hx'
    -- a • c_λ = a * c_λ in the left regular module
    -- Decompose a as a Finsupp: a = Σ_{g ∈ support} single g (a g)
    have key : a • YoungSymmetrizer n la =
        a.sum (fun g c => c • (MonoidAlgebra.of ℂ _ g * YoungSymmetrizer n la)) := by
      conv_lhs => rw [show a • YoungSymmetrizer n la =
          a * YoungSymmetrizer n la from rfl]
      conv_lhs => rw [← Finsupp.sum_single a]
      simp only [Finsupp.sum, Finset.sum_mul]
      congr 1; ext σ
      simp [MonoidAlgebra.of_apply]
    rw [key]
    apply Submodule.sum_mem
    intro σ _
    exact Submodule.smul_mem _ _ (perm_mul_youngSymmetrizer_mem_span_polytabloids n la σ)

/-! ### Dimension theorem from polytabloid basis -/

/-- The polytabloids form a basis of V_λ, so dim V_λ = |SYT(λ)|.

This combines linear independence and spanning of polytabloids to
construct an explicit basis of the Specht module indexed by standard
Young tableaux of shape λ.

This is the key infrastructure needed for the hook length formula
(Theorem 5.17.1). -/
theorem finrank_spechtModule_eq_card_syt (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Fintype.card (StandardYoungTableau n la) := by
  -- The polytabloids are linearly independent in SymGroupAlgebra n (as a ℂ-module)
  have hli := polytabloid_linearIndependent n la
  -- Their ℂ-span equals V_λ (as a ℂ-submodule of SymGroupAlgebra n)
  have hspan := polytabloid_span n la
  -- finrank of the span of linearly independent vectors equals cardinality
  have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n)))) =
      Fintype.card (StandardYoungTableau n la) :=
    finrank_span_eq_card hli
  -- The span equals V_λ.restrictScalars ℂ, so their finranks are equal
  rw [hspan] at h1
  -- finrank of restrictScalars = finrank of the original module
  -- Both ↥(M.restrictScalars ℂ) and ↥M have the same ℂ-module structure
  convert h1 using 1

end

end Etingof
