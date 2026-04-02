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
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.mul_sum]
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.mul_single_apply, mul_one]
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
theorem polytabloid_apply (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) (σ : Equiv.Perm (Fin n)) :
    (polytabloid n la T : SymGroupAlgebra n) σ =
      (YoungSymmetrizer n la : SymGroupAlgebra n) ((sytPerm n la T)⁻¹ * σ) := by
  unfold polytabloid
  simp only [MonoidAlgebra.of_apply]
  rw [MonoidAlgebra.single_mul_apply, one_mul]

/-- The coefficient of σ_T in polytabloid e_T is 1. This is the diagonal
entry of the evaluation matrix. -/
theorem polytabloid_self_coeff (n : ℕ) (la : Nat.Partition n)
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
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.mul_sum]
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.mul_single_apply, mul_one]
  -- c_λ(p) = Σ_{r ∈ P_λ} b_λ(p * r⁻¹). Only r = p contributes (giving b_λ(1) = 1).
  rw [Finset.sum_eq_single (⟨p, hp⟩ : ↑(RowSubgroup n la))]
  · -- r = p: b_λ(p * p⁻¹) = b_λ(1)
    simp only [mul_inv_cancel]
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
  · -- r ≠ p: b_λ(p * r⁻¹) = 0 because p * r⁻¹ ∉ Q_λ
    intro r _ hr
    have hr_ne : (r : Equiv.Perm (Fin n)) ≠ p := fun h => hr (Subtype.ext h)
    apply columnAntisymmetrizer_apply_not_mem'
    intro hcol
    have hid : p * (r : Equiv.Perm (Fin n))⁻¹ = 1 := by
      apply row_col_inter_trivial' n la
      · exact (RowSubgroup n la).mul_mem hp ((RowSubgroup n la).inv_mem r.prop)
      · exact hcol
    exact hr_ne (inv_injective (mul_left_cancel (a := p) (by rw [hid, mul_inv_cancel])))
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

/-! ### Support characterization of the Young symmetrizer -/

/-- The Young symmetrizer c_λ is supported on Q_λ · P_λ: if c_λ(g) ≠ 0 then g = q · p
for some q ∈ Q_λ and p ∈ P_λ, with c_λ(g) = sign(q). -/
private theorem youngSymmetrizer_support (n : ℕ) (la : Nat.Partition n)
    (g : Equiv.Perm (Fin n))
    (hg : (YoungSymmetrizer n la : SymGroupAlgebra n) g ≠ 0) :
    ∃ q ∈ ColumnSubgroup n la, ∃ p ∈ RowSubgroup n la,
      g = q * p := by
  classical
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.mul_sum] at hg
  rw [Finsupp.finset_sum_apply] at hg
  simp only [MonoidAlgebra.mul_single_apply, mul_one] at hg
  -- hg says ∑_{r ∈ P_λ} b_λ(g · r⁻¹) ≠ 0, so some term is nonzero
  obtain ⟨⟨r, hr⟩, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
  -- b_λ(g · r⁻¹) ≠ 0
  simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply] at hterm
  rw [Finsupp.finset_sum_apply] at hterm
  obtain ⟨⟨q, hq⟩, _, hq_term⟩ := Finset.exists_ne_zero_of_sum_ne_zero hterm
  -- sign(q) · δ_q(g · r⁻¹) ≠ 0
  change ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) •
    (Finsupp.single q (1 : ℂ))) (g * (r : Equiv.Perm (Fin n))⁻¹) ≠ 0 at hq_term
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at hq_term
  split_ifs at hq_term with heq
  · -- g · r⁻¹ = q, so g = q · r
    exact ⟨q, hq, r, hr, by
      have : g = q * r := by
        have h := heq.symm
        calc g = g * r⁻¹ * r := by group
             _ = q * r := by rw [heq]
      exact this⟩
  · simp at hq_term

/-- The coefficient of g in c_λ when g = q · p (q ∈ Q_λ, p ∈ P_λ) is sign(q). -/
private theorem youngSymmetrizer_pq_coeff (n : ℕ) (la : Nat.Partition n)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) (q * p) =
      (↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) := by
  classical
  simp only [YoungSymmetrizer, RowSymmetrizer, MonoidAlgebra.of_apply, Finset.mul_sum]
  rw [Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.mul_single_apply, mul_one]
  -- c_λ(q * p) = Σ_{r ∈ P_λ} b_λ(q * p * r⁻¹). Only r = p contributes (giving b_λ(q) = sign(q)).
  rw [Finset.sum_eq_single (⟨p, hp⟩ : ↑(RowSubgroup n la))]
  · -- r = p: b_λ(q * p * p⁻¹) = b_λ(q) = sign(q)
    simp only [mul_inv_cancel_right]
    simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single (⟨q, hq⟩ : ↑(ColumnSubgroup n la))]
    · change ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) •
        (Finsupp.single q (1 : ℂ))) q = _
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, if_pos rfl, mul_one]
    · intro q' _ hq'
      change ((↑(↑(Equiv.Perm.sign (q' : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
        (Finsupp.single (q' : Equiv.Perm (Fin n)) (1 : ℂ))) q = 0
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      have : (q' : Equiv.Perm (Fin n)) ≠ q := fun h => hq' (Subtype.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- r ≠ p: b_λ(q * p * r⁻¹) = 0 because q * p * r⁻¹ ∉ Q_λ
    intro r _ hr
    have hr_ne : (r : Equiv.Perm (Fin n)) ≠ p := fun h => hr (Subtype.ext h)
    apply columnAntisymmetrizer_apply_not_mem'
    intro hcol
    -- q * p * r⁻¹ ∈ Q_λ means p * r⁻¹ ∈ Q_λ⁻¹ * Q_λ = Q_λ
    have hpr : p * (r : Equiv.Perm (Fin n))⁻¹ ∈ ColumnSubgroup n la := by
      have h2 := (ColumnSubgroup n la).mul_mem ((ColumnSubgroup n la).inv_mem hq) hcol
      simp only [← mul_assoc] at h2
      rwa [inv_mul_cancel, one_mul] at h2
    -- p * r⁻¹ ∈ P_λ ∩ Q_λ = {1}
    have hid := row_col_inter_trivial' n la (p * (r : Equiv.Perm (Fin n))⁻¹)
      ((RowSubgroup n la).mul_mem hp ((RowSubgroup n la).inv_mem r.prop))
      hpr
    exact hr_ne (inv_injective (mul_left_cancel (a := p) (by rw [hid, mul_inv_cancel])))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- If e_{T₂}(σ) ≠ 0, then σ ∈ σ_{T₂} · Q_λ · P_λ: there exist q ∈ Q_λ and p ∈ P_λ
such that σ = σ_{T₂} · q · p. -/
theorem polytabloid_support (n : ℕ) (la : Nat.Partition n)
    (T₂ : StandardYoungTableau n la) (σ : Equiv.Perm (Fin n))
    (hne : (polytabloid n la T₂ : SymGroupAlgebra n) σ ≠ 0) :
    ∃ q ∈ ColumnSubgroup n la, ∃ p ∈ RowSubgroup n la,
      σ = sytPerm n la T₂ * q * p := by
  rw [polytabloid_apply] at hne
  obtain ⟨q, hq, p, hp, heq⟩ := youngSymmetrizer_support n la _ hne
  refine ⟨q, hq, p, hp, ?_⟩
  have : σ = sytPerm n la T₂ * ((sytPerm n la T₂)⁻¹ * σ) := by
    rw [mul_inv_cancel_left]
  rw [this, heq, mul_assoc]

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in V_λ.

The proof is in `TabloidModule.lean` as `polytabloid_linearIndependent'`, using
the tabloid module infrastructure (dominance order, tabloid projections).
This sorry is closed by that proof. -/
theorem polytabloid_linearIndependent (n : ℕ) (la : Nat.Partition n) :
    LinearIndependent ℂ (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n)) := by
  sorry

/-! ### Sorted comparison lemma -/

/-- **Sorted comparison lemma**: if A and B are finsets of the same cardinality m with an
injection f : Fin m → A such that f(i) < B.orderEmbOfFin(i) for all i, then the c-th
smallest element of A is strictly less than the c-th smallest element of B.

The proof is by contradiction: assuming B[c] ≤ A[c], at most c values of j have f(j) < B[c]
(via injectivity into {a ∈ A | a < A[c]}), while all remaining ≥ m-c values must have j > c
(from the pointwise bound), but {j | j > c} has only m-1-c elements. -/
private theorem orderEmbOfFin_lt_of_injective_lt [LinearOrder α]
    {A B : Finset α} {m : ℕ} (hA : A.card = m) (hB : B.card = m)
    (f : Fin m → α) (hfA : ∀ i, f i ∈ A) (hf_inj : Function.Injective f)
    (hlt : ∀ i, f i < B.orderEmbOfFin hB i) (c : Fin m) :
    A.orderEmbOfFin hA c < B.orderEmbOfFin hB c := by
  by_contra hge
  push_neg at hge
  -- hge : B.orderEmbOfFin hB c ≤ A.orderEmbOfFin hA c
  set β := B.orderEmbOfFin hB c
  -- Step 1: For j with f(j) ≥ β, we must have j > c
  have above_c : ∀ j : Fin m, β ≤ f j → c < j := by
    intro j hfj
    have h1 : β < B.orderEmbOfFin hB j := lt_of_le_of_lt hfj (hlt j)
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp h1
  -- Step 2: The "high" set {j | β ≤ f j} is contained in Ioi c
  have hi_sub : Finset.univ.filter (fun j : Fin m => β ≤ f j) ⊆ Finset.Ioi c := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Ioi.mpr (above_c j hj)
  -- Step 3: The "low" set {j | f j < β} maps injectively into A ∩ {a | a < β}
  have lo_inj : (Finset.univ.filter (fun j : Fin m => f j < β)).card ≤
      (A.filter (· < β)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_filter.mpr ⟨hfA j, hj⟩
    · exact Set.InjOn.mono (Set.subset_univ _) (Function.Injective.injOn hf_inj)
  -- Step 4: #{a ∈ A | a < β} ≤ c, because a < β ≤ A[c] implies a < A[c],
  -- and the elements of A strictly below A[c] are exactly {A[0], ..., A[c-1]}
  have filter_le_c : (A.filter (· < β)).card ≤ c.val := by
    have sub : A.filter (· < β) ⊆ A.filter (· < A.orderEmbOfFin hA c) := by
      apply Finset.monotone_filter_right A
      intro a _ ha; exact lt_of_lt_of_le ha hge
    have hsub : A.filter (· < A.orderEmbOfFin hA c) ⊆
        (Finset.Iio c).image (A.orderEmbOfFin hA) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have ⟨ha_mem, ha_lt⟩ := ha
      have ha_range : a ∈ Set.range (A.orderEmbOfFin hA) := by
        rw [Finset.range_orderEmbOfFin]; exact ha_mem
      obtain ⟨j, rfl⟩ := ha_range
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr
        ((A.orderEmbOfFin hA).lt_iff_lt.mp ha_lt), rfl⟩
    calc (A.filter (· < β)).card
        ≤ (A.filter (· < A.orderEmbOfFin hA c)).card := Finset.card_le_card sub
      _ ≤ ((Finset.Iio c).image (A.orderEmbOfFin hA)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Iio c).card := Finset.card_image_le
      _ = c.val := @Fin.card_Iio m c
  -- Step 5: Counting contradiction
  have sum_eq : (Finset.univ.filter (fun j : Fin m => f j < β)).card +
      (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card = m := by
    have := @Finset.card_filter_add_card_filter_not _ (Finset.univ : Finset (Fin m))
      (fun j : Fin m => f j < β) _ _
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hi_card : (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card ≤ m - 1 - c.val := by
    calc (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card
        ≤ (Finset.Ioi c).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          exact Finset.mem_Ioi.mpr (above_c j hj)
      _ = m - 1 - c.val := @Fin.card_Ioi m c
  omega

/-! ### Straightening infrastructure: row absorption and column inversions -/

/-- Right multiplication by a row permutation is absorbed by the Young symmetrizer:
c_λ · of(p) = c_λ for p ∈ P_λ. This follows from a_λ · of(p) = a_λ. -/
private theorem of_row_mul_youngSymmetrizer' (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    YoungSymmetrizer n la * MonoidAlgebra.of ℂ _ p = YoungSymmetrizer n la := by
  unfold YoungSymmetrizer
  rw [mul_assoc, RowSymmetrizer_mul_of_row p hp]

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
Given a column-standard σ, there exists p ∈ P_λ such that σ = p * sytPerm T
for some SYT T (LEFT coset).

**Note**: The RIGHT coset form `sytPerm T = σ * p` is FALSE in general.
Counterexample: partition (3,1) of n=4, σ = (13). Row-sorting gives SYT
T = [0,2,3/1] with sytPerm T = [0,3,1,2]. Then σ⁻¹ * sytPerm T = (23),
which is NOT in RowSubgroup (it maps position 2 in row 0 to position 3 in
row 1). Checked for ALL 3 SYTs of shape (3,1): none satisfy the right coset.

The left coset holds because: for each entry e in row r of the filling,
σ(e) and sytPerm T(e) are both positions in row r. The permutation
p = σ * sytPerm T⁻¹ maps canonical position k to σ(T(canonicalFilling(k))),
which is a position in the same canonical row as k. -/
private theorem column_standard_coset_has_syt' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    ∃ T : StandardYoungTableau n la,
      ∃ p ∈ RowSubgroup n la, σ = p * sytPerm n la T := by
  classical
  set parts := la.sortedParts with parts_def
  have hps : parts.sum = n := sortedParts_sum n la
  -- Positions in row r
  let rowPositions (r : ℕ) : Finset (Fin n) :=
    Finset.univ.filter (fun pos => rowOfPos parts pos.val = r)
  -- Entries in row r under filling σ
  let rowEntries (r : ℕ) : Finset (Fin n) := (rowPositions r).image σ.symm
  -- σ.symm is injective on each row
  have σ_inj_on_row (r : ℕ) : Set.InjOn σ.symm ↑(rowPositions r) :=
    Set.InjOn.mono (Set.subset_univ _) (Equiv.injective σ.symm).injOn
  -- Row entry cardinality equals row width
  have rowEnt_card : ∀ r : ℕ, r < parts.length →
      (rowEntries r).card = parts.getD r 0 := by
    intro r hr; rw [Finset.card_image_of_injOn (σ_inj_on_row r)]
    set S := rowPositions r
    set w := parts.getD r 0
    -- colOfPos injects S into Finset.range w
    have h_inj : Set.InjOn (fun pos : Fin n => colOfPos parts pos.val) ↑S := by
      intro ⟨a, _⟩ ha ⟨b, _⟩ hb heq
      simp only [S, rowPositions, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (rowOfPos_colOfPos_injective parts a b
        (by omega) (by omega) (ha.trans hb.symm) heq)
    have h_range : ∀ pos ∈ S, colOfPos parts pos.val ∈ Finset.range w := by
      intro pos hpos
      simp only [S, rowPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
      have := colOfPos_lt_getD parts pos.val (by omega)
      rw [hpos] at this; exact Finset.mem_range.mpr this
    -- exists_pos_of_cell provides a right inverse, showing surjectivity
    have h_surj : Finset.range w ⊆ (S.image (fun pos : Fin n => colOfPos parts pos.val)) := by
      intro c hc
      rw [Finset.mem_range] at hc
      obtain ⟨k, hk, hrow, hcol⟩ := exists_pos_of_cell parts r c hc
      exact Finset.mem_image.mpr ⟨⟨k, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩, hcol⟩
    -- |S| = |image of S under colOfPos| (by injectivity) = w (by surjectivity)
    calc S.card = (S.image (fun pos : Fin n => colOfPos parts pos.val)).card :=
          (Finset.card_image_of_injOn h_inj).symm
      _ = (Finset.range w).card := by
          apply le_antisymm
          · exact Finset.card_le_card (Finset.image_subset_iff.mpr (fun pos hp => h_range pos hp))
          · exact Finset.card_le_card h_surj
      _ = w := Finset.card_range w
  -- Define the sorted filling T(cell(r,c)) = c-th smallest entry in row r
  let T_fun : Cell n la → Fin n := fun cell =>
    (rowEntries cell.val.1).orderEmbOfFin (rowEnt_card cell.val.1 cell.prop.1)
      ⟨cell.val.2, by have := cell.prop.2; omega⟩
  -- T_fun is injective (different rows → disjoint entry sets; same row → orderEmb injective)
  have T_inj : Function.Injective T_fun := by
    intro ⟨⟨r₁, c₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, c₂⟩, hr₂, hc₂⟩ h
    simp only [T_fun] at h
    by_cases hr : r₁ = r₂
    · subst hr
      have hinj := ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).injective
      have := Fin.mk.inj (hinj h)
      exact Subtype.ext (Prod.ext rfl this)
    · exfalso
      -- The entry T_fun(r₁,c₁) is in rowEntries r₁ and (by h) also in rowEntries r₂
      have h1 := Finset.orderEmbOfFin_mem (rowEntries r₁) (rowEnt_card r₁ hr₁) ⟨c₁, by omega⟩
      have h2 := Finset.orderEmbOfFin_mem (rowEntries r₂) (rowEnt_card r₂ hr₂) ⟨c₂, by omega⟩
      -- h gives that these two orderEmbOfFin values are equal
      -- So the entry from row r₂ is also in rowEntries r₁
      have h1' : (rowEntries r₂).orderEmbOfFin (rowEnt_card r₂ hr₂)
          ⟨c₂, by omega⟩ ∈ rowEntries r₁ := h ▸ h1
      -- Unpack: entry ∈ rowEntries r means ∃ pos in row r with σ.symm pos = entry
      obtain ⟨pos₁, hpos₁, hv₁⟩ := Finset.mem_image.mp h1'
      obtain ⟨pos₂, hpos₂, hv₂⟩ := Finset.mem_image.mp h2
      -- Same entry from both rows
      have := σ.symm.injective (hv₁.trans hv₂.symm)
      rw [this] at hpos₁
      exact hr ((Finset.mem_filter.mp hpos₁).2.symm.trans (Finset.mem_filter.mp hpos₂).2)
  -- T_fun is surjective (injective function between types of equal finite cardinality)
  have T_surj : Function.Surjective T_fun := by
    have h_card : Fintype.card (Cell n la) = Fintype.card (Fin n) :=
      Fintype.card_of_bijective (canonicalFilling n la).bijective |>.symm
    exact ((Fintype.bijective_iff_injective_and_card T_fun).mpr ⟨T_inj, h_card⟩).2
  -- T_fun is row-increasing (orderEmbOfFin is monotone)
  have T_row_inc : ∀ c₁ c₂ : Cell n la,
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → T_fun c₁ < T_fun c₂ := by
    intro ⟨⟨r₁, col₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, col₂⟩, hr₂, hc₂⟩ hrow hcol
    simp only at hrow hcol; subst hrow
    exact ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).strictMono (by omega)
  -- T_fun is column-increasing: cells in same column, lower row > upper row.
  -- Requires: (1) sorted parts monotone (r₁ < r₂ ⟹ parts[r₁] ≥ parts[r₂])
  -- (2) column-standardness of σ to provide pointwise entry bounds between rows
  -- (3) orderEmbOfFin comparison: if row r₁ has ≥ j+1 entries < B[j], then A[j] < B[j]
  have T_col_inc : ∀ c₁ c₂ : Cell n la,
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → T_fun c₁ < T_fun c₂ := by
    -- Row-sorting preserves column-increasing for column-standard fillings.
    -- Proof outline: assume B[col] ≤ A[col] for contradiction.
    -- For each of the col+1 sorted entries B[0]≤...≤B[col] of rowEntries r₂,
    -- the column-standard condition provides a strictly smaller entry in rowEntries r₁
    -- (at the same column in the diagram). These col+1 distinct entries are all < B[col],
    -- but A[col] ≥ B[col] allows at most col elements of rowEntries r₁ below B[col].
    sorry
  let T : StandardYoungTableau n la :=
    ⟨T_fun, ⟨T_inj, T_surj⟩, T_row_inc, T_col_inc⟩
  -- T_fun maps row-r cells to entries in rowEntries r
  have T_mem_rowEntries : ∀ (cell : Cell n la),
      T_fun cell ∈ rowEntries cell.val.1 := by
    intro ⟨⟨r, c⟩, hr, hc⟩
    exact Finset.orderEmbOfFin_mem (rowEntries r) (rowEnt_card r hr) ⟨c, by omega⟩
  -- p = σ * (sytPerm T)⁻¹ preserves rows (LEFT coset: σ = p * sytPerm T)
  --
  -- Proof sketch: p(k) = σ((sytPerm T)⁻¹(k)). (sytPerm T)⁻¹(k) = T(canonical_cell(k)),
  -- i.e., the entry that T assigns to the cell at canonical position k.
  -- That entry is in rowEntries(rowOfPos(k)), so ∃ pos ∈ rowPositions(rowOfPos(k))
  -- with σ.symm(pos) = that entry, hence σ(that entry) = pos, and
  -- rowOfPos(pos) = rowOfPos(k). So rowOfPos(p(k)) = rowOfPos(k). ✓
  let p := σ * (sytPerm n la T)⁻¹
  have hp_row : p ∈ RowSubgroup n la := by
    intro k
    simp only [p, Equiv.Perm.coe_mul, Function.comp_apply]
    -- Goal: rowOfPos parts (σ ((sytPerm n la T)⁻¹ k)).val = rowOfPos parts k.val
    -- (sytPerm T)⁻¹(k) is the entry at the canonical cell of position k
    -- That entry is in T_fun(canonical_cell(k)), which is in rowEntries(rowOfPos(k))
    -- T_mem_rowEntries tells us: T_fun(cell) ∈ rowEntries(cell.val.1)
    -- And rowEntries(r) = (rowPositions r).image σ.symm,
    -- so the entry maps under σ to a position in the same row.
    set entry := (sytPerm n la T)⁻¹ k with entry_def
    -- entry = T_fun(canonical cell at k)
    have h_entry : entry = T_fun ((canonicalFilling n la) k) := by
      simp only [entry_def, sytPerm, Equiv.Perm.inv_def, Equiv.symm_trans_apply,
                 Equiv.symm_symm, Equiv.ofBijective_apply]
      rfl
    -- canonical cell's row = rowOfPos parts k.val
    have h_cell_row : ((canonicalFilling n la) k).val.1 = rowOfPos parts k.val := by
      simp [canonicalFilling, canonicalFillingFun, Equiv.ofBijective_apply]
      rfl
    -- entry ∈ rowEntries(rowOfPos parts k.val)
    have h_mem : entry ∈ rowEntries (rowOfPos parts k.val) := by
      rw [h_entry, ← h_cell_row]
      exact T_mem_rowEntries ((canonicalFilling n la) k)
    -- Unpack: ∃ pos with σ.symm(pos) = entry and pos in same row
    obtain ⟨pos, hpos, hv⟩ := Finset.mem_image.mp h_mem
    -- σ(entry) = pos
    have h_σ : σ entry = pos := by rw [← hv]; exact σ.apply_symm_apply pos
    rw [h_σ]
    exact (Finset.mem_filter.mp hpos).2
  exact ⟨T, p, hp_row, by simp only [p]; group⟩

/-- A column-standard filling gives a standard polytabloid.

**KNOWN ISSUE**: The previous proof used right-coset absorption:
  σ = sytPerm T * p⁻¹ ⟹ of(σ) * YS = of(sytPerm T) * of(p⁻¹) * YS = of(sytPerm T) * YS
But the right coset `sytPerm T = σ * p` is FALSE (see column_standard_coset_has_syt' doc).

With the correct LEFT coset `σ = p * sytPerm T`:
  of(σ) * YS = of(p) * of(sytPerm T) * YS
The left factor of(p) does NOT absorb into of(sytPerm T) * YS in general.

**ROOT CAUSE**: The polytabloid definition `of(sytPerm T) * a_λ * b_λ` uses the canonical
column antisymmetrizer b_λ. In James' treatment, the correct polytabloid uses the
T-DEPENDENT column antisymmetrizer: e_T = of(sytPerm T) * b_λ * a_λ (column × row,
not row × column). With that definition, the left coset works because
`a_λ * of(p) = a_λ` (right absorption of RowSymmetrizer).

Fixing this requires changing YoungSymmetrizer from `a_λ * b_λ` to `b_λ * a_λ`
or defining T-dependent polytabloids. See GitHub issue for details. -/
private theorem column_standard_in_span' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        (polytabloidInSpecht n la T : SymGroupAlgebra n))) := by
  sorry

/-- Non-column-standard implies existence of a column inversion. -/
private theorem exists_column_inversion (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (h : ¬ isColumnStandard' n la σ) :
    ∃ p₁ p₂ : Fin n,
      colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val ∧
      rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val ∧
      σ.symm p₂ < σ.symm p₁ := by
  simp only [isColumnStandard', not_forall] at h
  obtain ⟨p₁, p₂, hcol, hrow, hinv⟩ := h
  simp only [not_lt] at hinv
  have hne : p₁ ≠ p₂ := by intro heq; rw [heq] at hrow; exact Nat.lt_irrefl _ hrow
  have hne' : σ.symm p₁ ≠ σ.symm p₂ := σ.symm.injective.ne hne
  exact ⟨p₁, p₂, hcol, hrow, lt_of_le_of_ne hinv hne'.symm⟩

/-! ### Garnir element infrastructure

The Garnir reduction uses the following strategy:
1. Find a column inversion: positions p₁ (row r₁) and p₂ (row r₂) in column j
   with r₁ < r₂ and σ⁻¹(p₂) < σ⁻¹(p₁).
2. Define the Garnir set: A = positions in row r₁ with column ≥ j,
   B = positions in row r₂ with column ≤ j. Note |A| + |B| = (λ_{r₁} - j) + (j + 1) = λ_{r₁} + 1.
3. The Garnir element G = Σ_{w ∈ S_{A∪B}} sign(w) · w satisfies a_λ · G = 0 because
   P_λ ∩ S_{A∪B} contains a transposition t, and a_λ · t = a_λ while t · G = -G,
   giving a_λ · G = a_λ · t · G = -a_λ · G, hence 2 · a_λ · G = 0, so a_λ · G = 0
   (in characteristic 0).
4. Extracting the identity term: from a_λ · G = 0, we get
   a_λ = -Σ_{w ≠ id} sign(w) · a_λ · of(w)
   Hence c_λ = a_λ · b_λ = -Σ_{w ≠ id} sign(w) · a_λ · of(w) · b_λ
   And of(σ) · c_λ = -Σ_{w ≠ id} sign(w) · of(σ) · a_λ · of(w) · b_λ
5. Each term of(σ) · a_λ · of(w) · b_λ equals Σ_p of(σ·p·w) · b_λ, and the
   resulting permutations σ·p·w have fewer column inversions than σ.
-/

/-- The Garnir set positions: right part of row r₁ from column j,
plus left part of row r₂ through column j.

These are positions (as Fin n) satisfying:
- In row r₁ with column ≥ j, OR
- In row r₂ with column ≤ j -/
private def garnirSet (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) : Finset (Fin n) :=
  let parts := la.sortedParts
  let r₁ := rowOfPos parts p₁.val
  let r₂ := rowOfPos parts p₂.val
  let j := colOfPos parts p₁.val
  Finset.univ.filter fun pos =>
    (rowOfPos parts pos.val = r₁ ∧ j ≤ colOfPos parts pos.val) ∨
    (rowOfPos parts pos.val = r₂ ∧ colOfPos parts pos.val ≤ j)

/-- The Garnir element: alternating sum over all permutations supported on the Garnir set.
G = Σ_{w ∈ S_{garnirSet}} sign(w) · of(w) -/
private noncomputable def garnirElement (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) : SymGroupAlgebra n :=
  ∑ w : { w : Equiv.Perm (Fin n) // ∀ x, x ∉ garnirSet n la p₁ p₂ → w x = x },
    (↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ w.val

/-- The Garnir set contains at least two positions in the same row (pigeonhole).
Specifically, it contains p₁ and some other position in the same row as p₁
(or p₂ and another in row(p₂)) when the corresponding row has width ≥ 2. -/
private theorem garnirSet_has_row_pair (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val) :
    ∃ a b : Fin n, a ≠ b ∧ a ∈ garnirSet n la p₁ p₂ ∧ b ∈ garnirSet n la p₁ p₂ ∧
      rowOfPos la.sortedParts a.val = rowOfPos la.sortedParts b.val := by
  sorry

/-- Left multiplication by a transposition t ∈ S_{A∪B} negates the Garnir element:
of(t) * G = -G. This is a standard property of alternating sums. -/
private theorem left_transposition_negates_garnir (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) (t : Equiv.Perm (Fin n))
    (ht_supp : ∀ x, x ∉ garnirSet n la p₁ p₂ → t x = x)
    (ht_sign : Equiv.Perm.sign t = -1) :
    MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂ =
      -garnirElement n la p₁ p₂ := by
  sorry

private theorem garnir_row_annihilates (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val) :
    RowSymmetrizer n la * garnirElement n la p₁ p₂ = 0 := by
  -- Step 1: Find a transposition t in P_λ ∩ S_{A∪B}
  obtain ⟨a, b, hab, ha_mem, hb_mem, hrow_eq⟩ :=
    garnirSet_has_row_pair n la p₁ p₂ hcol hrow
  set t := Equiv.swap a b
  -- t is a transposition (sign = -1)
  have ht_sign : Equiv.Perm.sign t = -1 := Equiv.Perm.sign_swap hab
  -- t is supported on garnirSet (a, b ∈ garnirSet, swap fixes everything else)
  have ht_supp : ∀ x, x ∉ garnirSet n la p₁ p₂ → t x = x := by
    intro x hx
    simp only [t, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact absurd (h1 ▸ ha_mem) hx
    · exact absurd (h2 ▸ hb_mem) hx
    · rfl
  -- t ∈ P_λ (row subgroup): a and b are in the same row
  have ht_row : t ∈ RowSubgroup n la := by
    intro k; simp only [t, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact h1 ▸ hrow_eq.symm
    · exact h2 ▸ hrow_eq
    · rfl
  -- Step 2: use a_λ * of(t) = a_λ and of(t) * G = -G to get a_λ * G = -(a_λ * G)
  have h_neg : MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂ =
      -garnirElement n la p₁ p₂ :=
    left_transposition_negates_garnir n la p₁ p₂ t ht_supp ht_sign
  have h_absorb : RowSymmetrizer n la * MonoidAlgebra.of ℂ _ t =
      RowSymmetrizer n la := RowSymmetrizer_mul_of_row t ht_row
  -- key: a_λ * G = a_λ * (of(t) * of(t)) * G = (a_λ * of(t)) * (of(t) * G) = a_λ * (-G)
  have key : RowSymmetrizer n la * garnirElement n la p₁ p₂ =
      -(RowSymmetrizer n la * garnirElement n la p₁ p₂) := by
    have h_tt : t * t = 1 := Equiv.swap_mul_self a b
    -- Insert t * t = 1 before G
    have h_inv : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t *
        MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t = 1 := by
      rw [← map_mul, Equiv.swap_mul_self a b, map_one]
    have h_inv : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t *
        (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t * garnirElement n la p₁ p₂) =
        garnirElement n la p₁ p₂ := by
      rw [← mul_assoc, h_inv, one_mul]
    calc RowSymmetrizer n la * garnirElement n la p₁ p₂
        = RowSymmetrizer n la * (MonoidAlgebra.of ℂ _ t *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂)) := by
          rw [h_inv]
      _ = (RowSymmetrizer n la * MonoidAlgebra.of ℂ _ t) *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂) := by
          rw [mul_assoc]
      _ = RowSymmetrizer n la *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂) := by
          rw [h_absorb]
      _ = RowSymmetrizer n la * (-garnirElement n la p₁ p₂) := by rw [h_neg]
      _ = -(RowSymmetrizer n la * garnirElement n la p₁ p₂) := mul_neg _ _
  -- x = -x implies x = 0 (char 0)
  have h2 : RowSymmetrizer n la * garnirElement n la p₁ p₂ +
      RowSymmetrizer n la * garnirElement n la p₁ p₂ = 0 := by
    nth_rw 1 [key]; exact neg_add_cancel _
  have h3 : (2 : ℂ) • (RowSymmetrizer n la * garnirElement n la p₁ p₂) = 0 := by
    rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

/-- Garnir reduction via the Garnir element identity.

From `a_λ · G = 0`, extracting the identity term gives:
  `a_λ = -Σ_{w ≠ id} sign(w) · a_λ · of(w)`
Multiplying: `of(σ) · c_λ = -Σ_{w ≠ id} sign(w) · of(σ) · a_λ · of(w) · b_λ`

Each non-identity w ∈ S_{A∪B} moves entries between rows r₁ and r₂,
which reduces column inversions. Specifically:
- The terms `of(σ) · a_λ · of(w) · b_λ` can be regrouped as
  `Σ_τ d(τ) · of(τ) · c_λ` where each τ has fewer column inversions.

The column inversion decrease comes from: w moves entries from the
high-inversion row arrangement into a lower-inversion arrangement by
"sorting" entries between adjacent rows in the same column. -/
private theorem garnir_identity_expansion (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hinv : σ.symm p₂ < σ.symm p₁) :
    ∃ (S : Finset (Equiv.Perm (Fin n))) (c : Equiv.Perm (Fin n) → ℂ),
      (∀ τ ∈ S, columnInvCount' n la τ < columnInvCount' n la σ) ∧
      MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la =
        S.sum (fun τ => c τ • (MonoidAlgebra.of ℂ _ τ * YoungSymmetrizer n la)) := by
  sorry

/-- Garnir reduction: for a non-column-standard filling, of(σ) · c_λ
can be expressed as a combination of of(τᵢ) · c_λ with fewer column inversions.

The standard proof uses the Garnir element (see James, Ch. 7). -/
private theorem garnir_reduction' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (h : ¬ isColumnStandard' n la σ) :
    ∃ (S : Finset (Equiv.Perm (Fin n))) (c : Equiv.Perm (Fin n) → ℂ),
      (∀ τ ∈ S, columnInvCount' n la τ < columnInvCount' n la σ) ∧
      MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la =
        S.sum (fun τ => c τ • (MonoidAlgebra.of ℂ _ τ * YoungSymmetrizer n la)) := by
  obtain ⟨p₁, p₂, hcol, hrow, hinv⟩ := exists_column_inversion n la σ h
  exact garnir_identity_expansion n la σ p₁ p₂ hcol hrow hinv

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
