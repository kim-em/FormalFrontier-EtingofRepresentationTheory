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
* `Etingof.RelColumnAntisymmetrizer` — κ_T = Σ_{π ∈ C_T} sign(π) · of(π), the T-relative
  column antisymmetrizer
* `Etingof.polytabloid` — the polytabloid e_T = κ_T · of(σ_T) · a_λ (James' definition)

## Main results

* `Etingof.polytabloid_mem_spechtModule` — polytabloids lie in the Specht module
* `Etingof.polytabloid_linearIndependent` — polytabloids are linearly independent (sorry;
  proved at tabloid level as `polytabloidTab_linearIndependent` in `TabloidModule.lean`)
* `Etingof.perm_mul_youngSymmetrizer_mem_span_polytabloids` — straightening lemma (sorry;
  requires tabloid-level straightening or dimension argument; see issue #2104)
* `Etingof.polytabloid_span` — polytabloids span the Specht module (from straightening)
* `Etingof.finrank_spechtModule_eq_card_syt` — dim V_λ = |SYT(λ)| (from independence + span)

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

/-! ### T-relative column antisymmetrizer -/

/-- T-relative column antisymmetrizer: κ_T = Σ_{π ∈ C_T} sign(π) · of(π)
where C_T = σ_T⁻¹ Q_λ σ_T is the entry-level column stabilizer of T.

We sum over q ∈ Q_λ (position-level column subgroup) and conjugate each
element by σ_T to get the corresponding entry-level permutation.
Since sign is conjugation-invariant, sign(σ_T⁻¹ q σ_T) = sign(q). -/
noncomputable def RelColumnAntisymmetrizer (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) : SymGroupAlgebra n :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ q : ↥(ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ ((sytPerm n la T)⁻¹ * q.val * sytPerm n la T)

/-- When σ_T = 1, the T-relative column antisymmetrizer equals the canonical one. -/
theorem relColumnAntisymmetrizer_eq_of_sytPerm_one (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) (h : sytPerm n la T = 1) :
    RelColumnAntisymmetrizer n la T = ColumnAntisymmetrizer n la := by
  simp only [RelColumnAntisymmetrizer, ColumnAntisymmetrizer, h, inv_one, one_mul, mul_one,
    MonoidAlgebra.of_apply]

/-! ### Polytabloid construction -/

/-- The polytabloid e_T ∈ ℂ[S_n] associated to a standard Young tableau T.

Defined as κ_T · of(σ_T) · a_λ, where κ_T is the T-relative column
antisymmetrizer (summing over C_T = σ_T⁻¹ Q_λ σ_T) and a_λ is the
row symmetrizer.

This uses the T-dependent column antisymmetrizer (following James' treatment)
rather than the canonical b_λ. With the canonical b_λ, the polytabloid
depends only on the right P_λ-coset of σ_T, making it non-injective on SYTs.
The T-dependent version ensures different SYTs give different polytabloids. -/
def polytabloid (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    SymGroupAlgebra n :=
  RelColumnAntisymmetrizer n la T * MonoidAlgebra.of ℂ _ (sytPerm n la T) *
    RowSymmetrizer n la

/-- The polytabloid e_T lies in the Specht module V_λ = ℂ[S_n] · c_λ.

With the T-dependent column antisymmetrizer, membership in V_λ = ℂ[S_n] · a_λ · b_λ
is no longer trivial. The proof requires showing that κ_T · of(σ_T) · a_λ can be
expressed as a left multiple of a_λ · b_λ. -/
theorem polytabloid_mem_spechtModule (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) :
    polytabloid n la T ∈ SpechtModule n la := by
  sorry

/-- The polytabloid for the canonical filling equals b_λ · a_λ
(column antisymmetrizer times row symmetrizer). -/
theorem polytabloid_canonical (n : ℕ) (la : Nat.Partition n)
    (T₀ : StandardYoungTableau n la)
    (hT₀ : sytPerm n la T₀ = 1) :
    polytabloid n la T₀ = ColumnAntisymmetrizer n la * RowSymmetrizer n la := by
  unfold polytabloid
  rw [relColumnAntisymmetrizer_eq_of_sytPerm_one n la T₀ hT₀, hT₀,
    MonoidAlgebra.of_apply, mul_assoc]
  congr 1
  rw [show (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) (1 : ℂ)) = 1 from rfl, one_mul]

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

/-- The RowSymmetrizer is zero at permutations outside P_λ. -/
private lemma rowSymmetrizer_apply_not_mem' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∉ RowSubgroup n la) :
    (RowSymmetrizer n la : SymGroupAlgebra n) σ = 0 := by
  classical
  simp only [RowSymmetrizer, MonoidAlgebra.of_apply]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finsupp.single_apply]
  split_ifs with h
  · exact absurd (h ▸ p.prop) hσ
  · rfl

/-! ### Support characterization of the Young symmetrizer

The Young symmetrizer c_λ = b_λ · a_λ = (Σ_{q ∈ Q_λ} sign(q) · q) · (Σ_{p ∈ P_λ} p).
Since P_λ ∩ Q_λ = {id} (proved as `row_col_inter_trivial'`), the map (q,p) ↦ q*p is
injective from Q_λ × P_λ to S_n. Therefore:
- c_λ(g) = 0 if g ∉ Q_λ · P_λ
- c_λ(q*p) = sign(q) for the unique decomposition g = q*p

This is the "support characterization" used in the dominance triangularity analysis.
-/

/-- The Young symmetrizer c_λ = b·a is supported on Q_λ · P_λ: if c_λ(g) ≠ 0 then g = q · p
for some q ∈ Q_λ and p ∈ P_λ, with c_λ(g) = sign(q). -/
private theorem youngSymmetrizer_support (n : ℕ) (la : Nat.Partition n)
    (g : Equiv.Perm (Fin n))
    (hg : (YoungSymmetrizer n la : SymGroupAlgebra n) g ≠ 0) :
    ∃ q ∈ ColumnSubgroup n la, ∃ p ∈ RowSubgroup n la,
      g = q * p := by
  classical
  change (ColumnAntisymmetrizer n la * RowSymmetrizer n la) g ≠ 0 at hg
  have hmem : g ∈ (ColumnAntisymmetrizer n la * RowSymmetrizer n la).support :=
    Finsupp.mem_support_iff.mpr hg
  obtain ⟨q', hq'_mem, p', hp'_mem, hg_eq⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hmem)
  have hq'_col : q' ∈ ColumnSubgroup n la := by
    simp only [ColumnAntisymmetrizer, MonoidAlgebra.of_apply] at hq'_mem
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hq'_mem
    by_contra h_not
    apply hq'_mem
    apply Finset.sum_eq_zero
    intro ⟨r, hr⟩ _
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs with heq
    · exact absurd (heq ▸ hr) h_not
    · ring
  have hp'_row : p' ∈ RowSubgroup n la := by
    simp only [RowSymmetrizer, MonoidAlgebra.of_apply] at hp'_mem
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hp'_mem
    by_contra h_not
    apply hp'_mem
    apply Finset.sum_eq_zero
    intro ⟨r, hr⟩ _
    rw [Finsupp.single_apply]
    split_ifs with heq
    · exact absurd (heq ▸ hr) h_not
    · rfl
  exact ⟨q', hq'_col, p', hp'_row, hg_eq.symm⟩

/-- The coefficient of g in c_λ = b·a when g = q · p (q ∈ Q_λ, p ∈ P_λ) is sign(q). -/
private theorem youngSymmetrizer_pq_coeff (n : ℕ) (la : Nat.Partition n)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) (q * p) =
      (↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) := by
  classical
  -- Use support_mul approach: first show q * p ∈ support implies it factors through Q_λ × P_λ
  -- Direct evaluation via support analysis
  change (ColumnAntisymmetrizer n la * RowSymmetrizer n la) (q * p) = _
  -- The support of b_λ * a_λ ⊆ Q_λ * P_λ with the unique decomposition giving sign(q)
  -- We prove this by showing: for any decomposition g = q' * p' with q' ∈ Q_λ and p' ∈ P_λ,
  -- we must have q' = q and p' = p (by P∩Q = {1}).
  -- Use the convolution formula: (f * g)(x) = Σ_{y} f(y) * g(y⁻¹ * x)
  have heval : (ColumnAntisymmetrizer n la * RowSymmetrizer n la) (q * p) =
      ∑ q' : ↥(ColumnSubgroup n la),
        ((↑(↑(Equiv.Perm.sign q'.val) : ℤ) : ℂ) *
          (RowSymmetrizer n la : SymGroupAlgebra n) (q'.val⁻¹ * (q * p))) := by
    unfold ColumnAntisymmetrizer
    simp only [MonoidAlgebra.of_apply, Finset.sum_mul]
    rw [Finsupp.finset_sum_apply (N := ℂ)]
    congr 1; ext ⟨q', hq'⟩
    rw [Algebra.smul_mul_assoc, Finsupp.smul_apply, smul_eq_mul,
        MonoidAlgebra.single_mul_apply, one_mul]
  rw [heval]
  -- Only q' = q contributes: q'⁻¹ * (q * p) ∈ P_λ iff q' = q
  rw [Finset.sum_eq_single (⟨q, hq⟩ : ↥(ColumnSubgroup n la))]
  · -- q' = q: q⁻¹ * (q * p) = p ∈ P_λ, so a_λ(p) = 1
    simp only [inv_mul_cancel_left]
    rw [show (RowSymmetrizer n la : SymGroupAlgebra n) p = 1 from by
      simp only [RowSymmetrizer, MonoidAlgebra.of_apply]
      rw [Finsupp.finset_sum_apply]
      rw [Finset.sum_eq_single (⟨p, hp⟩ : ↥(RowSubgroup n la))]
      · simp
      · intro ⟨p', _⟩ _ hne
        rw [Finsupp.single_apply, if_neg (fun h => hne (Subtype.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h]
    ring
  · -- q' ≠ q: q'⁻¹ * (q * p) = (q'⁻¹ * q) * p, and a_λ at this is 0 unless q'⁻¹q ∈ P_λ
    intro ⟨q', hq'⟩ _ hne
    suffices h : (RowSymmetrizer n la : SymGroupAlgebra n) (q'⁻¹ * (q * p)) = 0 by
      rw [h, mul_zero]
    simp only [RowSymmetrizer, MonoidAlgebra.of_apply]
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro ⟨p', hp'⟩ _
    rw [Finsupp.single_apply]
    rw [if_neg]
    intro heq
    -- q'⁻¹ * q * p = p' implies q'⁻¹ * q = p' * p⁻¹ ∈ P_λ
    have : q'⁻¹ * q = p' * p⁻¹ := by
      have h : p' = q'⁻¹ * (q * p) := heq
      calc q'⁻¹ * q = q'⁻¹ * (q * p) * p⁻¹ := by group
        _ = p' * p⁻¹ := by rw [← h]
    have hqp_row : q'⁻¹ * q ∈ RowSubgroup n la := by
      rw [this]; exact (RowSubgroup n la).mul_mem hp' ((RowSubgroup n la).inv_mem hp)
    have hqp_col : q'⁻¹ * q ∈ ColumnSubgroup n la :=
      (ColumnSubgroup n la).mul_mem ((ColumnSubgroup n la).inv_mem hq') hq
    exact hne (Subtype.ext (inv_mul_eq_one.mp
      (row_col_inter_trivial' n la _ hqp_row hqp_col)))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The coefficient of the identity permutation in the Young symmetrizer is 1. -/
private lemma youngSymmetrizer_one_coeff (n : ℕ) (la : Nat.Partition n) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) 1 = 1 := by
  have h := youngSymmetrizer_pq_coeff n la 1 (ColumnSubgroup n la).one_mem
    1 (RowSubgroup n la).one_mem
  simpa [Equiv.Perm.sign_one] using h

/-! ### Note on false group-algebra coefficient formulas

The following statements were previously conjectured here but are **false**
for the T-dependent polytabloid definition `e_T = κ_T · of(σ_T) · a_λ`:

* `polytabloid_apply`: claimed `e_T(σ) = (b_λ · a_λ)(σ_T⁻¹ · σ)`, but this
  requires `of(τ⁻¹) · b_λ · of(τ²) · a_λ = of(τ) · b_λ · a_λ`, which fails
  because conjugating b_λ by τ² does not give b_λ in general.

* `polytabloid_self_coeff`: claimed `e_T(σ_T) = 1`, but the actual formula
  gives `Σ_{p ∈ P_λ ∩ τ⁻² Q_λ τ²} sgn(p)`, which equals 0 for some SYTs
  (counterexample: n=6, λ=(3,3), T₂ = [0,1,4 / 2,3,5]).

The **correct** self-coefficient result is at the tabloid level:
`polytabloidTab_coeff_self` in `TabloidModule.lean` proves that the coefficient
of tabloid {T} in the tabloid-module polytabloid e_T is 1. This uses
`P_λ ∩ Q_λ = {1}` (which IS true), not `C_T ∩ τ P_λ τ⁻¹ = {1}` (which fails).

See GitHub issue #2161 for the full analysis and counterexample.
-/

/-- The coefficient of p ∈ P_λ in the Young symmetrizer equals 1. -/
private lemma youngSymmetrizer_rowPerm_coeff (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) p = 1 := by
  have h := youngSymmetrizer_pq_coeff n la 1 (ColumnSubgroup n la).one_mem p hp
  simpa [Equiv.Perm.sign_one] using h

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

/-- If e_{T₂}(σ) ≠ 0, then σ ∈ C_{T₂} · σ_{T₂} · P_λ: there exist π ��� C_{T₂}
(entry-level column stabilizer) and p ∈ P_λ such that σ = π · σ_{T₂} · p.

Equivalently, σ ∈ σ_{T₂}⁻¹ Q_λ σ_{T₂} · σ_{T₂} · P_λ (using C_T = σ_T⁻¹ Q_λ σ_T). -/
theorem polytabloid_support (n : ℕ) (la : Nat.Partition n)
    (T₂ : StandardYoungTableau n la) (σ : Equiv.Perm (Fin n))
    (hne : (polytabloid n la T₂ : SymGroupAlgebra n) σ ≠ 0) :
    ∃ p ∈ RowSubgroup n la, ∃ q ∈ ColumnSubgroup n la,
      σ = (sytPerm n la T₂)⁻¹ * q * sytPerm n la T₂ * sytPerm n la T₂ * p := by
  classical
  set τ := sytPerm n la T₂
  -- σ is in the support of the polytabloid
  have hmem : σ ∈ (polytabloid n la T₂ : SymGroupAlgebra n).support :=
    Finsupp.mem_support_iff.mpr hne
  -- polytabloid = (κ_T * of(τ)) * a_λ
  change σ ∈ (RelColumnAntisymmetrizer n la T₂ * MonoidAlgebra.of ℂ _ τ *
    RowSymmetrizer n la).support at hmem
  -- Support of product ⊆ support(left) * support(right)
  have h1 := MonoidAlgebra.support_mul
    (RelColumnAntisymmetrizer n la T₂ * MonoidAlgebra.of ℂ _ τ)
    (RowSymmetrizer n la) hmem
  rw [Finset.mem_mul] at h1
  obtain ⟨x, hx_mem, p', hp'_mem, hσ⟩ := h1
  -- p' is in the support of RowSymmetrizer, so p' ∈ P_λ
  have hp'_row : p' ∈ RowSubgroup n la := by
    simp only [RowSymmetrizer, MonoidAlgebra.of_apply] at hp'_mem
    rw [Finsupp.mem_support_iff] at hp'_mem
    rw [Finsupp.finset_sum_apply] at hp'_mem
    simp only [Finsupp.single_apply] at hp'_mem
    by_contra h_not
    apply hp'_mem
    apply Finset.sum_eq_zero
    intro ⟨r, hr⟩ _
    split_ifs with heq
    · exact absurd (heq ▸ hr) h_not
    · rfl
  -- x is in the support of κ_T * of(τ)
  have h2 := MonoidAlgebra.support_mul
    (RelColumnAntisymmetrizer n la T₂) (MonoidAlgebra.of ℂ _ τ) hx_mem
  rw [Finset.mem_mul] at h2
  obtain ⟨y, hy_mem, z, hz_mem, hx_eq⟩ := h2
  -- z is in the support of of(τ), so z = τ
  have hz_eq : z = τ := by
    simp only [MonoidAlgebra.of_apply] at hz_mem
    rwa [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hz_mem
  -- y is in the support of κ_T, so y = τ⁻¹ * q * τ for some q ∈ Q_λ
  have hy_col : ∃ q ∈ ColumnSubgroup n la, y = τ⁻¹ * q * τ := by
    simp only [RelColumnAntisymmetrizer, MonoidAlgebra.of_apply] at hy_mem
    rw [Finsupp.mem_support_iff] at hy_mem
    rw [Finsupp.finset_sum_apply] at hy_mem
    by_contra h_all
    push_neg at h_all
    apply hy_mem
    apply Finset.sum_eq_zero
    intro ⟨q, hq⟩ _
    change ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) •
      (Finsupp.single (τ⁻¹ * q * τ) (1 : ℂ))) y = 0
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have := h_all q hq
    split_ifs with heq
    · exact absurd heq.symm this
    · ring
  obtain ⟨q, hq, hy_eq⟩ := hy_col
  -- Assemble: σ = x * p' = (y * z) * p' = (τ⁻¹ * q * τ * τ) * p'
  refine ⟨p', hp'_row, q, hq, ?_⟩
  -- hσ : x * p' = σ, hx_eq : y * z = x
  rw [← hσ, ← hx_eq, hy_eq, hz_eq]

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in V_λ.

The tabloid-module version `polytabloidTab_linearIndependent` in `TabloidModule.lean`
is proved. This group-algebra version requires a transfer argument (constructing a
ℂ-linear map from ℂ[S_n] to M^λ sending polytabloids to tabloid-module polytabloids).
The previous proof attempt here used `polytabloid_self_coeff` which is false
(see issue #2161). -/
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
c_λ · of(p) = c_λ for p ∈ P_λ. With c = b·a, this follows from a·of(p) = a. -/
private theorem youngSymmetrizer_mul_of_row' (n : ℕ) (la : Nat.Partition n)
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
  -- sortedParts is descending: r₁ < r₂ ⟹ parts.getD r₁ 0 ≥ parts.getD r₂ 0
  have parts_descending : ∀ r₁ r₂ : ℕ, r₁ < r₂ → r₂ < parts.length →
      parts.getD r₂ 0 ≤ parts.getD r₁ 0 := by
    intro r₁ r₂ hr₁₂ hr₂
    have hsorted : parts.Pairwise (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)
    have hi : r₁ < parts.length := by omega
    rw [List.getD_eq_getElem (hn := hr₂), List.getD_eq_getElem (hn := hi)]
    exact List.pairwise_iff_get.mp hsorted ⟨r₁, hi⟩ ⟨r₂, hr₂⟩ hr₁₂
  have T_col_inc : ∀ c₁ c₂ : Cell n la,
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → T_fun c₁ < T_fun c₂ := by
    intro ⟨⟨r₁, col₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, col₂⟩, hr₂, hc₂⟩ hcol_eq hrow
    simp only at hcol_eq hrow; subst hcol_eq
    -- Strategy: construct col₁+1 distinct elements of rowEntries r₁ that are
    -- all < (rowEntries r₂).orderEmbOfFin(col₁). This forces the col₁-th smallest
    -- of rowEntries r₁ to be < (rowEntries r₂).orderEmbOfFin(col₁).
    set w₂ := parts.getD r₂ 0
    have hw₂ : (rowEntries r₂).card = w₂ := rowEnt_card r₂ hr₂
    -- For each i : Fin w₂, get the i-th smallest entry of B and its source position
    have b_mem : ∀ i : Fin w₂,
        (rowEntries r₂).orderEmbOfFin hw₂ i ∈ rowEntries r₂ :=
      fun i => Finset.orderEmbOfFin_mem _ hw₂ i
    have b_source : ∀ i : Fin w₂, ∃ qi : Fin n,
        qi ∈ rowPositions r₂ ∧ σ.symm qi = (rowEntries r₂).orderEmbOfFin hw₂ i :=
      fun i => Finset.mem_image.mp (b_mem i)
    let qi : Fin w₂ → Fin n := fun i => (b_source i).choose
    have qi_mem : ∀ i, (qi i) ∈ rowPositions r₂ := fun i => (b_source i).choose_spec.1
    have qi_val : ∀ i, σ.symm (qi i) = (rowEntries r₂).orderEmbOfFin hw₂ i :=
      fun i => (b_source i).choose_spec.2
    -- Column of qi(i) is valid for row r₁ (parts descending)
    have qi_col_lt : ∀ i, colOfPos parts (qi i).val < parts.getD r₁ 0 := by
      intro i
      have hq_row := (Finset.mem_filter.mp (qi_mem i)).2
      have := colOfPos_lt_getD parts (qi i).val (by rw [hps]; exact (qi i).isLt)
      rw [hq_row] at this
      exact Nat.lt_of_lt_of_le this (parts_descending r₁ r₂ hrow hr₂)
    -- For each i, get position in row r₁ at same column as qi(i)
    have pi_exists : ∀ i : Fin w₂, ∃ pi : Fin n,
        rowOfPos parts pi.val = r₁ ∧
        colOfPos parts pi.val = colOfPos parts (qi i).val := by
      intro i
      obtain ⟨k, hk, hrow_k, hcol_k⟩ := exists_pos_of_cell parts r₁
        (colOfPos parts (qi i).val) (qi_col_lt i)
      exact ⟨⟨k, by rw [← hps]; exact hk⟩, hrow_k, hcol_k⟩
    let pi : Fin w₂ → Fin n := fun i => (pi_exists i).choose
    have pi_row : ∀ i, rowOfPos parts (pi i).val = r₁ := fun i => (pi_exists i).choose_spec.1
    have pi_col : ∀ i, colOfPos parts (pi i).val = colOfPos parts (qi i).val :=
      fun i => (pi_exists i).choose_spec.2
    -- f(i) = σ.symm(pi i) is in rowEntries r₁ and < B.orderEmbOfFin(i)
    let f : Fin w₂ → Fin n := fun i => σ.symm (pi i)
    have hfA : ∀ i, f i ∈ rowEntries r₁ :=
      fun i => Finset.mem_image.mpr ⟨pi i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, pi_row i⟩, rfl⟩
    have hf_lt : ∀ i, f i < (rowEntries r₂).orderEmbOfFin hw₂ i := by
      intro i; rw [← qi_val i]
      have hqi_row : rowOfPos parts (qi i).val = r₂ := (Finset.mem_filter.mp (qi_mem i)).2
      exact hcs (pi i) (qi i)
        (pi_col i)
        (by rw [pi_row, hqi_row]; exact hrow)
    -- f is injective (different source positions in row r₁ → different entries under σ.symm)
    have hf_inj : Function.Injective f := by
      intro i₁ i₂ heq
      have hp_eq : pi i₁ = pi i₂ := σ.symm.injective heq
      have hcol_eq : colOfPos parts (qi i₁).val = colOfPos parts (qi i₂).val := by
        rw [← pi_col i₁, ← pi_col i₂]
        exact congrArg (colOfPos parts ·.val) hp_eq
      have hq_eq : qi i₁ = qi i₂ :=
        Fin.ext (rowOfPos_colOfPos_injective parts _ _
          (by rw [hps]; exact (qi i₁).isLt) (by rw [hps]; exact (qi i₂).isLt)
          ((Finset.mem_filter.mp (qi_mem i₁)).2.trans
            (Finset.mem_filter.mp (qi_mem i₂)).2.symm) hcol_eq)
      have := congrArg σ.symm hq_eq
      rw [qi_val, qi_val] at this
      exact ((rowEntries r₂).orderEmbOfFin hw₂).injective this
    -- Now: the image of f restricted to {0, ..., col₁} gives col₁+1 distinct elements
    -- of rowEntries r₁ that are all < B.orderEmbOfFin(col₁) (by monotonicity of orderEmbOfFin).
    -- Therefore the col₁-th smallest element of rowEntries r₁ is also < B.orderEmbOfFin(col₁).
    set β := (rowEntries r₂).orderEmbOfFin hw₂ ⟨col₁, by omega⟩ with β_def
    -- The col₁+1 elements f(0), ..., f(col₁) are distinct and all in rowEntries r₁
    -- and all < β (since f(i) < B.orderEmbOfFin(i) ≤ B.orderEmbOfFin(col₁) for i ≤ col₁)
    have f_lt_β : ∀ i : Fin w₂, i.val ≤ col₁ → f i < β := by
      intro i hi
      calc f i < (rowEntries r₂).orderEmbOfFin hw₂ i := hf_lt i
        _ ≤ β := ((rowEntries r₂).orderEmbOfFin hw₂).monotone (by omega)
    -- {a ∈ rowEntries r₁ | a < β} has ≥ col₁+1 elements (it contains f(0),...,f(col₁))
    have count_below : col₁ + 1 ≤ ((rowEntries r₁).filter (· < β)).card := by
      let S : Finset (Fin w₂) := Finset.univ.filter (fun i => i.val ≤ col₁)
      have hS_card : S.card = col₁ + 1 := by
        rw [show S = Finset.Iic (⟨col₁, by omega⟩ : Fin w₂) from by
          ext i; simp [S, Finset.mem_Iic, Fin.le_def]]
        exact Fin.card_Iic ⟨col₁, by omega⟩
      rw [← hS_card]
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hi
        exact Finset.mem_filter.mpr ⟨hfA i, f_lt_β i hi⟩
      · exact Set.InjOn.mono (Set.subset_univ _) hf_inj.injOn
    -- The col₁-th smallest of rowEntries r₁ must be < β
    -- Proof: orderEmbOfFin(col₁) ≤ max of the first col₁+1 sorted elements = orderEmbOfFin(col₁)
    -- So we need: if |{a ∈ A | a < v}| ≥ col₁+1, then A.orderEmbOfFin(col₁) < v
    -- This is a counting argument about orderEmbOfFin.
    by_contra hge; push_neg at hge
    -- hge : β ≤ T_fun(r₁, col₁) = (rowEntries r₁).orderEmbOfFin(col₁)
    have hge' : β ≤ (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁) ⟨col₁, by omega⟩ := hge
    -- Elements of rowEntries r₁ below β are below orderEmbOfFin(col₁),
    -- so they're among orderEmbOfFin(0), ..., orderEmbOfFin(col₁-1): at most col₁ elements
    have filter_le : ((rowEntries r₁).filter (· < β)).card ≤ col₁ := by
      have sub : (rowEntries r₁).filter (· < β) ⊆
          (rowEntries r₁).filter (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)
            ⟨col₁, by omega⟩) :=
        Finset.monotone_filter_right _ (fun a _ ha => lt_of_lt_of_le ha hge')
      have sub2 : (rowEntries r₁).filter
          (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁) ⟨col₁, by omega⟩) ⊆
          (Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).image
            ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)) := by
        intro a ha
        rw [Finset.mem_filter] at ha
        have ⟨ha_mem, ha_lt⟩ := ha
        have ha_range : a ∈ Set.range ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)) := by
          rw [Finset.range_orderEmbOfFin]; exact ha_mem
        obtain ⟨j, rfl⟩ := ha_range
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr
          (((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).lt_iff_lt.mp ha_lt), rfl⟩
      calc ((rowEntries r₁).filter (· < β)).card
          ≤ ((rowEntries r₁).filter
              (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)
                ⟨col₁, by omega⟩)).card := Finset.card_le_card sub
        _ ≤ ((Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).image
              ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁))).card :=
            Finset.card_le_card sub2
        _ ≤ (Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).card :=
            Finset.card_image_le
        _ = col₁ := @Fin.card_Iio (parts.getD r₁ 0) ⟨col₁, by omega⟩
    omega
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

**Status**: This section proves `a_λ · G = 0` (the Garnir annihilation identity).
This result is mathematically correct and potentially useful for tabloid-level
straightening. However, the original plan to use it for group-algebra-level
straightening (steps 4-5 below) is **flawed**: by Lemma 5.13.1,
`a_λ · of(w) · b_λ = ℓ(of(w)) · c_λ`, so the Garnir expansion at the group
algebra level collapses to a scalar multiple of `of(σ) · c_λ` — a tautology.
The Garnir expansion only produces non-trivial reductions at the **tabloid
module** level, where the sandwich property does not apply. See issue #2104.

The Garnir reduction uses the following strategy:
1. Find a column inversion: positions p₁ (row r₁) and p₂ (row r₂) in column j
   with r₁ < r₂ and σ⁻¹(p₂) < σ⁻¹(p₁).
2. Define the Garnir set: A = positions in row r₁ with column ≥ j,
   B = positions in row r₂ with column ≤ j. Note |A| + |B| = (λ_{r₁} - j) + (j + 1) = λ_{r₁} + 1.
3. The Garnir element G = Σ_{w ∈ S_{A∪B}} sign(w) · w satisfies a_λ · G = 0 because
   P_λ ∩ S_{A∪B} contains a transposition t, and a_λ · t = a_λ while t · G = -G,
   giving a_λ · G = a_λ · t · G = -a_λ · G, hence 2 · a_λ · G = 0, so a_λ · G = 0
   (in characteristic 0).
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
(or p₂ and another in row(p₂)) when the corresponding row has width ≥ 2.

Note: the hypothesis `hwidth` excludes single-column partitions where
the Garnir set has only one element per row. Single-column partitions
need separate handling in the straightening algorithm. -/
private theorem garnirSet_has_row_pair (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (_hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hwidth : 1 < la.sortedParts.getD (rowOfPos la.sortedParts p₁.val) 0) :
    ∃ a b : Fin n, a ≠ b ∧ a ∈ garnirSet n la p₁ p₂ ∧ b ∈ garnirSet n la p₁ p₂ ∧
      rowOfPos la.sortedParts a.val = rowOfPos la.sortedParts b.val := by
  set parts := la.sortedParts with hparts_def
  set r₁ := rowOfPos parts p₁.val with hr₁_def
  set r₂ := rowOfPos parts p₂.val with hr₂_def
  set j := colOfPos parts p₁.val with hj_def
  -- p₁ is a valid position, so j < width(r₁), and p₂ gives j < width(r₂)
  have hn_pos : 0 < n := Fin.pos p₁
  have hp₁_valid : p₁.val < parts.sum := by
    rw [hparts_def, sortedParts_sum]; exact p₁.isLt
  have hp₂_valid : p₂.val < parts.sum := by
    rw [hparts_def, sortedParts_sum]; exact p₂.isLt
  have hj_lt_r₁ : j < parts.getD r₁ 0 := colOfPos_lt_getD parts p₁.val hp₁_valid
  have hj_lt_r₂ : j < parts.getD r₂ 0 := by
    have := colOfPos_lt_getD parts p₂.val hp₂_valid
    rwa [← hcol] at this
  -- Case split: j ≥ 1 (use row r₂) or j = 0 (use row r₁)
  by_cases hj_pos : 0 < j
  · -- Case j ≥ 1: row r₂ has positions at columns 0 and 1, both ≤ j
    -- Get position at (r₂, 0)
    have h0_lt : 0 < parts.getD r₂ 0 := by omega
    obtain ⟨k₀, hk₀_sum, hk₀_row, hk₀_col⟩ := exists_pos_of_cell parts r₂ 0 h0_lt
    -- Get position at (r₂, 1)
    have h1_lt : 1 < parts.getD r₂ 0 := by omega
    obtain ⟨k₁, hk₁_sum, hk₁_row, hk₁_col⟩ := exists_pos_of_cell parts r₂ 1 h1_lt
    -- They're distinct (different columns)
    have hne : k₀ ≠ k₁ := by
      intro heq; rw [heq] at hk₀_col; rw [hk₀_col] at hk₁_col; omega
    -- Convert to Fin n
    rw [hparts_def, sortedParts_sum n la] at hk₀_sum hk₁_sum
    refine ⟨⟨k₀, hk₀_sum⟩, ⟨k₁, hk₁_sum⟩, fun h => hne (congrArg Fin.val h), ?_, ?_, ?_⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      right; exact ⟨hk₀_row, by rw [hk₀_col]; omega⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      right; exact ⟨hk₁_row, by rw [hk₁_col]; omega⟩
    · rw [show (⟨k₀, hk₀_sum⟩ : Fin n).val = k₀ from rfl,
          show (⟨k₁, hk₁_sum⟩ : Fin n).val = k₁ from rfl, hk₀_row, hk₁_row]
  · -- Case j = 0: row r₁ has width ≥ 2, positions at cols 0 and 1, both ≥ j = 0
    push_neg at hj_pos
    have hj_eq : j = 0 := Nat.le_zero.mp hj_pos
    -- Get position at (r₁, 0)
    have h0_lt : 0 < parts.getD r₁ 0 := by omega
    obtain ⟨k₀, hk₀_sum, hk₀_row, hk₀_col⟩ := exists_pos_of_cell parts r₁ 0 h0_lt
    -- Get position at (r₁, 1)
    obtain ⟨k₁, hk₁_sum, hk₁_row, hk₁_col⟩ := exists_pos_of_cell parts r₁ 1 hwidth
    -- They're distinct
    have hne : k₀ ≠ k₁ := by
      intro heq; rw [heq] at hk₀_col; rw [hk₀_col] at hk₁_col; omega
    rw [hparts_def, sortedParts_sum n la] at hk₀_sum hk₁_sum
    refine ⟨⟨k₀, hk₀_sum⟩, ⟨k₁, hk₁_sum⟩, fun h => hne (congrArg Fin.val h), ?_, ?_, ?_⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      left; exact ⟨hk₀_row, by rw [← hj_def, hk₀_col, hj_eq]⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      left; exact ⟨hk₁_row, by rw [← hj_def, hj_eq]; omega⟩
    · rw [show (⟨k₀, hk₀_sum⟩ : Fin n).val = k₀ from rfl,
          show (⟨k₁, hk₁_sum⟩ : Fin n).val = k₁ from rfl, hk₀_row, hk₁_row]

/-- Left multiplication by a transposition t ∈ S_{A∪B} negates the Garnir element:
of(t) * G = -G. This is a standard property of alternating sums. -/
private theorem left_transposition_negates_garnir (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) (t : Equiv.Perm (Fin n))
    (ht_supp : ∀ x, x ∉ garnirSet n la p₁ p₂ → t x = x)
    (ht_sign : Equiv.Perm.sign t = -1) :
    MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂ =
      -garnirElement n la p₁ p₂ := by
  simp only [garnirElement]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp_rw [Algebra.mul_smul_comm, ← map_mul (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)))]
  -- Goal: ∑ w, (↑↑(sign w.val) : ℂ) • of(t * w.val) =
  --       ∑ w, -((↑↑(sign w.val) : ℂ) • of(w.val))
  set S := garnirSet n la p₁ p₂ with hS_def
  have ht_inv_supp : ∀ x, x ∉ S → t⁻¹ x = x := fun x hx => by
    calc t⁻¹ x = t⁻¹ (t x) := by rw [ht_supp x hx]
      _ = x := Equiv.symm_apply_apply t x
  set P := fun w : Equiv.Perm (Fin n) => ∀ x, x ∉ S → w x = x
  have hmul_mem : ∀ (w : Equiv.Perm (Fin n)), P w → P (t * w) := fun w hw x hx => by
    change t (w x) = x; rw [hw x hx, ht_supp x hx]
  have hinv_mem : ∀ (w : Equiv.Perm (Fin n)), P w → P (t⁻¹ * w) := fun w hw x hx => by
    change t⁻¹ (w x) = x; rw [hw x hx, ht_inv_supp x hx]
  -- Reindex LHS sum via bijection w ↦ t * w
  refine Fintype.sum_equiv
    ⟨fun ⟨w, hw⟩ => ⟨t * w, hmul_mem w hw⟩,
     fun ⟨w, hw⟩ => ⟨t⁻¹ * w, hinv_mem w hw⟩,
     fun ⟨w, _⟩ => Subtype.ext (show t⁻¹ * (t * w) = w by group),
     fun ⟨w, _⟩ => Subtype.ext (show t * (t⁻¹ * w) = w by group)⟩
    _ _ (fun ⟨w, hw⟩ => ?_)
  -- Term matching: sign(w) • of(t * w) = -(sign(t * w) • of(t * w))
  -- Since sign(t * w) = sign(t) * sign(w) = -1 * sign(w), we get
  -- -((-1 * sign(w)) • of(t*w)) = sign(w) • of(t*w)
  -- The equiv maps ⟨w,hw⟩ to ⟨t*w, ...⟩, so we need:
  -- sign(w) • of(t * w) = -(sign(t * w) • of(t * w))
  change (↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ (t * w) =
    -((↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ (t * w))
  have hsm : (↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) =
      -(↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) := by
    have h1 : Equiv.Perm.sign (t * w) = Equiv.Perm.sign t * Equiv.Perm.sign w := map_mul _ _ _
    rw [h1, ht_sign]
    simp only [Units.val_mul, Int.cast_mul]
    have : (↑(-1 : ℤˣ) : ℤ) = -1 := rfl
    rw [this, Int.cast_neg, Int.cast_one, neg_one_mul]
  rw [hsm, neg_smul, neg_neg]

private theorem garnir_row_annihilates (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hwidth : 1 < la.sortedParts.getD (rowOfPos la.sortedParts p₁.val) 0) :
    RowSymmetrizer n la * garnirElement n la p₁ p₂ = 0 := by
  -- Step 1: Find a transposition t in P_λ ∩ S_{A∪B}
  obtain ⟨a, b, hab, ha_mem, hb_mem, hrow_eq⟩ :=
    garnirSet_has_row_pair n la p₁ p₂ hcol hrow hwidth
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

/-- swap(p₁, p₂) belongs to the column subgroup when p₁ and p₂ are in the same column. -/
private theorem swap_mem_ColumnSubgroup' (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val) :
    Equiv.swap p₁ p₂ ∈ ColumnSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hcol.symm
  · subst h2; exact hcol
  · rfl

/-- Left multiplication by a column subgroup element on the Young symmetrizer:
of(q) * c_λ = sign(q) • c_λ for q ∈ Q_λ. With c = b·a, this follows from of(q)·b = sign(q)·b. -/
private theorem of_col_mul_YoungSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) :
    MonoidAlgebra.of ℂ _ q * YoungSymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • YoungSymmetrizer n la := by
  change MonoidAlgebra.of ℂ _ q * (ColumnAntisymmetrizer n la * RowSymmetrizer n la) =
    _ • (ColumnAntisymmetrizer n la * RowSymmetrizer n la)
  rw [← mul_assoc, of_col_mul_ColumnAntisymmetrizer q hq, Algebra.smul_mul_assoc]

/-- Key algebraic identity: for p₁, p₂ in the same column,
of(σ) · c_λ = -(of(σ · swap(p₁,p₂)) · c_λ).
This follows from swap(p₁,p₂) ∈ Q_λ and the left column absorption property. -/
private theorem garnir_swap_identity (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hne : p₁ ≠ p₂) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la =
      (-1 : ℂ) • (MonoidAlgebra.of ℂ _ (σ * Equiv.swap p₁ p₂) *
        YoungSymmetrizer n la) := by
  have hswap_col := swap_mem_ColumnSubgroup' n la p₁ p₂ hcol
  have h1 : MonoidAlgebra.of ℂ _ (Equiv.swap p₁ p₂) * YoungSymmetrizer n la =
      (-1 : ℂ) • YoungSymmetrizer n la := by
    rw [of_col_mul_YoungSymmetrizer n la _ hswap_col, Equiv.Perm.sign_swap hne]
    simp [Int.cast_neg, Int.cast_one]
  have key : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ *
      (MonoidAlgebra.of ℂ _ (Equiv.swap p₁ p₂) * YoungSymmetrizer n la) =
      MonoidAlgebra.of ℂ _ (σ * Equiv.swap p₁ p₂) * YoungSymmetrizer n la := by
    rw [← mul_assoc, ← map_mul]
  rw [h1, Algebra.mul_smul_comm] at key
  -- key : (-1) • (of(σ) * c) = of(σ * swap) * c
  -- goal : of(σ) * c = (-1) • (of(σ * swap) * c)
  rw [← key, smul_smul]; norm_num

/-- The column inversion count is positive when there exists an inversion. -/
private theorem columnInvCount'_pos_of_inv (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hinv : σ.symm p₂ < σ.symm p₁) :
    0 < columnInvCount' n la σ := by
  unfold columnInvCount'
  apply Finset.card_pos.mpr
  exact ⟨(p₁, p₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol, hrow, hinv⟩⟩

/-- For a single-column partition (all parts = 1), of(σ) * c_λ = sign(σ) • c_λ.
This gives a trivial Garnir expansion with S = {1}. -/
private theorem single_column_garnir (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (h_single : ∀ i, i < la.sortedParts.length → la.sortedParts.getD i 0 = 1) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) •
        (MonoidAlgebra.of ℂ _ (1 : Equiv.Perm (Fin n)) * YoungSymmetrizer n la) := by
  -- For single-column, every σ ∈ Q_λ (all positions in col 0)
  have hσ_col : σ ∈ ColumnSubgroup n la := by
    intro k
    have hk := k.isLt
    have hsum : la.sortedParts.sum = n := sortedParts_sum n la
    have hksum : k.val < la.sortedParts.sum := by omega
    -- Both σ k and k have colOfPos = 0 when all rows have width 1
    have hk_col : colOfPos la.sortedParts k.val = 0 := by
      have hrow := rowOfPos_lt_length la.sortedParts k.val hksum
      have hw := h_single _ hrow
      have hcol := colOfPos_lt_getD la.sortedParts k.val hksum
      rw [hw] at hcol; omega
    have hσk_col : colOfPos la.sortedParts (σ k).val = 0 := by
      have hσk := (σ k).isLt
      have hσksum : (σ k).val < la.sortedParts.sum := by omega
      have hrow := rowOfPos_lt_length la.sortedParts (σ k).val hσksum
      have hw := h_single _ hrow
      have hcol := colOfPos_lt_getD la.sortedParts (σ k).val hσksum
      rw [hw] at hcol; omega
    rw [hk_col, hσk_col]
  -- For single-column, RowSubgroup = {1} (each row has width 1)
  have h_row_trivial : ∀ (p : Equiv.Perm (Fin n)), p ∈ RowSubgroup n la → p = 1 := by
    intro p hp; ext k : 1; simp only [Equiv.Perm.one_apply]
    have hk_lt : k.val < la.sortedParts.sum := by rw [sortedParts_sum]; exact k.isLt
    have hpk_lt : (p k).val < la.sortedParts.sum := by rw [sortedParts_sum]; exact (p k).isLt
    have hcol_k : colOfPos la.sortedParts k.val = 0 := by
      have hcol := colOfPos_lt_getD la.sortedParts k.val hk_lt
      rw [h_single _ (rowOfPos_lt_length la.sortedParts k.val hk_lt)] at hcol; omega
    have hcol_pk : colOfPos la.sortedParts (p k).val = 0 := by
      have hcol := colOfPos_lt_getD la.sortedParts (p k).val hpk_lt
      rw [h_single _ (rowOfPos_lt_length la.sortedParts (p k).val hpk_lt)] at hcol; omega
    exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts (p k).val k.val
      hpk_lt hk_lt (hp k) (by rw [hcol_pk, hcol_k]))
  -- Therefore YoungSymmetrizer = RowSymmetrizer * ColAnti = of(1) * ColAnti = ColAnti
  -- and of(σ) * YoungSymmetrizer = of(σ) * ColAnti = sign(σ) • ColAnti = sign(σ) • YoungSymmetrizer
  have h_unique : Unique (↥(RowSubgroup n la)) :=
    ⟨⟨⟨1, (RowSubgroup n la).one_mem⟩⟩, fun g => Subtype.ext (h_row_trivial g.val g.prop)⟩
  have h_rowSym_eq : RowSymmetrizer n la = MonoidAlgebra.of ℂ _ (1 : Equiv.Perm (Fin n)) := by
    have hval : ∀ g : ↥(RowSubgroup n la), (g : Equiv.Perm (Fin n)) = 1 :=
      fun g => h_row_trivial g.val g.prop
    simp only [RowSymmetrizer, hval, Finset.sum_const, Finset.card_univ]
    haveI := h_unique
    simp [Fintype.card_unique]
  have h_of_one : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n)) = 1 :=
    map_one _
  rw [YoungSymmetrizer]
  simp only [h_rowSym_eq, h_of_one, mul_one, one_mul]
  exact of_col_mul_ColumnAntisymmetrizer σ hσ_col

/-- rowOfPos is monotone: a ≤ b implies rowOfPos a ≤ rowOfPos b. -/
private theorem rowOfPos_mono (parts : List ℕ) (a b : ℕ)
    (hb : b < parts.sum)
    (hab : a ≤ b) : rowOfPos parts a ≤ rowOfPos parts b := by
  induction parts generalizing a b with
  | nil => simp [List.sum_nil] at hb
  | cons p ps ih =>
    simp only [rowOfPos]
    split_ifs with ha hb
    · omega
    · omega
    · exfalso; simp [List.sum_cons] at hb; omega
    · have hb' : b - p < ps.sum := by simp [List.sum_cons] at hb; omega
      have hab' : a - p ≤ b - p := Nat.sub_le_sub_right hab p
      have := ih (a - p) (b - p) hb' hab'
      omega

/-- For the identity permutation, positions in canonical order have no column inversions:
if rowOfPos(a) < rowOfPos(b), then a < b. -/
private theorem rowOfPos_eq_length (parts : List ℕ) (a : ℕ) (ha : parts.sum ≤ a) :
    rowOfPos parts a = parts.length := by
  induction parts generalizing a with
  | nil => simp [rowOfPos]
  | cons p ps ih =>
    simp only [rowOfPos, List.length_cons]
    have : ¬(a < p) := by simp [List.sum_cons] at ha; omega
    rw [if_neg this]
    have : ps.sum ≤ a - p := by simp [List.sum_cons] at ha; omega
    rw [ih _ this]; omega

private theorem lt_of_lt_rowOfPos (parts : List ℕ) (a b : ℕ)
    (hb : b < parts.sum)
    (hrow : rowOfPos parts a < rowOfPos parts b) : a < b := by
  by_contra h
  push_neg at h
  -- a ≥ b. Two cases: a < parts.sum or a ≥ parts.sum
  by_cases ha : a < parts.sum
  · have := rowOfPos_mono parts b a ha h
    omega
  · push_neg at ha
    have := rowOfPos_eq_length parts a ha
    have := rowOfPos_lt_length parts b hb
    omega

/-- columnInvCount' for the identity permutation is 0. -/
private theorem columnInvCount'_one (n : ℕ) (la : Nat.Partition n) :
    columnInvCount' n la 1 = 0 := by
  unfold columnInvCount'
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro ⟨a, b⟩ _
  simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply, not_and]
  intro _ hrow
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  have hb : b.val < la.sortedParts.sum := by omega
  exact Nat.not_lt.mpr (Nat.le_of_lt (lt_of_lt_rowOfPos la.sortedParts a.val b.val hb hrow))

/-- **Straightening lemma**: any permutation applied to the Young symmetrizer
lies in the ℂ-span of standard polytabloids.

**Proof approach (revised)**: The original Garnir-based induction claimed
pointwise decrease of `columnInvCount'` under Garnir expansion. This is
FALSE: counterexample on partition (2,2) shows a Garnir coset representative
that preserves the column inversion count (see issue #2104).

Moreover, the Garnir identity `a_λ * G = 0`, when applied at the group
algebra level, yields a tautology via Lemma 5.13.1: each term
`of(σ) * a_λ * of(w) * b_λ = ℓ(of(w)) • of(σ) * c_λ`, so the expansion
collapses to `of(σ) * c_λ = -K • of(σ) * c_λ` with K = -1. The Garnir
expansion only produces non-trivial reductions at the **tabloid module**
level, where the sandwich property does not apply.

The correct approach requires one of:
1. **Tabloid-level straightening**: prove the straightening in M^λ using
   tabloid dominance order, then transfer to V_λ via the tabloid projection
   map (which is injective by irreducibility of V_λ, Theorem 5.12.2).
2. **Dimension argument**: show dim V_λ = |SYT(λ)| via the hook length
   formula or representation-theoretic dimension counting.

Both approaches require significant infrastructure not yet in this file. -/
theorem perm_mul_youngSymmetrizer_mem_span_polytabloids (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ _ σ * YoungSymmetrizer n la ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        (polytabloidInSpecht n la T : SymGroupAlgebra n))) := by
  sorry

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
