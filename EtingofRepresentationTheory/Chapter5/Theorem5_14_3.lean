import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_14_1

/-!
# Theorem 5.14.3: Character Formula via Power Sums

The character of the permutation module U_λ evaluated at conjugacy class C_i
(where i = (i₁, i₂, ...) is the cycle type) is given by:

  χ_{U_λ}(C_i) = coefficient of x^λ in ∏_{m≥1} p_m(x)^{i_m}

where p_m(x) = Σᵢ xᵢᵐ is the power sum symmetric polynomial.

## Formalization approach

The character of the permutation module U_λ = ℂ[S_n/S_λ] at σ is the number
of cosets gS_λ fixed by σ (since U_λ is a permutation representation, the
character equals the number of fixed points).

A coset gS_λ is fixed by σ iff each cycle of σ lies entirely within one row
of the partition λ (under the relabeling given by g). This "monochromatic"
condition is captured exactly by the power sum polynomial p_m = Σᵢ xᵢᵐ,
where each term xᵢᵐ represents placing an entire m-cycle into row i.

**Note**: An earlier version of this file incorrectly used `MvPolynomial.hsymm`
(complete homogeneous symmetric polynomials). The hsymm polynomial
H_m = Σ_{|α|=m} x^α allows distributing m elements across multiple rows,
but cycles must go to a single row. The power sum p_m = Σᵢ xᵢᵐ correctly
enforces this constraint.

## Mathlib correspondence

- `MvPolynomial.psum`: power sum symmetric polynomials p_m = Σᵢ xᵢᵐ
- `Equiv.Perm.cycleType`: cycle type as multiset (excluding fixed points)
- `MvPolynomial.coeff`: coefficient extraction
- `MulAction.fixedBy`: fixed points of a group element
-/

namespace Etingof

/-- Convert a partition's sorted parts to a finsupp for MvPolynomial coefficient extraction.
Position i maps to the i-th largest part (or 0 if i ≥ number of parts).
This encodes x^λ = x_0^{λ_1} · x_1^{λ_2} · ... -/
noncomputable def Nat.Partition.toFinsupp {n : ℕ} (la : Nat.Partition n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => la.sortedParts.getD i 0)

/-- The character of the permutation module U_λ at a permutation σ, defined as the number
of left cosets gS_λ fixed by left multiplication by σ. For permutation representations,
this equals the trace of the representation matrix. -/
noncomputable def permModuleCharacter (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  Nat.card (MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) σ)

/-- The product ∏_{m≥1} p_m(x)^{i_m} where i = (i₁, i₂, ...) counts cycles of each length
in σ (including fixed points as 1-cycles). The power sum polynomial p_m = Σᵢ xᵢᵐ ensures
each cycle is assigned to a single row, which is the correct generating function for
permutation module characters.

**Previous version used hsymm (H_m), which is incorrect**: H_m allows distributing m
elements across rows, but each cycle must go entirely to one row. -/
noncomputable def cycleTypePsumProduct (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) ℂ :=
  (σ.cycleType.map (MvPolynomial.psum (Fin n) ℂ)).prod *
    MvPolynomial.psum (Fin n) ℂ 1 ^ (n - σ.support.card)

/-! ## Helper infrastructure for Theorem 5.14.3

### Key types and constructions

The proof proceeds by showing both sides count "monochromatic colorings":
an assignment of each orbit of σ (cycles + fixed points) to a row of λ,
such that the total number of elements assigned to row j equals λ_j.

**LHS path**: A coset gS_λ is fixed by σ iff g⁻¹σg ∈ S_λ, i.e., σ preserves
each row under g's relabeling. This is equivalent to a monochromatic coloring.

**RHS path**: The product ∏ p_{|c|}(x) = ∏ (Σᵢ xᵢ^{|c|}) expands as a sum
over assignments of cycles to rows. The coefficient of x^λ counts assignments
with correct row sizes.
-/

/-- The "full cycle type" of σ, including fixed points as 1-cycles.
This is σ.cycleType (which only lists cycles of length ≥ 2) plus
(n - σ.support.card) copies of 1 (for fixed points). -/
noncomputable def fullCycleType (n : ℕ) (σ : Equiv.Perm (Fin n)) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (n - σ.support.card) 1

/-- The sum of the full cycle type equals n. -/
theorem fullCycleType_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fullCycleType n σ).sum = n := by
  simp only [fullCycleType, Multiset.sum_add, Multiset.sum_replicate]
  have h1 := σ.sum_cycleType
  have h2 : σ.support.card ≤ n :=
    (σ.support.card_le_univ).trans_eq (Fintype.card_fin n)
  -- Goal should be: σ.cycleType.sum + (n - σ.support.card) • 1 = n
  simp only [smul_eq_mul, mul_one] at *
  omega

/-- A monochromatic coloring: an assignment of each orbit (indexed by position in the
full cycle type multiset) to a row (indexed by Fin n), such that the total size of
orbits assigned to row j equals λ_j. -/
noncomputable def MonochromaticColoring (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin n //
    ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) =
      la.sortedParts.getD j 0 }

/-- The cycleTypePsumProduct can be rewritten using the full cycle type. -/
theorem cycleTypePsumProduct_eq_fullCycleType (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cycleTypePsumProduct n σ =
      ((fullCycleType n σ).map (MvPolynomial.psum (Fin n) ℂ)).prod := by
  unfold cycleTypePsumProduct fullCycleType
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]

/-- Each psum polynomial equals a sum of monomials: p_m = ∑ i, monomial (single i m) 1. -/
theorem psum_eq_sum_monomial (m : ℕ) :
    MvPolynomial.psum (Fin n) ℂ m = ∑ i : Fin n, MvPolynomial.monomial (Finsupp.single i m) 1 := by
  simp only [MvPolynomial.psum, MvPolynomial.X_pow_eq_monomial]

/-- The coefficient of x^λ in a product of psum polynomials equals the number of
monochromatic colorings. This is the polynomial side of the bijection. -/
-- Helper: the finsupp sum condition is equivalent to the pointwise condition
private lemma finsupp_sum_single_iff (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin n) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) =
      Nat.Partition.toFinsupp la) ↔
    (∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) =
      la.sortedParts.getD j 0) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
      Nat.Partition.toFinsupp, Finsupp.coe_equivFunOnFinite_symm] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
      Nat.Partition.toFinsupp, Finsupp.coe_equivFunOnFinite_symm]
    rw [← Finset.sum_filter]
    exact hall j

theorem coeff_psum_prod_eq_card_colorings (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypePsumProduct n σ) =
      Nat.card (MonochromaticColoring n la σ) := by
  rw [cycleTypePsumProduct_eq_fullCycleType]
  -- Convert multiset product to list product to Fin-indexed product
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  -- Expand each psum as a sum of monomials, distribute, collapse to single monomial
  simp_rw [psum_eq_sum_monomial]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  -- Extract coefficients
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  -- Goal: ↑(filter card) = ↑(Nat.card MonochromaticColoring)
  norm_cast
  -- Construct equiv between MonochromaticColoring and the filter
  have equiv : MonochromaticColoring n la σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[↑i])) =
          Nat.Partition.toFinsupp la } := by
    unfold MonochromaticColoring
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff n la σ f).symm)
  rw [Nat.card_congr equiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  congr

/-! ## Helper infrastructure for fixedCosets_eq_card_colorings

The proof proceeds through an intermediate type of σ-invariant row colorings:
1. Fixed cosets biject with σ-invariant colorings (via coset representatives)
2. σ-invariant colorings biject with MonochromaticColorings (via orbit decomposition)
-/

noncomputable section fixedCosets_helpers

open scoped Classical
open Finset

/-- Construct a fiber-matching bijection: given two functions with the same fiber
cardinalities, build a bijection that maps fibers to corresponding fibers. -/
private def fiberMatchEquiv' {N : ℕ} {T : Type*} [DecidableEq T]
    (p₁ p₂ : Fin N → T)
    (h : ∀ t : T, (univ.filter (fun k => p₁ k = t)).card =
                   (univ.filter (fun k => p₂ k = t)).card) :
    Fin N ≃ Fin N :=
  (Equiv.sigmaFiberEquiv p₁).symm.trans
    ((Equiv.sigmaCongrRight (fun t =>
      Fintype.equivOfCardEq (by simp only [Fintype.card_subtype]; exact h t))).trans
    (Equiv.sigmaFiberEquiv p₂))

private lemma fiberMatchEquiv'_spec {N : ℕ} {T : Type*} [DecidableEq T]
    (p₁ p₂ : Fin N → T) (h) (m : Fin N) :
    p₂ (fiberMatchEquiv' p₁ p₂ h m) = p₁ m := by
  simp only [fiberMatchEquiv', Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  exact ((Fintype.equivOfCardEq _ ((Equiv.sigmaFiberEquiv p₁).symm m).snd) :
    {k // p₂ k = ((Equiv.sigmaFiberEquiv p₁).symm m).fst}).prop

/-- The "row of position" function, mapping each Fin n to its row in the Young diagram,
viewed as a natural number. This is the same as `rowOfPos` applied to the sorted parts. -/
private abbrev rowFun (la : Nat.Partition n) (k : Fin n) : ℕ :=
  rowOfPos la.sortedParts k.val

/-- rowOfPos returns a value less than the list length when the position is valid. -/
private lemma rowOfPos_lt_length (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    rowOfPos parts k < parts.length := by
  induction parts generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    simp only [rowOfPos]; split
    · simp
    · next h =>
      push_neg at h
      have := ih (k - p) (by simp [List.sum_cons] at hk; omega)
      simp; omega

/-- The sorted parts of a partition sum to n. -/
private lemma sortedParts_sum (n : ℕ) (la : Nat.Partition n) : la.sortedParts.sum = n := by
  unfold Nat.Partition.sortedParts
  have h : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
  calc (la.parts.sort (· ≥ ·)).sum
      = (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ).sum := by rw [Multiset.sum_coe]
    _ = la.parts.sum := by rw [h]
    _ = n := la.parts_sum

/-- All parts of a partition are positive. -/
private lemma sortedParts_pos (n : ℕ) (la : Nat.Partition n) :
    ∀ x ∈ la.sortedParts, 1 ≤ x := by
  intro x hx; unfold Nat.Partition.sortedParts at hx
  have h : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
  exact Nat.Partition.parts_pos la (by rw [← h]; exact hx)

/-- A list of positive numbers has length at most its sum. -/
private lemma list_length_le_sum_of_pos (l : List ℕ) (h : ∀ x ∈ l, 1 ≤ x) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [List.sum_cons]
    have := h a (List.mem_cons.mpr (Or.inl rfl))
    have := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    omega

/-- The number of parts is at most n. -/
private lemma sortedParts_length_le (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.length ≤ n :=
  calc la.sortedParts.length
      ≤ la.sortedParts.sum := list_length_le_sum_of_pos _ (sortedParts_pos n la)
    _ = n := sortedParts_sum n la

/-- rowFun returns a value less than n. -/
private lemma rowFun_lt (la : Nat.Partition n) (k : Fin n) : rowFun la k < n := by
  calc rowFun la k
      < la.sortedParts.length := rowOfPos_lt_length _ _ (by rw [sortedParts_sum]; exact k.isLt)
    _ ≤ n := sortedParts_length_le n la

/-- rowOfPos (p :: ps) k = 0 iff k < p. -/
private lemma rowOfPos_cons_eq_zero (p : ℕ) (ps : List ℕ) (k : ℕ) :
    rowOfPos (p :: ps) k = 0 ↔ k < p := by
  simp [rowOfPos]

/-- Counting elements less than p in Fin (p + q). -/
private lemma card_filter_lt (p q : ℕ) :
    (univ.filter (fun k : Fin (p + q) => k.val < p)).card = p := by
  trans (Finset.univ : Finset (Fin p)).card
  · apply Finset.card_bij (fun k _ => ⟨k.val, by
      simp only [mem_filter, mem_univ, true_and] at *; assumption⟩)
    · intro k _; exact mem_univ _
    · intro a _ b _ h; ext; exact Fin.mk.inj h
    · intro k _; exact ⟨⟨k.val, by omega⟩, by simp [mem_filter, k.isLt], by ext; simp⟩
  · exact Fintype.card_fin p

/-- Shifting filter indices by p. -/
private lemma card_filter_shift (p q : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (univ.filter (fun k : Fin (p + q) => ¬(k.val < p) ∧ f (k.val - p) = j)).card =
    (univ.filter (fun k : Fin q => f k.val = j)).card := by
  set S := univ.filter (fun k : Fin (p + q) => ¬(k.val < p) ∧ f (k.val - p) = j)
  set T := univ.filter (fun k : Fin q => f k.val = j)
  apply Finset.card_bij (fun k _ => (⟨k.val - p, by
    have := k.isLt; have hk := (mem_filter.mp ‹k ∈ S›).2.1; omega⟩ : Fin q))
  · intro k hk; simp only [S, mem_filter, mem_univ, true_and] at hk
    simp only [T, mem_filter, mem_univ, true_and]; exact hk.2
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [S, mem_filter, mem_univ, true_and] at hk₁ hk₂
    simp only [Fin.mk.injEq] at heq; ext; omega
  · intro k hk; simp only [T, mem_filter, mem_univ, true_and] at hk
    refine ⟨⟨k.val + p, by omega⟩, ?_, ?_⟩
    · simp only [S, mem_filter, mem_univ, true_and]
      exact ⟨by omega, by show f (↑k + p - p) = j; simp [hk]⟩
    · ext; simp

/-- General counting lemma: #{k ∈ Fin parts.sum | rowOfPos parts k = j} = parts.getD j 0. -/
private lemma card_filter_rowOfPos_gen (parts : List ℕ) (j : ℕ) :
    (univ.filter (fun k : Fin parts.sum => rowOfPos parts k.val = j)).card =
    parts.getD j 0 := by
  induction parts generalizing j with
  | nil => simp [rowOfPos]
  | cons p ps ih =>
    cases j with
    | zero =>
      simp only [List.getD_cons_zero, List.sum_cons]
      have : (univ.filter (fun k : Fin (p + ps.sum) => rowOfPos (p :: ps) k.val = 0)) =
             (univ.filter (fun k : Fin (p + ps.sum) => k.val < p)) := by
        ext k; simp only [mem_filter, mem_univ, true_and]; exact rowOfPos_cons_eq_zero p ps k.val
      rw [this]; exact card_filter_lt p ps.sum
    | succ j =>
      simp only [List.getD_cons_succ, List.sum_cons]
      have : (univ.filter (fun k : Fin (p + ps.sum) => rowOfPos (p :: ps) k.val = j + 1)) =
             (univ.filter (fun k : Fin (p + ps.sum) =>
               ¬(k.val < p) ∧ rowOfPos ps (k.val - p) = j)) := by
        ext ⟨v, hv⟩; simp only [mem_filter, mem_univ, true_and, rowOfPos]; split_ifs with h
        · simp [h]
        · exact ⟨fun h1 => ⟨h, by omega⟩, fun ⟨_, h2⟩ => by omega⟩
      rw [this, card_filter_shift p ps.sum (rowOfPos ps) j]; exact ih j

/-- The key counting lemma: the number of positions in row j equals the j-th part. -/
private lemma card_filter_rowFun (la : Nat.Partition n) (j : ℕ) :
    (univ.filter (fun k : Fin n => rowFun la k = j)).card = la.sortedParts.getD j 0 := by
  have h := card_filter_rowOfPos_gen la.sortedParts j
  rw [sortedParts_sum] at h; exact h

/-- Sum of getD over Fin n equals list sum. -/
private lemma list_sum_eq_fin_sum_getD : ∀ (l : List ℕ) (m : ℕ), l.length ≤ m →
    ∑ j : Fin m, l.getD j.val 0 = l.sum := by
  intro l; induction l with
  | nil => intro m _; simp [List.getD]
  | cons h t ih =>
    intro m hm; cases m with
    | zero => simp at hm
    | succ m =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
        List.sum_cons]
      congr 1; exact ih m (by simp at hm; omega)

/-- InvColor coloring values are bounded by n. -/
private lemma invColor_val_lt {n : ℕ} {la : Nat.Partition n} {σ : Equiv.Perm (Fin n)}
    (c : { c : Fin n → ℕ //
      (∀ k : Fin n, c (σ k) = c k) ∧
      (∀ j : Fin n, (univ.filter (fun k => c k = j.val)).card =
        la.sortedParts.getD j.val 0) })
    (k : Fin n) : c.val k < n := by
  by_contra h; push_neg at h
  have hdisj : ∀ i j : Fin n, i ≠ j →
      Disjoint (univ.filter (fun k => c.val k = i.val))
               (univ.filter (fun k => c.val k = j.val)) := by
    intro i j hij
    simp only [Finset.disjoint_filter]
    intro x _ hi hj
    exact hij (Fin.val_injective (hi.symm.trans hj))
  have hsum : ∑ j : Fin n, (univ.filter (fun k' : Fin n => c.val k' = j.val)).card = n := by
    simp_rw [c.prop.2]
    rw [list_sum_eq_fin_sum_getD la.sortedParts n (sortedParts_length_le n la)]
    exact sortedParts_sum n la
  have hcard := card_biUnion (fun i (_ : i ∈ univ) j (_ : j ∈ univ) hij => hdisj i j hij)
  have hk₀_not : k ∉ univ.biUnion (fun j : Fin n =>
      univ.filter (fun k' => c.val k' = j.val)) := by
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists]; intro j; omega
  have hstrict : univ.biUnion (fun j : Fin n =>
      univ.filter (fun k' => c.val k' = j.val)) ⊂ univ :=
    ⟨subset_univ _, fun hall => hk₀_not (hall (mem_univ k))⟩
  have hlt := card_lt_card hstrict
  rw [Finset.card_univ, Fintype.card_fin] at hlt
  omega

/-- The row coloring induced by a permutation: c(m) = rowOfPos(parts, g⁻¹(m)). -/
private abbrev rowColorOf (la : Nat.Partition n) (g : Equiv.Perm (Fin n)) (m : Fin n) : ℕ :=
  rowFun la (g⁻¹ m)

/-- The row coloring from a fixed coset is σ-invariant. -/
private lemma rowColorOf_invariant (la : Nat.Partition n) (σ g : Equiv.Perm (Fin n))
    (hfix : σ • (QuotientGroup.mk g : Equiv.Perm (Fin n) ⧸ RowSubgroup n la) =
            QuotientGroup.mk g)
    (m : Fin n) : rowColorOf la g (σ m) = rowColorOf la g m := by
  -- σ • mk g = mk (σ * g), so (σ * g)⁻¹ * g ∈ RowSubgroup
  have hmem : (σ * g)⁻¹ * g ∈ RowSubgroup n la := by
    rw [show σ • (QuotientGroup.mk g : Equiv.Perm (Fin n) ⧸ RowSubgroup n la) =
         QuotientGroup.mk (σ * g) from rfl, QuotientGroup.eq] at hfix
    exact hfix
  -- Specialize at g⁻¹(σ m): ((σ*g)⁻¹ * g)(g⁻¹(σ m)) = g⁻¹ m
  have hpred := hmem (g⁻¹ (σ m))
  have hsimp : ((σ * g)⁻¹ * g) (g⁻¹ (σ m)) = g⁻¹ m := by
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply, mul_inv_rev]
  rw [hsimp] at hpred
  exact hpred.symm

/-- Two permutations in the same coset give the same row coloring. -/
private lemma rowColorOf_coset_eq (la : Nat.Partition n) (g₁ g₂ : Equiv.Perm (Fin n))
    (hcoset : (QuotientGroup.mk g₁ : Equiv.Perm (Fin n) ⧸ RowSubgroup n la) =
              QuotientGroup.mk g₂) (m : Fin n) :
    rowColorOf la g₁ m = rowColorOf la g₂ m := by
  rw [QuotientGroup.eq] at hcoset
  have hpred := hcoset (g₂⁻¹ m)
  have hsimp : (g₁⁻¹ * g₂) (g₂⁻¹ m) = g₁⁻¹ m := by
    simp [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  rw [hsimp] at hpred
  exact hpred

/-- The row coloring has the correct fiber sizes: #{m | rowColorOf g m = j} = λ_j. -/
private lemma card_rowColorOf (la : Nat.Partition n) (g : Equiv.Perm (Fin n)) (j : ℕ) :
    (univ.filter (fun m : Fin n => rowColorOf la g m = j)).card =
    la.sortedParts.getD j 0 := by
  have : (univ.filter (fun m => rowColorOf la g m = j)) =
         (univ.filter (fun k => rowFun la k = j)).image g := by
    ext m; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨g⁻¹ m, h, by simp⟩
    · rintro ⟨k, hk, rfl⟩; simp [rowColorOf, hk]
  rw [this, Finset.card_image_of_injective _ g.injective]
  exact card_filter_rowFun la j

/-- An σ-invariant row coloring with correct sizes. -/
private def InvColor (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) : Type :=
  { c : Fin n → ℕ //
    (∀ k : Fin n, c (σ k) = c k) ∧
    (∀ j : Fin n, (univ.filter (fun k => c k = j.val)).card = la.sortedParts.getD j.val 0) }

/-- Forward direction: fixed coset → InvColor -/
private def fixedToInvColor (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (q : MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) σ) :
    InvColor n la σ := by
  refine ⟨rowColorOf la (Quotient.out q.val), ?_, ?_⟩
  · intro k
    apply rowColorOf_invariant la σ (Quotient.out q.val)
    rw [QuotientGroup.out_eq']
    exact q.prop
  · intro j
    exact card_rowColorOf la (Quotient.out q.val) j.val

/-- The fiber sizes of an InvColor coloring match those of rowFun. -/
private lemma invColor_fiber_eq (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (c : InvColor n la σ) (t : ℕ) :
    (univ.filter (fun k : Fin n => c.val k = t)).card =
    (univ.filter (fun k : Fin n => rowFun la k = t)).card := by
  by_cases ht : t < n
  · exact (c.prop.2 ⟨t, ht⟩).trans (card_filter_rowFun la t).symm
  · -- Both filters are empty for t ≥ n
    have h1 : (univ.filter (fun k : Fin n => c.val k = t)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; exact ne_of_lt (lt_of_lt_of_le (invColor_val_lt c k) (not_lt.mp ht))
    have h2 : (univ.filter (fun k : Fin n => rowFun la k = t)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; exact ne_of_lt (lt_of_lt_of_le (rowFun_lt la k) (not_lt.mp ht))
    omega

/-- Backward direction: InvColor → fixed coset. -/
private def invColorToFixed (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (c : InvColor n la σ) :
    MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) σ := by
  set g_inv := fiberMatchEquiv' c.val (fun k => rowFun la k) (invColor_fiber_eq la σ c)
  have spec : ∀ m, rowFun la (g_inv m) = c.val m := fun m =>
    fiberMatchEquiv'_spec c.val _ _ m
  refine ⟨QuotientGroup.mk g_inv.symm, ?_⟩
  rw [MulAction.mem_fixedBy]
  change QuotientGroup.mk (σ * g_inv.symm) = QuotientGroup.mk g_inv.symm
  rw [QuotientGroup.eq]
  intro k
  change rowOfPos la.sortedParts (((σ * g_inv.symm)⁻¹ * g_inv.symm) k).val =
       rowOfPos la.sortedParts k.val
  have hperm : ((σ * g_inv.symm)⁻¹ * g_inv.symm) k =
               g_inv (σ⁻¹ (g_inv.symm k)) := by simp [mul_assoc]
  rw [hperm]
  change rowFun la (g_inv (σ⁻¹ (g_inv.symm k))) = rowFun la k
  rw [spec]
  have cinv' : ∀ x, c.val (σ⁻¹ x) = c.val x := fun x => by
    have := c.prop.1 (σ⁻¹ x); simp at this; exact this.symm
  rw [cinv', ← spec (g_inv.symm k), Equiv.apply_symm_apply]

/-- InvColor bijects with MonochromaticColoring via the orbit decomposition.
Each σ-invariant coloring assigns the same color to all elements in a cycle.
This collapses to a cycle-to-row assignment (MonochromaticColoring). -/
private def invColorEquivMC (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    InvColor n la σ ≃ MonochromaticColoring n la σ := by
  sorry

/-- If two representatives give the same row coloring, they're in the same coset. -/
private lemma rowColorOf_eq_imp_coset (la : Nat.Partition n) (g₁ g₂ : Equiv.Perm (Fin n))
    (h : ∀ m : Fin n, rowColorOf la g₁ m = rowColorOf la g₂ m) :
    (QuotientGroup.mk g₁ : Equiv.Perm (Fin n) ⧸ RowSubgroup n la) = QuotientGroup.mk g₂ := by
  rw [QuotientGroup.eq]
  intro k
  -- rowColorOf la g m = rowFun la (g⁻¹ m), so h says rowFun la (g₁⁻¹ m) = rowFun la (g₂⁻¹ m)
  -- We need rowOfPos parts ((g₁⁻¹ * g₂) k).val = rowOfPos parts k.val
  -- (g₁⁻¹ * g₂) k = g₁⁻¹ (g₂ k), and with m = g₂ k:
  -- rowFun la (g₁⁻¹ (g₂ k)) = rowFun la (g₂⁻¹ (g₂ k)) = rowFun la k
  have hk := h (g₂ k)
  -- hk : rowColorOf la g₁ (g₂ k) = rowColorOf la g₂ (g₂ k)
  -- rowColorOf la g₂ (g₂ k) = rowFun la (g₂⁻¹ (g₂ k)) = rowFun la k
  have hrhs : rowColorOf la g₂ (g₂ k) = rowFun la k := by
    change rowFun la (g₂⁻¹ (g₂ k)) = rowFun la k
    congr 1; exact g₂.symm_apply_apply k
  rw [hrhs] at hk
  -- hk : rowColorOf la g₁ (g₂ k) = rowFun la k
  -- = rowFun la (g₁⁻¹ (g₂ k)) = rowFun la k
  -- goal : rowFun la ((g₁⁻¹ * g₂) k) = rowFun la k
  have hmul : (g₁⁻¹ * g₂) k = g₁⁻¹ (g₂ k) := by simp [Equiv.Perm.mul_apply]
  rw [hmul]; exact hk

/-- Injectivity of fixedToInvColor: different cosets give different colorings. -/
private lemma fixedToInvColor_injective (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fixedToInvColor la σ) := by
  intro q₁ q₂ heq
  apply Subtype.ext
  have hcolor : ∀ m, rowColorOf la (Quotient.out q₁.val) m =
      rowColorOf la (Quotient.out q₂.val) m :=
    fun m => congr_fun (congr_arg Subtype.val heq) m
  have := rowColorOf_eq_imp_coset la (Quotient.out q₁.val) (Quotient.out q₂.val) hcolor
  rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

/-- Surjectivity helper: the right inverse property of fixedToInvColor ∘ invColorToFixed. -/
private lemma fixedToInvColor_rightInv (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (c : InvColor n la σ) :
    fixedToInvColor la σ (invColorToFixed la σ c) = c := by
  apply Subtype.ext; funext k
  set g := fiberMatchEquiv' c.val (fun k => rowFun la k) (invColor_fiber_eq la σ c)
  have hspec : ∀ m, (fun k => rowFun la k) (g m) = c.val m := fun m =>
    fiberMatchEquiv'_spec c.val _ _ m
  have hcoset := rowColorOf_coset_eq la
    (Quotient.out (QuotientGroup.mk g.symm : Equiv.Perm (Fin n) ⧸ RowSubgroup n la))
    g.symm (QuotientGroup.out_eq' _) k
  have hgsym : g.symm⁻¹ = g := by ext x; simp
  trans (rowColorOf la g.symm k)
  · exact hcoset
  · change rowFun la (g.symm⁻¹ k) = c.val k
    rw [hgsym]
    exact hspec k

/-- The fixedBy ≃ InvColor equivalence, via bijection of fixedToInvColor. -/
private def fixedByEquivInvColor (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) σ ≃
    InvColor n la σ :=
  Equiv.ofBijective (fixedToInvColor la σ)
    ⟨fixedToInvColor_injective la σ,
     fun c => ⟨invColorToFixed la σ c, fixedToInvColor_rightInv la σ c⟩⟩

end fixedCosets_helpers

theorem fixedCosets_eq_card_colorings (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    permModuleCharacter n la σ = Nat.card (MonochromaticColoring n la σ) := by
  unfold permModuleCharacter
  exact Nat.card_congr ((fixedByEquivInvColor la σ).trans (invColorEquivMC la σ))

/-- **Theorem 5.14.3** (Character formula via power sums): The character of the permutation
module U_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals the coefficient
of x^λ in ∏_{m≥1} p_m(x)^{i_m}, where p_m is the power sum symmetric polynomial
of degree m. (Etingof Theorem 5.14.3)

## Proof sketch

The LHS counts cosets gS_λ fixed by σ. A coset gS_λ is fixed by σ iff each cycle
of σ is monochromatic under the row coloring induced by g (i.e., all elements of
each cycle lie in the same row of the partition λ).

The RHS counts functions f : {cycles of σ} → {rows} such that the total size of
cycles assigned to row i equals λ_i. This is because p_m = Σᵢ xᵢᵐ, so the product
∏_c p_{|c|} = ∏_c (Σᵢ xᵢ^{|c|}) expands to Σ_f ∏_c x_{f(c)}^{|c|}, and the
coefficient of x^λ extracts exactly those assignments with correct row sizes.

These two counts are equal via a bijection between fixed cosets and valid
cycle-to-row assignments. -/
theorem Theorem5_14_3
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    (permModuleCharacter n la σ : ℂ) =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la) (cycleTypePsumProduct n σ) := by
  rw [coeff_psum_prod_eq_card_colorings, ← fixedCosets_eq_card_colorings]

end Etingof
