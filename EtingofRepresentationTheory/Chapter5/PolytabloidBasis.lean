import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_17_1

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
* `Etingof.polytabloid_span` — polytabloids span the Specht module (sorry)

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

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in V_λ.

This is the harder direction: it requires showing that the polytabloids
indexed by distinct standard Young tableaux do not satisfy any nontrivial
linear relation. The standard proof uses the straightening algorithm
(Garnir relations) and the dominance ordering on tabloids.

**Proof sketch:**
1. Define a partial order on tabloids using dominance of the corresponding
   row equivalence classes
2. Show that the leading tabloid of e_T (in the dominance order) is {T} itself
3. Different standard tableaux give different leading tabloids
4. A triangularity argument gives linear independence -/
theorem polytabloid_linearIndependent (n : ℕ) (la : Nat.Partition n) :
    LinearIndependent ℂ (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n)) := by
  sorry

/-- The polytabloids {e_T : T ∈ SYT(λ)} span V_λ.

**Proof sketch:**
1. V_λ = ℂ[S_n] · c_λ, so any element is x · c_λ for some x
2. Decompose x in terms of group elements: x = Σ a_σ · σ
3. Each σ · c_λ can be expressed as a linear combination of polytabloids
   (by straightening: rewriting non-standard polytabloids using Garnir relations)
4. Therefore the polytabloids span V_λ -/
theorem polytabloid_span (n : ℕ) (la : Nat.Partition n) :
    Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n))) =
    (SpechtModule n la).restrictScalars ℂ := by
  sorry

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
  sorry

end

end Etingof
