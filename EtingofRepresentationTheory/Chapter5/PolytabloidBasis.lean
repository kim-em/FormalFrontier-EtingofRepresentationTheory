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
* `Etingof.perm_mul_youngSymmetrizer_mem_span_polytabloids` — straightening lemma (sorry)
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

/-! ### Dominance triangularity

For distinct standard Young tableaux T and T', if c_λ(σ_T⁻¹ · σ_{T'}) ≠ 0 then
the tabloid of T strictly dominates the tabloid of T' in the dominance order.

**Proof strategy** (not yet formalized):
1. c_λ(g) ≠ 0 implies g ∈ P_λ · Q_λ (support of c_λ = a_λ · b_λ is P_λ · Q_λ)
2. σ_T⁻¹ · σ_{T'} = p · q for p ∈ P_λ, q ∈ Q_λ means σ_{T'} = σ_T · p · q
3. σ_T · p has the same tabloid as T (p is a row permutation)
4. Applying column permutation q can only decrease dominance
5. Since T ≠ T' give different tabloids, the dominance decrease is strict

This requires formalizing the dominance order on tabloids and the effect of column
permutations on dominance (standard results in James, Chapter 3).
-/

/-- There exists a well-founded strict partial order on SYT(λ) such that the
evaluation matrix of polytabloids is unitriangular: if c_λ(σ_T⁻¹ · σ_{T'}) ≠ 0
and T ≠ T', then T is strictly greater than T' in this order (the dominance
order on tabloids).

Concretely: for any nonempty finite subset S ⊆ SYT(λ), there exists a maximal
element T₀ ∈ S such that for all T ∈ SYT(λ) with T ≠ T₀,
c_λ(σ_T⁻¹ · σ_{T₀}) ≠ 0 implies T ∉ S.

**Proof**: Take T₀ to be the element of S whose tabloid is maximal in the
dominance order (which is a partial order on a finite set, hence has maximal
elements). If c_λ(σ_T⁻¹ · σ_{T₀}) ≠ 0 and T ≠ T₀, then by the triangularity
lemma, the tabloid of T strictly dominates the tabloid of T₀. But T₀ was
chosen to be maximal in S, so T ∉ S. -/
private lemma exists_maximal_for_eval (n : ℕ) (la : Nat.Partition n)
    (s : Finset (StandardYoungTableau n la)) (hs : s.Nonempty) :
    ∃ T₀ ∈ s, ∀ T : StandardYoungTableau n la, T ≠ T₀ →
      (YoungSymmetrizer n la : SymGroupAlgebra n)
        ((sytPerm n la T)⁻¹ * sytPerm n la T₀) ≠ 0 →
      T ∉ s := by
  sorry

/-- The polytabloids {e_T : T ∈ SYT(λ)} are linearly independent in V_λ.

**Proof**: By contradiction. Suppose Σ aₜ eₜ = 0 with some aₜ ≠ 0.
Let S = {T : aₜ ≠ 0}. By `exists_maximal_for_eval`, there exists T₀ ∈ S
maximal for the dominance order. Evaluating the linear combination at σ_{T₀}:
  Σ_T aₜ · eₜ(σ_{T₀}) = 0
For T = T₀: contribution is a_{T₀} · 1 = a_{T₀} (by `polytabloid_self_coeff`).
For T ≠ T₀ with eₜ(σ_{T₀}) ≠ 0: T ∉ S by maximality, so aₜ = 0.
Hence a_{T₀} = 0, contradicting T₀ ∈ S. -/
theorem polytabloid_linearIndependent (n : ℕ) (la : Nat.Partition n) :
    LinearIndependent ℂ (fun T : StandardYoungTableau n la =>
      (polytabloidInSpecht n la T : SymGroupAlgebra n)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg T hT
  -- hg says: ∑ T ∈ s, g T • polytabloidInSpecht T = 0
  -- We need: g T = 0
  -- Proof by contradiction: suppose some g values are nonzero
  by_contra h_ne
  -- Let S = {T ∈ s : g T ≠ 0}
  set S := s.filter (fun T' => g T' ≠ 0) with hS_def
  have hS_nonempty : S.Nonempty := ⟨T, Finset.mem_filter.mpr ⟨hT, h_ne⟩⟩
  -- Get a maximal element T₀
  obtain ⟨T₀, hT₀_mem, hT₀_max⟩ := exists_maximal_for_eval n la S hS_nonempty
  have hT₀_in_s : T₀ ∈ s := (Finset.mem_filter.mp hT₀_mem).1
  have hgT₀_ne : g T₀ ≠ 0 := (Finset.mem_filter.mp hT₀_mem).2
  -- Evaluate the linear combination at σ_{T₀}
  -- The overall sum is 0 as a Finsupp, so evaluating at any permutation gives 0
  -- Evaluate the zero sum at σ_{T₀}
  have h0 : (∑ T' ∈ s, g T' • (polytabloidInSpecht n la T' : SymGroupAlgebra n)) = 0 := hg
  -- Pointwise evaluation at σ_{T₀}
  have heval_raw : (∑ T' ∈ s, g T' •
      (polytabloidInSpecht n la T' : SymGroupAlgebra n)) (sytPerm n la T₀) = 0 := by
    rw [h0]; rfl
  -- Rewrite to use polytabloid directly
  have heval : ∑ T' ∈ s, g T' * (polytabloid n la T' : SymGroupAlgebra n)
      (sytPerm n la T₀) = 0 := by
    have : ∀ T' ∈ s, (g T' • (polytabloidInSpecht n la T' : SymGroupAlgebra n))
        (sytPerm n la T₀) =
        g T' * (polytabloid n la T' : SymGroupAlgebra n) (sytPerm n la T₀) := by
      intro T' _; rfl
    rw [Finsupp.finset_sum_apply] at heval_raw
    rwa [Finset.sum_congr rfl this] at heval_raw
  -- Split out the T₀ term
  rw [← Finset.add_sum_erase s _ hT₀_in_s] at heval
  rw [polytabloid_self_coeff, mul_one] at heval
  -- Each non-T₀ term is zero by triangularity
  have sum_zero : ∑ T' ∈ s.erase T₀,
      g T' * (polytabloid n la T' : SymGroupAlgebra n) (sytPerm n la T₀) = 0 := by
    apply Finset.sum_eq_zero
    intro T' hT'
    have hT'_ne : T' ≠ T₀ := (Finset.mem_erase.mp hT').1
    have hT'_in_s : T' ∈ s := (Finset.mem_erase.mp hT').2
    by_cases hgT' : g T' = 0
    · simp [hgT']
    · have hT'_in_S : T' ∈ S := Finset.mem_filter.mpr ⟨hT'_in_s, hgT'⟩
      rw [polytabloid_apply]
      by_cases hc : (YoungSymmetrizer n la : SymGroupAlgebra n)
          ((sytPerm n la T')⁻¹ * sytPerm n la T₀) = 0
      · simp [hc]
      · exact absurd hT'_in_S (hT₀_max T' hT'_ne hc)
  exact hgT₀_ne (by rw [sum_zero, add_zero] at heval; exact heval)

/-- **Straightening lemma**: any permutation applied to the Young symmetrizer
lies in the ℂ-span of standard polytabloids. This is the key step that
requires the Garnir relations and dominance order on tabloids.

For any σ ∈ Sₙ, the element σ · cλ can be expressed as a ℂ-linear combination
of the standard polytabloids {σ_T · cλ : T ∈ SYT(λ)} by the straightening
algorithm: non-standard tabloids are rewritten using Garnir relations until
all tabloids are standard.

TODO: requires Garnir relations, dominance order, and straightening algorithm. -/
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
