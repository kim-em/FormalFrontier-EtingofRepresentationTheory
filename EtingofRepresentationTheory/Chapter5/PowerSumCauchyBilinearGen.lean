import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinear
import EtingofRepresentationTheory.Chapter5.PermDiagonalTrace

/-!
# Generalized Power Sum Cauchy Identity: N ≠ n

This file generalizes the bilinear Cauchy identity infrastructure from `PowerSumCauchyBilinear`
to the case where the number of variables N may differ from the permutation group size n.

The original `CycleColoring n α σ` colors cycles of σ ∈ S_n with Fin n colors.
Here `CycleColoringGen N n α σ` colors cycles of σ ∈ S_n with Fin N colors.

This generalization is needed for the Weyl character formula (Theorem 5.22.1),
where `charValue` uses N variables (dim V) with S_n permutations (n = |λ|).

## Main definitions

* `CycleColoringGen N n α σ`: Cycle coloring with Fin N colors for σ ∈ S_n
* `NNMatrixWithMarginsGen N n α β`: N×N non-negative integer matrices with row sums α,
  column sums β, and entries bounded by n+1

## Main results

* `coeff_powerSumCycleProduct_eq_card`: The coefficient of x^α in the power sum cycle
  product equals the number of generalized cycle colorings
* `powerSum_bilinear_coeff_gen`: The generalized bilinear Cauchy identity
-/

open MvPolynomial Finset

namespace Etingof

noncomputable section

variable (N : ℕ) {n : ℕ}

/-! ### Generalized cycle colorings -/

/-- A generalized cycle coloring assigns each cycle of σ ∈ S_n a "color" from Fin N
(where N may differ from n), such that the total cycle lengths for each color match α.
This generalizes `CycleColoring` from the case N = n. -/
def CycleColoringGen (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin N //
    ∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) = α j }

instance (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CycleColoringGen N α σ) := by
  unfold CycleColoringGen
  exact Subtype.fintype _

/-- The finsupp sum condition is equivalent to the pointwise condition for generalized
cycle colorings. -/
private lemma finsupp_sum_single_iff_gen (α : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin N) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin N, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

/-- Each psum polynomial in N variables over ℚ equals a sum of monomials. -/
private theorem psum_eq_sum_monomial_gen (m : ℕ) :
    MvPolynomial.psum (Fin N) ℚ m =
    ∑ i : Fin N, MvPolynomial.monomial (Finsupp.single i m) 1 := by
  simp only [MvPolynomial.psum, MvPolynomial.X_pow_eq_monomial]

/-- The MvPolynomial coefficient of powerSumCycleProduct N σ at a composition α
equals the number of generalized cycle colorings. -/
theorem coeff_powerSumCycleProduct_eq_card (α : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (powerSumCycleProduct N σ) =
    ↑(Fintype.card (CycleColoringGen N α σ)) := by
  unfold powerSumCycleProduct
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial_gen]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast
  have equiv : CycleColoringGen N α σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α } := by
    unfold CycleColoringGen
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff_gen N α σ f).symm)
  rw [show Fintype.card (CycleColoringGen N α σ) = Fintype.card
      { f : Fin (fullCycleType n σ).toList.length → Fin N //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

/-! ### Generalized non-negative integer matrices -/

/-- A non-negative integer N×N matrix with prescribed row and column sums.
Entries are bounded by `n + 1` (since row sums α_i ≤ n) to ensure finiteness.
This generalizes `NNMatrixWithMargins` from the case N = n. -/
def NNMatrixWithMarginsGen (α β : Fin N → ℕ) : Type :=
  { K : Fin N → Fin N → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

instance (α β : Fin N → ℕ) : Fintype (NNMatrixWithMarginsGen N (n := n) α β) :=
  Subtype.fintype _

/-! ### Generalized double counting infrastructure -/

/-- Element bicoloring with prescribed marginals (generalized). -/
private def ElemBicolGen (α β : Fin N →₀ ℕ) : Type :=
  { h : Fin n → Fin N × Fin N //
    (∀ i : Fin N, (Finset.univ.filter fun x => (h x).1 = i).card = α i) ∧
    (∀ j : Fin N, (Finset.univ.filter fun x => (h x).2 = j).card = β j) }

private instance (α β : Fin N →₀ ℕ) : Fintype (ElemBicolGen N (n := n) α β) :=
  Subtype.fintype _

/-- Permutation preserving fibers of h (generalized). -/
private def FiberPermGen (h : Fin n → Fin N × Fin N) : Type :=
  { σ : Equiv.Perm (Fin n) // ∀ x, h (σ x) = h x }

private instance (h : Fin n → Fin N × Fin N) : Fintype (FiberPermGen N h) :=
  Subtype.fintype _

/-- Construct a generalized element bicoloring from cycle colorings. -/
private def cycleColToBicolGen (α β : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : CycleColoringGen N α σ × CycleColoringGen N β σ) :
    ElemBicolGen N (n := n) α β :=
  let π := (exists_orbIdx σ).choose
  have hπ := (exists_orbIdx σ).choose_spec
  ⟨fun x => (fg.1.val (π x), fg.2.val (π x)),
   ⟨fun i => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.1.val (π x) = i) =
          (Finset.univ.filter fun j => fg.1.val j = i).biUnion
            (fun j => Finset.univ.filter fun x => π x = j) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨j, hj, hjx⟩ => hjx ▸ hj⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext j; rw [hπ.2 j]
      exact fg.1.prop i,
    fun j => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.2.val (π x) = j) =
          (Finset.univ.filter fun k => fg.2.val k = j).biUnion
            (fun k => Finset.univ.filter fun x => π x = k) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨k, hk, hkx⟩ => hkx ▸ hk⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext k; rw [hπ.2 k]
      exact fg.2.prop j⟩⟩

/-- The permutation σ preserves the bicoloring constructed from its cycle colorings. -/
private lemma cycleColToBicolGen_compat (α β : Fin N →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : CycleColoringGen N α σ × CycleColoringGen N β σ) :
    ∀ x, (cycleColToBicolGen N α β σ fg).val (σ x) = (cycleColToBicolGen N α β σ fg).val x := by
  intro x
  simp only [cycleColToBicolGen]
  let π := (exists_orbIdx σ).choose
  have hπ := (exists_orbIdx σ).choose_spec
  show (fg.1.val (π (σ x)), fg.2.val (π (σ x))) = (fg.1.val (π x), fg.2.val (π x))
  have hkey : π (σ x) = π x := (hπ.1 (σ x) x).mpr ⟨-1, by simp⟩
  rw [hkey]

/-- **Part A (generalized)**: Bijection between (σ, CycleCol pairs) and (h, FiberPerm). -/
private lemma card_sigma_CycleCol_eq_card_sigma_fiberPermGen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ σ : Equiv.Perm (Fin n), CycleColoringGen N α σ × CycleColoringGen N β σ) =
    Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨σ, fg⟩ =>
      ⟨cycleColToBicolGen N α β σ fg,
       ⟨σ, cycleColToBicolGen_compat N α β σ fg⟩⟩
    invFun := fun p =>
      let h := p.1.val
      let σ := p.2.val
      let hcompat : ∀ x, h (σ x) = h x := p.2.property
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      let rep := fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)
      have hrep : ∀ i, π (rep i) = i := fun i =>
        (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih => intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hcompat]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ⟨σ,
        ⟨fun i => (h (rep i)).1, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).1 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).1 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).1 = j) by rw [heq]; exact p.1.2.1 j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩,
        ⟨fun i => (h (rep i)).2, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).2 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).2 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).2 = j) by rw [heq]; exact p.1.2.2 j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩⟩
    left_inv := fun ⟨σ, fg⟩ => by
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      refine Sigma.ext rfl (heq_of_eq ?_)
      simp only [cycleColToBicolGen]
      apply Prod.ext
      · apply Subtype.ext; funext i; exact congrArg fg.1.val (hrep i)
      · apply Subtype.ext; funext i; exact congrArg fg.2.val (hrep i)
    right_inv := fun ⟨⟨h, hrow, hcol⟩, ⟨σ, hcompat⟩⟩ => by
      simp only [cycleColToBicolGen]
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih =>
          intro y; rw [pow_succ, Equiv.Perm.mul_apply]
          exact (ih (σ y)).trans (hcompat y)
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ext1
      · apply Subtype.ext; funext x
        have key := hconst _ x (hrep (π x))
        simp only [Prod.mk.eta]; exact key
      · rfl
  }

/-! ### MulAction on generalized element bicolorings -/

private noncomputable def permSmulElemBicolGen {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) : ElemBicolGen N (n := n) α β :=
  ⟨hb.val ∘ ⇑σ⁻¹, by
    constructor
    · intro i
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).1 = i)).card =
          (Finset.univ.filter (fun x => (hb.val x).1 = i)).card := by
        apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Function.comp] at hx ⊢; convert hx using 1; simp
        · intro x _; simp
        · intro x _; simp
      rw [h1]; exact hb.2.1 i
    · intro j
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).2 = j)).card =
          (Finset.univ.filter (fun x => (hb.val x).2 = j)).card := by
        apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Function.comp] at hx ⊢; convert hx using 1; simp
        · intro x _; simp
        · intro x _; simp
      rw [h1]; exact hb.2.2 j⟩

@[simp]
private lemma permSmulElemBicolGen_val {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) :
    (permSmulElemBicolGen N σ hb).val = hb.val ∘ ⇑σ⁻¹ := rfl

private noncomputable instance permMulActionElemBicolGen {α β : Fin N →₀ ℕ} :
    MulAction (Equiv.Perm (Fin n)) (ElemBicolGen N (n := n) α β) where
  smul := permSmulElemBicolGen N
  one_smul hb := Subtype.ext (funext fun _ => by
    show (permSmulElemBicolGen N 1 hb).val _ = hb.val _
    simp [permSmulElemBicolGen_val, Function.comp])
  mul_smul σ τ hb := Subtype.ext (funext fun x => by
    show (permSmulElemBicolGen N (σ * τ) hb).val x =
      (permSmulElemBicolGen N σ (permSmulElemBicolGen N τ hb)).val x
    simp [permSmulElemBicolGen_val, Function.comp, mul_inv_rev, Equiv.Perm.mul_apply])

private lemma mem_stabilizer_iff_fiberPermGen {α β : Fin N →₀ ℕ}
    (hb : ElemBicolGen N (n := n) α β) (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) hb ↔ ∀ x, hb.val (σ x) = hb.val x := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 := congr_arg Subtype.val h
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicolGen_val N σ hb] at h1
    have := congr_fun h1 (σ x); simp at this; exact this.symm
  · intro h; apply Subtype.ext
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicolGen_val N σ hb]
    funext x; have := h (σ⁻¹ x); simp at this; exact this.symm

/-- Fiber size matrix for generalized bicolorings. -/
private noncomputable def fiberSizesGen {α β : Fin N →₀ ℕ}
    (hb : ElemBicolGen N (n := n) α β) : NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β) :=
  ⟨fun i j => ⟨(Finset.univ.filter fun x => hb.val x = (i, j)).card,
    Nat.lt_succ_of_le <| (Finset.card_filter_le _ _).trans <| by simp [Fintype.card_fin]⟩,
   fun i => by
     simp only [Fin.val_natCast]
     rw [← hb.2.1 i]
     rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hj =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hj (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.2)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨j, ⟨h1, h2⟩⟩ => h1, fun h => ⟨(hb.val x).2, ⟨h, rfl⟩⟩⟩,
   fun j => by
     simp only [Fin.val_natCast]
     rw [← hb.2.2 j]
     rw [← Finset.card_biUnion (fun i₁ _ i₂ _ hi =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hi (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.1)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨i, ⟨h1, h2⟩⟩ => h2, fun h => ⟨(hb.val x).1, ⟨rfl, h⟩⟩⟩⟩

private lemma fiberSizesGen_smul_eq {α β : Fin N →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) :
    fiberSizesGen N (σ • hb) = fiberSizesGen N hb := by
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizesGen, permSmulElemBicolGen_val]
  have : (Finset.univ.filter (fun x => (hb.val ∘ ⇑σ⁻¹) x = (i, j))).card =
      (Finset.univ.filter (fun x => hb.val x = (i, j))).card := by
    apply Finset.card_bij' (fun x _ => σ⁻¹ x) (fun x _ => σ x)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp] at hx ⊢; convert hx using 1; simp
    · intro x _; simp
    · intro x _; simp
  exact this

private lemma same_fiberSizes_same_orbitGen {α β : Fin N →₀ ℕ}
    (h₁ h₂ : ElemBicolGen N (n := n) α β) (heq : fiberSizesGen N h₁ = fiberSizesGen N h₂) :
    h₁ ∈ MulAction.orbit (Equiv.Perm (Fin n)) h₂ := by
  classical
  have hcard : ∀ p : Fin N × Fin N,
      Fintype.card { x // h₁.val x = p } = Fintype.card { x // h₂.val x = p } := by
    intro ⟨i, j⟩
    simp only [Fintype.card_subtype, Finset.card_filter]
    have := congr_arg (fun K => (K.1 i j : ℕ)) heq
    simpa [fiberSizesGen] using this
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofFiberEquiv (f := h₁.val) (g := h₂.val)
      (fun p => Fintype.equivOfCardEq (hcard p))
  have hσ : ∀ x, h₂.val (σ x) = h₁.val x := Equiv.ofFiberEquiv_map _
  refine ⟨σ⁻¹, Subtype.ext (funext fun x => ?_)⟩
  simp only [permSmulElemBicolGen_val, Function.comp, inv_inv]
  exact hσ x

/-- Helper for counting sigma-types over filter. -/
private lemma sigma_filter_fst_card_gen (K : Fin N → Fin N → ℕ) (i : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1.1 = i)).card = ∑ j, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ j, K i j = Fintype.card (Σ j : Fin N, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i', j⟩, k⟩, (hi : i' = i)⟩ => ⟨j, hi ▸ k⟩
    invFun := fun ⟨j, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i', j⟩, k⟩, hi⟩ => by subst hi; rfl
    right_inv := fun ⟨j, k⟩ => rfl }

private lemma sigma_filter_snd_card_gen (K : Fin N → Fin N → ℕ) (j : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1.2 = j)).card = ∑ i, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ i, K i j = Fintype.card (Σ i : Fin N, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i, j'⟩, k⟩, (hj : j' = j)⟩ => ⟨i, hj ▸ k⟩
    invFun := fun ⟨i, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i, j'⟩, k⟩, hj⟩ => by subst hj; rfl
    right_inv := fun ⟨i, k⟩ => rfl }

private lemma sigma_filter_pair_card_gen (K : Fin N → Fin N → ℕ) (i j : Fin N) :
    (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j))).card = K i j := by
  have : Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j)) =
    (Finset.univ : Finset (Fin (K i j))).map
      ⟨fun k => ⟨(i, j), k⟩, fun k₁ k₂ h => by simpa using h⟩ := by
    ext ⟨⟨i', j'⟩, k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (congr_arg Sigma.fst hk').symm
  rw [this, Finset.card_map, Finset.card_fin]

private noncomputable def elemBicolOfMatrixGen_equiv {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) :
    Fin n ≃ (Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type]
    simp_rw [K.2.1]; rw [hα])

private noncomputable def elemBicolOfMatrixGen {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) :
    ElemBicolGen N (n := n) α β :=
  ⟨fun x => (elemBicolOfMatrixGen_equiv N hα K x).1,
   ⟨fun i => by
      classical
      have h1 : (Finset.univ.filter (fun x =>
          (elemBicolOfMatrixGen_equiv N hα K x).1.1 = i)).card =
          (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
            s.1.1 = i)).card := by
        apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
          (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          convert hs using 1; simp
        · intro x _; simp
        · intro s _; simp
      rw [h1]
      have h2 := sigma_filter_fst_card_gen N (fun i j => (K.1 i j : ℕ)) i
      convert h2 using 1
      exact (K.2.1 i).symm,
    fun j => by
      classical
      have h1 : (Finset.univ.filter (fun x =>
          (elemBicolOfMatrixGen_equiv N hα K x).1.2 = j)).card =
          (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
            s.1.2 = j)).card := by
        apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
          (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
        · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
        · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          convert hs using 1; simp
        · intro x _; simp
        · intro s _; simp
      rw [h1]
      have h2 := sigma_filter_snd_card_gen N (fun i j => (K.1 i j : ℕ)) j
      convert h2 using 1
      exact (K.2.2 j).symm⟩⟩

private lemma fiberSizesGen_elemBicolOfMatrixGen {α β : Fin N →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) :
    fiberSizesGen N (elemBicolOfMatrixGen N hα K) = K := by
  classical
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizesGen, elemBicolOfMatrixGen]
  have h1 : (Finset.univ.filter (fun x =>
      (elemBicolOfMatrixGen_equiv N hα K x).1 = (i, j))).card =
      (Finset.univ.filter (fun (s : Σ ij : Fin N × Fin N, Fin (K.1 ij.1 ij.2 : ℕ)) =>
        s.1 = (i, j))).card := by
    apply Finset.card_bij' (fun x _ => elemBicolOfMatrixGen_equiv N hα K x)
      (fun s _ => (elemBicolOfMatrixGen_equiv N hα K).symm s)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      convert hs using 1; simp
    · intro x _; simp
    · intro s _; simp
  rw [h1]; exact sigma_filter_pair_card_gen N (fun i j => (K.1 i j : ℕ)) i j

/-- **Part B (generalized)**: orbit-stabilizer gives n! × card(matrices). -/
private lemma card_sigma_fiberPerm_eq_factorial_mulGen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) =
    n.factorial * Fintype.card (NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) := by
  classical
  -- Step 1: FiberPermGen ≃ stabilizer
  have step1 : Fintype.card (Σ hb : ElemBicolGen N (n := n) α β, FiberPermGen N hb.val) =
      Fintype.card (Σ hb : ElemBicolGen N (n := n) α β,
        MulAction.stabilizer (Equiv.Perm (Fin n)) hb) := by
    apply Fintype.card_congr
    exact Equiv.sigmaCongrRight (fun hb =>
      Equiv.subtypeEquiv (Equiv.refl _) (fun σ =>
        (mem_stabilizer_iff_fiberPermGen N hb σ).symm))
  rw [step1]
  -- Step 2: Swap sigma
  have step2 : Fintype.card (Σ hb : ElemBicolGen N (n := n) α β,
      MulAction.stabilizer (Equiv.Perm (Fin n)) hb) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) := by
    apply Fintype.card_congr
    calc (Σ hb : ElemBicolGen N (n := n) α β,
            MulAction.stabilizer (Equiv.Perm (Fin n)) hb)
      ≃ { p : ElemBicolGen N (n := n) α β × Equiv.Perm (Fin n) //
            p.2 ∈ MulAction.stabilizer _ p.1 } :=
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (hb : ElemBicolGen N (n := n) α β) (σ : Equiv.Perm (Fin n)) =>
            σ ∈ MulAction.stabilizer _ hb)).symm
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicolGen N (n := n) α β //
            p.1 ∈ MulAction.stabilizer _ p.2 } :=
        (Equiv.prodComm _ _).subtypeEquiv (fun ⟨_, _⟩ => Iff.rfl)
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicolGen N (n := n) α β //
            p.2 ∈ MulAction.fixedBy _ p.1 } :=
        Equiv.subtypeEquivRight (fun ⟨σ, hb⟩ => by
          simp [MulAction.mem_stabilizer_iff, MulAction.mem_fixedBy])
      _ ≃ (Σ σ : Equiv.Perm (Fin n),
            MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) :=
        Equiv.subtypeProdEquivSigmaSubtype
          (fun (σ : Equiv.Perm (Fin n)) (hb : ElemBicolGen N (n := n) α β) =>
            hb ∈ MulAction.fixedBy _ σ)
  rw [step2]
  -- Step 3: Burnside's lemma
  rw [show Fintype.card (Σ σ : Equiv.Perm (Fin n),
        MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) =
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (MulAction.fixedBy (ElemBicolGen N (n := n) α β) σ) from
    Fintype.card_sigma]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  rw [Fintype.card_perm, Fintype.card_fin, mul_comm]
  congr 1
  -- Step 4: Orbits ≃ NNMatrixWithMarginsGen via fiberSizesGen
  apply Fintype.card_congr
  letI := MulAction.orbitRel (Equiv.Perm (Fin n)) (ElemBicolGen N (n := n) α β)
  exact Equiv.ofBijective
    (Quotient.lift (fiberSizesGen N) (fun a b (hab : a ∈ MulAction.orbit _ b) => by
      obtain ⟨g, rfl⟩ := hab; exact fiberSizesGen_smul_eq N g b))
    ⟨fun q₁ q₂ => Quotient.inductionOn₂ q₁ q₂ (fun a b heq =>
        Quotient.sound (same_fiberSizes_same_orbitGen N a b heq)),
     fun K => ⟨Quotient.mk' (elemBicolOfMatrixGen N hα K),
              fiberSizesGen_elemBicolOfMatrixGen N hα K⟩⟩

/-- **Generalized double counting lemma**: The total number of (σ, f, g) triples
(where σ ∈ S_n, f colors cycles with Fin N colors matching α, g matches β)
equals n! times the number of N×N matrices with margins (α, β). -/
theorem double_counting_gen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoringGen N α σ) * Fintype.card (CycleColoringGen N β σ) =
    n.factorial * Fintype.card (NNMatrixWithMarginsGen N (n := n) (⇑α) (⇑β)) := by
  have h1 : ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoringGen N α σ) * Fintype.card (CycleColoringGen N β σ) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      CycleColoringGen N α σ × CycleColoringGen N β σ) := by
    simp_rw [← Fintype.card_prod]; exact Fintype.card_sigma.symm
  rw [h1, card_sigma_CycleCol_eq_card_sigma_fiberPermGen N α β hα hβ]
  exact card_sigma_fiberPerm_eq_factorial_mulGen N α β hα hβ

/-! ### Generalized fullCauchyProd coefficient = matrix count -/

/-- Naturality of `fullCauchyProd` under ring homomorphisms. -/
private theorem map_invOfUnit_one_sub_xy {k k' : Type*} [CommRing k] [CommRing k']
    (f : k →+* k') (i j : Fin N) :
    MvPowerSeries.map f
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : CauchyVars N) *
             MvPowerSeries.X (Sum.inr j : CauchyVars N) : MvPowerSeries (CauchyVars N) k) 1) =
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : CauchyVars N) *
           MvPowerSeries.X (Sum.inr j : CauchyVars N) : MvPowerSeries (CauchyVars N) k') 1 := by
  set g : MvPowerSeries (CauchyVars N) k :=
    1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)
  have hmapped : MvPowerSeries.map f g =
      (1 - MvPowerSeries.X (Sum.inl i : CauchyVars N) *
           MvPowerSeries.X (Sum.inr j) : MvPowerSeries _ k') := by
    simp [g, map_sub, map_one, map_mul, MvPowerSeries.map_X]
  have h1 := MvPowerSeries.mul_invOfUnit g 1
    (by simp [g, MvPowerSeries.constantCoeff_X])
  have h2 : MvPowerSeries.map f (g * g.invOfUnit 1) = MvPowerSeries.map f 1 := by rw [h1]
  rw [map_mul, hmapped, map_one] at h2
  set g' : MvPowerSeries (CauchyVars N) k' :=
    1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)
  have h3 := MvPowerSeries.mul_invOfUnit g' 1
    (by simp [g', MvPowerSeries.constantCoeff_X])
  have hU : IsUnit g' :=
    ⟨⟨_, _, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
  exact hU.mul_left_cancel (h2.trans h3.symm)

theorem map_fullCauchyProd {k k' : Type*} [CommRing k] [CommRing k'] (f : k →+* k') :
    MvPowerSeries.map f (fullCauchyProd N k) = fullCauchyProd N k' := by
  unfold fullCauchyProd
  rw [map_prod (MvPowerSeries.map f)]
  apply Finset.prod_congr rfl; intro i _
  rw [map_prod (MvPowerSeries.map f)]
  apply Finset.prod_congr rfl; intro j _
  exact map_invOfUnit_one_sub_xy N f i j

/-- NNMatrixWithMarginsGen and NNMatrixWithMargins have the same cardinality when
the entry bounds are both sufficient. -/
private theorem card_NNMatrixWithMarginsGen_eq_card_NNMatrixWithMargins
    (α β : Fin N → ℕ) (hα : ∀ i, α i ≤ n)
    (hα' : ∀ i, α i ≤ N) :
    Fintype.card (NNMatrixWithMarginsGen N (n := n) α β) =
    Fintype.card (NNMatrixWithMargins N α β) := by
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨K, hrow, hcol⟩ => ⟨fun i j => ⟨(K i j : ℕ),
      Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans (hα' i))⟩, hrow, hcol⟩
    invFun := fun ⟨K, hrow, hcol⟩ => ⟨fun i j => ⟨(K i j : ℕ),
      Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans (hα i))⟩, hrow, hcol⟩
    left_inv := fun ⟨K, _, _⟩ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_); simp
    right_inv := fun ⟨K, _, _⟩ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_); simp
  }

/-- Coefficient of invOfUnit(1-xy, 1) over ℚ, transferred from the ℂ version. -/
private theorem coeff_invOfUnit_one_sub_xy_rat (i j : Fin N) (e : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff e
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : CauchyVars N) *
             MvPowerSeries.X (Sum.inr j : CauchyVars N) : MvPowerSeries (CauchyVars N) ℚ) 1) =
    if e = e (Sum.inl i) • (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1)
    then 1 else 0 := by
  have h_inj : Function.Injective (algebraMap ℚ ℂ) := Rat.cast_injective
  apply h_inj
  rw [show (algebraMap ℚ ℂ) (MvPowerSeries.coeff e (MvPowerSeries.invOfUnit _ _)) =
      MvPowerSeries.coeff e (MvPowerSeries.map (algebraMap ℚ ℂ)
        (MvPowerSeries.invOfUnit _ _)) from by rw [MvPowerSeries.coeff_map]]
  rw [map_invOfUnit_one_sub_xy]
  rw [coeff_invOfUnit_one_sub_xy]
  split <;> simp [*]

/-- The full Cauchy product over ℚ as a product over pairs. -/
private theorem fullCauchyProd_eq_prod_pairs_gen :
    fullCauchyProd N ℚ = ∏ p : Fin N × Fin N,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl p.1 : CauchyVars N) *
             MvPowerSeries.X (Sum.inr p.2 : CauchyVars N) : MvPowerSeries (CauchyVars N) ℚ)
        (1 : ℚˣ) := by
  unfold fullCauchyProd
  rw [Fintype.prod_prod_type]

theorem fullCauchyProd_coeff_eq_card_gen (α β : Fin N → ℕ)
    (hα : ∀ i, α i ≤ n) :
    MvPowerSeries.coeff (bilinExponent N α β) (fullCauchyProd N ℚ) =
    ↑(Fintype.card (NNMatrixWithMarginsGen N (n := n) α β)) := by
  rw [fullCauchyProd_eq_prod_pairs_gen]
  rw [MvPowerSeries.coeff_prod]
  simp_rw [coeff_invOfUnit_one_sub_xy_rat, Finset.prod_boole,
    Finset.mem_univ, forall_true_left, Finset.sum_boole]
  norm_cast
  -- Bijection: valid antidiag elements ↔ NNMatrixWithMarginsGen
  set xyMon : Fin N × Fin N → CauchyVars N →₀ ℕ :=
    fun p => Finsupp.single (Sum.inl p.1) 1 + Finsupp.single (Sum.inr p.2) 1
  -- Extract row/col sum lemmas from antidiag membership
  have extract_row : ∀ (x : (Fin N × Fin N) →₀ (CauchyVars N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (bilinExponent N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ i, ∑ j, (x (i, j)) (Sum.inl i) = α i := by
    intro x hx hvalid i
    have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx).1 (Sum.inl i)
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, bilinExponent_inl] at h
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i _ _] at h
    · exact h
    · intro i' _ hi'
      exact Finset.sum_eq_zero fun j _ => by
        have := DFunLike.congr_fun (hvalid (i', j)) (Sum.inl i)
        simp [xyMon, Finsupp.single_apply, hi'] at this; exact this
    · exact fun h' => absurd (Finset.mem_univ i) h'
  have extract_col : ∀ (x : (Fin N × Fin N) →₀ (CauchyVars N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (bilinExponent N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ j, ∑ i, (x (i, j)) (Sum.inl i) = β j := by
    intro x hx hvalid j
    have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx).1 (Sum.inr j)
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, bilinExponent_inr] at h
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j _ _] at h
    · rwa [show (∑ i, (x (i, j)) (Sum.inr j)) = ∑ i, (x (i, j)) (Sum.inl i) from
        Finset.sum_congr rfl fun i _ => by
          have := DFunLike.congr_fun (hvalid (i, j)) (Sum.inr j)
          simp [xyMon, Finsupp.single_apply] at this; exact this] at h
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun i _ => by
        have := DFunLike.congr_fun (hvalid (i, j')) (Sum.inr j)
        simp [xyMon, Finsupp.single_apply, hj'] at this; exact this
    · exact fun h' => absurd (Finset.mem_univ j) h'
  have entry_bound : ∀ (x : (Fin N × Fin N) →₀ (CauchyVars N →₀ ℕ)),
      x ∈ Finset.univ.finsuppAntidiag (bilinExponent N α β) →
      (∀ p, x p = (x p) (Sum.inl p.1) • xyMon p) →
      ∀ i j, (x (i, j)) (Sum.inl i) < n + 1 := by
    intro x hx hvalid i j
    apply Nat.lt_succ_of_le; apply le_trans _ (hα i)
    calc (x (i, j)) (Sum.inl i)
        ≤ ∑ j' : Fin N, (x (i, j')) (Sum.inl i) :=
          Finset.single_le_sum (f := fun j' => (x (i, j')) (Sum.inl i))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = α i := extract_row x hx hvalid i
  change #_ = #(Finset.univ : Finset (NNMatrixWithMarginsGen N (n := n) α β))
  apply Finset.card_bij'
    (fun x hx =>
      let hmem := (Finset.mem_filter.mp hx).1
      let hvalid := (Finset.mem_filter.mp hx).2
      ⟨fun i j => ⟨(x (i, j)) (Sum.inl i), entry_bound x hmem hvalid i j⟩,
       extract_row x hmem hvalid, extract_col x hmem hvalid⟩)
    (fun K _ =>
      Finsupp.equivFunOnFinite.symm (fun p => (K.1 p.1 p.2 : ℕ) • xyMon p))
    (fun _ _ => Finset.mem_univ _)
    (fun K _ => by
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_finsuppAntidiag]
        constructor
        · apply DFunLike.ext; intro v
          simp only [Finsupp.coe_finset_sum, Finset.sum_apply,
            Finsupp.coe_equivFunOnFinite_symm]
          cases v with
          | inl i =>
            rw [bilinExponent_inl, Fintype.sum_prod_type]
            simp only [xyMon, Finsupp.smul_apply, smul_eq_mul,
              Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
            simp [Finset.sum_ite_eq']
            exact K.2.1 i
          | inr j =>
            rw [bilinExponent_inr, Fintype.sum_prod_type, Finset.sum_comm]
            simp only [xyMon, Finsupp.smul_apply, smul_eq_mul,
              Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
            simp [Finset.sum_ite_eq']
            exact K.2.2 j
        · exact Finset.subset_univ _
      · intro p; simp [xyMon]
      )
    (fun x hx => by
      apply DFunLike.ext; intro ⟨i, j⟩
      simp only [Finsupp.coe_equivFunOnFinite_symm, xyMon]
      exact ((Finset.mem_filter.mp hx).2 (i, j)).symm)
    (fun K _ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_)
      simp [xyMon, Finsupp.single_apply])

/-- **Generalized Power Sum Cauchy Identity** (coefficient-level bilinear version):

For α β : Fin N →₀ ℕ with total degree n,

  ∑_{σ∈Sₙ} [x^α](P_σ) · [x^β](P_σ) = n! · [x^α y^β](∏_{i,j∈[N]} 1/(1-xᵢyⱼ))

where P_σ = powerSumCycleProduct N σ is the power sum product with N variables. -/
theorem powerSum_bilinear_coeff_gen (α β : Fin N →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (powerSumCycleProduct N σ) : ℚ) *
      (MvPolynomial.coeff β (powerSumCycleProduct N σ) : ℚ)) =
    (Nat.factorial n : ℚ) * MvPowerSeries.coeff (bilinExponent N (⇑α) (⇑β))
      (fullCauchyProd N ℚ) := by
  -- Rewrite each MvPolynomial coefficient as card of CycleColoringGen
  simp_rw [coeff_powerSumCycleProduct_eq_card]
  -- Rewrite Cauchy product coefficient as card of NNMatrixWithMarginsGen
  have hα' : ∀ i, (α : Fin N → ℕ) i ≤ n := by
    intro i
    have := Finset.single_le_sum (f := (⇑α : Fin N → ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  rw [fullCauchyProd_coeff_eq_card_gen N α β hα']
  -- Both sides are natural number casts; reduce to ℕ equality
  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  congr 1
  exact double_counting_gen N α β hα hβ

end

end Etingof
