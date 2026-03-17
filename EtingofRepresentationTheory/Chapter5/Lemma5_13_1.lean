import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Lemma 5.13.1: Young Projector Linear Functional

For x ∈ ℂ[S_n], we have a_λ · x · b_λ = ℓ_λ(x) · c_λ, where ℓ_λ is a linear
functional on ℂ[S_n]. Here a_λ = Σ_{g ∈ P_λ} g and b_λ = Σ_{g ∈ Q_λ} sign(g) · g.

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1).
-/

namespace Etingof

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-- The row symmetrizer absorbs row group elements on the right:
a_λ * of(p) = a_λ for p ∈ P_λ. -/
theorem RowSymmetrizer_mul_of_row {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ (G n) p =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Row group elements are absorbed on the left:
of(p) * a_λ = a_λ for p ∈ P_λ. -/
theorem of_row_mul_RowSymmetrizer {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) p * RowSymmetrizer n la =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Column group elements are absorbed on the left of b_λ with sign:
of(q) * b_λ = sign(q) • b_λ for q ∈ Q_λ. -/
theorem of_col_mul_ColumnAntisymmetrizer {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) q * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(q * g), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]

/-- Column group elements are absorbed on the right of b_λ with sign:
b_λ * of(q) = sign(q) • b_λ for q ∈ Q_λ. -/
theorem ColumnAntisymmetrizer_mul_of_col {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ (G n) q =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.sum_mul, Finset.smul_sum]
  simp_rw [Algebra.smul_mul_assoc, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(g * q), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  -- Goal: sg = sq * (sg * sq). Proof: sq*(sg*sq) = sq*sq*sg = 1*sg = sg
  linear_combination -((↑(↑(Equiv.Perm.sign g.val) : ℤ) : ℂ)) * hsqq

open Pointwise in
/-- Key combinatorial lemma: if σ is not in the set product P_λ · Q_λ, then
there exists a transposition t ∈ P_λ whose conjugate σ⁻¹ · t · σ lies in Q_λ.
This is the pigeonhole argument: two elements in the same row must map to the
same column under σ. -/
-- A swap of two elements in the same row belongs to the row subgroup.
private theorem swap_mem_rowSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val) :
    Equiv.swap i j ∈ RowSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

-- A swap of two elements in the same column belongs to the column subgroup.
private theorem swap_mem_colSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val) :
    Equiv.swap i j ∈ ColumnSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

-- Conjugation of a swap: σ⁻¹ * swap(i,j) * σ = swap(σ⁻¹(i), σ⁻¹(j)).
private theorem conj_swap_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ⁻¹ * Equiv.swap i j * σ = Equiv.swap (σ⁻¹ i) (σ⁻¹ j) :=
  Equiv.trans_swap_trans_symm i j σ

open Pointwise in
private theorem pigeonhole_transposition {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))) :
    ∃ t : Equiv.Perm (Fin n), Equiv.Perm.IsSwap t ∧
      t ∈ RowSubgroup n la ∧ σ⁻¹ * t * σ ∈ ColumnSubgroup n la := by
  classical
  -- The map f(k) = (rowOfPos(k), colOfPos(σ⁻¹(k))) is either non-injective (giving the
  -- transposition directly) or injective (forcing σ ∈ P_λ · Q_λ, contradiction).
  -- We show it must be non-injective.
  let parts := la.sortedParts
  let row := fun k : Fin n => rowOfPos parts k.val
  let col := fun k : Fin n => colOfPos parts k.val
  -- Either ∃ distinct i, j in same row with σ⁻¹ images in same column, or not
  by_cases h_exists : ∃ i j : Fin n, i ≠ j ∧ row i = row j ∧ col (σ⁻¹ i) = col (σ⁻¹ j)
  · -- Case 1: We found the pair — construct the transposition
    obtain ⟨i, j, hij, hrow, hcol⟩ := h_exists
    exact ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, swap_mem_rowSubgroup hrow,
      by rw [conj_swap_eq]; exact swap_mem_colSubgroup hcol⟩
  · -- Case 2: No such pair exists — derive σ ∈ P_λ · Q_λ, contradicting hσ
    push_neg at h_exists
    -- h_exists : ∀ i j, i ≠ j → row i = row j → col (σ⁻¹ i) ≠ col (σ⁻¹ j)
    -- Equivalently (via a = σ⁻¹ i, b = σ⁻¹ j): same column → different rows under σ
    exfalso
    apply hσ
    sorry

/-- For σ ∈ P_λ · Q_λ with σ = p · q, the sandwiched product equals sign(q) • c_λ. -/
private theorem sandwich_mem {n : ℕ} {la : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (p * q) * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • YoungSymmetrizer n la := by
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (RowSymmetrizer n la), RowSymmetrizer_mul_of_row p hp,
    of_col_mul_ColumnAntisymmetrizer q hq, Algebra.mul_smul_comm]
  rfl

open Pointwise in
/-- For σ ∉ P_λ · Q_λ, a sign-reversing involution shows a_λ * of(σ) * b_λ = 0. -/
private theorem sandwich_not_mem {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la = 0 := by
  classical
  obtain ⟨t, ht_swap, ht_row, ht_col⟩ := pigeonhole_transposition σ hσ
  set t' := σ⁻¹ * t * σ with ht'_def
  -- Step 1: a * of(σ) = a * of(σ) * of(t')
  have h_absorb : RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ =
      RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ t' := by
    have htσ : t * σ = σ * t' := by simp [ht'_def]; group
    calc RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ
      _ = RowSymmetrizer n la * MonoidAlgebra.of ℂ _ t * MonoidAlgebra.of ℂ _ σ := by
          rw [RowSymmetrizer_mul_of_row t ht_row]
      _ = RowSymmetrizer n la * (MonoidAlgebra.of ℂ _ t * MonoidAlgebra.of ℂ _ σ) := by
          rw [mul_assoc]
      _ = RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (t * σ) := by rw [map_mul]
      _ = RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (σ * t') := by rw [htσ]
      _ = RowSymmetrizer n la * (MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ t') := by
          rw [← map_mul]
      _ = RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ t' := by
          rw [← mul_assoc]
  -- Step 2: sign(t') = -1
  have hsign_t' : (↑(↑(Equiv.Perm.sign t') : ℤ) : ℂ) = -1 := by
    have hsign_t : Equiv.Perm.sign t = -1 := by
      obtain ⟨x, z, hxz, ht_eq⟩ := ht_swap; rw [ht_eq]; exact Equiv.Perm.sign_swap hxz
    have : Equiv.Perm.sign t' = -1 := by
      change Equiv.Perm.sign (σ⁻¹ * t * σ) = -1
      rw [map_mul, map_mul, Equiv.Perm.sign_inv, hsign_t,
        mul_comm (Equiv.Perm.sign σ) (-1 : ℤˣ), mul_assoc, Int.units_mul_self, mul_one]
    simp [this]
  -- Step 3: y = -y
  set y := RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la
  have heq : y = -y := by
    change RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la = -y
    conv_lhs => rw [h_absorb, mul_assoc,
      of_col_mul_ColumnAntisymmetrizer t' ht_col, Algebra.mul_smul_comm]
    rw [hsign_t', neg_one_smul]
  -- Step 4: y = -y → y = 0
  have h2 : y + y = 0 := by nth_rw 1 [heq]; exact neg_add_cancel y
  have h3 : (2 : ℂ) • y = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

end Etingof

open Etingof Pointwise in
/-- For x ∈ ℂ[S_n], a_λ · x · b_λ is a scalar multiple of c_λ = a_λ · b_λ.
More precisely, there exists a linear functional ℓ_λ on ℂ[S_n] such that
a_λ * x * b_λ = ℓ_λ(x) • c_λ for all x.
(Etingof Lemma 5.13.1) -/
theorem Etingof.Lemma5_13_1
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RowSymmetrizer n la * x * ColumnAntisymmetrizer n la =
        ℓ x • YoungSymmetrizer n la := by
  classical
  -- For each basis element σ, compute the coefficient
  have basis_mul : ∀ σ : Equiv.Perm (Fin n), ∃ coeff : ℂ,
      RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la =
        coeff • YoungSymmetrizer n la := by
    intro σ
    by_cases hmem : σ ∈ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
        (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))
    · obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp hmem
      exact ⟨↑(↑(Equiv.Perm.sign q) : ℤ), hpq ▸ sandwich_mem p hp q hq⟩
    · exact ⟨0, by rw [zero_smul]; exact sandwich_not_mem σ hmem⟩
  -- Extract coefficient function and build linear functional
  choose f hf using basis_mul
  -- ℓ(x) = ∑_{σ} x(σ) * f(σ), constructed via Finsupp.lsum
  let ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ :=
    Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  refine ⟨ℓ, fun x => ?_⟩
  -- Both sides are linear in x; check on basis elements
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, add_smul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hℓ : ℓ (Finsupp.single σ r) = f σ * r := by
      change (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
        (Finsupp.single σ r) = f σ * r
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : (Finsupp.single σ r : MonoidAlgebra ℂ _) = r • MonoidAlgebra.of ℂ _ σ := by
      simp [MonoidAlgebra.of_apply, mul_one]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hf, smul_smul, hℓ, mul_comm]
