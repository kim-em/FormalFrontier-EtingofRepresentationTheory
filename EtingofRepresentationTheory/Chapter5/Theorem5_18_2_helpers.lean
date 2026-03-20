import Mathlib
import EtingofRepresentationTheory.Chapter5.Lemma5_18_3

/-!
# Helper lemmas for Theorem 5.18.2: centralizer ⊆ fullDiagonalSubalgebra
-/

open scoped TensorProduct

namespace Etingof.Theorem5_18_2_Helpers

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {n : ℕ}

/-- Conjugation by reindex(σ) sends map(f) to map(f ∘ σ⁻¹). -/
lemma map_conj_reindex (f : Fin n → Module.End k V)
    (σ : Equiv.Perm (Fin n)) :
    (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap *
      PiTensorProduct.map f *
      (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap =
    PiTensorProduct.map (fun i => f (σ.symm i)) := by
  set e := PiTensorProduct.reindex k (fun _ : Fin n => V) σ
  set eL := e.toLinearMap
  set eSL := e.symm.toLinearMap
  have h := PiTensorProduct.map_comp_reindex_eq f σ
  have hee : eL * eSL = 1 := by ext v; simp [eL, eSL, Module.End.mul_eq_comp]
  calc eL * PiTensorProduct.map f * eSL
      = PiTensorProduct.map (fun i => f (σ.symm i)) * eL * eSL := by
        congr 1; exact h.symm
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) * (eL * eSL) := by
        rw [mul_assoc]
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) * 1 := by rw [hee]
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) := mul_one _

section Spanning

variable [Module.Free k V] [Module.Finite k V]

/-- map applied to End-basis elements produces the End-basis of V^⊗n. -/
lemma map_endBasis_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bV : Module.Basis ι k V)
    (q r : Fin n → ι) :
    PiTensorProduct.map (fun l => bV.«end» (q l, r l)) =
    (Basis.piTensorProduct (fun _ : Fin n => bV)).«end» (q, r) := by
  set bTP := Basis.piTensorProduct (fun _ : Fin n => bV)
  apply bTP.ext
  intro s
  -- RHS: bTP.end (q,r) applied to bTP s
  rw [Module.Basis.end_apply_apply]
  -- RHS is now: if r = s then bTP q else 0
  -- LHS: PiTensorProduct.map (...) (bTP s)
  rw [show bTP s = PiTensorProduct.tprod k (fun l => bV (s l))
      from Basis.piTensorProduct_apply _ _]
  rw [PiTensorProduct.map_tprod]
  -- LHS is now: tprod k (fun l => bV.end (q l, r l) (bV (s l)))
  -- Simplify each component
  simp_rw [Module.Basis.end_apply_apply]
  -- LHS: tprod k (fun l => if r l = s l then bV (q l) else 0)
  -- RHS: if r = s then bTP q else 0
  by_cases hrs : r = s
  · subst hrs
    simp only [ite_true]
    exact (Basis.piTensorProduct_apply (fun _ : Fin n => bV) q).symm
  · rw [if_neg hrs]
    -- Need: tprod k (fun l => if r l = s l then bV (q l) else 0) = 0
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hrs
    exact (PiTensorProduct.tprod k).map_coord_zero l (if_neg hl)

/-- The image of PiTensorProduct.map spans all of End(V^⊗n). -/
lemma map_span_eq_top :
    Submodule.span k (Set.range (fun f : Fin n → Module.End k V =>
      PiTensorProduct.map f)) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  set bV := Module.Free.chooseBasis k V
  set ι := Module.Free.ChooseBasisIndex k V
  set bTP := Basis.piTensorProduct (fun _ : Fin n => bV)
  set bEnd := bTP.«end»
  rw [show φ = ∑ qr : (Fin n → ι) × (Fin n → ι),
      bEnd.repr φ qr • bEnd qr from (bEnd.sum_repr φ).symm]
  apply Submodule.sum_mem
  intro ⟨q, r⟩ _
  apply Submodule.smul_mem
  rw [show bEnd (q, r) = PiTensorProduct.map (fun l => bV.«end» (q l, r l))
      from (map_endBasis_eq bV q r).symm]
  exact Submodule.subset_span ⟨_, rfl⟩

end Spanning

section MainProof

variable [Module.Free k V] [Module.Finite k V] [CharZero k]

/-- Alternating sum of (-1)^|S| over subsets of a nonempty finset is zero (in any field). -/
private lemma sum_powerset_neg_one_pow_card_eq_zero
    {α : Type*} {x : Finset α} (hx : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : k) ^ m.card) = 0 := by
  have hZ := Finset.sum_powerset_neg_one_pow_card_of_nonempty hx
  have : (∑ m ∈ x.powerset, (-1 : k) ^ m.card) =
      ((∑ m ∈ x.powerset, (-1 : ℤ) ^ m.card : ℤ) : k) := by
    rw [Int.cast_sum]; congr 1; ext m; simp [Int.cast_pow]
  rw [this, hZ, Int.cast_zero]

/-- Coefficient evaluation: alternating sum over supersets.
∑_{S ⊇ T, S ⊆ univ} (-1)^{n-|S|} = 1 if T = univ, 0 otherwise. -/
private lemma alternating_superset_sum (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
      (-1 : k) ^ (n - S.card)) =
    if T = Finset.univ then 1 else 0 := by
  classical
  split_ifs with hT
  · subst hT
    have : Finset.univ.powerset.filter (fun S => Finset.univ ⊆ S) =
        {(Finset.univ : Finset (Fin n))} := by
      ext S; simp [Finset.univ_subset_iff]
    rw [this, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero]
  · have hC : (Finset.univ \ T).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun h => hT (Finset.univ_subset_iff.mp h)
    rw [show ∑ S ∈ Finset.univ.powerset.filter (fun S => T ⊆ S),
          (-1 : k) ^ (n - S.card) =
        ∑ T' ∈ (Finset.univ \ T).powerset,
          (-1 : k) ^ ((Finset.univ \ T).card - T'.card) from by
      apply Finset.sum_nbij' (· \ T) (· ∪ T)
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
        exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl T)
      · intro T' hT'
        simp only [Finset.mem_powerset] at hT'
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset (hT'.trans Finset.sdiff_subset) (Finset.subset_univ T),
               Finset.subset_union_right⟩
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        exact Finset.sdiff_union_of_subset hS.2
      · intro T' hT'
        simp only [Finset.mem_powerset] at hT'
        rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint]
        exact Finset.disjoint_of_subset_left hT' disjoint_sdiff_self_left
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        congr 1
        have h1 : (S \ T).card + T.card = S.card :=
          Finset.card_sdiff_add_card_eq_card hS.2
        have h2 : ((Finset.univ : Finset (Fin n)) \ T).card + T.card =
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
        have h3 : S.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card hS.1
        have h4 : (S \ T).card ≤ ((Finset.univ : Finset (Fin n)) \ T).card :=
          Finset.card_le_card (Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl T))
        simp only [Finset.card_univ, Fintype.card_fin] at h2 h3
        omega]
    -- Now ∑_{T' ⊆ C} (-1)^{|C| - |T'|} where C = univ \ T
    -- Factor out (-1)^|C| and use alternating sum = 0
    have : ∀ T' ∈ (Finset.univ \ T).powerset,
        (-1 : k) ^ ((Finset.univ \ T).card - T'.card) =
        (-1 : k) ^ (Finset.univ \ T).card * (-1 : k) ^ T'.card := by
      intro T' hT'
      have hle := Finset.card_le_card (Finset.mem_powerset.mp hT')
      have hmul : (-1 : k) ^ ((Finset.univ \ T).card - T'.card) *
          (-1 : k) ^ T'.card = (-1 : k) ^ (Finset.univ \ T).card := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hsq : (-1 : k) ^ T'.card * (-1 : k) ^ T'.card = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc (-1 : k) ^ ((Finset.univ \ T).card - T'.card)
          = (-1 : k) ^ ((Finset.univ \ T).card - T'.card) * 1 := (mul_one _).symm
        _ = (-1 : k) ^ ((Finset.univ \ T).card - T'.card) *
            ((-1 : k) ^ T'.card * (-1 : k) ^ T'.card) := by rw [hsq]
        _ = (-1 : k) ^ ((Finset.univ \ T).card - T'.card) * (-1 : k) ^ T'.card *
            (-1 : k) ^ T'.card := by rw [mul_assoc]
        _ = (-1 : k) ^ (Finset.univ \ T).card * (-1 : k) ^ T'.card := by rw [hmul]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    rw [sum_powerset_neg_one_pow_card_eq_zero (k := k) hC, mul_zero]

/-- Multilinear polarization: ∑_σ map(f ∘ σ) = ∑_S (-1)^{n-|S|} · map(fun _ => ∑_{i∈S} f i).
This is the general polarization identity for the multilinear map PiTensorProduct.map. -/
private lemma multilinear_polarization (f : Fin n → Module.End k V) :
    ∑ σ : Equiv.Perm (Fin n),
      PiTensorProduct.map (fun i => f (σ i)) =
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : k) ^ (n - S.card)) •
        PiTensorProduct.map (fun (_ : Fin n) => ∑ i ∈ S, f i) := by
  classical
  set F := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ => V)
  -- Step 1: Expand each F(const(∑_{i∈S} f i)) using multilinearity
  conv_rhs =>
    arg 2; ext S
    rw [show (-1 : k) ^ (n - S.card) • PiTensorProduct.map (fun _ => ∑ i ∈ S, f i) =
        ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
          (-1 : k) ^ (n - S.card) • F (fun i => f (r i)) by
      rw [show PiTensorProduct.map (fun _ => ∑ i ∈ S, f i) =
          F (fun _ => ∑ i ∈ S, f i) from rfl]
      rw [MultilinearMap.map_sum_finset F (fun _ => f) (fun _ => S)]
      rw [Finset.smul_sum]]
  -- Step 2: Swap summation order
  rw [Finset.sum_comm'
    (s' := fun r => Finset.univ.powerset.filter (fun S => ∀ i, r i ∈ S))
    (t' := Fintype.piFinset (fun _ : Fin n => Finset.univ))
    (h := by
      intro S r
      simp only [Finset.mem_powerset, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ]
      tauto)]
  -- Step 3: Factor out F(f ∘ r)
  simp_rw [← Finset.sum_smul]
  -- Step 4: Evaluate coefficient
  have coeff_eq : ∀ r : Fin n → Fin n,
      (∑ S ∈ Finset.univ.powerset.filter (fun S => ∀ j, r j ∈ S),
        (-1 : k) ^ (n - S.card)) =
      if Finset.image r Finset.univ = Finset.univ then 1 else 0 := by
    intro r
    convert alternating_superset_sum (k := k) (n := n) (Finset.image r Finset.univ) using 2
    ext S; simp [Finset.subset_iff]
  simp_rw [coeff_eq]
  -- Step 5: Non-surjective terms vanish
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Step 6: Biject surjective functions with permutations
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) :=
    ⟨fun σ => σ, fun σ₁ σ₂ h => Equiv.ext (congr_fun h)⟩
  have hmap : (Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset (Fin n))).filter
        (fun x => Finset.image x Finset.univ = Finset.univ) =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).map e := by
    ext r
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
      Finset.mem_map]
    constructor
    · intro ⟨_, hr⟩
      have hsurj : Function.Surjective r := by
        intro b
        have : b ∈ Finset.image r Finset.univ := by rw [hr]; exact Finset.mem_univ b
        exact let ⟨a, _, ha⟩ := Finset.mem_image.mp this; ⟨a, ha⟩
      exact ⟨Equiv.ofBijective r
        ((Finite.surjective_iff_bijective (α := Fin n)).mp hsurj), trivial, rfl⟩
    · rintro ⟨σ, _, rfl⟩
      exact ⟨fun _ => trivial, Finset.image_univ_of_surjective σ.surjective⟩
  rw [hmap, Finset.sum_map]; rfl

/-- A symmetrized pure tensor ∑_σ map(f ∘ σ⁻¹) lies in the fullDiagonalSubalgebra.
This follows from the multilinear polarization identity. -/
lemma symmetrized_map_mem_fullDiag (f : Fin n → Module.End k V) :
    ∑ σ : Equiv.Perm (Fin n),
      PiTensorProduct.map (fun i => f (σ.symm i)) ∈
    (Lemma5_18_3.fullDiagonalSubalgebra k V n).toSubmodule := by
  -- Re-index: ∑_σ map(f ∘ σ.symm) = ∑_σ map(f ∘ σ) (substitution σ ↦ σ.symm)
  rw [show ∑ σ : Equiv.Perm (Fin n), PiTensorProduct.map (fun i => f (σ.symm i)) =
      ∑ σ : Equiv.Perm (Fin n), PiTensorProduct.map (fun i => f (σ i)) from by
    apply Fintype.sum_equiv
      (⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩ :
        Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n))
    intro σ; rfl]
  -- Apply multilinear polarization
  rw [multilinear_polarization]
  -- Each summand is a scalar multiple of map(fun _ => g), which is in fullDiag
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  exact Algebra.subset_adjoin ⟨∑ i ∈ S, f i, rfl⟩

/-- The averaging map ψ ↦ ∑_σ conj_σ(ψ) sends span{map(f)} into fullDiag.
This is the key step for centralizer ⊆ fullDiag, factored out to avoid
circular imports with Theorem5_18_2. -/
lemma avg_conj_mem_fullDiag (φ : Module.End k (⨂[k] (_ : Fin n), V))
    (hmem : φ ∈ Submodule.span k (Set.range fun f : Fin n → Module.End k V =>
        PiTensorProduct.map f)) :
    ∑ σ : Equiv.Perm (Fin n),
      (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap * φ *
      (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap ∈
    (Lemma5_18_3.fullDiagonalSubalgebra k V n).toSubmodule := by
  set fullDiag := Lemma5_18_3.fullDiagonalSubalgebra k V n
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    simp_rw [map_conj_reindex]
    exact symmetrized_map_mem_fullDiag f
  | zero => simp [fullDiag.toSubmodule.zero_mem]
  | add x y _ _ hx hy =>
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    exact fullDiag.toSubmodule.add_mem hx hy
  | smul c x _ hx =>
    simp_rw [mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
    exact fullDiag.toSubmodule.smul_mem c hx

end MainProof

end Etingof.Theorem5_18_2_Helpers
