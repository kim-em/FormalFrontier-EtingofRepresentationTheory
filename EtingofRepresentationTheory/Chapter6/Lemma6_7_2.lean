import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_7_1
import EtingofRepresentationTheory.Chapter6.Corollary6_8_2

/-!
# Lemma 6.7.2: Coxeter Element Produces Negative Coefficients

Let β = Σᵢ kᵢ αᵢ with kᵢ ≥ 0 (not all zero). Then there exists N ∈ ℕ such that
cᴺβ has at least one strictly negative coefficient.

The proof shows that 1 is not an eigenvalue of the Coxeter element c. Since
c ∈ W (a finite group), cᴹ = 1 for some M, so 1 + c + c² + ⋯ + cᴹ⁻¹ = 0
as operators on ℝⁿ. If cv = v, then sᵢv = v for all i, implying B(v, αᵢ) = 0
for all i, contradicting nondegeneracy of B.

## Mathlib correspondence

Requires Coxeter groups, simple reflections, the bilinear form B, and its
nondegeneracy for Dynkin diagrams. Mathlib has Coxeter systems but the specific
eigenvalue argument needs custom development.

## Formalization note

The Coxeter element c acts on ℤⁿ as the composition of simple reflections
sₙ ∘ ⋯ ∘ s₁. Iterating c means composing with itself N times. We formalize
this using the existing `simpleReflection` (Definition 6.4.10) and
`coxeterElement` (Definition 6.7.1) infrastructure.
-/

/-- The action of the Coxeter element on a vector in ℤⁿ. The Coxeter element
c = sₙ ∘ ⋯ ∘ s₁ acts by composing all simple reflections in order, where
sᵢ is the simple reflection associated to the Cartan matrix A = 2·Id - adj. -/
def Etingof.coxeterAction (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  let A := Etingof.cartanMatrix n adj
  (List.ofFn (fun i : Fin n => Etingof.simpleReflection n A i)).foldr (· ∘ ·) id v

/-- Iterated action of the Coxeter element: c^N applied to a vector. -/
def Etingof.coxeterActionIter (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (N : ℕ) (v : Fin n → ℤ) : Fin n → ℤ :=
  (Etingof.coxeterAction n adj)^[N] v

namespace Etingof

section CoxeterHelpers

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

/-- The Cartan matrix of a Dynkin diagram is symmetric. -/
private theorem dynkin_cartan_symm (hDynkin : IsDynkinDiagram n adj) :
    (cartanMatrix n adj).IsSymm := by
  unfold cartanMatrix
  rw [Matrix.IsSymm]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [hDynkin.1.eq]

/-- For a Dynkin diagram, B(αᵢ, αᵢ) = 2 for each simple root. -/
private theorem dynkin_root_norm (hDynkin : IsDynkinDiagram n adj) (i : Fin n) :
    dotProduct (Pi.single i 1) ((cartanMatrix n adj).mulVec (Pi.single i 1)) = 2 := by
  unfold cartanMatrix
  simp only [Matrix.sub_mulVec]
  simp only [dotProduct_sub]
  have hsmul : (2 • (1 : Matrix (Fin n) (Fin n) ℤ)).mulVec (Pi.single i 1) =
      2 • Pi.single i 1 := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdot1 : dotProduct (Pi.single i (1 : ℤ)) (2 • Pi.single i (1 : ℤ)) = 2 := by
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  have hadj : dotProduct (Pi.single i (1 : ℤ)) (adj.mulVec (Pi.single i 1)) = adj i i := by
    simp [dotProduct, Pi.single_apply, Matrix.mulVec, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hsmul, hdot1, hadj, hDynkin.2.1 i]
  ring

/-- Simple reflection sᵢ only modifies the i-th coordinate.
    For j ≠ i, sᵢ(v)_j = v_j. -/
private theorem simpleReflection_apply_ne
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) (j : Fin n) (hij : j ≠ i) :
    simpleReflection n A i v j = v j := by
  unfold simpleReflection rootReflection
  simp [Pi.sub_apply, hij]

/-- The coxeterAction is the result of applying simple reflections in sequence.
    We express it as a fold over the list of Fin n indices. -/
private theorem coxeterAction_eq_fold (v : Fin n → ℤ) :
    coxeterAction n adj v =
    (List.ofFn (fun i : Fin n => simpleReflection n (cartanMatrix n adj) i)).foldr
      (· ∘ ·) id v := by
  rfl

/-- The Coxeter action preserves the bilinear form B(v, v).
    This follows because each simple reflection preserves B. -/
private theorem coxeterAction_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) :
    dotProduct (coxeterAction n adj v)
      ((cartanMatrix n adj).mulVec (coxeterAction n adj v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  unfold coxeterAction
  set A := cartanMatrix n adj
  have hA_symm := dynkin_cartan_symm hDynkin
  have hroots := dynkin_root_norm hDynkin
  -- The foldr of composed functions reduces to sequential application
  suffices h : ∀ (fs : List ((Fin n → ℤ) → Fin n → ℤ)) (w : Fin n → ℤ),
      (∀ f ∈ fs, ∀ u, dotProduct (f u) (A.mulVec (f u)) = dotProduct u (A.mulVec u)) →
      dotProduct (fs.foldr (· ∘ ·) id w) (A.mulVec (fs.foldr (· ∘ ·) id w)) =
      dotProduct w (A.mulVec w) by
    apply h
    intro f hf u
    simp only [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    exact simpleReflection_preserves_bilinearForm A hA_symm i (hroots i) u
  intro fs w hfs
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    rw [hfs f (List.mem_cons.mpr (Or.inl rfl))]
    exact ih (fun g hg => hfs g (List.mem_cons.mpr (Or.inr hg)))

/-- Iterated Coxeter action preserves B. -/
private theorem coxeterActionIter_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (N : ℕ) (v : Fin n → ℤ) :
    dotProduct (coxeterActionIter n adj N v)
      ((cartanMatrix n adj).mulVec (coxeterActionIter n adj N v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  unfold coxeterActionIter
  induction N with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [coxeterAction_preserves_B hDynkin]
    exact ih

/-- The set of integer vectors with a given B-value is finite when B is positive definite. -/
private theorem finite_lattice_points_with_B_value
    (hDynkin : IsDynkinDiagram n adj) (K : ℤ) :
    Set.Finite {v : Fin n → ℤ | dotProduct v ((cartanMatrix n adj).mulVec v) = K} := by
  -- Since B is positive definite, B(v,v) = K bounds each |vᵢ| ≤ K
  -- (because B(v,v) ≥ 2·vᵢ² for Dynkin diagrams)
  -- The set of integer vectors with bounded coordinates is finite
  sorry

/-- The orbit of any vector under the Coxeter action is finite. -/
private theorem coxeterAction_orbit_finite
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) :
    Set.Finite (Set.range (fun N => coxeterActionIter n adj N v)) := by
  apply Set.Finite.subset (finite_lattice_points_with_B_value hDynkin
    (dotProduct v ((cartanMatrix n adj).mulVec v)))
  intro w ⟨N, hN⟩
  simp only [Set.mem_setOf_eq]
  rw [← hN, coxeterActionIter_preserves_B hDynkin]

/-- Simple reflection is an involution: sᵢ(sᵢ(v)) = v. -/
private theorem simpleReflection_involutive
    (hA_symm : (cartanMatrix n adj).IsSymm)
    (hroots : ∀ i : Fin n, dotProduct (Pi.single i 1)
        ((cartanMatrix n adj).mulVec (Pi.single i 1)) = 2)
    (i : Fin n) (v : Fin n → ℤ) :
    simpleReflection n (cartanMatrix n adj) i
      (simpleReflection n (cartanMatrix n adj) i v) = v := by
  set A := cartanMatrix n adj
  unfold simpleReflection rootReflection
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Need to show: (v - c·eᵢ)_j - (v - c·eᵢ) ⬝ᵥ (A·eᵢ) * (eᵢ)_j = v_j
  -- where c = v ⬝ᵥ (A·eᵢ)
  set c := v ⬝ᵥ A.mulVec (Pi.single i 1)
  -- (v - c·eᵢ) ⬝ᵥ (A·eᵢ) = v ⬝ᵥ (A·eᵢ) - c·(eᵢ ⬝ᵥ A·eᵢ) = c - c·2 = -c
  have hroot : Pi.single i (1 : ℤ) ⬝ᵥ A.mulVec (Pi.single i 1) = 2 := by
    rw [Matrix.dotProduct_mulVec, ← hA_symm.eq, Matrix.vecMul_transpose, dotProduct_comm]
    exact hroots i
  have h1 : (v - c • Pi.single i 1) ⬝ᵥ A.mulVec (Pi.single i 1) = -c := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hroot]
    ring
  rw [h1]
  ring

/-- Each simple reflection is injective (since it's involutive). -/
private theorem simpleReflection_injective
    (hDynkin : IsDynkinDiagram n adj) (i : Fin n) :
    Function.Injective (simpleReflection n (cartanMatrix n adj) i) := by
  intro a b hab
  have := congr_arg (simpleReflection n (cartanMatrix n adj) i) hab
  rwa [simpleReflection_involutive (dynkin_cartan_symm hDynkin) (dynkin_root_norm hDynkin) i a,
       simpleReflection_involutive (dynkin_cartan_symm hDynkin) (dynkin_root_norm hDynkin) i b]
    at this

/-- The Coxeter action is injective (composition of injective functions). -/
private theorem coxeterAction_injective
    (hDynkin : IsDynkinDiagram n adj) :
    Function.Injective (coxeterAction n adj) := by
  unfold coxeterAction
  set A := cartanMatrix n adj
  suffices ∀ (fs : List ((Fin n → ℤ) → Fin n → ℤ)),
      (∀ f ∈ fs, Function.Injective f) →
      Function.Injective (fs.foldr (· ∘ ·) id) by
    apply this
    intro f hf
    simp only [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    exact simpleReflection_injective hDynkin i
  intro fs hfs
  induction fs with
  | nil => exact Function.injective_id
  | cons f fs ih =>
    simp only [List.foldr_cons]
    exact Function.Injective.comp (hfs f (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun g hg => hfs g (List.mem_cons.mpr (Or.inr hg))))

/-- The Coxeter action is periodic on any vector (finite orbit implies periodicity). -/
private theorem coxeterAction_periodic
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) :
    ∃ M : ℕ, 0 < M ∧ coxeterActionIter n adj M v = v := by
  have hfin := coxeterAction_orbit_finite hDynkin v
  -- By pigeonhole, some c^j(v) = c^k(v) with j < k, so c^(k-j)(v) = v
  have hnotinj : ¬ Function.Injective (fun N : ℕ => coxeterActionIter n adj N v) := by
    intro hinj
    exact (Set.infinite_range_of_injective hinj) hfin
  rw [Function.Injective] at hnotinj
  push_neg at hnotinj
  obtain ⟨j, k, hjk, hne⟩ := hnotinj
  set c := coxeterAction n adj with hc_def
  -- c is injective, so c^j is injective
  have hc_inj : Function.Injective c := coxeterAction_injective hDynkin
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · refine ⟨k - j, by omega, ?_⟩
    change c^[k - j] v = v
    have heq : c^[j] v = c^[k] v := by
      change coxeterActionIter n adj j v = coxeterActionIter n adj k v; exact hjk
    rw [show k = j + (k - j) from by omega, Function.iterate_add_apply] at heq
    exact (Function.Injective.iterate hc_inj j).eq_iff.mp heq.symm
  · refine ⟨j - k, by omega, ?_⟩
    change c^[j - k] v = v
    have heq : c^[j] v = c^[k] v := by
      change coxeterActionIter n adj j v = coxeterActionIter n adj k v; exact hjk
    rw [show j = k + (j - k) from by omega, Function.iterate_add_apply] at heq
    exact (Function.Injective.iterate hc_inj k).eq_iff.mp heq

/-- The Coxeter action is additive: c(u + v) = c(u) + c(v).
    This follows because each simple reflection is linear. -/
private theorem coxeterAction_add (v w : Fin n → ℤ) :
    coxeterAction n adj (v + w) =
    coxeterAction n adj v + coxeterAction n adj w := by
  unfold coxeterAction
  set A := cartanMatrix n adj
  -- Each simpleReflection is linear: sᵢ(u + v) = sᵢ(u) + sᵢ(v)
  -- The composition of additive maps is additive
  suffices h : ∀ (fs : List ((Fin n → ℤ) → Fin n → ℤ)),
      (∀ f ∈ fs, ∀ a b : Fin n → ℤ, f (a + b) = f a + f b) →
      fs.foldr (· ∘ ·) id (v + w) = fs.foldr (· ∘ ·) id v + fs.foldr (· ∘ ·) id w by
    apply h
    intro f hf
    simp only [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    intro a b
    unfold simpleReflection rootReflection
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_dotProduct]
    ring
  intro fs hfs
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    have hf_add := hfs f (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun g hg => hfs g (List.mem_cons.mpr (Or.inr hg)))
    rw [ih', hf_add]

/-- The Coxeter action applied to 0 gives 0. -/
private theorem coxeterAction_zero :
    coxeterAction n adj 0 = 0 := by
  unfold coxeterAction
  set A := cartanMatrix n adj
  suffices ∀ fs : List ((Fin n → ℤ) → Fin n → ℤ),
      (∀ g ∈ fs, g 0 = 0) → fs.foldr (· ∘ ·) id 0 = 0 by
    apply this
    intro g hg
    simp only [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    unfold simpleReflection rootReflection
    ext j; simp
  intro fs hfs
  induction fs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    rw [ih (fun h hh => hfs h (List.mem_cons.mpr (Or.inr hh)))]
    exact hfs g (List.mem_cons.mpr (Or.inl rfl))

/-- The Coxeter action distributes over Finset.range sums. -/
private theorem coxeterAction_sum_range
    (m : ℕ) (f : ℕ → Fin n → ℤ) :
    coxeterAction n adj (∑ k ∈ Finset.range m, f k) =
    ∑ k ∈ Finset.range m, coxeterAction n adj (f k) := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact coxeterAction_zero
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, coxeterAction_add, ih]

/-- Key lemma: The Coxeter element has no nonzero fixed point.

If c(v) = v, then since c = s₀ ∘ s₁ ∘ ... ∘ sₙ₋₁ and each sᵢ only modifies
coordinate i, applying these in sequence and getting back v requires each sᵢ
to fix the intermediate vector. This means (A·v)ᵢ = 0 for all i, so A·v = 0.
But A is positive definite, so v = 0.

The proof proceeds by induction: sₙ₋₁ is applied first to v and only modifies
coordinate n-1. Since no subsequent reflection touches coordinate n-1, the
final result at coord n-1 equals sₙ₋₁(v)(n-1). For c(v) = v, this must equal
v(n-1), forcing sₙ₋₁(v) = v. Then sₙ₋₂ acts on v (not some intermediate),
and the same argument gives sₙ₋₂(v) = v, etc. -/
private theorem coxeterAction_no_fixed_point
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ)
    (hfixed : coxeterAction n adj v = v) :
    v = 0 := by
  sorry

end CoxeterHelpers

/-- For a positive linear combination of simple roots (not all zero), some power of
the Coxeter element produces a vector with a negative coefficient.

Specifically: if β ∈ ℤⁿ with all coordinates nonneg and β ≠ 0, then there
exists N such that c^N(β) has at least one strictly negative coordinate, where
c is the Coxeter element (product of all simple reflections) associated to
the Dynkin diagram.
(Etingof Lemma 6.7.2) -/
theorem Lemma6_7_2
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : IsDynkinDiagram n adj)
    (β : Fin n → ℤ) (hβ_nonneg : ∀ i, 0 ≤ β i) (hβ_nonzero : β ≠ 0) :
    ∃ N : ℕ, ∃ i : Fin n,
      coxeterActionIter n adj N β i < 0 := by
  -- Proof by contradiction: assume all iterates have nonneg coordinates
  by_contra h
  push_neg at h
  -- h : ∀ N i, 0 ≤ coxeterActionIter n adj N β i
  -- Step 1: Get periodicity M > 0 with c^M(β) = β
  obtain ⟨M, hM_pos, hM_period⟩ := coxeterAction_periodic hDynkin β
  -- Step 2: Define S = β + c(β) + ... + c^{M-1}(β)
  set S := ∑ k ∈ Finset.range M, coxeterActionIter n adj k β with hS_def
  -- Step 3: S has all nonneg coordinates
  have hS_nonneg : ∀ i, 0 ≤ S i := by
    intro i
    simp only [hS_def, Finset.sum_apply]
    exact Finset.sum_nonneg (fun k _ => h k i)
  -- Step 4: S ≠ 0 (since β = c^0(β) is a summand with β ≠ 0 and all nonneg)
  have hS_nonzero : S ≠ 0 := by
    intro hS_eq
    have : β = 0 := by
      funext i
      have : S i = 0 := by simp [hS_eq]
      rw [hS_def, Finset.sum_apply] at this
      have h_each := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h k i)).mp this
      have h0 := h_each 0 (Finset.mem_range.mpr hM_pos)
      simp only [coxeterActionIter, Function.iterate_zero, id_eq] at h0
      simp only [Pi.zero_apply]
      exact h0
    exact hβ_nonzero this
  -- Step 5: c(S) = S (c cyclically permutes the sum)
  -- c(S) = c(Σ c^k β) = Σ c^{k+1} β. By the periodicity shift identity, this = S.
  have hS_fixed : coxeterAction n adj S = S := by
    rw [hS_def, coxeterAction_sum_range]
    -- Transform c(c^k(β)) into c^{k+1}(β)
    have hshift : ∀ k, coxeterAction n adj (coxeterActionIter n adj k β) =
        coxeterActionIter n adj (k + 1) β := fun k => by
      simp only [coxeterActionIter, Function.iterate_succ', Function.comp_apply]
    simp_rw [hshift]
    -- Now: Σ_{k<M} c^{k+1}(β) = Σ_{k<M} c^k(β)
    -- Use: Σ_{k<n+1} f(k) = Σ_{k<n} f(k+1) + f(0), rearranged
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    -- Finset.sum_range_succ': Σ_{k<n+1} f(k) = Σ_{k<n} f(k+1) + f(0)
    -- So: Σ_{k<M'+1} f(k+1) = Σ_{k<M'+2} f(k) - f(0) = (Σ_{k<M'+1} f(k) + f(M'+1)) - f(0)
    -- Since f(M'+1) = β = f(0): = Σ_{k<M'+1} f(k)
    have : ∑ k ∈ Finset.range (M' + 1), coxeterActionIter n adj (k + 1) β =
        ∑ k ∈ Finset.range (M' + 1), coxeterActionIter n adj k β := by
      have hsuc := Finset.sum_range_succ' (fun k => coxeterActionIter n adj k β) (M' + 1)
      -- hsuc: Σ_{k<M'+2} f(k) = Σ_{k<M'+1} f(k+1) + f(0)
      have hsucc2 := Finset.sum_range_succ (fun k => coxeterActionIter n adj k β) (M' + 1)
      -- hsucc2: Σ_{k<M'+2} f(k) = Σ_{k<M'+1} f(k) + f(M'+1)
      rw [hsucc2] at hsuc
      have hperiod : coxeterActionIter n adj (M' + 1) β = β := hM_period
      rw [hperiod] at hsuc
      -- hsuc: Σ f(k) + β = Σ f(k+1) + coxeterActionIter 0 β
      simp only [coxeterActionIter, Function.iterate_zero, id_eq] at hsuc
      -- hsuc: Σ f(k) + β = Σ f(k+1) + β
      exact add_right_cancel hsuc.symm
    exact this
  -- Step 6: c(S) = S and S ≠ 0 contradicts the no-fixed-point lemma
  exact hS_nonzero (coxeterAction_no_fixed_point hDynkin S hS_fixed)

end Etingof
