import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_5
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5

/-!
# Theorem 6.8.1: Reaching Simple Roots via Reflection Functors

There exists m ∈ ℕ such that d(V⁽ᵐ⁾) = αₚ for some vertex p, where V⁽ⁱ⁾ is the
sequence obtained by repeatedly applying reflection functors.

The proof uses strong induction on the sum of coordinates ∑ dᵢ. At each step,
we find a vertex k with 0 < (Ad)_k ≤ d_k, apply simple reflection s_k, and
recurse on the result which has strictly smaller coordinate sum.

The key lemma (exists_good_vertex) is proved by contradiction using positive
definiteness of the Cartan matrix: if no such k exists, one constructs a nonzero
vector with B(v,v) = 0, violating positive definiteness.

This is the key technical step toward Gabriel's theorem.

## Mathlib correspondence

Requires the full infrastructure of reflection functors (Def 6.6.3-4),
dimension vectors, Propositions 6.6.5-6.6.8, and Lemma 6.7.2.
Not in Mathlib.
-/

/-- Iterated application of simple reflections to a vector. Given a list of vertex
indices, applies the corresponding simple reflections in order. -/
def Etingof.iteratedSimpleReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (vertices : List (Fin n)) (v : Fin n → ℤ) : Fin n → ℤ :=
  vertices.foldl (fun d i => Etingof.simpleReflection n A i d) v

namespace Etingof

open Finset Matrix

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

lemma cartanMatrix_isSymm (hadj : adj.IsSymm) :
    (cartanMatrix n adj).IsSymm := by
  show (cartanMatrix n adj)ᵀ = cartanMatrix n adj
  unfold cartanMatrix
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [show adjᵀ = adj from hadj]

/-- Simple reflection at i only changes coordinate i. -/
private lemma simpleReflection_apply_ne {A : Matrix (Fin n) (Fin n) ℤ}
    (v : Fin n → ℤ) (i j : Fin n) (hij : j ≠ i) :
    simpleReflection n A i v j = v j := by
  simp [simpleReflection, rootReflection, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, hij]

/-- Simple reflection at i changes coordinate i. For symmetric A, this equals
    v i - (A.mulVec v) i. -/
private lemma simpleReflection_apply_self {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (v : Fin n → ℤ) (i : Fin n) :
    simpleReflection n A i v i = v i - (A.mulVec v) i := by
  -- s_i(v) = v - ⟨v, A·e_i⟩ · e_i, and for symmetric A, ⟨v, A·e_i⟩ = (Av)_i
  have symm : ∀ j, A j i = A i j := fun j => congr_fun (congr_fun hA i) j
  have key : dotProduct v (A.mulVec (Pi.single i 1)) = (A.mulVec v) i := by
    simp only [dotProduct, mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm j]; ring
  simp only [simpleReflection, rootReflection, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, if_pos rfl, mul_one, key, ite_true, smul_eq_mul]

/-- Sum of coordinates after reflection. -/
lemma simpleReflection_sum {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (v : Fin n → ℤ) (i : Fin n) :
    ∑ j : Fin n, simpleReflection n A i v j = (∑ j : Fin n, v j) - (A.mulVec v) i := by
  have : ∀ j, simpleReflection n A i v j =
      v j + (if j = i then -(A.mulVec v) i else 0) := by
    intro j
    by_cases h : j = i
    · subst h; rw [simpleReflection_apply_self hA]; simp; ring
    · rw [simpleReflection_apply_ne v i j h]; simp [h]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Reflection preserves the bilinear form B(d,d). -/
lemma simpleReflection_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) (i : Fin n) :
    dotProduct (simpleReflection n (cartanMatrix n adj) i v)
      ((cartanMatrix n adj).mulVec (simpleReflection n (cartanMatrix n adj) i v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  set A := cartanMatrix n adj with hA_def
  have hAsymm := cartanMatrix_isSymm hDynkin.1
  have symm_ij : ∀ j, A j i = A i j := fun j => congr_fun (congr_fun hAsymm i) j
  set c := (A.mulVec v) i
  -- s_i(v) = v - c • Pi.single i 1 (definition of rootReflection)
  -- First show the inner product ⟨v, A·(Pi.single i 1)⟩ = c
  have hc : dotProduct v (A.mulVec (Pi.single i (1 : ℤ))) = c := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_ij j]; ring
  -- Express s_i(v) as v - c • α where α = Pi.single i 1
  have hs : simpleReflection n A i v = v - c • (Pi.single i (1 : ℤ)) := by
    ext j
    simp only [simpleReflection, rootReflection, Pi.sub_apply, Pi.smul_apply, hc]
  -- A_ii = 2 for Cartan matrix
  have hAii : A i i = 2 := by
    simp only [hA_def, cartanMatrix, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one]
    have := hDynkin.2.1 i; simp_all
  -- B(α,α) = A_ii = 2
  have hBaa : dotProduct (Pi.single i (1 : ℤ)) (A.mulVec (Pi.single i (1 : ℤ))) = 2 := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hAii
  -- Now compute using bilinearity
  rw [hs]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
  -- Also need: B(α, v) = ⟨e_i, Av⟩ = (Av)_i = c
  have hBav : dotProduct (Pi.single i (1 : ℤ)) (A.mulVec v) = c := by
    simp only [dotProduct, mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl
  rw [hc, hBaa, hBav]
  ring

/-- If d ≥ 0 and (Ad)_k ≤ d_k, then s_k(d) ≥ 0. -/
lemma simpleReflection_nonneg {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (d : Fin n → ℤ) (k : Fin n)
    (hd_pos : ∀ i, 0 ≤ d i) (hk : (A.mulVec d) k ≤ d k) :
    ∀ i, 0 ≤ simpleReflection n A k d i := by
  intro i
  by_cases h : i = k
  · subst h; rw [simpleReflection_apply_self hA]; linarith
  · rw [simpleReflection_apply_ne d k i h]; exact hd_pos i

/-- If B(v,v) = 2 with positive definite Cartan matrix, then s_k(v) ≠ 0. -/
lemma simpleReflection_nonzero
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) (k : Fin n)
    (hv_root : dotProduct v ((cartanMatrix n adj).mulVec v) = 2) :
    simpleReflection n (cartanMatrix n adj) k v ≠ 0 := by
  intro h
  have hB := simpleReflection_preserves_B hDynkin v k
  rw [h] at hB
  -- dotProduct 0 (A.mulVec 0) = 0, but hB says it equals 2
  have : dotProduct (0 : Fin n → ℤ) ((cartanMatrix n adj).mulVec (0 : Fin n → ℤ)) = 0 := by
    simp [dotProduct]
  linarith

/-- A non-negative nonzero integer vector has positive sum. -/
lemma sum_pos_of_nonneg_ne_zero
    (d : Fin n → ℤ) (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0) :
    1 ≤ ∑ i : Fin n, d i := by
  by_contra h; push_neg at h
  have hsum0 : ∑ i : Fin n, d i = 0 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hd_pos i); omega
  have : ∀ i, d i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd_pos j)).mp hsum0 i (Finset.mem_univ i)
  exact hd_nonzero (funext this)

/-- Non-negative integer entries summing to 1 means exactly one entry is 1. -/
lemma sum_one_is_simpleRoot
    (d : Fin n → ℤ) (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0)
    (hd_sum : ∑ i : Fin n, d i = 1) :
    ∃ p, d = simpleRoot n p := by
  simp only [simpleRoot]
  have ⟨p, hp⟩ : ∃ p, d p = 1 := by
    by_contra h; push_neg at h
    -- Every nonzero entry is ≥ 2 (since d ≥ 0 and no entry = 1)
    -- But d ≠ 0, so some entry ≥ 2, making ∑ d ≥ 2, contradicting ∑ d = 1
    have hne1 : ∀ i, d i ≠ 1 := h
    have ⟨i, hi⟩ : ∃ i, 0 < d i := by
      by_contra h'; push_neg at h'
      exact hd_nonzero (funext fun i => le_antisymm (h' i) (hd_pos i))
    have hi2 : 2 ≤ d i := by have := hne1 i; omega
    have : 2 ≤ ∑ j : Fin n, d j :=
      le_trans hi2 (Finset.single_le_sum (fun j _ => hd_pos j) (Finset.mem_univ i))
    linarith
  refine ⟨p, funext fun i => ?_⟩
  by_cases h : i = p
  · simp [Pi.single_apply, h, hp]
  · simp only [Pi.single_apply, if_neg h]
    -- d i ≥ 0, d p = 1, and ∑ d = 1, so d i = 0
    have h1 : d i + d p ≤ ∑ j : Fin n, d j := by
      calc d i + d p = ∑ j ∈ ({i, p} : Finset (Fin n)), d j := by
            rw [Finset.sum_pair h]
        _ ≤ ∑ j : Fin n, d j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hd_pos j)
    linarith [hd_pos i]

/-- **Key lemma**: For a positive root d with ∑ d ≥ 2, there exists k
with 0 < (Ad)_k ≤ d_k. Proof by contradiction via positive definiteness. -/
lemma exists_good_vertex
    (hDynkin : IsDynkinDiagram n adj) (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((cartanMatrix n adj).mulVec d) = 2)
    (hd_sum : 2 ≤ ∑ i : Fin n, d i) :
    ∃ k, 0 < (cartanMatrix n adj).mulVec d k ∧
         (cartanMatrix n adj).mulVec d k ≤ d k := by
  set A := cartanMatrix n adj with hA_def
  set Ad := A.mulVec d
  by_contra hcon; push_neg at hcon
  -- hcon : ∀ k, 0 < Ad k → d k < Ad k  (so Ad k ≥ d k + 1 when Ad k > 0)
  -- Step 1: Find k₀ with d_{k₀} > 0 and Ad_{k₀} > 0
  have ⟨k₀, hdk₀, hAdk₀⟩ : ∃ k, 0 < d k ∧ 0 < Ad k := by
    by_contra hall; push_neg at hall
    -- All terms d_k * Ad_k ≤ 0, contradicting B(d,d) = 2
    have : ∀ k, d k * Ad k ≤ 0 := fun k => by
      by_cases hdk : 0 < d k
      · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdk) (by linarith [hall k hdk])
      · have : d k = 0 := le_antisymm (by linarith) (hd_pos k)
        simp [this]
    have hle := Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) => this k)
    simp only [dotProduct] at hd_root
    linarith
  -- Step 2: Ad_{k₀} ≥ d_{k₀} + 1 ≥ 2
  have hAdk₀_big : 2 ≤ Ad k₀ := by
    have := hcon k₀ hAdk₀; omega
  -- Step 3: d' = d - e_{k₀} → B(d', d') = 4 - 2·Ad_{k₀} ≤ 0
  set d' : Fin n → ℤ := d - Pi.single k₀ 1
  have hAsymm := cartanMatrix_isSymm hDynkin.1
  -- B(d, e_{k₀}) = Ad_{k₀} (by symmetry of A)
  have symm_k₀ : ∀ j, A j k₀ = A k₀ j := fun j => congr_fun (congr_fun hAsymm k₀) j
  have hBde : dotProduct d (A.mulVec (Pi.single k₀ (1 : ℤ))) = Ad k₀ := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_k₀ j]; ring
  -- B(e_{k₀}, d) = Ad_{k₀}
  have hBed : dotProduct (Pi.single k₀ (1 : ℤ)) (A.mulVec d) = Ad k₀ := by
    simp only [dotProduct, mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl
  -- B(e_{k₀}, e_{k₀}) = A_{k₀,k₀} = 2
  have hBee : dotProduct (Pi.single k₀ (1 : ℤ)) (A.mulVec (Pi.single k₀ (1 : ℤ))) = 2 := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [hA_def, cartanMatrix, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one]
    have := hDynkin.2.1 k₀; simp_all
  -- B(d', d') = B(d,d) - 2·Ad_{k₀} + 2 = 4 - 2·Ad_{k₀} ≤ 0
  have hBd' : dotProduct d' (A.mulVec d') = 4 - 2 * Ad k₀ := by
    show dotProduct (d - Pi.single k₀ 1) (A.mulVec (d - Pi.single k₀ 1)) = _
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
    rw [hd_root, hBde, hBed, hBee]
    ring
  have hBd'_nonpos : dotProduct d' (A.mulVec d') ≤ 0 := by linarith
  -- Step 4: d' ≠ 0 → positive definiteness gives B(d',d') > 0, contradiction
  -- d' = 0 → d = e_{k₀} → ∑ d = 1, contradicting ∑ d ≥ 2
  by_cases hd'_zero : d' = 0
  · -- d = e_{k₀}, so ∑ d = 1
    have : d = Pi.single k₀ 1 := by
      have := sub_eq_zero.mp (funext fun j => by exact congr_fun hd'_zero j)
      exact this
    have : ∑ i : Fin n, d i = 1 := by
      rw [this]; simp [Finset.sum_ite_eq']
    linarith
  · -- d' ≠ 0: positive definiteness gives B(d', d') > 0
    have hpos_def := hDynkin.2.2.2.2
    have hpos := hpos_def d' hd'_zero
    rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
    linarith

lemma iteratedSimpleReflection_cons (A : Matrix (Fin n) (Fin n) ℤ)
    (k : Fin n) (vertices : List (Fin n)) (v : Fin n → ℤ) :
    iteratedSimpleReflection n A (k :: vertices) v =
    iteratedSimpleReflection n A vertices (simpleReflection n A k v) := by
  simp [iteratedSimpleReflection]

end Etingof

/-- For any indecomposable representation V of a Dynkin quiver, repeated application
of reflection functors eventually produces a representation whose dimension vector
is a simple root αₚ.
(Etingof Theorem 6.8.1) -/
theorem Etingof.Theorem6_8_1
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices d =
        Etingof.simpleRoot n p := by
  set A := Etingof.cartanMatrix n adj with hA_def
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  -- Strong induction on ∑ d_i (as a natural number)
  suffices h : ∀ (m : ℕ) (d : Fin n → ℤ),
      (∑ i, d i).toNat = m →
      (∀ i, 0 ≤ d i) → d ≠ 0 →
      dotProduct d (A.mulVec d) = 2 →
      ∃ (vertices : List (Fin n)) (p : Fin n),
        Etingof.iteratedSimpleReflection n A vertices d = Etingof.simpleRoot n p from
    h _ d rfl hd_pos hd_nonzero hd_root
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro d hm hd_pos hd_nonzero hd_root
    have hsum_nonneg : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd_pos i
    have hsum_pos := Etingof.sum_pos_of_nonneg_ne_zero d hd_pos hd_nonzero
    by_cases hle : ∑ i : Fin n, d i ≤ 1
    · -- Base: ∑ d = 1 → d is a simple root
      have hd_sum : ∑ i : Fin n, d i = 1 := by omega
      obtain ⟨p, hp⟩ := Etingof.sum_one_is_simpleRoot d hd_pos hd_nonzero hd_sum
      exact ⟨[], p, by simp [Etingof.iteratedSimpleReflection, hp]⟩
    · -- Inductive step: find good vertex, reflect, recurse
      push_neg at hle
      have hd_sum2 : 2 ≤ ∑ i : Fin n, d i := by omega
      obtain ⟨k, hk_pos, hk_le⟩ :=
        Etingof.exists_good_vertex hDynkin d hd_pos hd_nonzero hd_root hd_sum2
      set d' := Etingof.simpleReflection n A k d with hd'_def
      have hd'_pos := Etingof.simpleReflection_nonneg hAsymm d k hd_pos hk_le
      have hd'_nonzero := Etingof.simpleReflection_nonzero hDynkin d k hd_root
      have hd'_root : dotProduct d' (A.mulVec d') = 2 :=
        Etingof.simpleReflection_preserves_B hDynkin d k ▸ hd_root
      have hd'_sum : ∑ j, d' j = (∑ j, d j) - (A.mulVec d) k :=
        Etingof.simpleReflection_sum hAsymm d k
      have hd'_sum_lt : (∑ j, d' j).toNat < m := by
        have h1 : ∑ j, d' j < ∑ j, d j := by linarith
        have h2 : 0 ≤ ∑ j, d' j := Finset.sum_nonneg fun i _ => hd'_pos i
        omega
      obtain ⟨vertices', p, hp⟩ := ih _ hd'_sum_lt d' rfl hd'_pos hd'_nonzero hd'_root
      exact ⟨k :: vertices', p, by
        rw [Etingof.iteratedSimpleReflection_cons]; exact hp⟩
