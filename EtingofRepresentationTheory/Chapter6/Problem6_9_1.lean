import Mathlib

open Matrix in
/-- The k-th power of the shift matrix has entry 1 at position (i, j) iff i = j + k. -/
private lemma shift_matrix_pow_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ (a b : Fin n), S a b = if a.val = b.val + 1 then 1 else 0)
    (k : ℕ) : ∀ (i j : Fin n),
    (S ^ k) i j = if i.val = j.val + k then 1 else 0 := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, one_apply, Nat.add_zero, Fin.ext_iff]
  | succ k ih =>
    intro i j
    rw [pow_succ', mul_apply]
    simp_rw [hS, ih]
    split_ifs with h
    · have hm : j.val + k < n := by omega
      rw [Finset.sum_eq_single ⟨j.val + k, hm⟩]
      · simp [show i.val = (j.val + k) + 1 from by omega]
      · intro m _ hne
        simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
        split_ifs with h1 h2
        · exact absurd (Fin.ext (by omega)) hne
        all_goals rfl
      · simp
    · apply Finset.sum_eq_zero
      intro m _
      simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      split_ifs with h1 h2
      · exact absurd (by omega : i.val = j.val + (k + 1)) h
      all_goals rfl

/-!
# Problem 6.9.1: Classification of Indecomposable Representations of Q₂

The cyclic quiver Q₂ has 2 vertices connected by 2 oriented edges forming a cycle:
a pair of linear operators A : V → W and B : W → V.

The classification states that every indecomposable representation of Q₂ belongs to
exactly one of four families:

1. **E_{n,λ}** (n ≥ 1, λ ∈ ℂ): V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id
2. **E_{n,∞}** (n ≥ 1): obtained from E_{n,0} by exchanging V ↔ W and A ↔ B
3. **H_n** (n ≥ 1): V = ℂⁿ, W = ℂⁿ⁻¹, A sends basis vᵢ to wᵢ (i < n), vₙ to 0,
   B sends wᵢ to v_{i+1}
4. **K_n** (n ≥ 1): obtained from H_n by exchanging V ↔ W and A ↔ B

## Mathlib correspondence

Not in Mathlib. The classification relies on the Jordan normal form theorem and
a chain decomposition argument for nilpotent operators.
-/

/-- A representation of the cyclic quiver Q₂: a pair of vector spaces V, W with
linear maps A : V → W and B : W → V. -/
structure Q₂Rep (k : Type*) [Field k] where
  V : Type*
  W : Type*
  [instACV : AddCommGroup V]
  [instModV : Module k V]
  [instFDV : FiniteDimensional k V]
  [instACW : AddCommGroup W]
  [instModW : Module k W]
  [instFDW : FiniteDimensional k W]
  A : V →ₗ[k] W
  B : W →ₗ[k] V

attribute [instance] Q₂Rep.instACV Q₂Rep.instModV Q₂Rep.instFDV
  Q₂Rep.instACW Q₂Rep.instModW Q₂Rep.instFDW

/-- Swap V ↔ W and A ↔ B. -/
def Q₂Rep.swap {k : Type*} [Field k] (ρ : Q₂Rep k) : Q₂Rep k where
  V := ρ.W
  W := ρ.V
  A := ρ.B
  B := ρ.A

/-- A Q₂-representation is indecomposable if it is nontrivial and for any
compatible decomposition V = V' ⊕ V'', W = W' ⊕ W'' (with A, B respecting
the decomposition), one of the summands is zero. -/
def Q₂Rep.Indecomposable {k : Type*} [Field k] (ρ : Q₂Rep k) : Prop :=
  (0 < Module.finrank k ρ.V ∨ 0 < Module.finrank k ρ.W) ∧
  ∀ (pV qV : Submodule k ρ.V) (pW qW : Submodule k ρ.W),
    IsCompl pV qV → IsCompl pW qW →
    (∀ x ∈ pV, ρ.A x ∈ pW) → (∀ x ∈ qV, ρ.A x ∈ qW) →
    (∀ x ∈ pW, ρ.B x ∈ pV) → (∀ x ∈ qW, ρ.B x ∈ qV) →
    (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥)

/-! ## Shared Fitting decomposition infrastructure for Q₂ representations -/

/-- Intertwining identity: (AB)^n ∘ A = A ∘ (BA)^n -/
private lemma Q₂Rep.intertwine_AB_A (ρ : Q₂Rep ℂ) (n : ℕ) (v : ρ.V) :
    ((ρ.A.comp ρ.B) ^ n) (ρ.A v) = ρ.A (((ρ.B.comp ρ.A) ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [show (ρ.A.comp ρ.B) (ρ.A v) = ρ.A ((ρ.B.comp ρ.A) v) from rfl, ih]

/-- Intertwining identity: (BA)^n ∘ B = B ∘ (AB)^n -/
private lemma Q₂Rep.intertwine_BA_B (ρ : Q₂Rep ℂ) (n : ℕ) (w : ρ.W) :
    ((ρ.B.comp ρ.A) ^ n) (ρ.B w) = ρ.B (((ρ.A.comp ρ.B) ^ n) w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [show (ρ.B.comp ρ.A) (ρ.B w) = ρ.B ((ρ.A.comp ρ.B) w) from rfl, ih]

private lemma Q₂Rep.ker_AB_pow_directed (ρ : Q₂Rep ℂ) :
    Directed (· ≤ ·) (fun n => LinearMap.ker ((ρ.A.comp ρ.B) ^ n)) :=
  Monotone.directed_le fun m n hmn x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show n = (n - m) + m from by omega, pow_add, Module.End.mul_apply, hx, map_zero]

private lemma Q₂Rep.ker_BA_pow_directed (ρ : Q₂Rep ℂ) :
    Directed (· ≤ ·) (fun n => LinearMap.ker ((ρ.B.comp ρ.A) ^ n)) :=
  Monotone.directed_le fun m n hmn x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show n = (n - m) + m from by omega, pow_add, Module.End.mul_apply, hx, map_zero]

/-- A maps the generalized kernel of BA into the generalized kernel of AB -/
private lemma Q₂Rep.fitting_A_ker_to_ker (ρ : Q₂Rep ℂ) (x : ρ.V)
    (hx : x ∈ ⨆ n, LinearMap.ker ((ρ.B.comp ρ.A) ^ n)) :
    ρ.A x ∈ ⨆ n, LinearMap.ker ((ρ.A.comp ρ.B) ^ n) := by
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_BA_pow_directed] at hx
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_AB_pow_directed]
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [LinearMap.mem_ker] at hn ⊢; rw [ρ.intertwine_AB_A, hn, map_zero]⟩

/-- A maps the eventual range of BA into the eventual range of AB -/
private lemma Q₂Rep.fitting_A_range_to_range (ρ : Q₂Rep ℂ) (x : ρ.V)
    (hx : x ∈ ⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n)) :
    ρ.A x ∈ ⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n) := by
  rw [Submodule.mem_iInf] at hx ⊢; intro n
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hx n)
  exact LinearMap.mem_range.mpr ⟨ρ.A y, by rw [← hy, ρ.intertwine_AB_A]⟩

/-- B maps the generalized kernel of AB into the generalized kernel of BA -/
private lemma Q₂Rep.fitting_B_ker_to_ker (ρ : Q₂Rep ℂ) (w : ρ.W)
    (hw : w ∈ ⨆ n, LinearMap.ker ((ρ.A.comp ρ.B) ^ n)) :
    ρ.B w ∈ ⨆ n, LinearMap.ker ((ρ.B.comp ρ.A) ^ n) := by
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_AB_pow_directed] at hw
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_BA_pow_directed]
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, by rw [LinearMap.mem_ker] at hn ⊢; rw [ρ.intertwine_BA_B, hn, map_zero]⟩

/-- B maps the eventual range of AB into the eventual range of BA -/
private lemma Q₂Rep.fitting_B_range_to_range (ρ : Q₂Rep ℂ) (w : ρ.W)
    (hw : w ∈ ⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n)) :
    ρ.B w ∈ ⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n) := by
  rw [Submodule.mem_iInf] at hw ⊢; intro n
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hw n)
  exact LinearMap.mem_range.mpr ⟨ρ.B y, by rw [← hy, ρ.intertwine_BA_B]⟩

/-- A is injective on the eventual range of BA (modulo the Fitting decomposition) -/
private lemma Q₂Rep.fitting_A_injective_on_range (ρ : Q₂Rep ℂ) {v₁ v₂ : ρ.V}
    (hv₁ : v₁ ∈ ⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n))
    (hv₂ : v₂ ∈ ⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n))
    (h : ρ.A v₁ = ρ.A v₂) : v₁ = v₂ := by
  have h_diff : ρ.A (v₁ - v₂) = 0 := by rw [map_sub, sub_eq_zero.mpr h]
  have h_pV : v₁ - v₂ ∈ ⨆ n, LinearMap.ker ((ρ.B.comp ρ.A) ^ n) :=
    Submodule.mem_iSup_of_mem 1 (by
      rw [pow_one, LinearMap.mem_ker, LinearMap.comp_apply, h_diff, map_zero])
  have h_qV : v₁ - v₂ ∈ ⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n) :=
    (⨅ n, LinearMap.range ((ρ.B.comp ρ.A) ^ n)).sub_mem hv₁ hv₂
  have h_bot := Submodule.mem_inf.mpr ⟨h_pV, h_qV⟩
  rw [(LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (ρ.B.comp ρ.A)).disjoint.eq_bot] at h_bot
  exact sub_eq_zero.mp h_bot

/-- B is injective on the eventual range of AB (modulo the Fitting decomposition) -/
private lemma Q₂Rep.fitting_B_injective_on_range (ρ : Q₂Rep ℂ) {w₁ w₂ : ρ.W}
    (hw₁ : w₁ ∈ ⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n))
    (hw₂ : w₂ ∈ ⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n))
    (h : ρ.B w₁ = ρ.B w₂) : w₁ = w₂ := by
  have h_diff : ρ.B (w₁ - w₂) = 0 := by rw [map_sub, sub_eq_zero.mpr h]
  have h_pW : w₁ - w₂ ∈ ⨆ n, LinearMap.ker ((ρ.A.comp ρ.B) ^ n) :=
    Submodule.mem_iSup_of_mem 1 (by
      rw [pow_one, LinearMap.mem_ker, LinearMap.comp_apply, h_diff, map_zero])
  have h_qW : w₁ - w₂ ∈ ⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n) :=
    (⨅ n, LinearMap.range ((ρ.A.comp ρ.B) ^ n)).sub_mem hw₁ hw₂
  have h_bot := Submodule.mem_inf.mpr ⟨h_pW, h_qW⟩
  rw [(LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (ρ.A.comp ρ.B)).disjoint.eq_bot] at h_bot
  exact sub_eq_zero.mp h_bot

/-- **Problem 6.9.1(a), Family E_{n,λ} (Etingof)**: For n ≥ 1 and λ ∈ ℂ,
the Q₂-representation with V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id is
indecomposable. This family is parameterized by (n, λ) ∈ ℕ₊ × ℂ. -/
noncomputable def Etingof.Q₂Rep_E (n : ℕ) (hn : 0 < n) (eigenval : ℂ) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin n)
  A := Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
    if i = j then eigenval else if i.val = j.val + 1 then 1 else 0)
  B := LinearMap.id

/-- The E_{n,λ} family is indecomposable. Key argument: since B = Id, any compatible
decomposition V = V₁ ⊕ V₂, W = W₁ ⊕ W₂ forces W₁ = V₁ and W₂ = V₂ (via dimension
counting from B mapping W₁ into V₁ and W₂ into V₂). Then A = J_n(λ) must preserve
both V₁ and V₂, but a single Jordan block has no nontrivial invariant direct summands. -/
theorem Etingof.Q₂Rep_E_indecomposable (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    (Etingof.Q₂Rep_E n hn eigenval).Indecomposable := by
  constructor
  · -- Nontriviality: dim V = n > 0
    left
    simp only [Q₂Rep_E, finrank_euclideanSpace_fin]
    exact hn
  · -- No nontrivial compatible decomposition
    intro pV qV pW qW hcV hcW hApV hAqV hBpV hBqW
    -- B = LinearMap.id, so B(pW) ⊆ pV means pW ≤ pV, B(qW) ⊆ qV means qW ≤ qV
    have hpWpV : pW ≤ pV := fun x hx => hBpV x hx
    have hqWqV : qW ≤ qV := fun x hx => hBqW x hx
    -- pW ≤ pV and qW ≤ qV force pW = pV: decompose x ∈ pV via IsCompl pW qW,
    -- the qW-component lies in pV ∩ qV = ⊥, so x ∈ pW.
    -- Show pV ≤ pW (with pW ≤ pV this gives equality)
    -- For x ∈ pV, decompose x = p + q (p ∈ pW, q ∈ qW) via IsCompl pW qW.
    -- Then q ∈ pV (since p ∈ pW ≤ pV) and q ∈ qW ≤ qV, so q ∈ pV ⊓ qV = ⊥.
    have aux : ∀ (s₁ t₁ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
        (s₂ t₂ : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        IsCompl s₁ t₁ → IsCompl s₂ t₂ → s₂ ≤ s₁ → t₂ ≤ t₁ → s₁ ≤ s₂ := by
      intro s₁ t₁ s₂ t₂ hc1 hc2 hs ht x hx
      have hx_top : x ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
      rw [← hc2.codisjoint.eq_top] at hx_top
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx_top
      have hq_s1 : q ∈ s₁ := by
        have heq : q = x + (-p) := by rw [← hpq]; abel
        rw [heq]; exact s₁.add_mem hx (s₁.neg_mem (hs hp))
      have hq_t1 : q ∈ t₁ := ht hq
      have hq_bot : q ∈ s₁ ⊓ t₁ := Submodule.mem_inf.mpr ⟨hq_s1, hq_t1⟩
      rw [hc1.disjoint.eq_bot] at hq_bot
      have hq0 : q = 0 := hq_bot
      rw [hq0, add_zero] at hpq; rwa [← hpq]
    have hpWeq : pW = pV := le_antisymm hpWpV (aux pV qV pW qW hcV hcW hpWpV hqWqV)
    have hqWeq : qW = qV := le_antisymm hqWqV (aux qV pV qW pW hcV.symm hcW.symm hqWqV hpWpV)
    -- Suffices to show pV = ⊥ ∨ qV = ⊥ (since pW = pV and qW = qV)
    suffices pV = ⊥ ∨ qV = ⊥ by
      rcases this with h | h
      · left; exact ⟨h, hpWeq ▸ h⟩
      · right; exact ⟨h, hqWeq ▸ h⟩
    -- By contradiction: assume both subspaces are nonzero
    by_contra h_both
    push_neg at h_both
    obtain ⟨hpV_ne, hqV_ne⟩ := h_both
    -- Define the nilpotent part N = A - eigenval • id (the shift matrix)
    set N : Module.End ℂ (EuclideanSpace ℂ (Fin n)) :=
      (Etingof.Q₂Rep_E n hn eigenval).A - eigenval • LinearMap.id with hN_def
    -- A preserves pV and qV (using pW = pV, qW = qV)
    have hA_pV : ∀ x ∈ pV, (Etingof.Q₂Rep_E n hn eigenval).A x ∈ pV :=
      fun x hx => hpWeq ▸ hApV x hx
    have hA_qV : ∀ x ∈ qV, (Etingof.Q₂Rep_E n hn eigenval).A x ∈ qV :=
      fun x hx => hqWeq ▸ hAqV x hx
    -- N preserves pV and qV (since A does and scalar maps preserve submodules)
    have hN_pV : ∀ x ∈ pV, N x ∈ pV := fun x hx =>
      pV.sub_mem (hA_pV x hx) (pV.smul_mem eigenval hx)
    have hN_qV : ∀ x ∈ qV, N x ∈ qV := fun x hx =>
      qV.sub_mem (hA_qV x hx) (qV.smul_mem eigenval hx)
    -- N is nilpotent: the shift matrix satisfies N^n = 0
    -- Strategy: N = toEuclideanLin(S) where S is the shift matrix, and S^n = 0
    set S := Matrix.of fun (a b : Fin n) =>
      if a.val = b.val + 1 then (1 : ℂ) else 0 with hS_def
    have hS_entry : ∀ (a b : Fin n), S a b = if a.val = b.val + 1 then 1 else 0 := by
      intro a b; simp [S, Matrix.of_apply]
    have hN_eq : N = Matrix.toEuclideanLin S := by
      -- N = toEuclideanLin(J) - eigenval • id
      --   = toEuclideanLin(J - eigenval • 1) = toEuclideanLin(S)
      -- First show J - eigenval • 1 = S as matrices
      set J := Matrix.of fun (i j : Fin n) =>
        if i = j then eigenval else if i.val = j.val + 1 then (1 : ℂ) else 0 with hJ_def
      have hmat : J - eigenval • (1 : Matrix (Fin n) (Fin n) ℂ) = S := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          Matrix.of_apply, S, J]
        by_cases h1 : i = j
        · subst h1; simp
        · simp only [h1, ↓reduceIte, mul_zero, sub_zero]
      -- Now lift to linear maps via toEuclideanLin
      -- toEuclideanLin(J - eigenval • 1) = toEuclideanLin(J) - eigenval • toEuclideanLin(1)
      --   = toEuclideanLin(J) - eigenval • id = N
      have h1 : Matrix.toEuclideanLin S = Matrix.toEuclideanLin J -
          Matrix.toEuclideanLin (eigenval • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [← map_sub, hmat]
      rw [h1, map_smul, Matrix.toLpLin_one]
      simp [N, Q₂Rep_E, J]
    have hS_pow : S ^ n = 0 := by
      ext i j
      rw [shift_matrix_pow_entry S hS_entry]
      simp only [Matrix.zero_apply]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
    have hN_nilp : IsNilpotent N :=
      ⟨n, by rw [hN_eq, ← Matrix.toLpLin_pow 2, hS_pow, map_zero]⟩
    -- N^{n-1} ≠ 0: the shift by n-1 sends e₀ to e_{n-1}
    have hN_pow_ne : N ^ (n - 1) ≠ 0 := by
      rw [hN_eq, ← Matrix.toLpLin_pow 2]
      intro h
      have hS_pow_ne : S ^ (n - 1) = 0 :=
        (Matrix.toEuclideanLin).injective (by rw [h, map_zero])
      have h0 := congr_fun (congr_fun hS_pow_ne ⟨n - 1, by omega⟩) ⟨0, hn⟩
      simp only [Matrix.zero_apply] at h0
      rw [shift_matrix_pow_entry S hS_entry _ ⟨n - 1, by omega⟩ ⟨0, hn⟩] at h0
      simp [Fin.val_mk] at h0
    -- Since pV ≠ ⊤ and qV ≠ ⊤ (from the complement being nonzero)
    have hpV_ne_top : pV ≠ ⊤ := by
      intro h
      apply hqV_ne
      have hd := hcV.disjoint.eq_bot
      rwa [h, top_inf_eq] at hd
    have hqV_ne_top : qV ≠ ⊤ := by
      intro h
      apply hpV_ne
      have hd := hcV.disjoint.eq_bot
      rwa [h, inf_top_eq] at hd
    -- finrank(pV) < n and finrank(qV) < n
    have hdim_pV : Module.finrank ℂ pV < n := by
      calc Module.finrank ℂ ↥pV
          < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.finrank_lt hpV_ne_top
        _ = n := finrank_euclideanSpace_fin
    have hdim_qV : Module.finrank ℂ qV < n := by
      calc Module.finrank ℂ ↥qV
          < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.finrank_lt hqV_ne_top
        _ = n := finrank_euclideanSpace_fin
    -- Helper: N^{n-1} kills any proper N-invariant submodule
    -- Proof: restrict N to S, it's nilpotent, Cayley-Hamilton gives (N|_S)^d = 0 where
    -- d = finrank S < n, so N^{n-1} = N^{n-1-d} ∘ N^d = 0 on S.
    have hN_kills_sub : ∀ (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        (hS : ∀ x ∈ S, N x ∈ S) → Module.finrank ℂ S < n →
        ∀ v ∈ S, (N ^ (n - 1)) v = 0 := by
      intro S hS hdimS v hv
      -- N restricted to S is nilpotent
      have hnil_S : IsNilpotent (N.restrict hS) := by
        obtain ⟨k, hk⟩ := hN_nilp
        exact ⟨k, LinearMap.ext fun ⟨m, hm⟩ => by
          rw [Module.End.pow_restrict, LinearMap.restrict_apply, LinearMap.zero_apply]
          exact Subtype.ext (show (N ^ k) m = 0 by
            exact LinearMap.congr_fun hk m)⟩
      -- By Cayley-Hamilton, (N.restrict)^{finrank S} = 0
      have hpow_S : (N.restrict hS) ^ Module.finrank ℂ ↥S = 0 := by
        have hchar := (LinearMap.isNilpotent_iff_charpoly (N.restrict hS)).mp hnil_S
        have hCH := LinearMap.aeval_self_charpoly (N.restrict hS)
        rw [hchar, Polynomial.aeval_X_pow] at hCH
        exact hCH
      -- So N^{finrank S} kills S
      have hkill : (N ^ Module.finrank ℂ ↥S) v = 0 := by
        have h := LinearMap.congr_fun hpow_S ⟨v, hv⟩
        rw [Module.End.pow_restrict, LinearMap.restrict_apply, LinearMap.zero_apply] at h
        exact congr_arg Subtype.val h
      -- N^{n-1} = N^{n-1-d} ∘ N^d where d = finrank S ≤ n-1
      rw [show n - 1 = (n - 1 - Module.finrank ℂ ↥S) + Module.finrank ℂ ↥S from by omega,
          pow_add, Module.End.mul_apply, hkill, map_zero]
    have hN_kills_pV : ∀ v ∈ pV, (N ^ (n - 1)) v = 0 :=
      hN_kills_sub pV hN_pV hdim_pV
    have hN_kills_qV : ∀ v ∈ qV, (N ^ (n - 1)) v = 0 :=
      hN_kills_sub qV hN_qV hdim_qV
    -- Since V = pV + qV (from IsCompl), N^{n-1} = 0 on all of V
    have hN_pow_zero : N ^ (n - 1) = 0 := by
      ext v
      simp only [LinearMap.zero_apply]
      have : v ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
      rw [← hcV.codisjoint.eq_top] at this
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp this
      rw [← hpq, map_add, hN_kills_pV p hp, hN_kills_qV q hq, add_zero]
    exact absurd hN_pow_zero hN_pow_ne

/-- **Problem 6.9.1(a), Family H_n (Etingof)**: For n ≥ 1, V = ℂⁿ with basis vᵢ,
W = ℂⁿ⁻¹ with basis wᵢ. A sends vᵢ ↦ wᵢ (i < n) and vₙ ↦ 0.
B sends wᵢ ↦ v_{i+1}. This is an indecomposable representation with dim V ≠ dim W. -/
noncomputable def Etingof.Q₂Rep_H (n : ℕ) (hn : 0 < n) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin (n - 1))
  A := Matrix.toEuclideanLin (Matrix.of fun (i : Fin (n - 1)) (j : Fin n) =>
    if i.val = j.val then (1 : ℂ) else 0)
  B := Matrix.toEuclideanLin (Matrix.of fun (i : Fin n) (j : Fin (n - 1)) =>
    if i.val = j.val + 1 then (1 : ℂ) else 0)

/-- **Problem 6.9.1(b) (Etingof)**: If AB : W → W is not nilpotent in a Q₂-representation,
then the representation decomposes as E' ⊕ E_{n,λ} for some λ ≠ 0.

This reduces the classification to the case where AB is nilpotent. -/
theorem Etingof.Problem6_9_1b (ρ : Q₂Rep ℂ)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    ∃ (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, ρ.A x ∈ pW) ∧ (∀ x ∈ qV, ρ.A x ∈ qW) ∧
      (∀ x ∈ pW, ρ.B x ∈ pV) ∧ (∀ x ∈ qW, ρ.B x ∈ qV) ∧
      -- The q-summand has equal dimensions (E_{n,λ} type with λ ≠ 0)
      Module.finrank ℂ (↥qV) = Module.finrank ℂ (↥qW) := by
  -- Fitting decomposition for AB on W and BA on V
  set AB := ρ.A.comp ρ.B with hAB_def
  set BA := ρ.B.comp ρ.A with hBA_def
  set pW := ⨆ n, LinearMap.ker (AB ^ n)
  set qW := ⨅ n, LinearMap.range (AB ^ n)
  set pV := ⨆ n, LinearMap.ker (BA ^ n)
  set qV := ⨅ n, LinearMap.range (BA ^ n)
  refine ⟨pV, qV, pW, qW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. IsCompl pV qV (Fitting for BA)
  · exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
  -- 2. IsCompl pW qW (Fitting for AB)
  · exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
  -- 3-6. A and B map Fitting subspaces to Fitting subspaces
  · exact fun x hx => ρ.fitting_A_ker_to_ker x hx
  · exact fun x hx => ρ.fitting_A_range_to_range x hx
  · exact fun x hx => ρ.fitting_B_ker_to_ker x hx
  · exact fun x hx => ρ.fitting_B_range_to_range x hx
  -- 7. dim qV = dim qW (via injectivity of restricted A and B on eventual ranges)
  · set A' : ↥qV →ₗ[ℂ] ↥qW :=
      (ρ.A.domRestrict qV).codRestrict qW (fun ⟨v, hv⟩ =>
        ρ.fitting_A_range_to_range v hv)
    set B' : ↥qW →ₗ[ℂ] ↥qV :=
      (ρ.B.domRestrict qW).codRestrict qV (fun ⟨w, hw⟩ =>
        ρ.fitting_B_range_to_range w hw)
    have hA'_inj : Function.Injective A' := by
      intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
      exact Subtype.ext (ρ.fitting_A_injective_on_range hv₁ hv₂ (by
        simpa [A', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
          using congr_arg Subtype.val h))
    have hB'_inj : Function.Injective B' := by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
      exact Subtype.ext (ρ.fitting_B_injective_on_range hw₁ hw₂ (by
        simpa [B', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
          using congr_arg Subtype.val h))
    exact le_antisymm
      (LinearMap.finrank_le_finrank_of_injective hA'_inj)
      (LinearMap.finrank_le_finrank_of_injective hB'_inj)

/-- If v₀ ∈ ker A, v₀ ≠ 0, v₀ ∉ range B, and dim W > 0, then ρ is decomposable.
Decomposition: (span{v₀}, ⊥) ⊕ (qV, ⊤) where qV contains range B. -/
private lemma Q₂Rep.decomp_of_ker_A_not_range_B (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hW_pos : 0 < Module.finrank ℂ ρ.W)
    (v₀ : ρ.V) (hv₀_ne : v₀ ≠ 0) (hv₀_kerA : ρ.A v₀ = 0)
    (hv₀_not_rangeB : v₀ ∉ LinearMap.range ρ.B) : False := by
  set V₁ := Submodule.span ℂ ({v₀} : Set ρ.V)
  set S := LinearMap.range ρ.B
  have h_disj : Disjoint V₁ S := by
    rw [disjoint_comm]; exact (Submodule.disjoint_span_singleton' hv₀_ne).mpr hv₀_not_rangeB
  obtain ⟨C, hTC⟩ := (V₁ ⊔ S).exists_isCompl
  set qV := S ⊔ C
  have hcV : IsCompl V₁ qV := by
    constructor
    · rw [disjoint_iff]
      simp only [Submodule.eq_bot_iff]
      intro x hx
      have hx₁ : x ∈ V₁ := (Submodule.mem_inf.mp hx).1
      have hx₂ : x ∈ qV := (Submodule.mem_inf.mp hx).2
      obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.mp hx₂
      have hc_T : c ∈ V₁ ⊔ S := by
        have heq : c = x - s := by rw [← hsc]; abel
        rw [heq]; exact (V₁ ⊔ S).sub_mem (Submodule.mem_sup_left hx₁) (Submodule.mem_sup_right hs)
      have hc0 : c = 0 := by
        have h := Submodule.mem_inf.mpr ⟨hc_T, hc⟩
        rwa [hTC.disjoint.eq_bot] at h
      have hxs : x = s := by rw [← hsc, hc0, add_zero]
      subst hxs
      exact h_disj.le_bot (Submodule.mem_inf.mpr ⟨hx₁, hs⟩)
    · simp only [codisjoint_iff]
      calc V₁ ⊔ qV = V₁ ⊔ (S ⊔ C) := rfl
        _ = (V₁ ⊔ S) ⊔ C := (sup_assoc _ _ _).symm
        _ = ⊤ := hTC.codisjoint.eq_top
  haveI : Nontrivial ρ.W := Module.finrank_pos_iff.mp hW_pos
  rcases hρ.2 V₁ qV ⊥ ⊤ hcV isCompl_bot_top
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hv₀_kerA])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by
      have := (Submodule.mem_bot ℂ).mp hx
      rw [this, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => (le_sup_left : S ≤ qV) (LinearMap.mem_range_self ρ.B x))
  with ⟨hV₁_bot, _⟩ | ⟨_, hqW_bot⟩
  · exact hv₀_ne (show v₀ ∈ (⊥ : Submodule ℂ ρ.V) from hV₁_bot ▸ Submodule.subset_span rfl)
  · exact absurd hqW_bot (top_ne_bot (α := Submodule ℂ ρ.W))

/-- Symmetric version: if w₀ ∈ ker B, w₀ ≠ 0, w₀ ∉ range A, and dim V > 0,
then ρ is decomposable. -/
private lemma Q₂Rep.decomp_of_ker_B_not_range_A (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (w₀ : ρ.W) (hw₀_ne : w₀ ≠ 0) (hw₀_kerB : ρ.B w₀ = 0)
    (hw₀_not_rangeA : w₀ ∉ LinearMap.range ρ.A) : False := by
  have hρ_swap : ρ.swap.Indecomposable := by
    refine ⟨hρ.1.symm, fun pW qW pV qV hcW hcV hBpW hBqW hApV hAqV => ?_⟩
    rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  exact ρ.swap.decomp_of_ker_A_not_range_B hρ_swap hV_pos w₀ hw₀_ne hw₀_kerB hw₀_not_rangeA

/-- If ρ is indecomposable with AB nilpotent and both dims > 0, then ker A ⊆ range B. -/
private lemma Q₂Rep.ker_A_sub_range_B (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    LinearMap.ker ρ.A ≤ LinearMap.range ρ.B := by
  intro v hv
  by_contra h
  exact ρ.decomp_of_ker_A_not_range_B hρ hW_pos v
    (fun h0 => by simp [h0] at h) (LinearMap.mem_ker.mp hv) h

/-- If ρ is indecomposable with AB nilpotent and both dims > 0, then ker B ⊆ range A. -/
private lemma Q₂Rep.ker_B_sub_range_A (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    LinearMap.ker ρ.B ≤ LinearMap.range ρ.A := by
  intro w hw
  by_contra h
  exact ρ.decomp_of_ker_B_not_range_A hρ hV_pos w
    (fun h0 => by simp [h0] at h) (LinearMap.mem_ker.mp hw) h

/-- The operator X(v,w) = (Bw, Av) on V × W has 1-dimensional kernel when ρ is indecomposable,
AB is nilpotent, and both V and W are nontrivial.

ker X = ker A × ker B (as sets), so dim(ker X) = dim(ker A) + dim(ker B).
The claim dim(ker X) = 1 means the nilpotent operator X has a single Jordan block
on V ⊕ W (the cyclic case). This is equivalent to the structure theorem for
finitely generated modules over k[X]/(X^N): an indecomposable module is cyclic.

The proof (following Problem 6.9.1(c) of Etingof):
- X is nilpotent (proved in `Problem6_9_1c`)
- X admits a chain basis compatible with V ⊕ W (each chain generator ∈ V or ∈ W)
- Indecomposability of ρ implies X has exactly one chain (single Jordan block)
- Therefore dim(ker X) = 1

The chain compatibility claim (generators can be chosen in V or W) uses the off-diagonal
structure of X. The single-chain deduction uses: if X had ≥ 2 chains, the V and W
components of each chain form sub-representations, giving a nontrivial decomposition.

This requires the structure theorem for modules over k[X]/(X^N), not yet in Mathlib. -/
private lemma ker_sum_ge_one (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    1 ≤ Module.finrank ℂ (LinearMap.ker ρ.A) + Module.finrank ℂ (LinearMap.ker ρ.B) := by
  -- AB nilpotent on W (dim W > 0) implies ker(AB) ≠ ⊥
  -- Then take w ∈ ker(AB) \ {0}: Bw ∈ ker A. If Bw ≠ 0 → ker A ≠ ⊥; else w ∈ ker B.
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have hA : Module.finrank ℂ (LinearMap.ker ρ.A) = 0 := by omega
  have hB : Module.finrank ℂ (LinearMap.ker ρ.B) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hA hB
  -- A is injective and B is injective
  have hA_inj : Function.Injective ρ.A := LinearMap.ker_eq_bot.mp hA
  have hB_inj : Function.Injective ρ.B := LinearMap.ker_eq_bot.mp hB
  -- AB injective → AB not nilpotent (contradiction with dim W > 0)
  have hAB_inj : Function.Injective (ρ.A.comp ρ.B) := hA_inj.comp hB_inj
  obtain ⟨N, hN⟩ := hAB
  have hW_ntriv : Nontrivial ρ.W := Module.finrank_pos_iff.mp hW_pos
  obtain ⟨w, hw⟩ := exists_ne (0 : ρ.W)
  have : (ρ.A.comp ρ.B) ^ N = 0 := hN
  have hw0 : ((ρ.A.comp ρ.B) ^ N) w = 0 := by rw [hN, LinearMap.zero_apply]
  -- But (AB)^N is injective (composition of injective maps)
  -- (AB)^N w = 0 but w ≠ 0 contradicts AB injective
  -- Use: if AB injective and (AB)^N = 0, then N = 0 or W = 0
  -- Prove: ker((AB)^n) = ⊥ for all n (by induction, using AB injective)
  suffices ∀ n, LinearMap.ker ((ρ.A.comp ρ.B) ^ n) = ⊥ by
    have hmem := LinearMap.mem_ker.mpr hw0
    rw [this N] at hmem
    exact hw ((Submodule.mem_bot ℂ).mp hmem)
  intro n; induction n with
  | zero => simp only [pow_zero, LinearMap.ker_eq_bot]; exact fun _ _ h => h
  | succ n ih =>
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at hxy
    exact LinearMap.ker_eq_bot.mp ih (hAB_inj hxy)

/-- When AB = 0, BA = 0, both ker A and ker B nontrivial, ker A ⊆ range B, ker B ⊆ range A:
the "cross-pairing" decomposition (ker A, complement of ker B) ⊕ (complement of ker A, ker B)
is a compatible Q₂-decomposition with both parts nontrivial. -/
private lemma decomp_of_AB_BA_zero (ρ : Q₂Rep ℂ)
    (hAB_zero : ρ.A.comp ρ.B = 0) (hBA_zero : ρ.B.comp ρ.A = 0)
    (hkA_pos : 0 < Module.finrank ℂ (LinearMap.ker ρ.A))
    (hkB_pos : 0 < Module.finrank ℂ (LinearMap.ker ρ.B))
    (hkA_rangeB : LinearMap.ker ρ.A ≤ LinearMap.range ρ.B)
    (hkB_rangeA : LinearMap.ker ρ.B ≤ LinearMap.range ρ.A) :
    ¬ρ.Indecomposable := by
  intro hρ
  -- ker A = range B (from AB = 0: range B ⊆ ker A, and ker A ⊆ range B)
  have hkA_eq : LinearMap.ker ρ.A = LinearMap.range ρ.B := by
    exact le_antisymm hkA_rangeB (fun w hw => by
      rw [LinearMap.mem_ker]
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hw
      exact LinearMap.congr_fun hAB_zero x)
  have hkB_eq : LinearMap.ker ρ.B = LinearMap.range ρ.A := by
    exact le_antisymm hkB_rangeA (fun v hv => by
      rw [LinearMap.mem_ker]
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
      exact LinearMap.congr_fun hBA_zero x)
  -- Get complements
  obtain ⟨qV, hcV⟩ := (LinearMap.ker ρ.A).exists_isCompl
  obtain ⟨qW, hcW⟩ := (LinearMap.ker ρ.B).exists_isCompl
  -- The cross-pairing decomposition:
  -- pV = ker A, pW = qW (complement of ker B)
  -- qV' = qV (complement of ker A), qW' = ker B
  -- Check A maps:
  -- A(ker A) = {0} ⊆ qW ✓
  -- A(qV) ⊆ range A = ker B ✓ (since BA = 0 means range A ⊆ ker B, hence = ker B)
  -- Check B maps:
  -- B(qW) ⊆ range B = ker A ✓ (since AB = 0 means range B ⊆ ker A, hence = ker A)
  -- B(ker B) = {0} ⊆ qV ✓
  have hA_pV : ∀ x ∈ LinearMap.ker ρ.A, ρ.A x ∈ qW := by
    intro x hx; rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
  have hA_qV : ∀ x ∈ qV, ρ.A x ∈ LinearMap.ker ρ.B := by
    intro x _; rw [hkB_eq]; exact LinearMap.mem_range_self ρ.A x
  have hB_qW : ∀ x ∈ qW, ρ.B x ∈ LinearMap.ker ρ.A := by
    intro x _; rw [hkA_eq]; exact LinearMap.mem_range_self ρ.B x
  have hB_kB : ∀ x ∈ LinearMap.ker ρ.B, ρ.B x ∈ qV := by
    intro x hx; rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
  -- Both summands nontrivial
  have hpV_ne : LinearMap.ker ρ.A ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hkA_pos; exact Nat.lt_irrefl 0 hkA_pos
  have hqW_ne : LinearMap.ker ρ.B ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hkB_pos; exact Nat.lt_irrefl 0 hkB_pos
  -- Apply indecomposability
  rcases hρ.2 (LinearMap.ker ρ.A) qV qW (LinearMap.ker ρ.B) hcV hcW.symm
    hA_pV hA_qV hB_qW hB_kB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hpV_ne h1
  · exact hqW_ne h2

open Polynomial in
/-- In `ℂ[X] ⧸ (X ^ n)`, any element annihilated by `X` lies in the ℂ-span of
the image of `X ^ (n - 1)`. This shows the X-torsion is at most 1-dimensional. -/
private lemma quotient_X_torsion_mem_span (n : ℕ)
    (a : ℂ[X] ⧸ Ideal.span {(X : ℂ[X]) ^ n})
    (ha : (X : ℂ[X]) • a = 0) :
    a ∈ Submodule.span ℂ ({Ideal.Quotient.mk
      (Ideal.span {(X : ℂ[X]) ^ n}) ((X : ℂ[X]) ^ (n - 1))} : Set _) := by
  obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective a
  -- X • mk(pa) = 0 means mk(X * pa) = 0, i.e., X^n ∣ X * pa
  have hmem : (X : ℂ[X]) ^ n ∣ X * pa := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] at ha
  cases n with
  | zero =>
    suffices h : (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 0})) pa = 0 by
      rw [h]; exact Submodule.zero_mem _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_zero]
    exact one_dvd pa
  | succ m =>
    -- X^(m+1) ∣ X * pa → X^m ∣ pa (cancel X in integral domain)
    rw [pow_succ'] at hmem
    have hpa : X ^ m ∣ pa :=
      (mul_dvd_mul_iff_left (Polynomial.X_ne_zero (R := ℂ))).mp hmem
    obtain ⟨q, rfl⟩ := hpa
    -- mk(X^m * q) ∈ span{mk(X^m)}, witnessed by c = q.coeff 0
    rw [Submodule.mem_span_singleton, show m + 1 - 1 = m from rfl]
    refine ⟨q.coeff 0, ?_⟩
    -- q.coeff 0 • mk(X^m) = mk(C(q.coeff 0) * X^m)
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℂ ℂ[X] _,
      Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_eq, ← map_mul]
    apply Ideal.Quotient.eq.mpr
    rw [mul_comm (C _) _, ← mul_sub, Ideal.mem_span_singleton, pow_succ]
    apply mul_dvd_mul_left
    rw [show (X : ℂ[X]) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, Polynomial.coeff_zero_eq_eval_zero]

-- PID structure theorem and direct sum manipulation require extra heartbeats
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in
/-- A nilpotent endomorphism with kernel of dimension ≥ 2 admits a nontrivial
invariant direct sum decomposition.

Case split: if ker T ⊄ range T, the elementary construction
  M₁ = span{v} (for v ∈ ker T \ range T), M₂ = range T ⊕ complement
gives the decomposition. The case ker T ⊆ range T requires the structure
theorem for modules over ℂ[X] (PID). -/
private lemma nilpotent_nontrivial_decomp {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (_hT : IsNilpotent T)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker T)) :
    ∃ (M₁ M₂ : Submodule ℂ V), M₁ ≠ ⊥ ∧ M₂ ≠ ⊥ ∧ IsCompl M₁ M₂ ∧
      (∀ v ∈ M₁, T v ∈ M₁) ∧ (∀ v ∈ M₂, T v ∈ M₂) := by
  -- Case 1: T = 0. Any nontrivial splitting works since every subspace is T-invariant.
  by_cases hT0 : T = 0
  · subst hT0
    -- dim V ≥ 2, so V has a nontrivial direct sum decomposition
    have hV : 2 ≤ Module.finrank ℂ V := le_trans hker (Submodule.finrank_le _)
    -- Pick a nonzero vector and its complement
    have : Nontrivial V := Module.finrank_pos_iff.mp (by linarith)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨M₂, hcompl⟩ := (Submodule.span ℂ {v}).exists_isCompl
    refine ⟨Submodule.span ℂ {v}, M₂, ?_, ?_, hcompl, ?_, ?_⟩
    · exact mt Submodule.span_singleton_eq_bot.mp hv
    · intro h
      have htop : Submodule.span ℂ {v} = ⊤ := eq_top_of_isCompl_bot (h ▸ hcompl)
      have h1 := finrank_span_singleton (K := ℂ) hv
      rw [htop] at h1
      simp at h1
      linarith
    · intro w _; simp
    · intro w _; simp
  -- Case 2: T ≠ 0.
  · by_cases hdisjoint : Disjoint (LinearMap.ker T) (LinearMap.range T)
    · -- Case 2a: ker T ∩ range T = 0. Use ker T and range T directly.
      refine ⟨LinearMap.ker T, LinearMap.range T, ?_, ?_, ?_, ?_, ?_⟩
      · -- ker T ≠ ⊥
        intro h; rw [h, finrank_bot] at hker; omega
      · -- range T ≠ ⊥
        rwa [ne_eq, LinearMap.range_eq_bot]
      · -- IsCompl: disjoint + dimensions add up
        have hdim := T.finrank_range_add_finrank_ker
        exact (Submodule.isCompl_iff_disjoint _ _
          (by linarith)).mpr hdisjoint
      · -- T-invariance of ker T
        intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        simp [hv]
      · -- T-invariance of range T
        intro v hv
        exact ⟨v, rfl⟩
    · -- Case 2b: ker T ∩ range T ≠ 0.
      -- Sub-case split: is there v ∈ ker T \ range T?
      by_cases hkR : LinearMap.ker T ≤ LinearMap.range T
      · -- Case 2b-ii: ker T ⊆ range T. Use PID structure theorem.
        -- View V as an X-torsion ℂ[X]-module via AEval'.
        open Polynomial in
        have htors : Module.IsTorsion' (Module.AEval' (R := ℂ) T)
            (Submonoid.powers (X : ℂ[X])) := by
          obtain ⟨n, hn⟩ := _hT
          intro m
          refine ⟨⟨X ^ n, n, rfl⟩, ?_⟩
          set v := (Module.AEval'.of (R := ℂ) T).symm m
          have hm : m = Module.AEval'.of T v := (LinearEquiv.apply_symm_apply _ m).symm
          rw [hm, Submonoid.smul_def, Module.AEval'.X_pow_smul_of,
            LinearEquiv.map_eq_zero_iff]
          show (T ^ n) v = 0
          simp [hn]
        -- Apply PID structure theorem: AEval' T ≅ ⨁ (i : Fin d) ℂ[X]/(X^kᵢ)
        open Polynomial in
        obtain ⟨d, k, ⟨e⟩⟩ := Module.torsion_by_prime_power_decomposition
          Polynomial.irreducible_X htors
        -- d ≥ 2: each summand contributes 1 to dim(ker T), and dim(ker T) ≥ 2
        have hd : 2 ≤ d := by
          by_contra hd_lt
          push_neg at hd_lt
          interval_cases d
          · -- d = 0: direct sum is trivial, V = 0, contradicts dim(ker T) ≥ 2
            have hsub : Subsingleton V := by
              constructor
              intro a b
              have ha : e (Module.AEval'.of (R := ℂ) T a) = 0 :=
                DFinsupp.ext (fun i => Fin.elim0 i)
              have hb : e (Module.AEval'.of (R := ℂ) T b) = 0 :=
                DFinsupp.ext (fun i => Fin.elim0 i)
              have := e.injective (ha.trans hb.symm)
              exact (Module.AEval'.of (R := ℂ) T).injective this
            haveI := hsub
            have : Module.finrank ℂ V = 0 := Module.finrank_zero_of_subsingleton
            have := Submodule.finrank_le (LinearMap.ker T)
            omega
          · -- d = 1: AEval' T ≅ ℂ[X]/(X^k₀), ker T has dim ≤ 1
            exfalso
            have h1 : Module.finrank ℂ (LinearMap.ker T) ≤ 1 := by
              set j₀ : Fin 1 := ⟨0, by omega⟩
              set gen := (Submodule.Quotient.mk ((X : ℂ[X]) ^ (k j₀ - 1)) :
                ℂ[X] ⧸ ℂ[X] ∙ X ^ k j₀)
              set w : V := (Module.AEval'.of (R := ℂ) T).symm
                (e.symm (DirectSum.of _ j₀ gen)) with hw_def
              suffices h_le : LinearMap.ker T ≤ Submodule.span ℂ ({w} : Set V) by
                exact (Submodule.finrank_mono h_le).trans
                  ((finrank_span_le_card ({w} : Set V)).trans (by simp))
              intro v hv
              rw [LinearMap.mem_ker] at hv
              -- e(AEval'.of T v) has X • it = 0
              have hX_tors : (X : ℂ[X]) • e (Module.AEval'.of (R := ℂ) T v) = 0 := by
                have h := e.map_smul (X : ℂ[X]) (Module.AEval'.of (R := ℂ) T v)
                rw [Module.AEval'.X_smul_of, hv, map_zero, map_zero] at h
                exact h.symm
              -- Component j₀ also has X • it = 0
              set c₀ := DirectSum.component ℂ[X] _ _ j₀ (e (Module.AEval'.of (R := ℂ) T v))
              have hc₀_tors : (X : ℂ[X]) • c₀ = 0 := by
                have h := (DirectSum.component ℂ[X] _ _ j₀).map_smul
                  (X : ℂ[X]) (e (Module.AEval'.of (R := ℂ) T v))
                rw [hX_tors, map_zero] at h; exact h.symm
              -- By quotient_X_torsion_mem_span, c₀ = c • X^(k₀-1) for some c
              have hc₀_span := quotient_X_torsion_mem_span (k j₀) c₀ hc₀_tors
              rw [Submodule.mem_span_singleton] at hc₀_span
              obtain ⟨c, hc⟩ := hc₀_span
              -- Reconstruct: for Fin 1, the direct sum element = of j₀ (component j₀)
              have hds_eq : e (Module.AEval'.of (R := ℂ) T v) = DirectSum.of _ j₀ c₀ := by
                apply DFinsupp.ext; intro ⟨i, hi⟩
                have : i = 0 := by omega
                subst this
                rw [DirectSum.of_eq_same]; rfl
              -- v = c • w: both map to the same element under e ∘ AEval'.of
              have hv_eq : v = c • w := by
                apply (Module.AEval'.of (R := ℂ) T).injective
                apply e.injective
                -- LHS = of j₀ (c • gen)
                have lhs : e (Module.AEval'.of (R := ℂ) T v) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [hds_eq]; congr 1; exact hc.symm
                -- RHS = of j₀ (c • gen)
                have rhs : e (Module.AEval'.of (R := ℂ) T (c • w)) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [map_smul, hw_def, LinearEquiv.apply_symm_apply]
                  -- Goal: e (c • e.symm (of j₀ gen)) = of j₀ (c • gen)
                  conv_lhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c
                      (e.symm (DirectSum.of _ j₀ gen))]
                  rw [e.map_smul, LinearEquiv.apply_symm_apply]
                  -- Goal: (algebraMap ℂ ℂ[X] c) • of j₀ gen = of j₀ (c • gen)
                  conv_rhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c gen]
                  exact ((DirectSum.lof ℂ[X] (Fin 1)
                    (fun i => ℂ[X] ⧸ ℂ[X] ∙ X ^ k i) j₀).map_smul _ gen).symm
                exact lhs.trans rhs.symm
              rw [hv_eq]
              exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
            omega
        -- Split the direct sum: one nontrivial summand vs the rest
        -- Define ℂ[X]-submodules of AEval' T via the isomorphism e
        let N : Fin d → Type := fun i => ℂ[X] ⧸ ℂ[X] ∙ (X : ℂ[X]) ^ k i
        -- Helper: N j is subsingleton when k j = 0
        have N_subsingleton : ∀ j, k j = 0 → Subsingleton (N j) := by
          intro j hj
          exact Submodule.Quotient.subsingleton_iff.mpr
            (by rw [hj, pow_zero]; exact Ideal.span_singleton_one)
        -- At least two summands are nontrivial (k > 0), otherwise dim(ker T) ≤ 1
        obtain ⟨j₀, j₁, hkj₀, hkj₁, hne⟩ :
            ∃ j₀ j₁ : Fin d, 0 < k j₀ ∧ 0 < k j₁ ∧ j₀ ≠ j₁ := by
          by_contra hall
          push_neg at hall
          -- hall : ∀ a b, 0 < k a → 0 < k b → a = b
          -- At most one index has k > 0. Show finrank(ker T) ≤ 1.
          exfalso
          have hker_le : Module.finrank ℂ (LinearMap.ker T) ≤ 1 := by
            by_cases hk_all : ∀ j : Fin d, k j = 0
            · -- All summands trivial → V ≅ 0
              haveI : Subsingleton V := by
                constructor; intro a b
                have ha : e (Module.AEval'.of (R := ℂ) T a) = 0 :=
                  DFinsupp.ext (fun j => (N_subsingleton j (hk_all j)).elim _ _)
                have hb : e (Module.AEval'.of (R := ℂ) T b) = 0 :=
                  DFinsupp.ext (fun j => (N_subsingleton j (hk_all j)).elim _ _)
                exact (Module.AEval'.of (R := ℂ) T).injective (e.injective (ha.trans hb.symm))
              have := Submodule.finrank_le (LinearMap.ker T)
              have := Module.finrank_zero_of_subsingleton (M := V) (R := ℂ)
              omega
            · -- Exactly one nontrivial summand
              push_neg at hk_all
              obtain ⟨j₀, hkj₀⟩ := hk_all
              have hkj₀_pos : 0 < k j₀ := Nat.pos_of_ne_zero hkj₀
              have hothers : ∀ j, j ≠ j₀ → k j = 0 := by
                intro j hj; by_contra hkj
                exact hj (hall j j₀ (Nat.pos_of_ne_zero hkj) hkj₀_pos)
              -- Every kernel element maps to span of one generator
              set gen := (Submodule.Quotient.mk (p := ℂ[X] ∙ (X : ℂ[X]) ^ k j₀)
                ((X : ℂ[X]) ^ (k j₀ - 1)) : N j₀)
              set w : V := (Module.AEval'.of (R := ℂ) T).symm
                (e.symm (DirectSum.of N j₀ gen)) with hw_def
              suffices h_le : LinearMap.ker T ≤ Submodule.span ℂ ({w} : Set V) by
                exact (Submodule.finrank_mono h_le).trans
                  ((finrank_span_le_card ({w} : Set V)).trans (by simp))
              intro v hv
              rw [LinearMap.mem_ker] at hv
              have hXv : (X : ℂ[X]) • e (Module.AEval'.of (R := ℂ) T v) = 0 := by
                have h := e.map_smul (X : ℂ[X]) (Module.AEval'.of (R := ℂ) T v)
                rw [Module.AEval'.X_smul_of, hv, map_zero, map_zero] at h
                exact h.symm
              set c₀ := DirectSum.component ℂ[X] _ _ j₀ (e (Module.AEval'.of (R := ℂ) T v))
              have hc₀_tors : (X : ℂ[X]) • c₀ = 0 := by
                have h := (DirectSum.component ℂ[X] _ _ j₀).map_smul
                  (X : ℂ[X]) (e (Module.AEval'.of (R := ℂ) T v))
                rw [hXv, map_zero] at h; exact h.symm
              have hc₀_span := quotient_X_torsion_mem_span (k j₀) c₀ hc₀_tors
              rw [Submodule.mem_span_singleton] at hc₀_span
              obtain ⟨c, hc⟩ := hc₀_span
              have hds_eq : e (Module.AEval'.of (R := ℂ) T v) = DirectSum.of _ j₀ c₀ := by
                apply DFinsupp.ext; intro j
                by_cases hj : j = j₀
                · subst hj; rw [DirectSum.of_eq_same]; rfl
                · haveI := N_subsingleton j (hothers j hj)
                  exact Subsingleton.elim _ _
              have hv_eq : v = c • w := by
                apply (Module.AEval'.of (R := ℂ) T).injective
                apply e.injective
                have lhs : e (Module.AEval'.of (R := ℂ) T v) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [hds_eq]; congr 1; exact hc.symm
                have rhs : e (Module.AEval'.of (R := ℂ) T (c • w)) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [map_smul, hw_def, LinearEquiv.apply_symm_apply]
                  conv_lhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c
                      (e.symm (DirectSum.of _ j₀ gen))]
                  rw [e.map_smul, LinearEquiv.apply_symm_apply]
                  conv_rhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c gen]
                  exact ((DirectSum.lof ℂ[X] (Fin d)
                    (fun i => ℂ[X] ⧸ ℂ[X] ∙ X ^ k i) j₀).map_smul _ gen).symm
                exact lhs.trans rhs.symm
              rw [hv_eq]
              exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
          linarith
        -- Use j₀ for the direct sum splitting
        -- P₁, P₂ are complementary in the direct sum
        let DS := DirectSum (Fin d) N
        let P₁ : Submodule ℂ[X] DS :=
          LinearMap.range (DirectSum.lof ℂ[X] (Fin d) N j₀)
        let P₂ : Submodule ℂ[X] DS :=
          LinearMap.ker (DirectSum.component ℂ[X] (Fin d) N j₀)
        have hP : IsCompl P₁ P₂ := by
          constructor
          · rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw₁
            have := LinearMap.mem_ker.mp hw₂
            rw [DirectSum.component.lof_self] at this
            simp [this]
          · rw [codisjoint_iff, Submodule.eq_top_iff']
            intro w
            have hw : w = DirectSum.lof ℂ[X] (Fin d) N j₀
                (DirectSum.component ℂ[X] (Fin d) N j₀ w) +
              (w - DirectSum.lof ℂ[X] (Fin d) N j₀
                (DirectSum.component ℂ[X] (Fin d) N j₀ w)) := by abel
            rw [hw]
            apply Submodule.add_mem_sup
            · exact LinearMap.mem_range.mpr ⟨_, rfl⟩
            · rw [LinearMap.mem_ker, map_sub, DirectSum.component.lof_self, sub_self]
        -- Transfer IsCompl through the order isomorphism induced by e.symm
        let oe := Submodule.orderIsoMapComap e.symm
        have hScompl : IsCompl (oe P₁) (oe P₂) := oe.isCompl hP
        -- S₁ = oe P₁, S₂ = oe P₂ as ℂ[X]-submodules
        let S₁ := oe P₁
        let S₂ := oe P₂
        -- Use these as ℂ-submodules of V (AEval' T = V as a type)
        refine ⟨S₁.restrictScalars ℂ, S₂.restrictScalars ℂ, ?_, ?_, ?_, ?_, ?_⟩
        · -- S₁ ≠ ⊥: N j₀ is nontrivial (k j₀ > 0), so P₁ = range(lof j₀) ≠ ⊥
          intro h
          rw [Submodule.restrictScalars_eq_bot_iff] at h
          have hP₁ : P₁ = ⊥ := by rwa [← oe.map_bot, oe.eq_iff_eq] at h
          rw [LinearMap.range_eq_bot] at hP₁
          have h1 := DFunLike.congr_fun hP₁ (1 : N j₀)
          simp only [LinearMap.zero_apply] at h1
          have hlof := DirectSum.lof_apply ℂ[X] j₀ (1 : N j₀)
          rw [h1, DFinsupp.zero_apply] at hlof
          haveI : Nontrivial (N j₀) := Submodule.Quotient.nontrivial_iff.mpr
            (Ideal.span_singleton_ne_top
              ((isUnit_pow_iff (by omega : k j₀ ≠ 0)).not.mpr Polynomial.not_isUnit_X))
          exact one_ne_zero hlof.symm
        · -- S₂ ≠ ⊥: lof j₁ 1 ∈ P₂ (j₁ ≠ j₀) and is nonzero (N j₁ nontrivial)
          intro h
          rw [Submodule.restrictScalars_eq_bot_iff] at h
          have hP₂ : P₂ = ⊥ := by rwa [← oe.map_bot, oe.eq_iff_eq] at h
          have hmem : DirectSum.lof ℂ[X] (Fin d) N j₁ (1 : N j₁) ∈ P₂ := by
            rw [LinearMap.mem_ker, DirectSum.component.of, dif_neg hne.symm]
          have hzero := (Submodule.eq_bot_iff _).mp hP₂ _ hmem
          have hlof := DirectSum.lof_apply ℂ[X] j₁ (1 : N j₁)
          rw [hzero, DFinsupp.zero_apply] at hlof
          haveI : Nontrivial (N j₁) := Submodule.Quotient.nontrivial_iff.mpr
            (Ideal.span_singleton_ne_top
              ((isUnit_pow_iff (by omega : k j₁ ≠ 0)).not.mpr Polynomial.not_isUnit_X))
          exact one_ne_zero hlof.symm
        · -- IsCompl S₁ S₂ as ℂ-submodules
          constructor
          · rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            exact Submodule.disjoint_def.mp hScompl.disjoint w hw₁ hw₂
          · rw [codisjoint_iff, Submodule.eq_top_iff']
            intro w
            have := Submodule.eq_top_iff'.mp hScompl.codisjoint.eq_top
              (Module.AEval'.of (R := ℂ) T w)
            rw [Submodule.mem_sup] at this ⊢
            obtain ⟨a, ha, b, hb, hab⟩ := this
            exact ⟨(Module.AEval'.of (R := ℂ) T).symm a, ha,
              (Module.AEval'.of (R := ℂ) T).symm b, hb,
              (Module.AEval'.of (R := ℂ) T).injective (by simp [hab])⟩
        · -- T-invariance of S₁
          intro w hw
          let w' := Module.AEval'.of (R := ℂ) T w
          have hw' : w' ∈ S₁ := hw
          have hXw : (X : ℂ[X]) • w' ∈ S₁ := S₁.smul_mem X hw'
          rw [Module.AEval'.X_smul_of] at hXw
          exact hXw
        · -- T-invariance of S₂
          intro w hw
          let w' := Module.AEval'.of (R := ℂ) T w
          have hw' : w' ∈ S₂ := hw
          have hXw : (X : ℂ[X]) • w' ∈ S₂ := S₂.smul_mem X hw'
          rw [Module.AEval'.X_smul_of] at hXw
          exact hXw
      · -- Case 2b-i: ker T ⊄ range T. Elementary: use hyperplane containing range T.
        -- Find v ∈ ker T \ range T
        obtain ⟨v, hv_ker, hv_range⟩ := Set.not_subset.mp hkR
        have hTv : T v = 0 := LinearMap.mem_ker.mp hv_ker
        have hv_ne : v ≠ 0 := fun h => by subst h; exact hv_range (Submodule.zero_mem _)
        -- span{v} ∩ range T = ⊥ (since v ∉ range T and span{v} is 1-dim)
        have hdv : Disjoint (Submodule.span ℂ {v}) (LinearMap.range T) := by
          rw [Submodule.disjoint_def]
          intro w hw₁ hw₂
          rw [Submodule.mem_span_singleton] at hw₁
          obtain ⟨c, rfl⟩ := hw₁
          by_contra h
          exact hv_range (by
            have hc : c ≠ 0 := fun hc => h (by simp [hc])
            exact (Submodule.smul_mem_iff _ hc).mp hw₂)
        -- Get complement C of (span{v} ⊔ range T) in V
        obtain ⟨C, hC⟩ := (Submodule.span ℂ {v} ⊔ LinearMap.range T).exists_isCompl
        -- M₂ = range T ⊔ C is complement of span{v}:
        -- V = span{v} ⊔ range T ⊔ C, and span{v} ∩ (range T ⊔ C) = ⊥
        refine ⟨Submodule.span ℂ {v}, LinearMap.range T ⊔ C, ?_, ?_, ?_, ?_, ?_⟩
        · -- span{v} ≠ ⊥
          exact mt Submodule.span_singleton_eq_bot.mp hv_ne
        · -- range T ⊔ C ≠ ⊥ (contains range T which is ≠ ⊥ since T ≠ 0)
          exact ne_bot_of_le_ne_bot (by rwa [ne_eq, LinearMap.range_eq_bot]) le_sup_left
        · -- IsCompl
          constructor
          · -- Disjoint: if w ∈ span{v} ∩ (range T ⊔ C), then w = 0
            rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            -- w ∈ span{v}, w ∈ range T ⊔ C
            obtain ⟨r, hr, c, hc, rfl⟩ := Submodule.mem_sup.mp hw₂
            -- r + c ∈ span{v}, so c = (r + c) - r ∈ span{v} + range T
            have hc_in : c ∈ Submodule.span ℂ {v} ⊔ LinearMap.range T := by
              have : r + c - r ∈ Submodule.span ℂ {v} ⊔ LinearMap.range T :=
                (Submodule.span ℂ {v} ⊔ LinearMap.range T).sub_mem
                  (Submodule.mem_sup_left hw₁) (Submodule.mem_sup_right hr)
              simpa using this
            -- c ∈ C ∩ (span{v} ⊔ range T) = ⊥
            have hc0 : c = 0 := by
              have : c ∈ (Submodule.span ℂ {v} ⊔ LinearMap.range T) ⊓ C :=
                Submodule.mem_inf.mpr ⟨hc_in, hc⟩
              rwa [hC.inf_eq_bot, Submodule.mem_bot] at this
            -- so w = r + 0 = r ∈ span{v} ∩ range T = ⊥
            rw [hc0, add_zero] at hw₁ ⊢
            exact Submodule.disjoint_def.mp hdv _ hw₁ hr
          · -- Codisjoint: span{v} ⊔ (range T ⊔ C) = ⊤
            rw [codisjoint_iff]
            calc Submodule.span ℂ {v} ⊔ (LinearMap.range T ⊔ C)
                = (Submodule.span ℂ {v} ⊔ LinearMap.range T) ⊔ C := by
                    rw [sup_assoc]
              _ = ⊤ := hC.codisjoint.eq_top
        · -- T-invariance of span{v}: Tv = 0
          intro w hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c, rfl⟩ := hw
          rw [map_smul, hTv, smul_zero]
          exact Submodule.zero_mem _
        · -- T-invariance of range T ⊔ C: T maps V into range T ⊆ range T ⊔ C
          intro w _
          exact Submodule.mem_sup_left ⟨w, rfl⟩

/-- For a nilpotent off-diagonal operator X(v,w) = (Bw, Av) on V × W with
dim(ker A) + dim(ker B) ≥ 2, there exists a nontrivial product-compatible
decomposition: subspaces pV, qV of V and pW, qW of W forming complementary
pairs, with A mapping pV → pW, qV → qW and B mapping pW → pV, qW → qV.

This is Problem 6.9.1(c) of Etingof: X admits a chain basis compatible with
the V ⊕ W grading (each chain generator lies in V×{0} or {0}×W). With such
a basis, splitting chains into two groups yields a product-compatible
decomposition where projections to V and W give complementary subspaces.

Proof outline (compatible chain basis theorem):
1. Each cyclic ℂ[X]-summand with generator g = (v,w) and X-order k satisfies:
   at least one of (v,0) or (0,w) also has X-order k (compatible generator lemma).
   Proof: X^k g = 0 and X^{k-1} g ≠ 0. Write g = g_V + g_W. Then
   X^{k-1} g_V + X^{k-1} g_W ≠ 0, so one of them is nonzero with X-order = k.
2. Generators can be replaced one at a time (PID theory: element of maximal order
   generates a direct summand).
3. With all generators compatible, each basis element is in V×{0} or {0}×W,
   so splitting chains partitions bases of V and W separately. -/
private lemma off_diagonal_nilpotent_product_decomp
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (_hAB : IsNilpotent (A.comp B))
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A) +
              Module.finrank ℂ (LinearMap.ker B)) :
    ∃ (pV qV : Submodule ℂ V) (pW qW : Submodule ℂ W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, A x ∈ pW) ∧ (∀ x ∈ qV, A x ∈ qW) ∧
      (∀ x ∈ pW, B x ∈ pV) ∧ (∀ x ∈ qW, B x ∈ qV) ∧
      ¬(pV = ⊥ ∧ pW = ⊥) ∧ ¬(qV = ⊥ ∧ qW = ⊥) := by
  sorry

/-- Given AB nilpotent with dim(ker A) + dim(ker B) ≥ 2, both V and W nontrivial,
and ker A ⊆ range B, ker B ⊆ range A (from indecomposability), there exists a
nontrivial Q₂-compatible direct sum decomposition.

Uses `off_diagonal_nilpotent_product_decomp` which provides the compatible
chain basis decomposition from Problem 6.9.1(c) of Etingof. -/
private lemma q2_nontrivial_decomp (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (_hV_pos : 0 < Module.finrank ℂ ρ.V)
    (_hW_pos : 0 < Module.finrank ℂ ρ.W)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker ρ.A) +
              Module.finrank ℂ (LinearMap.ker ρ.B))
    (_hkA : LinearMap.ker ρ.A ≤ LinearMap.range ρ.B)
    (_hkB : LinearMap.ker ρ.B ≤ LinearMap.range ρ.A) :
    ∃ (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, ρ.A x ∈ pW) ∧ (∀ x ∈ qV, ρ.A x ∈ qW) ∧
      (∀ x ∈ pW, ρ.B x ∈ pV) ∧ (∀ x ∈ qW, ρ.B x ∈ qV) ∧
      ¬(pV = ⊥ ∧ pW = ⊥) ∧ ¬(qV = ⊥ ∧ qW = ⊥) :=
  off_diagonal_nilpotent_product_decomp ρ.A ρ.B hAB hker

/-- If dim(ker A) + dim(ker B) ≥ 2 for a Q₂-rep with AB nilpotent and both dims > 0,
then the rep is decomposable.

Uses `q2_nontrivial_decomp` to produce a Q₂-compatible decomposition. -/
private lemma decomp_of_ker_sum_ge_two (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (_hV_pos : 0 < Module.finrank ℂ ρ.V)
    (_hW_pos : 0 < Module.finrank ℂ ρ.W)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker ρ.A) +
              Module.finrank ℂ (LinearMap.ker ρ.B)) :
    ¬ρ.Indecomposable := by
  intro hρ
  have hkA := ρ.ker_A_sub_range_B hρ hAB _hV_pos _hW_pos
  have hkB := ρ.ker_B_sub_range_A hρ hAB _hV_pos _hW_pos
  obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW, hp_ne, hq_ne⟩ :=
    q2_nontrivial_decomp ρ hAB _hV_pos _hW_pos hker hkA hkB
  exact (hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW).elim hp_ne hq_ne

/-- For indecomposable Q₂-reps with AB nilpotent and both dims > 0,
dim(ker A) + dim(ker B) ≤ 1. Combined with `ker_sum_ge_one`, gives sum = 1. -/
private lemma ker_sum_le_one (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    Module.finrank ℂ (LinearMap.ker ρ.A) + Module.finrank ℂ (LinearMap.ker ρ.B) ≤ 1 := by
  by_contra h
  exact absurd hρ (decomp_of_ker_sum_ge_two ρ hAB hV_pos hW_pos (by omega))

private lemma ker_sum_eq_one (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    Module.finrank ℂ (LinearMap.ker ρ.A) + Module.finrank ℂ (LinearMap.ker ρ.B) = 1 := by
  exact le_antisymm (ker_sum_le_one ρ hρ hAB hV_pos hW_pos) (ker_sum_ge_one ρ hAB hV_pos hW_pos)

/-- From `ker_sum_eq_one`: exactly one of A, B is injective and the other has
1-dimensional kernel. -/
private lemma exactly_one_injective (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    (LinearMap.ker ρ.A = ⊥ ∧ Module.finrank ℂ (LinearMap.ker ρ.B) = 1) ∨
    (LinearMap.ker ρ.B = ⊥ ∧ Module.finrank ℂ (LinearMap.ker ρ.A) = 1) := by
  have h := ker_sum_eq_one ρ hρ hAB hV_pos hW_pos
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ (LinearMap.ker ρ.A)) with hA | hA
  · left
    exact ⟨Submodule.finrank_eq_zero.mp hA, by omega⟩
  · right
    have hB : Module.finrank ℂ (LinearMap.ker ρ.B) = 0 := by omega
    exact ⟨Submodule.finrank_eq_zero.mp hB, by omega⟩

/-- Main nilpotent case: AB nilpotent + indecomposable + both dims > 0 → |dim V - dim W| ≤ 1.

Uses `exactly_one_injective` to get that exactly one of A, B is injective with the other
having 1-dimensional kernel, then derives the dimension bound via rank-nullity:
- If A injective (nullity B = 1): dim V = rank A ≤ dim W, and
  rank B = dim W - 1 ≤ dim V, so dim V ≤ dim W ≤ dim V + 1.
- If B injective (nullity A = 1): symmetric argument gives
  dim W ≤ dim V ≤ dim W + 1. -/
private theorem Problem6_9_1_nilpotent_main (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable)
    (hAB : IsNilpotent (ρ.A.comp ρ.B))
    (hV_pos : 0 < Module.finrank ℂ ρ.V)
    (hW_pos : 0 < Module.finrank ℂ ρ.W) :
    (Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W ∨
     Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W + 1 ∨
     Module.finrank ℂ ρ.W = Module.finrank ℂ ρ.V + 1) := by
  have hkA := ρ.ker_A_sub_range_B hρ hAB hV_pos hW_pos
  have hkB := ρ.ker_B_sub_range_A hρ hAB hV_pos hW_pos
  rcases exactly_one_injective ρ hρ hAB hV_pos hW_pos with ⟨hkA_bot, hkB_dim⟩ | ⟨hkB_bot, hkA_dim⟩
  · -- Case 1: A injective, nullity B = 1
    -- rank A = dim V (A injective), rank A ≤ dim W → dim V ≤ dim W
    have hV_le_W : Module.finrank ℂ ρ.V ≤ Module.finrank ℂ ρ.W := by
      have h_rA : Module.finrank ℂ (LinearMap.range ρ.A) = Module.finrank ℂ ρ.V := by
        have := LinearMap.finrank_range_add_finrank_ker ρ.A
        rw [hkA_bot, finrank_bot] at this; omega
      calc Module.finrank ℂ ρ.V
          = Module.finrank ℂ (LinearMap.range ρ.A) := h_rA.symm
        _ ≤ Module.finrank ℂ ρ.W := Submodule.finrank_le _
    -- rank B ≤ dim V and rank B = dim W - 1 → dim W ≤ dim V + 1
    have hW_le_V1 : Module.finrank ℂ ρ.W ≤ Module.finrank ℂ ρ.V + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ρ.B
      have h2 : Module.finrank ℂ (LinearMap.range ρ.B) ≤ Module.finrank ℂ ρ.V :=
        Submodule.finrank_le _
      rw [hkB_dim] at h1; omega
    omega
  · -- Case 2: B injective, nullity A = 1 (symmetric)
    have hW_le_V : Module.finrank ℂ ρ.W ≤ Module.finrank ℂ ρ.V := by
      have h_rB : Module.finrank ℂ (LinearMap.range ρ.B) = Module.finrank ℂ ρ.W := by
        have := LinearMap.finrank_range_add_finrank_ker ρ.B
        rw [hkB_bot, finrank_bot] at this; omega
      calc Module.finrank ℂ ρ.W
          = Module.finrank ℂ (LinearMap.range ρ.B) := h_rB.symm
        _ ≤ Module.finrank ℂ ρ.V := Submodule.finrank_le _
    have hV_le_W1 : Module.finrank ℂ ρ.V ≤ Module.finrank ℂ ρ.W + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ρ.A
      have h2 : Module.finrank ℂ (LinearMap.range ρ.A) ≤ Module.finrank ℂ ρ.W :=
        Submodule.finrank_le _
      rw [hkA_dim] at h1; omega
    omega

/-- **Problem 6.9.1(a) (Etingof)**: The four families E_{n,λ}, E_{n,∞}, H_n, K_n
(as defined above) are indecomposable and pairwise nonisomorphic. Moreover, these
are all the indecomposable representations of Q₂.

Specifically, every indecomposable representation of Q₂ is isomorphic to exactly one of:
- E_{n,λ} for some n ≥ 1, λ ∈ ℂ
- E_{n,∞} for some n ≥ 1 (obtained from E_{n,0} by swapping V ↔ W and A ↔ B)
- H_n for some n ≥ 1
- K_n for some n ≥ 1 (obtained from H_n by swapping V ↔ W and A ↔ B)

This extends the Jordan normal form classification from Q₁ (single vertex with a loop)
to Q₂ (two vertices with a cycle). -/
theorem Etingof.Problem6_9_1 (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable) :
    -- The representation belongs to one of the four families (existential form):
    -- Either dim V = dim W (E_{n,λ} or E_{n,∞} family)
    -- or |dim V - dim W| = 1 (H_n or K_n family)
    (Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W ∨
     Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W + 1 ∨
     Module.finrank ℂ ρ.W = Module.finrank ℂ ρ.V + 1) := by
  by_cases hAB : IsNilpotent (ρ.A.comp ρ.B)
  · -- Nilpotent case: AB nilpotent → |dim V - dim W| ≤ 1
    -- Tactic for showing all elements are zero when finrank = 0 over a field
    have allz_V : Module.finrank ℂ ρ.V = 0 → ∀ x : ρ.V, x = 0 := fun h0 x => by
      obtain ⟨c, hc, hcx⟩ := (Module.finrank_eq_zero_iff (R := ℂ) (M := ρ.V)).mp h0 x
      exact (smul_eq_zero.mp hcx).resolve_left hc
    have allz_W : Module.finrank ℂ ρ.W = 0 → ∀ x : ρ.W, x = 0 := fun h0 x => by
      obtain ⟨c, hc, hcx⟩ := (Module.finrank_eq_zero_iff (R := ℂ) (M := ρ.W)).mp h0 x
      exact (smul_eq_zero.mp hcx).resolve_left hc
    by_cases hV0 : Module.finrank ℂ ρ.V = 0
    · -- dim V = 0: show dim W = 1
      right; right; rw [hV0, zero_add]
      have hW_pos : 0 < Module.finrank ℂ ρ.W := by rcases hρ.1 with h | h <;> omega
      haveI hV_ss : Subsingleton ρ.V :=
        ⟨fun a b => by rw [allz_V hV0 a, allz_V hV0 b]⟩
      by_contra hW_ne1
      have : Nontrivial ρ.W := by
        by_contra h; rw [not_nontrivial_iff_subsingleton] at h
        exact absurd (Module.finrank_zero_of_subsingleton (R := ℂ) (M := ρ.W)) (by omega)
      obtain ⟨w, hw⟩ := exists_ne (0 : ρ.W)
      set pW := Submodule.span ℂ ({w} : Set ρ.W)
      obtain ⟨qW, hcW⟩ := pW.exists_isCompl
      have hpW_ne : pW ≠ ⊥ := by
        intro h; apply hw
        have : w ∈ pW := Submodule.subset_span rfl
        rw [h] at this; simpa [Submodule.mem_bot] using this
      have hqW_ne : qW ≠ ⊥ := by
        intro h
        have h1 : Module.finrank ℂ ↥pW ≤ 1 :=
          (finrank_span_le_card ({w} : Set ρ.W)).trans (by simp)
        have h2 : pW = ⊤ := eq_top_of_isCompl_bot (h ▸ hcW)
        rw [h2, finrank_top] at h1; omega
      rcases hρ.2 ⊥ ⊤ pW qW isCompl_bot_top hcW
        (fun x _ => by rw [allz_V hV0 x, map_zero]; exact zero_mem _)
        (fun x _ => by rw [allz_V hV0 x, map_zero]; exact zero_mem _)
        (fun x _ => by rw [allz_V hV0 (ρ.B x)]; exact zero_mem _)
        (fun x _ => Submodule.mem_top) with ⟨_, h⟩ | ⟨_, h⟩
      · exact hpW_ne h
      · exact hqW_ne h
    · by_cases hW0 : Module.finrank ℂ ρ.W = 0
      · -- dim W = 0: show dim V = 1 (symmetric)
        right; left; rw [hW0, zero_add]
        have hV_pos : 0 < Module.finrank ℂ ρ.V := by rcases hρ.1 with h | h <;> omega
        haveI hW_ss : Subsingleton ρ.W :=
          ⟨fun a b => by rw [allz_W hW0 a, allz_W hW0 b]⟩
        by_contra hV_ne1
        have : Nontrivial ρ.V := by
          by_contra h; rw [not_nontrivial_iff_subsingleton] at h
          exact absurd (Module.finrank_zero_of_subsingleton (R := ℂ) (M := ρ.V)) (by omega)
        obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
        set pV := Submodule.span ℂ ({v} : Set ρ.V)
        obtain ⟨qV, hcV⟩ := pV.exists_isCompl
        have hpV_ne : pV ≠ ⊥ := by
          intro h; apply hv
          have : v ∈ pV := Submodule.subset_span rfl
          rw [h] at this; simpa [Submodule.mem_bot] using this
        have hqV_ne : qV ≠ ⊥ := by
          intro h
          have h1 : Module.finrank ℂ ↥pV ≤ 1 :=
            (finrank_span_le_card ({v} : Set ρ.V)).trans (by simp)
          have h2 : pV = ⊤ := eq_top_of_isCompl_bot (h ▸ hcV)
          rw [h2, finrank_top] at h1; omega
        rcases hρ.2 pV qV ⊥ ⊤ hcV isCompl_bot_top
          (fun x _ => by rw [allz_W hW0 (ρ.A x)]; exact zero_mem _)
          (fun x _ => Submodule.mem_top)
          (fun x _ => by rw [allz_W hW0 x, map_zero]; exact zero_mem _)
          (fun x _ => by rw [allz_W hW0 x, map_zero]; exact zero_mem _) with ⟨h, _⟩ | ⟨h, _⟩
        · exact hpV_ne h
        · exact hqV_ne h
      · -- Both dims positive: main case
        exact Problem6_9_1_nilpotent_main ρ hρ hAB
          (Nat.pos_of_ne_zero hV0) (Nat.pos_of_ne_zero hW0)
  · -- Non-nilpotent case: Fitting decomposition → dim V = dim W
    left
    -- Use Fitting decomposition directly
    set AB := ρ.A.comp ρ.B
    set BA := ρ.B.comp ρ.A
    set pW := ⨆ n, LinearMap.ker (AB ^ n)
    set qW := ⨅ n, LinearMap.range (AB ^ n)
    set pV := ⨆ n, LinearMap.ker (BA ^ n)
    set qV := ⨅ n, LinearMap.range (BA ^ n)
    have hcV := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
    have hcW := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
    -- Fitting compatibility (via shared lemmas)
    have hApV : ∀ x ∈ pV, ρ.A x ∈ pW := fun x hx => ρ.fitting_A_ker_to_ker x hx
    have hAqV : ∀ x ∈ qV, ρ.A x ∈ qW := fun x hx => ρ.fitting_A_range_to_range x hx
    have hBpW : ∀ x ∈ pW, ρ.B x ∈ pV := fun x hx => ρ.fitting_B_ker_to_ker x hx
    have hBqW : ∀ x ∈ qW, ρ.B x ∈ qV := fun x hx => ρ.fitting_B_range_to_range x hx
    -- qW ≠ ⊥ (since AB not nilpotent, the eventual range is nontrivial)
    have hqW_ne : qW ≠ ⊥ := by
      intro h
      apply hAB
      -- qW = ⊥ means pW = ⊤ (from IsCompl)
      have hpW_top : pW = ⊤ := eq_top_of_isCompl_bot (h ▸ hcW)
      -- pW = ⨆ ker(AB^n) = ⊤ means ker(AB^N) = ⊤ for some N (Noetherian stabilization)
      have h_sup_top : ⨆ n, LinearMap.ker (AB ^ n) = ⊤ := hpW_top
      obtain ⟨N, hN⟩ := Filter.Eventually.exists (LinearMap.eventually_iSup_ker_pow_eq AB)
      rw [h_sup_top] at hN
      exact ⟨N, LinearMap.ker_eq_top.mp hN.symm⟩
    -- By indecomposability
    rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with ⟨hpV, hpW⟩ | ⟨_, hqW⟩
    · -- pV = ⊥, pW = ⊥: qV = ⊤, qW = ⊤
      have hqV_top : qV = ⊤ := eq_top_of_bot_isCompl (hpV ▸ hcV)
      have hqW_top : qW = ⊤ := eq_top_of_bot_isCompl (hpW ▸ hcW)
      -- Dimension equality via injectivity (using shared Fitting injectivity lemmas)
      set A' : ↥qV →ₗ[ℂ] ↥qW :=
        (ρ.A.domRestrict qV).codRestrict qW (fun ⟨v, hv⟩ => hAqV v hv)
      set B' : ↥qW →ₗ[ℂ] ↥qV :=
        (ρ.B.domRestrict qW).codRestrict qV (fun ⟨w, hw⟩ => hBqW w hw)
      have hA'_inj : Function.Injective A' := by
        intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
        exact Subtype.ext (ρ.fitting_A_injective_on_range hv₁ hv₂ (by
          simpa [A', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
            using congr_arg Subtype.val h))
      have hB'_inj : Function.Injective B' := by
        intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
        exact Subtype.ext (ρ.fitting_B_injective_on_range hw₁ hw₂ (by
          simpa [B', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
            using congr_arg Subtype.val h))
      -- dim V = dim qV ≤ dim qW = dim W and vice versa
      apply le_antisymm
      · calc Module.finrank ℂ ρ.V
            = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.V) := (finrank_top ℂ ρ.V).symm
          _ = Module.finrank ℂ ↥qV := by rw [hqV_top]
          _ ≤ Module.finrank ℂ ↥qW := LinearMap.finrank_le_finrank_of_injective hA'_inj
          _ = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.W) := by rw [hqW_top]
          _ = Module.finrank ℂ ρ.W := finrank_top ℂ ρ.W
      · calc Module.finrank ℂ ρ.W
            = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.W) := (finrank_top ℂ ρ.W).symm
          _ = Module.finrank ℂ ↥qW := by rw [hqW_top]
          _ ≤ Module.finrank ℂ ↥qV := LinearMap.finrank_le_finrank_of_injective hB'_inj
          _ = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.V) := by rw [hqV_top]
          _ = Module.finrank ℂ ρ.V := finrank_top ℂ ρ.V
    · -- qW = ⊥: contradiction with AB not nilpotent
      exact absurd hqW hqW_ne

/-- **Problem 6.9.1(c) (Etingof)**: When AB is nilpotent, the operator X on V ⊕ W
defined by X(v,w) = (Bw, Av) is also nilpotent and admits a basis of chains
compatible with the V ⊕ W decomposition.

This reduces to showing X has a Jordan chain basis where each chain starts in either
V or W. The chain structure directly gives the H_n and K_n families. -/
theorem Etingof.Problem6_9_1c (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B)) :
    -- The operator X = (0, B; A, 0) on V × W is nilpotent
    IsNilpotent ((ρ.B.comp ρ.A).prodMap (ρ.A.comp ρ.B) : (ρ.V × ρ.W) →ₗ[ℂ] (ρ.V × ρ.W)) := by
  -- Step 1: AB nilpotent implies BA nilpotent
  -- If (AB)^n = 0, then (BA)^(n+1) = B(AB)^n A = 0
  obtain ⟨n, hn⟩ := hAB
  have hBA : IsNilpotent (ρ.B.comp ρ.A) := by
    refine ⟨n + 1, ?_⟩
    -- (BA)^(n+1) v = B((AB)^n(Av)) = B(0) = 0
    -- Key shift lemma: ((BA)^m)(Bw) = B((AB)^m w)
    have key : ∀ (m : ℕ) (w : ρ.W),
        ((ρ.B.comp ρ.A) ^ m) (ρ.B w) = ρ.B (((ρ.A.comp ρ.B) ^ m) w) := by
      intro m; induction m with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, LinearMap.comp_apply, ih,
            Module.End.mul_apply, ← LinearMap.comp_apply ρ.A ρ.B]
    ext v
    simp only [LinearMap.zero_apply]
    rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply, key n (ρ.A v)]
    have := LinearMap.congr_fun hn (ρ.A v)
    simp only [LinearMap.zero_apply] at this
    rw [this, map_zero]
  -- Step 2: prodMap of nilpotent endomorphisms is nilpotent
  -- (f.prodMap g)^k = (f^k).prodMap (g^k) via prodMap_mul
  obtain ⟨m, hm⟩ := hBA
  refine ⟨max n m, ?_⟩
  have h1 : (ρ.A.comp ρ.B) ^ max n m = 0 := by
    rw [← Nat.sub_add_cancel (Nat.le_max_left n m), pow_add, hn, mul_zero]
  have h2 : (ρ.B.comp ρ.A) ^ max n m = 0 := by
    rw [← Nat.sub_add_cancel (Nat.le_max_right n m), pow_add, hm, mul_zero]
  -- Show (f.prodMap g)^k = (f^k).prodMap (g^k) by induction
  have pow_prodMap : ∀ (k : ℕ) (f : ρ.V →ₗ[ℂ] ρ.V) (g : ρ.W →ₗ[ℂ] ρ.W),
      (f.prodMap g) ^ k = (f ^ k).prodMap (g ^ k) := by
    intro k; induction k with
    | zero => intro f g; simp [LinearMap.prodMap_one]
    | succ k ih =>
      intro f g
      rw [pow_succ, ih f g, LinearMap.prodMap_mul, pow_succ, pow_succ]
  rw [pow_prodMap, h1, h2, LinearMap.prodMap_zero]
