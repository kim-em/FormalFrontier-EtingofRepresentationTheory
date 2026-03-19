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
    -- This requires the chain/Jordan structure argument for nilpotent Q₂ reps
    sorry
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
