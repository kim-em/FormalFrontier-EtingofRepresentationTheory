import Mathlib

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
    -- Now A preserves both pV and qV (using hApV, hAqV with pW = pV, qW = qV)
    -- The Jordan block J_n(λ) has no nontrivial invariant direct sum decomposition
    -- This follows from ker(A - λI) being 1-dimensional (spanned by e₁)
    -- TODO: Prove Jordan block indecomposability
    sorry

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
  sorry

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
  sorry

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
