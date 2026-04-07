import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Proposition6_6_7
import EtingofRepresentationTheory.Chapter6.Proposition6_6_8
import EtingofRepresentationTheory.Chapter6.Theorem6_8_1

/-!
# Corollary 6.8.4: Every Positive Root Is Realized

For every positive root α of a Dynkin quiver Q, there exists an indecomposable
representation V with d(V) = α.

The proof constructs V explicitly: apply the sequence s_n, s_{n-1}s_n, … to α
until reaching a simple root αᵢ. Then build V = F⁻_n F⁻_{n-1} ⋯ F⁻_q k_{(i)}
where k_{(i)} is the simple representation at vertex i on the appropriately
reoriented quiver.

This completes Gabriel's theorem: indecomposable representations of Dynkin quivers
are in bijection with positive roots.

## Mathlib correspondence

Requires full reflection functor machinery and the construction of simple
representations. Not in Mathlib.

## Formalization note

The statement says: for any positive root α (w.r.t. the Cartan form of a Dynkin
diagram), there is an indecomposable quiver representation whose dimension
vector equals α. The proof uses Theorem 6.8.1 (iterated reflections reach a
simple root) and the reflection functors (Definitions 6.6.3-6.6.4) to
reconstruct the representation from the simple one.

## Current status

### Infrastructure built
- **Simple representation construction** (`simpleRepresentation`): Constructs the
  indecomposable representation k₍ₚ₎ at vertex p (1-dim at p, 0 elsewhere, all
  maps zero) for any quiver Q.
- **Base case proved** (`Corollary6_8_4_simpleRoot`): When α = simpleRoot n p,
  the simple representation realizes it.
- **Induction structure**: The main proof reduces via Theorem 6.8.1 to the base
  case plus a reflection functor chain step (sorry'd).

### Remaining blocker
- **Reflection functor chain** (`reflectionFunctorChainStep`): Applying F⁻ᵢ to
  transform a realization on the reversed quiver back to Q. This requires:
  - Iterated quiver reversal tracking
  - Proposition 6.6.7 source case (currently sorry'd)
  - Proposition 6.6.8 source case for dimension vector tracking

### Fixed (issue #1094)
- **Q-adj connection**: Added `IsOrientationOf Q adj` hypothesis linking the
  quiver to the Dynkin diagram's adjacency matrix.
- **Universe polymorphism**: Pinned `obj` universe to match `k` in the
  conclusion's `QuiverRepresentation`.
-/

open scoped Matrix

section SimpleRepresentation

/-- The simple quiver representation at vertex p: assigns `Fin 1 → k` at p,
`Fin 0 → k` at all other vertices, and zero maps on all edges. -/
noncomputable def Etingof.simpleRepresentation
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n)
    {Q : Quiver (Fin n)} :
    @Etingof.QuiverRepresentation k (Fin n) _ Q where
  obj v := Fin (if v = p then 1 else 0) → k
  mapLinear _ := 0

/-- The simple representation at p has `Module.Free k` at every vertex. -/
instance Etingof.simpleRepresentation_free
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Free k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
  Module.Free.pi _ _

/-- The simple representation at p has `Module.Finite k` at every vertex. -/
instance Etingof.simpleRepresentation_finite
    (k : Type*) [CommSemiring k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.Finite k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
  Module.Finite.pi

private lemma Etingof.simpleRepresentation_finrank
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj v) =
      if v = p then 1 else 0 := by
  change Module.finrank k (Fin (if v = p then 1 else 0) → k) = _
  split_ifs with h <;> simp_all [Module.finrank_pi_fintype]

private lemma Etingof.simpleRepresentation_finrank_eq_simpleRoot
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} (v : Fin n) :
    (Etingof.simpleRoot n p v : ℤ) =
      ↑(Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj v)) := by
  rw [Etingof.simpleRepresentation_finrank]
  simp only [Etingof.simpleRoot, Pi.single_apply]
  split_ifs <;> simp_all

set_option maxHeartbeats 400000 in
-- 1-dim space case analysis with finrank API needs extra heartbeats
/-- The simple representation at p is indecomposable: nontrivial at p and
any complementary sub-representations must have one component trivial. -/
private lemma Etingof.simpleRepresentation_indecomposable
    (k : Type*) [Field k]
    {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} :
    (Etingof.simpleRepresentation k p (Q := Q)).IsIndecomposable := by
  refine ⟨⟨p, ?_⟩, fun W₁ W₂ _ _ hcompl => ?_⟩
  · -- Nontrivial at p: Fin 1 → k is nontrivial
    change Nontrivial (Fin (if p = p then 1 else 0) → k)
    simp only [ite_true]
    exact Pi.nontrivial
  · -- At vertices v ≠ p, both submodules are ⊥ (zero-dimensional space)
    have hbot : ∀ v, v ≠ p → W₁ v = ⊥ ∧ W₂ v = ⊥ := by
      intro v hv
      have hempty : IsEmpty (Fin (if v = p then 1 else 0)) := by
        simp only [hv, ite_false]; exact Fin.isEmpty
      haveI : Subsingleton ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        show Subsingleton (Fin (if v = p then 1 else 0) → k) from inferInstance
      exact ⟨Submodule.eq_bot_of_subsingleton, Submodule.eq_bot_of_subsingleton⟩
    -- At vertex p, 1-dimensional space: one complement must be ⊥
    have hdim_p : Module.finrank k (Fin (if p = p then 1 else 0) → k) = 1 := by
      simp
    -- In a 1-dim space, any IsCompl pair has one component = ⊥
    have hcompl_p := hcompl p
    -- Use disjointness: W₁ ⊓ W₂ = ⊥, W₁ ⊔ W₂ = ⊤
    -- In a 1-dim space, if both are nonzero then both = ⊤, contradicting disjointness
    have : W₁ p = ⊥ ∨ W₂ p = ⊥ := by
      -- upgrade to AddCommGroup for Submodule API
      letI : ∀ v, AddCommGroup ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        fun v => Etingof.addCommGroupOfRing (k := k)
      by_contra h
      push_neg at h
      obtain ⟨h1, h2⟩ := h
      have hr1 := Submodule.one_le_finrank_iff.mpr h1
      have hr2 := Submodule.one_le_finrank_iff.mpr h2
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W₁ p) (W₂ p)
      rw [hcompl_p.sup_eq_top, hcompl_p.inf_eq_bot] at hsum
      rw [finrank_top, finrank_bot] at hsum
      -- finrank of the whole space at p equals 1
      have hdim_p' : Module.finrank k ((Etingof.simpleRepresentation k p (Q := Q)).obj p) = 1 :=
        hdim_p
      omega
    rcases this with h | h
    · left; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).1
    · right; intro v; by_cases hv : v = p
      · subst hv; exact h
      · exact (hbot v hv).2

end SimpleRepresentation

universe u in
/-- Base case: when α is a simple root, the simple representation realizes it.
The `obj` universe is fixed to match `k` (uses `Fin m → k` for spaces).
Note: This fixes `QuiverRepresentation.obj` to live in the same universe as `k`. -/
theorem Etingof.Corollary6_8_4_simpleRoot
    {n : ℕ} (p : Fin n)
    (k : Type u) [Field k]
    {Q : Quiver (Fin n)} :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (Etingof.simpleRoot n p v : ℤ) = ↑(Module.finrank k (ρ.obj v)) :=
  ⟨Etingof.simpleRepresentation k p,
   fun v => Etingof.simpleRepresentation_free k p v,
   fun v => Etingof.simpleRepresentation_finite k p v,
   Etingof.simpleRepresentation_indecomposable k p,
   fun v => Etingof.simpleRepresentation_finrank_eq_simpleRoot k p v⟩

open Etingof in
/-- For a positive root α with ∑α ≥ 2 on a Dynkin diagram, `(Aα)_k ≤ α_k` at
every vertex k. This means reflecting at any vertex preserves non-negativity.

Proof: if `(Aα)_k > α_k`, then `α_k ≥ 1` (when `α_k = 0`, `(Aα)_k ≤ 0`).
Setting `β = α - e_k`, we get `B(β,β) = 4 - 2(Aα)_k ≤ 0` with `β ≥ 0`,
`β ≠ 0`, contradicting positive definiteness. -/
private lemma Etingof.positive_root_cartan_bound
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (α : Fin n → ℤ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_root : dotProduct α ((Etingof.cartanMatrix n adj).mulVec α) = 2)
    (hα_sum : 2 ≤ ∑ i, α i)
    (k : Fin n) :
    (Etingof.cartanMatrix n adj).mulVec α k ≤ α k := by
  set A := Etingof.cartanMatrix n adj
  have hAsymm := Etingof.cartanMatrix_isSymm hDynkin.1
  by_contra h; push_neg at h
  -- α_k ≥ 1: if α_k = 0, then (Aα)_k = -Σ adj_{k,j} α_j ≤ 0 ≤ α_k
  have hαk_pos : 1 ≤ α k := by
    by_contra h'; push_neg at h'
    have hαk0 : α k = 0 := le_antisymm (by omega) (hα_nonneg k)
    have : A.mulVec α k ≤ 0 := by
      show (∑ j : Fin n, A k j * α j) ≤ 0
      have hdiag : A k k = 2 := by
        show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k k = 2
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
        norm_num; have := hDynkin.2.1 k; omega
      calc ∑ j, A k j * α j = A k k * α k + ∑ j ∈ Finset.univ.erase k, A k j * α j := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
            _ = ∑ j ∈ Finset.univ.erase k, A k j * α j := by rw [hαk0, mul_zero, zero_add]
            _ ≤ 0 := by
                apply Finset.sum_nonpos; intro j hj
                have hne : j ≠ k := Finset.ne_of_mem_erase hj
                have : A k j ≤ 0 := by
                  show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k j ≤ 0
                  simp only [Matrix.sub_apply, Matrix.smul_apply,
                    Matrix.one_apply_ne (Ne.symm hne)]
                  norm_num; have := hDynkin.2.2.1 k j; omega
                exact mul_nonpos_of_nonpos_of_nonneg this (hα_nonneg j)
    linarith
  -- β = α - e_k: non-negative and nonzero
  set β : Fin n → ℤ := α - Pi.single k 1
  have hβ_nonneg : ∀ i, 0 ≤ β i := by
    intro i; simp only [β, Pi.sub_apply, Pi.single_apply]
    split_ifs with heq
    · subst heq; omega
    · simp only [sub_zero]; exact hα_nonneg i
  have hβ_nonzero : β ≠ 0 := by
    intro h0; apply_fun (fun f => ∑ i, f i) at h0
    simp only [β, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply,
      Finset.sum_const_zero] at h0
    omega
  -- B(β,β) = 4 - 2(Aα)_k ≤ 0
  have symm_k : ∀ j, A j k = A k j := fun j => congr_fun (congr_fun hAsymm k) j
  have hBde : dotProduct α (A.mulVec (Pi.single k (1 : ℤ))) = A.mulVec α k := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_k j]; ring
  have hBed : dotProduct (Pi.single k (1 : ℤ)) (A.mulVec α) = A.mulVec α k := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hBee : dotProduct (Pi.single k (1 : ℤ)) (A.mulVec (Pi.single k (1 : ℤ))) = 2 := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) k k = 2
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num; have := hDynkin.2.1 k; omega
  have hBβ : dotProduct β (A.mulVec β) = 4 - 2 * A.mulVec α k := by
    show dotProduct (α - Pi.single k 1) (A.mulVec (α - Pi.single k 1)) = _
    simp only [Matrix.mulVec_sub]
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hα_root, hBde, hBed, hBee]; ring
  have hBβ_nonpos : dotProduct β (A.mulVec β) ≤ 0 := by linarith
  -- Positive definiteness gives B(β,β) > 0, contradiction
  have hpos := hDynkin.2.2.2.2 β hβ_nonzero
  rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
  linarith

section BackwardConstruction

/-! ### Infrastructure for backward construction via F⁻

The backward construction walks an admissible ordering in reverse, applying F⁻
at sources to build up a representation from a simple root. -/

open Etingof in
/-- `Fintype` for `ArrowsOutOf Q i` from `Subsingleton` Hom types on `Fin n`.
Dual of `fintypeArrowsIntoOfSubsingleton`. -/
private noncomputable def fintypeArrowsOutOfOfSubsingleton
    {n : ℕ} {Q : Quiver (Fin n)}
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (i : Fin n) : Fintype (@Etingof.ArrowsOutOf (Fin n) Q i) := by
  haveI : ∀ (b : Fin n), Fintype (@Quiver.Hom (Fin n) Q i b) :=
    fun b => Etingof.fintypeHomOfSubsingleton i b
  exact Sigma.instFintype

open Etingof in
/-- `Module.Free` for `F⁻ᵢ(ρ)` at vertex `v ≠ i`.
At `v ≠ i`, `F⁻ᵢ(ρ).obj v ≃ₗ ρ.obj v`, so Free transfers. -/
private lemma reflFunctorMinus_free_ne
    {k₀ : Type*} [CommRing k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Free k₀ (@Etingof.QuiverRepresentation.obj k₀ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v) :=
  Module.Free.of_equiv (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).symm

open Etingof in
/-- `Module.Finite` for `F⁻ᵢ(ρ)` at vertex `v ≠ i`. -/
private lemma reflFunctorMinus_finite_ne
    {k₀ : Type*} [CommRing k₀] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k₀ Q)
    [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite k₀ (@Etingof.QuiverRepresentation.obj k₀ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v) :=
  Module.Finite.equiv (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
open Etingof in
/-- `Module.Free` for `F⁻ᵢ(ρ)` at vertex i (quotient of free module over field). -/
private lemma reflFunctorMinus_free_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Module.Free k₀ (@Etingof.QuiverRepresentation.obj k₀ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k₀)
  exact Module.Free.of_equiv (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm

set_option linter.unusedFintypeInType false in
open Etingof in
/-- `Module.Finite` for `F⁻ᵢ(ρ)` at vertex i (quotient of finite module). -/
private lemma reflFunctorMinus_finite_eq
    {k₀ : Type*} [Field k₀] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation k₀ Q)
    [∀ v, Module.Free k₀ (ρ.obj v)] [∀ v, Module.Finite k₀ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Module.Finite k₀ (@Etingof.QuiverRepresentation.obj k₀ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k₀)
  exact Module.Finite.equiv (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm

open Etingof in
/-- At a source of a Dynkin orientation with Subsingleton Hom types,
`simpleReflectionDimVector` (using `ArrowsOutOf`) equals `simpleReflection`.
Source-dual of `simpleReflectionDimVector_eq_simpleReflection`. -/
private lemma simpleReflectionDimVector_eq_simpleReflection_source
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {Q : Quiver (Fin n)} (hOrient : Etingof.IsOrientationOf Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @Etingof.IsSource (Fin n) Q p)
    (d : Fin n → ℤ) :
    haveI := fintypeArrowsOutOfOfSubsingleton (Q := Q) p
    Etingof.simpleReflectionDimVector (fun (a : @Etingof.ArrowsOutOf (Fin n) Q p) => a.1) p d =
    Etingof.simpleReflection n (Etingof.cartanMatrix n adj) p d := by
  haveI := fintypeArrowsOutOfOfSubsingleton (Q := Q) p
  haveI : ∀ (a b : Fin n), Fintype (@Quiver.Hom (Fin n) Q a b) :=
    fun a b => Etingof.fintypeHomOfSubsingleton a b
  ext v
  unfold Etingof.simpleReflectionDimVector Etingof.simpleReflection Etingof.rootReflection
  by_cases hv : v = p
  · subst hv
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, if_true]
    -- Goal: -d v + ∑ x, d x.fst = d v - d ⬝ᵥ cartanMatrix *ᵥ Pi.single v 1
    -- Step 1: compute dot product with Cartan matrix
    have hdot : d ⬝ᵥ Etingof.cartanMatrix n adj *ᵥ Pi.single v 1 =
        2 * d v - ∑ j : Fin n, adj v j * d j := by
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [Etingof.cartanMatrix]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (d _) (adj _ _)]
      -- adj is symmetric: adj j v = adj v j
      have hSymm := hDynkin.1
      simp_rw [show ∀ x, adj x v = adj v x from fun x => by
        exact congr_fun (congr_fun hSymm v) x]
      ring
    -- Step 2: card(v ⟶ j) = adj v j for each j
    have hcard : ∀ j : Fin n, (Fintype.card (@Quiver.Hom (Fin n) Q v j) : ℤ) = adj v j := by
      intro j
      rcases hDynkin.2.2.1 v j with h0 | h1
      · -- adj v j = 0: no arrows v → j
        haveI : IsEmpty (@Quiver.Hom (Fin n) Q v j) := hOrient.1 v j (by omega)
        rw [Fintype.card_eq_zero]; omega
      · -- adj v j = 1: exactly one arrow v → j (v is source, so j → v is impossible)
        rcases hOrient.2.1 v j h1 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · -- v → j exists, Subsingleton → card = 1
          haveI : Unique (@Quiver.Hom (Fin n) Q v j) :=
            { default := e, uniq := fun a => Subsingleton.elim a e }
          simp [Fintype.card_unique, h1]
        · -- j → v exists, but v is a source → contradiction
          exact ((hp j).false e).elim
    -- Step 3: decompose ArrowsOutOf sum via Sigma
    have hsum : (∑ a : @Etingof.ArrowsOutOf (Fin n) Q v, d a.fst) =
        ∑ j : Fin n, adj v j * d j := by
      letI sigmaFT : Fintype (Σ j : Fin n, @Quiver.Hom (Fin n) Q v j) := Sigma.instFintype
      have h_unfold : (∑ a : @Etingof.ArrowsOutOf (Fin n) Q v, d a.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ sigmaFT) (fun a => d a.fst) := by
        apply Finset.sum_congr
        · ext x; simp [Finset.mem_univ]
        · intros; rfl
      rw [h_unfold, Fintype.sum_sigma]
      congr 1; ext j
      change (∑ _ : @Quiver.Hom (Fin n) Q v j, d j) = adj v j * d j
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ (α := @Quiver.Hom (Fin n) Q v j)).card = Fintype.card _ := rfl
      rw [this, show (Fintype.card (@Quiver.Hom (Fin n) Q v j) : ℤ) = adj v j from hcard j]
    -- Combine
    have : ∀ (inst1 inst2 : Fintype (@Etingof.ArrowsOutOf (Fin n) Q v)),
        @Finset.sum _ _ _ (@Finset.univ _ inst1) (fun x => d x.fst) =
        @Finset.sum _ _ _ (@Finset.univ _ inst2) (fun x => d x.fst) := by
      intro i1 i2
      apply Finset.sum_congr
      · ext x; simp [Finset.mem_univ]
      · intros; rfl
    linarith [this (fintypeArrowsOutOfOfSubsingleton v) inferInstance, hsum, hdot]
  · simp only [hv, ite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_zero, sub_zero]

end BackwardConstruction

universe u in
/-- Every positive root of a Dynkin quiver is the dimension vector of some
indecomposable representation.

Given a Dynkin diagram with adjacency matrix `adj`, an orientation `Q` of that
diagram, and a positive root α (i.e., α ≠ 0, B(α, α) = 2, all coordinates
nonneg), there exists an indecomposable quiver representation ρ over any field k
such that `finrank k (ρ.obj v) = α v` at each vertex v.
(Etingof Corollary 6.8.4) -/
theorem Etingof.Corollary6_8_4
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (α : Fin n → ℤ) (hα : Etingof.IsPositiveRoot n adj α)
    (k : Type u) [Field k]
    {Q : Quiver (Fin n)} (hQ : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)] :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  -- Strong induction on coordinate sum, using exists_good_vertex directly.
  -- For the good vertex i: if i is a source or sink in Q, apply F⁺/F⁻ directly.
  -- For mixed vertices: sorry (requires admissible ordering backward construction).
  set A := Etingof.cartanMatrix n adj with hA_def
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  suffices h : ∀ (m : ℕ) (α : Fin n → ℤ) (Q : Quiver (Fin n)),
      (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)) →
      (∑ j, α j).toNat = m →
      Etingof.IsPositiveRoot n adj α →
      Etingof.IsOrientationOf Q adj →
      ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, _} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v))
        (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.IsIndecomposable ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) from
    h _ α Q ‹_› rfl hα hQ
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro α Q hSS hm hα_pos hQ_orient
    haveI : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b) := hSS
    have hα_nonneg := hα_pos.2
    have hα_nonzero := hα_pos.1.1
    have hα_root := hα_pos.1.2
    have hsum_pos := Etingof.sum_pos_of_nonneg_ne_zero α hα_nonneg hα_nonzero
    by_cases hle : ∑ j : Fin n, α j ≤ 1
    · -- Base case: ∑ α = 1, so α is a simple root → use simple representation.
      have hα_sum : ∑ j : Fin n, α j = 1 := by omega
      obtain ⟨p, hp⟩ := Etingof.sum_one_is_simpleRoot α hα_nonneg hα_nonzero hα_sum
      subst hp
      exact Etingof.Corollary6_8_4_simpleRoot p k
    · -- Inductive step: find good vertex, reflect, recurse.
      push_neg at hle
      have hd_sum2 : 2 ≤ ∑ j : Fin n, α j := by omega
      -- Step 1: Find a good vertex i with 0 < (Aα)_i ≤ α_i.
      obtain ⟨i, hi_pos, hi_le⟩ :=
        Etingof.exists_good_vertex hDynkin α hα_nonneg hα_nonzero hα_root hd_sum2
      -- Step 2: α' = s_i(α) is a positive root with strictly smaller coordinate sum.
      set α' := Etingof.simpleReflection n A i α with hα'_def
      have hα'_nonneg : ∀ j, 0 ≤ α' j :=
        Etingof.simpleReflection_nonneg hAsymm α i hα_nonneg hi_le
      have hα'_nonzero : α' ≠ 0 :=
        Etingof.simpleReflection_nonzero hDynkin α i hα_root
      have hα'_B : dotProduct α' (A.mulVec α') = 2 :=
        (Etingof.simpleReflection_preserves_B hDynkin α i).trans hα_root
      have hα'_positive : Etingof.IsPositiveRoot n adj α' :=
        ⟨⟨hα'_nonzero, hα'_B⟩, hα'_nonneg⟩
      have hα'_sum : ∑ j, α' j = (∑ j, α j) - (A.mulVec α) i :=
        Etingof.simpleReflection_sum hAsymm α i
      have hα'_sum_lt : (∑ j, α' j).toNat < m := by
        have h1 : ∑ j, α' j < ∑ j, α j := by linarith
        have h2 : 0 ≤ ∑ j, α' j := Finset.sum_nonneg fun i _ => hα'_nonneg i
        omega
      -- Step 3: The reversed quiver Q' is still an orientation of adj.
      set Q' := @Etingof.reversedAtVertex (Fin n) _ Q i with hQ'_def
      have hQ'_orient : Etingof.IsOrientationOf Q' adj :=
        Etingof.reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hQ_orient _
      have hSS' : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q' a b) :=
        fun a b => Etingof.subsingleton_hom_reversedAtVertex i a b
      -- Step 4: By IH, get an indecomposable ρ' on Q' with dimension vector α'.
      obtain ⟨ρ', hfree', hfinite', hindec', hdim'⟩ :=
        ih _ hα'_sum_lt α' Q' hSS' rfl hα'_positive hQ'_orient
      -- Step 5: Construct ρ on Q from ρ' on Q' via reflection functor at i.
      -- Split on whether i is a sink, source, or mixed vertex in Q.
      haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
      haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
      -- Key: α' ≠ simpleRoot n i (otherwise α_i ≥ 2, B(α,α) ≥ 8)
      have hα'_ne_ei : α' ≠ Etingof.simpleRoot n i := by
        intro heq
        -- α' = e_i means α'_j = 0 for j ≠ i, and α'_i = 1
        have hα'j : ∀ j, j ≠ i → α' j = 0 := by
          intro j hj; rw [heq]; simp [Etingof.simpleRoot, hj]
        -- simpleReflection only changes coordinate i, so α_j = 0 for j ≠ i
        have hαj : ∀ j, j ≠ i → α j = 0 := by
          intro j hj
          have := hα'j j hj
          rw [hα'_def, Etingof.simpleReflection_apply_ne α i j hj] at this
          exact this
        -- ∑ α' = 1, so (Aα)_i = ∑ α - 1 (from hα'_sum)
        have hα'_sum1 : ∑ j, α' j = 1 := by
          rw [heq]; simp [Etingof.simpleRoot, Finset.sum_pi_single']
        have hAαi : (A.mulVec α) i = (∑ j, α j) - 1 := by linarith [hα'_sum]
        -- α'_i = α_i - (Aα)_i = 1, so α_i = ∑ α
        have hα'i : α' i = α i - (A.mulVec α) i := by
          rw [hα'_def]; exact Etingof.simpleReflection_apply_self hAsymm α i
        have hα'i1 : α' i = 1 := by rw [heq]; simp [Etingof.simpleRoot]
        have hαi_eq_sum : α i = ∑ j, α j := by linarith
        -- Since α_j = 0 for j ≠ i and α_i = ∑ α, we have α_i ≥ 2
        have hαi_ge2 : 2 ≤ α i := by linarith
        -- Now (Aα)_i = α_i - 1 ≥ 1, but also (Aα)_i ≤ α_i (from hi_le)
        -- B(α,α) = ∑_j α_j * (Aα)_j. Since α_j = 0 for j ≠ i: B = α_i * (Aα)_i
        -- B(α,α) = α_i * (Aα)_i since α_j = 0 for j ≠ i.
        -- With (Aα)_i = α_i - 1 and B = 2: α_i * (α_i - 1) = 2, so α_i = 2.
        -- Compute B(α,α) directly: since α_j = 0 for j ≠ i, B = α_i² * A_{i,i} = 2α_i².
        -- B(α,α) = 2 gives α_i = 1, contradicting α_i ≥ 2.
        have hB_direct : dotProduct α (A.mulVec α) = 2 * α i ^ 2 := by
          -- Since α_j = 0 for j ≠ i, the bilinear form reduces to A_{i,i} * α_i²
          have h1 : ∀ j, j ≠ i → α j * A.mulVec α j = 0 := fun j hj => by
            rw [hαj j hj, zero_mul]
          have h2 : A.mulVec α i = 2 * α i := by
            simp only [Matrix.mulVec, dotProduct]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            have : ∀ k ∈ Finset.univ.erase i, A i k * α k = 0 :=
              fun k hk => by rw [hαj k (Finset.ne_of_mem_erase hk), mul_zero]
            rw [Finset.sum_eq_zero this, add_zero]
            have hAii : A i i = 2 := by
              show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i i = 2
              simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
              norm_num; have := hDynkin.2.1 i; omega
            rw [hAii]
          simp only [dotProduct]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have : ∀ j ∈ Finset.univ.erase i, α j * A.mulVec α j = 0 :=
            fun j hj => h1 j (Finset.ne_of_mem_erase hj)
          rw [Finset.sum_eq_zero this, add_zero, h2]; ring
        -- B(α,α) = 2 gives α_i² = 1, so α_i = 1, contradicting α_i ≥ 2
        -- hα_root uses expanded (2•1-adj), align with A = cartanMatrix
        have hα_root_A : α ⬝ᵥ A *ᵥ α = 2 := hα_root
        have : α i ^ 2 = 1 := by linarith
        have : α i = 1 := by
          have := hα_nonneg i
          nlinarith [sq_nonneg (α i - 1)]
        omega
      -- Step 5: Apply reflection functor at i on Q' to recover a representation on Q.
      -- ρ' is not simple at i (since α' ≠ e_i and dim vector matches α')
      have hρ'_not_simple : ¬ρ'.IsSimpleAt i := by
        intro ⟨h1, h2⟩
        apply hα'_ne_ei; ext j
        simp only [Etingof.simpleRoot, Pi.single_apply]
        by_cases hj : j = i
        · simp only [hj, ite_true]
          have := (hdim' i).symm
          rw [h1] at this; exact_mod_cast this.symm
        · simp only [hj, ite_false]
          have := (hdim' j).symm
          rw [h2 j hj] at this; exact_mod_cast this.symm
      -- Step 5b: Apply reflection functor at i on Q' to get representation on Q.
      --
      -- UNIVERSE BLOCKER: The reflection functor F⁻/F⁺ at vertex i constructs
      -- a cokernel/kernel whose universe Lean cannot unify with the target
      -- universe u. Specifically, reflectionFunctorMinus produces
      -- QuiverRepresentation.{u, 0, max u₁ ?, u₁} but we need .{u, 0, u, _}.
      --
      -- Possible fixes:
      -- 1. Reconstruct the representation at universe u using the LinearEquiv
      --    from reflFunctorMinus_equivAt_eq (cokernel ≃ₗ direct sum quotient)
      --    combined with Module.Free + finrank to get Fin m → k at vertex i
      -- 2. Add universe annotations to reflectionFunctorMinus/Plus definitions
      -- 3. Restructure the proof to use universe 0 internally (matching
      --    CoxeterInfrastructure) and transport to universe u at the end
      --
      -- Additionally, the MIXED VERTEX case (i neither source nor sink in Q)
      -- requires admissible ordering backward walk, not just a single F⁻/F⁺.
      --
      -- Infrastructure ready for source/sink cases:
      --   ✓ hρ'_not_simple (ρ' not simple at i, since α' ≠ e_i)
      --   ✓ Prop 6.6.5 source/sink: not simple → injective/surjective
      --   ✓ Prop 6.6.7 source/sink: F⁻/F⁺ indecomposable or zero
      --   ✓ Prop 6.6.8 source/sink: dim(F⁻/F⁺) = s_i(dim)
      --   ✓ simpleReflectionDimVector_eq_simpleReflection_source
      --   ✓ transportReversedTwice
      sorry
