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
import EtingofRepresentationTheory.Chapter6.Lemma6_7_2

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

open Etingof in
/-- For a positive root α on a Dynkin diagram, there exists a prefix of the replicated
admissible ordering that reduces α to a simple root. All intermediates are nonneg.

The proof uses `generalized_Lemma6_7_2` (iteration must produce a negative entry)
and `positive_root_cartan_bound` (intermediates stay nonneg while sum ≥ 2). -/
private lemma exists_prefix_to_simpleRoot
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (σ : List (Fin n)) (hσ : Etingof.IsAdmissibleOrdering Q σ)
    (α : Fin n → ℤ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_nonzero : α ≠ 0)
    (hα_B : dotProduct α ((Etingof.cartanMatrix n adj).mulVec α) = 2) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices α =
        Etingof.simpleRoot n p ∧
      (∀ m (hm : m < vertices.length),
        @Etingof.IsSink (Fin n)
          (@Etingof.iteratedReversedAtVertices _ _ Q (vertices.take m))
          (vertices.get ⟨m, hm⟩)) := by
  set A := Etingof.cartanMatrix n adj with hA_def
  -- By generalized_Lemma6_7_2, iterating the Coxeter element produces a negative entry
  obtain ⟨N, v_neg, hN⟩ := Etingof.generalized_Lemma6_7_2 hDynkin σ hσ.perm α hα_nonneg hα_nonzero
  -- The full vertex list for N rounds
  set fullList := (List.replicate N σ).flatten with hfullList_def
  -- fullList has the sinks property (from admissible_sinks_replicated with j = 0)
  have hSinks_full : ∀ m (hm : m < fullList.length),
      @Etingof.IsSink (Fin n)
        (@Etingof.iteratedReversedAtVertices _ _ Q (fullList.take m))
        (fullList.get ⟨m, hm⟩) := by
    intro m hm
    have hm' : m < ((List.replicate N σ).flatten ++ σ.take 0).length := by
      simp only [List.take_zero, List.append_nil, ← hfullList_def]; exact hm
    have h := Etingof.admissible_sinks_replicated Q σ hσ N 0 (Nat.zero_le _) m hm'
    have htake_eq : ((List.replicate N σ).flatten ++ σ.take 0).take m =
        fullList.take m := by
      congr 1; simp [hfullList_def]
    rw [htake_eq] at h
    have helem_eq : ((List.replicate N σ).flatten ++ σ.take 0).get ⟨m, hm'⟩ =
        fullList.get ⟨m, hm⟩ := by
      simp only [List.get_eq_getElem, List.take_zero,
        List.append_nil, hfullList_def]
    rw [helem_eq] at h
    exact h
  -- iteratedSimpleReflection on fullList = c^N(α)
  have hfull_eq : Etingof.iteratedSimpleReflection n A fullList α =
      (fun w => Etingof.iteratedSimpleReflection n A σ w)^[N] α := by
    rw [hfullList_def, Etingof.iteratedSimpleReflection_replicate_eq_iterate]
  -- c^N(α) has a negative entry, so some intermediate must have sum ≤ 1
  -- Find the first index where the intermediate is NOT (nonneg with sum ≥ 2)
  -- by showing all intermediates are nonneg as long as sum ≥ 2.
  -- Use well-ordering on the set of "bad" indices.
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  -- Key: for any prefix where all prior intermediates have sum ≥ 2,
  -- the current intermediate is nonneg with B = 2.
  have hprefix_nonneg_B : ∀ k ≤ fullList.length,
      (∀ j < k, 2 ≤ ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take j) α i) →
      (∀ i, 0 ≤ Etingof.iteratedSimpleReflection n A (fullList.take k) α i) ∧
      dotProduct (Etingof.iteratedSimpleReflection n A (fullList.take k) α)
        (A.mulVec (Etingof.iteratedSimpleReflection n A (fullList.take k) α)) = 2 := by
    intro k hk hall
    induction k with
    | zero => simp [Etingof.iteratedSimpleReflection]; exact ⟨hα_nonneg, hα_B⟩
    | succ k ih =>
      have hk' : k ≤ fullList.length := by omega
      obtain ⟨ih_nn, ih_B⟩ := ih hk' (fun j hj => hall j (by omega))
      have hk_sum := hall k (by omega)
      set dk := Etingof.iteratedSimpleReflection n A (fullList.take k) α
      have hcartan := Etingof.positive_root_cartan_bound hDynkin dk ih_nn ih_B hk_sum
      have hk1 : k + 1 ≤ fullList.length := hk
      have hk_lt : k < fullList.length := by omega
      have htake : fullList.take (k + 1) =
          fullList.take k ++ [fullList.get ⟨k, hk_lt⟩] := by
        apply List.ext_getElem
        · simp [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ _)]
        · intro i hi1 hi2
          simp only [List.getElem_append]
          split
          · next hi => simp [List.getElem_take]
          · next hi =>
            simp [List.length_take] at hi1 hi
            have : i = k := by omega
            subst this
            simp [List.get_eq_getElem]
      rw [htake, Etingof.iteratedSimpleReflection_append]
      simp only [Etingof.iteratedSimpleReflection, List.foldl]
      set vk := fullList.get ⟨k, by omega⟩
      constructor
      · exact Etingof.simpleReflection_nonneg hAsymm dk vk ih_nn (hcartan vk)
      · exact (Etingof.simpleReflection_preserves_B hDynkin dk vk).trans ih_B
  -- The last intermediate c^N(α) has a negative entry
  have hbad : ¬(∀ j < fullList.length,
      2 ≤ ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take j) α i) := by
    intro hall
    obtain ⟨hnn, _⟩ := hprefix_nonneg_B fullList.length le_rfl hall
    rw [List.take_length] at hnn
    rw [hfull_eq] at hnn
    exact not_le.mpr (hN) (hnn v_neg)
  -- Find the first "bad" index (where sum < 2)
  push_neg at hbad
  obtain ⟨k₀, hk₀_lt, hk₀_sum⟩ := hbad
  -- Get the minimal such index using Nat.find
  have hexists : ∃ m, m < fullList.length ∧
      ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take m) α i < 2 :=
    ⟨k₀, hk₀_lt, hk₀_sum⟩
  -- Use well-founded recursion to find the minimum
  have hexists' : ∃ m, (m < fullList.length ∧
      ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take m) α i < 2) := hexists
  set m := Nat.find hexists' with hm_def
  have hm_spec := Nat.find_spec hexists'
  have hm_lt := hm_spec.1
  have hm_sum : ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take m) α i < 2 :=
    hm_spec.2
  have hm_min : ∀ j < m,
      2 ≤ ∑ i, Etingof.iteratedSimpleReflection n A (fullList.take j) α i := by
    intro j hj
    by_contra h; push_neg at h
    exact Nat.find_min hexists' hj ⟨by omega, h⟩
  -- All intermediates before m have sum ≥ 2, so the m-th is nonneg with B = 2
  obtain ⟨hm_nn, hm_B⟩ := hprefix_nonneg_B m (by omega) hm_min
  set dm := Etingof.iteratedSimpleReflection n A (fullList.take m) α
  -- dm is nonneg, nonzero (B=2), and sum < 2
  have hm_nonzero : dm ≠ 0 := by
    intro h0
    have : dotProduct dm (A.mulVec dm) = 0 := by rw [h0]; simp [dotProduct, Matrix.mulVec]
    linarith
  have hm_sum_pos := Etingof.sum_pos_of_nonneg_ne_zero dm hm_nn hm_nonzero
  have hm_sum1 : ∑ i, dm i = 1 := by omega
  obtain ⟨p, hp⟩ := Etingof.sum_one_is_simpleRoot dm hm_nn hm_nonzero hm_sum1
  -- The prefix fullList.take m reduces α to simpleRoot p
  refine ⟨fullList.take m, p, hp, ?_⟩
  -- Sinks property for the prefix
  intro j hj
  have hj_lt_m : j < m := by
    rw [List.length_take] at hj; exact lt_of_lt_of_le hj (min_le_left _ _)
  have hj_lt : j < fullList.length := by omega
  rw [List.take_take, min_eq_left (by omega : j ≤ m)]
  have : (fullList.take m).get ⟨j, hj⟩ = fullList.get ⟨j, hj_lt⟩ := by
    simp [List.get_eq_getElem, List.getElem_take]
  rw [this]
  exact hSinks_full j hj_lt

universe u in
set_option maxHeartbeats 800000 in
/-- **Backward construction**: given a vertex list where each vertex is a sink at the
appropriate iterated-reversed quiver, and a positive root d that reduces to a simple root
along this list, construct an indecomposable representation on Q with dimension vector d.

The proof is by induction on the vertex list. At each step, v is a sink of Q, so v is a
source of Q' = reversedAtVertex Q v. We recurse on Q' with reflected dim vector s_v(d),
then apply F⁻ at source v on Q' to get back to Q. -/
private lemma backward_construct_rep
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (k : Type u) [Field k]
    (vertices : List (Fin n))
    {Q : @Quiver.{0, 0} (Fin n)}
    (hOrient : Etingof.IsOrientationOf Q adj)
    (hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b))
    (hSinks : ∀ m (hm : m < vertices.length),
      @Etingof.IsSink (Fin n)
        (@Etingof.iteratedReversedAtVertices _ _ Q (vertices.take m))
        (vertices.get ⟨m, hm⟩))
    (d : Fin n → ℤ)
    (hd_nonneg : ∀ v, 0 ≤ d v)
    (hd_nonzero : d ≠ 0)
    (hd_B : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2)
    (p : Fin n)
    (hreduce : Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices d =
      Etingof.simpleRoot n p) :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧ ∀ v, (d v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  set A := Etingof.cartanMatrix n adj with hA_def
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  induction vertices generalizing Q d with
  | nil =>
    -- d = simpleRoot p
    simp [Etingof.iteratedSimpleReflection] at hreduce
    subst hreduce
    exact Etingof.Corollary6_8_4_simpleRoot p k
  | cons v rest ih =>
    -- Check if d is already a simple root (sum ≤ 1)
    by_cases hle : ∑ j : Fin n, d j ≤ 1
    · -- d is a simple root: use base case directly
      have hsum_pos := Etingof.sum_pos_of_nonneg_ne_zero d hd_nonneg hd_nonzero
      have hd_sum1 : ∑ j, d j = 1 := by omega
      obtain ⟨q, hq⟩ := Etingof.sum_one_is_simpleRoot d hd_nonneg hd_nonzero hd_sum1
      subst hq
      exact Etingof.Corollary6_8_4_simpleRoot q k
    · -- d has sum ≥ 2: reflect at v (sink of Q), recurse
      push_neg at hle
      have hd_sum2 : 2 ≤ ∑ j, d j := by omega
      -- v is a sink of Q
      have hv_sink : @Etingof.IsSink (Fin n) Q v := by
        have := hSinks 0 (by simp)
        simp only [List.take_zero, Etingof.iteratedReversedAtVertices] at this
        exact this
      -- Q_rev = reversedAtVertex Q v; v is source in Q_rev
      let Q_rev := @Etingof.reversedAtVertex (Fin n) _ Q v
      have hv_source : @Etingof.IsSource (Fin n) Q_rev v :=
        @Etingof.isSink_reversedAtVertex_isSource (Fin n) _ Q v hv_sink
      have hOrient_rev : @Etingof.IsOrientationOf n Q_rev adj :=
        Etingof.reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hOrient v
      have hSS_rev : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q_rev a b) :=
        fun a b => Etingof.subsingleton_hom_reversedAtVertex v a b
      -- Reflected dimension vector
      set d₁ := Etingof.simpleReflection n A v d with hd₁_def
      have hd₁_nonneg : ∀ j, 0 ≤ d₁ j :=
        Etingof.simpleReflection_nonneg hAsymm d v hd_nonneg
          (Etingof.positive_root_cartan_bound hDynkin d hd_nonneg hd_B hd_sum2 v)
      have hd₁_nonzero : d₁ ≠ 0 := Etingof.simpleReflection_nonzero hDynkin d v hd_B
      have hd₁_B : dotProduct d₁ (A.mulVec d₁) = 2 :=
        (Etingof.simpleReflection_preserves_B hDynkin d v).trans hd_B
      -- iter rest d₁ = simpleRoot p
      have hreduce_rest : Etingof.iteratedSimpleReflection n A rest d₁ =
          Etingof.simpleRoot n p := by
        rw [← hreduce]; rfl
      -- Sinks property for rest on Q_rev
      have hSinks_rest : ∀ m (hm : m < rest.length),
          @Etingof.IsSink (Fin n)
            (@Etingof.iteratedReversedAtVertices _ _ Q_rev (rest.take m))
            (rest.get ⟨m, hm⟩) := by
        intro m hm
        have hm1 : m + 1 < (v :: rest).length := by simp; omega
        have h := hSinks (m + 1) hm1
        -- Simplify: (v :: rest).take (m+1) = v :: rest.take m
        have htake : (v :: rest).take (m + 1) = v :: rest.take m := by
          rfl
        -- (v :: rest)[m+1] = rest[m]
        have hget : (v :: rest).get ⟨m + 1, hm1⟩ = rest.get ⟨m, hm⟩ := by
          simp [List.get_eq_getElem]
        rw [htake, hget] at h
        -- iteratedReversedAtVertices Q (v :: rest.take m) =
        --   iteratedReversedAtVertices Q_rev (rest.take m)
        show @Etingof.IsSink (Fin n)
          (@Etingof.iteratedReversedAtVertices _ _ Q_rev (rest.take m))
          (rest.get ⟨m, hm⟩)
        convert h using 2
      -- IH gives ρ₁ on Q_rev with dim d₁
      obtain ⟨ρ₁, hFree₁, hFinite₁, hIndec₁, hDim₁⟩ :=
        ih hOrient_rev hSS_rev hSinks_rest d₁ hd₁_nonneg hd₁_nonzero hd₁_B hreduce_rest
      -- d₁ ≠ simpleRoot v (otherwise d = s_v(e_v) has sum = -1, contradicting nonneg)
      have hd₁_ne_ev : d₁ ≠ Etingof.simpleRoot n v := by
        intro heq
        have hinv : d = Etingof.simpleReflection n A v (Etingof.simpleRoot n v) := by
          rw [← heq, hd₁_def]
          exact (Etingof.simpleReflection_involutive hAsymm
            (Etingof.simpleRoot_B_eq_two hDynkin) v d).symm
        have hd_sum_eq : ∑ j, d j =
            (∑ j, Etingof.simpleRoot n v j) -
            (A.mulVec (Etingof.simpleRoot n v)) v := by
          conv_lhs => rw [hinv]
          exact Etingof.simpleReflection_sum hAsymm (Etingof.simpleRoot n v) v
        simp only [Etingof.simpleRoot, Finset.sum_pi_single', Finset.mem_univ, ite_true] at hd_sum_eq
        have hAev : (A.mulVec (Pi.single v (1 : ℤ))) v = 2 := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) v v = 2
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
          norm_num; have := hDynkin.2.1 v; omega
        rw [hAev] at hd_sum_eq
        linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hd_nonneg j)]
      -- ρ₁ not simple at v
      have hρ₁_not_simple : ¬ρ₁.IsSimpleAt v := by
        intro ⟨h1, h2⟩
        apply hd₁_ne_ev; ext j
        simp only [Etingof.simpleRoot, Pi.single_apply]
        by_cases hj : j = v
        · simp only [hj, ite_true]
          have := (hDim₁ v).symm; rw [h1] at this; exact_mod_cast this.symm
        · simp only [hj, ite_false]
          have := (hDim₁ j).symm; rw [h2 j hj] at this; exact_mod_cast this.symm
      classical
      -- Set up Fintype for ArrowsOutOf
      haveI hFT_out : Fintype (@Etingof.ArrowsOutOf (Fin n) Q_rev v) :=
        fintypeArrowsOutOfOfSubsingleton (Q := Q_rev) v
      -- Prop 6.6.5: sourceMap injective
      have h_inj : Function.Injective (ρ₁.sourceMap v) := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        rcases @Etingof.Proposition6_6_5_source k _ (Fin n) _ Q_rev
          ρ₁ v _ _ _ hv_source hIndec₁ with hsimple | hinj
        · exact absurd hsimple hρ₁_not_simple
        · exact hinj
      -- Apply F⁻ at source v on Q_rev
      set fm := @Etingof.reflectionFunctorMinus k _ (Fin n) _ Q_rev v hv_source ρ₁ _
      -- Involutivity: reversedAtVertex Q_rev v = Q
      have hinvol : @Etingof.reversedAtVertex (Fin n) _
          (@Etingof.reversedAtVertex (Fin n) _ Q v) v = Q :=
        @Etingof.reversedAtVertex_twice (Fin n) _ Q v
      -- Bridge dim vector
      set d' := fun w => (@Module.finrank k (ρ₁.obj w)
          _ (ρ₁.instAddCommMonoid w) (ρ₁.instModule w) : ℤ)
      have hd_eq : d' = fun w => (d₁ w : ℤ) := by
        ext w; simp only [d']; exact (hDim₁ w).symm
      have hbridge :=
        @simpleReflectionDimVector_eq_simpleReflection_source _ _
          hDynkin Q_rev hOrient_rev hSS_rev v hv_source d'
      -- Involutivity of simple reflection: s_v(s_v(d)) = d
      have hinvol_d : Etingof.simpleReflection n A v d₁ = d := by
        rw [hd₁_def]
        exact Etingof.simpleReflection_involutive hAsymm
          (Etingof.simpleRoot_B_eq_two hDynkin) v d
      -- Prop 6.6.7: F⁻(ρ₁) indecomposable or zero
      have hIndec_or_zero :
          @Etingof.QuiverRepresentation.IsIndecomposable k _ _
            (@Etingof.reversedAtVertex (Fin n) _ Q_rev v) fm ∨
          @Etingof.QuiverRepresentation.IsZero k _ _
            (@Etingof.reversedAtVertex (Fin n) _ Q_rev v) fm := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        exact @Etingof.Proposition6_6_7_source k _ _ _ Q_rev v hv_source ρ₁ _ _ _ hIndec₁
      -- Prop 6.6.8: dim vector
      have h668 : ∀ w,
          (fm.finrankAt' k w : ℤ) =
          Etingof.simpleReflectionDimVector
            (fun (a : @Etingof.ArrowsOutOf (Fin n) Q_rev v) => a.1) v d' w := by
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        exact @Etingof.Proposition6_6_8_source k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _ h_inj
      -- Free for fm
      have hFree_fm : ∀ w, Module.Free k
          (@Etingof.QuiverRepresentation.obj k (Fin n) _
            (@Etingof.reversedAtVertex (Fin n) _ Q_rev v) fm w) := by
        intro w
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        by_cases hw : w = v
        · rw [hw]; exact @reflFunctorMinus_free_eq k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _
        · exact @reflFunctorMinus_free_ne k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ w hw
      -- Finite for fm
      have hFinite_fm : ∀ w, Module.Finite k
          (@Etingof.QuiverRepresentation.obj k (Fin n) _
            (@Etingof.reversedAtVertex (Fin n) _ Q_rev v) fm w) := by
        intro w
        haveI : ∀ w, Module.Free k (ρ₁.obj w) := hFree₁
        haveI : ∀ w, Module.Finite k (ρ₁.obj w) := hFinite₁
        by_cases hw : w = v
        · rw [hw]; exact @reflFunctorMinus_finite_eq k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ _
        · exact @reflFunctorMinus_finite_ne k _ (Fin n) _ Q_rev v hv_source ρ₁ _ _ w hw
      -- Exclude zero case
      have hIndec_fm : @Etingof.QuiverRepresentation.IsIndecomposable k _ _
          (@Etingof.reversedAtVertex (Fin n) _ Q_rev v) fm := by
        rcases hIndec_or_zero with h | h_zero
        · exact h
        · exfalso
          obtain ⟨⟨w, hw⟩, _⟩ := hIndec₁
          suffices hs : ∀ w, Subsingleton (ρ₁.obj w) from
            absurd (hs w) (not_subsingleton_iff_nontrivial.mpr hw)
          intro w
          by_cases hw : w = v
          · rw [hw]
            refine ⟨fun a b => ?_⟩
            have hsub : ∀ (a : @Etingof.ArrowsOutOf (Fin n) Q_rev v),
                Subsingleton (ρ₁.obj a.1) :=
              fun ⟨m, hm⟩ => (Equiv.subsingleton_congr
                (@Etingof.reflFunctorMinus_equivAt_ne k _ (Fin n) _ Q_rev
                  v hv_source ρ₁ _ m (fun h => (hv_source m).false (h ▸ hm))).toEquiv).mp
                (h_zero m)
            haveI h_ds_ss : Subsingleton (DirectSum (@Etingof.ArrowsOutOf (Fin n) Q_rev v)
                (fun a => ρ₁.obj a.1)) :=
              ⟨fun x y => DFinsupp.ext (fun a => @Subsingleton.elim _ (hsub a) _ _)⟩
            exact @Subsingleton.elim _ h_inj.subsingleton a b
          · exact (Equiv.subsingleton_congr
              (@Etingof.reflFunctorMinus_equivAt_ne k _ (Fin n) _ Q_rev
                v hv_source ρ₁ _ w hw).toEquiv).mp (h_zero w)
      -- Dim vector
      have hDim_fm : ∀ w, (d w : ℤ) = ↑(fm.finrankAt' k w) := by
        intro w; rw [h668 w]
        show (d w : ℤ) = Etingof.simpleReflectionDimVector
          (fun (a : @Etingof.ArrowsOutOf (Fin n) Q_rev v) => a.1) v d' w
        have hgoal : (d w : ℤ) =
            Etingof.simpleReflection n (Etingof.cartanMatrix n adj) v d' w := by
          rw [← hA_def, hd_eq]; exact (congr_fun hinvol_d w).symm
        rw [hgoal]; convert (congr_fun hbridge w).symm using 2
      -- Transport to Q via double reversal
      exact hinvol ▸
        ⟨fm, hFree_fm, hFinite_fm, hIndec_fm, fun w => by
         change (d w : ℤ) = _; rw [hDim_fm w]; rfl⟩

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
    {Q : @Quiver.{0, 0} (Fin n)} (hQ : Etingof.IsOrientationOf Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)] :
    ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v))
      (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧
      ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := by
  -- Strong induction on coordinate sum, using exists_good_vertex directly.
  -- For the good vertex i: if i is a source or sink in Q, apply F⁺/F⁻ directly.
  -- For mixed vertices: sorry (requires admissible ordering backward construction).
  set A := Etingof.cartanMatrix n adj with hA_def
  have hAsymm : A.IsSymm := Etingof.cartanMatrix_isSymm hDynkin.1
  suffices h : ∀ (m : ℕ) (α : Fin n → ℤ) (Q : @Quiver.{0, 0} (Fin n)),
      (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)) →
      (∑ j, α j).toNat = m →
      Etingof.IsPositiveRoot n adj α →
      Etingof.IsOrientationOf Q adj →
      ∃ (ρ : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v))
        (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.IsIndecomposable ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v)) from
    h _ α Q ‹_› rfl hα hQ
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro α Q hSS hm hα_pos hQ_orient
    letI : Quiver (Fin n) := Q
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
      let Q' := @Etingof.reversedAtVertex (Fin n) _ Q i
      have hQ'_orient : Etingof.IsOrientationOf Q' adj :=
        Etingof.reversedAtVertex_isOrientationOf hDynkin.1 hDynkin.2.1 hQ_orient _
      have hSS' : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q' a b) :=
        fun a b => Etingof.subsingleton_hom_reversedAtVertex i a b
      -- Step 4: By IH, get an indecomposable ρ' on Q' with dimension vector α'.
      obtain ⟨ρ', hfree', hfinite', hindec', hdim'⟩ :=
        ih _ hα'_sum_lt α' Q' hSS' rfl hα'_positive hQ'_orient
      -- Step 5: Construct ρ on Q from ρ' on Q' via reflection functor at i.
      -- Split on whether i is a sink, source, or mixed vertex in Q.
      -- NOTE: Do NOT use haveI for Free/Finite here — it creates instance
      -- conflicts when reflection functor reps (on reversedAtVertex Q' i)
      -- coexist, since fp.obj v = ρ'.obj v for v ≠ i and both instModule
      -- become synthesizable.
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
        haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
        haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
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
      -- Key synthesis fix: do NOT use haveI for Free/Finite of ρ' in outer scope.
      -- The attribute [instance] on QuiverRepresentation.instModule makes both
      -- ρ'.instModule and fp.instModule discoverable for the same carrier type
      -- (since fp.obj v = ρ'.obj v for v ≠ i), causing synthesis conflicts.
      -- Solution: transport fp to Q via hinvol ▸, then sorry sub-proofs.
      classical
      -- Double reversal: reversedAtVertex(Q', i) = Q
      have hinvol : @Etingof.reversedAtVertex (Fin n) _
          (@Etingof.reversedAtVertex (Fin n) _ Q i) i = Q :=
        @Etingof.reversedAtVertex_twice (Fin n) _ Q i
      -- Involutivity of simple reflection: s_i(s_i(α)) = α
      have hinvol_α : Etingof.simpleReflection n A i α' = α := by
        rw [hα'_def]
        exact Etingof.simpleReflection_involutive
          (Etingof.cartanMatrix_isSymm hDynkin.1)
          (Etingof.simpleRoot_B_eq_two hDynkin) i α
      -- Helper: prove reflection step for both source and sink cases.
      -- Uses @ notation throughout to avoid letI quiver synthesis conflicts.
      -- The key pattern (from CoxeterInfrastructure): prove everything about the
      -- reflected representation fp/fm, then transport to Q via hinvol.
      by_cases hi_source : @Etingof.IsSource (Fin n) Q i
      · -- Case 1: i is a source in Q → i is a sink in Q'
        have hi_sink_Q' : @Etingof.IsSink (Fin n) Q' i :=
          @Etingof.isSource_reversedAtVertex_isSink (Fin n) _ Q i hi_source
        haveI hFT_into : Fintype (@Etingof.ArrowsInto (Fin n) Q' i) :=
          @Etingof.fintypeArrowsIntoOfSubsingleton _ Q' hSS' i
        -- Prop 6.6.5: not simple → sinkMap surjective (register instances locally)
        have h_surj : Function.Surjective (ρ'.sinkMap i) := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          rcases @Etingof.Proposition6_6_5_sink k _ (Fin n) _ Q'
            ρ' i _ _ hi_sink_Q' hindec' with hsimple | hsurj
          · exact absurd hsimple hρ'_not_simple
          · exact hsurj
        -- Apply F⁺ at sink i on Q'
        -- Precompute dim vector bridge before introducing fp (avoids quiver conflict)
        set d' := fun v => (@Module.finrank k (ρ'.obj v)
          _ (ρ'.instAddCommMonoid v) (ρ'.instModule v) : ℤ)
        have hd_eq : d' = fun v => (α' v : ℤ) := by
          ext v; simp only [d']; exact (hdim' v).symm
        have hbridge :=
          @Etingof.simpleReflectionDimVector_eq_simpleReflection _ _
            hDynkin Q' hQ'_orient hSS' i hi_sink_Q' d'
        -- Prop 6.6.7: Indec or zero (register instances locally)
        have hIndec_or_zero :
            @Etingof.QuiverRepresentation.IsIndecomposable k _ _
              (@Etingof.reversedAtVertex (Fin n) _ Q' i)
              (@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ') ∨
            @Etingof.QuiverRepresentation.IsZero k _ _
              (@Etingof.reversedAtVertex (Fin n) _ Q' i)
              (@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ') := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          exact @Etingof.Proposition6_6_7_sink k _ _ _ Q' i hi_sink_Q' ρ' _ _ hindec'
        -- Prop 6.6.8: dim vector (register instances locally)
        have h668 : ∀ v,
            ((@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ').finrankAt' k v : ℤ) =
            Etingof.simpleReflectionDimVector (fun (a : @Etingof.ArrowsInto (Fin n) Q' i) => a.1)
              i (fun w => (@Module.finrank k (ρ'.obj w) _ (ρ'.instAddCommMonoid w) (ρ'.instModule w) : ℤ)) v := by
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          exact @Etingof.Proposition6_6_8_sink k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _ h_surj
        -- Free for fp (register instances locally)
        have hFree_fp : ∀ v, Module.Free k
            (@Etingof.QuiverRepresentation.obj k (Fin n) _
              (@Etingof.reversedAtVertex (Fin n) _ Q' i)
              (@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ') v) := by
          intro v
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_free_eq k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _
          · exact @Etingof.reflFunctorPlus_free_ne k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ v hv
        -- Finite for fp
        have hFinite_fp : ∀ v, Module.Finite k
            (@Etingof.QuiverRepresentation.obj k (Fin n) _
              (@Etingof.reversedAtVertex (Fin n) _ Q' i)
              (@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ') v) := by
          intro v
          haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
          haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
          by_cases hv : v = i
          · rw [hv]; exact @Etingof.reflFunctorPlus_finite_eq k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ _ _
          · exact @Etingof.reflFunctorPlus_finite_ne k _ (Fin n) _ Q' i hi_sink_Q' ρ' _ v hv
        -- Exclude zero case for indecomposability
        have hIndec_fp : @Etingof.QuiverRepresentation.IsIndecomposable k _ _
            (@Etingof.reversedAtVertex (Fin n) _ Q' i)
            (@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ') := by
          rcases hIndec_or_zero with h | h_zero
          · exact h
          · exfalso
            obtain ⟨⟨v, hv⟩, _⟩ := hindec'
            suffices hs : ∀ w, Subsingleton (ρ'.obj w) from
              absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
            intro w
            by_cases hw : w = i
            · rw [hw]
              -- At sink i: sinkMap surjective + all source spaces subsingleton → subsingleton
              refine ⟨fun a b => ?_⟩
              obtain ⟨x, rfl⟩ := h_surj a
              obtain ⟨y, rfl⟩ := h_surj b
              suffices x = y by rw [this]
              have hds : ∀ z : DirectSum (@Etingof.ArrowsInto (Fin n) Q' i)
                  (fun a => ρ'.obj a.1), z = 0 :=
                fun z => DFinsupp.ext (fun ⟨m, hm⟩ =>
                  @Subsingleton.elim _
                    (Equiv.subsingleton_congr
                      (@Etingof.reflFunctorPlus_equivAt_ne k _ (Fin n) _ Q'
                        i hi_sink_Q' ρ' m (fun h => (hi_sink_Q' m).false (h ▸ hm))).toEquiv
                      |>.mp (h_zero m)) _ _)
              exact (hds x).trans (hds y).symm
            · exact (Equiv.subsingleton_congr
                (@Etingof.reflFunctorPlus_equivAt_ne k _ (Fin n) _ Q'
                  i hi_sink_Q' ρ' w hw).toEquiv).mp (h_zero w)
        -- Dim vector: combine Prop 6.6.8 + bridge + involution
        have hDim_fp : ∀ v, (α v : ℤ) =
            ↑((@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ').finrankAt' k v) := by
          intro v; rw [h668 v]
          show (α v : ℤ) = Etingof.simpleReflectionDimVector
            (fun (a : @Etingof.ArrowsInto (Fin n) Q' i) => a.1) i d' v
          -- hbridge uses a different Fintype instance, bridge via convert
          have hgoal : (α v : ℤ) = Etingof.simpleReflection n (Etingof.cartanMatrix n adj) i d' v := by
            rw [← hA_def, hd_eq]; exact (congr_fun hinvol_α v).symm
          rw [hgoal]; convert (congr_fun hbridge v).symm using 2
        -- Transport to Q via double reversal
        exact hinvol ▸
          ⟨@Etingof.reflectionFunctorPlus k _ (Fin n) _ Q' i hi_sink_Q' ρ',
           hFree_fp, hFinite_fp, hIndec_fp, fun v => by
           change (α v : ℤ) = _; rw [hDim_fp v]; rfl⟩
      · -- Cases 2 and 3: sink and mixed
        by_cases hi_sink : @Etingof.IsSink (Fin n) Q i
        · -- Case 2: i is a sink in Q → i is a source in Q'
          have hi_source_Q' : @Etingof.IsSource (Fin n) Q' i :=
            @Etingof.isSink_reversedAtVertex_isSource (Fin n) _ Q i hi_sink
          haveI hFT_out : Fintype (@Etingof.ArrowsOutOf (Fin n) Q' i) :=
            fintypeArrowsOutOfOfSubsingleton (Q := Q') i
          -- Prop 6.6.5 source: not simple → sourceMap injective
          have h_inj : Function.Injective (ρ'.sourceMap i) := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            rcases @Etingof.Proposition6_6_5_source k _ (Fin n) _ Q'
              ρ' i _ _ _ hi_source_Q' hindec' with hsimple | hinj
            · exact absurd hsimple hρ'_not_simple
            · exact hinj
          -- Precompute dim vector bridge
          set d' := fun v => (@Module.finrank k (ρ'.obj v)
            _ (ρ'.instAddCommMonoid v) (ρ'.instModule v) : ℤ)
          have hd_eq : d' = fun v => (α' v : ℤ) := by
            ext v; simp only [d']; exact (hdim' v).symm
          have hbridge :=
            simpleReflectionDimVector_eq_simpleReflection_source
              hDynkin hQ'_orient i hi_source_Q' d'
          -- Abbreviation for F⁻ applied at source i on Q'
          let fm := @Etingof.reflectionFunctorMinus k _ (Fin n) _ Q' i hi_source_Q' ρ' hFT_out
          -- Prop 6.6.7 source
          have hIndec_or_zero :
              @Etingof.QuiverRepresentation.IsIndecomposable k _ _
                (@Etingof.reversedAtVertex (Fin n) _ Q' i) fm ∨
              @Etingof.QuiverRepresentation.IsZero k _ _
                (@Etingof.reversedAtVertex (Fin n) _ Q' i) fm := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            exact @Etingof.Proposition6_6_7_source k _ _ _ Q' i hi_source_Q' ρ' _ _ _ hindec'
          -- Prop 6.6.8 source
          have h668 : ∀ v,
              (fm.finrankAt' k v : ℤ) =
              Etingof.simpleReflectionDimVector (fun (a : @Etingof.ArrowsOutOf (Fin n) Q' i) => a.1)
                i (fun w => (@Module.finrank k (ρ'.obj w) _ (ρ'.instAddCommMonoid w) (ρ'.instModule w) : ℤ)) v := by
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            exact @Etingof.Proposition6_6_8_source k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _ h_inj
          -- Free for fm
          have hFree_fm : ∀ v, Module.Free k
              (@Etingof.QuiverRepresentation.obj k (Fin n) _
                (@Etingof.reversedAtVertex (Fin n) _ Q' i) fm v) := by
            intro v
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            by_cases hv : v = i
            · rw [hv]; exact @reflFunctorMinus_free_eq k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _
            · exact @reflFunctorMinus_free_ne k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ v hv
          -- Finite for fm
          have hFinite_fm : ∀ v, Module.Finite k
              (@Etingof.QuiverRepresentation.obj k (Fin n) _
                (@Etingof.reversedAtVertex (Fin n) _ Q' i) fm v) := by
            intro v
            haveI : ∀ v, Module.Free k (ρ'.obj v) := hfree'
            haveI : ∀ v, Module.Finite k (ρ'.obj v) := hfinite'
            by_cases hv : v = i
            · rw [hv]; exact @reflFunctorMinus_finite_eq k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ _
            · exact @reflFunctorMinus_finite_ne k _ (Fin n) _ Q' i hi_source_Q' ρ' _ _ v hv
          -- Exclude zero case
          have hIndec_fm : @Etingof.QuiverRepresentation.IsIndecomposable k _ _
              (@Etingof.reversedAtVertex (Fin n) _ Q' i) fm := by
            rcases hIndec_or_zero with h | h_zero
            · exact h
            · exfalso
              obtain ⟨⟨v, hv⟩, _⟩ := hindec'
              suffices hs : ∀ w, Subsingleton (ρ'.obj w) from
                absurd (hs v) (not_subsingleton_iff_nontrivial.mpr hv)
              intro w
              by_cases hw : w = i
              · rw [hw]
                -- sourceMap injective + all target spaces subsingleton → domain subsingleton
                have hsub : ∀ (a : @Etingof.ArrowsOutOf (Fin n) Q' i), Subsingleton (ρ'.obj a.1) :=
                  fun ⟨m, hm⟩ => (Equiv.subsingleton_congr
                    (@Etingof.reflFunctorMinus_equivAt_ne k _ (Fin n) _ Q'
                      i hi_source_Q' ρ' _ m (fun h => (hi_source_Q' m).false (h ▸ hm))).toEquiv).mp
                    (h_zero m)
                haveI h_ds_ss : Subsingleton (DirectSum (@Etingof.ArrowsOutOf (Fin n) Q' i)
                    (fun a => ρ'.obj a.1)) :=
                  ⟨fun x y => DFinsupp.ext (fun a => @Subsingleton.elim _ (hsub a) _ _)⟩
                exact h_inj.subsingleton
              · exact (Equiv.subsingleton_congr
                  (@Etingof.reflFunctorMinus_equivAt_ne k _ (Fin n) _ Q'
                    i hi_source_Q' ρ' _ w hw).toEquiv).mp (h_zero w)
          -- Dim vector
          have hDim_fm : ∀ v, (α v : ℤ) = ↑(fm.finrankAt' k v) := by
            intro v; rw [h668 v]
            show (α v : ℤ) = Etingof.simpleReflectionDimVector
              (fun (a : @Etingof.ArrowsOutOf (Fin n) Q' i) => a.1) i d' v
            have hgoal : (α v : ℤ) = Etingof.simpleReflection n (Etingof.cartanMatrix n adj) i d' v := by
              rw [← hA_def, hd_eq]; exact (congr_fun hinvol_α v).symm
            rw [hgoal]; convert (congr_fun hbridge v).symm using 2
          -- Transport to Q
          exact hinvol ▸
            ⟨fm, hFree_fm, hFinite_fm, hIndec_fm, fun v => by
             change (α v : ℤ) = _; rw [hDim_fm v]; rfl⟩
        · -- Case 3: i is mixed (neither source nor sink)
          -- Use admissible ordering backward construction
          obtain ⟨σ, hσ⟩ := Etingof.admissibleOrdering_exists hDynkin hQ_orient
          obtain ⟨vertices, p, hreduce, hSinks_v⟩ :=
            exists_prefix_to_simpleRoot hDynkin hQ_orient σ hσ α hα_nonneg hα_nonzero hα_root
          exact backward_construct_rep hDynkin k vertices hQ_orient hSS hSinks_v
            α hα_nonneg hα_nonzero hα_root p hreduce
