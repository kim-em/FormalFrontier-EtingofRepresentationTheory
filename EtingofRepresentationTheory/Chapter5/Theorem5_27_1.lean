import Mathlib

/-!
# Theorem 5.27.1: Representations of Semidirect Products

For a semidirect product G ⋉ A (where A is abelian and G acts on A via φ):

(i) The representations V(O, U) are irreducible.
(ii) They are pairwise nonisomorphic (different orbit data gives non-isomorphic reps).
(iii) They form a complete set of irreducible representations of G ⋉ A.
(iv) The character is given by:
  χ_{V(O,U)}(a, g) = (1/|G_χ|) Σ_{h ∈ G : hgh⁻¹ ∈ G_χ} χ(h(a)) χ_U(hgh⁻¹)

Here O is a G-orbit on the character group Â = Hom(A, ℂˣ), χ ∈ O is a
representative, G_χ is the stabilizer of χ under the dual G-action
(g · χ)(a) = χ(φ(g⁻¹)(a)), U is an irreducible representation of G_χ,
and V(O, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ).

## Mathlib correspondence

Uses `SemidirectProduct` for G ⋉ A, `A →* ℂˣ` for the character group Â,
`MulAut` for the G-action on A, and `FDRep.character` for characters.
The orbit method classification is not yet in Mathlib.
-/

noncomputable section

-- Helper: the dual G-action on Â = (A →* ℂˣ) given by (g · χ)(a) = χ(φ(g⁻¹)(a))
private def dualSmulAux {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (g : G) (χ : A →* ℂˣ) : A →* ℂˣ :=
  χ.comp (φ g⁻¹).toMonoidHom

-- Helper: the stabilizer subgroup G_χ = {g ∈ G | g · χ = χ}
private def stabAux {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ) : Subgroup G where
  carrier := {g | dualSmulAux φ g χ = χ}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, dualSmulAux] at ha hb ⊢
    ext x
    have ha' := DFunLike.ext_iff.mp ha
    have hb' := DFunLike.ext_iff.mp hb
    simp only [MonoidHom.comp_apply] at ha' hb'
    simp only [MonoidHom.comp_apply, mul_inv_rev, map_mul, MulAut.mul_apply,
      MulEquiv.coe_toMonoidHom]
    exact congrArg Units.val ((hb' ((φ a⁻¹ : MulAut A) x)).trans (ha' x))
  one_mem' := by
    simp only [Set.mem_setOf_eq, dualSmulAux, inv_one, map_one]
    ext x
    simp [MonoidHom.comp_apply, MulAut.one_apply]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, dualSmulAux] at ha ⊢
    have ha' := DFunLike.ext_iff.mp ha
    simp only [MonoidHom.comp_apply] at ha'
    rw [inv_inv]
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have h := ha' ((φ a : MulAut A) x)
    simp only [MulEquiv.coe_toMonoidHom] at h
    rw [show (φ a⁻¹ : MulAut A) ((φ a : MulAut A) x) = x from by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]] at h
    exact congrArg Units.val h.symm

-- Helper: for s ∈ stabAux, χ(φ(s)(a)) = χ(a) (stabilizer invariance of character)
private lemma stab_char_inv {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ) {s : G} (hs : s ∈ stabAux φ χ) (a : A) :
    χ ((φ s : MulAut A) a) = χ a := by
  have hs' : dualSmulAux φ s χ = χ := hs
  have h := DFunLike.ext_iff.mp hs' ((φ s : MulAut A) a)
  simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [show (φ s⁻¹ : MulAut A) ((φ s : MulAut A) a) = a from by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]] at h
  exact h.symm

-- Helper: the transition element q.out⁻¹ * g * (g⁻¹ • q).out is in the stabilizer
open Classical in
private lemma transition_mem_stab {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ) (g : G) (q : G ⧸ (stabAux φ χ)) :
    q.out⁻¹ * g * (g⁻¹ • q).out ∈ stabAux φ χ := by
  -- g⁻¹ • q.out and (g⁻¹ • q).out are in the same left coset of stabAux φ χ
  -- because both project to g⁻¹ • q in the quotient
  set gi := g⁻¹
  have h1 := MulAction.Quotient.coe_smul_out (H := stabAux φ χ) gi q
  -- h1 : ↑(gi • q.out) = gi • q
  have h2 : (↑(gi • q).out : G ⧸ (stabAux φ χ)) = gi • q := Quotient.out_eq' _
  have hmem := QuotientGroup.leftRel_apply.mp (Quotient.exact' (h1.trans h2.symm))
  -- hmem : (gi • q.out)⁻¹ * (gi • q).out ∈ stabAux φ χ
  simp only [gi, smul_eq_mul, mul_inv_rev, inv_inv] at hmem
  exact hmem

-- The induced representation V(χ, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ)
-- Underlying space: (G ⧸ stabAux φ χ) → U (functions from cosets to U's space)
-- Action of (a, g') on f: permute cosets by g' and twist by χ and U
open Classical in
private noncomputable def inducedRepV {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ)) :
    FDRep ℂ (A ⋊[φ] G) :=
  FDRep.of (V := (G ⧸ (stabAux φ χ)) → ↥U) <|
  { toFun := fun ag =>
    { toFun := fun f q =>
        let tq := q.out
        let q' := ag.right⁻¹ • q
        let s : ↥(stabAux φ χ) := ⟨tq⁻¹ * ag.right * q'.out,
          transition_mem_stab φ χ ag.right q⟩
        ((χ ((φ tq⁻¹ : MulAut A) ag.left) : ℂˣ) : ℂ) •
          (FDRep.ρ U s (f q'))
      map_add' := fun f₁ f₂ => by ext q; simp [smul_add]
      map_smul' := fun c f => by
        ext q; simp only [RingHom.id_apply, Pi.smul_apply]
        rw [LinearMap.map_smul, smul_comm] }
    map_one' := by
      apply LinearMap.ext; intro f; funext q
      -- f : (G ⧸ H) → ↥U, q : G ⧸ H
      -- Goal: action of (1,1) on f at q = f q
      -- Step 1: character factor = 1
      have h1 : ((χ ((φ q.out⁻¹ : MulAut A) (1 : A ⋊[φ] G).left) : ℂˣ) : ℂ) = 1 := by
        simp only [SemidirectProduct.one_left, map_one, Units.val_one]
      -- Step 2: coset unchanged by identity
      have h2 : (1 : A ⋊[φ] G).right⁻¹ • q = q := by
        simp [SemidirectProduct.one_right]
      -- Step 3: transition element is 1
      have h3 : (⟨q.out⁻¹ * (1 : A ⋊[φ] G).right *
          ((1 : A ⋊[φ] G).right⁻¹ • q).out,
          transition_mem_stab φ χ (1 : A ⋊[φ] G).right q⟩ :
          ↥(stabAux φ χ)) = 1 := by
        ext
        simp [SemidirectProduct.one_right, inv_mul_cancel]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, h1, h2, one_smul]
      -- Goal: ρ_U(⟨q.out⁻¹ * 1 * q.out, _⟩)(f q) = f q
      -- The subtype proof doesn't match after simp rewrote h2, so use congr/ext
      have : ∀ (s : ↥(stabAux φ χ)) (hs : (s : G) = 1) (v : ↥U),
          (FDRep.ρ U s) v = v := by
        intro s hs v
        have : s = 1 := Subtype.ext hs
        rw [this, map_one, Module.End.one_apply]
      exact this _ (by simp [SemidirectProduct.one_right, inv_mul_cancel]) _
    map_mul' := fun ag₁ ag₂ => by
      apply LinearMap.ext; intro f; funext q
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
      set q₁ := ag₁.right⁻¹ • q
      have hcoset : (ag₁.right * ag₂.right)⁻¹ • q = ag₂.right⁻¹ • q₁ := by
        rw [mul_inv_rev, mul_smul]
      -- Character factor
      have hchar :
          ((χ ((φ q.out⁻¹ : MulAut A)
            (ag₁.left * (φ ag₁.right : MulAut A) ag₂.left)) : ℂˣ) : ℂ) =
          ((χ ((φ q.out⁻¹ : MulAut A) ag₁.left) : ℂˣ) : ℂ) *
          ((χ ((φ q₁.out⁻¹ : MulAut A) ag₂.left) : ℂˣ) : ℂ) := by
        rw [map_mul (φ q.out⁻¹ : MulAut A), map_mul χ, Units.val_mul]
        congr 1
        rw [← MulAut.mul_apply, ← map_mul φ]
        have : q.out⁻¹ * ag₁.right = (q.out⁻¹ * ag₁.right * q₁.out) * q₁.out⁻¹ := by group
        rw [this, map_mul φ, MulAut.mul_apply]
        exact congrArg _ (stab_char_inv φ χ (transition_mem_stab φ χ ag₁.right q) _)
      -- Stabilizer value telescoping
      have hstab_val : q.out⁻¹ * (ag₁.right * ag₂.right) *
          ((ag₁.right * ag₂.right)⁻¹ • q).out =
        (q.out⁻¹ * ag₁.right * q₁.out) *
        (q₁.out⁻¹ * ag₂.right * (ag₂.right⁻¹ • q₁).out) := by
        simp only [hcoset]; group
      -- For any s with correct value, ρ(s)(v) only depends on s.val
      have hrho_eq : ∀ (s₁ s₂ : ↥(stabAux φ χ)),
          (s₁ : G) = (s₂ : G) → ∀ v, (FDRep.ρ U s₁) v = (FDRep.ρ U s₂) v := by
        intro s₁ s₂ h v; rw [Subtype.ext h]
      -- Assemble: rewrite character, then handle ρ and cosets
      rw [hchar, mul_smul, ← map_smul]
      -- Both sides have the same outer scalar, strip it
      congr 1
      -- LHS: ρ(s)(c • f(q'))  RHS: ρ(s₁)(c • ρ(s₂)(f(q₂)))
      -- Step 1: Replace ρ(s) with ρ(s₁) ∘ ρ(s₂) using hrho_eq
      have step1 := hrho_eq
        ⟨_, transition_mem_stab φ χ (ag₁.right * ag₂.right) q⟩
        (⟨_, transition_mem_stab φ χ ag₁.right q⟩ *
         ⟨_, transition_mem_stab φ χ ag₂.right q₁⟩)
        (by rw [Subgroup.coe_mul]; exact hstab_val)
        (((χ ((φ q₁.out⁻¹ : MulAut A) ag₂.left) : ℂˣ) : ℂ) •
          f ((ag₁.right * ag₂.right)⁻¹ • q))
      rw [step1, map_mul, Module.End.mul_apply, map_smul]
      -- Now: ρ(s₁)(c • ρ(s₂)(f(q'))) = ρ(s₁)(c • ρ(s₂)(f(q₂)))
      -- Reduce to f(q') = f(q₂) which is congr_arg f hcoset
      simp_rw [hcoset]
      rfl }

-- Helper: trace of a "twisted permutation" on a function space.
-- If T acts by (Tf)(x) = L(x)(f(σ(x))), then
-- trace(T) = ∑ x, if σ(x) = x then trace(L(x)) else 0
open Classical in
private lemma trace_twisted_permutation
    {X : Type*} [Fintype X]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Module.Free ℂ V]
    (σ : X → X) (L : X → V →ₗ[ℂ] V)
    (T : (X → V) →ₗ[ℂ] (X → V))
    (hT : ∀ (f : X → V) (x : X), T f x = L x (f (σ x))) :
    LinearMap.trace ℂ (X → V) T =
    ∑ x : X, if σ x = x then LinearMap.trace ℂ V (L x) else 0 := by
  classical
  set b := Module.Free.chooseBasis ℂ V
  haveI : Fintype (Module.Free.ChooseBasisIndex ℂ V) :=
    FiniteDimensional.fintypeBasisIndex b
  set pb := Pi.basis (fun (_ : X) => b)
  rw [LinearMap.trace_eq_matrix_trace ℂ pb]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sigma]
  congr 1; ext x
  split_ifs with hfixed
  · -- Fixed point: sum gives trace(L x)
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    congr 1; ext i
    rw [show pb ⟨x, i⟩ = Pi.single x (b i) from Pi.basis_apply _ _, Pi.basis_repr]
    dsimp only
    congr 1; rw [hT, hfixed, Pi.single_eq_same]
  · -- Not a fixed point: all terms are 0
    apply Finset.sum_eq_zero; intro i _
    have heval : T (pb ⟨x, i⟩) x = 0 := by
      rw [show pb ⟨x, i⟩ = Pi.single x (b i) from Pi.basis_apply _ _]
      rw [hT]; simp only [Pi.single_apply, if_neg hfixed, map_zero]
    rw [Pi.basis_repr]; dsimp only
    rw [heval, map_zero, Finsupp.zero_apply]

-- Helper: the fixed-point condition for the coset action.
-- σ'(q) = g⁻¹ • q = q iff q.out⁻¹ * g * q.out ∈ H (quotient element is in stabilizer)
open Classical in
private lemma coset_fixed_iff {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by
  constructor
  · intro hfixed
    -- g⁻¹ • q = q means [g⁻¹ * q.out] = [q.out] in G/H
    -- i.e., (g⁻¹ * q.out)⁻¹ * q.out ∈ H, i.e., q.out⁻¹ * g * q.out ∈ H
    have h1 : (⟦g⁻¹ * q.out⟧ : G ⧸ H) = ⟦q.out⟧ := by
      have : g⁻¹ • (q : G ⧸ H) = q := hfixed
      rw [← QuotientGroup.out_eq' q] at this
      exact this
    have h2 := QuotientGroup.leftRel_apply.mp (Quotient.exact' h1)
    simpa [mul_inv_rev, inv_inv, mul_assoc] using h2
  · intro hmem
    rw [← QuotientGroup.out_eq' q]
    change (⟦g⁻¹ * q.out⟧ : G ⧸ H) = ⟦q.out⟧
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr (by
      simpa [mul_inv_rev, inv_inv] using hmem))

-- Helper: for a right-H-invariant function f on G, ∑ g, f g = |H| * ∑ q : G/H, f q.out
-- This is a standard result: the sum over G decomposes into fibers over G/H,
-- each fiber having |H| elements, all contributing f(q.out) by right-invariance.
open Classical in
private lemma sum_right_invariant_eq {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G)
    (f : G → ℂ) (hf : ∀ (h : G) (s : H), f (h * s) = f h) :
    ∑ h : G, f h = (Fintype.card H : ℂ) * ∑ q : G ⧸ H, f q.out := by
  -- Every element g ∈ G satisfies f(g) = f(q.out) where q = gH
  have key : ∀ g : G, f g = f (QuotientGroup.mk g : G ⧸ H).out := by
    intro g
    set q := (QuotientGroup.mk g : G ⧸ H)
    have hmem : q.out⁻¹ * g ∈ H := by
      rw [← QuotientGroup.leftRel_apply]
      exact Quotient.exact' (Quotient.out_eq' q)
    calc f g = f (q.out * (⟨q.out⁻¹ * g, hmem⟩ : H)) := by simp
      _ = f q.out := hf q.out ⟨q.out⁻¹ * g, hmem⟩
  -- Rewrite each term, then use fiber decomposition
  conv_lhs => arg 2; ext h; rw [key h]
  -- Now: ∑ h, f((hH).out) = |H| * ∑ q, f(q.out)
  -- The function h ↦ f((hH).out) factors through G/H
  -- Decompose by fibers of the quotient map
  have : ∀ q : G ⧸ H,
      (Finset.univ.filter (fun h : G => (h : G ⧸ H) = q)).card = Fintype.card H := by
    intro q
    -- The fiber over q has |H| elements by QuotientGroup.card_preimage_mk
    rw [show (Finset.univ.filter (fun h : G => (h : G ⧸ H) = q)).card =
        Fintype.card (QuotientGroup.mk (s := H) ⁻¹' {q}) from by
      rw [Fintype.card_ofFinset]
      congr 1; ext h; simp [Finset.mem_filter]]
    rw [show Fintype.card (QuotientGroup.mk (s := H) ⁻¹' {q}) =
        Nat.card (QuotientGroup.mk (s := H) ⁻¹' {q}) from by
      rw [Nat.card_eq_fintype_card]]
    rw [QuotientGroup.card_preimage_mk, Nat.card_eq_fintype_card (α := ↥H)]
    have : Nat.card ({q} : Set (G ⧸ H)) = 1 := by
      rw [Nat.card_eq_fintype_card]; simp
    rw [this, mul_one]
  -- ∑ h : G, f((hH).out) = ∑ q, ∑ h in fiber(q), f((hH).out)
  --                       = ∑ q, ∑ h in fiber(q), f(q.out)
  --                       = ∑ q, |fiber(q)| • f(q.out)
  --                       = ∑ q, |H| • f(q.out)
  --                       = |H| * ∑ q, f(q.out)
  -- Fiber decomposition: ∑_h f((hH).out) = ∑_q ∑_{h:hH=q} f(q.out) = ∑_q |H|*f(q.out)
  have step : ∀ q : G ⧸ H,
      ∑ h ∈ Finset.univ.filter (fun h : G => (h : G ⧸ H) = q), f ((h : G ⧸ H).out) =
      (Fintype.card H : ℂ) * f q.out := by
    intro q
    rw [show ∑ h ∈ Finset.univ.filter (fun h : G => (h : G ⧸ H) = q), f ((h : G ⧸ H).out) =
      ∑ _h ∈ Finset.univ.filter (fun h : G => (h : G ⧸ H) = q), f q.out from
      Finset.sum_congr rfl (fun h hm => congrArg (f ·.out) (Finset.mem_filter.mp hm).2)]
    rw [Finset.sum_const, this q, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun h : G => (h : G ⧸ H)) (fun _ _ => Finset.mem_univ _)]
  simp_rw [step, ← Finset.mul_sum]

-- Helper: evaluation at a coset is a linear map from V to U
open Classical in
private def evalAtCoset {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stabAux φ χ))
    (q : G ⧸ stabAux φ χ) : ((G ⧸ stabAux φ χ) → ↥U) →ₗ[ℂ] ↥U where
  toFun f := f q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- Helper: any equivariant endomorphism of inducedRepV preserves coset components.
-- This is because different cosets have different A-characters, so the A-action
-- distinguishes the coset components. An A-equivariant map must preserve eigenspaces.
-- Specifically: if f is supported on coset q₁ and T commutes with the A-action,
-- then T(f) is also supported on q₁ (Tf evaluated at q₂ ≠ q₁ is 0).
open Classical in
private lemma endo_preserves_cosets {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (T : ((G ⧸ stabAux φ χ) → ↥U) →ₗ[ℂ] (G ⧸ stabAux φ χ) → ↥U)
    (hT_A : ∀ (a : A) (f : (G ⧸ stabAux φ χ) → ↥U),
      T ((inducedRepV φ χ U).ρ ⟨a, 1⟩ f) = (inducedRepV φ χ U).ρ ⟨a, 1⟩ (T f))
    (q₁ q₂ : G ⧸ stabAux φ χ) (hq : q₁ ≠ q₂)
    (f : (G ⧸ stabAux φ χ) → ↥U) (hf : ∀ q, q ≠ q₁ → f q = 0) :
    T f q₂ = 0 := by
  -- Strategy: different cosets have different A-characters. Use A-equivariance
  -- to show T preserves the eigenspace decomposition.
  -- Specialize to A-action: g = 1, so g⁻¹ • q = q and transition element = 1
  have hA_action : ∀ (a : A) (g' : (G ⧸ stabAux φ χ) → ↥U) (q : G ⧸ stabAux φ χ),
      (inducedRepV φ χ U).ρ ⟨a, 1⟩ g' q =
      ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) • g' q := by
    intro a g' q
    -- The action of (a, 1) on g' at coset q: by definition,
    -- (a,1)·g' at q = χ(φ(q⁻¹)(a)) • ρ_U(s)(g'(1⁻¹ • q))
    -- where s = q.out⁻¹ * 1 * (1⁻¹ • q).out.
    -- Since 1⁻¹ = 1, 1 • q = q, s = q.out⁻¹ * q.out = 1, ρ_U(1) = id.
    -- The underlying computation matches the `map_one'` proof in `inducedRepV`.
    change ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) •
      (FDRep.ρ U ⟨q.out⁻¹ * (1 : G) * ((1 : G)⁻¹ • q).out,
        transition_mem_stab φ χ (1 : G) q⟩) (g' ((1 : G)⁻¹ • q)) = _
    have hrho : ∀ (s : ↥(stabAux φ χ)) (hs : (s : G) = 1) (v : ↥U),
        (FDRep.ρ U s) v = v := by
      intro s hs v; rw [show s = 1 from Subtype.ext hs, map_one, Module.End.one_apply]
    simp only [inv_one, one_smul, mul_one]
    congr 1
    exact hrho _ (inv_mul_cancel q.out) _
  -- Step 2: Different cosets have different A-characters.
  -- dualSmulAux φ q.out χ gives the character at coset q (since it equals a ↦ χ(φ(q.out⁻¹)(a)))
  -- Equal characters imply same coset via the stabilizer condition.
  have hchar_inj : dualSmulAux φ q₁.out χ = dualSmulAux φ q₂.out χ → q₁ = q₂ := by
    intro heq
    -- heq: ∀ a, χ(φ(q₁.out⁻¹)(a)) = χ(φ(q₂.out⁻¹)(a))
    -- Composing with φ(q₁.out) on the right: χ = χ ∘ φ(q₁.out⁻¹ * q₂.out)
    -- Hence q₁.out⁻¹ * q₂.out ∈ stabAux φ χ
    have hmem : q₁.out⁻¹ * q₂.out ∈ stabAux φ χ := by
      change dualSmulAux φ (q₁.out⁻¹ * q₂.out) χ = χ
      ext a
      simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      have := DFunLike.ext_iff.mp heq ((φ q₁.out : MulAut A) a)
      simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
      rw [show (φ q₁.out⁻¹ : MulAut A) ((φ q₁.out : MulAut A) a) = a from by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply],
        show (φ q₂.out⁻¹ : MulAut A) ((φ q₁.out : MulAut A) a) =
          (φ (q₁.out⁻¹ * q₂.out)⁻¹ : MulAut A) a from by
        rw [mul_inv_rev, inv_inv, map_mul, MulAut.mul_apply]] at this
      exact_mod_cast this.symm
    rw [← Quotient.out_eq' q₁, ← Quotient.out_eq' q₂]
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr hmem)
  -- Note: dualSmulAux φ q.out χ a = χ(φ(q.out⁻¹)(a)) (the A-character at coset q)
  -- Different cosets give different characters
  have hchar_ne : dualSmulAux φ q₁.out χ ≠ dualSmulAux φ q₂.out χ :=
    fun h => hq (hchar_inj h)
  -- Get a witness a ∈ A where the characters differ
  rw [Ne, DFunLike.ext_iff, not_forall] at hchar_ne
  obtain ⟨a, ha⟩ := hchar_ne
  -- ha: χ(φ(q₁.out⁻¹)(a)) ≠ χ(φ(q₂.out⁻¹)(a))
  simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at ha
  -- Step 3: From T(ρ(a,1)(f)) = ρ(a,1)(T(f)), derive (c₁ - c₂) • Tf(q₂) = 0
  -- For f supported on q₁: ρ(a,1)(f) = c(q₁) • f
  have haction_f : (inducedRepV φ χ U).ρ ⟨a, 1⟩ f =
      ((χ ((φ q₁.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) • f := by
    funext q
    rw [hA_action a f q, Pi.smul_apply]
    by_cases hq' : q = q₁
    · subst hq'; rfl
    · rw [hf q hq', smul_zero, smul_zero]
  -- From hT_A: T(ρ(a,1)(f)) = ρ(a,1)(T(f))
  -- LHS: T(c₁ • f) = c₁ • T(f) by linearity
  -- RHS at q₂: ρ(a,1)(T f)(q₂) = c₂ • T(f)(q₂) by hA_action
  have hcomm_q₂ := congr_fun (hT_A a f) q₂
  -- Rewrite LHS: T(ρ(a,1)(f)) = T(c₁ • f) = c₁ • T(f)
  rw [haction_f, map_smul] at hcomm_q₂
  -- hcomm_q₂: (c₁ • T f) q₂ = ρ(a,1)(T f) q₂
  rw [Pi.smul_apply, hA_action a (T f) q₂] at hcomm_q₂
  -- hcomm_q₂: c₁ • Tf(q₂) = c₂ • Tf(q₂)
  have hsub : (((χ ((φ q₁.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) -
      ((χ ((φ q₂.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ)) • T f q₂ = 0 := by
    rw [sub_smul, sub_eq_zero]; exact hcomm_q₂
  rw [smul_eq_zero] at hsub
  rcases hsub with h | h
  · exfalso; apply ha
    have := sub_eq_zero.mp h
    exact_mod_cast this
  · exact h

-- Helper: different cosets have different A-characters (standalone extraction from
-- endo_preserves_cosets). If q₁.out⁻¹ and q₂.out⁻¹ give the same twisted character, q₁ = q₂.
open Classical in
private lemma coset_char_injective {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (q₁ q₂ : G ⧸ stabAux φ χ) (heq : dualSmulAux φ q₁.out χ = dualSmulAux φ q₂.out χ) :
    q₁ = q₂ := by
  have hmem : q₁.out⁻¹ * q₂.out ∈ stabAux φ χ := by
    change dualSmulAux φ (q₁.out⁻¹ * q₂.out) χ = χ
    ext a
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have := DFunLike.ext_iff.mp heq ((φ q₁.out : MulAut A) a)
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    rw [show (φ q₁.out⁻¹ : MulAut A) ((φ q₁.out : MulAut A) a) = a from by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply],
      show (φ q₂.out⁻¹ : MulAut A) ((φ q₁.out : MulAut A) a) =
        (φ (q₁.out⁻¹ * q₂.out)⁻¹ : MulAut A) a from by
      rw [mul_inv_rev, inv_inv, map_mul, MulAut.mul_apply]] at this
    exact_mod_cast this.symm
  rw [← Quotient.out_eq' q₁, ← Quotient.out_eq' q₂]
  exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr hmem)

-- Helper: for q₁ ≠ q₂, there exists a ∈ A witnessing different character values.
open Classical in
private lemma coset_char_witness {G A : Type} [Group G] [CommGroup A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (q₁ q₂ : G ⧸ stabAux φ χ) (hne : q₁ ≠ q₂) :
    ∃ a : A, (χ ((φ q₁.out⁻¹ : MulAut A) a) : ℂˣ) ≠ χ ((φ q₂.out⁻¹ : MulAut A) a) := by
  by_contra h
  push_neg at h
  apply hne
  exact coset_char_injective φ χ q₁ q₂ (DFunLike.ext _ _ (fun a => by
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact_mod_cast h a))

-- A full faithful functor preserving monomorphisms reflects Simple objects.
open CategoryTheory in
private lemma simple_of_full_faithful_preservesMono''
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

-- Bridge: Simple in FDRep implies IsIrreducible of the underlying representation.
-- Proof: construct the inclusion morphism for each subrepresentation in FDRep, then
-- apply the Simple condition to show it's trivial or everything.
open CategoryTheory in
private lemma simple_fdRep_isIrreducible {k : Type} [Field k] {G : Type} [Group G]
    (U : FDRep k G) [hU : Simple U] : Representation.IsIrreducible (FDRep.ρ U) := by
  -- IsIrreducible = IsSimpleOrder (Subrepresentation (FDRep.ρ U))
  -- First, establish that U is nontrivial (nonzero vector space)
  have hnt : Nontrivial U := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    -- 𝟙 U = 0 because all morphisms out of a subsingleton object are equal
    apply id_nonzero U
    haveI : Subsingleton (↑U.V.obj) := h
    ext x
    exact Subsingleton.elim _ _
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · -- ⊥ ≠ ⊤ as subrepresentations
    intro h
    obtain ⟨x, y, hxy⟩ := hnt
    have h' := congr_arg Subrepresentation.toSubmodule h
    -- h' : ⊥.toSubmodule = ⊤.toSubmodule
    have hx : x - y ∈ (⊤ : Submodule k U) := Submodule.mem_top
    rw [show (⊤ : Submodule k U) = (⊤ : Subrepresentation (FDRep.ρ U)).toSubmodule from rfl,
        ← h'] at hx
    exact hxy (eq_of_sub_eq_zero ((Submodule.mem_bot k).mp hx))
  · -- eq_bot_or_eq_top: every subrepresentation is ⊥ or ⊤
    -- Construct inclusion FDRep.of S.toRepresentation ↪ U
    let W := FDRep.of S.toRepresentation
    let ι : W ⟶ U :=
      ⟨FGModuleCat.ofHom S.toSubmodule.subtype, fun g => by ext ⟨x, hx⟩; rfl⟩
    -- ι is a mono
    haveI : Mono ι := by
      refine ⟨fun {Z} f g h => ?_⟩
      have key : ∀ (x : Z), (f.hom.hom.hom x : U) = (g.hom.hom.hom x : U) := by
        intro x
        have := congr_arg (fun φ => (ConcreteCategory.hom φ) x) h
        exact this
      ext x
      exact key x
    -- By Simple: ι = 0 or IsIso ι
    by_cases h : ι = 0
    · -- ι = 0 ⟹ S = ⊥
      left; apply Subrepresentation.toSubmodule_injective; ext x; constructor
      · intro hx
        have : (S.toSubmodule.subtype ⟨x, hx⟩ : U) = 0 := by
          have := congr_arg (fun φ => (ConcreteCategory.hom φ) ⟨x, hx⟩) h
          exact this
        simp [Submodule.subtype] at this
        exact this ▸ Submodule.zero_mem _
      · exact fun hx => SetLike.le_def.mp bot_le hx
    · -- ι ≠ 0 ⟹ S = ⊤
      right; haveI : IsIso ι := (Simple.mono_isIso_iff_nonzero ι).mpr h
      apply Subrepresentation.toSubmodule_injective; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _
        have hsurj := (ConcreteCategory.bijective_of_isIso ι).2
        obtain ⟨⟨y, hy⟩, hyx⟩ := hsurj x
        have : (y : U) = x := hyx
        rw [← this]; exact hy

-- Bridge: IsSimpleModule over the monoid algebra implies Simple in FDRep.
open CategoryTheory in
private noncomputable def simple_of_isSimpleModule_asModule'
    {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (ρ : Representation k G V) [IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  haveI : Simple (ModuleCat.of (MonoidAlgebra k G) ρ.asModule) :=
    simple_of_isSimpleModule
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  haveI : Simple
      (E.functor.obj ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra k G) ρ.asModule)
    infer_instance
  haveI : Simple ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono'' E.functor _
  exact simple_of_full_faithful_preservesMono'' (forget₂ (FDRep k G) (Rep k G)) _

-- The underlying representation of inducedRepV, explicitly typed on (G/H → U).
-- This avoids going through FDRep carrier coercions.
open Classical in
private noncomputable def inducedRep_raw {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ)) :
    (A ⋊[φ] G) →* ((G ⧸ stabAux φ χ) → ↥U) →ₗ[ℂ] ((G ⧸ stabAux φ χ) → ↥U) :=
  { toFun := fun ag =>
    { toFun := fun f q =>
        let tq := q.out
        let q' := ag.right⁻¹ • q
        let s : ↥(stabAux φ χ) := ⟨tq⁻¹ * ag.right * q'.out,
          transition_mem_stab φ χ ag.right q⟩
        ((χ ((φ tq⁻¹ : MulAut A) ag.left) : ℂˣ) : ℂ) •
          (FDRep.ρ U s (f q'))
      map_add' := fun f₁ f₂ => by ext q; simp [smul_add]
      map_smul' := fun c f => by
        ext q; simp only [RingHom.id_apply, Pi.smul_apply]
        rw [LinearMap.map_smul, smul_comm] }
    map_one' := by
      apply LinearMap.ext; intro f; funext q
      have h1 : ((χ ((φ q.out⁻¹ : MulAut A) (1 : A ⋊[φ] G).left) : ℂˣ) : ℂ) = 1 := by
        simp only [SemidirectProduct.one_left, map_one, Units.val_one]
      have h3 : (⟨q.out⁻¹ * (1 : A ⋊[φ] G).right *
          ((1 : A ⋊[φ] G).right⁻¹ • q).out,
          transition_mem_stab φ χ (1 : A ⋊[φ] G).right q⟩ :
          ↥(stabAux φ χ)) = 1 := by
        ext; simp [SemidirectProduct.one_right, inv_mul_cancel]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, h1, one_smul,
        SemidirectProduct.one_right, inv_one, one_smul]
      have : ∀ (s : ↥(stabAux φ χ)) (hs : (s : G) = 1) (v : ↥U),
          (FDRep.ρ U s) v = v := by
        intro s hs v
        have : s = 1 := Subtype.ext hs
        rw [this, map_one, Module.End.one_apply]
      exact this _ (by simp [SemidirectProduct.one_right, inv_mul_cancel]) _
    map_mul' := fun ag₁ ag₂ => by
      apply LinearMap.ext; intro f; funext q
      -- This is the same as the map_mul' proof in inducedRepV
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
      set q₁ := ag₁.right⁻¹ • q
      have hcoset : (ag₁.right * ag₂.right)⁻¹ • q = ag₂.right⁻¹ • q₁ := by
        rw [mul_inv_rev, mul_smul]
      have hchar :
          ((χ ((φ q.out⁻¹ : MulAut A)
            (ag₁.left * (φ ag₁.right : MulAut A) ag₂.left)) : ℂˣ) : ℂ) =
          ((χ ((φ q.out⁻¹ : MulAut A) ag₁.left) : ℂˣ) : ℂ) *
          ((χ ((φ q₁.out⁻¹ : MulAut A) ag₂.left) : ℂˣ) : ℂ) := by
        rw [map_mul (φ q.out⁻¹ : MulAut A), map_mul χ, Units.val_mul]
        congr 1
        rw [← MulAut.mul_apply, ← map_mul φ]
        have : q.out⁻¹ * ag₁.right = (q.out⁻¹ * ag₁.right * q₁.out) * q₁.out⁻¹ := by group
        rw [this, map_mul φ, MulAut.mul_apply]
        exact congrArg _ (stab_char_inv φ χ (transition_mem_stab φ χ ag₁.right q) _)
      have hstab_val : q.out⁻¹ * (ag₁.right * ag₂.right) *
          ((ag₁.right * ag₂.right)⁻¹ • q).out =
        (q.out⁻¹ * ag₁.right * q₁.out) *
        (q₁.out⁻¹ * ag₂.right * (ag₂.right⁻¹ • q₁).out) := by
        simp only [hcoset]; group
      have hrho_eq : ∀ (s₁ s₂ : ↥(stabAux φ χ)),
          (s₁ : G) = (s₂ : G) → ∀ v, (FDRep.ρ U s₁) v = (FDRep.ρ U s₂) v := by
        intro s₁ s₂ h v; rw [Subtype.ext h]
      rw [hchar, mul_smul, ← map_smul]
      congr 1
      have step1 := hrho_eq
        ⟨_, transition_mem_stab φ χ (ag₁.right * ag₂.right) q⟩
        (⟨_, transition_mem_stab φ χ ag₁.right q⟩ *
         ⟨_, transition_mem_stab φ χ ag₂.right q₁⟩)
        (by rw [Subgroup.coe_mul]; exact hstab_val)
        (((χ ((φ q₁.out⁻¹ : MulAut A) ag₂.left) : ℂˣ) : ℂ) •
          f ((ag₁.right * ag₂.right)⁻¹ • q))
      rw [step1, map_mul, Module.End.mul_apply, map_smul]
      simp_rw [hcoset]
      rfl }

-- Helper: A-action formula at a coset. For (a,1) ∈ A ⋊ G acting on f at coset q:
-- (a,1)·f(q) = χ(φ(q⁻¹)(a)) • f(q)
open Classical in
private lemma A_action_at_coset {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (a : A) (f : (G ⧸ stabAux φ χ) → ↥U) (q : G ⧸ stabAux φ χ) :
    inducedRep_raw φ χ U ⟨a, 1⟩ f q =
      ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) • f q := by
  show ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) •
    (FDRep.ρ U ⟨q.out⁻¹ * (1 : G) * ((1 : G)⁻¹ • q).out,
      transition_mem_stab φ χ (1 : G) q⟩) (f ((1 : G)⁻¹ • q)) = _
  have hrho : ∀ (s : ↥(stabAux φ χ)) (hs : (s : G) = 1) (v : ↥U),
      (FDRep.ρ U s) v = v := by
    intro s hs v; rw [show s = 1 from Subtype.ext hs, map_one, Module.End.one_apply]
  simp only [inv_one, one_smul, mul_one]
  congr 1
  exact hrho _ (inv_mul_cancel q.out) _

-- Helper: G-action formula at a coset. For (1,s) ∈ A ⋊ G acting on f at coset q:
-- (1,s)·f(q) = ρ_U(transition)(f(s⁻¹•q))
-- (the character factor χ(φ(q⁻¹)(1)) is 1 since φ(g) maps 1↦1 and χ(1)=1)
open Classical in
private lemma G_action_at_coset {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (s : G) (f : (G ⧸ stabAux φ χ) → ↥U) (q : G ⧸ stabAux φ χ) :
    inducedRep_raw φ χ U ⟨1, s⟩ f q =
      FDRep.ρ U ⟨q.out⁻¹ * s * (s⁻¹ • q).out,
        transition_mem_stab φ χ s q⟩ (f (s⁻¹ • q)) := by
  change ((χ ((φ q.out⁻¹ : MulAut A) 1) : ℂˣ) : ℂ) •
    (FDRep.ρ U ⟨q.out⁻¹ * s * (s⁻¹ • q).out,
      transition_mem_stab φ χ s q⟩) (f (s⁻¹ • q)) = _
  simp [map_one, Units.val_one, one_smul]

-- Helper: if σ is an invariant submodule containing f with f(q₀) ≠ 0,
-- then σ contains an element supported only on q₀.
-- Uses the "A-eigenspace extraction" trick: iteratively kill other coset components.
open Classical in
private lemma extract_single_support {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (σ : Submodule ℂ ((G ⧸ stabAux φ χ) → ↥U))
    (hσ_inv : ∀ ag f, f ∈ σ → inducedRep_raw φ χ U ag f ∈ σ)
    (f : (G ⧸ stabAux φ χ) → ↥U) (hf : f ∈ σ)
    (q₀ : G ⧸ stabAux φ χ) (hq₀ : f q₀ ≠ 0) :
    ∃ g ∈ σ, g q₀ ≠ 0 ∧ ∀ q, q ≠ q₀ → g q = 0 := by
  -- Induction on the number of nonzero cosets other than q₀
  suffices ∀ (n : ℕ) (f : (G ⧸ stabAux φ χ) → ↥U), f ∈ σ →
      f q₀ ≠ 0 →
      (Finset.univ.filter (fun q => q ≠ q₀ ∧ f q ≠ 0)).card ≤ n →
      ∃ g ∈ σ, g q₀ ≠ 0 ∧ ∀ q, q ≠ q₀ → g q = 0 by
    exact this _ f hf hq₀ le_rfl
  intro n
  induction n with
  | zero =>
    intro f hf hfq₀ hcard
    refine ⟨f, hf, hfq₀, fun q hq => ?_⟩
    by_contra hne
    have : q ∈ Finset.univ.filter (fun q => q ≠ q₀ ∧ f q ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hne⟩
    exact Nat.not_lt.mpr hcard (Finset.card_pos.mpr ⟨q, this⟩)
  | succ n ih =>
    intro f hf hfq₀ hcard
    by_cases h_done : ∀ q, q ≠ q₀ → f q = 0
    · exact ⟨f, hf, hfq₀, h_done⟩
    · push_neg at h_done
      obtain ⟨q₁, hq₁_ne, hq₁_nz⟩ := h_done
      -- Get a witness a ∈ A where characters at q₀ and q₁ differ
      obtain ⟨a, ha⟩ := coset_char_witness φ χ q₀ q₁ hq₁_ne.symm
      -- Define f' = ρ(a,1)(f) - χ_{q₁}(a) • f ∈ σ
      -- This kills the q₁-component while preserving q₀
      set c₁ := ((χ ((φ q₁.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) with hc₁_def
      set f' := inducedRep_raw φ χ U ⟨a, 1⟩ f - c₁ • f with hf'_def
      have hf'_mem : f' ∈ σ := by
        apply σ.sub_mem
        · exact hσ_inv ⟨a, 1⟩ f hf
        · exact σ.smul_mem c₁ hf
      -- f' at any coset q: f'(q) = (χ_q(a) - c₁) • f(q)
      have hf'_eval : ∀ q, f' q =
          (((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) - c₁) • f q := by
        intro q
        show inducedRep_raw φ χ U ⟨a, 1⟩ f q - c₁ • f q = _
        rw [A_action_at_coset, sub_smul]
      -- f'(q₁) = 0 (since χ_{q₁}(a) - c₁ = 0)
      have hf'_q₁ : f' q₁ = 0 := by
        rw [hf'_eval]; simp [hc₁_def]
      -- f'(q₀) ≠ 0 (since χ_{q₀}(a) ≠ c₁ = χ_{q₁}(a))
      have hf'_q₀ : f' q₀ ≠ 0 := by
        rw [hf'_eval]
        refine smul_ne_zero (sub_ne_zero.mpr ?_) hfq₀
        simp only [hc₁_def]
        exact_mod_cast ha
      -- f' q = 0 whenever f q = 0
      have hf'_zero : ∀ q, f q = 0 → f' q = 0 := by
        intro q hfq; rw [hf'_eval, hfq, smul_zero]
      -- Support of f' is strictly smaller: it's a subset of supp(f)\{q₁}
      have hcard' : (Finset.univ.filter (fun q => q ≠ q₀ ∧ f' q ≠ 0)).card ≤ n := by
        have hsub : Finset.univ.filter (fun q => q ≠ q₀ ∧ f' q ≠ 0) ⊆
            (Finset.univ.filter (fun q => q ≠ q₀ ∧ f q ≠ 0)).erase q₁ := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [Finset.mem_erase]
          refine ⟨fun heq => hq.2 (heq ▸ hf'_q₁), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hq.1, fun hfq => hq.2 (hf'_zero q hfq)⟩
        calc _ ≤ _ := Finset.card_le_card hsub
          _ ≤ ((Finset.univ.filter (fun q => q ≠ q₀ ∧ f q ≠ 0)).card - 1) := by
              rw [Finset.card_erase_of_mem
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₁_ne, hq₁_nz⟩)]
          _ ≤ n := by omega
      exact ih f' hf'_mem hf'_q₀ hcard'

-- Helper: if σ is an invariant submodule containing a function supported on q₁
-- with nonzero value, and U is simple, then σ contains Pi.single q₁ u for all u.
-- Proof outline: the image of σ's single-support-on-q₁ elements under eval-at-q₁
-- forms a Subrepresentation of U (invariant via conjugation by q₁.out ∈ stabAux).
-- It's nonzero (contains g₁ q₁). By simplicity of U, the image is all of U.
-- For any u, there exists f ∈ σ supported on q₁ with f(q₁) = u.
-- Such f agrees with Pi.single q₁ u by funext.
open Classical in
private lemma sigma_contains_all_single {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ)) (hU : CategoryTheory.Simple U)
    (σ : Submodule ℂ ((G ⧸ stabAux φ χ) → ↥U))
    (hσ_inv : ∀ ag f, f ∈ σ → inducedRep_raw φ χ U ag f ∈ σ)
    (q₁ : G ⧸ stabAux φ χ) (hq₁_out_mem : q₁.out ∈ stabAux φ χ)
    (g₁ : (G ⧸ stabAux φ χ) → ↥U) (hg₁_mem : g₁ ∈ σ)
    (hg₁_nz : g₁ q₁ ≠ 0) (hg₁_supp : ∀ q, q ≠ q₁ → g₁ q = 0)
    (u : ↥U) : ∃ f ∈ σ, f q₁ = u ∧ ∀ q, q ≠ q₁ → f q = 0 := by
  -- Bridge: Simple U → IsIrreducible (FDRep.ρ U)
  -- Proof sketch: construct FDRep.of S.toRepresentation with subtype inclusion as
  -- a mono in FDRep. By Simple, it's zero or iso, giving S = ⊥ or S = ⊤.
  have hU_irred : Representation.IsIrreducible (FDRep.ρ U) :=
    simple_fdRep_isIrreducible U
  -- Build S = {v : ↥U | ∃ f ∈ σ, f q₁ = v ∧ ∀ q ≠ q₁, f q = 0}
  -- as a Subrepresentation of FDRep.ρ U.
  set S : Subrepresentation (FDRep.ρ U) :=
    { toSubmodule :=
        { carrier := {v : ↥U | ∃ f ∈ σ, f q₁ = v ∧ ∀ q, q ≠ q₁ → f q = 0}
          add_mem' := by
            rintro a b ⟨fa, hfa_mem, hfa_eq, hfa_supp⟩ ⟨fb, hfb_mem, hfb_eq, hfb_supp⟩
            exact ⟨fa + fb, σ.add_mem hfa_mem hfb_mem,
              by simp [hfa_eq, hfb_eq],
              fun q hq => by simp [hfa_supp q hq, hfb_supp q hq]⟩
          zero_mem' := ⟨0, σ.zero_mem, by simp, fun q _ => by simp⟩
          smul_mem' := by
            rintro c v ⟨f, hf_mem, hf_eq, hf_supp⟩
            exact ⟨c • f, σ.smul_mem c hf_mem,
              by simp [hf_eq],
              fun q hq => by simp [hf_supp q hq]⟩ }
      apply_mem_toSubmodule := by
        intro s v ⟨f, hf_mem, hf_eq, hf_supp⟩
        -- Need: ∃ f' ∈ σ, f' q₁ = ρ_U(s)(v) ∧ ∀ q ≠ q₁, f' q = 0
        -- Take f' = ρ(1, g')(f) where g' = q₁.out * ↑s * q₁.out⁻¹
        set g' : G := q₁.out * ↑s * q₁.out⁻¹
        have hg'_stab : g' ∈ stabAux φ χ :=
          (stabAux φ χ).mul_mem ((stabAux φ χ).mul_mem hq₁_out_mem s.2)
            ((stabAux φ χ).inv_mem hq₁_out_mem)
        -- g'⁻¹ preserves q₁ in the quotient (g'⁻¹ ∈ stabAux preserves all cosets)
        have hg'_inv_fix : g'⁻¹ • q₁ = q₁ := by
          have hmem_inv : g'⁻¹ ∈ stabAux φ χ := (stabAux φ χ).inv_mem hg'_stab
          -- q₁ = [q₁.out], g'⁻¹ • [q₁.out] = [g'⁻¹ * q₁.out]
          -- [g'⁻¹ * q₁.out] = [q₁.out] iff q₁.out⁻¹ * g'⁻¹ * q₁.out ∈ stabAux
          -- which holds since q₁.out ∈ stabAux and g'⁻¹ ∈ stabAux
          rw [← QuotientGroup.out_eq' q₁]
          apply Quotient.sound'; rw [QuotientGroup.leftRel_apply]
          simp only [smul_eq_mul, mul_inv_rev, inv_inv]
          exact (stabAux φ χ).mul_mem
            ((stabAux φ χ).mul_mem ((stabAux φ χ).inv_mem hq₁_out_mem) hg'_stab)
            hq₁_out_mem
        -- g' preserves q₁
        have hg'_fix : g' • q₁ = q₁ := by
          rw [← QuotientGroup.out_eq' q₁]
          apply Quotient.sound'; rw [QuotientGroup.leftRel_apply]
          simp only [smul_eq_mul, mul_inv_rev]
          exact (stabAux φ χ).mul_mem
            ((stabAux φ χ).mul_mem ((stabAux φ χ).inv_mem hq₁_out_mem) ((stabAux φ χ).inv_mem hg'_stab))
            hq₁_out_mem
        -- For q ≠ q₁: g'⁻¹ • q ≠ q₁
        have hg'_ne : ∀ q, q ≠ q₁ → g'⁻¹ • q ≠ q₁ := by
          intro q hq h; apply hq
          calc q = g' • (g'⁻¹ • q) := by rw [smul_inv_smul]
            _ = g' • q₁ := by rw [h]
            _ = q₁ := hg'_fix
        set f' := inducedRep_raw φ χ U ⟨1, g'⟩ f
        refine ⟨f', hσ_inv ⟨1, g'⟩ f hf_mem, ?_, ?_⟩
        · -- f'(q₁) = ρ_U(transition)(f(g'⁻¹ • q₁)) = ρ_U(s)(f(q₁)) = ρ_U(s)(v)
          change (inducedRep_raw φ χ U ⟨1, g'⟩ f) q₁ = (FDRep.ρ U s) v
          rw [G_action_at_coset]
          -- Use simp to handle the dependent rewrite of g'⁻¹ • q₁ = q₁
          simp only [show (g'⁻¹ : G) • (q₁ : G ⧸ stabAux φ χ) = q₁ from hg'_inv_fix]
          -- Now: ρ_U(⟨q₁.out⁻¹ * g' * q₁.out, _⟩)(f(q₁)) = ρ_U(s)(v)
          simp only [show f q₁ = v from hf_eq]
          -- Need: ρ_U(⟨q₁.out⁻¹ * g' * q₁.out, _⟩) = ρ_U(s)
          -- Since q₁.out⁻¹ * g' * q₁.out = q₁.out⁻¹ * (q₁.out * ↑s * q₁.out⁻¹) * q₁.out = ↑s
          have hrho_eq : ∀ (s₁ s₂ : ↥(stabAux φ χ)),
              (s₁ : G) = (s₂ : G) → ∀ w, (FDRep.ρ U s₁) w = (FDRep.ρ U s₂) w := by
            intro s₁ s₂ h w; rw [Subtype.ext h]
          exact hrho_eq _ s (by
            show q₁.out⁻¹ * g' * q₁.out = ↑s
            simp [g', mul_assoc, inv_mul_cancel, mul_inv_cancel]) v
        · -- At q ≠ q₁: f'(q) = ρ_U(trans)(f(g'⁻¹ • q)) = ρ_U(trans)(0) = 0
          intro q hq
          change (inducedRep_raw φ χ U ⟨1, g'⟩ f) q = 0
          rw [G_action_at_coset, hf_supp _ (hg'_ne q hq), map_zero] }
  -- S ≠ ⊥ (contains g₁ q₁)
  have hS_ne_bot : S ≠ ⊥ := by
    intro h; apply hg₁_nz
    have hmem : g₁ q₁ ∈ S := ⟨g₁, hg₁_mem, rfl, hg₁_supp⟩
    have : (⊥ : Subrepresentation (FDRep.ρ U)) = S := h.symm
    rw [← this] at hmem; exact hmem
  -- By simplicity: S = ⊤
  have hS_top : S = ⊤ := hU_irred.eq_bot_or_eq_top S |>.resolve_left hS_ne_bot
  -- For any u, u ∈ S
  have hu_mem : u ∈ S := by rw [hS_top]; trivial
  exact hu_mem

open Classical in
private lemma inducedRepV_simple {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (hU : CategoryTheory.Simple U) :
    CategoryTheory.Simple (inducedRepV φ χ U) := by
  -- Bridge: inducedRepV φ χ U = FDRep.of (inducedRep_raw φ χ U) (same action)
  suffices h : CategoryTheory.Simple (FDRep.of (inducedRep_raw φ χ U)) by
    have heq : inducedRepV φ χ U = FDRep.of (inducedRep_raw φ χ U) := by
      simp only [inducedRepV, inducedRep_raw]
    rw [heq]; exact h
  -- Use the IsSimpleModule → Simple bridge
  set ρ := inducedRep_raw φ χ U
  haveI : IsSimpleModule (MonoidAlgebra ℂ (A ⋊[φ] G)) (Representation.asModule ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp <| by
    -- IsIrreducible = IsSimpleOrder (Subrepresentation ρ)
    haveI : Nontrivial (Subrepresentation ρ) := by
      rw [nontrivial_iff]
      refine ⟨⊥, ⊤, fun h => ?_⟩
      -- ⊥ = ⊤ means V = {0}. Get contradiction from Simple U.
      -- Simple U implies 𝟙 U ≠ 0, hence ↥U is nontrivial
      have hid := CategoryTheory.id_nonzero U
      apply hid
      -- Show 𝟙 U = 0 when carrier is subsingleton
      have h_sub : (⊥ : Submodule ℂ ((G ⧸ stabAux φ χ) → ↥U)) =
          (⊤ : Submodule ℂ ((G ⧸ stabAux φ χ) → ↥U)) := by
        exact congrArg Subrepresentation.toSubmodule h
      -- All elements of V are 0
      have h_zero : ∀ v : (G ⧸ stabAux φ χ) → ↥U, v = 0 := by
        intro v
        have hv : v ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
        rw [← h_sub] at hv
        exact (Submodule.mem_bot (R := ℂ)).mp hv
      -- In particular, ∀ u : ↥U, u = 0 (evaluate at any coset)
      haveI : Subsingleton ↥U := by
        constructor; intro a b
        have : Pi.single (⟦(1 : G)⟧ : G ⧸ stabAux φ χ) a = 0 := h_zero _
        have ha : a = 0 := by simpa [Pi.single, Function.update] using congr_fun this ⟦1⟧
        have : Pi.single (⟦(1 : G)⟧ : G ⧸ stabAux φ χ) b = 0 := h_zero _
        have hb : b = 0 := by simpa [Pi.single, Function.update] using congr_fun this ⟦1⟧
        rw [ha, hb]
      -- With ↥U subsingleton, 𝟙 U = 0
      haveI : Subsingleton ↑U.V.obj := ‹Subsingleton ↥U›
      ext; exact Subsingleton.elim _ _
    exact {
      eq_bot_or_eq_top := fun σ => by
        by_cases hσ : σ = ⊥
        · exact Or.inl hσ
        · right
          -- σ is nonzero, get f ∈ σ with f ≠ 0
          have hσ_ne : ∃ f ∈ σ.toSubmodule, f ≠ 0 := by
            by_contra h; push_neg at h
            apply hσ
            exact le_antisymm (fun x hx => (Submodule.mem_bot (R := ℂ)).mpr (h x hx)) bot_le
          obtain ⟨f, hf_mem, hf_ne⟩ := hσ_ne
          have ⟨q₀, hq₀⟩ : ∃ q₀, f q₀ ≠ 0 := by
            by_contra h; push_neg at h; exact hf_ne (funext h)
          -- Extract single-coset support using A-eigenspace trick
          have hσ_inv : ∀ ag f, f ∈ σ.toSubmodule → ρ ag f ∈ σ.toSubmodule :=
            fun ag f hf => σ.apply_mem_toSubmodule ag hf
          obtain ⟨g, hg_mem, hg_nz, hg_supp⟩ :=
            extract_single_support φ χ U σ.toSubmodule hσ_inv f hf_mem q₀ hq₀
          -- g is in σ, supported only on q₀ with g(q₀) ≠ 0
          -- Step 1: Move g to the identity coset [1] via G-action
          set q₁ := (⟦(1 : G)⟧ : G ⧸ stabAux φ χ) with hq₁_def
          -- Act by (1, q₀.out⁻¹) to move support from q₀ to q₀.out⁻¹ • q₀ = [1]
          -- (ρ(1,s)(f) supported on s • q₀ when f supported on q₀)
          set g₁ := ρ ⟨1, q₀.out⁻¹⟩ g with hg₁_def
          have hg₁_mem : g₁ ∈ σ.toSubmodule := hσ_inv ⟨1, q₀.out⁻¹⟩ g hg_mem
          have hg₁_supp_target : q₀.out⁻¹ • q₀ = q₁ := by
            rw [hq₁_def, ← MulAction.Quotient.coe_smul_out (H := stabAux φ χ)]
            simp [smul_eq_mul, inv_mul_cancel]
          -- Step 2: σ contains all Pi.single q u
          -- (main argument uses simplicity of U)
          suffices h_single : ∀ q u, Pi.single q u ∈ σ.toSubmodule by
            apply eq_top_iff.mpr
            intro x _
            have : x = ∑ q ∈ Finset.univ, Pi.single q (x q) := by
              ext q; simp [Finset.sum_apply, Pi.single_apply]
            rw [this]
            exact σ.toSubmodule.sum_mem (fun q _ => h_single q (x q))
          -- First show Pi.single q₁ u ∈ σ for all u, using simplicity of U
          -- q₁.out ∈ H since [q₁.out] = q₁ = [1]
          have hq₁_out_mem : q₁.out ∈ stabAux φ χ := by
            have := QuotientGroup.leftRel_apply.mp (Quotient.exact' (QuotientGroup.out_eq' q₁))
            simpa using (stabAux φ χ).inv_mem this
          have h_at_q₁ : ∀ u, Pi.single q₁ u ∈ σ.toSubmodule := by
            letI : MulAction G (G ⧸ stabAux φ χ) := inferInstance
            -- Step 1: g₁ is supported only on q₁
            have hg₁_supp : ∀ q, q ≠ q₁ → g₁ q = 0 := by
              intro q hq
              -- g₁ = ρ⟨1, q₀.out⁻¹⟩ g. By G_action_at_coset, g₁(q) involves
              -- g(q₀.out⁻¹⁻¹ • q) = g(q₀.out • q). This is 0 when q₀.out • q ≠ q₀,
              -- which happens iff q ≠ q₀.out⁻¹ • q₀ = q₁.
              change (ρ ⟨1, q₀.out⁻¹⟩ g) q = 0
              rw [show ρ = inducedRep_raw φ χ U from rfl, G_action_at_coset]
              simp only [inv_inv]
              have h1 : g (q₀.out • q) = 0 := hg_supp _ (by
                intro h; apply hq
                calc q = 1 • q := (one_smul G q).symm
                  _ = (q₀.out⁻¹ * q₀.out) • q := by rw [inv_mul_cancel]
                  _ = q₀.out⁻¹ • (q₀.out • q) := mul_smul _ _ _
                  _ = q₀.out⁻¹ • q₀ := by rw [h]
                  _ = q₁ := hg₁_supp_target)
              simp only [h1, map_zero]
            -- Step 2: g₁ q₁ ≠ 0
            have hg₁_nz : g₁ q₁ ≠ 0 := by
              change (ρ ⟨1, q₀.out⁻¹⟩ g) q₁ ≠ 0
              rw [show ρ = inducedRep_raw φ χ U from rfl, G_action_at_coset]
              set s₀ : ↥(stabAux φ χ) := ⟨_, transition_mem_stab φ χ q₀.out⁻¹ q₁⟩
              simp only [inv_inv]
              have heval : q₀.out • q₁ = q₀ := by
                rw [show q₁ = q₀.out⁻¹ • q₀ from hg₁_supp_target.symm,
                  ← mul_smul, mul_inv_cancel, one_smul]
              conv in g _ => rw [heval]
              intro h
              apply hg_nz
              have key := congr_arg (FDRep.ρ U s₀⁻¹) h
              rw [map_zero] at key
              rwa [show FDRep.ρ U s₀⁻¹ (FDRep.ρ U s₀ (g q₀)) = g q₀ from by
                change (FDRep.ρ U s₀⁻¹ * FDRep.ρ U s₀) (g q₀) = g q₀
                rw [← map_mul, inv_mul_cancel, map_one]; rfl] at key
            -- Step 3: g₁ = Pi.single q₁ (g₁ q₁)
            have hg₁_eq : g₁ = Pi.single q₁ (g₁ q₁) := by
              ext q; by_cases hq : q = q₁
              · rw [hq, Pi.single_eq_same]
              · rw [hg₁_supp q hq]
                simp [Pi.single, Function.update, if_neg hq]
            -- Step 4: S = {u | Pi.single q₁ u ∈ σ} is a nonzero sub-rep of U
            -- For any s ∈ stabAux, acting by (1, q₁.out * s * q₁.out⁻¹) on
            -- Pi.single q₁ u gives Pi.single q₁ (ρ_U(s)(u)).
            -- Since σ is invariant, this shows S is invariant under ρ_U.
            -- By simplicity of U, S = U.
            intro u
            obtain ⟨f, hf_mem, hf_eq, hf_supp⟩ := sigma_contains_all_single φ χ U hU
              σ.toSubmodule hσ_inv q₁ hq₁_out_mem g₁ hg₁_mem hg₁_nz hg₁_supp u
            -- f ∈ σ, f(q₁) = u, f(q) = 0 for q ≠ q₁
            -- f = Pi.single q₁ u by funext
            convert hf_mem using 1
            ext q; by_cases hq : q = q₁
            · rw [hq, Pi.single_eq_same, hf_eq]
            · rw [Pi.single_eq_of_ne hq, hf_supp q hq]
          -- For any coset q, Pi.single q u ∈ σ
          -- Transport via G-action: ρ(1, q.out) maps V_{q₁} to V_q
          intro q u
          letI : MulAction G (G ⧸ stabAux φ χ) := inferInstance
          set t : ↥(stabAux φ χ) := ⟨q₁.out, hq₁_out_mem⟩
          set u' := FDRep.ρ U t⁻¹ u
          -- Pi.single q₁ u' ∈ σ
          have hu'_mem := h_at_q₁ u'
          -- ρ(1, q.out)(Pi.single q₁ u') ∈ σ
          have h_acted := hσ_inv ⟨1, q.out⟩ _ hu'_mem
          -- Show ρ(1, q.out)(Pi.single q₁ u') = Pi.single q u pointwise
          have hq_inv : q.out⁻¹ • q = q₁ := by
            rw [hq₁_def, ← QuotientGroup.out_eq' q,
              ← MulAction.Quotient.coe_smul_out (H := stabAux φ χ)]
            simp [smul_eq_mul, inv_mul_cancel]
          have heq : ∀ q', (inducedRep_raw φ χ U ⟨1, q.out⟩ (Pi.single q₁ u')) q' =
              (Pi.single q u : (G ⧸ stabAux φ χ) → ↥U) q' := by
            intro q'
            by_cases hq' : q' = q
            · -- At q' = q: ρ_U(t)(u') = ρ_U(t)(ρ_U(t⁻¹)(u)) = u
              rw [hq', Pi.single_eq_same, G_action_at_coset]
              -- Simplify transition element
              simp only [show (q.out⁻¹ : G) • (q : G ⧸ stabAux φ χ) = q₁ from hq_inv]
              -- Evaluate Pi.single at the argument
              simp only [Pi.single_apply, show (q.out⁻¹ : G) • (q : G ⧸ stabAux φ χ) = q₁
                from hq_inv, ite_true]
              -- Now: (U.ρ ⟨q.out⁻¹ * q.out * q₁.out, ⋯⟩) u' = u
              have hrho_eq : ∀ (s₁ s₂ : ↥(stabAux φ χ)),
                  (s₁ : G) = (s₂ : G) → ∀ v, (FDRep.ρ U s₁) v = (FDRep.ρ U s₂) v := by
                intro s₁ s₂ h v; rw [Subtype.ext h]
              rw [hrho_eq _ t (by
                show q.out⁻¹ * q.out * q₁.out = q₁.out
                rw [inv_mul_cancel, one_mul]) u']
              change (FDRep.ρ U t * FDRep.ρ U t⁻¹) u = u
              rw [← map_mul, mul_inv_cancel, map_one]; rfl
            · -- At q' ≠ q: both sides are 0
              rw [Pi.single_eq_of_ne hq', G_action_at_coset]
              have hne : q.out⁻¹ • q' ≠ q₁ := by
                intro h; apply hq'
                have key : q.out⁻¹ • q' = q.out⁻¹ • q := h.trans hq_inv.symm
                calc q' = (q.out * q.out⁻¹) • q' := by rw [mul_inv_cancel, one_smul]
                  _ = q.out • (q.out⁻¹ • q') := mul_smul _ _ _
                  _ = q.out • (q.out⁻¹ • q) := by rw [key]
                  _ = (q.out * q.out⁻¹) • q := (mul_smul _ _ _).symm
                  _ = q := by rw [mul_inv_cancel, one_smul]
              rw [Pi.single_eq_of_ne hne, map_zero]
          -- Conclude membership: ρ(1,q.out)(Pi.single q₁ u') and Pi.single q u
          -- agree pointwise, so they're in the same submodule
          have h_fn_eq : ρ ⟨1, q.out⟩ (Pi.single q₁ u') = Pi.single q u := by
            change inducedRep_raw φ χ U ⟨1, q.out⟩ (Pi.single q₁ u') = Pi.single q u
            exact funext heq
          rw [← h_fn_eq]; convert h_acted }
  exact simple_of_isSimpleModule_asModule' ρ

-- (ii) Orbit injectivity: if V(χ₁, U₁) ≅ V(χ₂, U₂) then χ₁, χ₂ are in the same orbit.
-- Proof: the A-eigenvalues of V(χ, U) form the orbit of χ under G. An isomorphism
-- preserves A-eigenvalues, so the orbits must coincide.
-- Helper: the A-action on V(χ,U) at coset q is scalar multiplication by the character.
-- This is extracted from endo_preserves_cosets's hA_action proof.
open Classical in
private lemma A_action_scalar {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (U : FDRep ℂ ↥(stabAux φ χ))
    (a : A) (f : (G ⧸ stabAux φ χ) → ↥U) (q : G ⧸ stabAux φ χ) :
    (inducedRepV φ χ U).ρ ⟨a, 1⟩ f q =
    ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) • f q := by
  change ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) •
    (FDRep.ρ U ⟨q.out⁻¹ * (1 : G) * ((1 : G)⁻¹ • q).out,
      transition_mem_stab φ χ (1 : G) q⟩) (f ((1 : G)⁻¹ • q)) = _
  have hrho : ∀ (s : ↥(stabAux φ χ)) (hs : (s : G) = 1) (v : ↥U),
      (FDRep.ρ U s) v = v := by
    intro s hs v; rw [show s = 1 from Subtype.ext hs, map_one, Module.End.one_apply]
  simp only [inv_one, one_smul, mul_one]
  congr 1
  exact hrho _ (inv_mul_cancel q.out) _

open Classical in
private lemma inducedRepV_orbit_injectivity {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (χ₁ χ₂ : A →* ℂˣ)
    (U₁ : FDRep ℂ ↥(stabAux φ χ₁)) (U₂ : FDRep ℂ ↥(stabAux φ χ₂))
    (hU₁ : CategoryTheory.Simple U₁) (hU₂ : CategoryTheory.Simple U₂)
    (hiso : Nonempty (inducedRepV φ χ₁ U₁ ≅ inducedRepV φ χ₂ U₂)) :
    ∃ g : G, dualSmulAux φ g χ₁ = χ₂ := by
  obtain ⟨e⟩ := hiso
  set T := FDRep.isoToLinearEquiv e
  -- T commutes with the group action
  have hT_comm : ∀ (ag : A ⋊[φ] G) (f : ↥(inducedRepV φ χ₁ U₁)),
      T ((inducedRepV φ χ₁ U₁).ρ ag f) = (inducedRepV φ χ₂ U₂).ρ ag (T f) := by
    intro ag f
    have h := FDRep.Iso.conj_ρ e ag
    show T (((inducedRepV φ χ₁ U₁).ρ ag) f) = ((inducedRepV φ χ₂ U₂).ρ ag) (T f)
    simp only [h, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change T (((inducedRepV φ χ₁ U₁).ρ ag) f) = T (((inducedRepV φ χ₁ U₁).ρ ag) (T.symm (T f)))
    rw [LinearEquiv.symm_apply_apply]
  -- Get nonzero element of U₁ (Simple implies nontrivial)
  haveI : Nontrivial ↥U₁ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply CategoryTheory.id_nonzero U₁
    haveI : Subsingleton ↑U₁.V.obj := ‹Subsingleton ↥U₁›
    ext; exact Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := exists_ne (0 : ↥U₁)
  -- Identity coset q₁ = ⟦1⟧ in G/G_{χ₁}
  set q₁ := (⟦(1 : G)⟧ : G ⧸ stabAux φ χ₁)
  -- f = Pi.single q₁ u is nonzero
  set f : (G ⧸ stabAux φ χ₁) → ↥U₁ := Pi.single q₁ u
  have hf_ne : f ≠ 0 := by
    intro h; apply hu
    have := congr_fun h q₁
    simpa [f, Pi.single_eq_same] using this
  -- Tf ≠ 0 (T is bijective)
  have hTf_ne : T f ≠ 0 := by
    rw [ne_eq, ← T.map_zero]; exact T.injective.ne hf_ne
  -- ∃ q₂ with (Tf)(q₂) ≠ 0
  obtain ⟨q₂, hq₂⟩ : ∃ q₂ : G ⧸ stabAux φ χ₂, (T f) q₂ ≠ 0 := by
    by_contra h; push_neg at h; exact hTf_ne (funext h)
  -- Key: dualSmulAux φ q₁.out χ₁ = dualSmulAux φ q₂.out χ₂
  -- (eigenvalue argument: characters must match where Tf is nonzero)
  have hchar_match : dualSmulAux φ q₁.out χ₁ = dualSmulAux φ q₂.out χ₂ := by
    by_contra hne
    apply hq₂
    -- Get witness a where characters differ
    have hne' : ¬ (dualSmulAux φ q₁.out χ₁ = dualSmulAux φ q₂.out χ₂) := hne
    rw [DFunLike.ext_iff, not_forall] at hne'
    obtain ⟨a₀, ha₀⟩ := hne'
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at ha₀
    -- From T-equivariance at ⟨a₀, 1⟩ evaluated at q₂:
    have hcomm_q₂ : (T ((inducedRepV φ χ₁ U₁).ρ ⟨a₀, 1⟩ f)) q₂ =
        ((inducedRepV φ χ₂ U₂).ρ ⟨a₀, 1⟩ (T f)) q₂ :=
      congr_fun (hT_comm ⟨a₀, 1⟩ f) q₂
    -- LHS: f is supported on q₁, so V₁.ρ ⟨a₀,1⟩ f = c₁ • f, so T(c₁ • f) = c₁ • Tf
    have hf_supp : ∀ q, q ≠ q₁ → f q = 0 := by
      intro q hq; simp [f, Ne.symm hq]
    have haction_f : (inducedRepV φ χ₁ U₁).ρ ⟨a₀, 1⟩ f =
        ((χ₁ ((φ q₁.out⁻¹ : MulAut A) a₀) : ℂˣ) : ℂ) • f := by
      funext q
      rw [A_action_scalar φ χ₁ U₁ a₀ f q, Pi.smul_apply]
      by_cases hq : q = q₁
      · subst hq; rfl
      · rw [hf_supp q hq, smul_zero, smul_zero]
    rw [haction_f, map_smul, Pi.smul_apply] at hcomm_q₂
    -- RHS: V₂.ρ ⟨a₀,1⟩ (Tf) at q₂ = c₂ • (Tf)(q₂)
    rw [A_action_scalar φ χ₂ U₂ a₀ (T f) q₂] at hcomm_q₂
    -- hcomm_q₂: c₁ • (Tf)(q₂) = c₂ • (Tf)(q₂)
    have hsub : (((χ₁ ((φ q₁.out⁻¹ : MulAut A) a₀) : ℂˣ) : ℂ) -
        ((χ₂ ((φ q₂.out⁻¹ : MulAut A) a₀) : ℂˣ) : ℂ)) • (T f) q₂ = 0 := by
      rw [sub_smul, sub_eq_zero]; exact hcomm_q₂
    rw [smul_eq_zero] at hsub
    rcases hsub with h | h
    · exfalso; apply ha₀; exact_mod_cast sub_eq_zero.mp h
    · exact h
  -- q₁.out ∈ stabAux φ χ₁, so dualSmulAux φ q₁.out χ₁ = χ₁
  have hq₁_stab : q₁.out ∈ stabAux φ χ₁ := by
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact' (QuotientGroup.out_eq' q₁))
    simpa using (stabAux φ χ₁).inv_mem this
  -- dualSmulAux φ q₁.out χ₁ = χ₁ (stabilizer condition)
  have hq₁_char : dualSmulAux φ q₁.out χ₁ = χ₁ := hq₁_stab
  -- So χ₁ = dualSmulAux φ q₂.out χ₂
  have h_eq : χ₁ = dualSmulAux φ q₂.out χ₂ := hq₁_char ▸ hchar_match
  -- Invert: χ₂ = dualSmulAux φ (q₂.out⁻¹) χ₁
  exact ⟨q₂.out⁻¹, by
    ext a
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, inv_inv]
    have h := DFunLike.ext_iff.mp h_eq ((φ q₂.out : MulAut A) a)
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [show (φ q₂.out⁻¹ : MulAut A) ((φ q₂.out : MulAut A) a) = a from by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]] at h
    exact congrArg Units.val h⟩

-- (iii) Completeness: every irrep of G ⋉ A arises as some V(χ, U).
-- Proof strategy (direct construction, following the book):
-- 1. Restrict W to A. Since A is finite abelian over ℂ, W|_A decomposes into characters.
-- 2. Pick any character χ appearing (i.e., W_χ ≠ 0).
-- 3. The χ-weight space W_χ is a G_χ-submodule of W.
-- 4. Pick a simple G_χ-subrepresentation U ↪ W_χ.
-- 5. Construct a nonzero A⋊G-morphism V(χ,U) → W via Frobenius reciprocity.
-- 6. By Schur's lemma (both are simple), this morphism is an isomorphism.

-- The weight space W_χ = {w ∈ W | ∀ a, ρ(a,1)(w) = χ(a) · w}
private def weightSpace {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (W : FDRep ℂ (A ⋊[φ] G)) (χ : A →* ℂˣ) : Submodule ℂ W :=
  ⨅ (a : A), LinearMap.ker (W.ρ ⟨a, 1⟩ - ((χ a : ℂˣ) : ℂ) • LinearMap.id)

-- Helper: A character of A appearing in W exists (W_χ ≠ 0 for some χ)
-- Proof: A is finite abelian over ℂ (alg. closed, char 0), so W|_A is semisimple
-- and decomposes into 1-dimensional characters. Since W ≠ 0 (it's simple), some
-- weight space is nonzero.
private lemma exists_character_in_rep {G A : Type} [Group G] [CommGroup A]
    [Fintype G] [Fintype A]
    (φ : G →* MulAut A) (W : FDRep ℂ (A ⋊[φ] G)) (hW : CategoryTheory.Simple W) :
    ∃ χ : A →* ℂˣ, weightSpace φ W χ ≠ ⊥ := by
  -- W is nontrivial since it's simple
  have hnt : Nontrivial W := by
    by_contra h; rw [not_nontrivial_iff_subsingleton] at h
    exact (CategoryTheory.Simple.not_isZero W)
      ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr (by
        haveI : Subsingleton (↑W.V.obj) := h
        ext x; exact Subsingleton.elim _ _))
  -- Restrict W to A via a ↦ (a,1). By Maschke, the ℂ[A]-module is semisimple.
  let ρ_A : Representation ℂ A W := (FDRep.ρ W).comp SemidirectProduct.inl
  haveI : NeZero (Nat.card A : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- Get a simple ℂ[A]-submodule (exists by semisimplicity + nontriviality)
  haveI : Nontrivial ρ_A.asModule := hnt
  obtain ⟨m, hm⟩ := IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra ℂ A) ρ_A.asModule
  -- Since A is commutative, m is 1-dim (finrank_eq_one_of_isMulCommutative)
  -- The A-action on m is by scalars → defines a character χ : A →* ℂˣ
  -- Any nonzero v ∈ m satisfies ρ(a,1)v = χ(a)·v, so v ∈ weightSpace φ W χ
  sorry

-- Helper: The weight space W_χ is invariant under G_χ
-- Proof: For g ∈ G_χ and w ∈ W_χ, ρ(a,1)(ρ(1,g)(w)) = ρ(1,g)(ρ(g⁻¹ag,1)(w))
-- = ρ(1,g)(χ(g⁻¹ag)·w) = χ(g⁻¹ag)·ρ(1,g)(w). Since g ∈ G_χ, χ(g⁻¹ag) = χ(a).
private lemma weightSpace_stabAux_invariant {G A : Type} [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) (W : FDRep ℂ (A ⋊[φ] G)) (χ : A →* ℂˣ)
    (g : ↥(stabAux φ χ)) : ∀ w ∈ weightSpace φ W χ,
      W.ρ ⟨1, (g : G)⟩ w ∈ weightSpace φ W χ := by
  intro w hw
  -- w ∈ weightSpace means: for all a, ρ(a,1)(w) = χ(a) • w
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at hw ⊢
  intro a
  -- Need: ρ(a,1)(ρ(1,g)(w)) - χ(a) • ρ(1,g)(w) = 0
  -- Key: ρ(a,1) ∘ ρ(1,g) = ρ(a,g) = ρ(1,g) ∘ ρ(g⁻¹ag, 1) (since (1,g)(g⁻¹ag,1) = (a,g))
  -- And since g ∈ G_χ and A is commutative: χ(g⁻¹ag) = χ(a)
  -- So ρ(a,1)(ρ(1,g)(w)) = ρ(1,g)(ρ(g⁻¹ag,1)(w)) = ρ(1,g)(χ(g⁻¹ag)•w) = χ(a)•ρ(1,g)(w)
  have hga : (⟨a, (1 : G)⟩ : A ⋊[φ] G) * ⟨1, (g : G)⟩ =
      ⟨1, (g : G)⟩ * ⟨(φ (g : G)⁻¹ : MulAut A) a, 1⟩ := by
    ext
    · simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.one_left, SemidirectProduct.one_right]
    · simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.one_left, SemidirectProduct.one_right]
  -- ρ(a,1)(ρ(1,g)(w)) = ρ((a,1)*(1,g))(w) = ρ((1,g)*(g⁻¹ag,1))(w)
  have step1 : W.ρ ⟨a, (1 : G)⟩ (W.ρ ⟨1, (g : G)⟩ w) =
      W.ρ ⟨1, (g : G)⟩ (W.ρ ⟨(φ (g : G)⁻¹ : MulAut A) a, 1⟩ w) := by
    rw [← Module.End.mul_apply, ← map_mul, hga, map_mul, Module.End.mul_apply]
  -- ρ(g⁻¹ag,1)(w) = χ(g⁻¹ag) • w (since w ∈ W_χ)
  have step2 := hw ((φ (g : G)⁻¹ : MulAut A) a)
  -- Since A is commutative: g⁻¹ag = a in A, so χ(g⁻¹ag) = χ(a)
  -- Actually, (φ g⁻¹)(a) is what appears. Since g ∈ G_χ, χ((φ g⁻¹)(a)) = χ(a).
  have hstab : χ ((φ (g : G)⁻¹ : MulAut A) a) = χ a := by
    have hg_mem := g.2  -- g ∈ stabAux φ χ means dualSmulAux φ g χ = χ
    have := DFunLike.ext_iff.mp hg_mem a
    simp only [dualSmulAux, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    exact this
  rw [step1, sub_eq_zero]
  -- step2 says ρ(φ(g⁻¹)(a),1)(w) - χ(φ(g⁻¹)(a)) • w = 0
  rw [sub_eq_zero] at step2
  rw [step2, map_smul, hstab]

-- Construct the G_χ-representation on the weight space
private noncomputable def weightSpaceRep {G A : Type} [Group G] [CommGroup A]
    [Fintype G] [Fintype A]
    (φ : G →* MulAut A) (W : FDRep ℂ (A ⋊[φ] G)) (χ : A →* ℂˣ)
    (hχ : weightSpace φ W χ ≠ ⊥) : FDRep ℂ ↥(stabAux φ χ) :=
  FDRep.of (V := ↥(weightSpace φ W χ)) <|
  { toFun := fun g =>
    { toFun := fun ⟨w, hw⟩ =>
        ⟨W.ρ ⟨1, (g : G)⟩ w, weightSpace_stabAux_invariant φ W χ g w hw⟩
      map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => Subtype.ext (map_add _ _ _)
      map_smul' := fun c ⟨x, _⟩ => Subtype.ext (map_smul _ _ _) }
    map_one' := by
      ext ⟨w, hw⟩
      -- Goal: action of 1 ∈ G_χ on (w, hw) = (w, hw)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
      congr 1
      show (W.ρ ⟨1, ((1 : ↥(stabAux φ χ)) : G)⟩) w = w
      rw [show ((1 : ↥(stabAux φ χ)) : G) = 1 from rfl]
      have : (⟨(1 : A), (1 : G)⟩ : A ⋊[φ] G) = 1 := by
        ext <;> simp [SemidirectProduct.one_left, SemidirectProduct.one_right]
      rw [this, map_one]; rfl
    map_mul' := fun g₁ g₂ => by
      ext ⟨w, hw⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
      -- Goal: ⟨ρ(1,g₁g₂)w, _⟩ = ⟨ρ(1,g₁)(ρ(1,g₂)w), _⟩
      -- (1,g₁)*(1,g₂) = (1,g₁g₂) in A ⋊ G (since φ(g₁)(1) = 1)
      -- Need: ρ(1,g₁g₂)w = ρ(1,g₁)(ρ(1,g₂)w), i.e. the underlying elements match
      change (W.ρ ⟨1, ↑(g₁ * g₂)⟩) w = (W.ρ ⟨1, ↑g₁⟩) ((W.ρ ⟨1, ↑g₂⟩) w)
      rw [← Module.End.mul_apply, ← map_mul]
      congr 1
      ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.one_left,
          SemidirectProduct.mul_right, SemidirectProduct.one_right, Subgroup.coe_mul] }

-- Helper: A nonzero finite-dimensional ℂ-representation of a finite group has a simple
-- subrepresentation. Uses Maschke's theorem (semisimplicity) and induction on finrank.
private lemma exists_simple_subrep {H : Type} [Group H] [Fintype H]
    (V : FDRep ℂ H) (hV : ¬ CategoryTheory.Limits.IsZero V) :
    ∃ U : FDRep ℂ H, CategoryTheory.Simple U ∧ Nonempty (U ⟶ V) := by
  sorry

-- Helper: Frobenius reciprocity map from V(χ,U) to W
-- Given U ↪ W_χ (as G_χ-reps), construct a nonzero A⋊G-morphism V(χ,U) → W
private lemma exists_nonzero_map_from_induced {G A : Type} [Group G] [CommGroup A]
    [Fintype G] [Fintype A]
    (φ : G →* MulAut A) (χ : A →* ℂˣ)
    (W : FDRep ℂ (A ⋊[φ] G)) (hW : CategoryTheory.Simple W)
    (hχ : weightSpace φ W χ ≠ ⊥)
    (U : FDRep ℂ ↥(stabAux φ χ)) (hU : CategoryTheory.Simple U)
    (hUW : Nonempty (U ⟶ weightSpaceRep φ W χ hχ)) :
    Nonempty (inducedRepV φ χ U ≅ W) := by
  sorry

open Classical in
private lemma inducedRepV_completeness {G A : Type} [Group G] [CommGroup A]
    [Fintype G] [Fintype A]
    (φ : G →* MulAut A)
    (W : FDRep ℂ (A ⋊[φ] G)) (hW : CategoryTheory.Simple W) :
    ∃ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stabAux φ χ)),
      CategoryTheory.Simple U ∧ Nonempty (W ≅ inducedRepV φ χ U) := by
  -- Step 1: Find a character χ with nonzero weight space
  obtain ⟨χ, hχ⟩ := exists_character_in_rep φ W hW
  -- Step 2: The weight space is a nonzero G_χ-representation
  let Wχ := weightSpaceRep φ W χ hχ
  -- Step 3: Find a simple G_χ-subrepresentation U of W_χ
  have hWχ_nz : ¬ CategoryTheory.Limits.IsZero Wχ := by
    -- Contrapositive: weightSpace ≠ ⊥ means Nontrivial carrier; Nontrivial carrier ⟹ ¬ IsZero
    rw [Ne, Submodule.eq_bot_iff, not_forall] at hχ
    obtain ⟨v, hv⟩ := hχ; push_neg at hv; obtain ⟨hv_mem, hv_ne⟩ := hv
    intro hzero; apply hv_ne
    -- IsZero implies Subsingleton carrier
    have hsub : Subsingleton ↑Wχ.V.obj := by
      constructor; intro a b
      -- Subsingleton follows from IsZero.eq_of_src: all parallel morphisms are equal
      -- Build two morphisms from the terminal FDRep to Wχ hitting a and b respectively
      -- Since IsZero Wχ, all maps into it are equal, but we need out of it
      -- Instead: IsZero means all endomorphisms are equal, in particular 𝟙 = 0
      -- This means the identity linear map equals zero, so ∀ x, x = 0
      have h : (CategoryTheory.CategoryStruct.id Wχ : Wχ ⟶ Wχ) = 0 :=
        hzero.eq_of_src _ _
      -- Extract at element level using the ext lemma pattern
      -- We know that for FDRep, ext says morphisms are determined by their .hom component
      -- And .hom is in FGModuleCat where ext says determined by underlying function
      -- So 𝟙 = 0 at function level: ∀ x, id x = 0 x, i.e., x = 0
      have ha : a = 0 := by
        have := congr_arg (fun (f : Wχ ⟶ Wχ) => f.hom.hom.hom a) h
        simpa using this
      have hb : b = 0 := by
        have := congr_arg (fun (f : Wχ ⟶ Wχ) => f.hom.hom.hom b) h
        simpa using this
      exact ha ▸ hb ▸ rfl
    have h := @Subsingleton.elim _ hsub ⟨v, hv_mem⟩ ⟨0, (weightSpace φ W χ).zero_mem⟩
    exact congr_arg Subtype.val h
  obtain ⟨U, hU_simple, ⟨ι⟩⟩ := exists_simple_subrep Wχ hWχ_nz
  -- Step 4: By Frobenius reciprocity + Schur, V(χ,U) ≅ W
  exact ⟨χ, U, hU_simple, (exists_nonzero_map_from_induced φ χ W hW hχ U hU_simple ⟨ι⟩).map CategoryTheory.Iso.symm⟩

open Classical in
/-- Classification of irreducible representations of semidirect products G ⋉ A
via the orbit method: they are parametrized by pairs (O, U) where O is a
G-orbit on the character group Â and U is an irreducible representation of
the stabilizer G_χ for a representative χ ∈ O.

The statement asserts the existence of:
- A dual G-action on Â = (A →* ℂˣ) given by (g · χ)(a) = χ(φ(g⁻¹)(a))
- For each χ, a stabilizer subgroup G_χ ≤ G
- A construction V(χ, U) producing a representation of A ⋊[φ] G

satisfying irreducibility, injectivity on orbits, surjectivity onto all
irreducibles, and the explicit character formula. (Etingof Theorem 5.27.1) -/
theorem Etingof.Theorem5_27_1
    (G A : Type) [Group G] [CommGroup A] [Fintype G] [Fintype A]
    (φ : G →* MulAut A) :
    ∃ (-- The dual G-action on Â: (g · χ)(a) = χ(φ(g⁻¹)(a))
       dualSmul : G → (A →* ℂˣ) → (A →* ℂˣ))
      (_ : ∀ g χ a, dualSmul g χ a = χ ((φ g⁻¹ : MulAut A) a))
      (-- Stabilizer G_χ = {g ∈ G | g · χ = χ}
       stab : (A →* ℂˣ) → Subgroup G)
      (_ : ∀ χ g, g ∈ stab χ ↔ dualSmul g χ = χ)
      (-- The construction V(χ, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ)
       V : (χ : A →* ℂˣ) → FDRep ℂ ↥(stab χ) → FDRep ℂ (A ⋊[φ] G)),
      -- (i) V(χ, U) is irreducible when U is irreducible
      (∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
        CategoryTheory.Simple U → CategoryTheory.Simple (V χ U)) ∧
      -- (ii) V(χ₁, U₁) ≅ V(χ₂, U₂) implies χ₁ and χ₂ are in the same G-orbit
      (∀ (χ₁ χ₂ : A →* ℂˣ)
        (U₁ : FDRep ℂ ↥(stab χ₁)) (U₂ : FDRep ℂ ↥(stab χ₂)),
        CategoryTheory.Simple U₁ → CategoryTheory.Simple U₂ →
        Nonempty (V χ₁ U₁ ≅ V χ₂ U₂) →
        ∃ g : G, dualSmul g χ₁ = χ₂) ∧
      -- (iii) Every irreducible representation of A ⋊[φ] G arises as V(χ, U)
      (∀ (W : FDRep ℂ (A ⋊[φ] G)), CategoryTheory.Simple W →
        ∃ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
          CategoryTheory.Simple U ∧ Nonempty (W ≅ V χ U)) ∧
      -- (iv) Character formula
      (∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
        CategoryTheory.Simple U →
        ∀ (a : A) (g : G),
          (V χ U).character ⟨a, g⟩ =
            (Fintype.card ↥(stab χ) : ℂ)⁻¹ *
              ∑ h : G, if hh : h * g * h⁻¹ ∈ stab χ
                then (χ ((φ h : MulAut A) a) : ℂ) *
                  U.character ⟨h * g * h⁻¹, hh⟩
                else 0) := by
  -- Provide the dual action, stabilizer, and induced representation constructions
  refine ⟨dualSmulAux φ, fun g χ a => rfl, stabAux φ, fun χ g => Iff.rfl, ?_⟩
  -- Use the concrete induced representation V(χ, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ)
  refine ⟨fun χ U => inducedRepV φ χ U, ?_, ?_, ?_, ?_⟩
  -- (i) Irreducibility: V(χ, U) is irreducible when U is irreducible
  · exact fun χ U hU => inducedRepV_simple φ χ U hU
  -- (ii) Orbit injectivity: iso implies same G-orbit
  · exact fun χ₁ χ₂ U₁ U₂ hU₁ hU₂ hiso =>
      inducedRepV_orbit_injectivity φ χ₁ χ₂ U₁ U₂ hU₁ hU₂ hiso
  -- (iii) Completeness: every irrep arises as some V(χ, U)
  · exact fun W hW => inducedRepV_completeness φ W hW
  -- (iv) Character formula
  · intro χ U _hU a g
    classical
    change (LinearMap.trace ℂ ((G ⧸ stabAux φ χ) → ↥U))
        ((inducedRepV φ χ U).ρ ⟨a, g⟩) = _
    -- The action has twisted permutation form: T f q = L q (f (σ q))
    have hTwist : ∀ (f : G ⧸ stabAux φ χ → ↥U) (q : G ⧸ stabAux φ χ),
        (inducedRepV φ χ U).ρ ⟨a, g⟩ f q =
        (((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) •
          FDRep.ρ U ⟨q.out⁻¹ * g * (g⁻¹ • q).out,
            transition_mem_stab φ χ g q⟩)
        (f (g⁻¹ • q)) := fun f q => rfl
    have step1 := trace_twisted_permutation (g⁻¹ • ·)
      (fun q => ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) •
        FDRep.ρ U ⟨q.out⁻¹ * g * (g⁻¹ • q).out,
          transition_mem_stab φ χ g q⟩) _ hTwist
    rw [step1]
    -- Goal: ∑ q, if g⁻¹•q = q then trace(c•ρ(s)) else 0
    --     = |H|⁻¹ * ∑ h:G, if h*g*h⁻¹ ∈ H then χ(φ(h)a) * char(h*g*h⁻¹) else 0
    -- Define the per-element function f on G
    -- f(h) = if h*g*h⁻¹ ∈ H then χ(φ(h)(a)) * U.character ⟨h*g*h⁻¹, _⟩ else 0
    -- Strategy: show both sides equal ∑ q, f(q.out⁻¹)
    -- Step 2: Both sides equal ∑ q, F(q)
    -- Use trans to go through an intermediate form
    -- LHS → intermediate: coset_fixed_iff + trace linearity
    -- intermediate → RHS: fiber sum decomposition
    trans (∑ q : G ⧸ stabAux φ χ,
      if hq : q.out⁻¹ * g * q.out ∈ stabAux φ χ then
        ((χ ((φ q.out⁻¹ : MulAut A) a) : ℂˣ) : ℂ) *
          U.character ⟨q.out⁻¹ * g * q.out, hq⟩
      else 0)
    · -- LHS = intermediate
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : q.out⁻¹ * g * q.out ∈ stabAux φ χ
      · have hfixed : g⁻¹ • q = q := (coset_fixed_iff _ g q).mpr hq
        have hout : (g⁻¹ • q).out = q.out := congrArg Quotient.out hfixed
        simp only [hfixed, ite_true, dif_pos hq, map_smul, smul_eq_mul, FDRep.character]
      · have hnotfixed : g⁻¹ • q ≠ q :=
          fun h => hq ((coset_fixed_iff _ g q).mp h)
        simp [hnotfixed, dif_neg hq]
    · -- Need: ∑ q F(q) = |H|⁻¹ * ∑ h f(h)
      -- Equivalently: ∑ h f(h) = |H| * ∑ q F(q)
      -- where F(q) = f(q.out⁻¹) with f(h) = if hgh⁻¹∈H then χ(φ(h)a)*char(hgh⁻¹) else 0
      -- Step 1: Show ∑ q, F(q) = ∑ q, f(q.out⁻¹)
      -- Step 2: ∑ h, f(h) = ∑ h, f(h⁻¹) (involution)
      -- Step 3: f∘inv is right-H-invariant
      -- Step 4: ∑ h, (f∘inv)(h) = |H| * ∑ q, (f∘inv)(q.out) = |H| * ∑ q, f(q.out⁻¹)
      -- Suffices to show |H| * ∑ q F(q) = ∑ h f(h), then multiply by |H|⁻¹
      rw [eq_comm, inv_mul_eq_div, div_eq_iff]
      · -- Need: ∑ h, f(h) = (∑ q, F(q)) * |H|
        -- Proof outline:
        -- (A) f is left-H-invariant: f(sh) = f(h) for s ∈ H
        --     because (sh)g(sh)⁻¹ = s(hgh⁻¹)s⁻¹ ∈ H ↔ hgh⁻¹ ∈ H,
        --     χ(φ(sh)(a)) = χ(φ(h)(a)) by stab_char_inv,
        --     char(sts⁻¹) = char(t) by FDRep.char_mul_comm
        -- (B) ∑ h, f(h) = ∑ h, f(h⁻¹) by Equiv.sum_comp (MulEquiv.inv G)
        -- (C) g := f∘inv is right-H-invariant (from A)
        -- (D) ∑ h, g(h) = |H| * ∑ q, g(q.out) by groupEquivQuotientProdSubgroup
        -- (E) g(q.out) = f(q.out⁻¹) = F(q) since q.out⁻¹*g*(q.out⁻¹)⁻¹ = q.out⁻¹*g*q.out
        -- Define g(h) = the "inverted" summand, which is right-H-invariant
        -- g(h) = if h⁻¹*g*h ∈ H then χ(φ(h⁻¹)(a))*char(h⁻¹*g*h) else 0
        -- Note: h⁻¹*g*(h⁻¹)⁻¹ = h⁻¹*g*h, so g(h) = f(h⁻¹) where f is the original
        -- ∑ h, f(h) = ∑ h, g(h) by reindexing
        -- g is right-H-invariant ⟹ ∑ h, g(h) = |H| * ∑ q, g(q.out) = |H| * ∑ q, F(q)
        let H := stabAux φ χ
        -- Define g directly to avoid `set`/`dif` issues
        let gfun : G → ℂ := fun h =>
          if hh : h⁻¹ * g * h ∈ H then
            ((χ ((φ h⁻¹ : MulAut A) a) : ℂˣ) : ℂ) *
              U.character ⟨h⁻¹ * g * h, hh⟩
          else 0
        -- Step 1: ∑ h, (original summand) = ∑ h, gfun h (by h ↦ h⁻¹)
        have sum_reindex : (∑ h : G, (if hh : h * g * h⁻¹ ∈ H then
              ((χ ((φ h : MulAut A) a) : ℂˣ) : ℂ) *
                U.character ⟨h * g * h⁻¹, hh⟩
            else 0)) = ∑ h : G, gfun h := by
          apply Fintype.sum_equiv (Equiv.inv G)
          intro h; simp only [Equiv.inv_apply, gfun, inv_inv]
        -- Step 2: gfun is right-H-invariant
        have gfun_right_inv : ∀ (h : G) (s : ↥H), gfun (h * ↑s) = gfun h := by
          intro h s; simp only [gfun]
          -- (h*s)⁻¹ * g * (h*s) = s⁻¹ * (h⁻¹ * g * h) * s
          have heq : (h * ↑s)⁻¹ * g * (h * ↑s) = (↑s)⁻¹ * (h⁻¹ * g * h) * ↑s := by group
          -- H-membership equivalence under conjugation
          have hmem_iff : (h * ↑s)⁻¹ * g * (h * ↑s) ∈ H ↔ h⁻¹ * g * h ∈ H := by
            rw [heq]
            constructor
            · intro ht
              have h1 := H.mul_mem (H.mul_mem s.2 ht) (H.inv_mem s.2)
              rwa [show ↑s * ((↑s)⁻¹ * (h⁻¹ * g * h) * ↑s) *
                (↑s)⁻¹ = h⁻¹ * g * h from by group] at h1
            · exact fun ht =>
                H.mul_mem (H.mul_mem (H.inv_mem s.2) ht) s.2
          by_cases hmem : h⁻¹ * g * h ∈ H
          · rw [dif_pos hmem, dif_pos (hmem_iff.mpr hmem)]
            congr 1
            · -- χ part: χ(φ((h*s)⁻¹)(a)) = χ(φ(h⁻¹)(a))
              -- (h*s)⁻¹ = s⁻¹*h⁻¹, so φ((h*s)⁻¹)(a) = φ(s⁻¹)(φ(h⁻¹)(a))
              -- Then χ(φ(s⁻¹)(x)) = χ(x) by stab_char_inv since s⁻¹ ∈ H
              congr 1
              rw [mul_inv_rev, map_mul, MulAut.mul_apply]
              exact stab_char_inv φ χ (H.inv_mem s.2) _
            · -- character part: char(s⁻¹*(h⁻¹*g*h)*s) = char(h⁻¹*g*h)
              -- Rewrite the subtype element as a conjugate
              have key : (⟨(h * ↑s)⁻¹ * g * (h * ↑s), hmem_iff.mpr hmem⟩ : ↥H) =
                  ⟨(↑s)⁻¹, H.inv_mem s.2⟩ * ⟨h⁻¹ * g * h, hmem⟩ *
                    ⟨(↑s)⁻¹, H.inv_mem s.2⟩⁻¹ := by
                ext; simp [Subgroup.coe_mul]; group
              rw [key]
              exact FDRep.char_conj U ⟨h⁻¹ * g * h, hmem⟩ ⟨(↑s)⁻¹, H.inv_mem s.2⟩
          · rw [dif_neg hmem, dif_neg (hmem_iff.not.mpr hmem)]
        -- Step 3: decompose ∑ h, gfun h = |H| * ∑ q, gfun q.out
        have sum_decomp := sum_right_invariant_eq H gfun gfun_right_inv
        -- Step 4: gfun(q.out) = F(q) since q.out⁻¹ * g * q.out matches
        rw [mul_comm, sum_reindex, sum_decomp]
      · -- Need: |H| ≠ 0
        exact Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')
