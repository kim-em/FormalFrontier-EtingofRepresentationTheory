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
    (G A : Type) [Group G] [CommGroup A] [Fintype G]
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
  · exact fun _ _ _ => sorry
  -- (ii) Orbit injectivity: iso implies same G-orbit
  · exact fun _ _ _ _ _ _ _ => sorry
  -- (iii) Completeness: every irrep arises as some V(χ, U)
  · exact fun _ _ => sorry
  -- (iv) Character formula
  · intro χ U _hU a g
    classical
    change (LinearMap.trace ℂ ((G ⧸ stabAux φ χ) → ↥U))
        ((inducedRepV φ χ U).ρ ⟨a, g⟩) = _
    haveI : Fintype (G ⧸ stabAux φ χ) := Quotient.fintype _
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
        sorry
      · -- Need: |H| ≠ 0
        exact Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')
