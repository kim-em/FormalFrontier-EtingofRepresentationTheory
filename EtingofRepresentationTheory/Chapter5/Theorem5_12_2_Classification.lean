import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Distinct
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Theorem 5.12.2 (Part 3): Wedderburn Block Machinery and Classification

Every irreducible representation of S_n over ℂ is isomorphic to V_λ for a unique
partition λ. The proof uses the Wedderburn decomposition of ℂ[S_n] and central
idempotents to match simple modules to Wedderburn blocks.
-/

namespace Etingof

noncomputable section
open scoped Classical

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A' (n : ℕ) := MonoidAlgebra ℂ (G' n)

/-- Central idempotent for block j of the Wedderburn decomposition. -/
private noncomputable def centralIdem' (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j : Fin D.n) :
    A' n :=
  D.iso.symm (Pi.single j 1)

private lemma centralIdem'_sq (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j : Fin D.n) :
    centralIdem' n D j * centralIdem' n D j = centralIdem' n D j := by
  simp only [centralIdem']
  rw [← map_mul D.iso.symm]
  congr 1; ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

private lemma centralIdem'_sum (n : ℕ) (D : IrrepDecomp ℂ (G' n)) :
    ∑ j, centralIdem' n D j = 1 := by
  simp only [centralIdem']
  rw [← map_sum D.iso.symm]
  conv_rhs => rw [← AlgEquiv.symm_apply_apply D.iso 1]
  congr 1
  ext i
  simp only [Finset.sum_apply, map_one, Pi.one_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji; simp [Pi.single_eq_of_ne (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma centralIdem'_orthog (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (i j : Fin D.n) (hij : i ≠ j) :
    centralIdem' n D i * centralIdem' n D j = 0 := by
  simp only [centralIdem']
  rw [← map_mul D.iso.symm, ← map_zero D.iso.symm]
  congr 1; ext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij]
    simp
  · simp [Pi.single_eq_of_ne hki]

private lemma centralIdem'_comm (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (j : Fin D.n) (a : A' n) :
    centralIdem' n D j * a = a * centralIdem' n D j := by
  simp only [centralIdem']
  apply D.iso.injective
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/-- For a simple A'(n)-module, exactly one central idempotent acts as identity. -/
private lemma exists_unique_block (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    ∃! j : Fin D.n, ∀ l : L, centralIdem' n D j • l = l := by
  -- Since ∑ e_j = 1, we have l = ∑ e_j • l for all l
  have hsum : ∀ l : L, l = ∑ j, centralIdem' n D j • l := by
    intro l; conv_lhs => rw [← one_smul (A' n) l, ← centralIdem'_sum n D]; rw [Finset.sum_smul]
  -- For each j, the kernel of e_j is a submodule (since e_j is central)
  -- By simplicity it's 0 or L, so e_j acts as 0 or as identity
  have hact : ∀ j, (∀ l : L, centralIdem' n D j • l = 0) ∨
                    (∀ l : L, centralIdem' n D j • l = l) := by
    intro j
    -- The kernel of e_j is a submodule of L (using centrality)
    let ker_j : Submodule (A' n) L :=
      { carrier := {l | centralIdem' n D j • l = l}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          change centralIdem' n D j • (a + b) = a + b
          rw [smul_add, ha, hb]
        smul_mem' := fun a {l} hl => by
          change centralIdem' n D j • (a • l) = a • l
          rw [← mul_smul, centralIdem'_comm, mul_smul, hl] }
    rcases IsSimpleOrder.eq_bot_or_eq_top ker_j with h | h
    · -- ker_j = ⊥: no element is fixed by e_j
      -- Since e_j² = e_j, for any l: e_j • (e_j • l) = e_j • l, so e_j • l ∈ ker_j = ⊥
      left; intro l
      have : centralIdem' n D j • l ∈ ker_j := by
        change centralIdem' n D j • (centralIdem' n D j • l) = centralIdem' n D j • l
        rw [← mul_smul, centralIdem'_sq]
      rw [h] at this; exact (Submodule.mem_bot (A' n)).mp this
    · right; intro l
      have : l ∈ ker_j := h ▸ Submodule.mem_top
      exact this
  -- Existence: not all e_j annihilate (since ∑ e_j • l = l)
  haveI := IsSimpleModule.nontrivial (R := A' n) (M := L)
  obtain ⟨l₀, hl₀⟩ := exists_ne (0 : L)
  have hexists : ∃ j, ∀ l : L, centralIdem' n D j • l = l := by
    by_contra hall
    push_neg at hall
    have : ∀ j, ∀ l : L, centralIdem' n D j • l = 0 := by
      intro j; exact (hact j).resolve_right (fun h => (hall j).elim (fun l hl => hl (h l)))
    exact hl₀ (by rw [hsum l₀, Finset.sum_eq_zero (fun j _ => this j l₀)])
  obtain ⟨j₀, hj₀⟩ := hexists
  -- Uniqueness: if e_i and e_j both act as identity, then i = j
  refine ⟨j₀, hj₀, ?_⟩
  intro j hj
  by_contra hij
  -- e_i * e_j = 0, but e_i * e_j • l = e_i • (e_j • l) = e_i • l = l ≠ 0
  have h1 : centralIdem' n D j * centralIdem' n D j₀ = 0 := centralIdem'_orthog n D j j₀ hij
  have h2 : (centralIdem' n D j * centralIdem' n D j₀) • l₀ = l₀ := by
    rw [mul_smul, hj₀ l₀, hj l₀]
  rw [h1, zero_smul] at h2
  exact hl₀ h2.symm

/-- The block assignment for a simple submodule of A'(n). -/
private noncomputable def blockOf (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    Fin D.n :=
  (exists_unique_block n D L).choose

private lemma blockOf_spec (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    ∀ l : L, centralIdem' n D (blockOf n D L) • l = l :=
  (exists_unique_block n D L).choose_spec.1

private lemma blockOf_unique (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L]
    (j : Fin D.n) (hj : ∀ l : L, centralIdem' n D j • l = l) :
    j = blockOf n D L :=
  (exists_unique_block n D L).choose_spec.2 j hj

/-- For x in block j₀, the A'(n)-action factors: a * x = iso⁻¹(Pi.single j₀ (proj a)) * x -/
private lemma action_factors_block (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) (a : A' n) :
    a * x = D.iso.symm (Pi.single j₀ (D.projRingHom j₀ a)) * x := by
  have key : a * centralIdem' n D j₀ = D.iso.symm (Pi.single j₀ (D.projRingHom j₀ a)) := by
    apply D.iso.injective; rw [map_mul, AlgEquiv.apply_symm_apply]
    ext k; simp only [Pi.mul_apply, centralIdem', AlgEquiv.apply_symm_apply]
    by_cases hk : k = j₀
    · subst hk; simp [Pi.single_eq_same, IrrepDecomp.projRingHom, Pi.evalRingHom]
    · simp [Pi.single_eq_of_ne hk]
  calc a * x = a * (centralIdem' n D j₀ * x) := by rw [hx]
    _ = (a * centralIdem' n D j₀) * x := by rw [mul_assoc]
    _ = D.iso.symm (Pi.single j₀ (D.projRingHom j₀ a)) * x := by rw [key]

/-- For block elements, D.iso x = Pi.single j₀ (proj x) -/
private lemma iso_eq_single_of_block (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) :
    D.iso x = Pi.single j₀ (D.projRingHom j₀ x) := by
  have h1 : D.iso (centralIdem' n D j₀ * x) = D.iso x := by rw [hx]
  rw [map_mul] at h1; simp only [centralIdem', AlgEquiv.apply_symm_apply] at h1
  ext k; rw [← h1]; simp only [Pi.mul_apply]
  by_cases hk : k = j₀
  · subst hk; simp [Pi.single_eq_same, IrrepDecomp.projRingHom, Pi.evalRingHom]
  · simp [Pi.single_eq_of_ne hk]

/-- For block elements, iso.symm ∘ Pi.single j₀ ∘ proj = id -/
private lemma recover_block (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) :
    D.iso.symm (Pi.single j₀ (D.projRingHom j₀ x)) = x := by
  rw [← iso_eq_single_of_block n D j₀ hx, D.iso.symm_apply_apply]

/-- projRingHom is injective on block j₀ elements -/
private lemma proj_inj_on_block (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x)
    (h0 : D.projRingHom j₀ x = 0) : x = 0 := by
  rw [← recover_block n D j₀ hx, h0, Pi.single_zero, map_zero]

/-- The image of a left ideal L (in block j₀) under projRingHom, as a left ideal of Matj. -/
private def projImage (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    (L : Submodule (A' n) (A' n)) : Submodule
      (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ)
      (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ) where
  carrier := {m | ∃ l ∈ L, D.projRingHom j₀ l = m}
  zero_mem' := ⟨0, L.zero_mem, map_zero _⟩
  add_mem' := fun ⟨l₁, hl₁, he₁⟩ ⟨l₂, hl₂, he₂⟩ =>
    ⟨l₁ + l₂, L.add_mem hl₁ hl₂, by rw [map_add, he₁, he₂]⟩
  smul_mem' := fun m {x} hx => by
    obtain ⟨l, hl, he⟩ := hx
    obtain ⟨a, ha⟩ := D.projRingHom_surjective j₀ m
    exact ⟨a * l, L.smul_mem a hl, by
      rw [map_mul, ha, he, smul_eq_mul]⟩

/-- The projImage of a simple left ideal (in the correct block) is simple as a Matj-module. -/
private lemma projImage_isSimple (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    (L : Submodule (A' n) (A' n)) [IsSimpleModule (A' n) L]
    (hL : ∀ l : L, centralIdem' n D j₀ * (l : A' n) = ↑l) :
    IsSimpleModule
      (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ)
      (projImage n D j₀ L) := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  · -- projImage ≠ ⊥: L is nontrivial, proj is injective on block
    intro h
    haveI := IsSimpleModule.nontrivial (R := A' n) (M := L)
    obtain ⟨l, hl⟩ := exists_ne (0 : L)
    have : D.projRingHom j₀ ↑l = 0 := by
      have hm : D.projRingHom j₀ ↑l ∈ projImage n D j₀ L := ⟨↑l, l.prop, rfl⟩
      rw [h] at hm; exact (Submodule.mem_bot _).mp hm
    exact hl (Subtype.ext (proj_inj_on_block n D j₀ (hL l) this))
  · -- Any proper sub-ideal N < projImage is ⊥
    intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN
    -- Pullback: {l ∈ L | proj(l) ∈ N}
    set N' : Submodule (A' n) L :=
      { carrier := {l : L | D.projRingHom j₀ ↑l ∈ N}
        zero_mem' := by simp [N.zero_mem]
        add_mem' := fun {a b} ha hb => by
          change D.projRingHom j₀ (↑a + ↑b) ∈ N
          rw [map_add]; exact N.add_mem ha hb
        smul_mem' := fun c {l} hl => by
          change D.projRingHom j₀ (c * ↑l) ∈ N
          rw [map_mul]; exact N.smul_mem _ hl } with N'_def
    -- N' ≠ ⊤ since N < projImage
    have hN'_ne_top : N' ≠ ⊤ := by
      intro h_eq
      apply ne_of_lt hN
      apply le_antisymm hN_le
      intro m hm
      obtain ⟨l, hl, he⟩ := hm
      have : (⟨l, hl⟩ : L) ∈ N' := h_eq ▸ Submodule.mem_top
      rw [N'_def] at this
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rw [← he]; exact this
    have hN'_bot :=
      (IsSimpleOrder.eq_bot_or_eq_top N').resolve_right hN'_ne_top
    -- N = ⊥
    apply hN_ne_bot; rw [eq_bot_iff]
    intro m hmN
    have hm_pi := hN_le hmN
    obtain ⟨l, hl, he⟩ := hm_pi
    have : (⟨l, hl⟩ : L) ∈ N' := by
      rw [N'_def]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      rw [he]; exact hmN
    rw [hN'_bot] at this
    rw [Submodule.mem_bot] at this
    have hl0 : l = 0 := congr_arg Subtype.val this
    rw [Submodule.mem_bot, ← he, hl0, map_zero]

/-- For m in projImage of L (in block j₀), recover(m) ∈ L. -/
private lemma recover_mem_of_projImage (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    (L : Submodule (A' n) (A' n))
    (hL : ∀ l : L, centralIdem' n D j₀ * (l : A' n) = ↑l)
    {m : Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ}
    (hm : m ∈ projImage n D j₀ L) :
    D.iso.symm (Pi.single j₀ m) ∈ L := by
  obtain ⟨l, hl, he⟩ := hm
  rw [← he, recover_block n D j₀ (hL ⟨l, hl⟩)]
  exact hl

/-- Recovering from projImage is injective (follows from iso.symm injective). -/
private lemma recover_injective_on_projImage (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    {m₁ m₂ : Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ}
    (h : D.iso.symm (Pi.single j₀ m₁) = D.iso.symm (Pi.single j₀ m₂)) :
    m₁ = m₂ := by
  have h1 := D.iso.symm.injective h
  have h2 := congr_fun h1 j₀
  simp only [Pi.single_eq_same] at h2
  exact h2

/-- proj ∘ recover = id on projImage elements. -/
private lemma proj_recover (n : ℕ) (D : IrrepDecomp ℂ (G' n)) (j₀ : Fin D.n)
    (m : Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ) :
    D.projRingHom j₀ (D.iso.symm (Pi.single j₀ m)) = m := by
  simp [IrrepDecomp.projRingHom, Pi.evalRingHom, Pi.single_eq_same]

/-- Two simple left ideals of A'(n) in the same Wedderburn block are isomorphic.
The proof projects both to simple left ideals of Mat_{j₀}(ℂ) via projRingHom,
uses IsSimpleRing.isIsotypic to get a Mat-linear isomorphism, then constructs
an A'(n)-linear map via recover ∘ φ_mat ∘ proj. Schur's lemma gives bijectivity. -/
private lemma same_block_iso (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (L₁ L₂ : Submodule (A' n) (A' n))
    [IsSimpleModule (A' n) L₁] [IsSimpleModule (A' n) L₂]
    (hblock : blockOf n D L₁ = blockOf n D L₂) :
    Nonempty (L₁ ≃ₗ[A' n] L₂) := by
  set j₀ := blockOf n D L₁ with hj₀_def
  -- Block specs: centralIdem' j₀ acts as identity on elements of L₁ and L₂
  have hL₁ : ∀ l : L₁, centralIdem' n D j₀ * (l : A' n) = ↑l :=
    fun l => congr_arg Subtype.val (blockOf_spec n D L₁ l)
  have hL₂ : ∀ l : L₂, centralIdem' n D j₀ * (l : A' n) = ↑l :=
    fun l => congr_arg Subtype.val (hblock ▸ blockOf_spec n D L₂ l)
  -- Project to simple left ideals of Matj, get Matj-linear iso via isIsotypic
  haveI := projImage_isSimple n D j₀ L₁ hL₁
  haveI := projImage_isSimple n D j₀ L₂ hL₂
  haveI := D.d_pos j₀
  haveI : IsSimpleRing (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ) := IsSimpleRing.matrix ..
  haveI : IsArtinianRing (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ) := inferInstance
  -- isIsotypic S m gives (m ≃ₗ S), swap args for (projImage L₁ ≃ₗ projImage L₂) direction
  obtain ⟨φ_mat⟩ := (IsSimpleRing.isIsotypic
    (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ)
    (Matrix (Fin (D.d j₀)) (Fin (D.d j₀)) ℂ))
    (projImage n D j₀ L₂) (projImage n D j₀ L₁)
  -- Helper: construct projImage element from L element
  let projElem (L : Submodule (A' n) (A' n)) (l : L) : projImage n D j₀ L :=
    ⟨D.projRingHom j₀ ↑l, ↑l, l.prop, rfl⟩
  -- Construct A'(n)-linear map f : L₁ →ₗ[A' n] L₂
  set f : L₁ →ₗ[A' n] L₂ :=
    { toFun := fun l₁ =>
        ⟨D.iso.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val),
         recover_mem_of_projImage n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop⟩
      map_add' := fun l₁ l₂ => by
        apply Subtype.ext; apply D.iso.injective
        simp only [Submodule.coe_add, map_add, AlgEquiv.apply_symm_apply]
        -- Pi.single distributes over addition
        have he : projElem L₁ (l₁ + l₂) = projElem L₁ l₁ + projElem L₁ l₂ := by
          ext; simp [projElem, map_add]
        rw [he, φ_mat.map_add, Submodule.coe_add, Pi.single_add]
      map_smul' := fun a l₁ => by
        apply Subtype.ext
        simp only [SetLike.val_smul, smul_eq_mul]
        -- LHS = iso.symm(Pi.single j₀ (φ(proj(a * l₁)).val))
        -- RHS = a * iso.symm(Pi.single j₀ (φ(proj l₁).val))
        set v := (φ_mat (projElem L₁ l₁)).val
        -- φ(proj(a * l₁)) = proj(a) • φ(proj l₁) by Matj-linearity
        have e_smul : projElem L₁ (a • l₁) = D.projRingHom j₀ a • projElem L₁ l₁ := by
          ext; simp [projElem, map_mul]
        have φ_smul : (φ_mat (projElem L₁ (a • l₁))).val = D.projRingHom j₀ a * v := by
          rw [e_smul, φ_mat.map_smul]; rfl
        rw [show D.iso.symm (Pi.single j₀ (φ_mat (projElem L₁ (a • l₁))).val) =
          D.iso.symm (Pi.single j₀ (D.projRingHom j₀ a * v)) from by rw [φ_smul]]
        -- RHS: a * iso.symm(Pi.single j₀ v)
        have hv_mem : D.iso.symm (Pi.single j₀ v) ∈ L₂ :=
          recover_mem_of_projImage n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop
        have hv_block : centralIdem' n D j₀ * D.iso.symm (Pi.single j₀ v) =
            D.iso.symm (Pi.single j₀ v) := hL₂ ⟨_, hv_mem⟩
        simp only [RingHom.id_apply]
        rw [action_factors_block n D j₀ hv_block a, ← map_mul D.iso.symm]
        congr 1; ext k; simp only [Pi.mul_apply]
        by_cases hk : k = j₀
        · subst hk; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne hk] }
  -- f is nonzero (since φ_mat is an equiv and proj is injective on block)
  have hf_ne : f ≠ 0 := by
    intro h
    haveI := IsSimpleModule.nontrivial (R := A' n) (M := L₁)
    obtain ⟨l₁, hl₁⟩ := exists_ne (0 : L₁)
    have h1 : f l₁ = 0 := congr_fun (congr_arg DFunLike.coe h) l₁
    -- f l₁ = 0 means iso.symm(Pi.single j₀ (φ_mat(proj l₁)).val) = 0
    have h2 : D.iso.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val) = 0 :=
      congr_arg Subtype.val h1
    -- So Pi.single j₀ (φ_mat(proj l₁)).val = 0, hence φ_mat(proj l₁).val = 0
    have h3 : (φ_mat (projElem L₁ l₁)).val = 0 := by
      have h3a := D.iso.symm.injective (by rw [h2, map_zero] : D.iso.symm (Pi.single j₀
        (φ_mat (projElem L₁ l₁)).val) = D.iso.symm 0)
      have h3b := congr_fun h3a j₀
      simp only [Pi.single_eq_same, Pi.zero_apply] at h3b
      exact h3b
    -- φ_mat is injective, so (projElem L₁ l₁).val = 0
    have h4 : projElem L₁ l₁ = 0 := by
      have : φ_mat (projElem L₁ l₁) = 0 := Subtype.ext h3
      exact φ_mat.injective (by rw [this, map_zero])
    have h5 : (projElem L₁ l₁).val = 0 := congr_arg Subtype.val h4
    exact hl₁ (Subtype.ext (proj_inj_on_block n D j₀ (hL₁ l₁) h5))
  -- By Schur's lemma, f is bijective
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf_ne)⟩

/-- The block map on Specht modules is injective: distinct partitions give distinct blocks. -/
private lemma blockOf_specht_injective (n : ℕ) (D : IrrepDecomp ℂ (G' n))
    (la mu : Nat.Partition n)
    (hla : IsSimpleModule (A' n) (SpechtModule n la))
    (hmu : IsSimpleModule (A' n) (SpechtModule n mu))
    (hblock : blockOf n D (SpechtModule n la) = blockOf n D (SpechtModule n mu)) :
    la = mu := by
  by_contra h
  have ⟨φ⟩ := @same_block_iso n D (SpechtModule n la) (SpechtModule n mu) hla hmu hblock
  exact (Theorem5_12_2_distinct n la mu h).false φ


/-- For any simple ℂ[S_n]-module M, some Young symmetrizer acts nontrivially.
This is the key step for the classification: it follows from the fact that
#partitions(n) = #conjugacy_classes(S_n) = #Wedderburn_blocks(ℂ[S_n]),
ensuring that the Specht modules exhaust all Wedderburn blocks. -/
private lemma exists_young_symmetrizer_nontrivial (n : ℕ)
    (M : Type) [AddCommGroup M] [Module (A' n) M]
    [IsSimpleModule (A' n) M] :
    ∃ la : Nat.Partition n, ∃ m : M, YoungSymmetrizer n la • m ≠ 0 := by
  by_contra h
  push_neg at h
  -- h : ∀ la m, YoungSymmetrizer n la • m = 0
  -- Build the Wedderburn decomposition
  let D := IrrepDecomp.mk' (k := ℂ) (G := G' n)
  -- Get the block of M
  set j₀ := blockOf n D M
  -- The Specht modules are simple and have distinct blocks
  have hspecht_simple : ∀ la : Nat.Partition n,
      IsSimpleModule (A' n) (SpechtModule n la) := Theorem5_12_2_irreducible n
  -- The block map β : Part(n) → Fin D.n is injective
  let β : Nat.Partition n → Fin D.n :=
    fun la => @blockOf n D (SpechtModule n la) _ _ (hspecht_simple la)
  have β_inj : Function.Injective β := by
    intro la mu h
    exact blockOf_specht_injective n D la mu (hspecht_simple la) (hspecht_simple mu) h
  -- D.n ≤ |Part(n)| by counting
  have hn_le := irrepDecomp_n_le_card_partition n D
  -- |Part(n)| = D.n (injection β gives ≤, counting gives ≥)
  have hcard_eq : Fintype.card (Nat.Partition n) = Fintype.card (Fin D.n) := by
    apply le_antisymm
    · have := Fintype.card_le_of_injective β β_inj; exact this
    · rwa [Fintype.card_fin]
  -- So β is surjective (injection between types of equal cardinality)
  have β_surj : Function.Surjective β :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard_eq)).mp β_inj
  -- Get λ₀ with block(V_{λ₀}) = j₀
  obtain ⟨la₀, hla₀⟩ := β_surj j₀
  -- The central idempotent e_{j₀} acts as identity on M
  have hM_block := blockOf_spec n D M
  haveI := hspecht_simple la₀
  -- M is isomorphic to V_{la₀} (both simple, same block)
  have hiso : Nonempty (M ≃ₗ[A' n] SpechtModule n la₀) := by
    -- First embed M as a left ideal of A'(n)
    obtain ⟨I, ⟨φ_M⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (A' n) M
    -- I is a simple left ideal, in the same block as M (hence j₀)
    haveI : IsSimpleModule (A' n) I := IsSimpleModule.congr φ_M.symm
    have hI_block : blockOf n D I = j₀ := by
      apply (blockOf_unique n D I j₀ _).symm
      intro l
      have := hM_block (φ_M.symm l)
      rw [← φ_M.symm.map_smul] at this
      exact φ_M.symm.injective this
    -- I and V_{la₀} are in the same block
    have hblock : blockOf n D I = blockOf n D (SpechtModule n la₀) := by
      rw [hI_block]; exact hla₀.symm
    obtain ⟨ψ⟩ := same_block_iso n D I (SpechtModule n la₀) hblock
    exact ⟨φ_M.trans ψ⟩
  obtain ⟨φ⟩ := hiso
  -- Under φ : M ≃ V_{la₀}, the action of c_{la₀} transfers
  set c := YoungSymmetrizer n la₀
  have hc_mem : c ∈ SpechtModule n la₀ := Submodule.subset_span rfl
  have hc_sq_mem : c * c ∈ SpechtModule n la₀ :=
    (SpechtModule n la₀).smul_mem c hc_mem
  have hc_sq_ne : (⟨c * c, hc_sq_mem⟩ : SpechtModule n la₀) ≠ 0 := by
    intro h_eq; exact young_symmetrizer_sq_ne_zero n la₀ (Subtype.ext_iff.mp h_eq)
  -- φ⁻¹(c * c) ≠ 0 (φ is bijective)
  have hpre_ne : φ.symm ⟨c * c, hc_sq_mem⟩ ≠ 0 := by
    intro h_eq; exact hc_sq_ne (φ.symm.injective (by simp [h_eq]))
  -- But c • φ⁻¹(c) = φ⁻¹(c • c) = φ⁻¹(c * c)
  -- And c • φ⁻¹(c) = 0 by assumption h
  have h1 : c • (φ.symm ⟨c, hc_mem⟩) = 0 := h la₀ (φ.symm ⟨c, hc_mem⟩)
  have h2 : φ.symm ⟨c * c, hc_sq_mem⟩ = 0 := by
    rw [show (⟨c * c, hc_sq_mem⟩ : SpechtModule n la₀) = c • ⟨c, hc_mem⟩ from rfl]
    rw [LinearEquiv.map_smul]
    exact h1
  exact hpre_ne h2

/-- The evaluation linear map from a Specht module V_λ to M, sending v to v • m₀.
This is ℂ[S_n]-linear since the action on V_λ ⊆ ℂ[S_n] is left multiplication. -/
private noncomputable def spechtEvalMap (n : ℕ) (la : Nat.Partition n)
    (M : Type) [AddCommGroup M] [Module (A' n) M] (m₀ : M) :
    (SpechtModule n la) →ₗ[A' n] M where
  toFun v := (v : A' n) • m₀
  map_add' v w := by
    change ((v : A' n) + (w : A' n)) • m₀ = (v : A' n) • m₀ + (w : A' n) • m₀
    exact add_smul (v : A' n) (w : A' n) m₀
  map_smul' a v := by
    change (a * (v : A' n)) • m₀ = a • ((v : A' n) • m₀)
    exact mul_smul a (v : A' n) m₀

/-- Every simple left ℂ[S_n]-module is isomorphic to the Specht module V_λ for some
partition λ of n. (Etingof Theorem 5.12.2, part 2b)

The proof strategy: for a simple M, some Young symmetrizer c_λ acts nontrivially
on M. The evaluation map V_λ → M, v ↦ v · m₀, is then a nonzero ℂ[S_n]-linear map
between simple modules. By Schur's lemma, it is an isomorphism. -/
theorem Theorem5_12_2_classification
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (SymGroupAlgebra n) M]
    [IsSimpleModule (SymGroupAlgebra n) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[SymGroupAlgebra n] (SpechtModule n la)) := by
  -- Step 1: Find a partition λ and element m₀ such that c_λ • m₀ ≠ 0
  obtain ⟨la, m₀, hm₀⟩ := exists_young_symmetrizer_nontrivial n M
  -- Step 2: The evaluation map V_λ → M is nonzero (it sends c_λ to c_λ • m₀ ≠ 0)
  set f := spechtEvalMap n la M m₀
  have hf_ne : f ≠ 0 := by
    intro h
    apply hm₀
    have : f ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h) ⟨YoungSymmetrizer n la, Submodule.subset_span rfl⟩
    exact this
  -- Step 3: By Schur's lemma, f is bijective (both domain and codomain are simple)
  haveI : IsSimpleModule (A' n) (SpechtModule n la) := Theorem5_12_2_irreducible n la
  have hf_bij := LinearMap.bijective_of_ne_zero hf_ne
  -- Step 4: Construct the linear equivalence
  exact ⟨la, ⟨(LinearEquiv.ofBijective f hf_bij).symm⟩⟩

end

end Etingof
