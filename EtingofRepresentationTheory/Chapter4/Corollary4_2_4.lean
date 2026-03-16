import Mathlib

/-!
# Corollary 4.2.4: Representations Determined by Characters

If k has characteristic 0, any finite dimensional representation of G is determined
by its character: χ_V = χ_W implies V ≅ W.
-/

open FDRep CategoryTheory CategoryTheory.Limits Module

/-- Equal characters ⟹ equal Hom-space dimensions from any S. -/
private lemma hom_finrank_eq_of_char_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W)
    (S : FDRep ℂ G) :
    finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W) := by
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1 := scalar_product_char_eq_finrank_equivariant S V
  have h2 := scalar_product_char_eq_finrank_equivariant S W
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

/-- Equal characters imply equal dimension. -/
private lemma finrank_eq_of_char_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    finrank ℂ V = finrank ℂ W := by
  have h1 := FDRep.char_one V
  have h2 := FDRep.char_one W
  have h3 := congr_fun h 1
  exact_mod_cast h1.symm.trans (h3.trans h2)

/-- In a preadditive k-linear category, Hom into a biproduct decomposes as a product. -/
private noncomputable def homBiprodLinearEquiv
    {G : Type} [Group G] [Fintype G]
    (T X Y : FDRep ℂ G) [HasBinaryBiproduct X Y] :
    (T ⟶ X ⊞ Y) ≃ₗ[ℂ] (T ⟶ X) × (T ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  map_add' f g := by simp
  map_smul' r f := by simp
  invFun p := biprod.lift p.1 p.2
  left_inv f := by
    dsimp
    rw [biprod.lift_eq]
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, biprod.total, Category.comp_id]
  right_inv p := by simp

private lemma finrank_hom_biprod_eq
    {G : Type} [Group G] [Fintype G]
    (T X Y : FDRep ℂ G) [HasBinaryBiproduct X Y] :
    finrank ℂ (T ⟶ X ⊞ Y) = finrank ℂ (T ⟶ X) + finrank ℂ (T ⟶ Y) := by
  rw [← finrank_prod]
  exact LinearEquiv.finrank_eq (homBiprodLinearEquiv T X Y)

/-- In FDRep ℂ G, Hom dimensions are preserved by isomorphism in the target. -/
private lemma finrank_hom_iso
    {G : Type} [Group G] [Fintype G]
    (T V W : FDRep ℂ G) (φ : V ≅ W) :
    finrank ℂ (T ⟶ V) = finrank ℂ (T ⟶ W) :=
  LinearEquiv.finrank_eq
    { toFun := fun f => f ≫ φ.hom
      map_add' := fun f g => by simp
      map_smul' := fun r f => by simp
      invFun := fun f => f ≫ φ.inv
      left_inv := fun f => by simp
      right_inv := fun f => by simp }

/-- finrank is preserved by FDRep isomorphisms. -/
private lemma finrank_iso
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G) (φ : V ≅ W) :
    finrank ℂ V = finrank ℂ W :=
  LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv φ)

/-- finrank of a biproduct in FDRep equals the sum of finranks. -/
private lemma finrank_biprod
    {G : Type} [Group G] [Fintype G]
    (X Y : FDRep ℂ G) [HasBinaryBiproduct X Y] :
    finrank ℂ (X ⊞ Y : FDRep ℂ G) = finrank ℂ X + finrank ℂ Y := by
  rw [← finrank_prod]
  apply LinearEquiv.finrank_eq
  refine {
    toFun := fun v => ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
                        (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
    map_add' := fun a b => by simp [map_add]
    map_smul' := fun r a => by simp [map_smul]
    invFun := fun p => (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
                        (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
    left_inv := fun v => by
      show ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
        (X ⊞ Y : FDRep ℂ G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
      rw [biprod.total]; rfl
    right_inv := fun p => by
      have hzero : ∀ (A B : FDRep ℂ G) (x : A.V), (0 : A ⟶ B).hom.hom.hom x = 0 := by
        intro A B x
        show (0 : A.V.obj ⟶ B.V.obj).hom x = 0
        simp [ModuleCat.Hom.hom]
        exact LinearMap.zero_apply x
      have hid : ∀ (A : FDRep ℂ G) (x : A.V), (𝟙 A : A ⟶ A).hom.hom.hom x = x := fun _ _ => rfl
      ext <;> dsimp only
      · change ((biprod.fst : X ⊞ Y ⟶ X)).hom.hom.hom
            ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
             (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.1
        rw [map_add]
        show ((biprod.inl ≫ biprod.fst : X ⟶ X)).hom.hom.hom p.1 +
             ((biprod.inr ≫ biprod.fst : Y ⟶ X)).hom.hom.hom p.2 = p.1
        rw [biprod.inl_fst, biprod.inr_fst, hid, hzero, add_zero]
      · change ((biprod.snd : X ⊞ Y ⟶ Y)).hom.hom.hom
            ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
             (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.2
        rw [map_add]
        show ((biprod.inl ≫ biprod.snd : X ⟶ Y)).hom.hom.hom p.1 +
             ((biprod.inr ≫ biprod.snd : Y ⟶ Y)).hom.hom.hom p.2 = p.2
        rw [biprod.inl_snd, biprod.inr_snd, hzero, hid, zero_add] }

/-- Zero case: if V is zero and all Hom dimensions match, then W is also zero. -/
private lemma iso_of_hom_finrank_eq_zero
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (hV0 : IsZero V)
    (h : ∀ S : FDRep ℂ G, finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) :
    Nonempty (V ≅ W) := by
  have hWV : Subsingleton (W ⟶ V) := ⟨fun f g => hV0.eq_of_tgt f g⟩
  have h1 : finrank ℂ (W ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  have h2 : finrank ℂ (W ⟶ W) = 0 := by rw [← h W]; exact h1
  have hWW : Subsingleton (W ⟶ W) := Module.finrank_zero_iff.mp h2
  have hW : IsZero W := by
    rw [IsZero.iff_id_eq_zero]
    exact Subsingleton.eq_zero _
  exact ⟨hV0.iso hW⟩

/-- Simple FDRep objects have positive finrank. -/
private lemma finrank_pos_of_simple
    {G : Type} [Group G] [Fintype G]
    (S : FDRep ℂ G) [Simple S] : 0 < finrank ℂ S := by
  by_contra h
  push_neg at h
  have h0 : finrank ℂ S = 0 := Nat.eq_zero_of_le_zero h
  have hSS : finrank ℂ (S ⟶ S) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]; simp
  have hsub : Subsingleton S := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (S ⟶ S) := by
    constructor; intro f g
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have : finrank ℂ (S ⟶ S) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- In FDRep ℂ G (semisimple by Maschke), any nonzero morphism from a simple object
is mono and splits: if f : S ⟶ W is nonzero with S simple, then W ≅ S ⊞ W'. -/
private lemma biprod_of_nonzero_from_simple
    {G : Type} [Group G] [Fintype G]
    (S W : FDRep ℂ G) [Simple S] (f : S ⟶ W) (hf : f ≠ 0) :
    ∃ (W' : FDRep ℂ G), Nonempty (W ≅ S ⊞ W') := by
  -- f is mono since S is simple and f ≠ 0
  haveI : Mono f := mono_of_nonzero_from_simple hf
  -- S is Injective by Maschke's theorem, so f is a split mono
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Injective S := inferInstance
  haveI : IsSplitMono f := IsSplitMono.mk' ⟨Injective.factorThru (𝟙 S) f, Injective.comp_factorThru (𝟙 S) f⟩
  -- FDRep is abelian, so f has a cokernel
  have hcok := cokernelIsCokernel f
  -- Build biproduct from split mono + cokernel
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct S (cokernel f) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  exact ⟨cokernel f, ⟨biprod.uniqueUpToIso S (cokernel f) hbl⟩⟩

/-- A split mono in FDRep gives a biproduct decomposition with the cokernel. -/
private lemma biprod_of_split_mono
    {G : Type} [Group G] [Fintype G]
    (Y V : FDRep ℂ G) (f : Y ⟶ V) [Mono f] [IsSplitMono f] :
    Nonempty (V ≅ Y ⊞ cokernel f) := by
  have hcok := cokernelIsCokernel f
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct Y (cokernel f) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  exact ⟨biprod.uniqueUpToIso Y (cokernel f) hbl⟩

/-- In FDRep ℂ G (semisimple by Maschke), any nonzero object has a simple direct summand. -/
private lemma exists_simple_biprod
    {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (hV : ¬IsZero V) :
    ∃ (S V' : FDRep ℂ G), Simple S ∧ Nonempty (V ≅ S ⊞ V') := by
  -- Helper: zero finrank implies IsZero
  have isZero_of_finrank_zero : ∀ (W : FDRep ℂ G), finrank ℂ W = 0 → IsZero W := by
    intro W h0; rw [IsZero.iff_id_eq_zero]
    have hsub : Subsingleton W := Module.finrank_zero_iff.mp h0
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- Strong induction on finrank
  suffices key : ∀ (n : ℕ) (V : FDRep ℂ G), ¬IsZero V → finrank ℂ V ≤ n →
      ∃ (S V' : FDRep ℂ G), Simple S ∧ Nonempty (V ≅ S ⊞ V') from
    key _ V hV le_rfl
  intro n
  induction n with
  | zero =>
    intro V hV hfr
    exact absurd (isZero_of_finrank_zero V (Nat.eq_zero_of_le_zero hfr)) hV
  | succ n ih =>
    intro V hV hfr
    by_cases hS : Simple V
    · -- V is simple: use biprod_of_nonzero_from_simple with 𝟙 V
      haveI := hS
      have hid : (𝟙 V : V ⟶ V) ≠ 0 := by
        intro h; apply hV; rwa [IsZero.iff_id_eq_zero]
      obtain ⟨V', ⟨φ⟩⟩ := biprod_of_nonzero_from_simple V V (𝟙 V) hid
      exact ⟨V, V', hS, ⟨φ⟩⟩
    · -- V is not simple: extract a nonzero non-iso mono
      have h_exists : ∃ (Y : FDRep ℂ G) (f : Y ⟶ V), Mono f ∧ f ≠ 0 ∧ ¬IsIso f := by
        by_contra h_all
        apply hS
        refine ⟨fun {Y} f _ => ⟨?_, ?_⟩⟩
        · -- IsIso f → f ≠ 0
          intro hi habs
          haveI := hi
          apply hV; rw [IsZero.iff_id_eq_zero]
          have key := IsIso.inv_hom_id (f := f)
          simp only [habs, comp_zero] at key
          exact key.symm
        · -- f ≠ 0 → IsIso f
          intro hne
          by_contra hni
          exact h_all ⟨Y, f, ‹Mono f›, hne, hni⟩
      obtain ⟨Y, f, hfm, hfne, hfni⟩ := h_exists
      haveI := hfm
      -- Y is Injective (Maschke), so f is a split mono
      haveI : IsSplitMono f :=
        IsSplitMono.mk' ⟨Injective.factorThru (𝟙 Y) f, Injective.comp_factorThru (𝟙 Y) f⟩
      -- V ≅ Y ⊞ cokernel f
      obtain ⟨iso_V⟩ := biprod_of_split_mono Y V f
      -- Y is nonzero
      have hY : ¬IsZero Y := fun hY0 => hfne (hY0.eq_of_src f 0)
      -- cokernel f is nonzero (otherwise f is epi, mono+epi → iso in abelian category)
      have hcok_nz : ¬IsZero (cokernel f : FDRep ℂ G) := by
        intro hcok0
        haveI : Epi f := (Preadditive.epi_iff_isZero_cokernel f).mpr hcok0
        exact hfni (isIso_of_mono_of_epi f)
      -- finrank Y ≤ n
      have hfr_eq : finrank ℂ V = finrank ℂ Y + finrank ℂ (cokernel f : FDRep ℂ G) :=
        by rw [finrank_iso V (Y ⊞ cokernel f) iso_V, finrank_biprod]
      have hcok_pos : 0 < finrank ℂ (cokernel f : FDRep ℂ G) := by
        by_contra h; push_neg at h
        exact hcok_nz (isZero_of_finrank_zero _ (Nat.eq_zero_of_le_zero h))
      have hY_le : finrank ℂ Y ≤ n := by omega
      -- By induction, Y has a simple summand
      obtain ⟨S, Y', hSS, ⟨ψ⟩⟩ := ih Y hY hY_le
      -- V ≅ Y ⊞ cok ≅ (S ⊞ Y') ⊞ cok ≅ S ⊞ (Y' ⊞ cok)
      exact ⟨S, Y' ⊞ cokernel f, hSS,
        ⟨iso_V.trans ((biprod.mapIso ψ (Iso.refl _)).trans
          (biprod.associator S Y' (cokernel f)))⟩⟩

/-- In a semisimple category (FDRep ℂ G), objects with equal Hom-space dimensions
from every object are isomorphic. This is the categorical core: it uses semisimplicity
(Maschke) and Schur's lemma to match simple constituents. -/
private lemma iso_of_hom_finrank_eq
    {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (h : ∀ S : FDRep ℂ G, finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) :
    Nonempty (V ≅ W) := by
  -- Strong induction on finrank ℂ V.
  suffices key : ∀ (n : ℕ) (V W : FDRep ℂ G),
      finrank ℂ V ≤ n →
      (∀ S : FDRep ℂ G, finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) →
      Nonempty (V ≅ W) from
    key _ V W le_rfl h
  intro n
  induction n with
  | zero =>
    intro V W hVn h
    by_cases hV : IsZero V
    · exact iso_of_hom_finrank_eq_zero V W hV h
    · obtain ⟨S, V', hS, ⟨φ⟩⟩ := exists_simple_biprod V hV
      haveI := hS
      have : finrank ℂ V = 0 := Nat.eq_zero_of_le_zero hVn
      have : 0 < finrank ℂ S := finrank_pos_of_simple S
      have : finrank ℂ S ≤ finrank ℂ V := by
        rw [finrank_iso V (S ⊞ V') φ, finrank_biprod]
        omega
      omega
  | succ n ih =>
    intro V W hVn h
    by_cases hV : IsZero V
    · exact iso_of_hom_finrank_eq_zero V W hV h
    · obtain ⟨S, V', hS, ⟨φ⟩⟩ := exists_simple_biprod V hV
      haveI : Simple S := hS
      have hV_decomp : ∀ T, finrank ℂ (T ⟶ V) = finrank ℂ (T ⟶ S) + finrank ℂ (T ⟶ V') := by
        intro T
        rw [finrank_hom_iso T V (S ⊞ V') φ, finrank_hom_biprod_eq]
      have hSS : finrank ℂ (S ⟶ S) = 1 := by
        rw [FDRep.finrank_hom_simple_simple]; simp
      have hSV_pos : 0 < finrank ℂ (S ⟶ V) := by
        rw [hV_decomp S]; omega
      have hSW_pos : 0 < finrank ℂ (S ⟶ W) := by rw [← h S]; exact hSV_pos
      have : Nontrivial (S ⟶ W) := by
        rw [nontrivial_iff]
        exact (finrank_pos_iff.mp hSW_pos).exists_pair_ne
      obtain ⟨f, hf⟩ := exists_ne (0 : S ⟶ W)
      obtain ⟨W', ⟨ψ⟩⟩ := biprod_of_nonzero_from_simple S W f hf
      have hW_decomp : ∀ T, finrank ℂ (T ⟶ W) = finrank ℂ (T ⟶ S) + finrank ℂ (T ⟶ W') := by
        intro T
        rw [finrank_hom_iso T W (S ⊞ W') ψ, finrank_hom_biprod_eq]
      have hV'W' : ∀ T, finrank ℂ (T ⟶ V') = finrank ℂ (T ⟶ W') := by
        intro T
        have hv := hV_decomp T
        have hw := hW_decomp T
        have := h T
        omega
      have hV'_le : finrank ℂ V' ≤ n := by
        have hfr : finrank ℂ V = finrank ℂ S + finrank ℂ V' := by
          rw [finrank_iso V (S ⊞ V') φ, finrank_biprod]
        have hS_pos : 0 < finrank ℂ S := finrank_pos_of_simple S
        omega
      obtain ⟨θ⟩ := ih V' W' hV'_le hV'W'
      exact ⟨φ.trans ((biprod.mapIso (Iso.refl S) θ).trans ψ.symm)⟩

/-- In characteristic 0, representations are determined by their characters.
(Etingof Corollary 4.2.4) -/
theorem Etingof.Corollary4_2_4
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    Nonempty (V ≅ W) :=
  iso_of_hom_finrank_eq V W (hom_finrank_eq_of_char_eq V W h)
