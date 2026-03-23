import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues
import EtingofRepresentationTheory.Chapter5.GL2NormalizerInfra

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)


/-- Character orthogonality for finite groups: the sum of a nontrivial
character over all group elements is zero. Applied to ν^{q-1} on F_{q²}×. -/
private lemma Etingof.sum_nontrivial_char_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  -- Standard character orthogonality: ∑_g χ(g) = 0 for nontrivial χ
  -- Choose g₀ with χ(g₀) ≠ 1
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push_neg at h; exact absurd (MonoidHom.ext h) hχ
  -- χ(g₀) * ∑ g, χ(g) = ∑ g, χ(g₀ * g) = ∑ g, χ(g) (by reindexing)
  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h; apply hg₀; exact Units.val_injective h
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
  -- (χ(g₀) - 1) * ∑ χ = 0, with χ(g₀) ≠ 1
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

open Classical in
/-- On elliptic elements, the complementary series character simplifies to
just the negated induced character: χ(g) = -(|K|⁻¹ ∑ x, ν(x⁻¹gx)).
This is because charW₁(g) = -1 and charVα₁(g) = 0 for elliptic g,
so χ(g) = (-1)·0 - 0 - Ind = -Ind. -/
private lemma Etingof.complementarySeriesChar_elliptic_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g =
    -((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) := by
  unfold Etingof.GL2.complementarySeriesChar
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  have hW : Etingof.GL2.charW₁ p n g = -1 := Etingof.charW₁_elliptic p n g hg
  have hV : Etingof.GL2.charVα₁ p n alpha g = 0 := Etingof.charVα₁_elliptic p n alpha g hg
  rw [hW, hV]
  ring

/-- The elliptic subgroup K = 𝔽_{q²}× is commutative, since it is
the image of the multiplicative group of a field under a group homomorphism. -/
private noncomputable instance Etingof.ellipticSubgroup_commGroup :
    CommGroup ↥(Etingof.GL2.ellipticSubgroup p n) :=
  { (inferInstance : Group ↥(Etingof.GL2.ellipticSubgroup p n)) with
    mul_comm := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      ext
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      simp only [Subgroup.coe_mul, ← map_mul, mul_comm a' b'] }

/-- The (q-1)-power character k ↦ ν(k)^{q-1} on K = 𝔽_{q²}×. -/
private noncomputable def Etingof.qm1_char
    [Fintype (GaloisField p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ :=
  (powMonoidHom (Fintype.card (GaloisField p n) - 1)).comp nu

/-- If ν^q ≠ ν, then ν^{q-1} ≠ 1 as a character on K. -/
private lemma Etingof.qm1_char_nontrivial
    [Fintype (GaloisField p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    Etingof.qm1_char p n nu ≠ 1 := by
  obtain ⟨k, hk⟩ := hnu_ne
  intro h
  apply hk
  have := congr_fun (congr_arg DFunLike.coe h) k
  simp only [qm1_char, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
    MonoidHom.one_apply] at this
  -- this : ν(k)^{q-1} = 1, need to show ν(k)^q = ν(k)
  have hq_pos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  rw [show Fintype.card (GaloisField p n) = Fintype.card (GaloisField p n) - 1 + 1
    from by omega, pow_succ, this, one_mul]

/-- On scalar elements of K (i.e., F_q× ⊂ K), ν^{q-1} = 1. -/
private lemma Etingof.qm1_char_on_scalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (nu : ↥(Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (hn : n ≠ 0)
    (a : (GaloisField p n)ˣ) :
    Etingof.qm1_char p n nu (Etingof.GL2.scalarToElliptic p n a) = 1 := by
  simp only [qm1_char, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
  -- Need: ν(scalarToElliptic(a))^{q-1} = 1
  -- scalarToElliptic(a) has order dividing q-1 (since F_q× has order q-1)
  -- so ν(scalarToElliptic(a)) has order dividing q-1
  -- hence ν(scalarToElliptic(a))^{q-1} = 1
  have : (Etingof.GL2.scalarToElliptic p n a) ^ (Fintype.card (GaloisField p n) - 1) = 1 := by
    have hord : orderOf a ∣ Fintype.card (GaloisField p n) - 1 := by
      rw [← Fintype.card_units]
      exact orderOf_dvd_card
    have := map_pow (Etingof.GL2.scalarToElliptic p n) a (Fintype.card (GaloisField p n) - 1)
    rw [← this]
    have ha_pow : a ^ (Fintype.card (GaloisField p n) - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hord
    rw [ha_pow, map_one]
  rw [← map_pow, this, map_one]

/-- For k ∈ K and ¬IsElliptic k, the element is scalar (not parabolic or split semisimple).
In char ≠ 2, elements of K = 𝔽_{q²}× have disc = 0 (scalar) or non-square disc (elliptic).
So ¬IsElliptic forces disc = 0, which combined with K not containing parabolic elements
(by `parabolic_conj_not_in_ellipticSubgroup`) gives IsScalar. -/
private lemma Etingof.ellipticSubgroup_not_elliptic_isScalar
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n)
    (hne : ¬GL2.IsElliptic (p := p) (n := n) k) :
    GL2.IsScalar (p := p) (n := n) k := by
  -- k ∈ K implies disc(k) = 0 ∨ ¬IsSquare(disc(k))
  have hK := Etingof.ellipticSubgroup_disc p n hp2 k hk
  -- ¬IsElliptic means IsSquare(disc(k))
  have hIsSquare : IsSquare (GL2.disc k) := by
    simp only [GL2.IsElliptic, not_not] at hne; exact hne
  -- Combined: disc(k) = 0
  have hdisc_zero : GL2.disc k = 0 := by
    rcases hK with h | h
    · exact h
    · exact absurd hIsSquare h
  -- disc = 0 means IsScalar or IsParabolic
  rcases GL2.conjugacyClass_exhaustive k with hs | hp | hss | he
  · exact hs
  · -- Parabolic: impossible, since parabolic elements aren't in K
    have h_para := Etingof.parabolic_conj_not_in_ellipticSubgroup p n k hp 1
    simp only [inv_one, one_mul, mul_one] at h_para
    exact absurd hk h_para
  · -- SplitSemisimple: disc ≠ 0, contradiction
    exact absurd hdisc_zero hss.1
  · -- Elliptic: contradicts hne
    exact absurd he hne

-- The character orthogonality sum over non-scalar K elements.
-- ∑_K ψ = conj(∑_K ν^{q-1}) = conj(0) = 0 (nontrivial character)
-- ψ = 1 on F_q× (ν^{q-1} = 1 on scalars)
-- ∑_{K \ F_q×} (1+ψ) = (q²-1) - 2(q-1) = (q-1)²
open Classical in
private lemma Etingof.nonscalar_char_sum
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)
       else 0) =
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
  -- Strategy: ∑_{K_ns} f = ∑_K f - ∑_{K_scalar} f
  -- ∑_K f = |K| (using character orthogonality)
  -- ∑_{K_scalar} f = 2·|F_q×| (each scalar contributes 2)
  -- Result: (q²-1) - 2(q-1) = (q-1)²
  -- Step 1: ∑_K (1+ψ) = |K|
  set ψ : ↥(Etingof.GL2.ellipticSubgroup p n) → ℂ :=
    fun k => starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ) with hψ_def
  -- conj(∑_K qm1_char) = conj(0) = 0
  have h_conj_sum_zero : ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n), ψ k = 0 := by
    rw [hψ_def]
    rw [show (∑ k, starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)) =
      starRingEnd ℂ (∑ k, ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)) from
        (map_sum (starRingEnd ℂ) _ _).symm]
    rw [Etingof.sum_nontrivial_char_eq_zero (Etingof.qm1_char p n nu)
      (Etingof.qm1_char_nontrivial p n nu hnu_ne), map_zero]
  have h_full_sum : ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n), ((1 : ℂ) + ψ k) =
      (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      h_conj_sum_zero, add_zero]
  -- Step 2: Decompose into elliptic + non-elliptic
  have hdecomp : ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + ψ k else 0) =
      ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n), ((1 : ℂ) + ψ k) -
      ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
        (if ¬GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
         then (1 : ℂ) + ψ k else 0) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext k; split_ifs with h <;> simp
  -- Step 3: Non-elliptic K elements are scalar, ψ = 1, so each contributes 2
  have h_scalar_psi_one : ∀ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      ¬GL2.IsElliptic (p := p) (n := n) (k : GL2 p n) → ψ k = 1 := by
    intro k hne
    have hscalar := Etingof.ellipticSubgroup_not_elliptic_isScalar p n hp2 hn
      (k : GL2 p n) k.2 hne
    -- k₀₀ ≠ 0 (k is invertible, det = k₀₀² since off-diagonals are 0)
    have hk00_ne : (k : GL2 p n).val 0 0 ≠ 0 := by
      obtain ⟨h01, h10, h00_eq⟩ := hscalar
      -- h01, h10, h00_eq use private GL2.mat which is defeq to .val
      intro h0
      have h01' : (k : GL2 p n).val 0 1 = 0 := h01
      have h10' : (k : GL2 p n).val 1 0 = 0 := h10
      have h00_eq' : (k : GL2 p n).val 0 0 = (k : GL2 p n).val 1 1 := h00_eq
      have h11 : (k : GL2 p n).val 1 1 = 0 := by rw [← h00_eq']; exact h0
      have hdet_zero : Matrix.det (k : GL2 p n).val = 0 := by
        rw [Matrix.det_fin_two]; simp [h01', h10', h0, h11]
      have hdet_unit := (k : GL2 p n).isUnit
      rw [Matrix.isUnit_iff_isUnit_det] at hdet_unit
      exact not_isUnit_zero (hdet_zero ▸ hdet_unit)
    set a := Units.mk0 ((k : GL2 p n).val 0 0) hk00_ne
    -- k = scalarToElliptic(a) as elements of K
    have hk_eq : k = Etingof.GL2.scalarToElliptic p n a := by
      apply Subtype.ext
      letI := Etingof.algebraGaloisFieldExt p n
      unfold GL2.scalarToElliptic
      simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
      exact Etingof.scalar_eq_fieldExtEmbed p n hn (k : GL2 p n) hscalar hk00_ne
    -- ψ(k) = ψ(scalarToElliptic(a)) = conj(qm1_char(scalarToElliptic(a)))
    -- = conj(1) = 1
    show ψ k = 1
    have hqm1 : (Etingof.qm1_char p n nu (Etingof.GL2.scalarToElliptic p n a) : ℂˣ) =
      (1 : ℂˣ) := Etingof.qm1_char_on_scalar p n nu hn a
    simp only [hψ_def, hk_eq, hqm1, Units.val_one, map_one]
  -- Step 4: Non-elliptic sum = 2 · |{k ∈ K : ¬IsElliptic k}|
  have h_scalar_sum : ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (if ¬GL2.IsElliptic (p := p) (n := n) (k : GL2 p n) then (1 : ℂ) + ψ k else 0) =
      2 * (Fintype.card (GaloisField p n) - 1 : ℂ) := by
    -- Each non-elliptic k contributes (1 + 1) = 2
    have hval : ∀ k : ↥(Etingof.GL2.ellipticSubgroup p n),
        ¬GL2.IsElliptic (p := p) (n := n) (k : GL2 p n) →
        (1 : ℂ) + ψ k = 2 := by
      intro k hne; rw [h_scalar_psi_one k hne]; norm_num
    -- Each non-elliptic contributes 2, elliptic contributes 0
    -- So sum = 2 * |{k ∈ K : ¬IsElliptic k}| = 2 * (q - 1)
    -- since non-elliptic K elements ↔ F_q× (scalar matrices)
    -- Step A: Replace each term with 2 or 0
    have h_ite_eq : ∀ k' : ↥(Etingof.GL2.ellipticSubgroup p n),
        (if ¬GL2.IsElliptic (p := p) (n := n) (k' : GL2 p n) then (1 : ℂ) + ψ k' else 0) =
        if ¬GL2.IsElliptic (p := p) (n := n) (k' : GL2 p n) then (2 : ℂ) else 0 := by
      intro k'; split_ifs with h
      · rfl
      · exact hval k' h
    simp_rw [h_ite_eq]
    -- Step B: Convert sum to 2 * card
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    -- Step C: Card of non-elliptic K elements = q - 1
    letI := Etingof.algebraGaloisFieldExt p n
    set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    -- Matrix entry: scalarToElliptic(a) i j = if i = j then a else 0
    have h_entry : ∀ (a : (GaloisField p n)ˣ) (i j : Fin 2),
        ((Etingof.GL2.scalarToElliptic p n a :
          ↥(Etingof.GL2.ellipticSubgroup p n)) : GL2 p n).val i j =
        if i = j then (a : GaloisField p n) else 0 := by
      intro a i j
      unfold GL2.scalarToElliptic GL2.fieldExtEmbed
      simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
      show (Algebra.leftMulMatrix b
        ((algebraMap (GaloisField p n) (GaloisField p (2 * n))) (a : GaloisField p n))) i j = _
      rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, map_smul, Finsupp.smul_apply, smul_eq_mul,
          b.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
      simp only [eq_comm]
    -- scalarToElliptic(a) is not elliptic (it's scalar)
    have h_ste_not_ell : ∀ a : (GaloisField p n)ˣ,
        ¬GL2.IsElliptic (p := p) (n := n)
          ((Etingof.GL2.scalarToElliptic p n a :
            ↥(Etingof.GL2.ellipticSubgroup p n)) : GL2 p n) :=
      fun a => GL2.isScalar_not_isElliptic _
        ((GL2.isScalar_iff _).mpr ⟨by simp [h_entry], by simp [h_entry], by simp [h_entry]⟩)
    -- scalarToElliptic is injective
    have h_ste_inj : Function.Injective (Etingof.GL2.scalarToElliptic p n) := by
      intro a₁ a₂ h
      have h₀ := h_entry a₁ 0 0; simp only [ite_true] at h₀
      have h₁ := h_entry a₂ 0 0; simp only [ite_true] at h₁
      have : (a₁ : GaloisField p n) = (a₂ : GaloisField p n) := by
        have := congr_arg (fun k : ↥(Etingof.GL2.ellipticSubgroup p n) =>
          (k : GL2 p n).val 0 0) h
        simp only [h₀, h₁] at this; exact this
      exact Units.ext this
    -- Card of non-elliptic filter = q - 1 via bijection with F_q×
    have h_card : (Finset.univ.filter (fun k : ↥(Etingof.GL2.ellipticSubgroup p n) =>
        ¬GL2.IsElliptic (p := p) (n := n) (k : GL2 p n))).card =
        Fintype.card (GaloisField p n) - 1 := by
      rw [← Fintype.card_units, ← Finset.card_univ (α := (GaloisField p n)ˣ)]
      symm
      apply Finset.card_nbij (Etingof.GL2.scalarToElliptic p n)
      · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_ste_not_ell a⟩
      · intro a₁ _ a₂ _ h; exact h_ste_inj h
      · intro k hk
        rw [Finset.mem_coe, Finset.mem_filter] at hk
        have hscalar := Etingof.ellipticSubgroup_not_elliptic_isScalar p n hp2 hn
          (k : GL2 p n) k.2 hk.2
        have hk00_ne : (k : GL2 p n).val 0 0 ≠ 0 := by
          obtain ⟨h01, h10, _⟩ := (GL2.isScalar_iff _).mp hscalar
          intro h0
          have : Matrix.det (k : GL2 p n).val = 0 := by
            rw [Matrix.det_fin_two]; simp [h01, h10, h0]
          exact (Matrix.isUnits_det_units (k : GL2 p n)).ne_zero this
        refine ⟨Units.mk0 _ hk00_ne, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        apply Subtype.ext
        unfold GL2.scalarToElliptic
        simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
        exact (Etingof.scalar_eq_fieldExtEmbed p n hn _ hscalar hk00_ne).symm
    rw [h_card]; push_cast [Nat.cast_sub Fintype.card_pos]; ring
  -- Step 5: Combine
  rw [hdecomp, h_full_sum, h_scalar_sum]
  -- |K| - 2(q-1) = (q-1)²  where |K| = q² - 1
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq_pos : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact Nat.one_lt_pow hn hp.out.one_lt
  have hinj : Function.Injective (Etingof.GL2.fieldExtEmbed p n) := by
    intro a b hab
    unfold GL2.fieldExtEmbed at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  have hKc_units : Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) =
      Fintype.card (GaloisField p (2 * n))ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(Etingof.GL2.fieldExtEmbed p n).range = _
    exact Nat.card_congr ((Etingof.GL2.fieldExtEmbed p n).ofInjective hinj).symm.toEquiv
  have hq_pn : q = p ^ n := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  have hKc_nat : Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) = q ^ 2 - 1 := by
    rw [hKc_units, Fintype.card_units,
      ← Nat.card_eq_fintype_card,
      GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
    congr 1
    rw [hq_pn, show 2 * n = n * 2 from by ring, pow_mul]
  have h1 : 1 ≤ q ^ 2 := by nlinarith
  have hKc_C : (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) =
      (q : ℂ) ^ 2 - 1 := by
    rw [hKc_nat]; push_cast [Nat.cast_sub h1]; ring
  rw [hKc_C]; ring

-- For non-scalar k ∈ K, the normalizer character sum evaluates to |K|·(1 + conj(ψ(k))).
-- Proof: {z : z⁻¹kz ∈ K} = N(K) = K ∪ σK. On K: ν(k)·conj(ν(k)) = 1 (norm).
-- On σK: ν(k)·conj(ν(k^q)) = conj(ψ(k)). Rest contributes 0.
open Classical in
private lemma Etingof.normalizer_char_eval
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (k : ↥(Etingof.GL2.ellipticSubgroup p n))
    (hk_ell : GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)) :
    ∑ z : GL2 p n,
      (if h : z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
       else 0) =
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
    ((1 : ℂ) + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)) := by
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  -- k is non-scalar (elliptic ⟹ non-scalar)
  have hk_ns : ¬GL2.IsScalar (p := p) (n := n) (k : GL2 p n) :=
    fun hs => GL2.isScalar_not_isElliptic (k : GL2 p n) hs hk_ell
  -- Get field element underlying k
  obtain ⟨β, hβ⟩ := k.2
  -- Define the three filter sets
  set N := Finset.univ.filter (fun z : GL2 p n => Etingof.GL2.isInNormalizer p n z)
  set K_set := Finset.univ.filter (fun z : GL2 p n =>
    z ∈ Etingof.GL2.ellipticSubgroup p n) with hK_set_def
  set σK_set := Finset.univ.filter (fun z : GL2 p n =>
    ∃ α : (GaloisField p (2 * n))ˣ,
      z = Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α) with hσK_set_def
  -- The summand
  set F : GL2 p n → ℂ := fun z =>
    if h : z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n
    then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
    else 0 with hF_def
  -- Step 1: Terms outside N(K) vanish
  have h_vanish : ∀ z : GL2 p n, ¬Etingof.GL2.isInNormalizer p n z → F z = 0 := by
    intro z hz; simp only [F, hF_def]
    rw [dif_neg]; intro h
    exact hz (Etingof.GL2.conj_mem_implies_normalizer p n hn hp2
      (k : GL2 p n) k.2 hk_ns z h)
  -- Step 2: Restrict sum to normalizer
  have h_restrict : ∑ z, F z = ∑ z ∈ N, F z := by
    symm; apply Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _)
    · intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_filter] at hz
      exact h_vanish z hz
    · intro z _; rfl
  -- Step 3: N(K) = K ∪ σK (from normalizer_mem_dichotomy)
  have hN_eq : N = K_set ∪ σK_set := by
    ext z
    simp only [N, K_set, σK_set, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · exact Etingof.GL2.normalizer_mem_dichotomy p n hn hp2 z
    · rintro (hk | ⟨α, hα⟩)
      · exact Etingof.GL2.ellipticSubgroup_mem_normalizer p n z hk
      · subst hα
        exact Etingof.GL2.normalizer_contains_frobeniusCoset p n hn _ ⟨α, rfl⟩
  -- Step 4: K and σK are disjoint
  have hKσK_disj : Disjoint K_set σK_set := by
    rw [Finset.disjoint_filter]
    intro z _ hz_K ⟨α, hα⟩
    have : Etingof.GL2.frobeniusMatrix p n ∈ Etingof.GL2.ellipticSubgroup p n := by
      obtain ⟨γ, hγ⟩ := hz_K
      rw [hα] at hγ
      have : Etingof.GL2.frobeniusMatrix p n =
          Etingof.GL2.fieldExtEmbed p n γ * (Etingof.GL2.fieldExtEmbed p n α)⁻¹ := by
        rw [hγ]; group
      rw [this]; exact ⟨γ * α⁻¹, by rw [map_mul, map_inv]⟩
    exact Etingof.GL2.frobeniusMatrix_not_in_elliptic p n hn this
  -- Step 5: Split the sum
  rw [h_restrict, hN_eq, Finset.sum_union hKσK_disj]
  -- Step 6: Evaluate K-part
  -- For z ∈ K: z⁻¹kz = k (K abelian), so F(z) = ν(k)*conj(ν(k)) = 1
  have hK_eval : ∑ z ∈ K_set, F z =
      (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) := by
    -- For z ∈ K: z⁻¹kz = k (K is abelian), so F(z) = ν(k)*conj(ν(k)) = 1
    have hK_conj : ∀ z : GL2 p n, z ∈ Etingof.GL2.ellipticSubgroup p n →
        z⁻¹ * (k : GL2 p n) * z = (k : GL2 p n) := by
      intro z hz
      obtain ⟨α, rfl⟩ := hz
      obtain ⟨γ, hγ⟩ := k.2
      change (Etingof.GL2.fieldExtEmbed p n α)⁻¹ * (k : GL2 p n) *
        Etingof.GL2.fieldExtEmbed p n α = (k : GL2 p n)
      rw [show (k : GL2 p n) = Etingof.GL2.fieldExtEmbed p n γ from hγ.symm]
      simp only [← map_inv, ← map_mul, inv_mul_cancel_comm]
    have hK_mem : ∀ z : GL2 p n, z ∈ Etingof.GL2.ellipticSubgroup p n →
        z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n := by
      intro z hz; rw [hK_conj z hz]; exact k.2
    -- Each term = ν(k)*conj(ν(k)) = 1
    have hterm : ∀ z ∈ K_set, F z = 1 := by
      intro z hz
      simp only [K_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [F, dif_pos (hK_mem z hz)]
      have : (⟨z⁻¹ * (k : GL2 p n) * z, hK_mem z hz⟩ :
          ↥(Etingof.GL2.ellipticSubgroup p n)) = k := by
        exact Subtype.ext (hK_conj z hz)
      rw [this]
      exact Etingof.normSq_monoidHom_val_eq_one nu k
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- |K_set| = |K|
    simp only [K_set, ← Fintype.card_subtype]
  -- Step 7: Evaluate σK-part
  -- For z = σ·α: z⁻¹kz = k^q (Frobenius), so F(z) = ν(k)*conj(ν(k^q)) = conj(ψ(k))
  have hσK_eval : ∑ z ∈ σK_set, F z =
      (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
      starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ) := by
    -- For z = σ·embed(α) ∈ σK:
    -- z⁻¹kz = α⁻¹·σ⁻¹·k·σ·α = α⁻¹·(k^q)·α = k^q (K abelian)
    -- where k^q = fieldExtEmbed(β^q) with k = fieldExtEmbed(β)
    -- So F(z) = ν(k)·conj(ν(k^q)) = ν(k)·conj(ν(k)^q) = conj(ν(k)^{q-1}) = conj(ψ(k))
    obtain ⟨γ, hγ⟩ := k.2  -- k = fieldExtEmbed(γ)
    -- The Frobenius image of k in K
    set kq_units : (GaloisField p (2 * n))ˣ :=
      ⟨(γ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       (γ⁻¹ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, mul_inv_cancel₀ γ.ne_zero],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, inv_mul_cancel₀ γ.ne_zero]⟩
    have hkq_mem : Etingof.GL2.fieldExtEmbed p n kq_units ∈
        Etingof.GL2.ellipticSubgroup p n := ⟨kq_units, rfl⟩
    -- σ⁻¹·k·σ = fieldExtEmbed(kq_units) (by frobeniusMatrix_conj)
    have hfrob_conj : (Etingof.GL2.frobeniusMatrix p n)⁻¹ *
        (k : GL2 p n) * Etingof.GL2.frobeniusMatrix p n =
        Etingof.GL2.fieldExtEmbed p n kq_units := by
      rw [show (k : GL2 p n) = Etingof.GL2.fieldExtEmbed p n γ from hγ.symm]
      exact Etingof.GL2.frobeniusMatrix_conj p n hn γ
    -- For z = σ·embed(α): z⁻¹·k·z = fieldExtEmbed(kq_units)
    have hσK_conj : ∀ α : (GaloisField p (2 * n))ˣ,
        (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
        (k : GL2 p n) *
        (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α) =
        Etingof.GL2.fieldExtEmbed p n kq_units := by
      intro α
      -- (σα)⁻¹ k (σα) = α⁻¹ (σ⁻¹ k σ) α = α⁻¹ kq α = kq (K abelian)
      have h1 : (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
          (k : GL2 p n) *
          (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α) =
          (Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
          ((Etingof.GL2.frobeniusMatrix p n)⁻¹ * (k : GL2 p n) *
            Etingof.GL2.frobeniusMatrix p n) *
          Etingof.GL2.fieldExtEmbed p n α := by group
      rw [h1, hfrob_conj, ← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
    -- Membership in K for conjugates
    have hσK_mem : ∀ α : (GaloisField p (2 * n))ˣ,
        (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
        (k : GL2 p n) *
        (Etingof.GL2.frobeniusMatrix p n * Etingof.GL2.fieldExtEmbed p n α) ∈
        Etingof.GL2.ellipticSubgroup p n := by
      intro α; rw [hσK_conj α]; exact hkq_mem
    -- Character value: ν(k)·conj(ν(kq)) = conj(ψ(k))
    -- ψ(k) = qm1_char(k) = ν(k)^{q-1}
    -- ν(kq) = ν(fieldExtEmbed(γ^q)) = ν(fieldExtEmbed(γ))^q = ν(k)^q
    -- (since fieldExtEmbed is a homomorphism and γ^q = γ^q as group power)
    have hnu_kq : nu ⟨Etingof.GL2.fieldExtEmbed p n kq_units, hkq_mem⟩ =
        (nu k) ^ Fintype.card (GaloisField p n) := by
      have : ⟨Etingof.GL2.fieldExtEmbed p n kq_units, hkq_mem⟩ =
          k ^ Fintype.card (GaloisField p n) := by
        apply Subtype.ext
        show Etingof.GL2.fieldExtEmbed p n kq_units =
          (k : GL2 p n) ^ Fintype.card (GaloisField p n)
        rw [show (k : GL2 p n) = Etingof.GL2.fieldExtEmbed p n γ from hγ.symm,
          ← map_pow]
        congr 1; exact Units.ext rfl
      rw [this, map_pow]
    -- ν(k)·conj(ν(k)^q) = conj(ν(k)^{q-1})
    have hchar_val : (nu k : ℂ) * starRingEnd ℂ ((nu k : ℂ) ^ Fintype.card (GaloisField p n)) =
        starRingEnd ℂ ((nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1)) := by
      set v := (nu k : ℂ)
      set c := starRingEnd ℂ v
      have hvc : v * c = 1 := Etingof.normSq_monoidHom_val_eq_one nu k
      rw [map_pow, map_pow]
      -- v * c^q = c^{q-1}
      have hq_pos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
      rw [show Fintype.card (GaloisField p n) = Fintype.card (GaloisField p n) - 1 + 1 from
        by omega, pow_succ]
      calc v * (c ^ (Fintype.card (GaloisField p n) - 1) * c)
          = c ^ (Fintype.card (GaloisField p n) - 1) * (v * c) := by ring
        _ = c ^ (Fintype.card (GaloisField p n) - 1) * 1 := by rw [hvc]
        _ = c ^ (Fintype.card (GaloisField p n) - 1) := mul_one _
    -- Each term in σK contributes the same value
    have hterm : ∀ z ∈ σK_set, F z =
        starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ) := by
      intro z hz
      simp only [σK_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨α, rfl⟩ := hz
      simp only [F, dif_pos (hσK_mem α)]
      -- The conjugated element equals kq
      have hconj_eq : (⟨_ , hσK_mem α⟩ : ↥(Etingof.GL2.ellipticSubgroup p n)) =
          ⟨Etingof.GL2.fieldExtEmbed p n kq_units, hkq_mem⟩ :=
        Subtype.ext (hσK_conj α)
      rw [hconj_eq, hnu_kq, Units.val_pow_eq_pow_val, hchar_val]
      congr 1 -- conj is injective; both sides reduce to the same qm1_char definition
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    -- |σK_set| = |K|
    congr 1
    -- σK bijects with K via z ↦ σ⁻¹z
    rw [show σK_set = K_set.map ⟨(Etingof.GL2.frobeniusMatrix p n * ·),
        mul_right_injective _⟩ from by
      ext z; simp only [σK_set, K_set, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨Etingof.GL2.fieldExtEmbed p n α, ⟨α, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨α, rfl⟩, rfl⟩
        exact ⟨α, rfl⟩]
    rw [Finset.card_map]
    simp only [K_set, ← Fintype.card_subtype]
  -- Step 8: Combine
  rw [hK_eval, hσK_eval]; ring

-- The algebraic core: change of variables and normalizer evaluation.
-- The sum over elliptic elements rewrites via (g,x,y) -> (k,x,z) as
-- |GL₂| * |K| * ∑_{k in K non-scalar} (1 + conj(qm1_char(k))).
-- This encapsulates:
-- 1. Bijection {(g,x): g elliptic, x⁻¹gx ∈ K} <-> {(k,x): k ∈ K non-scalar, x ∈ GL₂}
-- 2. Normalizer N_{GL₂}(K) = K ∪ σK (σ = Frobenius lift)
-- 3. Conjugation: z ∈ K -> z⁻¹kz = k, z ∈ σK -> z⁻¹kz = k^q
-- 4. Character: ν(k)*conj(ν(k)) = 1, ν(k)*conj(ν(k^q)) = ν(k)^{1-q}
open Classical in
private lemma Etingof.elliptic_sum_algebraic_core
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
    ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)
       else 0) := by
  -- Step A: Reindex the triple sum.
  -- Expand |S(g)|² into double sum, change variables (g,x,y) → (k,x,z) where
  -- k = x⁻¹gx ∈ K non-scalar, z = x⁻¹y. The x variable is free → factor |GL₂|.
  -- Result: LHS = |GL₂| * ∑_{k ∈ K, ell} ∑_z ν(k)*conj(ν(z⁻¹kz))
  have hreindex :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    ∑ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
       then ∑ z : GL2 p n,
         (if h : z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
          else 0)
       else 0) := by
    -- Triple-sum rearrangement: expand |S(g)|², change variables (g,x,y) → (k,x,z),
    -- factor out |GL₂|. Key ingredients: S is class-invariant, IsElliptic is
    -- conjugation-invariant (disc_conj_eq), non-K terms vanish from the dite.
    sorry
  -- Step B: Evaluate the normalizer sum for each non-scalar k ∈ K.
  -- For non-scalar k: {z : z⁻¹kz ∈ K} = N(K) = K ∪ σK (disjoint).
  -- K-part: z⁻¹kz = k (K abelian), so ν(k)*conj(ν(k)) = 1 by normSq.
  -- σK-part: z⁻¹kz = k^q (Frobenius), so ν(k)*conj(ν(k^q)) = conj(ψ(k)).
  -- Total: |K|·1 + |K|·conj(ψ(k)) = |K|·(1 + conj(ψ(k))).
  have hnorm_eval : ∀ (k : ↥(Etingof.GL2.ellipticSubgroup p n)),
    GL2.IsElliptic (p := p) (n := n) (k : GL2 p n) →
    ∑ z : GL2 p n,
      (if h : z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
       else 0) =
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
    ((1 : ℂ) + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)) :=
    fun k hk => Etingof.normalizer_char_eval p n hp2 nu hn k hk
  -- Step C: Combine the two results.
  rw [hreindex]
  -- Replace inner sums using hnorm_eval
  have hinner : ∀ k : ↥(Etingof.GL2.ellipticSubgroup p n),
    (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
     then ∑ z : GL2 p n,
       (if h : z⁻¹ * (k : GL2 p n) * z ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
        else 0)
     else 0) =
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
    (if GL2.IsElliptic (p := p) (n := n) (k : GL2 p n)
     then (1 : ℂ) + starRingEnd ℂ ((Etingof.qm1_char p n nu k : ℂˣ) : ℂ)
     else 0) := by
    intro k; split_ifs with hk
    · exact hnorm_eval k hk
    · simp
  simp_rw [hinner, ← Finset.mul_sum]
  ring

open Classical in
/-- The sum of |Ind_K^G ν|² over elliptic elements equals q(q-1)³.

This encapsulates the three hardest steps of the elliptic contribution proof:

1. **Conjugacy class decomposition**: The sum over elliptic GL₂ elements rewrites as
   (q(q-1)/2) times the sum over non-scalar elements of K = 𝔽_{q²}×.
   Uses orbit-stabilizer: each elliptic conjugacy class has q(q-1) elements,
   and Frobenius pairing (ζ ~ ζ^q) halves the representative count.

2. **Induced character on K**: For non-scalar ζ ∈ K, the Frobenius character formula
   gives Ind_K^G ν(ζ) = ν(ζ) + ν^q(ζ), since N_G(K)/K ≅ Gal(𝔽_{q²}/𝔽_q).
   Hence |Ind(ζ)|² = 2 + ν^{q-1}(ζ) + ν^{1-q}(ζ) (using |ν(ζ)| = 1).

3. **Character orthogonality**: ∑_K ν^{q-1} = 0 (by `sum_nontrivial_char_eq_zero`
   since ν^q ≠ ν). On 𝔽_q× ⊂ K, ν^{q-1} = 1, so ∑_{K\𝔽_q×} ν^{q-1} = -(q-1).
   Total: q(q-1)/2 · [2·q(q-1) - 2(q-1)] = q(q-1)/2 · 2(q-1)² = q(q-1)³. -/
private lemma Etingof.induced_normSq_sum_elliptic
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) *
      starRingEnd ℂ ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
  -- Step 1: Factor out |K|⁻² from the sum
  -- Each term is (c⁻¹ * S) * conj(c⁻¹ * S) = c⁻² * (S * conj(S)) where c = |K|
  have h_factor : ∀ (S : ℂ),
      ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ * S) *
      starRingEnd ℂ ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ * S) =
      (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ ^ 2 *
      (S * starRingEnd ℂ S) := by
    intro S; simp only [map_mul, map_inv₀, Complex.conj_natCast]; ring
  simp_rw [h_factor, ← Finset.mul_sum]
  -- Step 2: The raw sum ∑_{g ell} f(g)·conj(f(g)) = |GL₂|·|K|·(q-1)²
  -- via orbit-stabilizer decomposition and character orthogonality:
  --   (a) Expand f(g)·conj(f(g)) as double sum over x, y
  --   (b) Substitute k = x⁻¹gx ∈ K (non-scalar ↔ g elliptic), z = x⁻¹y
  --   (c) The x sum is free → factor |GL₂|
  --   (d) For non-scalar k ∈ K: {z : z⁻¹kz ∈ K} = N_{GL₂}(K), |N| = 2|K|
  --       For z ∈ K: z⁻¹kz = k (K abelian); for z ∈ N\K: z⁻¹kz = k^q (Frobenius)
  --   (e) ∑_{k ∈ K\F_q×} [ν(k)·conj(ν(k)) + ν(k)·conj(ν(k^q))]
  --       = ∑_{K\F_q×} [1 + ν^{1-q}(k)]
  --   (f) By sum_nontrivial_char_eq_zero: ∑_K ν^{1-q} = 0 (since ν^q ≠ ν)
  --       On F_q×: ν^{1-q} = 1 (since a^{q-1} = 1), so ∑_{F_q×} ν^{1-q} = q-1
  --       Hence ∑_{K\F_q×} ν^{1-q} = -(q-1)
  --   (g) Total: |GL₂|·|K|·[q(q-1) - (q-1)] = |GL₂|·|K|·(q-1)²
  have hraw : ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
    -- Sub-step A: Sum rearrangement
    -- Expand ∑_g (∑_x ν(x⁻¹gx))·conj(∑_y ν(y⁻¹gy)) as triple sum over (g,x,y).
    -- Substitute k = x⁻¹gx ∈ K, z = x⁻¹y. The map (g,x,y) ↦ (k,x,z) is a bijection
    -- restricted to {g elliptic, x⁻¹gx ∈ K, y⁻¹gy ∈ K} ↔ {k ∈ K\F_q×, x ∈ GL₂, z⁻¹kz ∈ K}.
    -- The x variable is free → factor |GL₂|.
    -- Result: |GL₂| · ∑_{z ∈ GL₂} ∑_{k ∈ K\F_q× : z⁻¹kz ∈ K} ν(k)·conj(ν(z⁻¹kz))
    --
    -- Sub-step B: Normalizer evaluation
    -- For non-scalar k ∈ K with centralizer C_{GL₂}(k) = K:
    --   {z : z⁻¹kz ∈ K} = N_{GL₂}(K), |N| = 2|K|
    --   N/K ≅ Gal(F_{q²}/F_q) = {id, Frob}
    -- So: ∑_z [...] = ∑_{z ∈ K} ν(k)·conj(ν(k)) + ∑_{z ∈ N\K} ν(k)·conj(ν(k^q))
    --                = |K|·1 + |K|·ν^{1-q}(k)
    -- Result: |GL₂|·|K| · ∑_{k ∈ K\F_q×} (1 + ν^{1-q}(k))
    --
    -- Sub-step C: Character orthogonality
    -- ∑_K ν^{1-q} = 0 by sum_nontrivial_char_eq_zero (since ν^q ≠ ν implies ν^{1-q} ≠ 1)
    -- ∑_{F_q×} ν^{1-q} = q-1 (since a^{q-1} = 1 for a ∈ F_q×, so ν^{1-q}(a) = ν(1) = 1)
    -- ∑_{K\F_q×} ν^{1-q} = 0 - (q-1) = -(q-1)
    -- ∑_{K\F_q×} (1 + ν^{1-q}(k)) = q(q-1) + (-(q-1)) = (q-1)²
    -- Result: |GL₂|·|K|·(q-1)²
    --
    -- Implementation plan for removing this sorry:
    -- 1. Use simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum] to expand
    --    |S(g)|² into a triple sum ∑_g ∑_x ∑_y
    -- 2. Use Finset.sum_comm to reorder, then Fintype.sum_bijective with
    --    the map g ↦ x⁻¹gx (for fixed x) and y ↦ x⁻¹y to change variables
    --    to (k, x, z) where k = x⁻¹gx ∈ K\F_q×, z = x⁻¹y
    -- 3. Factor out free variable x via Finset.sum_const
    -- 4. For each non-scalar k ∈ K, prove {z : z⁻¹kz ∈ K} = N_{GL₂}(K)
    --    (requires: K ∩ zKz⁻¹ = F_q× for z ∉ N, using that K is a maximal torus)
    -- 5. Decompose N(K) = K ∪ σK where σ is a Frobenius lift, using |N/K| = 2
    -- 6. For z ∈ K: ν(k)*conj(ν(k)) = 1 (by normSq_monoidHom_val_eq_one)
    --    For z ∈ σK: ν(k)*conj(ν(k^q)) = (qm1_char p n nu k)⁻¹
    -- 7. Apply sum_nontrivial_char_eq_zero with qm1_char_nontrivial (uses hnu_ne)
    --    and qm1_char_on_scalar to evaluate ∑_{K\F_q×} ψ = -(q-1)
    -- Steps 4-5 require the deepest algebraic infrastructure (normalizer theory).
    -- Use the two helper lemmas: algebraic core + character orthogonality
    rw [Etingof.elliptic_sum_algebraic_core p n hp2 nu hn hnu_ne,
        Etingof.nonscalar_char_sum p n hp2 nu hn hnu_ne]
  rw [hraw]
  -- Step 3: Arithmetic: Kc⁻² · Gc · Kc · (q-1)² = q · (q-1)³
  -- Using Gc = (q²-1)(q²-q) and Kc = q²-1
  -- First establish cardinality facts
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq_pos : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact Nat.one_lt_pow hn hp.out.one_lt
  have hinj : Function.Injective (Etingof.GL2.fieldExtEmbed p n) := by
    intro a b hab
    unfold GL2.fieldExtEmbed at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  -- |K| as ℕ: goes through fieldExtEmbed injectivity
  have hKc_units : Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) =
      Fintype.card (GaloisField p (2 * n))ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(Etingof.GL2.fieldExtEmbed p n).range = _
    exact Nat.card_congr ((Etingof.GL2.fieldExtEmbed p n).ofInjective hinj).symm.toEquiv
  -- |K| = q² - 1 as ℕ
  have hq_pn : q = p ^ n := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  have hKc_nat : Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) = q ^ 2 - 1 := by
    rw [hKc_units, Fintype.card_units,
      ← Nat.card_eq_fintype_card,
      GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
    congr 1
    rw [hq_pn, show 2 * n = n * 2 from by ring, pow_mul]
  -- |GL₂| = (q²-1)(q²-q) as ℕ
  have hGc_nat : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
  -- Cast to ℂ
  have h1 : 1 ≤ q ^ 2 := by nlinarith
  have h2 : q ≤ q ^ 2 := by nlinarith
  have hKc_C : (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) =
      (q : ℂ) ^ 2 - 1 := by
    rw [hKc_nat]; push_cast [Nat.cast_sub h1]; ring
  have hGc_C : (Fintype.card (GL2 p n) : ℂ) =
      ((q : ℂ) ^ 2 - 1) * ((q : ℂ) ^ 2 - (q : ℂ)) := by
    rw [hGc_nat, Nat.cast_mul]; push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  have hKc_ne : (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos (α := ↥(Etingof.GL2.ellipticSubgroup p n)).ne'
  rw [hGc_C, hKc_C]
  have hq2_ne : (q : ℂ) ^ 2 - 1 ≠ 0 := by rw [← hKc_C]; exact hKc_ne
  field_simp

open Classical in
/-- The elliptic contribution to ∑ |χ|² equals q(q-1)³.

For elliptic g, χ(g) = -Ind_K^G ν(g) (by `complementarySeriesChar_elliptic_eq`),
so |χ(g)|² = |Ind(g)|². The sum of |Ind|² over elliptic elements equals q(q-1)³
by conjugacy class decomposition and character orthogonality
(see `induced_normSq_sum_elliptic`). -/
private lemma Etingof.elliptic_contribution
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      Etingof.GL2.complementarySeriesChar p n nu g *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
  -- Step 1: Rewrite each |χ(g)|² = |Ind(g)|² using complementarySeriesChar_elliptic_eq
  have hconv : ∀ g ∈ Finset.univ.filter
      (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      Etingof.GL2.complementarySeriesChar p n nu g *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
      ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [Etingof.complementarySeriesChar_elliptic_eq p n nu g hg.2]
    simp only [map_neg, neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_congr rfl hconv]
  -- Step 2: Apply the helper for the induced character norm-squared sum
  exact Etingof.induced_normSq_sum_elliptic p n hp2 nu hn hnu_ne

/-- Arithmetic identity: contributions from scalar, parabolic, and elliptic conjugacy classes
sum to |GL₂(𝔽_q)|. Specifically:
  (q-1)³ + (q-1)(q²-1) + q(q-1)³ = q(q-1)²(q+1) = (q²-1)(q²-q) -/
private lemma Etingof.innerProduct_arith_identity (q : ℂ) :
    (q - 1) ^ 3 + (q - 1) * (q ^ 2 - 1) + q * (q - 1) ^ 3 =
    (q ^ 2 - 1) * (q ^ 2 - q) := by
  ring

/-- The inner product sum ∑_{g∈G} |χ(g)|² equals |G| = q(q-1)²(q+1).

The proof splits the sum over GL₂(𝔽_q) by conjugacy class type:
- **Scalar matrices** xI (q-1 elements): |χ(xI)|² = (q-1)², total (q-1)³
- **Parabolic matrices** (q-1)(q²-1) elements: |χ|² = 1, total (q-1)(q²-1)
- **Non-scalar semisimple** (split): χ = 0, total 0
- **Elliptic elements**: uses character orthogonality ∑_{F_{q²}×} ν^{q-1}(ζ) = 0
  to get total q(q-1)³

Combined: (q-1)³ + (q-1)(q²-1) + q(q-1)³ = (q-1)²[q-1+q+1+q(q-1)] = (q-1)²q(q+1) = |G|.
-/
private lemma Etingof.innerProduct_sum_eq_card
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (∑ x : GL2 p n,
      Etingof.GL2.complementarySeriesChar p n nu x *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) : ℂ) =
    (Fintype.card (GL2 p n) : ℂ) := by
  have hn_ne : n ≠ 0 := by omega
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq1 : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    exact Nat.one_lt_pow hn_ne hp.out.one_lt
  -- |GL₂(𝔽_q)| = (q²-1)(q²-q)
  have hG : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
  -- Step 1: Split sum by conjugacy class type
  set χ := Etingof.GL2.complementarySeriesChar p n nu
  set f : GL2 p n → ℂ := fun g => χ g * starRingEnd ℂ (χ g)
  -- Use GL2.sum_split (GL2 and GL2' are definitionally equal)
  have hsplit := GL2.sum_split (p := p) (n := n) f
  rw [hsplit]
  -- Step 2: Compute contribution from each class type
  -- Scalar: each element contributes (q-1)², total = (q-1) * (q-1)² = (q-1)³
  have h_scalar : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsScalar g), f g =
      ((q : ℂ) - 1) ^ 3 := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsScalar (p := p) (n := n) g),
        f g = ((q : ℂ) - 1) ^ 2 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_scalar p n nu hn_ne g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isScalar hn_ne, nsmul_eq_mul]
    have h1 : 1 ≤ q := by omega
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1]; ring
  -- Parabolic: each element contributes 1, total = (q-1)(q²-1)
  have h_parabolic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic g), f g =
      ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - 1) := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic (p := p) (n := n) g),
        f g = 1 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_parabolic p n hp2 nu g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isParabolic hp2 hn_ne, nsmul_eq_mul,
      mul_one]
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := by nlinarith
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  -- Split semisimple: each element contributes 0
  have h_split : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsSplitSemisimple g), f g = 0 := by
    apply Finset.sum_eq_zero; intro g hg
    rw [Finset.mem_filter] at hg
    have h0 : χ g = 0 := Etingof.complementaryChar_splitSemisimple_eq_zero p n hp2 nu g hg.2
    change χ g * starRingEnd ℂ (χ g) = 0
    rw [h0, map_zero, mul_zero]
  -- Elliptic: total = q(q-1)³
  have h_elliptic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsElliptic g), f g =
      (q : ℂ) * ((q : ℂ) - 1) ^ 3 :=
    Etingof.elliptic_contribution p n hp2 nu hn_ne hnu_ne
  -- Combine
  rw [h_scalar, h_parabolic, h_split, h_elliptic, hG]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := by nlinarith
  have h3 : q ≤ q ^ 2 := by nlinarith
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]; ring

/-- **Lemma 5.25.3 (part 1)**: The complementary series virtual character
satisfies ⟨χ, χ⟩ = 1, establishing (via Lemma 5.7.2) that it is the character
of an actual irreducible representation. (Etingof Lemma 5.25.3) -/
theorem Etingof.Lemma5_25_3_innerProduct
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(Etingof.GL2.ellipticSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ x : GL2 p n,
        Etingof.GL2.complementarySeriesChar p n nu x *
        starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) = 1 := by
  rw [Etingof.innerProduct_sum_eq_card p n hp2 nu hn hnu_ne]
  simp only [smul_eq_mul]
  have hcard : (Fintype.card (GL2 p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact inv_mul_cancel₀ hcard

/-- **Lemma 5.25.3 (part 2)**: The complementary series virtual character
satisfies χ(1) = q - 1 > 0, confirming it has positive dimension.
(Etingof Lemma 5.25.3) -/
private lemma Etingof.charW₁_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] :
    Etingof.GL2.charW₁ p n 1 =
      (Fintype.card (GaloisField p n) : ℂ) := by
  unfold GL2.charW₁
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  norm_num

private lemma Etingof.dimension_arith_identity
    (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hqp1 : q + 1 ≠ 0) :
    q * (q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q))) -
    q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) -
    (q ^ 2 - 1)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) = q - 1 := by
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [this]; exact mul_ne_zero hq1 hqp1
  have hqm1sq : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  field_simp [hq, hq1, hqp1, hq2m1, hqm1sq]
  ring

theorem Etingof.Lemma5_25_3_dimension
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    Etingof.GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1 ∧
    (0 : ℝ) < (p ^ n : ℝ) - 1 := by
  constructor
  · -- Part 1: χ(1) = q - 1
    -- At g = 1, x⁻¹·1·x = 1 for all x
    have h1x : ∀ x : GL2 p n, x⁻¹ * 1 * x = 1 := by intro x; simp
    -- Unfold and simplify the character at identity
    change GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1
    unfold GL2.complementarySeriesChar GL2.charW₁ GL2.charVα₁
    simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h1x]
    -- Simplify nu at identity: nu(⟨1, _⟩) = nu(1) = 1, scalarToElliptic(1) = 1
    have hnu_sub : ∀ h, nu (⟨1, h⟩ : ↥(GL2.ellipticSubgroup p n)) = 1 :=
      fun h => (congrArg nu (Subtype.ext rfl)).trans (map_one nu)
    simp only [hnu_sub, Units.val_one]
    -- Resolve Fin 2 if-conditions and simplify 0*t²+0*t-0=0
    norm_num
    -- Goal: q * (q⁻¹ * (q-1)²⁻¹ * |G|) - q⁻¹ * (q-1)²⁻¹ * |G| - |K|⁻¹ * |G| = p^n - 1
    -- where q = p^n, |G| = |GL₂(𝔽_q)|, |K| = |𝔽_{q²}×|
    -- Factor out |G|: ((q-1) * q⁻¹ * (q-1)²⁻¹ - q⁻¹ * (q-1)²⁻¹ - |K|⁻¹) * |G|
    -- = ((q-1)/((q-1)²q) - 1/((q-1)²q) - 1/|K|) * |G|
    -- = (1/((q-1)q) - 1/|K|) * |G|  -- since (q-1-1)/((q-1)²q) = ... wait
    -- Actually: (q-1)/(q(q-1)²) = 1/(q(q-1))
    -- And 1/(q(q-1)²) = 1/(q(q-1)²) stays.
    -- So: q/(q(q-1)²) - 1/(q(q-1)²) - 1/(q²-1) = (q-1)/(q(q-1)²) - 1/(q²-1)
    --   = 1/(q(q-1)) - 1/((q-1)(q+1))  = ((q+1) - q) / (q(q-1)(q+1)) = 1/(q(q-1)(q+1))
    -- Then 1/(q(q-1)(q+1)) * q(q-1)²(q+1) = q-1. ✓
    -- This needs |GL₂| = q(q²-1)(q-1) and |K| = q²-1
    -- Convert all Fintype.card to Nat.card to avoid Fintype instance mismatches
    simp only [← Nat.card_eq_fintype_card]
    have hn_ne : n ≠ 0 := by omega
    have hq_val : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn_ne
    have hq1 : 1 < Nat.card (GaloisField p n) := by
      rw [hq_val]; exact Nat.one_lt_pow hn_ne hp.out.one_lt
    -- GL₂ cardinality (card_GL_field uses Fintype.card for q, convert to Nat.card)
    have hG : Nat.card (GL2 p n) =
        (Nat.card (GaloisField p n) ^ 2 - 1) *
        (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
      haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
      have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
      simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
                  ← Nat.card_eq_fintype_card] at this
      exact this
    -- Elliptic subgroup cardinality: |K| = |𝔽_{q²}×| = q² - 1
    have hK : Nat.card ↥(GL2.ellipticSubgroup p n) =
        Nat.card (GaloisField p n) ^ 2 - 1 := by
      -- K = fieldExtEmbed.range
      change Nat.card ↥(GL2.fieldExtEmbed p n).range = _
      -- fieldExtEmbed is injective (leftMulMatrix is injective as AlgHom from a field)
      have hinj : Function.Injective (GL2.fieldExtEmbed p n) := by
        intro a b hab
        unfold GL2.fieldExtEmbed at hab
        simp only [dif_neg hn_ne] at hab
        have hval := congr_arg (fun g => g.val) hab
        have := RingHom.injective
          (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
          (GaloisField p (2 * n)) (finrank_galoisField_ext p n hn_ne))).toRingHom
        exact Units.ext (this hval)
      -- |range| = |domain| since injective
      have : (GL2.fieldExtEmbed p n).range.carrier = Set.range (GL2.fieldExtEmbed p n) :=
        MonoidHom.coe_range _
      rw [show Nat.card ↥(GL2.fieldExtEmbed p n).range =
        Nat.card ↥(Set.range (GL2.fieldExtEmbed p n)) from by
        congr 1]
      rw [Nat.card_range_of_injective hinj]
      -- |𝔽_{q²}ˣ| = |𝔽_{q²}| - 1 = p^(2n) - 1 = (p^n)² - 1 = q² - 1
      rw [Nat.card_units]
      rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn_ne)]
      rw [hq_val]; ring_nf
    -- Substitute q = p^n throughout (now the goal uses Nat.card)
    rw [hq_val] at hG hK ⊢
    -- Substitute G and K cardinalities
    rw [hG, hK]
    -- Now the goal is purely in terms of p, n as ℕ with casts to ℂ
    -- Convert ℕ subtractions and prove with field_simp + ring
    have h1 : 1 ≤ p ^ n := by omega
    have h2 : 1 ≤ (p ^ n) ^ 2 := by nlinarith
    have h3 : p ^ n ≤ (p ^ n) ^ 2 := by nlinarith
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_pow,
               Nat.cast_one]
    -- Now all ℕ casts are gone, everything is in (↑p : ℂ)^n
    -- Nonzero conditions for field_simp
    have hpn_ne : (↑p : ℂ) ^ n ≠ 0 := by
      exact_mod_cast show (p ^ n : ℕ) ≠ 0 by omega
    have hpn1_ne : (↑p : ℂ) ^ n - 1 ≠ 0 := by
      intro h
      have : (p ^ n : ℕ) = 1 := by exact_mod_cast sub_eq_zero.mp h
      omega
    have hpnp1_ne : (↑p : ℂ) ^ n + 1 ≠ 0 := by
      have : (↑(p ^ n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast [Nat.cast_pow] at this; exact this
    -- Apply the standalone arithmetic identity
    exact dimension_arith_identity _ hpn_ne hpn1_ne hpnp1_ne
  · -- Part 2: q - 1 > 0
    have hp_pos := hp.out.pos
    have h1 : 1 < p ^ n := by
      calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hn
        _ = p := pow_one p
        _ ≥ 2 := hp.out.two_le
    have h2 : (1 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast h1
    linarith
