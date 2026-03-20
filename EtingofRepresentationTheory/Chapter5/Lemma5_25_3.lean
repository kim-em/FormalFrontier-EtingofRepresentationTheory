import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues

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
    sorry
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
  exact Etingof.induced_normSq_sum_elliptic p n nu hn hnu_ne

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
    Etingof.elliptic_contribution p n nu hn_ne hnu_ne
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
