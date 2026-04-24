import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Formal character determines isomorphism class

For polynomial representations of `GL_N(k)` over algebraically closed fields,
the formal character determines the isomorphism class. This is a consequence of
the complete reducibility of polynomial representations (Schur-Weyl duality).

This file provides the formal-character isomorphism theorem and the weight space
shift computation for the determinant twist.

## Mathematical content

The key theorem `iso_of_formalCharacter_eq_schurPoly` states that a `GL_N(k)`-
representation whose formal character equals a Schur polynomial `S_λ` is
isomorphic to the Schur module `L_λ`. The proof requires:
1. Complete reducibility of polynomial `GL_N` representations
2. Uniqueness of irreducible components with a given highest weight

The previous formulation (`iso_of_glWeightSpace_finrank_eq`) was stated for
arbitrary `FDRep k (GL_N k)`, which is false: non-polynomial representations
like `det⁻¹` and `det⁻²` have all `ℕ`-valued weight spaces trivial (so the
equal-dimensions hypothesis holds vacuously) yet are non-isomorphic.
-/

open CategoryTheory MvPolynomial

noncomputable section

namespace Etingof

/-! ### Schur polynomial injectivity

Distinct antitone partitions have distinct Schur polynomials. The proof uses:
1. `schurPoly_mul_vandermonde`: `S_λ · Δ = det(alt(λ + δ))`
2. `alternant_coeff_kronecker`: the Kronecker delta property of alternant det coefficients
3. Shifted exponents are strictly antitone for antitone partitions
-/

/-- If two strictly antitone exponent sequences give the same alternant determinant,
they are equal. Uses `alternant_coeff_kronecker` (the Kronecker delta property). -/
private theorem alternant_det_injective (N : ℕ) (e₁ e₂ : Fin N → ℕ)
    (he₁ : StrictAnti e₁) (he₂ : StrictAnti e₂)
    (h : (alternantMatrix N e₁).det = (alternantMatrix N e₂).det) :
    e₁ = e₂ := by
  -- coeff_{e₁}(det(alt(e₁))) = 1 by Kronecker delta with e = e' = e₁
  have hc₁ := alternant_coeff_kronecker he₁ he₁
  simp only [ite_true] at hc₁
  -- Since det(alt(e₁)) = det(alt(e₂)), coeff_{e₁}(det(alt(e₂))) = 1
  rw [h, alternant_coeff_kronecker he₂ he₁] at hc₁
  -- So e₂ = e₁ (the if-then-else equals 1 only when the condition holds)
  revert hc₁; split_ifs with heq
  · exact fun _ => heq.symm
  · exact fun h => absurd h one_ne_zero.symm

/-- The shifted exponents `λ + δ` are strictly antitone for antitone `λ`. -/
private theorem shiftedExps_strictAnti' (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    StrictAnti (shiftedExps N lam) := by
  intro i j hij; simp only [shiftedExps]
  exact Nat.add_lt_add_of_le_of_lt (hlam hij.le) (Nat.sub_lt_sub_left (by omega) hij)

/-- Shifted exponents determine the partition. -/
private theorem shiftedExps_injective (N : ℕ) :
    Function.Injective (shiftedExps N) := by
  intro lam₁ lam₂ h
  funext j; exact Nat.add_right_cancel (congr_fun h j)

/-- Schur polynomials are injective on antitone partitions: equal Schur polynomials
imply equal partitions. -/
theorem schurPoly_injective (N : ℕ) (lam₁ lam₂ : Fin N → ℕ)
    (hlam₁ : Antitone lam₁) (hlam₂ : Antitone lam₂)
    (h : schurPoly N lam₁ = schurPoly N lam₂) :
    lam₁ = lam₂ := by
  have h_alt : (alternantMatrix N (shiftedExps N lam₁)).det =
      (alternantMatrix N (shiftedExps N lam₂)).det := by
    have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
    apply mul_right_cancel₀ hΔ
    rw [← schurPoly_mul_vandermonde, ← schurPoly_mul_vandermonde, h]
  exact shiftedExps_injective N
    (alternant_det_injective N _ _ (shiftedExps_strictAnti' N lam₁ hlam₁)
      (shiftedExps_strictAnti' N lam₂ hlam₂) h_alt)

/-- The Schur polynomials `{schurPoly N lam : lam antitone}` are linearly independent
in `MvPolynomial (Fin N) ℚ`.

The proof multiplies a hypothetical linear dependence by the Vandermonde determinant
`Δ = det(X_i^{N-1-j})`, turning each Schur polynomial into the corresponding shifted
alternant `det(X_i^{λ_j + N - j})` via `schurPoly_mul_vandermonde`. The shifted
alternants are linearly independent because their `Finsupp.equivFunOnFinite.symm
(shiftedExps N μ)` coefficient is a Kronecker delta (`alternant_coeff_kronecker`),
isolating the `μ` term from the rest. -/
theorem schurPoly_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun (lam : {lam : Fin N → ℕ // Antitone lam}) =>
      schurPoly N lam.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum μ hμ
  -- Step 1: Multiply `hsum` by the Vandermonde determinant Δ to convert each
  -- `schurPoly N lam` into `det(alternantMatrix N (shiftedExps N lam))`.
  have hmul : ∑ lam ∈ s, g lam • (alternantMatrix N (shiftedExps N lam.val)).det = 0 := by
    have step : (∑ lam ∈ s, g lam • schurPoly N lam.val) *
          (alternantMatrix N (vandermondeExps N)).det = 0 := by
      rw [hsum, zero_mul]
    rw [Finset.sum_mul] at step
    simp only [smul_mul_assoc, schurPoly_mul_vandermonde] at step
    exact step
  -- Step 2: Take the coefficient at `d := Finsupp.equivFunOnFinite.symm (shiftedExps N μ)`.
  have hcoeff := congr_arg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N μ.val))) hmul
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
  -- Step 3: Kronecker property collapses the inner coefficient to
  -- `[shiftedExps λ = shiftedExps μ]`, which by injectivity equals `[λ = μ]`.
  have h_each : ∀ lam ∈ s,
      g lam * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N μ.val))
        (alternantMatrix N (shiftedExps N lam.val)).det =
          if lam = μ then g lam else 0 := by
    intro lam _
    rw [alternant_coeff_kronecker (shiftedExps_strictAnti' N lam.val lam.prop)
      (shiftedExps_strictAnti' N μ.val μ.prop)]
    rcases eq_or_ne lam μ with heq | hne
    · subst heq; rw [if_pos rfl, if_pos rfl, mul_one]
    · have h_ne : shiftedExps N lam.val ≠ shiftedExps N μ.val :=
        fun h => hne (Subtype.ext (shiftedExps_injective N h))
      rw [if_neg h_ne, if_neg hne, mul_zero]
  rw [Finset.sum_congr rfl h_each, Finset.sum_ite_eq' s μ g, if_pos hμ] at hcoeff
  exact hcoeff

/-! ### Homogeneity of Schur polynomials

`schurPoly N lam` is homogeneous of total degree `∑ i, lam i`. We derive this from
`schurPoly_mul_vandermonde`: both the Vandermonde determinant and the shifted
alternant are homogeneous (their degrees match), so their ratio is homogeneous too.
-/

/-- If `ψ` is homogeneous of degree `n`, the homogeneous-component operator commutes
with right-multiplication by `ψ`. -/
private lemma homogeneousComponent_mul_of_isHomogeneous_right
    {σ R : Type*} [CommSemiring R]
    (φ ψ : MvPolynomial σ R) {n : ℕ} (hψ : ψ.IsHomogeneous n) (k : ℕ) :
    MvPolynomial.homogeneousComponent (k + n) (φ * ψ) =
      MvPolynomial.homogeneousComponent k φ * ψ := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_homogeneousComponent]
  split_ifs with hd
  · rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hdeg : d.degree = x.1.degree + x.2.degree := by
      rw [← hx]; exact map_add Finsupp.degree x.1 x.2
    split_ifs with h1
    · rfl
    · have h2 : x.2.degree ≠ n := fun h => h1 (by omega)
      rw [hψ.coeff_eq_zero h2, mul_zero, mul_zero]
  · symm
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hdeg : d.degree = x.1.degree + x.2.degree := by
      rw [← hx]; exact map_add Finsupp.degree x.1 x.2
    split_ifs with h1
    · have h2 : x.2.degree ≠ n := fun h => hd (by omega)
      rw [hψ.coeff_eq_zero h2, mul_zero]
    · exact zero_mul _

/-- `d.degree = Finsupp.weight 1 d` as natural numbers — extracted from the
AddMonoidHom equality `Finsupp.degree_eq_weight_one`. -/
private lemma degree_eq_weight_one_apply {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.degree d = Finsupp.weight 1 d := by
  rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]

/-- The Schur polynomial `schurPoly N lam` is homogeneous of degree `∑ i, lam i`. -/
theorem schurPoly_isHomogeneous (N : ℕ) (lam : Fin N → ℕ) :
    (schurPoly N lam).IsHomogeneous (∑ i, lam i) := by
  intro d hd
  -- Goal (unfolded): Finsupp.weight 1 d = ∑ lam.
  -- Reduce to showing d.degree = ∑ lam, then convert via degree_eq_weight_one_apply.
  rw [← degree_eq_weight_one_apply]
  -- Goal: d.degree = ∑ lam.
  by_contra hne
  have halt : (alternantMatrix N (shiftedExps N lam)).det.IsHomogeneous
      ((∑ i, lam i) + (∑ j : Fin N, vandermondeExps N j)) := by
    have h := alternant_isHomogeneous (shiftedExps N lam)
    have heq : ∑ j : Fin N, shiftedExps N lam j =
        (∑ i, lam i) + (∑ j : Fin N, vandermondeExps N j) := by
      simp only [shiftedExps, vandermondeExps, Finset.sum_add_distrib]
    rw [heq] at h
    exact h
  have hΔhom : (alternantMatrix N (vandermondeExps N)).det.IsHomogeneous
      (∑ j : Fin N, vandermondeExps N j) :=
    alternant_isHomogeneous (vandermondeExps N)
  have hΔne : (alternantMatrix N (vandermondeExps N)).det ≠ 0 :=
    alternantMatrix_vandermondeExps_det_ne_zero N
  -- Apply the helper lemma with k = d.degree.
  have hprod_eq := homogeneousComponent_mul_of_isHomogeneous_right
    (schurPoly N lam) (alternantMatrix N (vandermondeExps N)).det hΔhom d.degree
  rw [schurPoly_mul_vandermonde] at hprod_eq
  -- The LHS is 0 (since d.degree ≠ ∑ lam, hence d.degree + dΔ ≠ ∑ lam + dΔ).
  have hne' : d.degree + (∑ j : Fin N, vandermondeExps N j) ≠
      (∑ i, lam i) + (∑ j : Fin N, vandermondeExps N j) := fun heq => hne (by omega)
  have halt_zero :
      MvPolynomial.homogeneousComponent (d.degree + (∑ j : Fin N, vandermondeExps N j))
        (alternantMatrix N (shiftedExps N lam)).det = 0 := by
    rw [MvPolynomial.homogeneousComponent_of_mem halt, if_neg hne']
  rw [halt_zero] at hprod_eq
  -- So (homogeneousComponent d.degree schurPoly) * Δ = 0; cancel the nonzero Δ.
  have h_eq_zero : MvPolynomial.homogeneousComponent d.degree (schurPoly N lam) = 0 :=
    (mul_eq_zero.mp hprod_eq.symm).resolve_right hΔne
  -- But coeff d of that homogeneous component equals coeff d schurPoly (since d.degree = d.degree).
  have h_coeff_zero :
      MvPolynomial.coeff d (MvPolynomial.homogeneousComponent d.degree (schurPoly N lam)) = 0 := by
    rw [h_eq_zero]; exact MvPolynomial.coeff_zero d
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl] at h_coeff_zero
  exact hd h_coeff_zero

variable (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]

/-- The family of weight spaces of a `GL_N(k)`-representation is sup-independent.
This follows from `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`
applied to the commuting family `diagUnit(i, t)`, combined with the containment
`glWeightSpace μ ≤ ⨅ p, maxGenEigenspace(f p, χ μ p)` and injectivity of
`χ : μ ↦ (p ↦ t^(μ i))`. -/
theorem glWeightSpace_iSupIndep (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    iSupIndep (fun μ : Fin N →₀ ℕ => glWeightSpace k N M (fun i => μ i)) := by
  set f : Fin N × kˣ → Module.End k M := fun p => M.ρ (diagUnit k N p.1 p.2)
  have h_comm : ∀ (p₁ p₂ : Fin N × kˣ), Commute (f p₁) (f p₂) :=
    fun p₁ p₂ => rep_diagUnit_commute k N M p₁.1 p₁.2 p₂.1 p₂.2
  have h_mapsTo : ∀ (p₁ p₂ : Fin N × kˣ) (φ : k),
      Set.MapsTo (f p₁) ((f p₂).maxGenEigenspace φ) ((f p₂).maxGenEigenspace φ) :=
    fun p₁ p₂ φ => Module.End.mapsTo_maxGenEigenspace_of_comm (h_comm p₂ p₁) φ
  have h_indep := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo
  -- Define eigenvalue map χ μ p = (p.2)^(μ p.1) and show injectivity
  set χ : (Fin N →₀ ℕ) → (Fin N × kˣ → k) :=
    fun μ p => (p.2 : k) ^ (μ p.1)
  have h_inj : Function.Injective χ := by
    intro μ₁ μ₂ heq
    ext i
    by_contra hi
    obtain ⟨t, ht⟩ := exists_unit_pow_ne k hi
    exact ht (congr_fun heq (i, t))
  -- Compose with injective χ to reindex; then use mono with the containment
  exact (h_indep.comp h_inj).mono (fun μ =>
    le_iInf (fun p => glWeightSpace_le_maxGenEigenspace k N M (fun j => μ j) p.1 p.2))

/-- For a polynomial `GL_N(k)`-representation (i.e., one where the `ℕ`-valued
weight spaces span the whole module), the finrank equals the sum of weight space
dimensions over the (finite) support. -/
theorem finrank_eq_sum_glWeightSpace (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    Module.finrank k M =
      ∑ μ ∈ (glWeightSpace_finite_support k N M).toFinset,
        Module.finrank k (glWeightSpace k N M (fun i => μ i)) := by
  set p : (Fin N →₀ ℕ) → Submodule k M :=
    fun μ => glWeightSpace k N M (fun i => μ i) with hp_def
  have h_indep : iSupIndep p := glWeightSpace_iSupIndep k N M
  have hs_fin : {μ | p μ ≠ ⊥}.Finite := glWeightSpace_finite_support k N M
  haveI : Fintype {μ // p μ ≠ ⊥} := hs_fin.fintype
  -- Restrict to nonzero weight spaces; still IsInternal
  have h_internal : DirectSum.IsInternal (fun μ : {μ // p μ ≠ ⊥} => p μ.val) := by
    rw [DirectSum.isInternal_ne_bot_iff]
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨h_indep, h_top⟩
  -- Linear equivalence (⨁ μ : support, p μ) ≃ M via IsInternal
  let e : DirectSum {μ // p μ ≠ ⊥} (fun μ => (p μ.val : Submodule k M)) ≃ₗ[k] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h_internal
  rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]
  -- Convert sum over {μ // p μ ≠ ⊥} to sum over hs_fin.toFinset
  rw [← Finset.sum_attach hs_fin.toFinset (fun μ => Module.finrank k (p μ)),
    show hs_fin.toFinset.attach = (Finset.univ : Finset {x // x ∈ hs_fin.toFinset})
      from Finset.attach_eq_univ]
  -- Now both sides are Fintype sums on subtypes; relate them via an equiv
  refine Fintype.sum_equiv
    ({ toFun := fun ⟨x, hx⟩ => ⟨x, (Set.Finite.mem_toFinset hs_fin).mpr hx⟩,
       invFun := fun ⟨x, hx⟩ => ⟨x, (Set.Finite.mem_toFinset hs_fin).mp hx⟩,
       left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      {μ // p μ ≠ ⊥} ≃ {x // x ∈ hs_fin.toFinset})
    (fun μ => Module.finrank k (p μ.val))
    (fun μ => Module.finrank k (p μ.val)) (fun _ => rfl)

/-- Two polynomial `GL_N(k)`-representations with the same formal character have the
same finrank. For polynomial reps, `finrank M = ∑_μ finrank(M_μ)`, and equal characters
imply equal weight space dimensions pointwise via `formalCharacter_coeff`. -/
theorem finrank_eq_of_formalCharacter_eq (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h₁_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M₁ (fun i => μ i) = ⊤)
    (h₂_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M₂ (fun i => μ i) = ⊤)
    (h_char : formalCharacter k N M₁ = formalCharacter k N M₂) :
    Module.finrank k M₁ = Module.finrank k M₂ := by
  -- Pointwise equality of weight space dimensions via formalCharacter_coeff
  have h_ptw : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (glWeightSpace k N M₁ (fun i => μ i)) =
      Module.finrank k (glWeightSpace k N M₂ (fun i => μ i)) := by
    intro μ
    have h₁ := formalCharacter_coeff k N M₁ μ
    have h₂ := formalCharacter_coeff k N M₂ μ
    have h_ℚ : ((Module.finrank k (glWeightSpace k N M₁ (fun i => μ i)) : ℚ) =
        (Module.finrank k (glWeightSpace k N M₂ (fun i => μ i)) : ℚ)) := by
      rw [← h₁, ← h₂, h_char]
    exact_mod_cast h_ℚ
  -- Both finranks equal sums over respective supports; extend to union of supports
  rw [finrank_eq_sum_glWeightSpace k N M₁ h₁_top,
      finrank_eq_sum_glWeightSpace k N M₂ h₂_top]
  set S₁ := (glWeightSpace_finite_support k N M₁).toFinset
  set S₂ := (glWeightSpace_finite_support k N M₂).toFinset
  have h_extend : ∀ (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (S : Finset (Fin N →₀ ℕ))
      (hS : (glWeightSpace_finite_support k N M).toFinset ⊆ S),
      ∑ μ ∈ (glWeightSpace_finite_support k N M).toFinset,
          Module.finrank k (glWeightSpace k N M (fun i => μ i)) =
        ∑ μ ∈ S, Module.finrank k (glWeightSpace k N M (fun i => μ i)) := by
    intro M S hS
    apply Finset.sum_subset hS
    intro μ _ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    simp only [Set.mem_setOf_eq, not_not] at hμ
    rw [hμ, finrank_bot]
  rw [h_extend M₁ (S₁ ∪ S₂) Finset.subset_union_left,
      h_extend M₂ (S₁ ∪ S₂) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun μ _ => h_ptw μ)

/-- If a finite-dimensional polynomial `GL_N(k)`-representation has formal character
equal to `schurPoly N lam` for an antitone partition `lam`, then every weight `μ`
with nonzero weight-space dimension has the same magnitude as `lam`.

This is the tensor-degree homogeneity of the representation: because the Schur
polynomial is homogeneous of total degree `∑ lam`, its only monomials occur at
weights of that magnitude, and formal-character equality transports this to `M`. -/
theorem weight_magnitude_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (μ : Fin N → ℕ) (hμ : 0 < Module.finrank k (glWeightSpace k N M μ)) :
    ∑ i, μ i = ∑ i, lam i := by
  set d : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm μ with hd_def
  -- `d` coincides with `μ` as a function, so the weight-space finranks agree
  have hd_fun : (fun i : Fin N => (d i : ℕ)) = μ := by
    funext i; rfl
  -- The coefficient at `d` of the formal character is positive (= finrank of weight space)
  have hcoeff_char : (formalCharacter k N M).coeff d > 0 := by
    rw [formalCharacter_coeff k N M d, hd_fun]
    exact_mod_cast hμ
  -- Therefore the same coefficient in `schurPoly N lam` is nonzero
  have hcoeff_schur : (schurPoly N lam).coeff d ≠ 0 := by
    rw [← h]; exact ne_of_gt hcoeff_char
  -- By homogeneity of `schurPoly`, `weight 1 d = ∑ lam`; convert to `d.degree`.
  have h_weight : Finsupp.weight 1 d = ∑ i, lam i :=
    schurPoly_isHomogeneous N lam hcoeff_schur
  have hd_deg_lam : d.degree = ∑ i, lam i := by
    rw [degree_eq_weight_one_apply]; exact h_weight
  -- But `d.degree = ∑ μ` since `d` agrees pointwise with `μ`
  have hd_deg_mu : d.degree = ∑ i, μ i := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl (fun i _ => congrFun hd_fun i)
  omega

/-- A `GL_N(k)`-representation whose formal character equals a Schur polynomial
`S_λ` and whose dimension matches the Schur module is isomorphic to `L_λ`.

The dimension hypothesis `h_dim` is necessary: without it, one could take
`M = L_λ ⊕ det⁻¹`, which has `formalCharacter M = schurPoly N lam` (since
`det⁻¹` has no `ℕ`-valued weight spaces and is invisible to `formalCharacter`),
yet `M ≇ L_λ` due to the dimension mismatch. The hypothesis ensures `M` is
"polynomial" — its `ℕ`-valued weight spaces account for all of `M`.

The proof requires GL_N-equivariant complete reducibility: every polynomial
`GL_N`-representation decomposes into a direct sum of Schur modules. Combined
with `Theorem5_22_1` (Weyl character formula) and `schurPoly_injective`,
this forces `M ≅ L_λ`.

The downstream use is in `schurModule_shift_iso_detTwist` (Proposition 5.22.2),
where both representations are polynomial and have character equal to
`schurPoly N (λ + 1^N)`. -/
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)) :
    Nonempty (M ≅ SchurModule k N lam) := by
  -- Proof outline:
  -- 1. From h + Theorem5_22_1: weight space dims match at every ℕ-valued weight
  -- 2. From h_dim: ℕ-valued weight spaces span M (M is polynomial)
  -- 3. By GL_N-equivariant complete reducibility (Schur-Weyl): M ≅ ⊕ nᵢ · L_μᵢ
  -- 4. Character additivity + schurPoly_injective: nλ = 1, all others = 0
  -- 5. Therefore M ≅ L_λ
  sorry

/-- The finsupp with all values equal to 1 on `Fin N`. -/
private def onesFinsupp (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

private theorem onesFinsupp_apply (N : ℕ) (i : Fin N) : onesFinsupp N i = 1 := by
  simp [onesFinsupp]

private theorem onesFinsupp_support (N : ℕ) : (onesFinsupp N).support = Finset.univ := by
  ext i; simp [onesFinsupp]

private theorem prod_X_eq_monomial_ones (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) =
      MvPolynomial.monomial (onesFinsupp N) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial (R := ℚ) (s := onesFinsupp N),
    onesFinsupp_support]
  simp_rw [onesFinsupp_apply, pow_one]

/-- If the weight space dimensions of `M₁` at weight `ν + (1,…,1)` equal those of `M₂` at `ν`
(for all `ν`), and weight spaces of `M₁` at weights with some zero component are trivial,
then the formal character of `M₁` is `(∏ Xᵢ) · char(M₂)`. -/
theorem formalCharacter_shift_of_weightSpace_finrank (N : ℕ)
    (M₁ M₂ : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_shift : ∀ ν : Fin N → ℕ,
      Module.finrank k (glWeightSpace k N M₁ (fun i => ν i + 1)) =
        Module.finrank k (glWeightSpace k N M₂ ν))
    (h_vanish : ∀ μ : Fin N → ℕ, (∃ i, μ i = 0) →
      Module.finrank k (glWeightSpace k N M₁ μ) = 0) :
    formalCharacter k N M₁ =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N M₂ := by
  ext μ
  rw [formalCharacter_coeff, prod_X_eq_monomial_ones, coeff_monomial_mul']
  split_ifs with h
  · -- Case: onesFinsupp N ≤ μ, i.e., all μ i ≥ 1
    rw [one_mul, formalCharacter_coeff]
    have hge : ∀ i : Fin N, 1 ≤ μ i := fun i => by
      have := h i; rwa [onesFinsupp_apply] at this
    have key : (fun i => (μ - onesFinsupp N) i + 1) = (⇑μ : Fin N → ℕ) := by
      ext i; simp [Finsupp.tsub_apply, onesFinsupp_apply, Nat.sub_add_cancel (hge i)]
    have := h_shift (fun i => (μ - onesFinsupp N) i)
    rw [key] at this
    exact_mod_cast this
  · -- Case: ¬(onesFinsupp N ≤ μ), i.e., some μ i = 0
    have hexists : ∃ i : Fin N, (μ i : ℕ) = 0 := by
      by_contra hall
      push_neg at hall
      exact h fun i => by rw [onesFinsupp_apply]; exact Nat.one_le_iff_ne_zero.mpr (hall i)
    exact_mod_cast h_vanish (⇑μ) hexists

/-! ### Character additivity and multiplicativity

Two foundational identities for the formal character:
* **Direct-sum additivity**: `formalCharacter (⨁ i, M_i) = ∑ i, formalCharacter M_i`.
* **Trivial-tensor multiplicativity**: `formalCharacter (S ⊗ L) = (dim S) • formalCharacter L`
  when `S` carries the trivial `GL_N`-action.

Both follow from the analogous statements on weight-space finranks, combined with
`formalCharacter_coeff`. -/

open scoped DirectSum in
open Representation in
/-- Componentwise formula for the direct-sum representation: for `x : DirectSum ι V`,
the `j`-th coordinate of applying `Representation.directSum ρ g` to `x` is
`ρ j g (x j)`. -/
private lemma directSum_rep_coord (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (g : Matrix.GeneralLinearGroup (Fin N) k) (x : DirectSum ι V) (j : ι) :
    (Representation.directSum ρ g x) j = ρ j g (x j) := by
  change (DirectSum.lmap (fun m => ρ m g)) x j = ρ j g (x j)
  rw [DirectSum.lmap_apply]

open scoped DirectSum in
open Representation in
/-- The weight space of a direct-sum representation splits coordinate-wise: a
vector `x` lies in the weight space iff each coordinate `x j` lies in the
corresponding weight space of `ρ j`. -/
private lemma mem_glWeightSpace_directSum_iff (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) (x : DirectSum ι V) :
    x ∈ glWeightSpace k N (FDRep.of (Representation.directSum ρ)) μ ↔
      ∀ j : ι, x j ∈ glWeightSpace k N (FDRep.of (ρ j)) μ := by
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, FDRep.of_ρ',
    LinearMap.sub_apply, LinearMap.smul_apply]
  -- Note: `LinearMap.id_apply` is rfl, so we rely on definitional equality via `change`.
  constructor
  · intro h j i t
    -- h : ∀ i t, Rep.directSum ρ (diag i t) x - t^μi • LinearMap.id x = 0
    -- LinearMap.id x ≡ x definitionally
    have hit : Representation.directSum ρ (diagUnit k N i t) x -
        (↑t : k) ^ μ i • x = 0 := h i t
    -- Take the j-th component
    have h_comp : (Representation.directSum ρ (diagUnit k N i t) x -
        (↑t : k) ^ μ i • x) j = (0 : DirectSum ι V) j := by rw [hit]
    rw [DFinsupp.sub_apply, DFinsupp.smul_apply, directSum_rep_coord,
      DFinsupp.zero_apply] at h_comp
    -- Goal: ρ j (diag) (x j) - t^μi • LinearMap.id (x j) = 0
    -- Same definitional step
    exact h_comp
  · intro h i t
    -- Goal: Rep.directSum ρ (diag) x - t^μi • LinearMap.id x = 0
    refine DFinsupp.ext fun j => ?_
    show (Representation.directSum ρ (diagUnit k N i t) x -
        (↑t : k) ^ μ i • x) j = (0 : DirectSum ι V) j
    rw [DFinsupp.sub_apply, DFinsupp.smul_apply, directSum_rep_coord,
      DFinsupp.zero_apply]
    have := h j i t
    exact this

open scoped DirectSum in
open Representation in
/-- Linear equivalence between the direct sum of weight spaces and the weight
space of a direct-sum representation. -/
noncomputable def glWeightSpace_directSum_equiv (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) :
    DirectSum ι (fun j => ↥(glWeightSpace k N (FDRep.of (ρ j)) μ)) ≃ₗ[k]
      ↥(glWeightSpace k N (FDRep.of (Representation.directSum ρ)) μ) := by
  -- Build the equivalence via `LinearMap.range`, starting with an unrestricted map
  let fwd₀ : DirectSum ι (fun j => ↥(glWeightSpace k N (FDRep.of (ρ j)) μ)) →ₗ[k]
      DirectSum ι V :=
    DirectSum.lmap (fun j => (glWeightSpace k N (FDRep.of (ρ j)) μ).subtype)
  have h_inj : Function.Injective fwd₀ :=
    (DirectSum.lmap_injective _).mpr (fun _ => Subtype.val_injective)
  have h_range : LinearMap.range fwd₀ =
      (glWeightSpace k N (FDRep.of (Representation.directSum ρ)) μ) := by
    ext z
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_glWeightSpace_directSum_iff]
      intro j
      -- Goal: (fwd₀ x) j ∈ glWeightSpace ρ_j μ
      -- fwd₀ x = DirectSum.lmap subtypes x, so (fwd₀ x) j = (x j).val by lmap_apply (rfl)
      show (x j).val ∈ glWeightSpace k N (FDRep.of (ρ j)) μ
      exact (x j).2
    · intro hz
      rw [mem_glWeightSpace_directSum_iff] at hz
      -- Construct preimage as a sum of single-indexed elements
      refine ⟨∑ j : ι, DirectSum.of
        (fun j' => ↥(glWeightSpace k N (FDRep.of (ρ j')) μ)) j ⟨z j, hz j⟩, ?_⟩
      -- fwd₀ is linear, so distributes across the sum; each summand becomes
      -- DirectSum.of V j (z j) via lmap_lof, and the total sum reconstructs z.
      rw [map_sum]
      simp only [fwd₀, DirectSum.lmap_lof, Submodule.subtype_apply]
      -- Now goal: ∑ j, DirectSum.of V j (z j) = z
      -- This is DirectSum.sum_univ_of for Fintype
      ext j
      rw [DFinsupp.finset_sum_apply]
      simp [DirectSum.of_apply]
  -- Assemble the equiv
  exact (LinearEquiv.ofInjective fwd₀ h_inj).trans
    (LinearEquiv.ofEq _ _ h_range)

open scoped DirectSum in
open Representation in
/-- The finrank of the weight space of a direct-sum representation is the sum of
finranks of the individual weight spaces. -/
private lemma finrank_glWeightSpace_directSum (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i))
    (μ : Fin N → ℕ) :
    Module.finrank k
        (glWeightSpace k N (FDRep.of (Representation.directSum ρ)) μ) =
      ∑ j : ι, Module.finrank k (glWeightSpace k N (FDRep.of (ρ j)) μ) := by
  rw [← LinearEquiv.finrank_eq (glWeightSpace_directSum_equiv k N V ρ μ),
    Module.finrank_directSum]

open scoped DirectSum in
open Representation in
/-- **Direct-sum additivity of formal character.**
For a finite family of representations `ρ i` on finite-dimensional `k`-modules,
the formal character of the direct-sum representation equals the sum of the
individual formal characters. -/
theorem formalCharacter_directSum (N : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type _) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module.Finite k (V i)]
    (ρ : ∀ i, Representation k (Matrix.GeneralLinearGroup (Fin N) k) (V i)) :
    formalCharacter k N (FDRep.of (Representation.directSum ρ)) =
      ∑ j : ι, formalCharacter k N (FDRep.of (ρ j)) := by
  ext μ
  rw [formalCharacter_coeff, MvPolynomial.coeff_sum]
  simp_rw [formalCharacter_coeff]
  exact_mod_cast finrank_glWeightSpace_directSum k N V ρ μ

end Etingof
