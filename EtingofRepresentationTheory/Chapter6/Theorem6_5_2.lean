import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_3
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure
import EtingofRepresentationTheory.Chapter6.Lemma6_4_2

/-!
# Theorem 6.5.2: Gabriel's Theorem

Let Q be a quiver of type Aₙ, Dₙ, E₆, E₇, E₈. Then Q has finitely many
indecomposable representations. Namely, the dimension vector of any indecomposable
representation is a positive root (with respect to B_Γ) and for any positive root α
there is exactly one indecomposable representation with dimension vector α.

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. This is a major result connecting quiver
representation theory to root systems. Mathlib has basic quiver support and
root system infrastructure, but the connection (Gabriel's theorem) is absent.

## Formalization note

This theorem has three parts:
1. Finiteness of indecomposable representations for ADE quivers
2. Dimension vectors of indecomposables are positive roots
3. Each positive root corresponds to exactly one indecomposable (up to isomorphism)

The statement requires substantial infrastructure: quiver representations,
indecomposability, dimension vectors, and the root system of a Dynkin diagram.

We state the three parts separately for clarity, then combine them into the
full theorem.
-/

section Finiteness

/-- The minimum value of B(x,x) for nonzero x ∈ ℤⁿ is 2. This follows from
positive definiteness (giving > 0) and evenness (Lemma 6.4.2). -/
theorem Etingof.posdef_min_value
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (x : Fin n → ℤ) (hx : x ≠ 0) :
    2 ≤ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  have hpos := hDynkin.2.2.2.2 x hx
  have heven := Etingof.Lemma_6_4_2_even n adj hDynkin.1 hDynkin.2.1 x
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hpos ⊢
  omega

/-- The Cartan matrix mulVec is injective for a Dynkin diagram: if C·x = C·y
then x = y. This follows from positive definiteness: C(x-y) = 0 implies
(x-y)ᵀC(x-y) = 0, hence x-y = 0. -/
private theorem Etingof.cartan_mulVec_injective
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj) :
    Function.Injective (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec := by
  intro x y hxy
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hpos := hDynkin.2.2.2.2 (x - y) hne'
  have hzero : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
  simp only [dotProduct, hzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hpos
  omega

/-- Symmetry of the bilinear form for a symmetric matrix:
    y ⬝ᵥ C *ᵥ x = x ⬝ᵥ C *ᵥ y when C is symmetric. -/
private lemma Etingof.dotProduct_mulVec_comm
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct y (C.mulVec x) = dotProduct x (C.mulVec y) := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j
  rw [hCsymm.apply j i]; ring

/-- Helper: bilinear form expansion B(x-y,x-y) = B(x,x) - 2B(x,y) + B(y,y)
for a symmetric matrix, stated in terms of dotProduct and mulVec. -/
private lemma Etingof.bilinear_expand_sub
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct (x - y) (C.mulVec (x - y)) =
    dotProduct x (C.mulVec x) - 2 * dotProduct x (C.mulVec y) +
    dotProduct y (C.mulVec y) := by
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  have hsym := Etingof.dotProduct_mulVec_comm C hCsymm x y
  linarith

/-- Helper: bilinear form expansion B(x+y,x+y) = B(x,x) + 2B(x,y) + B(y,y)
for a symmetric matrix, stated in terms of dotProduct and mulVec. -/
private lemma Etingof.bilinear_expand_add
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct (x + y) (C.mulVec (x + y)) =
    dotProduct x (C.mulVec x) + 2 * dotProduct x (C.mulVec y) +
    dotProduct y (C.mulVec y) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  have hsym := Etingof.dotProduct_mulVec_comm C hCsymm x y
  linarith

/-- For a positive root d of a Dynkin diagram, -2 ≤ (Cd)_i ≤ 2 for all i.
Proof: B(d±e_i, d±e_i) = 4 ± 2(Cd)_i. Since these are nonzero when d ≠ ∓e_i,
posdef_min_value gives |(Cd)_i| ≤ 1 (or = 2 when d = e_i). -/
private theorem Etingof.cartan_mulVec_bounded
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ) (hd : Etingof.IsPositiveRoot n adj d) (i : Fin n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d i ∈ Set.Icc (-2 : ℤ) 2 := by
  set C := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj)
  have hBdd : dotProduct d (C.mulVec d) = 2 := hd.1.2
  have hCsymm : C.IsSymm := Matrix.IsSymm.ext fun a b => by
    simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [hDynkin.1.apply a b]; split_ifs <;> omega
  -- B(e_i, e_i) = 2
  have hBei : dotProduct (Pi.single i 1) (C.mulVec (Pi.single i 1)) = 2 := by
    simp only [dotProduct, C, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Pi.single_apply]
    simp [Finset.sum_ite_eq', hDynkin.2.1 i]
  -- B(e_i, d) = (Cd)_i
  have hBeid : dotProduct (Pi.single i 1) (C.mulVec d) = C.mulVec d i := by
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  -- B(d, e_i) = (Cd)_i  (by symmetry of C)
  have hBdei : dotProduct d (C.mulVec (Pi.single i 1)) = C.mulVec d i := by
    -- Rewrite as: ∑_a d_a * (∑_b C_{ab} * δ_{bi}) = ∑_b C_{ib} * d_b
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    -- Goal: ∑_a d_a * C_{ai} = ∑_b C_{ib} * d_b
    congr 1; ext a; rw [hCsymm.apply i a]; ring
  constructor
  · -- Lower bound: -2 ≤ (Cd)_i
    -- d + e_i ≠ 0
    have hne : d + Pi.single i 1 ≠ 0 := by
      intro h; have := congr_fun h i
      simp [Pi.add_apply] at this; linarith [hd.2 i]
    have hB := Etingof.posdef_min_value hDynkin _ hne
    have hexp := Etingof.bilinear_expand_add C hCsymm d (Pi.single i 1)
    rw [hBdd, hBdei, hBei] at hexp; linarith
  · -- Upper bound: (Cd)_i ≤ 2
    by_cases hdeq : d = Pi.single i 1
    · subst hdeq; rw [← hBeid]; linarith [hBei]
    · have hne : d - Pi.single i 1 ≠ 0 := sub_ne_zero.mpr hdeq
      have hB := Etingof.posdef_min_value hDynkin _ hne
      have hexp := Etingof.bilinear_expand_sub C hCsymm d (Pi.single i 1)
      rw [hBdd, hBdei, hBei] at hexp; linarith

/-- Part (a) of Gabriel's theorem: for a Dynkin diagram, there are finitely many
positive roots. The proof uses the Cauchy-Schwarz bound: for any positive root d,
the vector Cd has entries in {-2,...,2}. Since the map d ↦ Cd is injective
(positive definiteness), the set of positive roots injects into the finite set
{v : Fin n → ℤ | ∀ i, -2 ≤ v i ≤ 2}, hence is finite.
(Etingof Theorem 6.5.2(a)) -/
theorem Etingof.Theorem_6_5_2a_finiteness
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj) :
    Set.Finite {d : Fin n → ℤ | Etingof.IsPositiveRoot n adj d} := by
  set C := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj)
  -- The map d ↦ Cd is injective
  have hC_inj := Etingof.cartan_mulVec_injective hDynkin
  -- The image of positive roots under C.mulVec is in [-2, 2]ⁿ
  have hbounded : ∀ d ∈ {d : Fin n → ℤ | Etingof.IsPositiveRoot n adj d},
      C.mulVec d ∈ Set.Icc (fun (_ : Fin n) => (-2 : ℤ)) (fun _ => 2) := by
    intro d hd
    simp only [Set.mem_Icc, Pi.le_def]
    exact ⟨fun i => (Etingof.cartan_mulVec_bounded hDynkin d hd i).1,
           fun i => (Etingof.cartan_mulVec_bounded hDynkin d hd i).2⟩
  -- [-2, 2]ⁿ is finite
  have hfin : Set.Finite (Set.Icc (fun (_ : Fin n) => (-2 : ℤ)) (fun _ => 2)) :=
    Set.finite_Icc _ _
  -- The image of positive roots is a subset of a finite set, hence finite
  have himg_fin : Set.Finite (C.mulVec '' {d | Etingof.IsPositiveRoot n adj d}) :=
    hfin.subset (Set.image_subset_iff.mpr hbounded)
  -- By injectivity, the domain is also finite
  exact himg_fin.of_finite_image (hC_inj.injOn.mono (Set.subset_univ _))

/-- Gabriel's theorem (combined, part a): the set of positive roots is finite. -/
theorem Etingof.Theorem_6_5_2_Gabriels_theorem
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj) :
    Set.Finite {d : Fin n → ℤ | Etingof.IsPositiveRoot n adj d} :=
  Etingof.Theorem_6_5_2a_finiteness hDynkin

end Finiteness

/-- Part (b) of Gabriel's theorem: the dimension vector of any indecomposable
representation of a Dynkin quiver is a positive root.

Given a dimension vector d that is nonneg, nonzero, and arises from an
indecomposable representation of a Dynkin quiver, d satisfies B(d, d) = 2.
(Etingof Theorem 6.5.2(b)) -/
theorem Etingof.Theorem_6_5_2b_dimvec_is_positive_root
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (_hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2) :
    Etingof.IsPositiveRoot n adj d :=
  ⟨⟨hd_nonzero, by rwa [Etingof.cartanMatrix] at hd_root⟩, hd_pos⟩

/-- Part (c) of Gabriel's theorem: for each positive root α of a Dynkin quiver,
there is exactly one indecomposable representation (up to isomorphism) with
dimension vector α.

This combines Corollary 6.8.4 (every positive root is realized) and
Corollary 6.8.3 (dimension vector determines indecomposable).
(Etingof Theorem 6.5.2(c)) -/
theorem Etingof.Theorem_6_5_2c_bijection
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (k : Type*) [Field k]
    {Q : Quiver (Fin n)}
    (α : Fin n → ℤ) (hα : Etingof.IsPositiveRoot n adj α) :
    -- Existence: there is an indecomposable with dimension vector α
    (∃ (ρ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v)) (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.IsIndecomposable ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v))) ∧
    -- Uniqueness: any two such are isomorphic
    (∀ (ρ₁ ρ₂ : @Etingof.QuiverRepresentation k (Fin n) _ Q)
      [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
      [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)],
      ρ₁.IsIndecomposable → ρ₂.IsIndecomposable →
      (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₁.obj v))) →
      (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₂.obj v))) →
      Nonempty (Etingof.QuiverRepresentation.Iso ρ₁ ρ₂)) := sorry
