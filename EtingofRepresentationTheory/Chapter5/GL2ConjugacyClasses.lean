import Mathlib

/-!
# Conjugacy Class Partition for GL₂(𝔽_q)

Every element of GL₂(𝔽_q) falls into exactly one of four conjugacy class types:
- **Scalar**: scalar matrices xI
- **Parabolic**: discriminant zero but not scalar
- **Split semisimple**: discriminant is a nonzero square in 𝔽_q
- **Elliptic**: discriminant is a non-square in 𝔽_q

The classification uses the discriminant Δ = (M₀₀ - M₁₁)² + 4·M₀₁·M₁₀ of the
characteristic polynomial X² - tr(g)X + det(g).
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section Predicates

variable {p n}

/-- Abbreviation for matrix coercion. -/
private abbrev GL2.mat (g : GL2' p n) : Matrix (Fin 2) (Fin 2) (GaloisField p n) := g

/-- The discriminant of a GL₂ element's characteristic polynomial:
Δ = (M₀₀ - M₁₁)² + 4·M₀₁·M₁₀ = tr² - 4·det. -/
noncomputable def GL2.disc (g : GL2' p n) : GaloisField p n :=
  (GL2.mat g 0 0 - GL2.mat g 1 1) ^ 2 + 4 * GL2.mat g 0 1 * GL2.mat g 1 0

/-- A GL₂ element is **scalar** if it is a scalar matrix xI. -/
def GL2.IsScalar (g : GL2' p n) : Prop :=
  GL2.mat g 0 1 = 0 ∧ GL2.mat g 1 0 = 0 ∧ GL2.mat g 0 0 = GL2.mat g 1 1

/-- A GL₂ element is **parabolic** if its discriminant is zero but it is not scalar. -/
def GL2.IsParabolic (g : GL2' p n) : Prop :=
  GL2.disc g = 0 ∧ ¬GL2.IsScalar g

/-- A GL₂ element is **split semisimple** if its discriminant is a nonzero square. -/
def GL2.IsSplitSemisimple (g : GL2' p n) : Prop :=
  GL2.disc g ≠ 0 ∧ IsSquare (GL2.disc g)

/-- A GL₂ element is **elliptic** if its discriminant is a non-square. -/
def GL2.IsElliptic (g : GL2' p n) : Prop :=
  ¬IsSquare (GL2.disc g)

noncomputable instance [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (GL2.IsScalar g) := by
  unfold GL2.IsScalar; infer_instance

noncomputable instance [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (GL2.IsParabolic g) := by
  unfold GL2.IsParabolic; infer_instance

noncomputable instance [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (GL2.IsSplitSemisimple g) := by
  unfold GL2.IsSplitSemisimple; infer_instance

noncomputable instance [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2' p n) : Decidable (GL2.IsElliptic g) := by
  unfold GL2.IsElliptic; infer_instance

end Predicates

section Partition

variable {p n}

/-- A scalar matrix has discriminant zero. -/
lemma GL2.disc_eq_zero_of_isScalar (g : GL2' p n) (h : GL2.IsScalar g) :
    GL2.disc g = 0 := by
  obtain ⟨h01, h10, h00⟩ := h
  unfold disc; rw [h01, h10, h00]; ring

/-- The four conjugacy class predicates are exhaustive. -/
theorem GL2.conjugacyClass_exhaustive (g : GL2' p n) :
    GL2.IsScalar g ∨ GL2.IsParabolic g ∨
    GL2.IsSplitSemisimple g ∨ GL2.IsElliptic g := by
  by_cases hscalar : GL2.IsScalar g
  · exact Or.inl hscalar
  · by_cases hsq : IsSquare (GL2.disc g)
    · -- disc is a square
      by_cases hdisc : GL2.disc g = 0
      · -- disc = 0 and not scalar → parabolic
        exact Or.inr (Or.inl ⟨hdisc, hscalar⟩)
      · -- disc ≠ 0 and square → split semisimple
        exact Or.inr (Or.inr (Or.inl ⟨hdisc, hsq⟩))
    · -- disc is not a square → elliptic
      exact Or.inr (Or.inr (Or.inr hsq))

/-- Scalar and parabolic are disjoint. -/
theorem GL2.isScalar_not_isParabolic (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsParabolic g := by
  intro hs hp; exact hp.2 hs

/-- Scalar and split semisimple are disjoint (scalar has disc = 0). -/
theorem GL2.isScalar_not_isSplitSemisimple (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsSplitSemisimple g := by
  intro hs hss
  exact hss.1 (GL2.disc_eq_zero_of_isScalar g hs)

/-- Scalar and elliptic are disjoint (scalar has disc = 0 which is a square). -/
theorem GL2.isScalar_not_isElliptic (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsElliptic g := by
  intro hs he
  apply he
  rw [GL2.disc_eq_zero_of_isScalar g hs]
  exact IsSquare.zero

/-- Parabolic and split semisimple are disjoint. -/
theorem GL2.isParabolic_not_isSplitSemisimple (g : GL2' p n) :
    GL2.IsParabolic g → ¬GL2.IsSplitSemisimple g := by
  intro hp hss; exact hss.1 hp.1

/-- Parabolic and elliptic are disjoint (disc = 0 is a square). -/
theorem GL2.isParabolic_not_isElliptic (g : GL2' p n) :
    GL2.IsParabolic g → ¬GL2.IsElliptic g := by
  intro hp he
  apply he
  rw [hp.1]
  exact IsSquare.zero

/-- Split semisimple and elliptic are disjoint. -/
theorem GL2.isSplitSemisimple_not_isElliptic (g : GL2' p n) :
    GL2.IsSplitSemisimple g → ¬GL2.IsElliptic g := by
  intro hss he; exact he hss.2

/-- No element satisfies more than one predicate. -/
theorem GL2.conjugacyClass_unique (g : GL2' p n) :
    (GL2.IsScalar g → ¬GL2.IsParabolic g ∧ ¬GL2.IsSplitSemisimple g ∧ ¬GL2.IsElliptic g) ∧
    (GL2.IsParabolic g → ¬GL2.IsScalar g ∧ ¬GL2.IsSplitSemisimple g ∧ ¬GL2.IsElliptic g) ∧
    (GL2.IsSplitSemisimple g → ¬GL2.IsScalar g ∧ ¬GL2.IsParabolic g ∧ ¬GL2.IsElliptic g) ∧
    (GL2.IsElliptic g → ¬GL2.IsScalar g ∧ ¬GL2.IsParabolic g ∧ ¬GL2.IsSplitSemisimple g) :=
  ⟨fun h => ⟨GL2.isScalar_not_isParabolic g h,
             GL2.isScalar_not_isSplitSemisimple g h,
             GL2.isScalar_not_isElliptic g h⟩,
   fun h => ⟨h.2, GL2.isParabolic_not_isSplitSemisimple g h,
             GL2.isParabolic_not_isElliptic g h⟩,
   fun h => ⟨fun hs => GL2.isScalar_not_isSplitSemisimple g hs h,
             fun hp => GL2.isParabolic_not_isSplitSemisimple g hp h,
             GL2.isSplitSemisimple_not_isElliptic g h⟩,
   fun h => ⟨fun hs => GL2.isScalar_not_isElliptic g hs h,
             fun hp => GL2.isParabolic_not_isElliptic g hp h,
             fun hss => GL2.isSplitSemisimple_not_isElliptic g hss h⟩⟩

/-- The four predicates form a decidable partition: every element satisfies exactly one. -/
theorem GL2.conjugacyClass_partition (g : GL2' p n) :
    (GL2.IsScalar g ∧ ¬GL2.IsParabolic g ∧ ¬GL2.IsSplitSemisimple g ∧ ¬GL2.IsElliptic g) ∨
    (GL2.IsParabolic g ∧ ¬GL2.IsScalar g ∧ ¬GL2.IsSplitSemisimple g ∧ ¬GL2.IsElliptic g) ∨
    (GL2.IsSplitSemisimple g ∧ ¬GL2.IsScalar g ∧ ¬GL2.IsParabolic g ∧ ¬GL2.IsElliptic g) ∨
    (GL2.IsElliptic g ∧ ¬GL2.IsScalar g ∧ ¬GL2.IsParabolic g ∧ ¬GL2.IsSplitSemisimple g) := by
  rcases GL2.conjugacyClass_exhaustive g with h | h | h | h
  · exact Or.inl ⟨h, (GL2.conjugacyClass_unique g).1 h⟩
  · exact Or.inr (Or.inl ⟨h, (GL2.conjugacyClass_unique g).2.1 h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, (GL2.conjugacyClass_unique g).2.2.1 h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, (GL2.conjugacyClass_unique g).2.2.2 h⟩))

end Partition

section SumDecomposition

variable {p n}

/-- Every element of GL₂ is in at least one of the four filtered sets. -/
theorem GL2.mem_filter_of_exhaustive [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] (g : GL2' p n) :
    g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g) ∨
    g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact GL2.conjugacyClass_exhaustive g

/-- Split a sum over GL₂(𝔽_q) into the four conjugacy class types. -/
theorem GL2.sum_split [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] (f : GL2' p n → ℂ) :
    ∑ g : GL2' p n, f g =
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g), f g) +
    (∑ g ∈ Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g), f g) := by
  -- Pairwise disjointness of the four filtered sets
  set S := Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g)
  set P := Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g)
  set SS := Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g)
  set E := Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g)
  have hSP : Disjoint S P := Finset.disjoint_filter.mpr
    fun g _ hs hp => (GL2.isScalar_not_isParabolic g hs) hp
  have hSSS : Disjoint S SS := Finset.disjoint_filter.mpr
    fun g _ hs hss => (GL2.isScalar_not_isSplitSemisimple g hs) hss
  have hSE : Disjoint S E := Finset.disjoint_filter.mpr
    fun g _ hs he => (GL2.isScalar_not_isElliptic g hs) he
  have hPSS : Disjoint P SS := Finset.disjoint_filter.mpr
    fun g _ hp hss => (GL2.isParabolic_not_isSplitSemisimple g hp) hss
  have hPE : Disjoint P E := Finset.disjoint_filter.mpr
    fun g _ hp he => (GL2.isParabolic_not_isElliptic g hp) he
  have hSSE : Disjoint SS E := Finset.disjoint_filter.mpr
    fun g _ hss he => (GL2.isSplitSemisimple_not_isElliptic g hss) he
  -- Composite disjointness
  have hSPuSS : Disjoint (S ∪ P) SS :=
    disjoint_sup_left.mpr ⟨hSSS, hPSS⟩
  have hSPSSuE : Disjoint (S ∪ P ∪ SS) E :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hSE, hPE⟩, hSSE⟩
  -- The four sets cover univ
  have hunion : Finset.univ = S ∪ P ∪ SS ∪ E := by
    ext g; simp only [S, P, SS, E]
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    rcases GL2.conjugacyClass_exhaustive g with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  conv_lhs => rw [hunion]
  rw [Finset.sum_union hSPSSuE, Finset.sum_union hSPuSS, Finset.sum_union hSP]

end SumDecomposition

section Cardinalities

variable {p n}

/-- The number of scalar matrices in GL₂(𝔽_q) is q - 1. -/
theorem GL2.card_isScalar [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g)).card =
    Fintype.card (GaloisField p n) - 1 := by
  -- Scalar matrices biject with nonzero field elements
  -- Define the scalar matrix construction
  let scalarMat : (GaloisField p n)ˣ → GL2' p n := fun x =>
    ⟨Matrix.diagonal (fun _ => (x : GaloisField p n)),
     Matrix.diagonal (fun _ => (↑x⁻¹ : GaloisField p n)),
     by rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_one],
     by rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_one]⟩
  -- scalarMat is injective
  have scalarMat_inj : Function.Injective scalarMat := by
    intro a b hab
    have h := congr_arg (fun g => (g : GL2' p n).val 0 0) hab
    simp only [scalarMat, Matrix.diagonal_apply, ite_true] at h
    exact Units.ext h
  -- Image of scalarMat = scalar filter
  have scalarMat_image : (Finset.univ.image scalarMat) =
      Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;> simp [GL2.IsScalar, GL2.mat, scalarMat, Matrix.diagonal]
    · intro hg
      obtain ⟨h01, h10, h00⟩ := hg
      -- g₀₀ is nonzero (since g ∈ GL₂ and det = g₀₀²)
      have h00_ne : g.val 0 0 ≠ 0 := by
        intro h0
        have hdet : Matrix.det g.val = 0 := by
          simp only [GL2.mat] at h01 h10 h00
          rw [Matrix.det_fin_two, h01, h10, ← h00, h0]; ring
        have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
          rw [← Matrix.det_mul, hmul, Matrix.det_one]
        rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
      refine ⟨Units.mk0 (g.val 0 0) h00_ne, Units.ext (Matrix.ext fun i j => ?_)⟩
      fin_cases i <;> fin_cases j <;>
        simp [scalarMat, Matrix.diagonal_apply, h01, h10, h00]
  -- Compute the cardinality
  rw [← scalarMat_image, Finset.card_image_of_injective _ scalarMat_inj,
      Finset.card_univ, Fintype.card_units]

/-- The number of parabolic elements in GL₂(𝔽_q) is (q-1)(q²-1). -/
theorem GL2.card_isParabolic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) ^ 2 - 1) := by
  sorry

/-- The number of split semisimple elements in GL₂(𝔽_q) is
(q-1)(q-2)q(q+1)/2. -/
theorem GL2.card_isSplitSemisimple [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) - 2) *
    Fintype.card (GaloisField p n) *
    (Fintype.card (GaloisField p n) + 1) / 2 := by
  sorry

/-- The number of elliptic elements in GL₂(𝔽_q) is q²(q-1)²/2. -/
theorem GL2.card_isElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g)).card =
    Fintype.card (GaloisField p n) ^ 2 *
    (Fintype.card (GaloisField p n) - 1) ^ 2 / 2 := by
  sorry

end Cardinalities
