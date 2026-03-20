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

/-- The discriminant expressed in terms of public matrix entries. -/
@[simp] lemma GL2.disc_eq (g : GL2' p n) :
    GL2.disc g = (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 := rfl

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

@[simp] lemma GL2.isScalar_iff (g : GL2' p n) :
    GL2.IsScalar g ↔ g.val 0 1 = 0 ∧ g.val 1 0 = 0 ∧ g.val 0 0 = g.val 1 1 := Iff.rfl

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

/-! ### Disc = 0 counting

The disc = 0 condition is `(g₀₀ - g₁₁)² + 4·g₀₁·g₁₀ = 0`.

We count by cases:
- **Case g₀₁ = 0**: forces g₀₀ = g₁₁ (call it `a`), g₁₀ free. det = a² ≠ 0 so a ∈ 𝔽_q×.
  Count: (q-1)·q.
- **Case g₀₁ ≠ 0**: g₁₀ is determined as `-(g₀₀-g₁₁)²/(4·g₀₁)`.
  det = ((g₀₀+g₁₁)/2)² ≠ 0, so g₀₀+g₁₁ ≠ 0.
  Free params: g₀₁ ∈ 𝔽_q×, (g₀₀,g₁₁) with sum ≠ 0.
  Count: (q-1)·(q²-q) = (q-1)²·q.
- **Total**: (q-1)·q + (q-1)²·q = (q-1)·q².
-/

/-- In characteristic ≠ 2, the element (2 : GaloisField p n) is nonzero. -/
private lemma GaloisField.two_ne_zero (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (2 : GaloisField p n) ≠ 0 := by
  intro h
  apply hp2
  have h2' : (Nat.cast 2 : GaloisField p n) = 0 := h
  rw [CharP.cast_eq_zero_iff (GaloisField p n) p 2] at h2'
  exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le

/-- In characteristic ≠ 2, (4 : GaloisField p n) is nonzero. -/
private lemma GaloisField.four_ne_zero (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (4 : GaloisField p n) ≠ 0 := by
  intro h
  have h2 := GaloisField.two_ne_zero hp2 hn
  apply h2
  have : (4 : GaloisField p n) = 2 * 2 := by ring
  rw [this] at h
  exact (mul_self_eq_zero.mp h)

/-- Helper: disc = 0 with g₀₁ = 0 forces g₀₀ = g₁₁ in char ≠ 2. -/
private lemma GL2.disc_eq_zero_of_g01_zero {g : GL2' p n}
    (hdisc : GL2.disc g = 0) (h01 : g.val 0 1 = 0) :
    g.val 0 0 = g.val 1 1 := by
  simp only [GL2.disc, GL2.mat] at hdisc
  rw [h01] at hdisc
  simp only [mul_zero, zero_mul, add_zero] at hdisc
  rwa [sq_eq_zero_iff, sub_eq_zero] at hdisc

/-- Helper: when disc = 0 and g₀₁ ≠ 0, then g₁₀ is determined. -/
private lemma GL2.g10_of_disc_zero_g01_ne {g : GL2' p n}
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hdisc : GL2.disc g = 0) (h01 : g.val 0 1 ≠ 0) :
    g.val 1 0 = -((g.val 0 0 - g.val 1 1) ^ 2) / (4 * g.val 0 1) := by
  simp only [GL2.disc, GL2.mat] at hdisc
  have h4 : (4 : GaloisField p n) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  have h4c : (4 * g.val 0 1) ≠ 0 := mul_ne_zero h4 h01
  rw [eq_div_iff h4c]
  linear_combination hdisc

/-- Helper: when disc = 0 and g₀₁ ≠ 0, the determinant equals ((g₀₀+g₁₁)/2)². -/
private lemma GL2.det_of_disc_zero_g01_ne {g : GL2' p n}
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hdisc : GL2.disc g = 0) (h01 : g.val 0 1 ≠ 0) :
    Matrix.det g.val = ((g.val 0 0 + g.val 1 1) / 2) ^ 2 := by
  have h2 : (2 : GaloisField p n) ≠ 0 := GaloisField.two_ne_zero hp2 hn
  have h4 : (4 : GaloisField p n) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  have hg10 := GL2.g10_of_disc_zero_g01_ne hp2 hn hdisc h01
  rw [Matrix.det_fin_two]
  rw [hg10]
  field_simp
  ring

/-- The set of disc = 0 matrices in GL₂ with g₀₁ = 0 has cardinality (q-1)·q. -/
private lemma GL2.card_disc_zero_g01_zero (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n =>
      GL2.disc g = 0 ∧ g.val 0 1 = 0)).card =
    (Fintype.card (GaloisField p n) - 1) * Fintype.card (GaloisField p n) := by
  -- Bijection with (𝔽_q× × 𝔽_q): (a, b) ↦ [[a, 0], [b, a]], det = a² ≠ 0
  let F := GaloisField p n
  -- Helper: det of a GL₂ element is nonzero
  have det_ne_zero : ∀ g : GL2' p n, Matrix.det g.val ≠ 0 := by
    intro g hdet
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  -- Define the forward map
  let toMat : Fˣ → F → Matrix (Fin 2) (Fin 2) F := fun a b =>
    !![↑a, 0; b, ↑a]
  have toMat_det : ∀ (a : Fˣ) (b : F), Matrix.det (toMat a b) ≠ 0 := by
    intro a b; simp [toMat, Matrix.det_fin_two]
  let toGL : Fˣ × F → GL2' p n := fun ⟨a, b⟩ =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (toMat a b) (toMat_det a b)
  -- toGL lands in the filter
  have toGL_val : ∀ (a : Fˣ) (b : F), (toGL ⟨a, b⟩).val = toMat a b := by
    intro a b; simp [toGL]
  have toGL_disc : ∀ (a : Fˣ) (b : F), GL2.disc (toGL ⟨a, b⟩) = 0 := by
    intro a b
    simp only [GL2.disc, GL2.mat, toGL_val, toMat]; simp
  have toGL_01 : ∀ (a : Fˣ) (b : F), (toGL ⟨a, b⟩).val 0 1 = 0 := by
    intro a b; simp [toGL_val, toMat]
  -- toGL is injective
  have toGL_inj : Function.Injective toGL := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    have hval : toMat a₁ b₁ = toMat a₂ b₂ := by
      have := congr_arg Units.val h
      rwa [toGL_val, toGL_val] at this
    have ha : (a₁ : F) = (a₂ : F) := by
      have := congr_fun (congr_fun hval 0) 0
      simp [toMat] at this; exact this
    have hb : b₁ = b₂ := by
      have := congr_fun (congr_fun hval 1) 0
      simp [toMat] at this; exact this
    exact Prod.ext (Units.ext ha) hb
  -- toGL is surjective onto the filter
  have toGL_surj : ∀ g ∈ Finset.univ.filter (fun g : GL2' p n =>
      GL2.disc g = 0 ∧ g.val 0 1 = 0), ∃ ab : Fˣ × F, toGL ab = g := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hdisc, h01⟩ := hg
    have h00_eq : g.val 0 0 = g.val 1 1 := GL2.disc_eq_zero_of_g01_zero hdisc h01
    have h00_ne : g.val 0 0 ≠ 0 := by
      intro h0
      apply det_ne_zero g
      rw [Matrix.det_fin_two, h01, ← h00_eq, h0]; ring
    refine ⟨⟨Units.mk0 (g.val 0 0) h00_ne, g.val 1 0⟩,
      Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp only [toGL_val, toMat]
    fin_cases i <;> fin_cases j <;> simp [h01, h00_eq]
  -- Now compute the cardinality
  have himage : (Finset.univ.image toGL) =
      Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 = 0) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨toGL_disc a b, toGL_01 a b⟩
    · intro hg
      exact toGL_surj g (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  rw [← himage, Finset.card_image_of_injective _ toGL_inj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_units]

/-- The set of disc = 0 matrices in GL₂ with g₀₁ ≠ 0 has cardinality (q-1)²·q. -/
private lemma GL2.card_disc_zero_g01_ne (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n =>
      GL2.disc g = 0 ∧ g.val 0 1 ≠ 0)).card =
    (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n) := by
  -- Bijection with (𝔽_q× × 𝔽_q× × 𝔽_q):
  -- (c, s, d) ↦ [[s+d, c], [-d²/c, s-d]], where s = (a+b)/2, d = (a-b)/2
  -- disc = (2d)² + 4·c·(-d²/c) = 4d² - 4d² = 0
  -- det = (s+d)(s-d) - c·(-d²/c) = s²-d²+d² = s² ≠ 0
  let F := GaloisField p n
  have h2 : (2 : F) ≠ 0 := GaloisField.two_ne_zero hp2 hn
  have h4 : (4 : F) ≠ 0 := GaloisField.four_ne_zero hp2 hn
  -- Helper: det of a GL₂ element is nonzero
  have det_ne_zero : ∀ g : GL2' p n, Matrix.det g.val ≠ 0 := by
    intro g hdet
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  have cancel_inv : ∀ (a b : F), a ≠ 0 → a * (b * a⁻¹) = b := by
    intros a b ha; rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  -- Define the forward map
  let toMat : Fˣ → Fˣ → F → Matrix (Fin 2) (Fin 2) F := fun c s d =>
    !![↑s + d, ↑c; -(d ^ 2 * (↑c : F)⁻¹), ↑s - d]
  have toMat_det : ∀ (c : Fˣ) (s : Fˣ) (d : F), Matrix.det (toMat c s d) ≠ 0 := by
    intro c s d
    have hc_ne : (↑c : F) ≠ 0 := c.ne_zero
    have : (toMat c s d).det = (↑s : F) ^ 2 := by
      -- det = (s+d)(s-d) + c·(d²·c⁻¹) = s²-d²+d² = s²
      simp only [toMat, Matrix.det_fin_two]; simp
      -- Goal: (↑s + d) * (↑s - d) - ↑c * -(d ^ 2 * (↑c)⁻¹) = ↑s ^ 2
      rw [mul_neg, sub_neg_eq_add, cancel_inv _ _ hc_ne]; ring
    rw [this]; exact pow_ne_zero 2 s.ne_zero
  let toGL : Fˣ × Fˣ × F → GL2' p n := fun ⟨c, s, d⟩ =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (toMat c s d) (toMat_det c s d)
  have toGL_val : ∀ (c : Fˣ) (s : Fˣ) (d : F), (toGL ⟨c, s, d⟩).val = toMat c s d := by
    intro c s d; simp [toGL]
  -- toGL has disc = 0
  have toGL_disc : ∀ (c : Fˣ) (s : Fˣ) (d : F), GL2.disc (toGL ⟨c, s, d⟩) = 0 := by
    intro c s d
    have hc_ne : (↑c : F) ≠ 0 := c.ne_zero
    simp only [GL2.disc, GL2.mat, toGL_val]
    -- Reduce !![...] i j and simplify the disc expression
    simp [toMat]
    -- Goal: (d + d) ^ 2 + -(4 * ↑c * (d ^ 2 * (↑c)⁻¹)) = 0
    rw [show 4 * (↑c : F) * (d ^ 2 * (↑c : F)⁻¹) =
      4 * ((↑c : F) * (d ^ 2 * (↑c : F)⁻¹)) from by ring,
      cancel_inv _ _ hc_ne]; ring
  -- toGL has g₀₁ ≠ 0
  have toGL_01 : ∀ (c : Fˣ) (s : Fˣ) (d : F), (toGL ⟨c, s, d⟩).val 0 1 ≠ 0 := by
    intro c s d
    simp [toGL_val, toMat, c.ne_zero]
  -- toGL is injective
  have toGL_inj : Function.Injective toGL := by
    intro ⟨c₁, s₁, d₁⟩ ⟨c₂, s₂, d₂⟩ h
    have hval : toMat c₁ s₁ d₁ = toMat c₂ s₂ d₂ := by
      have := congr_arg Units.val h; rwa [toGL_val, toGL_val] at this
    have hc : (c₁ : F) = (c₂ : F) := by
      have := congr_fun (congr_fun hval 0) 1
      simp [toMat] at this; exact this
    have hsd_sum : (↑s₁ : F) + d₁ = ↑s₂ + d₂ := by
      have := congr_fun (congr_fun hval 0) 0
      simp [toMat] at this; exact this
    have hsd_diff : (↑s₁ : F) - d₁ = ↑s₂ - d₂ := by
      have := congr_fun (congr_fun hval 1) 1
      simp [toMat] at this; exact this
    have hs : (s₁ : F) = (s₂ : F) := by
      have h_sum := hsd_sum; have h_diff := hsd_diff
      have : 2 * (↑s₁ : F) = 2 * ↑s₂ := by linear_combination h_sum + h_diff
      exact mul_left_cancel₀ h2 this
    have hd : d₁ = d₂ := by
      have h1 := hsd_sum  -- ↑s₁ + d₁ = ↑s₂ + d₂
      rw [hs] at h1  -- now ↑s₂ + d₁ = ↑s₂ + d₂
      exact add_left_cancel h1
    exact Prod.ext (Units.ext hc) (Prod.ext (Units.ext hs) hd)
  -- toGL is surjective onto the filter
  have toGL_surj : ∀ g ∈ Finset.univ.filter (fun g : GL2' p n =>
      GL2.disc g = 0 ∧ g.val 0 1 ≠ 0), ∃ csd : Fˣ × Fˣ × F, toGL csd = g := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hdisc, h01⟩ := hg
    -- c = g₀₁ (nonzero)
    -- s = (g₀₀ + g₁₁)/2, d = (g₀₀ - g₁₁)/2
    set c := Units.mk0 (g.val 0 1) h01
    set s_val := (g.val 0 0 + g.val 1 1) / 2
    set d_val := (g.val 0 0 - g.val 1 1) / 2
    -- s_val is nonzero because det = s_val² ≠ 0
    have hdet := det_ne_zero g
    have hg10 := GL2.g10_of_disc_zero_g01_ne hp2 hn hdisc h01
    have hdet_eq := GL2.det_of_disc_zero_g01_ne hp2 hn hdisc h01
    have hs_ne : s_val ≠ 0 := by
      intro h0
      apply hdet
      rw [hdet_eq]; change s_val ^ 2 = 0; rw [h0, sq, zero_mul]
    set s := Units.mk0 s_val hs_ne
    -- Show g₀₀ = s_val + d_val, g₁₁ = s_val - d_val
    have h00 : g.val 0 0 = s_val + d_val := by
      show g.val 0 0 = (g.val 0 0 + g.val 1 1) / 2 + (g.val 0 0 - g.val 1 1) / 2
      field_simp; ring
    have h11 : g.val 1 1 = s_val - d_val := by
      show g.val 1 1 = (g.val 0 0 + g.val 1 1) / 2 - (g.val 0 0 - g.val 1 1) / 2
      field_simp; ring
    -- Show g₁₀ = -(d_val^2 * g₀₁⁻¹)
    have h10 : g.val 1 0 = -(d_val ^ 2 * (g.val 0 1)⁻¹) := by
      rw [hg10]
      -- hg10 gives: g₁₀ = -(g₀₀ - g₁₁)² / (4 * g₀₁)
      -- d_val = (g₀₀ - g₁₁) / 2, so d_val² = (g₀₀ - g₁₁)² / 4
      -- -(d_val² * g₀₁⁻¹) = -((g₀₀ - g₁₁)² / 4 * g₀₁⁻¹) = -(g₀₀ - g₁₁)² / (4 * g₀₁)
      simp only [d_val]
      field_simp; ring
    refine ⟨⟨c, s, d_val⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    simp only [toGL_val, toMat]
    fin_cases i <;> fin_cases j <;> simp [s, s_val, d_val, c]
    · exact h00.symm
    · exact h10.symm
    · exact h11.symm
  -- Now compute the cardinality
  have himage : (Finset.univ.image toGL) =
      Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 ≠ 0) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c, s, d⟩, rfl⟩; exact ⟨toGL_disc c s d, toGL_01 c s d⟩
    · intro hg
      exact toGL_surj g (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  rw [← himage, Finset.card_image_of_injective _ toGL_inj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_prod]
  -- card (Fˣ × Fˣ × F) = card Fˣ * (card Fˣ * card F) = (q-1) * ((q-1) * q) = (q-1)² * q
  -- F = GaloisField p n as a let-binding, so unfold it for card_units
  change Fintype.card (GaloisField p n)ˣ * (Fintype.card (GaloisField p n)ˣ *
    Fintype.card (GaloisField p n)) =
    (Fintype.card (GaloisField p n) - 1) ^ 2 * Fintype.card (GaloisField p n)
  rw [Fintype.card_units]
  set q := Fintype.card (GaloisField p n)
  have hq1 : 1 ≤ q := Fintype.card_pos
  -- (q-1) * ((q-1)*q) = (q-1)^2 * q
  zify [hq1]; ring

private lemma GL2.card_disc_eq_zero (hp2 : p ≠ 2) (hn : n ≠ 0)
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2' p n)] :
    (Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0)).card =
    (Fintype.card (GaloisField p n) - 1) * Fintype.card (GaloisField p n) ^ 2 := by
  -- Split filter by g₀₁ = 0 vs g₀₁ ≠ 0
  have hsplit : Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0) =
      Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 = 0) ∪
      Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 ≠ 0) := by
    ext g; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h; by_cases h01 : g.val 0 1 = 0
      · exact Or.inl ⟨h, h01⟩
      · exact Or.inr ⟨h, h01⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint
      (Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 = 0))
      (Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0 ∧ g.val 0 1 ≠ 0)) := by
    apply Finset.disjoint_filter.mpr
    intro g _ ⟨_, h0⟩ ⟨_, h1⟩; exact h1 h0
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [GL2.card_disc_zero_g01_zero hp2 hn, GL2.card_disc_zero_g01_ne hp2 hn]
  set q := Fintype.card (GaloisField p n)
  have hq1 : 1 ≤ q := Fintype.card_pos
  -- (q-1)*q + (q-1)²*q = (q-1)*q² in ℕ
  zify [hq1]; ring

/-- The number of parabolic elements in GL₂(𝔽_q) is (q-1)(q²-1). -/
theorem GL2.card_isParabolic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) ^ 2 - 1) := by
  -- IsParabolic = disc=0 ∧ ¬IsScalar, so filter = disc=0 \ scalar
  have h_sub : Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g) ⊆
      Finset.univ.filter (fun g : GL2' p n => GL2.disc g = 0) := by
    intro g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact GL2.disc_eq_zero_of_isScalar g
  have h_eq : Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g) =
      Finset.univ.filter (fun g => GL2.disc g = 0) \
      Finset.univ.filter (fun g => GL2.IsScalar g) := by
    ext g; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨h1, h2⟩
    · exact fun ⟨h1, h2⟩ => ⟨h1, h2⟩
  rw [h_eq]
  have h_card := Finset.card_sdiff_add_card_eq_card h_sub
  have h_disc := GL2.card_disc_eq_zero hp2 hn
  have h_scalar := GL2.card_isScalar (p := p) hn
  set q := Fintype.card (GaloisField p n)
  -- sdiff.card + (q-1) = (q-1)*q², and we need sdiff.card = (q-1)*(q²-1)
  have hq1 : 1 ≤ q := Fintype.card_pos
  suffices h : (q - 1) * (q ^ 2 - 1) + (q - 1) = (q - 1) * q ^ 2 by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  zify [hq1, hq2]; ring

/-- The number of split semisimple elements in GL₂(𝔽_q) is
(q-1)(q-2)q(q+1)/2. -/
theorem GL2.card_isSplitSemisimple [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g)).card =
    (Fintype.card (GaloisField p n) - 1) *
    (Fintype.card (GaloisField p n) - 2) *
    Fintype.card (GaloisField p n) *
    (Fintype.card (GaloisField p n) + 1) / 2 := by
  sorry

/-- The number of elliptic elements in GL₂(𝔽_q) is q²(q-1)²/2. -/
theorem GL2.card_isElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hp2 : p ≠ 2) (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g)).card =
    Fintype.card (GaloisField p n) ^ 2 *
    (Fintype.card (GaloisField p n) - 1) ^ 2 / 2 := by
  sorry

end Cardinalities
