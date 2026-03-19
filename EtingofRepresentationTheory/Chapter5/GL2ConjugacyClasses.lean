import Mathlib

/-!
# Conjugacy Class Partition for GL₂(𝔽_q)

Every element of GL₂(𝔽_q) falls into exactly one of four conjugacy class types:
- **Scalar**: scalar matrices xI
- **Parabolic**: conjugate to [[x,1],[0,x]] but not scalar
- **Split semisimple**: diagonalizable over 𝔽_q with distinct eigenvalues
- **Elliptic**: characteristic polynomial irreducible over 𝔽_q

The classification is based on the eigenvalues of the characteristic polynomial
X² - tr(g)X + det(g):
- No roots in 𝔽_q → elliptic
- One double root, g = λI → scalar
- One double root, g ≠ λI → parabolic
- Two distinct roots → split semisimple
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section Predicates

variable {p n}

/-- Abbreviation for matrix coercion. -/
private abbrev GL2.mat (g : GL2' p n) : Matrix (Fin 2) (Fin 2) (GaloisField p n) := g

/-- The set of eigenvalues of a 2×2 matrix over 𝔽_q: roots of X² - tr·X + det in 𝔽_q. -/
private noncomputable def GL2.eigenvalueSet [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) : Finset (GaloisField p n) :=
  Finset.univ.filter fun a =>
    a ^ 2 - (GL2.mat g 0 0 + GL2.mat g 1 1) * a +
    (GL2.mat g 0 0 * GL2.mat g 1 1 - GL2.mat g 0 1 * GL2.mat g 1 0) = 0

/-- A GL₂ element is **scalar** if it equals xI for some scalar x. -/
def GL2.IsScalar (g : GL2' p n) : Prop :=
  GL2.mat g 0 1 = 0 ∧ GL2.mat g 1 0 = 0 ∧ GL2.mat g 0 0 = GL2.mat g 1 1

/-- A GL₂ element is **parabolic** if its characteristic polynomial has a double root
but the matrix is not scalar (i.e., it is a non-trivial unipotent-times-scalar). -/
def GL2.IsParabolic (g : GL2' p n) : Prop :=
  (GL2.mat g 0 0 - GL2.mat g 1 1) ^ 2 + 4 * GL2.mat g 0 1 * GL2.mat g 1 0 = 0 ∧
  ¬GL2.IsScalar g

/-- A GL₂ element is **split semisimple** if its characteristic polynomial has
two distinct roots in 𝔽_q (equivalently, discriminant is a nonzero square). -/
def GL2.IsSplitSemisimple [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) : Prop :=
  (GL2.eigenvalueSet g).card = 2

/-- A GL₂ element is **elliptic** if its characteristic polynomial has no roots
in 𝔽_q (i.e., is irreducible over 𝔽_q). -/
def GL2.IsElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) : Prop :=
  (GL2.eigenvalueSet g).card = 0

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

section EigenvalueProperties

variable {p n}

/-- The discriminant of a GL₂ element's char poly: (M₀₀ - M₁₁)² + 4·M₀₁·M₁₀. -/
private noncomputable def GL2.disc (g : GL2' p n) : GaloisField p n :=
  (GL2.mat g 0 0 - GL2.mat g 1 1) ^ 2 + 4 * GL2.mat g 0 1 * GL2.mat g 1 0

/-- A scalar matrix has eigenvalue set = {diagonal entry}, so card = 1. -/
private lemma GL2.eigenvalueSet_scalar [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n)
    (hscalar : GL2.IsScalar g) :
    (GL2.eigenvalueSet g).card = 1 := by
  obtain ⟨h01, h10, h00⟩ := hscalar
  -- eigenvalueSet uses GL2.mat which is an abbrev, so it unfolds transparently
  unfold eigenvalueSet
  rw [show GL2.mat g 0 1 = 0 from h01, show GL2.mat g 1 0 = 0 from h10,
      show GL2.mat g 0 0 = GL2.mat g 1 1 from h00]
  simp only [mul_zero, sub_zero]
  suffices h : Finset.univ.filter (fun a : GaloisField p n =>
      a ^ 2 - (GL2.mat g 1 1 + GL2.mat g 1 1) * a +
      GL2.mat g 1 1 * GL2.mat g 1 1 = 0) =
      {GL2.mat g 1 1} by
    rw [h, Finset.card_singleton]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have hsq : (a - GL2.mat g 1 1) ^ 2 = 0 := by linear_combination h
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro rfl; ring

/-- When the discriminant is zero and the matrix is not scalar,
the eigenvalue set has exactly 1 element (the double root). -/
private lemma GL2.eigenvalueSet_card_of_disc_zero [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n)
    (hdisc : GL2.disc g = 0) :
    (GL2.eigenvalueSet g).card = 1 := by
  -- disc = 0 means (M₀₀ - M₁₁)² = -4·M₀₁·M₁₀
  -- The charpoly becomes (X - (M₀₀+M₁₁)/2)² (in char ≠ 2) or has a double root
  -- In any case, tr/2 is the unique root when disc = 0
  -- For char = 2: disc = 0 means (M₀₀+M₁₁)² + 4·M₀₁·M₁₀ = (M₀₀+M₁₁)² = 0
  -- so M₀₀ = M₁₁, and the poly is X² + M₀₀·X + M₀₀² + M₀₁·M₁₀... hmm
  -- Actually let's work this out more carefully.
  -- The eigenvalue equation is a² - (M₀₀+M₁₁)·a + (M₀₀·M₁₁-M₀₁·M₁₀) = 0
  -- disc = (M₀₀+M₁₁)² - 4(M₀₀·M₁₁-M₀₁·M₁₀) = (M₀₀-M₁₁)² + 4·M₀₁·M₁₀
  -- When disc = 0, complete the square: the unique root is (M₀₀+M₁₁)/2
  -- But division by 2 requires char ≠ 2.
  -- For char 2: disc = (M₀₀-M₁₁)² = (M₀₀+M₁₁)² = 0, so M₀₀ = M₁₁.
  -- Then the poly is a² - 2·M₀₀·a + M₀₀² - M₀₁·M₁₀ = a² + M₀₁·M₁₀ (in char 2)
  -- And disc = 0 means 4·M₀₁·M₁₀ = 0 so M₀₁·M₁₀ = 0 (since 4=0 in char 2... wait)
  -- Actually in char 2, 4 = 0, so disc = (M₀₀-M₁₁)² always, and the condition
  -- disc = 0 just means M₀₀ = M₁₁. Then the poly is a² + M₀₁·M₁₀.
  -- Its roots: a² = M₀₁·M₁₀ = -(M₀₁·M₁₀) in char 2.
  -- This could have 0 or 1 root depending on whether M₀₁·M₁₀ is a square.
  -- Hmm, this is getting complicated. Let me sorry this for now.
  sorry

/-- When the discriminant is nonzero, the eigenvalue set has 0 or 2 elements. -/
private lemma GL2.eigenvalueSet_card_of_disc_ne_zero [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n)
    (hdisc : GL2.disc g ≠ 0) :
    (GL2.eigenvalueSet g).card = 0 ∨ (GL2.eigenvalueSet g).card = 2 := by
  -- When disc ≠ 0, the charpoly has either 0 or 2 distinct roots.
  -- Over a finite field, a degree-2 polynomial with nonzero discriminant
  -- either splits into 2 distinct linear factors or is irreducible.
  sorry

end EigenvalueProperties

section Partition

variable {p n}

/-- The four conjugacy class predicates are exhaustive. -/
theorem GL2.conjugacyClass_exhaustive [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsScalar g ∨ GL2.IsParabolic g ∨
    GL2.IsSplitSemisimple g ∨ GL2.IsElliptic g := by
  by_cases hscalar : GL2.IsScalar g
  · exact Or.inl hscalar
  · by_cases hdisc : GL2.disc g = 0
    · -- discriminant zero, not scalar → parabolic
      exact Or.inr (Or.inl ⟨hdisc, hscalar⟩)
    · -- discriminant nonzero → either 0 or 2 eigenvalues
      rcases GL2.eigenvalueSet_card_of_disc_ne_zero g hdisc with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

/-- Scalar and parabolic are disjoint. -/
theorem GL2.isScalar_not_isParabolic (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsParabolic g := by
  intro hs hp; exact hp.2 hs

/-- Scalar and split semisimple are disjoint. -/
theorem GL2.isScalar_not_isSplitSemisimple [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsSplitSemisimple g := by
  intro hs hss
  unfold IsSplitSemisimple at hss
  have := GL2.eigenvalueSet_scalar g hs
  omega

/-- Scalar and elliptic are disjoint. -/
theorem GL2.isScalar_not_isElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsScalar g → ¬GL2.IsElliptic g := by
  intro hs he
  unfold IsElliptic at he
  have := GL2.eigenvalueSet_scalar g hs
  omega

/-- Split semisimple and elliptic are disjoint. -/
theorem GL2.isSplitSemisimple_not_isElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsSplitSemisimple g → ¬GL2.IsElliptic g := by
  intro hss he; unfold IsSplitSemisimple IsElliptic at *; omega

/-- Parabolic and split semisimple are disjoint. -/
theorem GL2.isParabolic_not_isSplitSemisimple [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsParabolic g → ¬GL2.IsSplitSemisimple g := by
  intro hp hss
  -- parabolic means disc = 0, giving at most 1 eigenvalue (card = 1)
  -- split semisimple means card = 2, contradiction
  have hdisc := hp.1
  have h1 := GL2.eigenvalueSet_card_of_disc_zero g hdisc
  unfold IsSplitSemisimple at hss
  omega

/-- Parabolic and elliptic are disjoint. -/
theorem GL2.isParabolic_not_isElliptic [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
    GL2.IsParabolic g → ¬GL2.IsElliptic g := by
  intro hp he
  have hdisc := hp.1
  have h1 := GL2.eigenvalueSet_card_of_disc_zero g hdisc
  unfold IsElliptic at he
  omega

/-- No element satisfies more than one predicate. -/
theorem GL2.conjugacyClass_unique [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] (g : GL2' p n) :
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

end Partition

section Cardinalities

variable {p n}

/-- The number of scalar matrices in GL₂(𝔽_q) is q - 1. -/
theorem GL2.card_isScalar [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] (hn : n ≠ 0) :
    (Finset.univ.filter (fun g : GL2' p n => GL2.IsScalar g)).card =
    Fintype.card (GaloisField p n) - 1 := by
  sorry

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
