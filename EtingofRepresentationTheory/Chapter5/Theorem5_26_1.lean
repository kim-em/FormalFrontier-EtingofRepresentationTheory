import Mathlib
import EtingofRepresentationTheory.Chapter4.Theorem4_2_1

/-!
# Theorem 5.26.1: Artin's Theorem

Let X be a conjugation-invariant system of subgroups of a finite group G.
Two conditions are equivalent:

(i) Any element of G belongs to a subgroup H ∈ X.

(ii) The character of any irreducible representation of G belongs to the
ℚ-span of characters of induced representations Ind_H^G V, where H ∈ X
and V is an irreducible representation of H.

## Mathlib correspondence

Uses `Subgroup`, `FDRep.character`, `CategoryTheory.Simple` for irreducible
representations, and `Submodule.span ℚ` for rational linear combinations.
The induced character is expressed via the Frobenius character formula.
-/

noncomputable section

open Classical in
/-- The character of the induced representation Ind_H^G W, computed via the
Frobenius character formula:
  χ_{Ind_H^G W}(g) = (1/|H|) ∑_{x ∈ G} [x⁻¹gx ∈ H] · χ_W(x⁻¹gx)
This defines a class function on G from a class function on a subgroup H. -/
def Etingof.inducedCharacter {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : ↥H → ℂ) : G → ℂ :=
  fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ x : G, if h : x⁻¹ * g * x ∈ H then χ ⟨x⁻¹ * g * x, h⟩ else 0

open Classical in
/-- Frobenius reciprocity for character inner products: for a class function f on G
and a function χ on a subgroup H,
  ∑_{g:G} f(g) · (Ind_H^G χ)(g⁻¹) = (|G|/|H|) · ∑_{h:H} f(↑h) · χ(h⁻¹)
This is a direct computation from the Frobenius character formula:
1. Expand Ind_H^G(χ)(g⁻¹) using the Frobenius formula
2. Swap the double sum over G × G to G × G
3. For each x, substitute h = x⁻¹g⁻¹x (bijection G → G restricting to H)
4. Use that f is a class function: f(xh⁻¹x⁻¹) = f(h⁻¹)
5. Factor out |G| from the sum over x. -/
private lemma frobenius_char_reciprocity {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → ℂ) (χ : ↥H → ℂ)
    (hf : ∀ g x : G, f (x * g * x⁻¹) = f g) :
    ∑ g : G, f g * Etingof.inducedCharacter H χ g⁻¹ =
    (Fintype.card G : ℂ) * (Fintype.card ↥H : ℂ)⁻¹ *
      ∑ h : ↥H, f ↑h * χ (h⁻¹) := by
  -- Key lemma: for each x, the inner sum over g reindexes to a sum over H.
  -- The bijection φ : G ≃ G, φ(k) = x * k⁻¹ * x⁻¹ sends k to g with x⁻¹g⁻¹x = k.
  suffices inner_sum_eq : ∀ x : G,
      ∑ g : G, f g * (if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) =
      ∑ h : ↥H, f ↑h * χ (h⁻¹) by
    -- Once we have inner_sum_eq, the main result follows by simple algebra
    simp_rw [Etingof.inducedCharacter]
    -- Goal: ∑ g, f g * (|H|⁻¹ * ∑ x, ite ...) = |G| * |H|⁻¹ * ∑ h, ...
    -- Transform the LHS step by step
    have lhs_eq : (∑ g : G, f g *
        ((↑(Fintype.card ↥H))⁻¹ * ∑ x : G,
          if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0)) =
      (↑(Fintype.card ↥H))⁻¹ * ∑ x : G, ∑ g : G,
        f g * (if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) := by
      -- Factor |H|⁻¹ and swap sums
      conv_lhs => arg 2; ext g
                  rw [mul_left_comm]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [lhs_eq]
    -- Now: |H|⁻¹ * ∑ x, ∑ g, f g * ite ... = |G| * |H|⁻¹ * ∑ h, ...
    simp_rw [inner_sum_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- Now prove inner_sum_eq for each x
  intro x
  -- Step 1: Reindex via the bijection φ(k) = x * k⁻¹ * x⁻¹
  -- Under this substitution: x⁻¹ * (φ k)⁻¹ * x = k, and f(φ k) = f(k⁻¹) (class function)
  let φ : G ≃ G :=
    { toFun := fun k => x * k⁻¹ * x⁻¹
      invFun := fun g => x⁻¹ * g⁻¹ * x
      left_inv := fun k => by group
      right_inv := fun g => by group }
  rw [← Equiv.sum_comp φ]
  -- Goal: ∑ k, f (φ k) * ite(x⁻¹(φ k)⁻¹x ∈ H)(χ(x⁻¹(φ k)⁻¹x))(0) = ∑ h, f ↑h * χ h⁻¹
  -- Simplify: x⁻¹(φ k)⁻¹x = k
  have hsimp : ∀ k : G, x⁻¹ * (x * k⁻¹ * x⁻¹)⁻¹ * x = k := fun k => by group
  simp_rw [show ∀ k : G, φ k = x * k⁻¹ * x⁻¹ from fun _ => rfl, hsimp]
  -- Simplify: f(x * k⁻¹ * x⁻¹) = f(k⁻¹) (class function)
  simp_rw [show ∀ k : G, f (x * k⁻¹ * x⁻¹) = f k⁻¹ from fun k => hf k⁻¹ x]
  -- Goal: ∑ k, f k⁻¹ * ite(k ∈ H)(χ ⟨k, _⟩)(0) = ∑ h, f ↑h * χ h⁻¹
  -- Step 2: Push f inside the dite, then convert to subtype sum
  conv_lhs => arg 2; ext k; rw [show f k⁻¹ * (if h : k ∈ H then χ ⟨k, h⟩ else 0) =
    if h : k ∈ H then f k⁻¹ * χ ⟨k, h⟩ else 0 by split_ifs <;> simp]
  -- Goal: ∑ k:G, dite(k∈H)(f k⁻¹ χ ⟨k,_⟩)(0) = ∑ h:↥H, f ↑h χ h⁻¹
  -- This is a standard identity: the G-sum with dite restricts to ↥H,
  -- then reindexing h → h⁻¹ in H converts f(↑h)⁻¹ * χ(h) to f(↑h) * χ(h⁻¹).
  -- The mathematical content is trivial; the remaining complexity is
  -- matching Lean Fintype instances between {x // x ∈ H} and ↥H.
  -- Step 3: Split G-sum into H-part and complement
  -- The G-sum with dite restricts to ↥H (complement terms are 0)
  have h_restrict : (∑ k : G, if h_1 : k ∈ H then f k⁻¹ * χ ⟨k, h_1⟩ else 0) =
      ∑ k : ↥H, f (↑k)⁻¹ * χ k := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ H)
      (fun k : G => if h_1 : k ∈ H then f k⁻¹ * χ ⟨k, h_1⟩ else 0)]
    have h_compl : (∑ k : {k : G // k ∉ H},
        if h_1 : (↑k : G) ∈ H then f (↑k)⁻¹ * χ ⟨↑k, h_1⟩ else 0) = 0 :=
      Finset.sum_eq_zero (fun ⟨k, hk⟩ _ => dif_neg hk)
    rw [h_compl, add_zero]
    congr 1; ext ⟨k, hk⟩; exact dif_pos hk
  rw [h_restrict]
  -- Step 4: Reindex by h ↦ h⁻¹ in the subtype sum
  conv_lhs => rw [← Equiv.sum_comp (Equiv.inv ↥H)]
  congr 1; ext h
  simp only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv]

open Classical in
/-- Character completeness on subgroups: if a class function f on G, when restricted to
a subgroup H, is orthogonal to all irreducible characters of H, then f vanishes on H.

This follows from Theorem 4.2.1 applied to H: the restriction f|_H is a class function
on H (since f is a class function on G and H is a subgroup), and characters of irreducible
representations of H span all class functions on H. The orthogonality condition forces
all Fourier coefficients to be zero, so f|_H = 0.

Requires `[IsAlgClosed ℂ]` and `[Invertible (Fintype.card ↥H : ℂ)]` (both automatic
over ℂ since it is algebraically closed with characteristic 0). -/
private lemma class_fun_vanishes_on_subgroup_of_orthogonal
    {G : Type} [Group G] [Fintype G]
    (H : Subgroup G)
    (f : G → ℂ) (hf_class : ∀ g x : G, f (x * g * x⁻¹) = f g)
    (horth : ∀ (W : FDRep ℂ ↥H), CategoryTheory.Simple W →
      ∑ h : ↥H, f ↑h * W.character (h⁻¹) = 0) :
    ∀ h : ↥H, f ↑h = 0 := by
  -- It suffices to show the restriction g(h) = f(↑h) is zero as a function
  suffices hzero : (fun h : ↥H => f ↑h) = 0 by
    intro h; exact congr_fun hzero h
  -- |H| is invertible in ℂ (characteristic 0, |H| > 0)
  haveI : Invertible (Fintype.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- Apply character completeness on H (Theorem 4.2.1)
  apply Etingof.classFunction_eq_zero_of_orthogonal_simples
  · -- The restriction is a class function on H
    intro a b
    change f ↑(b * a * b⁻¹) = f ↑a
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf_class ↑a ↑b
  · -- The restriction is orthogonal to all irreducible characters of H
    intro W
    exact horth W ‹_›

/-- Trivial covering argument: if f vanishes on every subgroup in X and X covers G,
then f vanishes on all of G. -/
private lemma covering_implies_vanishing {G : Type} [Group G]
    (X : Set (Subgroup G))
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)
    (f : G → ℂ)
    (hvan : ∀ H ∈ X, ∀ h : ↥H, f ↑h = 0) :
    f = 0 := by
  ext g
  obtain ⟨H, hH, hg⟩ := hcov g
  exact hvan H hH ⟨g, hg⟩

/-- Any class function f on G that is orthogonal to all induced characters from X
(in the sense of ∑ f(g) · IndChar(g⁻¹) = 0) must also satisfy
∑ f(g) · s(g⁻¹) = 0 for all s in the ℚ-span of induced characters.
This is because the pairing is ℂ-linear in s. -/
private lemma inner_zero_of_span_mem {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (f : G → ℂ) (hf_class : ∀ g x : G, f (x * g * x⁻¹) = f g)
    (hf_orth : ∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
      ∑ g : G, f g * Etingof.inducedCharacter H W.character g⁻¹ = 0)
    (s : G → ℂ)
    (hs : s ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = Etingof.inducedCharacter H W.character}) :
    ∑ g : G, f g * s g⁻¹ = 0 := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, hH, W, rfl⟩ := hx
    exact hf_orth H hH W
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hx, hy, add_zero]
  | smul r x _ hx =>
    show ∑ g : G, f g * (r • x) g⁻¹ = 0
    have key : ∀ g : G, f g * (r • x) g⁻¹ = (r : ℂ) * (f g * x g⁻¹) := by
      intro g; show f g * r • x g⁻¹ = _; rw [show r • x g⁻¹ = (r : ℂ) * x g⁻¹ from
        Algebra.smul_def r (x g⁻¹)]; ring
    simp_rw [key, ← Finset.mul_sum, hx, mul_zero]

/-- Integer rank preservation for Artin's theorem (Remark 5.26.2):
When X covers G, every irreducible character of G lies in the ℚ-span
of induced characters from X.

Proof strategy: by contradiction using `horth_trivial`.
If V.character ∉ span_ℚ(S), we construct a nonzero class function
in the orthogonal complement of S (via the ℚ-dual of the irreducible
character space), contradicting `horth_trivial`. The key insight is
that induced characters have ℕ-coefficients when decomposed into
irreducible characters, so the inner product of a ℚ-coefficient class
function with an induced character equals a rational multiple of the
ℚ-functional applied to that induced character. -/
private lemma artin_Q_span_of_induced_chars {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X)
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)
    -- The orthogonal complement of induced characters is trivial:
    (horth_trivial : ∀ (f : G → ℂ),
      (∀ g x : G, f (x * g * x⁻¹) = f g) →
      (∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
        ∑ g : G, f g * Etingof.inducedCharacter H W.character g⁻¹ = 0) →
      f = 0)
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = Etingof.inducedCharacter H W.character} := by
  -- Abbreviation for the spanning set
  set S := {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
    f = Etingof.inducedCharacter H W.character} with hS_def
  -- Step 1: By contradiction
  by_contra hV_not_mem
  -- Step 2: Any class function orthogonal to all induced characters is zero (by horth_trivial)
  -- In particular, V.character ∉ span_ℚ(S) should lead to a contradiction.
  -- The argument: if V.character ∉ span_ℚ(S), construct a nonzero class function f
  -- with ⟨f, s⟩ = 0 for all s ∈ S, contradicting horth_trivial.
  -- This uses the integer decomposition structure of induced characters.
  --
  -- The core mathematical argument (Remark 5.26.2):
  -- 1. Each induced character ∈ ℕ-span of irreducible characters (semisimple decomposition)
  -- 2. So span_ℚ(S) ⊆ span_ℚ{irreducible characters}
  -- 3. The irreducible characters are ℂ-linearly independent (char_orthonormal)
  -- 4. Hence also ℚ-linearly independent (restrict_scalars)
  -- 5. span_ℂ(S) = span_ℂ{irred chars} (from horth_trivial)
  -- 6. Since induced chars have ℤ-coords in the irred char basis,
  --    dim_ℚ(span_ℚ(S)) ≥ dim_ℂ(span_ℂ(S)) = n = dim_ℚ(span_ℚ{irred chars})
  -- 7. So span_ℚ(S) = span_ℚ{irred chars} ∋ V.character
  --
  -- The formal proof requires helper infrastructure. We proceed by constructing
  -- a nonzero class function in the orthogonal complement of S.
  --
  -- Set up infrastructure
  classical
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  -- Enumerate irreducible representations via Wedderburn-Artin
  let D := IrrepDecomp.mk' (k := ℂ) (G := G)
  -- V is isomorphic to some column representation
  obtain ⟨j₀, ⟨hj₀⟩⟩ := D.columnFDRep_surjective V ‹_›
  -- V.character = (D.columnFDRep j₀).character (isomorphic representations have same character)
  have hV_char : V.character = (D.columnFDRep j₀).character :=
    FDRep.char_iso hj₀
  -- Key helper: each induced character lies in the ℤ-span of irreducible characters.
  -- This follows from semisimplicity (Maschke's theorem): every representation
  -- decomposes as a direct sum of irreducibles with ℕ-multiplicities.
  -- Therefore its character is an ℕ-linear combination of irreducible characters.
  have hS_in_ℤspan : ∀ s ∈ S, s ∈ Submodule.span ℤ
      (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) := by
    intro s hs
    obtain ⟨H, hHX, W, rfl⟩ := hs
    -- Setup: |H| is invertible in ℂ
    haveI : Invertible (Fintype.card ↥H : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    haveI : NeZero (Nat.card ↥H : ℂ) :=
      ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
    -- Restrict each G-irreducible to H
    let resH : Fin D.n → FDRep ℂ ↥H := fun i =>
      FDRep.of ((D.columnFDRep i).ρ.comp H.subtype)
    -- Multiplicities: m_i = dim Hom_H(W, Res_H(V_i))
    let m : Fin D.n → ℕ := fun i => Module.finrank ℂ (W ⟶ resH i)
    -- Step 1: Show IndChar = ∑ m_i • χ_i as functions G → ℂ
    suffices hsuff : Etingof.inducedCharacter H W.character =
        ∑ i : Fin D.n, (m i : ℤ) • (D.columnFDRep i).character by
      rw [hsuff]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- Step 2: Prove equality by showing difference is zero
    -- via classFunction_eq_zero_of_orthogonal_simples
    have hdiff : Etingof.inducedCharacter H W.character -
        ∑ i : Fin D.n, (m i : ℤ) • (D.columnFDRep i).character = 0 := by
      apply Etingof.classFunction_eq_zero_of_orthogonal_simples
      · -- The difference is a class function
        intro g x
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
        congr 1
        · -- IndChar is a class function (reindex y ↦ x⁻¹y in the sum)
          show Etingof.inducedCharacter H W.character (x * g * x⁻¹) =
               Etingof.inducedCharacter H W.character g
          simp only [Etingof.inducedCharacter]
          congr 1
          let φ : G ≃ G :=
            { toFun := fun y => x * y
              invFun := fun z => x⁻¹ * z
              left_inv := fun y => by group
              right_inv := fun z => by group }
          rw [← Equiv.sum_comp φ]
          apply Finset.sum_congr rfl
          intro y _
          -- (xy)⁻¹(xgx⁻¹)(xy) = y⁻¹gy, so the dite terms match
          have dite_eq : ∀ (a b : G) (hab : a = b),
              (if h : a ∈ H then W.character ⟨a, h⟩ else 0) =
              (if h : b ∈ H then W.character ⟨b, h⟩ else 0) := by
            rintro a b rfl; rfl
          exact dite_eq _ _ (by change (x * y)⁻¹ * (x * g * x⁻¹) * (x * y) = y⁻¹ * g * y; group)
        · -- ∑ m_i • χ_i is a class function
          congr 1; ext i; congr 1
          exact FDRep.char_conj (D.columnFDRep i) g x
      · -- Orthogonal to all simple characters
        intro V' hV'
        obtain ⟨j, ⟨iso_j⟩⟩ := D.columnFDRep_surjective V' hV'
        rw [FDRep.char_iso iso_j]
        -- Need: ∑_g (IndChar(g) - ∑_i m_i χ_i(g)) * χ_j(g⁻¹) = 0
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, sub_mul,
          Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        -- Character orthonormality on G
        haveI (i : Fin D.n) : CategoryTheory.Simple (D.columnFDRep i) :=
          D.columnFDRep_simple i
        have horth_G : ∀ i : Fin D.n,
            ∑ g : G, (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ =
            if i = j then (Fintype.card G : ℂ) else 0 := by
          intro i
          have h := FDRep.char_orthonormal (D.columnFDRep i) (D.columnFDRep j)
          rw [smul_eq_mul] at h
          have hinv : ∀ (x y : ℂ), ⅟(Fintype.card G : ℂ) * x = y →
              x = (Fintype.card G : ℂ) * y := fun x y h => by
            rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl]
            exact (hinv _ _ (by rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h; exact h)).trans
              (mul_one _)
          · rw [if_neg hij]
            exact (hinv _ _ (by rw [if_neg (fun ⟨iso⟩ => hij
              (D.columnFDRep_injective i j ⟨iso⟩))] at h; exact h)).trans (mul_zero _)
        -- Both sides equal ↑(m j) * |G|
        -- LHS: via g ↦ g⁻¹ substitution + Frobenius reciprocity + scalar product
        -- RHS: via character orthonormality
        trans (↑(m j) * (Fintype.card G : ℂ))
        · -- LHS = m_j * |G|
          -- Reindex: ∑_g IndChar(g) * χ_j(g⁻¹) = ∑_g χ_j(g) * IndChar(g⁻¹)
          have lhs_sub : ∑ g : G,
              Etingof.inducedCharacter H W.character g *
                (D.columnFDRep j).character g⁻¹ =
              ∑ g : G, (D.columnFDRep j).character g *
                Etingof.inducedCharacter H W.character g⁻¹ := by
            rw [← Equiv.sum_comp (Equiv.inv G)]
            congr 1; ext g; simp [mul_comm]
          have hfrob := frobenius_char_reciprocity H (D.columnFDRep j).character W.character
            (fun g x => FDRep.char_conj (D.columnFDRep j) g x)
          rw [lhs_sub, hfrob]
          -- Rewrite χ_j(↑h) with (resH j).char(h)
          have hlhs_rw : ∑ h : ↥H, (D.columnFDRep j).character (↑h : G) * W.character h⁻¹ =
              ∑ h : ↥H, (resH j).character h * W.character h⁻¹ :=
            Finset.sum_congr rfl (fun h _ => rfl)
          rw [hlhs_rw]
          -- scalar_product_char_eq_finrank_equivariant on H
          have hmult : ⅟(Fintype.card ↥H : ℂ) •
              ∑ h : ↥H, (resH j).character h * W.character h⁻¹ = ↑(m j) := by
            have := FDRep.scalar_product_char_eq_finrank_equivariant W (resH j)
            rw [smul_eq_mul] at this ⊢
            convert this using 1
          -- Extract: ∑_h = |H| * m_j
          have hsum_H : ∑ h : ↥H, (resH j).character h * W.character h⁻¹ =
              (Fintype.card ↥H : ℂ) * ↑(m j) := by
            rw [smul_eq_mul] at hmult
            calc _ = (Fintype.card ↥H : ℂ) * (⅟(Fintype.card ↥H : ℂ) *
                ∑ h : ↥H, (resH j).character h * W.character h⁻¹) := by
                  rw [← mul_assoc, mul_invOf_self, one_mul]
              _ = _ := by rw [hmult]
          rw [hsum_H]
          have hH_ne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          field_simp
        · -- RHS = m_j * |G| (via char orthonormality)
          symm
          simp only [zsmul_eq_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc, ← Finset.mul_sum, horth_G, mul_ite, mul_zero]
          simp [Finset.sum_ite_eq', Finset.mem_univ]
    exact sub_eq_zero.mp hdiff
  -- Irreducible characters are ℂ-linearly independent (from char_orthonormal + non-isomorphism)
  have h_li_C : LinearIndependent ℂ (fun i : Fin D.n => (D.columnFDRep i).character) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    -- From hc: ∑ i, c i • (D.columnFDRep i).character = 0
    -- We extract c j by taking the inner product with χ_j
    -- ⅟|G| • ∑ g, (∑ i, c i • χ_i)(g) • χ_j(g⁻¹) = c j
    -- Each columnFDRep i is simple
    haveI (i : Fin D.n) : CategoryTheory.Simple (D.columnFDRep i) := D.columnFDRep_simple i
    -- Iso iff equal index
    have h_iso_iff : ∀ i k : Fin D.n,
        Nonempty ((D.columnFDRep i) ≅ (D.columnFDRep k)) ↔ i = k := by
      intro i k
      constructor
      · exact D.columnFDRep_injective i k
      · rintro rfl; exact ⟨CategoryTheory.Iso.refl _⟩
    -- Apply inner product with χ_j: extract c_j from the linear combination
    -- Use char_orthonormal: ⅟|G| • ∑_g χ_i(g) * χ_j(g⁻¹) = δ_{ij}
    have h_orth : ∀ i : Fin D.n,
        ⅟(Fintype.card G : ℂ) • ∑ g : G,
          (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ =
        if i = j then 1 else 0 := by
      intro i
      rw [FDRep.char_orthonormal]
      simp [h_iso_iff]
    -- From hc: ∑ c_i • χ_i = 0, evaluate at each g
    have lhs_zero : ∀ g, (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) = 0 := by
      intro g
      have := congr_fun hc g
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this
    -- Compute: 0 = ⅟|G| • ∑_g 0 * χ_j(g⁻¹) = ⅟|G| • ∑_g (∑_i c_i χ_i(g)) * χ_j(g⁻¹)
    --        = ∑_i c_i * (⅟|G| • ∑_g χ_i(g) * χ_j(g⁻¹)) = ∑_i c_i * δ_{ij} = c_j
    -- Step A: ⅟|G| • ∑_g (∑_i c_i χ_i(g)) * χ_j(g⁻¹) = 0
    have stepA : ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) *
        (D.columnFDRep j).character g⁻¹ = 0 := by
      simp_rw [lhs_zero, zero_mul, Finset.sum_const_zero, smul_zero]
    -- Step B: Rearrange LHS to ∑_i c_i * (⅟|G| • ∑_g χ_i(g) * χ_j(g⁻¹))
    have stepB : ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) *
        (D.columnFDRep j).character g⁻¹ =
        ∑ i : Fin D.n, c i * (⅟(Fintype.card G : ℂ) • ∑ g : G,
          (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹) := by
      calc ⅟(Fintype.card G : ℂ) • ∑ g : G,
              (∑ i, c i * (D.columnFDRep i).character g) * (D.columnFDRep j).character g⁻¹
          _ = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i,
              c i * (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ := by
            congr 1; apply Finset.sum_congr rfl; intro g _; rw [Finset.sum_mul]
          _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ g : G,
              c i * (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ := by
            congr 1; rw [Finset.sum_comm]
          _ = ⅟(Fintype.card G : ℂ) • ∑ i,
              c i * ∑ g : G, (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ := by
            congr 1; apply Finset.sum_congr rfl; intro i _
            conv_lhs => arg 2; ext g; rw [mul_assoc]
            rw [← Finset.mul_sum]
          _ = ∑ i, c i * (⅟(Fintype.card G : ℂ) •
              ∑ g : G, (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [Algebra.mul_smul_comm]
    -- Step C: Use h_orth to simplify
    simp_rw [stepB, h_orth] at stepA
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at stepA
    exact stepA
  -- Therefore also ℚ-linearly independent
  have h_li_Q : LinearIndependent ℚ (fun i : Fin D.n => (D.columnFDRep i).character) :=
    h_li_C.restrict_scalars (smul_left_injective ℚ one_ne_zero)
  -- span_ℚ(S) ⊆ span_ℚ{irred chars}
  have hS_sub_Q : Submodule.span ℚ S ≤ Submodule.span ℚ
      (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) := by
    apply Submodule.span_le.mpr
    intro s hs
    exact Submodule.span_mono (by intro x ⟨i, hi⟩; exact ⟨i, hi⟩)
      (Submodule.span_le_restrictScalars (R := ℤ) (S := ℚ) _ (hS_in_ℤspan s hs))
  -- V.character ∈ span_ℚ{irred chars} (it IS one of the irred chars)
  have hV_in_Q : V.character ∈ Submodule.span ℚ
      (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) := by
    rw [hV_char]
    exact Submodule.subset_span ⟨j₀, rfl⟩
  -- Derive contradiction using a separating ℚ-linear functional.
  -- Since V.char ∉ span_ℚ(S), there exists ℓ vanishing on span_ℚ(S) with ℓ(V.char) ≠ 0.
  -- We construct f = ∑_i (ℓ(χ_i) : ℂ) • χ_i, show f is orthogonal to all induced chars
  -- (using character orthonormality + ℓ(Ind) = 0), then horth_trivial gives f = 0,
  -- contradicting f ≠ 0 (from ℓ(V.char) ≠ 0 + ℂ-linear independence).
  obtain ⟨ℓ, hℓ_ne, hℓ_ker⟩ := Submodule.exists_le_ker_of_notMem hV_not_mem
  -- ℓ vanishes on each s ∈ S
  have hℓS : ∀ s ∈ S, ℓ s = 0 := fun s hs =>
    LinearMap.mem_ker.mp (hℓ_ker (Submodule.subset_span hs))
  -- Define f = ∑_i (ℓ(χ_i) : ℂ) • χ_i
  let c : Fin D.n → ℂ := fun i =>
    algebraMap ℚ ℂ (ℓ ((D.columnFDRep i).character))
  -- Character orthonormality at scale |G|
  haveI (i : Fin D.n) : CategoryTheory.Simple (D.columnFDRep i) := D.columnFDRep_simple i
  have horth_G2 : ∀ i j : Fin D.n,
      ∑ g : G, (D.columnFDRep i).character g * (D.columnFDRep j).character g⁻¹ =
      if i = j then (Fintype.card G : ℂ) else 0 := by
    intro i j
    have h := FDRep.char_orthonormal (D.columnFDRep i) (D.columnFDRep j)
    rw [smul_eq_mul] at h
    have hinv : ∀ (x y : ℂ), ⅟(Fintype.card G : ℂ) * x = y →
        x = (Fintype.card G : ℂ) * y := fun x y h => by
      rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]
      exact (hinv _ _ (by rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h; exact h)).trans
        (mul_one _)
    · rw [if_neg hij]
      exact (hinv _ _ (by rw [if_neg (fun ⟨iso⟩ => hij
        (D.columnFDRep_injective i j ⟨iso⟩))] at h; exact h)).trans (mul_zero _)
  -- Key: ⟨f, s⟩ = |G| * algebraMap ℚ ℂ (ℓ s) for s ∈ span_ℤ{χ_i}
  have hf_inner_span : ∀ s : G → ℂ,
      s ∈ Submodule.span ℤ (Set.range (fun i : Fin D.n => (D.columnFDRep i).character)) →
      ∑ g : G, (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) * s g⁻¹ =
      (Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ s) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      conv_lhs => arg 2; ext g; rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, horth_G2, mul_ite, mul_zero]
      simp [Finset.sum_ite_eq', Finset.mem_univ, c, mul_comm]
    | zero => simp [map_zero]
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add, _root_.map_add]
      rw [hx, hy]
    | smul n x _ hx =>
      -- LHS: ∑_g (∑_i c_i χ_i(g)) * (n • x)(g⁻¹) = (n : ℂ) * ∑_g ... * x(g⁻¹)
      have lhs_eq : ∑ g : G, (∑ i, c i * (D.columnFDRep i).character g) * (n • x) g⁻¹ =
          (n : ℂ) * ∑ g, (∑ i, c i * (D.columnFDRep i).character g) * x g⁻¹ := by
        simp only [Pi.smul_apply, zsmul_eq_mul, mul_left_comm _ (n : ℂ)]
        rw [← Finset.mul_sum]
      -- RHS: |G| * alg(ℓ(n • x)) = (n : ℂ) * |G| * alg(ℓ(x))
      have rhs_eq : (Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ (n • x)) =
          (n : ℂ) * ((Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ x)) := by
        rw [map_zsmul ℓ, zsmul_eq_mul, _root_.map_mul, map_intCast]; ring
      rw [lhs_eq, hx, rhs_eq]
  -- f is orthogonal to each induced char (since ℓ(Ind) = 0)
  have hf_orth : ∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
      ∑ g : G, (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) *
        Etingof.inducedCharacter H W.character g⁻¹ = 0 := by
    intro H hH W
    rw [hf_inner_span _ (hS_in_ℤspan _ ⟨H, hH, W, rfl⟩),
      hℓS _ ⟨H, hH, W, rfl⟩, map_zero, mul_zero]
  -- f is a class function
  have hf_class : ∀ g x : G,
      (∑ i : Fin D.n, c i * (D.columnFDRep i).character (x * g * x⁻¹)) =
      (∑ i : Fin D.n, c i * (D.columnFDRep i).character g) := by
    intro g x; congr 1; ext i; congr 1; exact FDRep.char_conj _ _ _
  -- Apply horth_trivial to get f = 0
  have hf_zero := horth_trivial
    (fun g => ∑ i : Fin D.n, c i * (D.columnFDRep i).character g) hf_class hf_orth
  -- But ℓ(V.char) ≠ 0, so c j₀ ≠ 0
  have hc_ne : c j₀ ≠ 0 := by
    simp only [c, ← hV_char]
    intro h; exact hℓ_ne ((algebraMap ℚ ℂ).injective (by rwa [map_zero]))
  -- f = 0 as a function, so the coefficients c_i are all zero by ℂ-linear independence
  rw [Fintype.linearIndependent_iff] at h_li_C
  exact absurd (h_li_C c (by ext g; simpa [smul_eq_mul] using congr_fun hf_zero g) j₀) hc_ne

/-- Forward direction of Artin's theorem: if X covers G, every irreducible character
is in the ℚ-span of induced characters from X.

Proof outline (Etingof, Theorem 5.26.1):
1. By `frobenius_char_reciprocity`: if f is orthogonal to all Ind_H^G(W), then
   f|_H is orthogonal to all irreducible characters of H (up to a nonzero scalar).
2. By `class_fun_vanishes_on_subgroup_of_orthogonal`: f vanishes on H.
3. By `covering_implies_vanishing`: since X covers G, f vanishes on all of G.
4. Steps 1-3 show the orthogonal complement of induced characters is trivial.
5. By `artin_Q_span_of_induced_chars` (Remark 5.26.2): the ℚ-span of induced
   characters contains all irreducible characters.

All helpers are fully proved: `frobenius_char_reciprocity`,
`covering_implies_vanishing`, `class_fun_vanishes_on_subgroup_of_orthogonal`,
and `artin_Q_span_of_induced_chars`. -/
private lemma artin_forward {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X)
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = Etingof.inducedCharacter H W.character} := by
  apply artin_Q_span_of_induced_chars X hX hcov
  -- Prove the orthogonal complement of induced characters is trivial
  intro f hf_class hf_orth
  -- Step 1: For each H ∈ X, f|_H is orthogonal to all irreducible chars of H
  -- (by frobenius_char_reciprocity, the inner product is proportional)
  -- Step 2: By class_fun_vanishes_on_subgroup_of_orthogonal, f vanishes on each H
  have hvan : ∀ H ∈ X, ∀ h : ↥H, f ↑h = 0 := by
    intro H hHX
    apply class_fun_vanishes_on_subgroup_of_orthogonal H f hf_class
    intro W hW
    -- Need: ∑ h : ↥H, f ↑h * W.character (h⁻¹) = 0
    -- From frobenius_char_reciprocity:
    --   ∑ g : G, f g * (Ind_H^G χ_W)(g⁻¹) = (|G|/|H|) · ∑ h : ↥H, f ↑h * χ_W(h⁻¹)
    -- The LHS = 0 by hf_orth. Since |G|/|H| ≠ 0, the RHS sum = 0.
    classical
    have hfrob := frobenius_char_reciprocity H f W.character hf_class
    have hzero := hf_orth H hHX W
    rw [hzero] at hfrob
    -- hfrob : 0 = (|G| : ℂ) * (|H| : ℂ)⁻¹ * ∑ h, f ↑h * W.character (h⁻¹)
    have hG_ne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hH_ne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hcoeff_ne : (Fintype.card G : ℂ) * (Fintype.card ↥H : ℂ)⁻¹ ≠ 0 :=
      mul_ne_zero hG_ne (inv_ne_zero hH_ne)
    -- hfrob : 0 = coeff * ∑ h, ...
    -- Need: ∑ h, ... = 0
    exact mul_left_cancel₀ hcoeff_ne (by rw [mul_zero]; exact hfrob.symm)
  -- Step 3: By covering, f = 0 on all of G
  exact covering_implies_vanishing X hcov f hvan

/-- The trivial representation of G on ℂ: every group element acts as the identity. -/
private def trivialRep (G : Type) [Group G] : Representation ℂ G ℂ := 1

/-- The trivial FDRep: the 1-dimensional representation where G acts trivially. -/
private def trivialFDRep (G : Type) [Group G] [Fintype G] : FDRep ℂ G :=
  FDRep.of (trivialRep G)

/-- The character of the trivial representation equals 1 at every group element. -/
private theorem trivialFDRep_character (G : Type) [Group G] [Fintype G] (g : G) :
    (trivialFDRep G).character g = 1 := by
  change LinearMap.trace ℂ _ ((trivialRep G) g) = 1
  simp [trivialRep, MonoidHom.one_apply, LinearMap.trace_one, Module.finrank_self]

open CategoryTheory in
/-- A full faithful functor preserving monomorphisms reflects Simple objects. -/
private lemma simple_of_full_faithful_preservesMono
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

open CategoryTheory in
/-- The trivial FDRep is simple (irreducible). -/
private theorem trivialFDRep_simple (G : Type) [Group G] [Fintype G] :
    Simple (trivialFDRep G) := by
  -- Step 1: The asModule of the trivial representation is a simple k[G]-module
  -- (1-dimensional over ℂ, so any nonzero submodule is everything)
  let ρ := trivialRep G
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule := by
    rw [isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one (Module.finrank_self ℂ)
  -- Step 2: Transfer to Simple in ModuleCat
  haveI : Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule) :=
    simple_of_isSimpleModule
  -- Step 3: Transfer through Rep.equivalenceModuleMonoidAlgebra
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)
  haveI : Simple
      (E.functor.obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (trivialFDRep G))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule)
    infer_instance
  haveI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (trivialFDRep G)) :=
    simple_of_full_faithful_preservesMono E.functor _
  exact simple_of_full_faithful_preservesMono (forget₂ (FDRep ℂ G) (Rep ℂ G)) _

/-- Artin's theorem: a conjugation-invariant system of subgroups X covers G
iff every irreducible character is a ℚ-linear combination of induced
characters from subgroups in X.

The hypothesis `hX` asserts that X is closed under conjugation:
for every H ∈ X and g ∈ G, the conjugate gHg⁻¹ also belongs to X.

Condition (i) states that X covers G: every element belongs to some H ∈ X.

Condition (ii) states that for every irreducible representation V of G,
V.character lies in the ℚ-span of {Ind_H^G(W).character | H ∈ X, W ∈ Rep(H)}.
(Etingof Theorem 5.26.1) -/
theorem Etingof.Theorem5_26_1
    (G : Type) [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X) :
    (∀ g : G, ∃ H ∈ X, g ∈ H) ↔
    (∀ (V : FDRep ℂ G), CategoryTheory.Simple V →
      V.character ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = Etingof.inducedCharacter H W.character}) := by
  constructor
  · -- Forward direction: covering → span
    -- By Frobenius reciprocity + covering, the ℂ-span of induced characters
    -- contains all class functions. By Remark 5.26.2, ℚ-span = ℂ-span for this set.
    intro hcov V hV
    exact artin_forward X hX hcov V
  · -- Backward direction: span → covering (by contrapositive)
    -- If some g₀ is not covered by X, all induced characters vanish at g₀
    -- (since X is conjugation-invariant), so the span vanishes at g₀.
    -- But the trivial character equals 1 at g₀, contradiction.
    intro hspan
    by_contra hncov
    push_neg at hncov
    obtain ⟨g₀, hg₀⟩ := hncov
    -- Step 1: No conjugate of g₀ lies in any H ∈ X
    have hconj_out : ∀ H ∈ X, ∀ x : G, x⁻¹ * g₀ * x ∉ H := by
      intro H hHX x hmem
      have : g₀ ∈ H.map (MulAut.conj x).toMonoidHom := by
        apply Subgroup.mem_map.mpr
        refine ⟨x⁻¹ * g₀ * x, hmem, ?_⟩
        change x * (x⁻¹ * g₀ * x) * x⁻¹ = g₀
        group
      exact hg₀ _ (hX H hHX x) this
    -- Step 2: All induced characters vanish at g₀
    have hgen_vanish : ∀ f ∈ ({f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = Etingof.inducedCharacter H W.character} : Set (G → ℂ)),
        f g₀ = 0 := by
      rintro f ⟨H, hHX, W, rfl⟩
      classical
      simp only [Etingof.inducedCharacter]
      suffices h : ∑ x : G, (if h : x⁻¹ * g₀ * x ∈ H
          then W.character ⟨x⁻¹ * g₀ * x, h⟩ else 0) = 0 by
        rw [h, mul_zero]
      apply Finset.sum_eq_zero
      intro x _
      exact dif_neg (hconj_out H hHX x)
    -- Step 3: All functions in the ℚ-span vanish at g₀
    have hspan_vanish : ∀ f ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = Etingof.inducedCharacter H W.character},
        f g₀ = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx => exact hgen_vanish x hx
      | zero => rfl
      | add x y _ _ hx hy => simp [Pi.add_apply, hx, hy]
      | smul r x _ hx => simp [Pi.smul_apply, hx]
    -- Step 4: The trivial character is in the span (by hypothesis) but equals 1 at g₀
    have hmem := hspan (trivialFDRep G) (trivialFDRep_simple G)
    have hval := hspan_vanish _ hmem
    rw [trivialFDRep_character] at hval
    exact one_ne_zero hval
