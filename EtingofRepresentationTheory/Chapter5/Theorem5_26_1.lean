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

/-- Integer rank preservation for Artin's theorem (Remark 5.26.2):
When X covers G, every irreducible character of G lies in the ℚ-span
of induced characters from X.

This combines:
(a) The orthogonal complement argument: by `frobenius_char_reciprocity` +
    `class_fun_vanishes_on_subgroup_of_orthogonal` + `covering_implies_vanishing`,
    any class function orthogonal to all induced characters from X vanishes identically.
    This shows the ℂ-span of induced characters = space of all class functions.
(b) The integer rank argument (Remark 5.26.2): each induced character decomposes
    as Ind_H^G(W) = ∑_V n_V · χ_V with n_V ∈ ℕ (multiplicities of irreducibles
    in the induced representation). The decomposition matrix M has ℕ entries
    and full rank over ℂ (from step (a)), hence full rank over ℚ (Cramer's rule:
    det ∈ ℤ, cofactors ∈ ℤ). So each χ_V is a ℚ-linear combination of the
    induced characters. -/
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
  sorry

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

Sorry status: 2 sorry'd helpers (`class_fun_vanishes_on_subgroup_of_orthogonal`,
`artin_Q_span_of_induced_chars`). `frobenius_char_reciprocity` and
`covering_implies_vanishing` are fully proved.
The `artin_forward` proof itself is sorry-free given the helpers. -/
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
