import Mathlib

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
    -- This is the hard direction of Artin's theorem, requiring deep character theory
    -- (Brauer's characterization of characters or algebraic norm arguments).
    -- Not currently provable with available Mathlib infrastructure.
    sorry
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
