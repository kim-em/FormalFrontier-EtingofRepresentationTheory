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
  sorry
