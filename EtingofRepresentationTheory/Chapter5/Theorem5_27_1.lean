import Mathlib

/-!
# Theorem 5.27.1: Representations of Semidirect Products

For a semidirect product G ⋉ A (where A is abelian and G acts on A via φ):

(i) The representations V(O, U) are irreducible.
(ii) They are pairwise nonisomorphic (different orbit data gives non-isomorphic reps).
(iii) They form a complete set of irreducible representations of G ⋉ A.
(iv) The character is given by:
  χ_{V(O,U)}(a, g) = (1/|G_χ|) Σ_{h ∈ G : hgh⁻¹ ∈ G_χ} χ(h(a)) χ_U(hgh⁻¹)

Here O is a G-orbit on the character group Â = Hom(A, ℂˣ), χ ∈ O is a
representative, G_χ is the stabilizer of χ under the dual G-action
(g · χ)(a) = χ(φ(g⁻¹)(a)), U is an irreducible representation of G_χ,
and V(O, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ).

## Mathlib correspondence

Uses `SemidirectProduct` for G ⋉ A, `A →* ℂˣ` for the character group Â,
`MulAut` for the G-action on A, and `FDRep.character` for characters.
The orbit method classification is not yet in Mathlib.
-/

noncomputable section

open Classical in
/-- Classification of irreducible representations of semidirect products G ⋉ A
via the orbit method: they are parametrized by pairs (O, U) where O is a
G-orbit on the character group Â and U is an irreducible representation of
the stabilizer G_χ for a representative χ ∈ O.

The statement asserts the existence of:
- A dual G-action on Â = (A →* ℂˣ) given by (g · χ)(a) = χ(φ(g⁻¹)(a))
- For each χ, a stabilizer subgroup G_χ ≤ G
- A construction V(χ, U) producing a representation of A ⋊[φ] G

satisfying irreducibility, injectivity on orbits, surjectivity onto all
irreducibles, and the explicit character formula. (Etingof Theorem 5.27.1) -/
theorem Etingof.Theorem5_27_1
    (G A : Type) [Group G] [CommGroup A] [Fintype G]
    (φ : G →* MulAut A) :
    ∃ (-- The dual G-action on Â: (g · χ)(a) = χ(φ(g⁻¹)(a))
       dualSmul : G → (A →* ℂˣ) → (A →* ℂˣ))
      (_ : ∀ g χ a, dualSmul g χ a = χ ((φ g⁻¹ : MulAut A) a))
      (-- Stabilizer G_χ = {g ∈ G | g · χ = χ}
       stab : (A →* ℂˣ) → Subgroup G)
      (_ : ∀ χ g, g ∈ stab χ ↔ dualSmul g χ = χ)
      (-- The construction V(χ, U) = Ind_{G_χ ⋉ A}^{G ⋉ A} (U ⊗ ℂ_χ)
       V : (χ : A →* ℂˣ) → FDRep ℂ ↥(stab χ) → FDRep ℂ (A ⋊[φ] G)),
      -- (i) V(χ, U) is irreducible when U is irreducible
      (∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
        CategoryTheory.Simple U → CategoryTheory.Simple (V χ U)) ∧
      -- (ii) V(χ₁, U₁) ≅ V(χ₂, U₂) implies χ₁ and χ₂ are in the same G-orbit
      (∀ (χ₁ χ₂ : A →* ℂˣ)
        (U₁ : FDRep ℂ ↥(stab χ₁)) (U₂ : FDRep ℂ ↥(stab χ₂)),
        CategoryTheory.Simple U₁ → CategoryTheory.Simple U₂ →
        Nonempty (V χ₁ U₁ ≅ V χ₂ U₂) →
        ∃ g : G, dualSmul g χ₁ = χ₂) ∧
      -- (iii) Every irreducible representation of A ⋊[φ] G arises as V(χ, U)
      (∀ (W : FDRep ℂ (A ⋊[φ] G)), CategoryTheory.Simple W →
        ∃ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
          CategoryTheory.Simple U ∧ Nonempty (W ≅ V χ U)) ∧
      -- (iv) Character formula
      (∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
        CategoryTheory.Simple U →
        ∀ (a : A) (g : G),
          (V χ U).character ⟨a, g⟩ =
            (Fintype.card ↥(stab χ) : ℂ)⁻¹ *
              ∑ h : G, if hh : h * g * h⁻¹ ∈ stab χ
                then (χ ((φ h : MulAut A) a) : ℂ) *
                  U.character ⟨h * g * h⁻¹, hh⟩
                else 0) := by
  sorry
