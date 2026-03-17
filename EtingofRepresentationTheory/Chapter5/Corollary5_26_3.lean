import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_26_1

/-!
# Corollary 5.26.3: Characters from Cyclic Subgroups

Any irreducible character of a finite group is a rational linear combination
of induced characters from its cyclic subgroups.

This follows from Artin's theorem (Theorem 5.26.1) applied to the system
X = {⟨g⟩ | g ∈ G} of all cyclic subgroups, which is conjugation-invariant
and covers G (since every g belongs to ⟨g⟩).

## Mathlib correspondence

Uses `Subgroup.zpowers` for cyclic subgroups, `FDRep.character` for characters,
and `Submodule.span ℚ` for the ℚ-linear span. The induced character is
computed via the Frobenius formula.
-/

noncomputable section

open Classical in
/-- The character of the induced representation Ind_H^G W, computed via the
Frobenius character formula. (See Theorem 5.26.1 for details.) -/
def Etingof.inducedCharacter' {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : ↥H → ℂ) : G → ℂ :=
  fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ x : G, if h : x⁻¹ * g * x ∈ H then χ ⟨x⁻¹ * g * x, h⟩ else 0

/-- Any irreducible character of a finite group is a ℚ-linear combination of
characters induced from cyclic subgroups.

For each g ∈ G, `Subgroup.zpowers g` is the cyclic subgroup ⟨g⟩. The set of
all such subgroups covers G and is conjugation-invariant, so by Artin's theorem
(Theorem 5.26.1), every irreducible character lies in the ℚ-span of characters
induced from cyclic subgroups. (Etingof Corollary 5.26.3) -/
theorem Etingof.Corollary5_26_3
    (G : Type) [Group G] [Fintype G]
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ (g : G) (W : FDRep ℂ ↥(Subgroup.zpowers g)),
        f = Etingof.inducedCharacter' (Subgroup.zpowers g) W.character} := by
  -- Apply Artin's theorem with X = set of all cyclic subgroups
  have hX_conj : ∀ H ∈ ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} : Set (Subgroup G)),
      ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈
        ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} : Set (Subgroup G)) := by
    rintro H ⟨a, rfl⟩ g
    exact ⟨g * a * g⁻¹, by rw [MonoidHom.map_zpowers]; rfl⟩
  have hcover : ∀ g : G, ∃ H ∈ ({H : Subgroup G | ∃ g : G, H = Subgroup.zpowers g} :
      Set (Subgroup G)), g ∈ H :=
    fun g => ⟨Subgroup.zpowers g, ⟨g, rfl⟩, Subgroup.mem_zpowers g⟩
  have artin := (Etingof.Theorem5_26_1 G _ hX_conj).mp hcover V ‹_›
  -- Convert span sets: theorem uses inducedCharacter, corollary uses inducedCharacter'
  apply Submodule.span_mono _ artin
  rintro f ⟨H, ⟨g, rfl⟩, W, rfl⟩
  exact ⟨g, W, by unfold Etingof.inducedCharacter Etingof.inducedCharacter'; rfl⟩
