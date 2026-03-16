import Mathlib

/-!
# Theorem 5.27.1: Representations of Semidirect Products

For a semidirect product G ⋉ A (where A is abelian and G acts on A):

(i) The representations V(O, U) are irreducible.
(ii) They are pairwise nonisomorphic.
(iii) They form a complete set of irreducible representations of G ⋉ A.
(iv) The character is given by:
  χ_{V(O,U)}(a, g) = (1/|G_x|) Σ_{h ∈ G : hgh⁻¹ ∈ G_x} x(h(a)) χ_U(hgh⁻¹)

Here O is an orbit of G on characters of A, U is an irreducible representation
of the stabilizer G_x, and V(O, U) = Ind_{G_x ⋉ A}^{G ⋉ A} (U ⊗ ℂ_x).

## Mathlib correspondence

Uses `SemidirectProduct`. The orbit method classification is not in Mathlib.
-/

/-- Classification of irreducible representations of semidirect products G ⋉ A:
they are parametrized by pairs (O, U) where O is a G-orbit on Â and U is an
irreducible representation of the stabilizer. (Etingof Theorem 5.27.1) -/
theorem Etingof.Theorem5_27_1
    (G A : Type*) [Group G] [CommGroup A] [Fintype G] [Fintype A]
    [DecidableEq G] [DecidableEq A]
    (φ : G →* MulAut A) :
    -- V(O, U) are irreducible, pairwise nonisomorphic, and form a complete set
    (sorry : Prop) := by
  sorry
