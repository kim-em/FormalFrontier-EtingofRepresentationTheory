import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Theorem 5.1.5: Frobenius-Schur Theorem (Involution Count)

The number of involutions (elements g with g² = 1) in a finite group G equals:
  Σ_V dim(V) · FS(V)
where the sum is over all irreducible representations V, and FS(V) is the
Frobenius-Schur indicator.

The proof uses the decomposition of the symmetric and exterior squares:
  χ_V(g²) = χ_{S²V}(g) - χ_{Λ²V}(g)

## Mathlib correspondence

Uses symmetric and exterior powers, character theory, and the Frobenius-Schur indicator.
-/

open FDRep CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- Frobenius-Schur indicator of an FDRep object, computed as
(1/|G|) Σ_{g∈G} χ_V(g²). -/
noncomputable def FDRep.frobeniusSchurIndicator
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, V.character (g * g)

/-- The number of involutions in G equals Σ_i dim(V_i) · FS(V_i), where the sum ranges over
irreducible representations indexed by a Wedderburn-Artin decomposition.
(Etingof Theorem 5.1.5)

The RHS uses `IrrepDecomp` to enumerate irreducible representations and
`FDRep.frobeniusSchurIndicator` for the Frobenius-Schur indicator.
Proof is blocked on `IrrepDecomp.n_eq_card_simples` (issue #655). -/
theorem Etingof.Theorem5_1_5
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.n, D.d i * (V i).frobeniusSchurIndicator := by
  sorry
