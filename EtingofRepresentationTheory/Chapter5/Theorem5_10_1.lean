import Mathlib

/-!
# Theorem 5.10.1: Frobenius Reciprocity

For a subgroup H ≤ G, a representation V of G, and a representation W of H,
there is a natural isomorphism:

  Hom_G(V, Ind_H^G W) ≅ Hom_H(Res_H^G V, W)

This is the fundamental adjunction between induction and restriction functors.

## Mathlib correspondence

Mathlib has `Representation.ofMulAction` and basic representation theory, but
the induction/restriction adjunction for group representations may not be
fully formalized. The categorical adjunction `Ind ⊣ Res` is the key statement.
-/

/-- Frobenius reciprocity: Hom_G(V, Ind_H^G W) ≅ Hom_H(Res V, W).
(Etingof Theorem 5.10.1) -/
theorem Etingof.Theorem5_10_1
    (k : Type*) [Field k]
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H]
    (V : Type*) [AddCommGroup V] [Module k V]
    (W : Type*) [AddCommGroup W] [Module k W]
    (ρ : Representation k G V)
    (σ : Representation k (↥H) W) :
    -- Hom_G(V, Ind_H^G W) ≅ Hom_H(Res V, W) as k-vector spaces
    (sorry : Prop) := by
  sorry
