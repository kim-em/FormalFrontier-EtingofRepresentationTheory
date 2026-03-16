import Mathlib

/-!
# Theorem 5.10.1: Frobenius Reciprocity

For a subgroup H ≤ G, a representation V of G, and a representation W of H,
there is a natural isomorphism:

  Hom_G(Ind_H^G W, V) ≅ Hom_H(W, Res_H^G V)

This is the fundamental adjunction between induction and restriction functors.

Mathlib's `Rep.indResHomEquiv` provides a k-linear equivalence between
`(Rep.ind H.subtype W ⟶ V)` and `(W ⟶ (Action.res _ H.subtype).obj V)`,
which is precisely Frobenius reciprocity stated as Ind ⊣ Res.

## Mathlib correspondence

- `Rep.indResHomEquiv` — the k-linear equivalence (Frobenius reciprocity)
- `Rep.indResAdjunction` — the categorical adjunction Ind ⊣ Res
- `Rep.ind` — the induced representation functor
- `Action.res` — the restriction functor
-/

open CategoryTheory

/-- Frobenius reciprocity: there is a k-linear equivalence
  Hom_G(Ind_H^G W, V) ≃ₗ[k] Hom_H(W, Res_H V).
This is the adjunction between the induction and restriction functors.
(Etingof Theorem 5.10.1) -/
theorem Etingof.Theorem5_10_1
    (k G : Type) [Field k] [Group G]
    (H : Subgroup G)
    (V : Rep k G) (W : Rep k ↥H) :
    Nonempty ((Rep.ind H.subtype W ⟶ V) ≃ₗ[k] (W ⟶ (Action.res _ H.subtype).obj V)) :=
  ⟨Rep.indResHomEquiv H.subtype W V⟩
