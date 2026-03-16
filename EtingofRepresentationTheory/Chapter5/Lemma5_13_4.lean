import Mathlib

/-!
# Lemma 5.13.4: Module Homomorphisms via Idempotents

For an idempotent e in an algebra A and a left A-module M, there is a natural
isomorphism:

  Hom_A(Ae, M) ≅ eM

where eM = {em : m ∈ M} is the image of e acting on M.

This is a general algebraic fact used in the study of Specht modules.

## Mathlib correspondence

This is a standard result in module theory. Mathlib has idempotents and
module homomorphisms, but this specific statement may need to be proved.
-/

/-- For an idempotent e in algebra A, Hom_A(Ae, M) ≅ eM naturally.
(Etingof Lemma 5.13.4) -/
theorem Etingof.Lemma5_13_4
    (A : Type*) [Ring A]
    (e : A) (he : e * e = e)
    (M : Type*) [AddCommGroup M] [Module A M] :
    -- Hom_A(A·e, M) is naturally isomorphic to the image of e acting on M
    (sorry : Prop) := by
  sorry
