import Mathlib

/-!
# Lemma 6.4.2: Properties of the Cartan Inner Product

(1) B is positive definite (follows from the definition of Dynkin diagram).

(2) B(x, x) takes only even values for x ∈ ℤⁿ.

Proof of (2): B(x, x) = xᵀ A x = 2 Σᵢ xᵢ² + 2 Σᵢ<ⱼ aᵢⱼ xᵢ xⱼ, which is even.

## Mathlib correspondence

The positive-definiteness follows from the definition. The evenness property is a
direct computation using the structure of the Cartan matrix A = 2·Id - R.
-/

/-- (1) The bilinear form B associated to a Dynkin diagram is positive definite.
(Etingof Lemma 6.4.2(1)) -/
theorem Etingof.Lemma_6_4_2_pos_def : (sorry : Prop) := sorry

/-- (2) B(x, x) takes only even values for x ∈ ℤⁿ, where B is the bilinear form
of the Cartan matrix A = 2·Id - R. (Etingof Lemma 6.4.2(2)) -/
theorem Etingof.Lemma_6_4_2_even : (sorry : Prop) := sorry
