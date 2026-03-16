import Mathlib

/-!
# Theorem 4.1.1: Maschke's Theorem

**Maschke's theorem.** Let G be a finite group and k a field whose characteristic does
not divide |G|. Then:

(i) The group algebra k[G] is semisimple.

(ii) There is an isomorphism k[G] ≅ ⊕ᵢ End(Vᵢ), where Vᵢ are all the irreducible
representations of G. Moreover, the regular representation decomposes as
k[G] ≅ ⊕ᵢ Vᵢ^(dim Vᵢ), giving the dimension formula |G| = Σᵢ (dim Vᵢ)².

## Mathlib correspondence

Mathlib has `IsSemisimpleRing` and `MonoidAlgebra.instIsSemisimpleRing` for part (i).
The decomposition and dimension formula require additional work.
-/

/-- Maschke's theorem, part (i): The group algebra k[G] is semisimple when the
characteristic of k does not divide |G|. (Etingof Theorem 4.1.1) -/
theorem Etingof.Theorem4_1_1_semisimple
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    [DecidableEq G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  sorry

/-- Maschke's theorem, part (ii): The sum-of-squares formula |G| = Σᵢ (dim Vᵢ)².
(Etingof Theorem 4.1.1) -/
theorem Etingof.Theorem4_1_1_sum_of_squares
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    [DecidableEq G] :
    -- The sum of squares of dimensions of irreducible representations equals |G|
    -- TODO: State precisely once irreducible rep enumeration is available
    True := by
  trivial
