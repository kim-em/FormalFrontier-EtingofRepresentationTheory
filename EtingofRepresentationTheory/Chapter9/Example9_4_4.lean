import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Example 9.4.4: Homological dimension of polynomial algebra (Hilbert syzygies)

By the Hilbert syzygies theorem, the homological dimension of k[x₁, …, xₙ] is n
(where k is a field).

## Mathlib correspondence

The Hilbert syzygy theorem is not yet in Mathlib.
-/

universe u

/-- The Hilbert syzygy theorem: the homological dimension of k[x₁, …, xₙ] is n.
(Etingof Example 9.4.4) -/
theorem Etingof.Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :
    Etingof.homologicalDimension (MvPolynomial (Fin n) k) = n := sorry
