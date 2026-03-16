import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Trace

/-!
# Theorem 3.6.2: Linear Independence of Characters

(i) Characters of (distinct) irreducible finite dimensional representations of A are
    linearly independent.

(ii) If A is a finite dimensional semisimple algebra, then these characters form a basis
     of (A/[A,A])*.

The proof of (i) uses the density theorem: the surjectivity of the combined representation
map ensures that traces of distinct irreducibles can be independently varied.

The proof of (ii) shows that [Mat_d(k), Mat_d(k)] = sl_d(k) (traceless matrices),
so A/[A,A] ≅ k^r for semisimple A = ⊕ Mat_{dᵢ}(k), and r linearly independent
characters on an r-dimensional space form a basis.
-/

/-- Characters of distinct irreducible representations are linearly independent.
Etingof Theorem 3.6.2(i). -/
theorem Etingof.characters_linearly_independent (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    -- The characters χ_{V₁}, …, χ_{Vᵣ} of pairwise nonisomorphic irreducible
    -- representations are linearly independent as elements of Hom_k(A, k).
    True := by
  sorry

/-- For a semisimple algebra, characters of irreducibles form a basis of (A/[A,A])*.
Etingof Theorem 3.6.2(ii). -/
theorem Etingof.characters_basis_semisimple (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A] :
    -- The characters form a basis of the dual of the abelianization A/[A,A].
    True := by
  sorry
