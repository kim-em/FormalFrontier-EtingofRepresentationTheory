import Mathlib

/-!
# Theorem 5.23.2: Complete Reducibility and Peter-Weyl for GL(V)

(i) Every finite dimensional algebraic representation of GL(V) is completely
reducible and decomposes into summands Lλ (which are pairwise nonisomorphic).

(ii) (Peter-Weyl for GL(V)) The algebra R of polynomial functions on GL(V),
as a representation of GL(V) × GL(V), decomposes as:
  R ≅ ⊕_λ L*λ ⊗ Lλ

## Mathlib correspondence

Complete reducibility for semisimple groups is partially in Mathlib.
The Peter-Weyl decomposition for GL(V) is not.
-/

/-- Every finite dimensional algebraic representation of GL(V) is completely
reducible, decomposing into pairwise nonisomorphic summands Lλ.
(Etingof Theorem 5.23.2, part i) -/
theorem Etingof.Theorem5_23_2_i
    {k : Type*} [Field k] [IsAlgClosed k]
    (n : ℕ) :
    -- Every algebraic representation of GL_n(k) is completely reducible
    (sorry : Prop) := by
  sorry

/-- Peter-Weyl theorem for GL(V): the algebra of polynomial functions on GL(V)
decomposes as R ≅ ⊕_λ L*λ ⊗ Lλ under the GL(V) × GL(V) action.
(Etingof Theorem 5.23.2, part ii) -/
theorem Etingof.Theorem5_23_2_ii
    {k : Type*} [Field k] [IsAlgClosed k]
    (n : ℕ) :
    -- R = ⊕_λ L*λ ⊗ Lλ as GL(V) × GL(V) representations
    (sorry : Prop) := by
  sorry
