import Mathlib

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.

## Formalization note

This theorem is equivalent to Gabriel's theorem (Theorem 6.5.2). It connects the
representation-theoretic property (finite type) with the combinatorial property
(Dynkin diagram). The statement is sorry'd pending development of quiver
representation theory infrastructure.
-/

/-- A connected quiver Q is of finite type (finitely many indecomposable representations)
if and only if its underlying unoriented graph is a Dynkin diagram.
(Etingof Problem 6.1.5 Theorem) -/
theorem Etingof.Theorem_6_1_5 : (sorry : Prop) := sorry
