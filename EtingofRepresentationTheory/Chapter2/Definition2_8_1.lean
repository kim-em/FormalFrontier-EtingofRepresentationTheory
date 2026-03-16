import Mathlib.Combinatorics.Quiver.Basic

/-!
# Definition 2.8.1: Quiver

A **quiver** Q is a directed graph, possibly with self-loops and/or multiple edges
between two vertices.

## Mathlib correspondence

This is exactly `Quiver V` — a typeclass providing `Hom : V → V → Sort*`.
-/

/-- A quiver, in the sense of Etingof Definition 2.8.1.
This is `Quiver V` in Mathlib. -/
abbrev Etingof.QuiverDef (V : Type*) := Quiver V
