import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.Lattice
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Definition 9.2.2: Projective cover

The projective module Pᵢ (from Theorem 9.2.1) is called the **projective cover** of the
simple module Mᵢ. It is the unique indecomposable projective module with a surjection
onto Mᵢ.

## Mathlib correspondence

Projective covers are not yet formalized in Mathlib. The concept would bundle a projective
module P together with a surjection P ↠ M that is essential (minimal).

Indecomposability uses `Etingof.IsIndecomposable` from Definition 2.3.8.
-/

/-- The projective cover of a module M, in the sense of Etingof Definition 9.2.2.

A projective cover consists of:
- A module `P` that is projective and indecomposable
- A surjective `R`-linear map `π : P →ₗ[R] M`

This bundles the data of the projective cover together with the surjection.
Uniqueness (up to isomorphism) is a separate theorem (part of Theorem 9.2.1). -/
structure Etingof.ProjectiveCover (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The carrier type of the projective cover -/
  P : Type*
  [addCommGroup : AddCommGroup P]
  [module : Module R P]
  [projective : Module.Projective R P]
  indecomposable : Etingof.IsIndecomposable R P
  /-- The surjection from the projective cover onto the module -/
  surjection : P →ₗ[R] M
  surjection_surjective : Function.Surjective surjection

attribute [instance] Etingof.ProjectiveCover.addCommGroup
  Etingof.ProjectiveCover.module
  Etingof.ProjectiveCover.projective
