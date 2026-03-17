import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

universe u v

/-!
# Definition 9.6.2: Projective generator (progenerator)

An object P in an abelian category is a **projective generator** (or **progenerator**)
if P is projective and every object X in the category is a quotient of a direct sum of
copies of P.

Example: the free module A (the algebra itself) is a projective generator in the
category of finite dimensional A-modules.

## Mathlib correspondence

Mathlib has `CategoryTheory.Projective` for projective objects and
`CategoryTheory.IsSeparator` for generator-like properties. We combine projectivity
with the condition that every object admits an epimorphism from a finite biproduct
of copies of P.
-/

open CategoryTheory CategoryTheory.Limits

/-- A projective generator (progenerator) in the sense of Etingof Definition 9.6.2.
An object P is a progenerator if it is projective and every object X admits an
epimorphism from a finite biproduct of copies of P. -/
class Etingof.IsProgenerator {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : C)
    extends Projective P where
  /-- Every object admits an epimorphism from a finite biproduct of copies of P. -/
  epiFromBiproduct : ∀ (X : C), ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
    (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f
