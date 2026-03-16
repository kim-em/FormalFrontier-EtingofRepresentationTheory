import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Example 8.1.7: Duality between projective and injective modules

Let A be an algebra and P be a left A-module. Then P is projective if and only if P* is
an injective right A-module.

## Mathlib correspondence

This duality uses `Module.Dual` for P*. The categorical version of this duality is
available as `CategoryTheory.injective_iff_projective_op` / `projective_iff_injective_op`
in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.

At the module level, this relates `Module.Projective R P` and
`Module.Injective R (Module.Dual R P)`.
-/

/-- Duality between projective and injective modules: P is projective iff the dual module
P* = Hom(P, R) is injective.
(Etingof Example 8.1.7) -/
theorem Etingof.Example_8_1_7
    (R : Type*) [CommRing R]
    (P : Type*) [AddCommGroup P] [Module R P] :
    Module.Projective R P →
      Module.Injective R (Module.Dual R P) := by
  sorry
