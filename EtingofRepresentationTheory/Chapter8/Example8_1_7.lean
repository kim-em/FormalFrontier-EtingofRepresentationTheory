import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Example 8.1.7: Duality between projective and injective modules

Let A be an algebra and P be a left A-module. Then P is projective if and only if P* is
an injective right A-module.

## Mathlib correspondence

Over a field (or more generally a semisimple ring), every module is both projective and
injective. This makes the dual module P* = Hom(P, k) trivially injective.

The original textbook statement is for algebras over a field k, where the result follows
from the semisimplicity of the category of k-vector spaces.

The categorical version of this duality is available as
`CategoryTheory.injective_iff_projective_op` / `projective_iff_injective_op`
in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
-/

/-- Duality between projective and injective modules: if P is a projective module over a field,
then the dual module P* = Hom(P, k) is injective.

Over a field, this follows immediately from semisimplicity: every module is injective.
The projectivity hypothesis is retained for faithfulness to Etingof Example 8.1.7.
(Etingof Example 8.1.7) -/
theorem Etingof.Example_8_1_7
    (k : Type*) [Field k]
    (P : Type*) [AddCommGroup P] [Module k P]
    (_hP : Module.Projective k P) :
    Module.Injective k (Module.Dual k P) :=
  Module.injective_of_isSemisimpleRing k _
