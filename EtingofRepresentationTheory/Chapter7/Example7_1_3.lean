import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Example 7.1.3: Examples of Categories

1. The category **Sets** of sets (morphisms are arbitrary maps).
2. The categories **Groups**, **Rings** (morphisms are homomorphisms).
3. The category Vect_k of vector spaces over a field k (morphisms are linear maps).
4. The category Rep(A) of representations of an algebra A (= A-mod).
5. The category of topological spaces (morphisms are continuous maps).

## Mathlib correspondence

All of these categories exist in Mathlib as bundled categories.
-/

open CategoryTheory

/-- The category of types (Sets). (Etingof Example 7.1.3(1)) -/
example : Category (Type*) := inferInstance

/-- The category of groups. (Etingof Example 7.1.3(2)) -/
example : Category GrpCat := inferInstance

/-- The category of rings. (Etingof Example 7.1.3(2)) -/
example : Category RingCat := inferInstance

/-- The category of k-vector spaces (= k-modules). (Etingof Example 7.1.3(3)) -/
example (k : Type*) [Field k] : Category (ModuleCat k) := inferInstance

/-- The category of left A-modules (= Rep(A)). (Etingof Example 7.1.3(4)) -/
example (A : Type*) [Ring A] : Category (ModuleCat A) := inferInstance

/-- The category of topological spaces. (Etingof Example 7.1.3(5)) -/
example : Category TopCat := inferInstance
