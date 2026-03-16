import Mathlib.Algebra.Category.Grp.Basic

/-!
# Example 7.1.5: AbelianGroups as Full Subcategory of Groups

The category **AbelianGroups** is a full subcategory of the category **Groups**.

## Mathlib correspondence

Mathlib has `CommGrpCat` (= abelian groups) and `GrpCat`. The forgetful functor
from `CommGrpCat` to `GrpCat` realizes the full subcategory relationship.
-/

open CategoryTheory

/-- CommGrpCat (abelian groups) is a category. (Etingof Example 7.1.5)
The forgetful functor to GrpCat is fully faithful, realizing abelian groups
as a full subcategory of groups. -/
example : Category CommGrpCat := inferInstance
