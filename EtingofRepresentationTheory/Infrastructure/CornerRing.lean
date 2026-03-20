import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Corner rings (eAe)

For an idempotent element `e` in a ring `A`, the **corner ring** `eAe` is the set
`{e * a * e | a : A}` equipped with the multiplication inherited from `A` and
unit `e`. This is a fundamental construction in representation theory and Morita theory.

## Main definitions

* `Etingof.cornerSubmodule`: The `k`-submodule `eAe` of `A`, defined as the range of
  the linear map `a ↦ e * a * e`.

## Main results

* `Etingof.cornerSubmodule_left_mul`: For `x ∈ eAe`, `e * x = x`
* `Etingof.cornerSubmodule_right_mul`: For `x ∈ eAe`, `x * e = x`
* `Etingof.cornerSubmodule_mul_mem`: `eAe` is closed under multiplication
* `Etingof.finrank_cornerSubmodule_le`: `finrank k ↥(cornerSubmodule e) ≤ finrank k A`
* `Etingof.cornerSubmodule_finite`: `eAe` is finite-dimensional when `A` is

## Implementation notes

The `k`-submodule `cornerSubmodule e` captures the linear structure. Closure under
multiplication (`cornerSubmodule_mul_mem`) and containment of `e`
(`mem_cornerSubmodule_self`) are proved separately. Together these show `eAe` has
ring structure with unit `e`, which we construct as `CornerRing.instRing`.

The Ring and Algebra instances on `CornerRing e` are constructed by transferring
the ring axioms from `A` via `Subtype.ext`. The key observations are:
- Associativity and distributivity follow directly from `A`'s ring axioms.
- The identity `e * x = x = x * e` for `x ∈ eAe` follows from idempotency of `e`.
- The Algebra instance uses `Algebra.ofModule` since scalar multiplication commutes
  with the inherited multiplication.
-/

universe u

variable {k : Type u} [Field k]
variable {A : Type u} [Ring A] [Algebra k A]

namespace Etingof

/-- The linear map `a ↦ e * a * e` for a fixed element `e : A`. -/
noncomputable def cornerLinearMap (e : A) : A →ₗ[k] A where
  toFun a := e * a * e
  map_add' a b := by simp [mul_add, add_mul]
  map_smul' c a := by simp [Algebra.smul_mul_assoc]

@[simp]
lemma cornerLinearMap_apply (e a : A) : cornerLinearMap (k := k) e a = e * a * e := rfl

/-- The `k`-submodule `eAe` of `A`, defined as the range of the linear map `a ↦ e * a * e`. -/
noncomputable def cornerSubmodule (e : A) : Submodule k A :=
  LinearMap.range (cornerLinearMap (k := k) e)

lemma mem_cornerSubmodule_iff (e a : A) :
    a ∈ cornerSubmodule (k := k) e ↔ ∃ b : A, e * b * e = a :=
  LinearMap.mem_range

/-- Every element of `eAe` satisfies `e * x = x` when `e` is idempotent. -/
lemma cornerSubmodule_left_mul {e : A} (he : IsIdempotentElem e) {x : A}
    (hx : x ∈ cornerSubmodule (k := k) e) : e * x = x := by
  obtain ⟨a, rfl⟩ := (mem_cornerSubmodule_iff e x).mp hx
  rw [← mul_assoc, ← mul_assoc, he.eq]

/-- Every element of `eAe` satisfies `x * e = x` when `e` is idempotent. -/
lemma cornerSubmodule_right_mul {e : A} (he : IsIdempotentElem e) {x : A}
    (hx : x ∈ cornerSubmodule (k := k) e) : x * e = x := by
  obtain ⟨a, rfl⟩ := (mem_cornerSubmodule_iff e x).mp hx
  rw [mul_assoc, he.eq]

/-- The product of two elements of `eAe` is in `eAe` when `e` is idempotent. -/
lemma cornerSubmodule_mul_mem {e : A} {x y : A}
    (hx : x ∈ cornerSubmodule (k := k) e) (hy : y ∈ cornerSubmodule (k := k) e) :
    x * y ∈ cornerSubmodule (k := k) e := by
  obtain ⟨a, rfl⟩ := (mem_cornerSubmodule_iff e x).mp hx
  obtain ⟨b, rfl⟩ := (mem_cornerSubmodule_iff e y).mp hy
  rw [mem_cornerSubmodule_iff]
  refine ⟨a * e * e * b, ?_⟩
  simp only [mul_assoc]

/-- The idempotent `e` is in `eAe` (it is the unit of the corner ring). -/
lemma mem_cornerSubmodule_self (e : A) (he : IsIdempotentElem e) :
    e ∈ cornerSubmodule (k := k) e := by
  rw [mem_cornerSubmodule_iff]
  exact ⟨1, by rw [mul_one, he.eq]⟩

/-- **Dimension bound**: `finrank k (eAe) ≤ finrank k A`. -/
theorem finrank_cornerSubmodule_le (e : A) [Module.Finite k A] :
    Module.finrank k (cornerSubmodule (k := k) e) ≤ Module.finrank k A :=
  Submodule.finrank_le _

/-- `eAe` is finite-dimensional when `A` is. -/
noncomputable instance cornerSubmodule_finite (e : A) [Module.Finite k A] :
    Module.Finite k (cornerSubmodule (k := k) e) :=
  Module.Finite.of_injective (Submodule.subtype _) (Submodule.subtype_injective _)

/-! ### Ring structure on the corner ring

The corner ring `eAe` has a ring structure with:
- Multiplication: inherited from `A` (product of elements in `eAe` stays in `eAe`)
- Unit: `e` (not `1` of `A`)
- Addition: inherited from `A`

We define `CornerRing` as a type alias to hold the Ring and Algebra instances,
since the standard unit of `↥(cornerSubmodule e)` (inherited from the submodule)
is `0`, not `e`. -/

/-- The corner ring `eAe` as a type, to be equipped with its own Ring instance. -/
noncomputable def CornerRing (e : A) := cornerSubmodule (k := k) e

namespace CornerRing

variable {e : A} (he : IsIdempotentElem e)

-- The Ring instance on eAe. The multiplication is inherited from A
-- (which is well-defined by cornerSubmodule_mul_mem), and the unit is e
-- (which is in eAe by mem_cornerSubmodule_self).
-- The ring axioms (associativity, distributivity) follow from A's ring axioms.
-- The only non-trivial part is that e acts as an identity: e * x = x = x * e
-- for x ∈ eAe, which is cornerSubmodule_left_mul and cornerSubmodule_right_mul.
noncomputable instance instRing : Ring (CornerRing (k := k) e) :=
  { (inferInstance : AddCommGroup (CornerRing (k := k) e)) with
    mul := fun x y => ⟨(x : A) * (y : A), cornerSubmodule_mul_mem x.prop y.prop⟩
    one := ⟨e, mem_cornerSubmodule_self e he⟩
    mul_assoc := fun a b c => Subtype.ext (mul_assoc _ _ _)
    one_mul := fun a => Subtype.ext (cornerSubmodule_left_mul he a.prop)
    mul_one := fun a => Subtype.ext (cornerSubmodule_right_mul he a.prop)
    left_distrib := fun a b c => Subtype.ext (left_distrib _ _ _)
    right_distrib := fun a b c => Subtype.ext (right_distrib _ _ _)
    zero_mul := fun a => Subtype.ext (zero_mul _)
    mul_zero := fun a => Subtype.ext (mul_zero _) }

-- The Algebra instance on eAe over k.
-- The algebra map sends r : k to (algebraMap k A r) • e, which is in eAe
-- since e * ((algebraMap k A r) • e) * e = (algebraMap k A r) • (e * e * e)
--                                        = (algebraMap k A r) • e  (using he.eq).
-- Commutativity of the algebra map with multiplication follows from
-- r • (eae) = e(ra)e = (eae) • r for elements of eAe.
noncomputable instance instAlgebra :
    @Algebra k (CornerRing (k := k) e) _ (instRing he).toSemiring :=
  @Algebra.ofModule k (CornerRing (k := k) e) _ (instRing he).toSemiring _
    (fun r x y => Subtype.ext (Algebra.smul_mul_assoc r (x : A) (y : A)))
    (fun r x y => Subtype.ext (Algebra.mul_smul_comm r (x : A) (y : A)))

/-- `CornerRing e` is finite-dimensional when `A` is. -/
noncomputable instance instModuleFinite [Module.Finite k A] :
    Module.Finite k (CornerRing (k := k) e) :=
  cornerSubmodule_finite e

/-- The dimension of the corner ring is at most the dimension of `A`. -/
theorem finrank_le [Module.Finite k A] :
    Module.finrank k (CornerRing (k := k) e) ≤ Module.finrank k A :=
  finrank_cornerSubmodule_le e

end CornerRing

end Etingof
