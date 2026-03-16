import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Example 3.1.2: End(V) as a Semisimple Representation

Let V be an irreducible representation of A of dimension n. Then Y = End(V), with action
of A by left multiplication, is a semisimple representation of A, isomorphic to nV
(the direct sum of n copies of V). Indeed, any basis v₁, …, vₙ of V gives rise to an
isomorphism of representations End(V) → nV, given by x ↦ (xv₁, …, xvₙ).

## Proof strategy

Given a k-basis b of V, the evaluation map f ↦ (f(b₀), …, f(bₙ₋₁)) is an A-linear
bijection from End_k(V) to V^n. Since V is simple (hence semisimple), V^n is semisimple,
and semisimplicity transfers along the equivalence.
-/

set_option autoImplicit false

section

variable {k : Type*} {A : Type*} {V : Type*}
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V]

/-- The evaluation map sending f ∈ End_k(V) to (f(b₀), …, f(bₙ₋₁)) is A-linear. -/
private noncomputable def evalMap (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Module.End k V →ₗ[A] (Fin (Module.finrank k V) → V) where
  toFun f i := f (b i)
  map_add' f g := by ext i; simp
  map_smul' (a : A) f := by ext i; simp [LinearMap.smul_apply]

omit [FiniteDimensional k V] [IsSimpleModule A V] in
private theorem evalMap_bijective (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Bijective (evalMap (A := A) b) := by
  constructor
  · intro f g h
    ext v
    have hfg : ∀ i, f (b i) = g (b i) := congr_fun h
    rw [← b.sum_repr v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hfg i]
  · intro g
    exact ⟨b.constr k (fun i => g i), by ext i; simp [evalMap]⟩

end

/-- End(V) with left multiplication by A is isomorphic to n copies of V as a representation,
where n = dim V. Etingof Example 3.1.2. -/
theorem Etingof.endomorphism_semisimple (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    IsSemisimpleModule A (Module.End k V) :=
  IsSemisimpleModule.congr
    (LinearEquiv.ofBijective (evalMap (Module.finBasis k V)) (evalMap_bijective _))
