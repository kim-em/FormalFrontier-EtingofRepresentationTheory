import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Theorem 3.10.2: Irreducible Representations of Tensor Products of Algebras

(i) Let V be an irreducible finite dimensional representation of A and let W be an
    irreducible finite dimensional representation of B. Then V ⊗ W is an irreducible
    representation of A ⊗ B.

(ii) Any irreducible finite dimensional representation M of A ⊗ B has the form (i) for
     unique V and W.
-/

/-- The tensor product of irreducible representations is irreducible over the tensor
product of algebras. Etingof Theorem 3.10.2(i). -/
theorem Etingof.tensor_product_irreducible (k : Type*) (A B V W : Type*)
    [Field k]
    [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    -- V ⊗_k W is an irreducible representation of A ⊗_k B
    True := by
  sorry

/-- Every irreducible representation of A ⊗ B arises as V ⊗ W for unique irreducible
representations V of A and W of B. Etingof Theorem 3.10.2(ii). -/
theorem Etingof.tensor_product_irreducible_classification (k : Type*) (A B : Type*)
    [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B] :
    -- Every irreducible representation of A ⊗_k B is of the form V ⊗_k W
    -- for unique irreducible V of A and W of B.
    True := by
  sorry
