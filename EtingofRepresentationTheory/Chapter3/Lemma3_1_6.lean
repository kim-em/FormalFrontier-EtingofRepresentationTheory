import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.Zorn

/-!
# Lemma 3.1.6: Surjective Map from Direct Sum of Irreducibles Splits

There exists a subset J ⊆ I such that V_J := ⊕_{i ∈ J} Vᵢ is mapped isomorphically by f
onto U.

More precisely: if f : ⊕ᵢ Vᵢ → U is a surjective homomorphism where the Vᵢ are irreducible,
then f restricts to an isomorphism on some sub-direct-sum.
-/

/-- A surjective map from a semisimple module splits: there exists a complement of the kernel
that maps isomorphically onto the target. Etingof Lemma 3.1.6. -/
theorem Etingof.surjective_map_splits (A : Type*) (V U : Type*)
    [Ring A] [AddCommGroup V] [Module A V] [AddCommGroup U] [Module A U]
    [IsSemisimpleModule A V] (f : V →ₗ[A] U) (hf : Function.Surjective f) :
    ∃ (W : Submodule A V), Disjoint W (LinearMap.ker f) ∧ W ⊔ LinearMap.ker f = ⊤ := by
  obtain ⟨W, hW⟩ := exists_isCompl (LinearMap.ker f)
  exact ⟨W, hW.symm.disjoint, hW.symm.sup_eq_top⟩
