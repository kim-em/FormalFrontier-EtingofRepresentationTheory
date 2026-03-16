import Mathlib

/-!
# Definition 5.4.1: Solvable Group

A group G is **solvable** if there exists a chain of subgroups
  {e} = G₁ ⊲ G₂ ⊲ ... ⊲ Gₙ = G
such that each quotient Gᵢ₊₁/Gᵢ is abelian.

Equivalently, the derived series G ⊃ [G,G] ⊃ [[G,G],[G,G]] ⊃ ... terminates at {e}.

## Mathlib correspondence

Exact match: `IsSolvable G` in Mathlib, defined via the derived series.
-/

/-- A group G is solvable iff its derived series terminates at the trivial subgroup.
This is `IsSolvable G` in Mathlib. (Etingof Definition 5.4.1)

Example: S₃ is solvable with chain {e} ⊲ A₃ ⊲ S₃. -/
example : IsSolvable (Equiv.Perm (Fin 3)) := by
  -- S₃ is solvable with derived series S₃ ⊃ A₃ ⊃ {e}.
  -- A₃ is commutative (order 3, cyclic), hence solvable.
  haveI : IsSolvable (alternatingGroup (Fin 3)) := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card]
      native_decide
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI := isCyclic_of_prime_card hcard
    exact isSolvable_of_comm (fun a b => mul_comm a b)
  exact solvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype
    (Equiv.Perm.sign)
    (by rw [← alternatingGroup_eq_sign_ker]; exact fun x hx => ⟨⟨x, hx⟩, rfl⟩)
