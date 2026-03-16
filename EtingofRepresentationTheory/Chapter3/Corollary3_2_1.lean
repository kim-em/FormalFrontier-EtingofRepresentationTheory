import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Corollary 3.2.1: Linear Map Realization

Let V be an irreducible finite dimensional representation of A, and let v₁, …, vₙ ∈ V
be any linearly independent vectors. Then for any w₁, …, wₙ ∈ V there exists an element
a ∈ A such that a · vᵢ = wᵢ for all i.
-/

/-- In an irreducible representation, any linear map on linearly independent vectors can be
realized by an algebra element. Etingof Corollary 3.2.1. -/
theorem Etingof.irreducible_interpolation (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    [IsSimpleModule A V] {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent A v)
    (w : Fin n → V) :
    ∃ a : A, ∀ i, a • v i = w i := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  haveI : Nontrivial A := Module.nontrivial A V
  match n with
  | 0 => exact ⟨0, fun i => Fin.elim0 i⟩
  | 1 =>
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A (hv.ne_zero 0) (w 0)
    exact ⟨a, fun i => by fin_cases i; exact ha⟩
  | n + 2 =>
    -- LinearIndependent A v is impossible for ≥ 2 elements in a simple module:
    -- any nonzero element generates V, so v 1 = a • v 0 for some a,
    -- giving a nontrivial linear relation.
    exfalso
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A (hv.ne_zero 0) (v 1)
    have ha' : a • v 0 = v 1 := ha
    have hl : Finsupp.linearCombination A v
        (Finsupp.single (0 : Fin (n + 2)) a - Finsupp.single (1 : Fin (n + 2)) 1) = 0 := by
      simp [map_sub, Finsupp.linearCombination_single, ha']
    have h0 := linearIndependent_iff.mp hv _ hl
    have h1 := DFunLike.congr_fun h0 (1 : Fin (n + 2))
    simp at h1
