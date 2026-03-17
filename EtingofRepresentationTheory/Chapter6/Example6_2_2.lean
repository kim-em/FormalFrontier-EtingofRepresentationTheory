import Mathlib

/-!
# Example 6.2.2: Indecomposable Representations of A₁

The quiver A₁ consists of a single vertex and has no edges. Since a representation
of this quiver is just a single vector space, the only indecomposable representation
is the ground field (= a 1-dimensional space).

## Formalization

We formalize the statement as: a finite-dimensional vector space V over a field k
is indecomposable (every complementary pair of submodules is trivial) if and only
if `Module.finrank k V = 1`.
-/

/-- A finite-dimensional vector space over a field k is indecomposable (i.e., for any
internal direct sum decomposition V = p ⊕ q, one of p or q is trivial) if and only if
it has dimension 1. This classifies the indecomposable representations of the A₁ quiver
(single vertex, no edges). (Etingof Example 6.2.2) -/
theorem Etingof.Example_6_2_2 (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (Nontrivial V ∧ ∀ (p q : Submodule k V), IsCompl p q → p = ⊥ ∨ q = ⊥) ↔
    Module.finrank k V = 1 := by
  constructor
  · -- Forward: indecomposable → dim = 1
    intro ⟨hnt, hind⟩
    by_contra h
    have hpos : 0 < Module.finrank k V := Module.finrank_pos (R := k) (M := V)
    -- finrank V ≥ 2
    have hge2 : 2 ≤ Module.finrank k V := by omega
    -- Pick a nonzero vector and span it
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    set p := Submodule.span k {v}
    have hp_rank : Module.finrank k p = 1 := finrank_span_singleton hv
    -- Every subspace of a vector space has a complement
    obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
    have hq_rank : Module.finrank k q = Module.finrank k V - 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hpq
      omega
    -- Apply indecomposability
    rcases hind p q hpq with hp_bot | hq_bot
    · -- span {v} = ⊥ contradicts v ≠ 0
      have : v ∈ (⊥ : Submodule k V) := hp_bot ▸ Submodule.subset_span (Set.mem_singleton v)
      simp only [Submodule.mem_bot] at this
      exact hv this
    · -- q = ⊥ means finrank q = 0, but finrank q = finrank V - 1 ≥ 1
      have : Module.finrank k q = 0 := by rw [hq_bot]; exact finrank_bot k V
      omega
  · -- Backward: dim = 1 → indecomposable
    intro h1
    refine ⟨Module.nontrivial_of_finrank_eq_succ (n := 0) (by omega), fun p q hpq => ?_⟩
    have hdim : Module.finrank k p + Module.finrank k q = 1 := by
      rw [Submodule.finrank_add_eq_of_isCompl hpq, h1]
    rcases Nat.eq_zero_or_pos (Module.finrank k p) with hp | hp
    · left; rwa [Submodule.finrank_eq_zero] at hp
    · right; have : Module.finrank k q = 0 := by omega
      rwa [Submodule.finrank_eq_zero] at this
