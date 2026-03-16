import Mathlib

/-!
# Proposition 4.7.1: Orthogonality of Matrix Elements

Let V, W be nonisomorphic irreducible representations of G with orthonormal bases.
Define matrix elements t^V_{ij}(g) = ⟨v_i, ρ_V(g) v_j⟩.

(i) Matrix elements of nonisomorphic irreducible representations are orthogonal:
  (t^V_{ij}, t^W_{kl}) = 0 for V ≇ W.

(ii) (t^V_{ij}, t^V_{i'j'}) = δ_{ii'} δ_{jj'} / dim(V).

In particular, the matrix elements of all irreducible representations form an orthogonal
basis of the space of functions F(G, ℂ) (Peter–Weyl for finite groups).

## Mathlib correspondence

This extends the character orthogonality (Theorem 4.5.1) to matrix elements.
Not directly in Mathlib.
-/

/-- Matrix elements of irreducible representations form an orthogonal system.
(Etingof Proposition 4.7.1) -/
theorem Etingof.Proposition4_7_1
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    -- Matrix elements of distinct irreducible reps are orthogonal and
    -- those of the same rep satisfy (t^V_{ij}, t^V_{i'j'}) = δ_{ii'}δ_{jj'}/dim V
    True := by  -- TODO: needs matrix element API
  sorry
