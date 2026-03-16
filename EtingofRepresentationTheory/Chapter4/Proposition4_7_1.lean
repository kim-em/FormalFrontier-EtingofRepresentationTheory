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

open FDRep CategoryTheory

universe u

/-- Matrix element orthogonality, part (i): for nonisomorphic irreducible representations
V, W, the inner product of any pair of matrix coefficients is zero.
(1/|G|) Σ_g (ρ_V(g))_{ij} (ρ_W(g⁻¹))_{pq} = 0 when V ≇ W.
(Etingof Proposition 4.7.1(i)) -/
theorem Etingof.Proposition4_7_1_i
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k V) (bW : Module.Basis (Fin nW) k W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q = 0 := by
  sorry

/-- Matrix element orthogonality, part (ii): for an irreducible representation V,
(1/|G|) Σ_g (ρ(g))_{ij} (ρ(g⁻¹))_{pq} = δ_{iq} δ_{jp} / dim(V).
(Etingof Proposition 4.7.1(ii)) -/
theorem Etingof.Proposition4_7_1_ii
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) [Simple V]
    [Invertible (Module.finrank k (↑V : Type u) : k)]
    {n : ℕ}
    (b : Module.Basis (Fin n) k V)
    (i j p q : Fin n) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix b b (V.ρ g)) i j *
      (LinearMap.toMatrix b b (V.ρ g⁻¹)) p q =
    if i = q ∧ j = p then (⅟(Module.finrank k (↑V : Type u) : k) : k) else 0 := by
  sorry
