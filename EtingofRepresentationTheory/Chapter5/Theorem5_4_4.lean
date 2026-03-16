import Mathlib
import EtingofRepresentationTheory.Chapter5.Lemma5_4_5

/-!
# Theorem 5.4.4: Character Vanishing or Scalar Action

For an irreducible representation V of G and a conjugacy class C such that
gcd(|C|, dim V) = 1: for any g ∈ C, either χ_V(g) = 0 or g acts as a scalar
on V (i.e., ρ(g) = λ · id for some root of unity λ).

The proof uses Lemma 5.4.5 (roots of unity average) and the fact that
χ_V(g)/dim(V) is an algebraic integer when gcd(|C|, dim(V)) = 1.

## Mathlib correspondence

Uses `IsIntegral`, `IsPrimitiveRoot`, character theory.

## Proof outline

1. ρ(g) has finite order d = orderOf g, so (ρ(g))^d = id.
2. The charpoly of ρ(g) divides (X^d - 1)^n, so all roots are d-th roots of unity.
3. Over ℂ, trace = sum of roots of charpoly = sum of roots of unity.
4. By Prop 5.3.2 + coprimality (Bezout), χ_V(g)/dim(V) is an algebraic integer.
5. Lemma 5.4.5 gives: either all eigenvalues are equal or their sum is 0.
6. Sum = 0 means χ_V(g) = 0. All equal means ρ(g) = c·id (semisimplicity).
-/

open CategoryTheory Finset

/-! ### Helper: eigenvalue decomposition of ρ(g)

For g in a finite group G, ρ(g) is diagonalizable (semisimple, since the minimal
polynomial divides X^d - 1, which is squarefree over ℂ). The character
χ_V(g) = trace(ρ(g)) equals the sum of eigenvalues, each a root of unity.
Moreover, if all eigenvalues are equal to some c, then ρ(g) = c • id.

Key Mathlib APIs used:
- `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` for diagonalizability
- `Matrix.trace_eq_sum_roots_charpoly` for trace as sum of charpoly roots
- `LinearMap.trace_eq_matrix_trace` to bridge LinearMap and Matrix trace
-/
private lemma character_eigenvalue_decomposition
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    ∃ (ε : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1) ∧
      V.character g = ∑ i, ε i ∧
      ((∀ i j, ε i = ε j) → ∃ (c : ℂ), V.ρ g = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj)) := by
  sorry

/-! ### Helper: χ_V(g)/dim(V) is an algebraic integer when gcd(|C|, dim V) = 1

This follows from:
1. Proposition 5.3.2: |C| · χ_V(g) / dim(V) is an algebraic integer
   (the class sum ∑_{h ∈ C} h acts on V as a scalar λ by Schur's lemma,
   and λ is an algebraic integer since it's a root of a monic polynomial
   with integer coefficients)
2. χ_V(g) is itself an algebraic integer (sum of roots of unity)
3. By Bezout: gcd(|C|, dim V) = 1 implies ∃ a b : ℤ, a·|C| + b·dim(V) = 1
4. So χ_V(g)/dim(V) = a · (|C|·χ_V(g)/dim(V)) + b · χ_V(g) is algebraic integer
-/
private lemma character_div_dim_isIntegral
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    IsIntegral ℤ (V.character g / (Module.finrank ℂ V : ℂ)) := by
  sorry

open CategoryTheory in
/-- If gcd(|C|, dim V) = 1 for an irreducible V and conjugacy class C containing g, then
either χ_V(g) = 0 or g acts as a scalar on V. (Etingof Theorem 5.4.4) -/
theorem Etingof.Theorem5_4_4
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    V.character g = 0 ∨ ∃ (c : ℂ), V.ρ g = c • LinearMap.id := by
  -- V is a simple FDRep, so it has positive dimension
  have hn : 0 < Module.finrank ℂ V := by
    by_contra h
    push_neg at h
    have h0 : Module.finrank ℂ V = 0 := by omega
    haveI : Subsingleton V.V.obj := Module.finrank_zero_iff.1 h0
    apply id_nonzero V
    ext x
    exact Subsingleton.elim _ _
  -- Step 1: Decompose character as sum of roots of unity with scalar action guarantee
  obtain ⟨ε, hε_roots, hε_sum, hε_scalar⟩ :=
    character_eigenvalue_decomposition G V g hn
  -- Step 2: The average (∑ εᵢ)/dim(V) is an algebraic integer
  have hint : IsIntegral ℤ ((∑ i, ε i) / (Module.finrank ℂ V : ℂ)) := by
    rw [← hε_sum]
    exact character_div_dim_isIntegral G V g h_coprime
  -- Step 3: Apply Lemma 5.4.5
  rcases Etingof.Lemma5_4_5 (Module.finrank ℂ V) hn ε hε_roots hint with hall | hzero
  · -- All eigenvalues are equal → g acts as scalar
    exact Or.inr (hε_scalar hall)
  · -- Sum of eigenvalues is zero → character is zero
    exact Or.inl (by rw [hε_sum, hzero])
