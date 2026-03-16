import Mathlib

/-!
# Theorem 5.4.6: Conjugacy Class of Prime Power Size

If G has a conjugacy class C of size p^k where p is prime and k > 0,
then G has a proper nontrivial normal subgroup (and hence is not simple).

The proof uses the column orthogonality of the character table, splitting
irreducible representations into three sets based on whether p divides
their dimension, and applying Theorem 5.4.4 and Lemma 5.4.7.

## Mathlib correspondence

Uses `Subgroup.Normal`, character orthogonality.

## Proof status

The core argument requires column orthogonality of the character table
(summing over irreducible representations), which is not yet available
in Mathlib (Mathlib has row orthogonality `FDRep.char_orthonormal` but
not column orthogonality). The proof also requires:
- Regular representation decomposition into irreducibles
- The identity: for g ≠ 1, ∑_V dim(V) · χ_V(g) = 0
- Algebraic integer argument (Theorem 5.4.4, uses Lemma 5.4.5)
- Scalar action implies normal subgroup (kernel argument)

The proof structure is set up with the elementary steps proved
and the character theory core isolated as a sorry.
-/

/-- The conjugacy class of 1 is {1}, so has cardinality 1. -/
private lemma card_conjClass_one (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Fintype.card { h : G // IsConj (1 : G) h } = 1 := by
  have : Unique { h : G // IsConj (1 : G) h } := by
    refine ⟨⟨⟨1, IsConj.refl 1⟩⟩, ?_⟩
    rintro ⟨h, hh⟩
    simp only [Subtype.mk.injEq]
    rwa [isConj_one_right] at hh
  exact Fintype.card_unique

/-- A simple finite group cannot have a conjugacy class of prime power size.
This is the core character theory argument of Theorem 5.4.6.

The proof goes: assume G is simple with |Cl(g)| = p^k, k > 0.
1. g ≠ 1 (since |Cl(1)| = 1)
2. Z(G) = {1} (since G is simple and g ∉ Z(G), G is non-abelian)
3. By the regular representation character identity:
   0 = 1 + ∑_{V nontrivial irred} dim(V) · χ_V(g)
4. For V with gcd(p^k, dim V) = 1: χ_V(g)/dim(V) is an algebraic integer,
   so by Lemma 5.4.5 either χ_V(g) = 0 or g acts as scalar on V.
5. If g acts as scalar on V, then ker(ρ_V) is a proper nontrivial normal
   subgroup, contradicting simplicity. So χ_V(g) = 0 for such V.
6. Then 0 = 1 + ∑_{p | dim V} dim(V) · χ_V(g), giving p | 1, contradiction. -/
private lemma IsSimpleGroup.no_prime_power_conjClass
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    [IsSimpleGroup G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G) (hg_ne : g ≠ 1)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    False := by
  -- This proof requires column orthogonality of the character table,
  -- which is not yet available in Mathlib.
  -- Column orthogonality requires: summing characters over all irreducible
  -- representations (Mathlib only has row orthogonality: summing over group elements).
  -- Infrastructure needed:
  -- 1. Finite set of irreducible representations (up to isomorphism)
  -- 2. Regular representation decomposition: k[G] ≅ ⊕ dim(V_i) · V_i
  -- 3. Character of regular representation at g ≠ 1 is 0
  -- 4. Algebraic integer properties of χ_V(g)/dim(V) when gcd(|Cl(g)|, dim V) = 1
  sorry

/-- If G has a conjugacy class of size p^k (p prime, k > 0), then G has a proper
nontrivial normal subgroup. (Etingof Theorem 5.4.6) -/
theorem Etingof.Theorem5_4_6
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G)
    -- Hypothesis: the conjugacy class of g has size p^k
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  -- Step 1: g ≠ 1 (since |Cl(1)| = 1 but p^k ≥ 2)
  have hg_ne : g ≠ 1 := by
    intro heq; subst heq
    rw [card_conjClass_one] at hconj
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
    omega
  -- Step 2: By contradiction, assume G has no proper nontrivial normal subgroup
  by_contra habs
  push_neg at habs
  -- habs : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤
  -- Step 3: G is nontrivial (since g ≠ 1, there are at least two elements)
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  -- Step 4: Therefore G is simple
  have habs' : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := by
    intro H hH
    by_cases h : H = ⊥
    · exact Or.inl h
    · exact Or.inr (habs H hH h)
  haveI : IsSimpleGroup G := { eq_bot_or_eq_top_of_normal := habs' }
  -- Step 5: But a simple group cannot have a conjugacy class of prime power size
  exact IsSimpleGroup.no_prime_power_conjClass G p hp k hk g hg_ne hconj
