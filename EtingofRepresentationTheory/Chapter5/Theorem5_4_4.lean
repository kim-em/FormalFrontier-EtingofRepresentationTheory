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
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
private lemma character_eigenvalue_decomposition
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    ∃ (ε : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1) ∧
      V.character g = ∑ i, ε i ∧
      ((∀ i j, ε i = ε j) → ∃ (c : ℂ), V.ρ g = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj)) := by
  set n := Module.finrank ℂ V with hn_def
  set f := V.ρ g with hf_def
  -- f^d = 1 where d = orderOf g
  have hd_pos : 0 < orderOf g := orderOf_pos g
  have hf_pow : f ^ orderOf g = 1 := by
    show (V.ρ g) ^ orderOf g = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  -- Charpoly roots cardinality = n
  have hne : LinearMap.charpoly f ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hcard : (LinearMap.charpoly f).roots.card = n := by
    have hsplits := IsAlgClosed.splits (LinearMap.charpoly f)
    rw [← hsplits.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  -- aeval f (X^d - 1) = 0
  have haeval : Polynomial.aeval f
      ((Polynomial.X : Polynomial ℂ) ^ orderOf g - 1) = 0 := by
    simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, hf_pow, sub_self]
  -- Every root of charpoly is a d-th root of unity
  have hroots_unity : ∀ μ ∈ (LinearMap.charpoly f).roots, μ ^ orderOf g = 1 := by
    intro μ hμ
    rw [Polynomial.mem_roots hne] at hμ
    -- μ is an eigenvalue of f
    have heig : Module.End.HasEigenvalue f μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ
    -- Get a nonzero eigenvector v with f v = μ • v
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    -- f^d v = v (since f^d = 1), but also f^d v = μ^d • v
    have hpow_v : ∀ k : ℕ, (f ^ k) v = (μ ^ k) • v := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul,
          map_smul, ih, smul_smul, ← pow_succ']
    have h1 : v = (μ ^ orderOf g) • v := by
      rw [← hpow_v, hf_pow]; simp
    -- So (μ^d - 1) • v = 0, and v ≠ 0 → μ^d = 1
    have h2 : (μ ^ orderOf g - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv.2
  -- Construct ε from the roots list
  set rl := (LinearMap.charpoly f).roots.toList with hrl_def
  have hlen : rl.length = n := by rw [hrl_def, Multiset.length_toList, hcard]
  have hlt (i : Fin n) : i.val < rl.length := by omega
  refine ⟨fun i => rl[i.val]'(hlt i), ?_, ?_, ?_⟩
  -- Part 1: Each ε_i is a root of unity
  · intro i
    refine ⟨orderOf g, hd_pos, ?_⟩
    apply hroots_unity
    exact Multiset.mem_toList.mp (List.getElem_mem (hlt i))
  -- Part 2: character g = ∑ ε_i
  · -- V.character g = trace(f) = sum of charpoly roots
    change V.character g = _
    show LinearMap.trace ℂ V f = _
    -- Use matrix trace = sum of charpoly roots
    set b := Module.finBasis ℂ V
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    -- Matrix trace = sum of charpoly roots (algebraically closed)
    have h1 : (LinearMap.toMatrix b b f).trace =
        (LinearMap.toMatrix b b f).charpoly.roots.sum :=
      Matrix.trace_eq_sum_roots_charpoly _
    simp only [LinearMap.charpoly_toMatrix] at h1
    rw [h1]
    -- roots.sum = ∑ over Fin n (via list conversion)
    rw [← Multiset.sum_toList]
    change rl.sum = _
    have : rl = List.ofFn (fun i : Fin rl.length => rl[i.val]) := by
      rw [List.ofFn_getElem]
    conv_lhs => rw [this, List.sum_ofFn]
    exact Finset.sum_equiv (finCongr hlen) (by simp) (by intro i _; simp [finCongr])
  -- Part 3: All eigenvalues equal → scalar action
  · intro hall
    -- All roots of charpoly are equal to c := rl[0]
    have hn' : 0 < rl.length := by omega
    set c := rl[0]'hn' with hc_def
    -- Every root of charpoly is c
    have hall' : ∀ μ ∈ f.charpoly.roots, μ = c := by
      intro μ hμ
      have hμ_list : μ ∈ rl := Multiset.mem_toList.mpr hμ
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hμ_list
      exact hall ⟨i, hlen ▸ hi⟩ ⟨0, hn⟩
    refine ⟨c, ?_⟩
    -- Proof: f is semisimple (X^d-1 separable, annihilates f), so minpoly is squarefree.
    -- minpoly divides charpoly which has only root c, so minpoly = X - c.
    -- Therefore f = c • id.
    -- Step 1: X^d - 1 is separable (hence squarefree) over ℂ
    have hsep : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).Separable := by
      rw [Polynomial.X_pow_sub_one_separable_iff]
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd_pos)
    -- Step 2: minpoly divides X^d - 1
    have hf_integral : IsIntegral ℂ f :=
      ⟨f.charpoly, LinearMap.charpoly_monic f, LinearMap.aeval_self_charpoly f⟩
    have hmin_dvd : minpoly ℂ f ∣ (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, hf_pow, sub_self]
    -- Step 3: minpoly is squarefree (divides squarefree polynomial)
    have hmin_sqfree : Squarefree (minpoly ℂ f) :=
      hsep.squarefree.squarefree_of_dvd hmin_dvd
    -- Step 4: Every root of minpoly is a root of charpoly, hence equals c
    have hmin_roots : ∀ μ, (minpoly ℂ f).IsRoot μ → μ = c := by
      intro μ hμ_root
      apply hall'
      have hdvd := LinearMap.minpoly_dvd_charpoly f
      have hμ_mem : μ ∈ (minpoly ℂ f).roots :=
        (Polynomial.mem_roots (minpoly.ne_zero hf_integral)).mpr hμ_root
      exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd
        (LinearMap.charpoly_monic f).ne_zero hdvd) hμ_mem
    -- Step 5: minpoly is squarefree with only root c, so minpoly = X - C c
    -- (squarefree + splits + all roots = c → degree ≤ 1 → X - C c)
    have hmin_eq : minpoly ℂ f = Polynomial.X - Polynomial.C c := by
      have hmin_ne := minpoly.ne_zero hf_integral
      have hmin_monic := minpoly.monic hf_integral
      have hmin_splits := IsAlgClosed.splits (minpoly ℂ f)
      -- c is a root of charpoly (it's in the roots list)
      have hc_mem : c ∈ f.charpoly.roots := by
        rw [← Multiset.mem_toList]; exact List.getElem_mem hn'
      -- c is an eigenvalue, hence root of minpoly
      have hc_eig : Module.End.HasEigenvalue f c :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly f c).mpr
          (Polynomial.isRoot_of_mem_roots hc_mem)
      have hc_min_root : (minpoly ℂ f).IsRoot c :=
        Module.End.hasEigenvalue_iff_isRoot.mp hc_eig
      -- roots of minpoly = {c} (all roots are c, squarefree means count ≤ 1)
      have hroots_eq : (minpoly ℂ f).roots = {c} := by
        ext x
        by_cases hx : x = c
        · subst hx
          simp only [Multiset.count_singleton_self]
          have h1 : 0 < (minpoly ℂ f).roots.count c :=
            Multiset.count_pos.mpr ((Polynomial.mem_roots hmin_ne).mpr hc_min_root)
          have h2 : (minpoly ℂ f).roots.count c ≤ 1 :=
            Polynomial.count_roots_le_one
              (PerfectField.separable_iff_squarefree.mpr hmin_sqfree) c
          omega
        · simp only [Multiset.count_singleton, if_neg hx]
          exact Multiset.count_eq_zero.mpr
            (fun h => hx (hmin_roots x ((Polynomial.mem_roots hmin_ne).mp h)))
      -- minpoly = ∏ r in roots, (X - C r) = X - C c
      conv_lhs => rw [hmin_splits.eq_prod_roots_of_monic hmin_monic, hroots_eq]
      simp [Multiset.map_singleton, Multiset.prod_singleton]
    -- Step 6: f = c • id (from minpoly = X - C c)
    have := minpoly.aeval ℂ f
    rw [hmin_eq] at this
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at this
    rw [sub_eq_zero] at this
    exact this

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
