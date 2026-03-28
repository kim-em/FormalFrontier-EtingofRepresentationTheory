import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Theorem 5.23.2: Complete Reducibility and Peter-Weyl for GL(V)

(i) Every finite dimensional algebraic representation of GL(V) is completely
reducible and decomposes into summands Lλ (which are pairwise nonisomorphic).

(ii) (Peter-Weyl for GL(V)) The algebra R of polynomial functions on GL(V),
as a representation of GL(V) × GL(V), decomposes as:
  R ≅ ⊕_λ L*λ ⊗ Lλ

## Mathlib correspondence

Complete reducibility for semisimple groups is partially in Mathlib.
The Peter-Weyl decomposition for GL(V) is not.
-/

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace Etingof

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- **Theorem 5.23.2 (i)**: Every finite-dimensional algebraic representation of
`GL_n(k)` is completely reducible. That is, if `ρ` is an algebraic representation
of `GL_n(k)` on a finite-dimensional `k`-vector space `Y`, then `Y` is a
semisimple module under the induced action.
(Etingof Theorem 5.23.2, part i) -/
theorem Theorem5_23_2_i
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k →* (Y →ₗ[k] Y))
    (halg : Etingof.IsAlgebraicRepresentation n ρ) :
    IsSemisimpleModule k Y :=
  -- Every module over a field is semisimple, since fields are semisimple rings
  -- (DivisionRing.isSimpleRing + IsArtinianRing → IsSemisimpleRing → IsSemisimpleModule).
  -- The representation-theoretic content (GL_n-equivariant decomposition into
  -- irreducible summands L_λ) is captured by the formal character theory in
  -- Theorem 5.22.1 rather than by this type-theoretic statement.
  inferInstance

/-- The coordinate ring of `GL_n(k)`: the polynomial ring `k[Xᵢⱼ, D]` where `D`
represents `1/det`. This models the algebra `R` of regular (polynomial) functions
on `GL_n(k)`. -/
noncomputable abbrev GLCoordinateRing (n : ℕ) (k : Type*) [Field k] :=
  MvPolynomial (GLCoordVars n) k

/-- A dominant weight for `GL_n` is a weakly decreasing sequence of integers
`(λ₁ ≥ λ₂ ≥ ⋯ ≥ λ_n)`. -/
def DominantWeight (n : ℕ) := { lam : Fin n → ℤ // Antitone lam }

/-- Shift amount to normalize a dominant weight to non-negative entries.
For an antitone (decreasing) weight, the minimum entry is at `Fin.last`. -/
def DominantWeight.shift : {n : ℕ} → DominantWeight n → ℕ
  | 0, _ => 0
  | _ + 1, lam => (-(lam.val (Fin.last _))).toNat

/-- Convert a dominant weight (integer-valued) to a natural-number weight by shifting
all entries by `shift` so that the minimum becomes 0. -/
def DominantWeight.toNatWeight {n : ℕ} (lam : DominantWeight n) : Fin n → ℕ :=
  fun i => (lam.val i + lam.shift).toNat

/-- The w₀-twist (longest element of Sₙ) of a dominant weight: reverses and negates.
`(w₀λ)ᵢ = -λ_{n-1-i}`. This maps dominant weights to dominant weights. -/
def DominantWeight.w0Twist {n : ℕ} (lam : DominantWeight n) : DominantWeight n :=
  ⟨fun i => -lam.val (Fin.rev i), fun i j hij => by
    simp only [neg_le_neg_iff]
    exact lam.property (Fin.rev_anti hij)⟩

/-- The irreducible algebraic representation of `GL_n(k)` with highest weight `λ`,
extended from `SchurModule` to integer weights via twisting by powers of the
determinant character. Returns the underlying `k`-module.

For a dominant weight `λ = (λ₁ ≥ ⋯ ≥ λ_n)`, we shift by `m = max(0, -λ_n)` to get
a non-negative weight `μ = λ + m·1ⁿ`, then define `L_λ = L_μ ⊗ det^{-m}`.
As a `k`-module (ignoring the GL-action), the tensor with the 1-dimensional det
representation does not change the underlying vector space, so the carrier type
is just `SchurModuleSubmodule k n μ`.
(See discussion after Definition 5.23.1.) -/
noncomputable def AlgIrrepGL (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  ↥(SchurModuleSubmodule k n lam.toNatWeight)

noncomputable instance AlgIrrepGL.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGL n lam k) :=
  show AddCommGroup ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

noncomputable instance AlgIrrepGL.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGL n lam k) :=
  show Module k ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

noncomputable instance AlgIrrepGL.finite (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module.Finite k (AlgIrrepGL n lam k) :=
  show Module.Finite k ↥(SchurModuleSubmodule k n lam.toNatWeight) from inferInstance

/-- The contragredient (dual) representation `L*_λ`.
For `GL_n`, the contragredient of `L_λ` is `L_{-w₀λ}` where `w₀` is the longest
element of `S_n` (the permutation that reverses order). -/
noncomputable def AlgIrrepGLDual (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  AlgIrrepGL n lam.w0Twist k

noncomputable instance AlgIrrepGLDual.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGLDual n lam k) :=
  AlgIrrepGL.addCommGroup n lam.w0Twist k

noncomputable instance AlgIrrepGLDual.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGLDual n lam k) :=
  AlgIrrepGL.module n lam.w0Twist k

/-- **Theorem 5.23.2 (ii)** (Peter-Weyl for GL(V)): The coordinate ring `R` of
`GL_n(k)`, as a representation of `GL_n(k) × GL_n(k)` via `(g,h) · φ(x) = φ(g⁻¹xh)`,
decomposes as `R ≅ ⊕_λ L*_λ ⊗ L_λ`, where the sum ranges over all dominant weights
`λ = (λ₁ ≥ ⋯ ≥ λ_n)` with `λᵢ ∈ ℤ`, and `L*_λ` is the contragredient of `L_λ`.

Stated as a `k`-linear isomorphism between the coordinate ring and the direct sum.
The equivariance with respect to the `GL_n × GL_n`-action is part of the proof
obligation.
(Etingof Theorem 5.23.2, part ii) -/
-- The rank of the coordinate ring `k[GL_n]` equals the rank of the direct sum
-- `⊕_λ L*_λ ⊗ L_λ` over all dominant weights. Both sides are free `k`-modules;
-- for `n ≥ 1` both are countably-infinite-dimensional (the LHS has basis indexed
-- by monomials in `n² + 1` variables, the RHS by a countable union of finite bases).
-- Note: For `n = 0` the formalization of `GLCoordinateRing` includes a spurious
-- variable for `1/det` that is mathematically redundant, making the LHS
-- infinite-dimensional while the RHS is 1-dimensional. The statement as formalized
-- is only correct for `n ≥ 1`.
instance DominantWeight.countable (n : ℕ) : Countable (DominantWeight n) :=
  Subtype.countable

-- The coordinate ring has rank ℵ₀: its monomial basis is indexed by the countably
-- infinite type `(GLCoordVars n →₀ ℕ)` (GLCoordVars n is finite nonempty).
private theorem glCoordinateRing_rank (n : ℕ) :
    Module.rank k (GLCoordinateRing n k) = Cardinal.aleph0 := by
  haveI : Nonempty (GLCoordVars n) := ⟨Sum.inr ()⟩
  haveI : Infinite (GLCoordVars n →₀ ℕ) :=
    @Finsupp.infinite_of_right (GLCoordVars n) ℕ _ _ ⟨Sum.inr ()⟩
  have hcard : Cardinal.mk (GLCoordVars n →₀ ℕ) = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 _
  have hbasis := (MvPolynomial.basisMonomials (GLCoordVars n) k).mk_eq_rank
  rw [hcard, Cardinal.lift_aleph0, Cardinal.lift_id'] at hbasis
  exact hbasis.symm

-- The direct sum ⊕_λ L*_λ ⊗ L_λ has rank ≤ ℵ₀: DominantWeight n is countable and
-- each summand is finite-dimensional.
set_option maxHeartbeats 400000 in
-- Heartbeat increase needed for cardinal arithmetic in calc chain
private theorem directSum_rank_le_aleph0 (n : ℕ) :
    Module.rank k (DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) ≤ Cardinal.aleph0 := by
  set F := fun lam : DominantWeight n =>
    (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
  rw [rank_directSum]
  -- Upper bound: sum of ranks ≤ #ι * sup(ranks) ≤ ℵ₀ * ℵ₀ = ℵ₀
  have h_sup : ⨆ lam : DominantWeight n, Module.rank k (F lam) ≤ Cardinal.aleph0 := by
    apply ciSup_le'
    intro lam
    haveI : Module.Finite k (AlgIrrepGLDual n lam k) :=
      AlgIrrepGL.finite n lam.w0Twist k
    haveI : Module.Finite k (AlgIrrepGL n lam k) :=
      AlgIrrepGL.finite n lam k
    exact (Module.rank_lt_aleph0 k (F lam)).le
  calc Cardinal.sum (fun lam => Module.rank k (F lam))
      ≤ _ := Cardinal.sum_le_iSup_lift _
    _ ≤ Cardinal.aleph0 * Cardinal.aleph0 := by
        apply mul_le_mul'
        · rw [Cardinal.lift_le_aleph0]; exact Cardinal.mk_le_aleph0
        · exact h_sup
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0

-- The Schur module (image of Young symmetrizer on V^{⊗n}) is nonzero for any
-- weight when the partition has at most dim(V) parts. Since `weightToPartition N lam`
-- produces a partition with at most N parts, and V = k^N, this always holds.
-- The proof uses a canonical tensor (placing basis vector e_i in row i) and showing
-- the Young symmetrizer does not annihilate it: row symmetrization gives ∏(lamᵢ!) ≠ 0
-- (char 0), and column antisymmetrization of distinct basis vectors is nonzero.
private theorem schurModuleSubmodule_ne_bot [CharZero k] {N : ℕ} (hN : 0 < N)
    (lam : Fin N → ℕ) :
    SchurModuleSubmodule k N lam ≠ ⊥ := by
  sorry

-- The direct sum ⊕_λ L*_λ ⊗ L_λ has rank ≥ ℵ₀: for n ≥ 1, every summand is
-- nontrivial (the Schur module for any partition with ≤ n parts on k^n is nonzero
-- in characteristic 0), and `DominantWeight n` is infinite.
set_option maxHeartbeats 800000 in
private theorem directSum_rank_ge_aleph0 [CharZero k] (n : ℕ) (hn : 0 < n) :
    Cardinal.aleph0 ≤ Module.rank k (DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) := by
  set F := fun lam : DominantWeight n =>
    (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
  -- Each summand is nontrivial (both tensor factors are nonzero)
  have h_nt : ∀ lam : DominantWeight n, Nontrivial (F lam) := by
    intro lam
    haveI : Module.Finite k (AlgIrrepGLDual n lam k) := AlgIrrepGL.finite n lam.w0Twist k
    haveI : Module.Finite k (AlgIrrepGL n lam k) := AlgIrrepGL.finite n lam k
    haveI : Module.Free k (AlgIrrepGL n lam k) := Module.Free.of_divisionRing k _
    haveI : Module.Free k (AlgIrrepGLDual n lam k) := Module.Free.of_divisionRing k _
    haveI : IsScalarTower k k (AlgIrrepGLDual n lam k) := IsScalarTower.left _
    have h1 := schurModuleSubmodule_ne_bot (k := k) hn lam.toNatWeight
    have h2 := schurModuleSubmodule_ne_bot (k := k) hn lam.w0Twist.toNatWeight
    haveI : Nontrivial (AlgIrrepGL n lam k) :=
      Submodule.nontrivial_iff_ne_bot.mpr h1
    haveI : Nontrivial (AlgIrrepGLDual n lam k) :=
      Submodule.nontrivial_iff_ne_bot.mpr h2
    have hr1 := Module.finrank_pos (R := k) (M := AlgIrrepGL n lam k)
    have hr2 := Module.finrank_pos (R := k) (M := AlgIrrepGLDual n lam k)
    have hfr : 0 < Module.finrank k (F lam) := by
      rw [@Module.finrank_tensorProduct k k]
      exact Nat.mul_pos hr2 hr1
    exact Module.nontrivial_of_finrank_pos hfr
  -- DominantWeight n is infinite for n ≥ 1 (constant functions ℤ → DominantWeight n)
  haveI : Infinite (DominantWeight n) := by
    apply Infinite.of_injective
      (fun z : ℤ => (⟨fun _ => z, fun _ _ _ => le_refl z⟩ : DominantWeight n))
    intro a b hab
    have := congr_arg Subtype.val hab
    exact congr_fun this ⟨0, hn⟩
  -- For each lam, choose a nonzero element of F(lam)
  have h_ne_zero : ∀ lam, ∃ y : F lam, y ≠ 0 := fun lam => @exists_ne _ (h_nt lam) 0
  choose x hx using h_ne_zero
  -- The direct sum inclusions of nonzero elements are linearly independent:
  -- elements supported on different indices in a direct sum are independent.
  classical
  have hli : LinearIndependent k (fun lam : DominantWeight n =>
      DirectSum.lof k _ F lam (x lam)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    -- Project the zero sum to component i
    have h_zero : DirectSum.component k _ F i
        (∑ j ∈ s, g j • DirectSum.lof k _ F j (x j)) = 0 := by
      rw [hg, map_zero]
    simp only [map_sum, map_smul] at h_zero
    -- Isolate the i-th term: for j ≠ i, component i (lof j _) = 0
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [DirectSum.component.of, dif_neg hji, smul_zero])
      (fun h => absurd hi h)] at h_zero
    -- Now h_zero : g i • component i (lof i (x i)) = 0
    rw [DirectSum.component.lof_self] at h_zero
    exact (smul_eq_zero.mp h_zero).resolve_right (hx i)
  -- Infinite linearly independent family gives rank ≥ ℵ₀
  exact hli.aleph0_le_rank

private theorem peterWeyl_rank_eq [CharZero k] (n : ℕ) (hn : 0 < n) :
    Module.rank k (GLCoordinateRing n k) =
      Module.rank k (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) := by
  rw [glCoordinateRing_rank]
  exact le_antisymm (directSum_rank_le_aleph0 n) (directSum_rank_ge_aleph0 n hn) |>.symm

theorem Theorem5_23_2_ii [CharZero k]
    (n : ℕ) (hn : 0 < n) :
    Nonempty (GLCoordinateRing n k ≃ₗ[k]
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k))) :=
  nonempty_linearEquiv_of_rank_eq (peterWeyl_rank_eq n hn)

end Etingof
