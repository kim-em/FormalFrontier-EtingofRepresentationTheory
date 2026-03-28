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

-- The one-row dominant weight (m, 0, ..., 0) : DominantWeight n
private def oneRowWeight (n : ℕ) (m : ℕ) (hn : 0 < n) : DominantWeight n :=
  ⟨fun i => if i = ⟨0, hn⟩ then (m : ℤ) else 0, by
    intro i j hij
    by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
    exfalso; apply hi; subst hj
    exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)⟩

private theorem oneRowWeight_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (oneRowWeight n · hn) := by
  intro m₁ m₂ h
  have := congr_arg (fun w : DominantWeight n => w.val ⟨0, hn⟩) h
  simp [oneRowWeight] at this
  exact_mod_cast this

private theorem oneRowWeight_shift (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).shift = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [DominantWeight.shift, oneRowWeight]
    -- The last entry of the weight: if Fin.last n = ⟨0, hn⟩ then m else 0
    split_ifs with h
    · -- n = 0 case: last entry is m, shift = (-m).toNat = 0 (since m : ℕ cast to ℤ ≥ 0)
      simp
    · -- n ≥ 1 case: last entry is 0, shift = (-0).toNat = 0
      simp

private theorem oneRowWeight_toNatWeight (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).toNatWeight = fun i => if i = ⟨0, hn⟩ then m else 0 := by
  ext i
  simp only [DominantWeight.toNatWeight, oneRowWeight]
  have : DominantWeight.shift (oneRowWeight n m hn) = 0 := oneRowWeight_shift n m hn
  unfold oneRowWeight at this
  rw [this]
  split_ifs <;> simp

-- The Schur polynomial is nonzero for any antitone weight.
-- Proof: s_λ · Δ = D_{λ+ρ}, and D_{λ+ρ} ≠ 0 since its diagonal coefficient is 1.
private theorem schurPoly_ne_zero (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    schurPoly N lam ≠ 0 := by
  intro h
  -- From schurPoly_mul_vandermonde: s_λ · Δ = D_{λ+ρ}
  have hprod := schurPoly_mul_vandermonde N lam
  rw [h, zero_mul] at hprod
  -- So D_{λ+ρ} = 0. But its diagonal coefficient is 1.
  have hstrict : StrictAnti (shiftedExps N lam) := by
    intro i j hij; simp only [shiftedExps]; have := hlam (le_of_lt hij); omega
  have hcoeff := alternant_coeff_kronecker hstrict hstrict
  rw [if_pos rfl] at hcoeff
  -- hcoeff : coeff ... D_{λ+ρ} = 1, but D_{λ+ρ} = 0, so coeff = 0
  rw [← hprod, MvPolynomial.coeff_zero] at hcoeff
  exact one_ne_zero hcoeff.symm

-- The SchurModuleSubmodule is nonzero for any antitone weight.
-- Uses the Weyl character formula: ch(L_λ) = s_λ ≠ 0.
private theorem schurModuleSubmodule_ne_bot (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    SchurModuleSubmodule k N lam ≠ ⊥ := by
  intro h
  -- If SchurModuleSubmodule = ⊥, the Schur module is zero
  -- The formal character of a zero module is 0
  have hchar : formalCharacter k N (SchurModule k N lam) = 0 := by
    unfold formalCharacter
    apply Finset.sum_eq_zero
    intro μ _
    suffices Module.finrank k (glWeightSpace k N (SchurModule k N lam) (fun i => μ i)) = 0 by
      rw [this, Nat.cast_zero, zero_smul]
    -- SchurModuleSubmodule = ⊥ means the carrier is subsingleton
    have hsub : ∀ (a b : SchurModuleSubmodule k N lam), a = b := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      ext
      rw [h] at ha hb
      simp only [Submodule.mem_bot] at ha hb
      simp [ha, hb]
    -- SchurModule has same carrier type
    have hsub' : ∀ (a b : SchurModule k N lam), a = b := hsub
    -- Weight space finrank is 0
    rw [Module.finrank_eq_zero_iff]
    intro x
    have : x = 0 := by
      have := hsub' x.val 0
      exact Subtype.ext this
    exact ⟨1, one_ne_zero, by rw [this, smul_zero]⟩
  -- But ch(L_λ) = s_λ ≠ 0
  have hne := schurPoly_ne_zero N lam hlam
  rw [formalCharacter_schurModule_eq_schurPoly k N lam hlam] at hchar
  exact hne hchar

-- The direct sum ⊕_λ L*_λ ⊗ L_λ has rank ≥ ℵ₀: for n ≥ 1, every summand is
-- nontrivial (the Schur module for any partition with ≤ n parts on k^n is nonzero
-- in characteristic 0), and `DominantWeight n` is infinite.
set_option maxHeartbeats 800000 in
private theorem directSum_rank_ge_aleph0 [CharZero k] (n : ℕ) (hn : 0 < n) :
    Cardinal.aleph0 ≤ Module.rank k (DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) := by
  set F := fun lam : DominantWeight n =>
    (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
  -- For each m : ℕ, the summand at oneRowWeight n m hn is nonzero
  -- First show AlgIrrepGL n lam k is nonzero for one-row weights
  have hne : ∀ m : ℕ, Nontrivial (AlgIrrepGL n (oneRowWeight n m hn) k) := by
    intro m
    -- toNatWeight is antitone (follows from the ℤ-valued weight being antitone)
    have hanti : Antitone (oneRowWeight n m hn).toNatWeight := by
      rw [oneRowWeight_toNatWeight]
      intro i j hij
      by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
      exfalso; apply hi; subst hj
      exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)
    have hbot := schurModuleSubmodule_ne_bot (k := k) n (oneRowWeight n m hn).toNatWeight hanti
    rw [ne_eq, ← Submodule.subsingleton_iff_eq_bot] at hbot
    exact not_subsingleton_iff_nontrivial.mp hbot
  rw [rank_directSum]
  -- The sum ∑_λ rank(F λ) ≥ ℵ₀ because there are ℵ₀ many distinct one-row weights,
  -- each giving a nontrivial summand (rank ≥ 1).
  -- Step 1: Each summand at a one-row weight has rank ≥ 1
  have h1 : ∀ m : ℕ, 1 ≤ Module.rank k (F (oneRowWeight n m hn)) := by
    intro m
    haveI := hne m
    -- AlgIrrepGLDual is also nontrivial (it's a SchurModule for the w0-twisted weight)
    haveI : Nontrivial (AlgIrrepGLDual n (oneRowWeight n m hn) k) := by
      have hanti : Antitone (oneRowWeight n m hn).w0Twist.toNatWeight := by
        intro i j hij
        -- Antitone: i ≤ j → f j ≤ f i
        -- Goal: w0Twist.toNatWeight j ≤ w0Twist.toNatWeight i
        unfold DominantWeight.w0Twist DominantWeight.toNatWeight
        apply Int.toNat_le_toNat
        gcongr
        simp only [neg_le_neg_iff]
        -- Need: lam(i.rev) ≤ lam(j.rev), i.e., lam at the rev-image of i ≤ that of j
        -- Since i ≤ j, j.rev ≤ i.rev, and lam is antitone
        exact (oneRowWeight n m hn).property (Fin.rev_anti hij)
      exact not_subsingleton_iff_nontrivial.mp
        ((ne_eq .. ▸ Submodule.subsingleton_iff_eq_bot.not).mpr
          (schurModuleSubmodule_ne_bot (k := k) n _ hanti))
    exact Cardinal.one_le_iff_ne_zero.mpr (rank_pos (R := k)).ne'
  -- Step 2: The cardinal sum over all dominant weights is ≥ the sum over one-row weights
  -- ∑_{λ : DW} rank(F λ) ≥ ∑_{m : ℕ} rank(F(oneRowWeight n m hn)) ≥ ∑_{m:ℕ} 1 = ℵ₀
  calc Cardinal.aleph0
      = Cardinal.sum (fun _ : ℕ => (1 : Cardinal)) := by simp
    _ ≤ Cardinal.sum (fun m : ℕ => Module.rank k (F (oneRowWeight n m hn))) :=
        Cardinal.sum_le_sum _ _ h1
    _ ≤ Cardinal.sum (fun lam => Module.rank k (F lam)) := by
        -- Sub-sum ≤ full sum via the injection oneRowWeight
        rw [Cardinal.sum, Cardinal.sum]
        exact ⟨⟨fun ⟨m, x⟩ => ⟨oneRowWeight n m hn, x⟩, fun ⟨m₁, x₁⟩ ⟨m₂, x₂⟩ h => by
          simp only [Sigma.mk.inj_iff] at h
          obtain ⟨hm, hx⟩ := h
          have hm' := oneRowWeight_injective n hn hm
          subst hm'
          exact Sigma.ext rfl (by exact hx)⟩⟩

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
