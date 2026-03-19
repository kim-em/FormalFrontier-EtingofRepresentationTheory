import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import EtingofRepresentationTheory.Chapter2.Sl2Defs
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Theorem 2.1.1: Classification of irreducible representations of U(sl(2))

Let k = ℂ be the field of complex numbers. Then:

(i) The algebra U(sl(2)) has exactly one irreducible representation V_d of each dimension d,
up to equivalence; this representation is realized in the space of homogeneous polynomials of
two variables x, y of degree d - 1.

(ii) Any indecomposable finite dimensional representation of U(sl(2)) is irreducible. That is,
any finite dimensional representation of U(sl(2)) is a direct sum of irreducible representations.

## Mathlib correspondence

Partial match. Mathlib has `LieAlgebra`, `LieModule`,
`LieAlgebra.SpecialLinear.sl` (special linear Lie algebra), and
`LieModule.IsIrreducible`, but the classification of irreducible
sl(2)-representations and complete reducibility are not in Mathlib.

## Formalization note

We formalize sl(2, ℂ) as `LieAlgebra.SpecialLinear.sl (Fin 2) ℂ`,
the traceless 2×2 complex matrices.
Part (i) states existence and uniqueness (up to Lie module isomorphism) of an irreducible
representation in each positive dimension. Part (ii) states complete reducibility: every
finite-dimensional Lie module over sl(2, ℂ) has a complemented lattice of Lie submodules.
-/

open scoped Matrix
open LieModule Module

namespace Etingof

/-! ## Primitive vector theory for sl(2)-modules

We prove that every nontrivial finite-dimensional irreducible sl(2, ℂ)-module has a primitive
(highest weight) vector, and use this to classify irreducible representations. -/

section PrimitiveVectorTheory

open Sl2Irrep

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [LieRingModule sl2 V] [LieModule ℂ sl2 V]

/-- In any nontrivial finite-dimensional sl2-module over ℂ, there exists an eigenvalue μ of h
such that μ+2 is not an eigenvalue. -/
private lemma exists_highest_eigenvalue [Nontrivial V] :
    ∃ μ : ℂ, (toEnd ℂ sl2 V sl2_h).HasEigenvalue μ ∧
    ¬(toEnd ℂ sl2 V sl2_h).HasEigenvalue (μ + 2) := by
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (toEnd ℂ sl2 V sl2_h)
  by_contra h_all
  push_neg at h_all
  have h_chain : ∀ n : ℕ, (toEnd ℂ sl2 V sl2_h).HasEigenvalue (μ₀ + 2 * n) := by
    intro n; induction n with
    | zero => simpa using hμ₀
    | succ n ih =>
      have := h_all _ ih
      convert this using 1; push_cast; ring
  have h_inj : Function.Injective (fun n : ℕ ↦ μ₀ + 2 * (n : ℂ)) := by
    intro a b hab
    have h1 : 2 * (a : ℂ) = 2 * (b : ℂ) := add_left_cancel hab
    have h2 : (a : ℂ) = (b : ℂ) := mul_left_cancel₀ (two_ne_zero) h1
    exact_mod_cast h2
  have h_li := Module.End.eigenvectors_linearIndependent' (toEnd ℂ sl2 V sl2_h)
    (fun n : ℕ ↦ μ₀ + 2 * (n : ℂ)) h_inj
    (fun n ↦ (h_chain n).exists_hasEigenvector.choose)
    (fun n ↦ (h_chain n).exists_hasEigenvector.choose_spec)
  exact Module.Finite.not_linearIndependent_of_infinite _ h_li

/-- In any nontrivial finite-dimensional irreducible sl(2, ℂ)-module,
there exists a primitive vector with respect to the standard sl₂ triple. -/
private lemma exists_primitiveVector [Nontrivial V]
    (hirr : LieModule.IsIrreducible ℂ sl2 V) :
    ∃ (v : V) (μ : ℂ), sl2_triple.HasPrimitiveVectorWith v μ := by
  obtain ⟨μ, hμ, hμ2⟩ := exists_highest_eigenvalue (V := V)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨v, μ, ?_⟩
  constructor
  · exact hv.2
  · exact Module.End.mem_eigenspace_iff.mp hv.1
  · -- e·v has h-eigenvalue μ+2; since μ+2 is not an eigenvalue of h, e·v = 0
    by_contra he_ne
    apply hμ2
    have hmem : ⁅sl2_e, v⁆ ∈ (toEnd ℂ sl2 V sl2_h).eigenspace (μ + 2) := by
      rw [Module.End.mem_eigenspace_iff]
      show ⁅sl2_h, ⁅sl2_e, v⁆⁆ = (μ + 2) • ⁅sl2_e, v⁆
      have hv_eq : ⁅sl2_h, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
      calc ⁅sl2_h, ⁅sl2_e, v⁆⁆
          = ⁅⁅sl2_h, sl2_e⁆, v⁆ + ⁅sl2_e, ⁅sl2_h, v⁆⁆ := leibniz_lie ..
        _ = ⁅(2 : ℕ) • sl2_e, v⁆ + ⁅sl2_e, μ • v⁆ := by
            rw [sl2_triple.lie_h_e_nsmul, hv_eq]
        _ = (2 : ℕ) • ⁅sl2_e, v⁆ + μ • ⁅sl2_e, v⁆ := by
            rw [nsmul_lie, lie_smul]
        _ = (μ + 2) • ⁅sl2_e, v⁆ := by
            rw [← Nat.cast_smul_eq_nsmul ℂ, ← add_smul, add_comm]; norm_cast
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, he_ne⟩

/-- Every element of sl2 decomposes as a ℂ-linear combination of sl2_h, sl2_e, sl2_f. -/
private lemma sl2_decomp (x : sl2) :
    x = x.val 0 0 • sl2_h + x.val 0 1 • sl2_e + x.val 1 0 • sl2_f := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2_h, sl2_e, sl2_f,
      LieAlgebra.SpecialLinear.val_singleSubSingle,
      LieAlgebra.SpecialLinear.val_single,
      Matrix.single, smul_eq_mul, sl2_traceless x, Pi.add_apply, Pi.smul_apply]

/-- ⁅x, f^k · m⁆ is in the span of the f-orbit for any x : sl2. -/
private lemma lie_primitiveOrbit_mem (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ))
    (x : sl2) (k : ℕ) (hk : k ≤ n) :
    ⁅x, ((toEnd ℂ sl2 V sl2_f) ^ k) m⁆ ∈ Submodule.span ℂ
      (Set.range (fun j : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (j : ℕ)) m)) := by
  set S := Submodule.span ℂ
    (Set.range (fun j : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (j : ℕ)) m))
  -- Decompose x = x₀₀ • h + x₀₁ • e + x₁₀ • f
  rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
  refine S.add_mem (S.add_mem (S.smul_mem _ ?_) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
  · -- ⁅h, f^k · m⁆ = (n - 2k) • f^k · m ∈ S
    rw [P.lie_h_pow_toEnd_f k]
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
  · -- ⁅e, f^k · m⁆ ∈ S
    by_cases hk0 : k = 0
    · subst hk0; simp [P.lie_e, S.zero_mem]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [P.lie_e_pow_succ_toEnd_f k']
      exact S.smul_mem _ (Submodule.subset_span ⟨⟨k', by omega⟩, rfl⟩)
  · -- ⁅f, f^k · m⁆ = f^(k+1) · m ∈ S
    have : ⁅sl2_f, ((toEnd ℂ sl2 V sl2_f) ^ k) m⁆ =
        ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) m := by
      rw [pow_succ']; rfl
    rw [this]
    by_cases hk_last : k + 1 ≤ n
    · exact Submodule.subset_span ⟨⟨k + 1, by omega⟩, by simp [pow_succ']⟩
    · have hkn : k = n := by omega
      subst hkn
      rw [P.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)]
      exact S.zero_mem

/-- The span of the f-orbit of a primitive vector is a LieSubmodule. -/
private lemma primitiveOrbit_lieInvariant (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    let S := Submodule.span ℂ
      (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) m))
    ∀ (x : sl2) (v : V), v ∈ S → ⁅x, v⁆ ∈ S := by
  intro S x v hv
  -- ⁅x, ·⁆ is linear, so preimage of S is a submodule containing the generators
  have hle : S ≤ S.comap (toEnd ℂ sl2 V x) := by
    rw [Submodule.span_le]
    intro w ⟨⟨k, hk⟩, hw⟩
    show (toEnd ℂ sl2 V x) w ∈ S
    rw [← hw]
    exact lie_primitiveOrbit_mem m n P x k (by omega)
  exact hle hv

/-- The f-orbit of a primitive vector spans the whole module (for irreducible modules). -/
private lemma primitiveOrbit_span_eq_top
    (hirr : LieModule.IsIrreducible ℂ sl2 V) (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    Submodule.span ℂ
      (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) m)) = ⊤ := by
  set S := Submodule.span ℂ
    (Set.range (fun k : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) m))
  -- Construct S as a LieSubmodule
  let N : LieSubmodule ℂ sl2 V :=
    LieSubmodule.mk S (fun {x v} hv ↦ primitiveOrbit_lieInvariant m n P x v hv)
  -- N contains m ≠ 0, so by irreducibility N = ⊤
  have hne : N ≠ ⊥ := by
    intro h
    have : m ∈ (⊥ : LieSubmodule ℂ sl2 V) := by
      rw [← h]; show m ∈ S
      exact Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ n⟩, by simp⟩
    simp [LieSubmodule.mem_bot] at this
    exact P.ne_zero this
  have htop := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hne
  have : N.toSubmodule = ⊤ := by rw [htop]; rfl
  exact this

/-- The f-orbit vectors of a primitive vector are linearly independent. -/
private lemma primitiveOrbit_linearIndependent (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    LinearIndependent ℂ (fun k : Fin (n + 1) ↦ ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) m) := by
  -- These are eigenvectors of h with distinct eigenvalues n, n-2, ..., -n
  apply Module.End.eigenvectors_linearIndependent' (toEnd ℂ sl2 V sl2_h)
    (fun k : Fin (n + 1) ↦ ((n : ℂ) - 2 * (k : ℕ)))
  · -- Injectivity of eigenvalue map
    intro a b hab
    have h := hab
    simp only at h
    -- h : ↑n - 2 * ↑↑a = ↑n - 2 * ↑↑b
    exact Fin.ext (by exact_mod_cast (mul_left_cancel₀ (two_ne_zero (α := ℂ))
      (neg_injective (add_left_cancel (show (n : ℂ) + -(2 * ↑↑a) = ↑n + -(2 * ↑↑b) from by
        simp only [← sub_eq_add_neg]; exact h)))))
  · intro ⟨k, hk⟩
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact P.lie_h_pow_toEnd_f k
    · exact P.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega)

/-- The f-orbit vectors form a basis for irreducible modules. -/
private noncomputable def primitiveOrbit_basis
    (hirr : LieModule.IsIrreducible ℂ sl2 V) (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    Basis (Fin (n + 1)) ℂ V :=
  Basis.mk (primitiveOrbit_linearIndependent m n P)
    (primitiveOrbit_span_eq_top hirr m n P ▸ le_refl _)

/-- For an irreducible module with primitive vector of eigenvalue n, the dimension is n+1. -/
private lemma primitiveVector_dim
    (hirr : LieModule.IsIrreducible ℂ sl2 V) (m : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    Module.finrank ℂ V = n + 1 := by
  rw [finrank_eq_card_basis (primitiveOrbit_basis hirr m n P), Fintype.card_fin]

/-- Two irreducible sl2-modules with primitive vectors of the same weight are isomorphic
as Lie modules. The isomorphism sends f^k·m_V ↦ f^k·m_W. -/
private noncomputable def sl2_irrep_equiv
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule sl2 W] [LieModule ℂ sl2 W]
    (hirrV : LieModule.IsIrreducible ℂ sl2 V)
    (hirrW : LieModule.IsIrreducible ℂ sl2 W)
    (mV : V) (mW : W) (n : ℕ)
    (PV : sl2_triple.HasPrimitiveVectorWith mV (n : ℂ))
    (PW : sl2_triple.HasPrimitiveVectorWith mW (n : ℂ)) :
    V ≃ₗ⁅ℂ, sl2⁆ W := by
  -- Build the linear equiv from f-orbit bases
  let bV := primitiveOrbit_basis hirrV mV n PV
  let bW := primitiveOrbit_basis hirrW mW n PW
  let φ : V ≃ₗ[ℂ] W := bV.equiv bW (Equiv.refl _)
  -- Construct the LieModuleEquiv
  exact {
    toLinearMap := φ.toLinearMap
    map_lie' := by
      intro x v
      -- φ sends bV i to bW i
      have hφ : ∀ i, φ (bV i) = bW i := fun i => by simp [φ, Basis.equiv_apply]
      -- φ maps f^k·mV to f^k·mW
      have hφ_pow : ∀ k (hk : k < n + 1),
          φ (((toEnd ℂ sl2 V sl2_f) ^ k) mV) = ((toEnd ℂ sl2 W sl2_f) ^ k) mW := by
        intro k hk
        have h1 : bV ⟨k, hk⟩ = ((toEnd ℂ sl2 V sl2_f) ^ k) mV := Basis.mk_apply _ _ _
        have h2 : bW ⟨k, hk⟩ = ((toEnd ℂ sl2 W sl2_f) ^ k) mW := Basis.mk_apply _ _ _
        rw [← h1, hφ, h2]
      -- Key: φ(⁅x, f^k·mV⁆) = ⁅x, f^k·mW⁆ for all valid k
      have h_key : ∀ (k : ℕ) (hk : k < n + 1),
          φ (⁅x, ((toEnd ℂ sl2 V sl2_f) ^ k) mV⁆) =
          ⁅x, ((toEnd ℂ sl2 W sl2_f) ^ k) mW⁆ := by
        intro k hk
        -- Decompose x = a•h + b•e + c•f
        rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie,
            map_add, map_add, map_smul, map_smul, map_smul,
            sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
        congr 1; congr 1
        · -- h case
          rw [PV.lie_h_pow_toEnd_f k, PW.lie_h_pow_toEnd_f k, map_smul, hφ_pow k hk]
        · -- e case
          by_cases hk0 : k = 0
          · subst hk0; simp [PV.lie_e, PW.lie_e]
          · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            rw [PV.lie_e_pow_succ_toEnd_f k', PW.lie_e_pow_succ_toEnd_f k', map_smul,
                hφ_pow k' (by omega)]
        · -- f case
          have hfV : ⁅sl2_f, ((toEnd ℂ sl2 V sl2_f) ^ k) mV⁆ =
              ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) mV := by rw [pow_succ']; rfl
          have hfW : ⁅sl2_f, ((toEnd ℂ sl2 W sl2_f) ^ k) mW⁆ =
              ((toEnd ℂ sl2 W sl2_f) ^ (k + 1)) mW := by rw [pow_succ']; rfl
          rw [hfV, hfW]
          by_cases hk_last : k + 1 ≤ n
          · rw [hφ_pow (k + 1) (by omega)]
          · have hkn : k + 1 = n + 1 := by omega
            rw [hkn, PV.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast),
                PW.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast), map_zero]
      -- Extend from basis to all v by linearity
      show φ (⁅x, v⁆) = ⁅x, φ v⁆
      rw [show v = ∑ i, bV.repr v i • bV i from (bV.sum_repr v).symm]
      simp only [lie_sum, lie_smul, map_sum, map_smul]
      congr 1; ext ⟨k, hk⟩; congr 1
      -- Need: φ(⁅x, bV ⟨k,hk⟩⁆) = ⁅x, φ(bV ⟨k,hk⟩)⁆
      -- bV = primitiveOrbit_basis = Basis.mk
      have hbV : bV ⟨k, hk⟩ = ((toEnd ℂ sl2 V sl2_f) ^ k) mV := by
        show primitiveOrbit_basis hirrV mV n PV ⟨k, hk⟩ = _
        exact Basis.mk_apply _ _ _
      rw [hbV, h_key k hk, ← hφ_pow k hk]
    invFun := φ.symm
    left_inv := φ.symm_apply_apply
    right_inv := φ.apply_symm_apply
  }

end PrimitiveVectorTheory

/-- Part (i): For each positive integer d, there is exactly one irreducible representation
of sl(2, ℂ) of dimension d, up to isomorphism.
(Etingof Theorem 2.1.1(i)) -/
theorem Theorem_2_1_1_i (d : ℕ+) :
    -- Existence: there is an irreducible representation of dimension d
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
       (_ : LieRingModule sl2 V) (_ : LieModule ℂ sl2 V),
       Module.finrank ℂ V = d ∧ LieModule.IsIrreducible ℂ sl2 V) ∧
    -- Uniqueness: any two irreducible representations of the same dimension are isomorphic
    (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
       [LieRingModule sl2 V] [LieModule ℂ sl2 V]
       [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
       [LieRingModule sl2 W] [LieModule ℂ sl2 W],
       Module.finrank ℂ V = d → LieModule.IsIrreducible ℂ sl2 V →
       Module.finrank ℂ W = d → LieModule.IsIrreducible ℂ sl2 W →
       Nonempty (V ≃ₗ⁅ℂ, sl2⁆ W)) := by
  constructor
  · -- Existence: use the d-dimensional representation from Sl2Irrep
    have hd : NeZero (d : ℕ) := ⟨PNat.ne_zero d⟩
    exact ⟨Fin d → ℂ, inferInstance, inferInstance,
      Sl2Irrep.irrepLieRingModule d, Sl2Irrep.irrepLieModule d,
      Sl2Irrep.irrep_finrank d, Sl2Irrep.irrep_isIrreducible d⟩
  · -- Uniqueness: both V and W have primitive vectors of the same weight, yielding an isomorphism
    intro V W _ _ _ _ _ _ _ _ _ _  hdV hirrV hdW hirrW
    have hntV : Nontrivial V := by
      rw [← finrank_pos_iff (R := ℂ), hdV]; exact d.pos
    have hntW : Nontrivial W := by
      rw [← finrank_pos_iff (R := ℂ), hdW]; exact d.pos
    -- Get primitive vectors
    obtain ⟨mV, μV, PV⟩ := exists_primitiveVector hirrV
    obtain ⟨mW, μW, PW⟩ := exists_primitiveVector hirrW
    -- Primitive vector eigenvalues are natural numbers
    obtain ⟨nV, hnV⟩ := PV.exists_nat
    obtain ⟨nW, hnW⟩ := PW.exists_nat
    -- Rewrite with natural number eigenvalues
    rw [hnV] at PV; rw [hnW] at PW
    -- Both have dimension n + 1, so the weights are equal
    have hdimV := primitiveVector_dim hirrV mV nV PV
    have hdimW := primitiveVector_dim hirrW mW nW PW
    have hneq : nV = nW := by omega
    subst hneq
    exact ⟨sl2_irrep_equiv hirrV hirrW mV mW nV PV PW⟩

/-- Part (ii): Any finite-dimensional representation of sl(2, ℂ) is completely reducible.
Every Lie submodule has a complementary Lie submodule, i.e., the lattice of Lie submodules
is complemented. This is equivalent to saying every finite-dimensional representation
decomposes as a direct sum of irreducible representations.
(Etingof Theorem 2.1.1(ii)) -/
theorem Theorem_2_1_1_ii (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V] :
    ComplementedLattice (LieSubmodule ℂ sl2 V) :=
  -- Complete reducibility for sl(2) follows from Weyl's theorem: every finite-dimensional
  -- representation of a semisimple Lie algebra over a field of characteristic zero is
  -- completely reducible. sl(2) is simple hence semisimple.
  -- Weyl's theorem is not in Mathlib (no ComplementedLattice instance for LieSubmodule
  -- of representations of semisimple Lie algebras). This requires either:
  -- (1) Weyl's unitarian trick (using compact real form), or
  -- (2) Whitehead's lemma (Ext¹ vanishing for semisimple Lie algebras), or
  -- (3) Direct proof using Casimir element.
  -- All approaches require substantial infrastructure not yet in Mathlib.
  sorry

end Etingof
