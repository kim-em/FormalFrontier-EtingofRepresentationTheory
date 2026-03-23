import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Tactic.NoncommRing
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

/-- In an irreducible sl2-module with primitive vector of weight n, the h-eigenspace
for any eigenvalue not of the form n-2k (k = 0,...,n) is trivial. -/
private lemma eigenspace_eq_bot_of_not_weight
    (hirr : LieModule.IsIrreducible ℂ sl2 V) (m₀ : V) (n : ℕ)
    (P : sl2_triple.HasPrimitiveVectorWith m₀ (n : ℂ))
    (mu : ℂ) (hmu : ∀ k : Fin (n + 1), mu ≠ (n : ℂ) - 2 * ↑k.val) :
    (toEnd ℂ sl2 V sl2_h).eigenspace mu = ⊥ := by
  by_contra h_ne
  simp only [Submodule.eq_bot_iff, not_forall, exists_prop] at h_ne
  obtain ⟨v, hv_mem, hv_ne⟩ := h_ne
  -- Build n+2 eigenvectors: v plus the f-orbit basis, all with distinct eigenvalues
  have hdim := primitiveVector_dim hirr m₀ n P
  have hli := Module.End.eigenvectors_linearIndependent' (toEnd ℂ sl2 V sl2_h)
    (fun i : Option (Fin (n + 1)) => match i with | none => mu | some k => (n : ℂ) - 2 * ↑k.val)
    (by -- injectivity of eigenvalue map
      intro a b hab; match a, b with
      | none, none => rfl
      | none, some k => exact absurd hab (hmu k)
      | some k, none => exact absurd hab.symm (hmu k)
      | some a, some b =>
        congr 1; ext; exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := ℂ))
          (neg_injective (add_left_cancel (show (n : ℂ) + -(2 * ↑↑a) = ↑n + -(2 * ↑↑b) from by
            simp only [← sub_eq_add_neg]; exact hab))))
    (fun i => match i with
      | none => v
      | some k => ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) m₀)
    (fun i => match i with
      | none => ⟨hv_mem, hv_ne⟩
      | some k =>
        ⟨Module.End.mem_eigenspace_iff.mpr (P.lie_h_pow_toEnd_f k),
         P.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega)⟩)
  have : Fintype.card (Option (Fin (n + 1))) ≤ finrank ℂ V :=
    hli.fintype_card_le_finrank
  simp [Fintype.card_option, hdim] at this

/-- Commutation formula: ⁅h, f^k u⁆ = f^k(⁅h, u⁆) - 2k • f^k u. -/
private lemma h_comm_pow_f (k : ℕ) (u : V) :
    ⁅sl2_h, ((toEnd ℂ sl2 V sl2_f) ^ k) u⁆ =
    ((toEnd ℂ sl2 V sl2_f) ^ k) ⁅sl2_h, u⁆ -
    (2 * (k : ℂ)) • (((toEnd ℂ sl2 V sl2_f) ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- ⁅h, f(f^k u)⁆ = ⁅⁅h,f⁆, f^k u⁆ + ⁅f, ⁅h, f^k u⁆⁆
    have step1 : ⁅sl2_h, ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) u⁆ =
        ⁅⁅sl2_h, sl2_f⁆, ((toEnd ℂ sl2 V sl2_f) ^ k) u⁆ +
        ⁅sl2_f, ⁅sl2_h, ((toEnd ℂ sl2 V sl2_f) ^ k) u⁆⁆ := by
      rw [pow_succ', Module.End.mul_apply]; exact leibniz_lie ..
    rw [step1, sl2_triple.lie_h_f_nsmul, ih, lie_sub, lie_smul, neg_lie, nsmul_lie]
    simp only [pow_succ', Module.End.mul_apply, ← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_ofNat, Nat.cast_succ,
      show ∀ x : V, ⁅sl2_f, x⁆ = (toEnd ℂ sl2 V sl2_f) x from fun _ => rfl]
    rw [show (2 : ℂ) * ((k : ℂ) + 1) = 2 * (k : ℂ) + 2 from by ring, add_smul]
    abel

/-- Commutation formula: e(f^{k+1} u) = f^{k+1}(eu) + (k+1)·f^k(hu - k·u). -/
private lemma e_f_pow_succ_comm (k : ℕ) (u : V) :
    ⁅sl2_e, ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) u⁆ =
    ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) ⁅sl2_e, u⁆ +
    ((k + 1 : ℂ)) • (((toEnd ℂ sl2 V sl2_f) ^ k) ⁅sl2_h, u⁆ -
    (k : ℂ) • (((toEnd ℂ sl2 V sl2_f) ^ k) u)) := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, Nat.cast_zero, zero_add, one_smul, zero_smul, sub_zero]
    -- Goal: ⁅e, f u⁆ = f(eu) + hu. Use leibniz: ⁅e, ⁅f, u⁆⁆ = ⁅⁅e,f⁆, u⁆ + ⁅f, ⁅e, u⁆⁆
    -- (toEnd f) u = ⁅f, u⁆ by rfl
    change ⁅sl2_e, ⁅sl2_f, u⁆⁆ = ⁅sl2_f, ⁅sl2_e, u⁆⁆ + ⁅sl2_h, u⁆
    rw [leibniz_lie, sl2_triple.lie_e_f, add_comm]
  | succ k ih =>
    -- ⁅e, f(f^{k+1} u)⁆ = ⁅h, f^{k+1} u⁆ + ⁅f, ⁅e, f^{k+1} u⁆⁆
    have step1 : ⁅sl2_e, ((toEnd ℂ sl2 V sl2_f) ^ (k + 2)) u⁆ =
        ⁅⁅sl2_e, sl2_f⁆, ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) u⁆ +
        ⁅sl2_f, ⁅sl2_e, ((toEnd ℂ sl2 V sl2_f) ^ (k + 1)) u⁆⁆ := by
      rw [show (k + 2) = (k + 1) + 1 from by omega, pow_succ', Module.End.mul_apply]
      exact leibniz_lie ..
    rw [step1, sl2_triple.lie_e_f, ih, h_comm_pow_f (k + 1) u,
      lie_add, lie_smul, lie_sub, lie_smul]
    simp only [pow_succ', Module.End.mul_apply, Nat.cast_succ,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat,
      show ∀ x : V, ⁅sl2_f, x⁆ = (toEnd ℂ sl2 V sl2_f) x from fun _ => rfl]
    module

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

/-! ## Casimir element and complete reducibility

The Casimir element C = h² + 2ef + 2fe of sl(2) commutes with the action of sl(2) on any
module V. On the irreducible V_n (dimension n+1), C acts as the scalar n(n+2).
This is used to prove complete reducibility by strong induction on dimension. -/

section Casimir

open Sl2Irrep

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [LieRingModule sl2 V] [LieModule ℂ sl2 V]

/-- The Casimir element of sl(2) acting on a module V:
C = h² + 2ef + 2fe where h,e,f act via the Lie module structure. -/
noncomputable def sl2_casimir : Module.End ℂ V :=
  (toEnd ℂ sl2 V sl2_h) ^ 2 +
  2 • ((toEnd ℂ sl2 V sl2_e) * (toEnd ℂ sl2 V sl2_f)) +
  2 • ((toEnd ℂ sl2 V sl2_f) * (toEnd ℂ sl2 V sl2_e))

-- Operator relations in Module.End ℂ V: HE = EH + 2E, HF = FH - 2F, EF = FE + H
private lemma end_HE :
    toEnd ℂ sl2 V sl2_h * toEnd ℂ sl2 V sl2_e =
    toEnd ℂ sl2 V sl2_e * toEnd ℂ sl2 V sl2_h + 2 • toEnd ℂ sl2 V sl2_e := by
  have := (toEnd ℂ sl2 V).map_lie sl2_h sl2_e
  rw [sl2_triple.lie_h_e_nsmul, map_nsmul, LieRing.of_associative_ring_bracket] at this
  -- this : 2 • E = H * E - E * H
  rw [eq_comm, sub_eq_iff_eq_add, add_comm] at this; exact this

private lemma end_HF :
    toEnd ℂ sl2 V sl2_h * toEnd ℂ sl2 V sl2_f =
    toEnd ℂ sl2 V sl2_f * toEnd ℂ sl2 V sl2_h - 2 • toEnd ℂ sl2 V sl2_f := by
  have := (toEnd ℂ sl2 V).map_lie sl2_h sl2_f
  rw [sl2_triple.lie_h_f_nsmul, map_neg, map_nsmul, LieRing.of_associative_ring_bracket] at this
  -- this : -(2 • F) = H * F - F * H
  rw [eq_comm, sub_eq_iff_eq_add] at this
  -- this : H * F = -(2 • F) + F * H
  rw [this]; abel

private lemma end_EF :
    toEnd ℂ sl2 V sl2_e * toEnd ℂ sl2 V sl2_f =
    toEnd ℂ sl2 V sl2_f * toEnd ℂ sl2 V sl2_e + toEnd ℂ sl2 V sl2_h := by
  have := (toEnd ℂ sl2 V).map_lie sl2_e sl2_f
  rw [lie_e_f, LieRing.of_associative_ring_bracket] at this
  -- this : H = E * F - F * E
  rw [eq_comm, sub_eq_iff_eq_add, add_comm] at this; exact this

/-- The Casimir element commutes with the action of any x : sl(2).
Proof: [C, x] = 0 for x = h, e, f (hence for all x by linearity).
Computation uses [h,e] = 2e, [h,f] = -2f, [e,f] = h. -/
-- Helper: the casimir in terms of FE instead of EF
private lemma sl2_casimir_eq :
    sl2_casimir (V := V) = (toEnd ℂ sl2 V sl2_h) ^ 2 +
    2 • toEnd ℂ sl2 V sl2_h + 4 • (toEnd ℂ sl2 V sl2_f * toEnd ℂ sl2 V sl2_e) := by
  unfold sl2_casimir
  have hEF := end_EF (V := V)
  simp only [sq]
  rw [hEF]
  simp only [smul_add]
  abel

private lemma sl2_casimir_comm (x : sl2) :
    sl2_casimir (V := V) ∘ₗ (toEnd ℂ sl2 V x) =
    (toEnd ℂ sl2 V x) ∘ₗ sl2_casimir := by
  set H := toEnd ℂ sl2 V sl2_h; set E := toEnd ℂ sl2 V sl2_e; set F := toEnd ℂ sl2 V sl2_f
  have hHE := end_HE (V := V)  -- HE = EH + 2E
  have hHF := end_HF (V := V)  -- HF = FH - 2F
  have hEF := end_EF (V := V)  -- EF = FE + H
  -- Derive pointwise relations (H*E = E*H + 2•E etc. applied to vectors)
  have pHE : ∀ w, H (E w) = E (H w) + 2 • E w := LinearMap.congr_fun hHE
  have pHF : ∀ w, H (F w) = F (H w) - 2 • F w := LinearMap.congr_fun hHF
  have pEF : ∀ w, E (F w) = F (E w) + H w := LinearMap.congr_fun hEF
  -- Decompose x into h, e, f basis
  rw [sl2_decomp x]
  simp only [map_add, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp]
  -- After decomposition and simp, we need C∘X = X∘C for each basis element (up to smul)
  -- Use `congr` to strip the outer structure, leaving 3 goals
  -- Prove each basis case via pointwise computation
  have casimir_rw : ∀ (X : Module.End ℂ V), sl2_casimir ∘ₗ X = X ∘ₗ sl2_casimir →
      ∀ (c : ℂ), c • (sl2_casimir ∘ₗ X) = c • (X ∘ₗ sl2_casimir) :=
    fun _ h c => by rw [h]
  -- Tactic block for each basis case: unfold, rewrite to normal form, close with module
  -- After the first simp, goal is: H(H(Xv)) + 2•E(F(Xv)) + 2•F(E(Xv)) = X(H(Hv) + 2•E(Fv) + 2•F(Ev))
  -- We distribute X over the RHS sum, then rewrite using pHE/pHF/pEF, then close with module
  have hComm : ∀ X, X = H ∨ X = E ∨ X = F → sl2_casimir ∘ₗ X = X ∘ₗ sl2_casimir := by
    intro X hX; ext v; unfold sl2_casimir
    simp only [sq, Module.End.mul_eq_comp, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply,
      show toEnd ℂ sl2 V sl2_h = H from rfl, show toEnd ℂ sl2 V sl2_e = E from rfl,
      show toEnd ℂ sl2 V sl2_f = F from rfl]
    -- LHS has X applied first (innermost), then H²+2EF+2FE
    -- RHS has H²+2EF+2FE applied first, then X
    -- Both sides are in the form f(g(h(v))) for various f,g,h
    -- Use pHE/pHF/pEF to rewrite H∘E, H∘F, E∘F patterns, distributing over sums
    rcases hX with rfl | rfl | rfl <;> {
      -- Each case: distribute outer operator on RHS, then rewrite H∘E, H∘F, E∘F
      -- patterns using pointwise rules, distribute again, then close with module.
      -- We alternate: distribute (map_add/map_nsmul/map_sub) then rewrite (pHE/pHF/pEF)
      -- until all patterns are in "normal form" with only F(E(H(v)))‐like atoms
      simp only [map_add, map_sub, map_nsmul, pHE, pHF, pEF]
      module }
  congr 1
  · congr 1
    · congr 1; exact hComm H (Or.inl rfl)
    · congr 1; exact hComm E (Or.inr (Or.inl rfl))
  · congr 1; exact hComm F (Or.inr (Or.inr rfl))

/-- The eigenspaces of the Casimir element are Lie submodules. -/
private lemma casimir_eigenspace_lie_invariant (c₀ : ℂ) :
    ∀ (x : sl2) (v : V),
    v ∈ (sl2_casimir (V := V)).eigenspace c₀ →
      ⁅x, v⁆ ∈ (sl2_casimir (V := V)).eigenspace c₀ := by
  intro x v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcomm := sl2_casimir_comm (V := V) x
  have hCxv : sl2_casimir (V := V) (⁅x, v⁆) = (toEnd ℂ sl2 V x) (sl2_casimir v) :=
    LinearMap.congr_fun hcomm v
  rw [hCxv, hv, map_smul, LieModule.toEnd_apply_apply]

/-- On an irreducible module V with primitive vector of weight n,
the Casimir acts as the scalar n*(n+2). -/
private lemma casimir_on_irreducible_scalar
    (hirr : LieModule.IsIrreducible ℂ sl2 V) [Nontrivial V]
    (m : V) (n : ℕ) (P : sl2_triple.HasPrimitiveVectorWith m (n : ℂ)) :
    sl2_casimir (V := V) = (n * (n + 2) : ℂ) • (1 : Module.End ℂ V) := by
  -- Step 1: Compute C·m = n(n+2)·m
  -- Using C = H² + 2H + 4FE (from sl2_casimir_eq)
  set H := toEnd ℂ sl2 V sl2_h
  set E := toEnd ℂ sl2 V sl2_e
  set F := toEnd ℂ sl2 V sl2_f
  set c := (n * (n + 2) : ℂ)
  -- Extract primitive vector properties as endomorphism equations
  have hHm : H m = (n : ℂ) • m := by
    show ⁅sl2_h, m⁆ = (n : ℂ) • m; exact P.lie_h
  have hEm : E m = 0 := by
    show ⁅sl2_e, m⁆ = 0; exact P.lie_e
  -- Compute C·m
  have hCm : sl2_casimir (V := V) m = c • m := by
    rw [sl2_casimir_eq]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply]
    rw [hHm, map_smul, hHm, hEm, map_zero, smul_zero]
    simp only [c, smul_smul]
    simp only [add_zero, sq, two_nsmul, ← add_smul, smul_smul]
    congr 1; ring
  -- Step 2: The eigenspace of C for eigenvalue c is a Lie submodule
  -- containing m ≠ 0, hence = ⊤ by irreducibility
  have hm_eigen : m ∈ (sl2_casimir (V := V)).eigenspace c := by
    rw [Module.End.mem_eigenspace_iff]; exact hCm
  -- Build the LieSubmodule
  let N : LieSubmodule ℂ sl2 V :=
    LieSubmodule.mk ((sl2_casimir (V := V)).eigenspace c)
      (fun {x v} hv ↦ casimir_eigenspace_lie_invariant c x v hv)
  have hN_ne : N ≠ ⊥ := by
    intro h
    have : m ∈ (⊥ : LieSubmodule ℂ sl2 V) := h ▸ hm_eigen
    simp [LieSubmodule.mem_bot] at this
    exact P.ne_zero this
  -- By irreducibility, N = ⊤
  have hN_top : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN_ne
  -- Therefore C = c · id: for any v, C v = c • v
  ext v
  have hv_in : v ∈ (⊤ : LieSubmodule ℂ sl2 V) := LieSubmodule.mem_top v
  rw [← hN_top] at hv_in
  have hv_eigen := (Module.End.mem_eigenspace_iff.mp hv_in : sl2_casimir v = c • v)
  simp only [LinearMap.smul_apply]
  exact hv_eigen

end Casimir

/-! ## Complete reducibility of sl(2)-representations

The proof of complete reducibility proceeds by strong induction on the dimension of the
representation. The Casimir element C commutes with the sl(2) action, so its eigenspaces
are Lie submodules. On each irreducible V_n, C acts as n(n+2), and n ↦ n(n+2) is injective
on ℕ, so the Casimir separates non-isomorphic irreducibles.

The proof has three main components:
1. When the Casimir has multiple eigenvalues, the eigenspaces decompose V into smaller
   Lie submodules, each completely reducible by induction.
2. When all composition factors have the same non-trivial Casimir eigenvalue,
   the ker(C - λ) construction gives complements.
3. When all composition factors are trivial (Casimir eigenvalue 0), sl(2) acts as 0
   (because sl(2) is perfect), so every subspace is a Lie submodule and the lattice is
   complemented since ℂ is a field. -/

section CompleteReducibility

open Sl2Irrep

/-- The map n ↦ n(n+2) is injective on ℕ. This is used to show that non-isomorphic
irreducible sl(2)-modules have distinct Casimir eigenvalues. -/
private lemma casimir_eigenvalue_injective :
    Function.Injective (fun n : ℕ ↦ (n : ℂ) * ((n : ℂ) + 2)) := by
  intro a b hab
  -- n ↦ n*(n+2) = n^2 + 2n is strictly monotone on ℕ, hence injective.
  -- Reduce to ℕ arithmetic.
  change (a : ℂ) * ((a : ℂ) + 2) = (b : ℂ) * ((b : ℂ) + 2) at hab
  -- Cast down to ℕ
  have hab_nat : a * (a + 2) = b * (b + 2) := by
    have h1 : ((a : ℂ) * ((a : ℂ) + 2)) = ((a * (a + 2) : ℕ) : ℂ) := by push_cast; ring
    have h2 : ((b : ℂ) * ((b : ℂ) + 2)) = ((b * (b + 2) : ℕ) : ℂ) := by push_cast; ring
    exact_mod_cast h1 ▸ h2 ▸ hab
  -- n*(n+2)+1 = (n+1)^2
  have h1 : a * (a + 2) + 1 = (a + 1) ^ 2 := by ring
  have h2 : b * (b + 2) + 1 = (b + 1) ^ 2 := by ring
  have h3 : (a + 1) ^ 2 = (b + 1) ^ 2 := by omega
  have h4 : a + 1 = b + 1 := Nat.pow_left_injective (by omega) h3
  omega

/-- sl(2) is perfect: every element is a linear combination of Lie brackets.
Specifically, h = [e,f], e = (1/2)[h,e], f = -(1/2)[h,f]. -/
private lemma sl2_isPerfect : ∀ x : sl2,
    x ∈ Submodule.span ℂ (Set.range (fun p : sl2 × sl2 ↦ ⁅p.1, p.2⁆)) := by
  intro x
  rw [Submodule.mem_span]
  intro S hS
  -- x = x₀₀ • h + x₀₁ • e + x₁₀ • f, and h = [e,f], e = (1/2)[h,e], f = -(1/2)[h,f]
  rw [sl2_decomp x]
  refine S.add_mem (S.add_mem (S.smul_mem _ ?_) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
  · -- h = [e, f]
    rw [← lie_e_f]
    exact hS ⟨(sl2_e, sl2_f), rfl⟩
  · -- e = (1/2) • [h, e]
    have : sl2_e = (1/2 : ℂ) • ⁅sl2_h, sl2_e⁆ := by
      rw [sl2_triple.lie_h_e_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      simp [smul_smul]
    rw [this]
    exact S.smul_mem _ (hS ⟨(sl2_h, sl2_e), rfl⟩)
  · -- f = -(1/2) • [h, f]
    have : sl2_f = -(1/2 : ℂ) • ⁅sl2_h, sl2_f⁆ := by
      rw [sl2_triple.lie_h_f_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      simp [smul_smul, neg_smul, smul_neg]
    rw [this]
    exact S.smul_mem _ (hS ⟨(sl2_h, sl2_f), rfl⟩)

/-- If sl(2) acts trivially on a quotient V/N and trivially on N, then sl(2) acts
trivially on V. (Consequence of sl(2) being perfect.) -/
private lemma sl2_acts_trivially_of_quotient_and_sub
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (N : LieSubmodule ℂ sl2 V)
    (hN : ∀ (x : sl2) (v : N), ⁅x, (v : V)⁆ = 0)
    (hQ : ∀ (x : sl2) (v : V), (⁅x, v⁆ : V) ∈ N) :
    ∀ (x : sl2) (v : V), ⁅x, v⁆ = 0 := by
  intro x v
  -- For any y, z ∈ sl(2): [y, [z, v]] = [[y,z], v] + [z, [y, v]]
  -- [z, v] ∈ N (by hQ), so [y, [z, v]] = 0 (by hN)
  -- [[y,z], v] ∈ N (by hQ), so [[y,z], v] is in N
  -- Therefore 0 = [[y,z], v] + [z, [y, v]], and [z, [y, v]] = 0 (by hN since [y,v] ∈ N)
  -- So [[y,z], v] = 0 for all y, z.
  -- Since sl(2) is perfect, every x is a linear combination of brackets, so [x, v] = 0.
  -- But [x, v] ∈ N, and we need [x, v] = 0.
  have hbracket : ∀ (y z : sl2), ⁅⁅y, z⁆, v⁆ = 0 := by
    intro y z
    have h1 : ⁅y, ⁅z, v⁆⁆ = (0 : V) := by
      have hzv : ⁅z, v⁆ ∈ N := hQ z v
      exact hN y ⟨⁅z, v⁆, hzv⟩
    have h2 : ⁅z, ⁅y, v⁆⁆ = (0 : V) := by
      have hyv : ⁅y, v⁆ ∈ N := hQ y v
      exact hN z ⟨⁅y, v⁆, hyv⟩
    have := leibniz_lie y z v
    rw [h1, h2, add_zero] at this
    exact this.symm
  -- Now use perfectness: x is a linear combination of brackets
  -- so ⁅x, v⁆ is a linear combination of ⁅⁅y,z⁆, v⁆ = 0
  have hxv_mem : ⁅x, v⁆ ∈ N := hQ x v
  -- Decompose x = x₀₀ • h + x₀₁ • e + x₁₀ • f
  rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
  -- h = [e,f], so [h,v] = [[e,f],v] = 0
  have hh : ⁅sl2_h, v⁆ = (0 : V) := by rw [← lie_e_f]; exact hbracket sl2_e sl2_f
  -- e = (1/2)[h,e], but we can directly use hbracket for [h,e] case
  -- Actually, we need [[h,e], v] = 0 which gives [2e, v] = 0 hence [e, v] = 0
  have he : ⁅sl2_e, v⁆ = (0 : V) := by
    have h2e := hbracket sl2_h sl2_e
    rw [sl2_triple.lie_h_e_nsmul, nsmul_lie] at h2e
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h2e
    exact h2e.resolve_left (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0))
  have hf : ⁅sl2_f, v⁆ = (0 : V) := by
    have h2f := hbracket sl2_h sl2_f
    rw [sl2_triple.lie_h_f_nsmul, neg_lie, nsmul_lie, neg_eq_zero] at h2f
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h2f
    exact h2f.resolve_left (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0))
  simp [hh, he, hf]

/-- Auxiliary lemma for sl2_trivial_action_of_trivial_subquotients.
Strong induction on dimension: if the Casimir acts as 0 on a module of dimension ≤ d,
then sl(2) acts trivially on it. -/
private lemma sl2_trivial_of_casimir_zero_aux (d : ℕ) :
    ∀ {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule sl2 W] [LieModule ℂ sl2 W],
    finrank ℂ W ≤ d →
    (∀ v : W, sl2_casimir (V := W) v = 0) →
    ∀ (x : sl2) (v : W), ⁅x, v⁆ = 0 := by
  induction d with
  | zero =>
    intro W _ _ _ _ _ hd hC x v
    haveI : Subsingleton W := by
      by_contra h; rw [not_subsingleton_iff_nontrivial] at h; haveI := h
      exact absurd (Module.finrank_pos (R := ℂ) (M := W)) (not_lt.mpr hd)
    simp [Subsingleton.elim v 0]
  | succ d ih =>
    intro W _ _ _ _ _ hd hC x v
    by_cases hirr : LieModule.IsIrreducible ℂ sl2 W
    · -- Irreducible with C = 0: dim must be 1, action is trivial
      haveI : Nontrivial W := (LieSubmodule.nontrivial_iff ℂ sl2 (M := W)).mp hirr.toNontrivial
      obtain ⟨m, μ, P⟩ := exists_primitiveVector hirr
      obtain ⟨n, hn⟩ := P.exists_nat; rw [hn] at P
      have hCscalar := casimir_on_irreducible_scalar hirr m n P
      have hC0 : sl2_casimir (V := W) = 0 := by ext w; exact hC w
      -- n(n+2) = 0
      have hn0 : (n : ℂ) * ((n : ℂ) + 2) = 0 := by
        by_contra hne
        have h1 : (↑n * (↑n + 2) : ℂ) • (1 : Module.End ℂ W) = 0 := by
          rw [← hCscalar, hC0]
        exact (exists_ne (0 : W)).choose_spec
          (LinearMap.congr_fun ((smul_eq_zero.mp h1).resolve_left hne) _)
      -- n = 0 (since n : ℕ)
      have hn_zero : n = 0 := by
        rcases mul_eq_zero.mp hn0 with h1 | h2
        · exact_mod_cast h1
        · exfalso; have h3 : (n : ℂ) + 2 = 0 := h2
          have h4 : (↑(n + 2) : ℂ) = 0 := by push_cast; exact h3
          exact_mod_cast h4
      subst hn_zero
      -- h, e, f all kill the primitive vector m
      have hHm : ⁅sl2_h, m⁆ = (0 : W) := by
        have := P.lie_h; simp only [Nat.cast_zero, zero_smul] at this; exact this
      have hEm : ⁅sl2_e, m⁆ = (0 : W) := P.lie_e
      have hFm : ⁅sl2_f, m⁆ = (0 : W) := by
        have h1 := P.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) rfl
        simpa [pow_succ, pow_zero] using h1
      -- x kills m (by sl2_decomp)
      have hxm : ⁅x, m⁆ = (0 : W) := by
        rw [sl2_decomp x, add_lie, add_lie, smul_lie, smul_lie, smul_lie, hHm, hEm, hFm]; simp
      -- m spans W (basis of size 1)
      let hbasis := primitiveOrbit_basis hirr m 0 P
      rw [show v = ∑ i : Fin 1, hbasis.repr v i • hbasis i from (hbasis.sum_repr v).symm,
          Fin.sum_univ_one, lie_smul]
      suffices hbasis (0 : Fin 1) = m by rw [this, hxm, smul_zero]
      change primitiveOrbit_basis hirr m 0 P ⟨0, _⟩ = _
      exact Basis.mk_apply _ _ _
    · -- Not irreducible
      by_cases htriv : Subsingleton W
      · haveI := htriv; exact Subsingleton.elim _ _
      · rw [not_subsingleton_iff_nontrivial] at htriv
        -- ∃ proper nonzero Lie submodule
        have : ¬ ∀ a : LieSubmodule ℂ sl2 W, a = ⊥ ∨ a = ⊤ := by
          intro hall
          exact hirr (LieModule.IsIrreducible.mk (fun N hN => (hall N).resolve_left hN))
        push_neg at this
        obtain ⟨N, hNbot, hNtop⟩ := this
        -- finrank N < finrank W
        have hN_sub_lt : N.toSubmodule < ⊤ :=
          lt_top_iff_ne_top.mpr (mt (LieSubmodule.toSubmodule_eq_top (N := N)).mp hNtop)
        have hfN : finrank ℂ ↥N.toSubmodule < finrank ℂ W := by
          have := Submodule.finrank_lt_finrank_of_lt hN_sub_lt
          rwa [finrank_top] at this
        -- finrank (W ⧸ N) < finrank W
        have hN_pos : 0 < finrank ℂ ↥N.toSubmodule := by
          have : Nontrivial ↥N := (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := W)).mpr hNbot
          exact Module.finrank_pos (R := ℂ)
        have hfN_eq : finrank ℂ ↥N = finrank ℂ ↥N.toSubmodule := rfl
        have hfQ_eq : finrank ℂ (W ⧸ N) = finrank ℂ (W ⧸ N.toSubmodule) := rfl
        have hfQ : finrank ℂ (W ⧸ N.toSubmodule) < finrank ℂ W := by
          have := Submodule.finrank_quotient_add_finrank N.toSubmodule; omega
        -- Casimir = 0 on N (restriction from W)
        have hCN : ∀ w : ↥N, sl2_casimir (V := ↥N) w = 0 := by
          intro w; apply Subtype.val_injective
          simp only [ZeroMemClass.coe_zero, sl2_casimir, LinearMap.add_apply,
            LinearMap.smul_apply, sq, Module.End.mul_apply,
            LieModule.toEnd_apply_apply]
          exact hC ↑w
        -- sl(2) acts trivially on N (by induction)
        have hN_triv : ∀ (y : sl2) (w : ↥N), ⁅y, (w : W)⁆ = 0 := by
          intro y w
          have h1 := ih (show finrank ℂ ↥N ≤ d from by omega) hCN y w
          rw [← LieSubmodule.coe_bracket]; simp [h1]
        -- Casimir = 0 on W ⧸ N (quotient from W)
        have hCQ : ∀ w : W ⧸ N, sl2_casimir (V := W ⧸ N) w = 0 := by
          intro w
          obtain ⟨w, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N w
          have mk'_lie := fun (a : sl2) (b : W) =>
            (LieSubmodule.Quotient.mk' N).map_lie a b |>.symm
          simp only [sl2_casimir, LinearMap.add_apply, LinearMap.smul_apply, sq,
            Module.End.mul_apply, LieModule.toEnd_apply_apply, mk'_lie]
          exact congrArg _ (hC w)
        -- sl(2) acts trivially on W ⧸ N ⟹ ⁅x, v⁆ ∈ N
        have hQ : ∀ (y : sl2) (w : W), (⁅y, w⁆ : W) ∈ N := by
          intro y w
          have hq := ih (show finrank ℂ (W ⧸ N) ≤ d from by omega) hCQ y
            (LieSubmodule.Quotient.mk' N w)
          rw [← (LieSubmodule.Quotient.mk' N).map_lie] at hq
          rwa [LieSubmodule.Quotient.mk_eq_zero] at hq
        exact sl2_acts_trivially_of_quotient_and_sub N hN_triv hQ x v

/-- If V is a finite-dimensional sl(2,ℂ)-module where all irreducible subquotients are
trivial (1-dimensional), then sl(2) acts as 0 on V. -/
private lemma sl2_trivial_action_of_trivial_subquotients
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (h : ∀ (_x : sl2) (v : V), sl2_casimir (V := V) v = 0) :
    ∀ (x : sl2) (v : V), ⁅x, v⁆ = 0 :=
  sl2_trivial_of_casimir_zero_aux (finrank ℂ V) le_rfl (fun v => h sl2_h v)

/-- When sl(2) acts trivially on V, every LieSubmodule is just a Submodule,
and the lattice of LieSubmodules is complemented (since ℂ is a field). -/
private lemma complementedLattice_of_trivial_action
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (h : ∀ (x : sl2) (v : V), ⁅x, v⁆ = 0) :
    ComplementedLattice (LieSubmodule ℂ sl2 V) := by
  constructor
  intro N
  -- Since sl(2) acts trivially, every subspace is a Lie submodule
  -- Use the vector space complement
  obtain ⟨M, hM⟩ := N.toSubmodule.exists_isCompl
  let M' : LieSubmodule ℂ sl2 V :=
    LieSubmodule.mk M (fun {x v} hv ↦ by rw [h x v]; exact M.zero_mem)
  exact ⟨M', LieSubmodule.isCompl_toSubmodule.mp hM⟩

/-- Key complement construction: if C - c₀ is injective on N (as a submodule)
and (C - c₀) maps V into N, then ker(C - c₀) is a Lie complement to N. -/
private lemma casimir_eigenspace_complement
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (N : LieSubmodule ℂ sl2 V) (c₀ : ℂ)
    (hInj : ∀ v ∈ N.toSubmodule, sl2_casimir v = c₀ • v → v = 0)
    (hImg : ∀ v : V, sl2_casimir v - c₀ • v ∈ N.toSubmodule) :
    ∃ N' : LieSubmodule ℂ sl2 V, IsCompl N N' := by
  -- ker(C - c₀) is a Lie submodule (eigenspace of C for eigenvalue c₀)
  set K := (sl2_casimir (V := V)).eigenspace c₀
  have hK_lie : ∀ (x : sl2) (v : V), v ∈ K → ⁅x, v⁆ ∈ K :=
    casimir_eigenspace_lie_invariant c₀
  let K' : LieSubmodule ℂ sl2 V :=
    LieSubmodule.mk K (fun {x v} hv ↦ hK_lie x v hv)
  refine ⟨K', ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule]
  constructor
  · -- Disjoint: N ∩ K = ⊥
    rw [disjoint_iff_inf_le]
    intro v ⟨hvN, hvK⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hvK
    exact hInj v hvN hvK
  · -- Codisjoint: N ⊔ K = ⊤ via dimension counting
    -- Strategy: im(C - c₀) ⊆ N (by hImg), so dim(ker(C-c₀)) ≥ dim(V) - dim(N).
    -- Since ker(C-c₀) ∩ N = 0 (disjoint) and dim(ker) ≥ dim(V)-dim(N),
    -- we get dim(ker) + dim(N) ≥ dim(V), hence ker + N = V.
    rw [codisjoint_iff]
    -- K = eigenspace c₀ = ker(C - c₀ • 1)
    have hK_eq : K = LinearMap.ker (sl2_casimir (V := V) - c₀ • 1) :=
      Module.End.eigenspace_def
    -- range(C - c₀ • 1) ≤ N
    have hRange : LinearMap.range (sl2_casimir (V := V) - c₀ • 1) ≤ N.toSubmodule := by
      intro w hw
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
      simp only [LinearMap.sub_apply, LinearMap.smul_apply] at hv
      rw [← hv]
      exact hImg v
    -- By rank-nullity and range ≤ N, finrank V ≤ finrank N + finrank K
    have hRN := LinearMap.finrank_range_add_finrank_ker
      (sl2_casimir (V := V) - c₀ • 1)
    have hRangeFinrank := Submodule.finrank_mono hRange
    rw [← hK_eq] at hRN
    -- N.toSubmodule ⊔ K = ⊤
    apply Submodule.eq_top_of_disjoint N.toSubmodule K (by omega)
    exact disjoint_iff_inf_le.mpr (fun v ⟨hvN, hvK⟩ ↦
      hInj v hvN (Module.End.mem_eigenspace_iff.mp hvK))

/-- The quotient morphism commutes with sl2_casimir. -/
private lemma casimir_quotient_comm
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (M : LieSubmodule ℂ sl2 V) (v : V) :
    LieSubmodule.Quotient.mk' M (sl2_casimir v) =
    sl2_casimir (V := V ⧸ M) (LieSubmodule.Quotient.mk' M v) := by
  have hmk_lie := fun (a : sl2) (b : V) =>
    (LieSubmodule.Quotient.mk' M).map_lie a b |>.symm
  simp only [sl2_casimir, LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply,
    LieModule.toEnd_apply_apply, hmk_lie, map_add, map_nsmul]

/-- If C = c₀ on V/M, then (C - c₀) maps V into M. -/
private lemma casimir_sub_maps_to_submodule
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (M : LieSubmodule ℂ sl2 V) (c₀ : ℂ)
    (hQ_casimir : ∀ v : V ⧸ M, sl2_casimir (V := V ⧸ M) v = c₀ • v) :
    ∀ v : V, sl2_casimir v - c₀ • v ∈ M.toSubmodule := by
  intro v
  have hq : LieSubmodule.Quotient.mk' M (sl2_casimir v - c₀ • v) = 0 := by
    rw [map_sub, map_smul, casimir_quotient_comm, hQ_casimir, sub_self]
  rwa [LieSubmodule.Quotient.mk_eq_zero] at hq

/-- Every nontrivial finite-dimensional sl(2)-module has an irreducible Lie submodule.
(By taking a minimal nonzero submodule, which exists in finite dimensions.) -/
private lemma exists_irreducible_lieSubmodule
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V] [Nontrivial V] :
    ∃ W : LieSubmodule ℂ sl2 V, IsAtom W := by
  have : (⊤ : LieSubmodule ℂ sl2 V) ≠ ⊥ := by
    intro h
    have hsub := (LieSubmodule.eq_bot_iff (N := (⊤ : LieSubmodule ℂ sl2 V))).mp h
    exact absurd (⟨fun a b => by simp [hsub a (LieSubmodule.mem_top a),
      hsub b (LieSubmodule.mem_top b)]⟩ : Subsingleton V) (not_subsingleton V)
  exact (eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ sl2 V)).resolve_left this
    |>.imp fun W ⟨hW, _⟩ => hW

/-- An atom in the lattice of Lie submodules is irreducible as a Lie module. -/
private lemma isAtom_isIrreducible
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    {N : LieSubmodule ℂ sl2 V} (hN : IsAtom N) :
    LieModule.IsIrreducible ℂ sl2 ↥N := by
  haveI : Nontrivial ↥N :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hN.1
  exact LieModule.IsIrreducible.mk fun M hM => by
    set M' := LieSubmodule.map N.incl M
    have hM'_le : M' ≤ N := by
      intro v hv
      rw [LieSubmodule.mem_map] at hv
      obtain ⟨m, _, rfl⟩ := hv; exact m.property
    have hM'_ne : M' ≠ ⊥ := by
      intro h; apply hM; rw [eq_bot_iff]; intro m hm
      have : N.incl m ∈ (⊥ : LieSubmodule ℂ sl2 V) := h ▸ LieSubmodule.mem_map_of_mem hm
      rw [LieSubmodule.mem_bot] at this
      rw [LieSubmodule.mem_bot]; exact Subtype.val_injective this
    have hM'_eq : M' = N := (hN.le_iff.mp hM'_le).resolve_left hM'_ne
    rw [eq_top_iff]; intro m _
    suffices hmem : (m : V) ∈ M' by
      rw [LieSubmodule.mem_map] at hmem
      obtain ⟨m', hm', hm'_eq⟩ := hmem
      exact (Subtype.val_injective hm'_eq) ▸ hm'
    rw [hM'_eq]; exact m.property

/-- Helper: If W ∩ N = ⊥ in V with W an atom (irreducible), then N has a complement in V,
given that all strictly smaller-dimensional modules are completely reducible. -/
private lemma complement_case_disjoint.{u} (d : ℕ)
    (ih : ∀ d' < d, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule sl2 W] [LieModule ℂ sl2 W],
      finrank ℂ W ≤ d' → ComplementedLattice (LieSubmodule ℂ sl2 W))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (hd : finrank ℂ V ≤ d)
    (N W : LieSubmodule ℂ sl2 V) (hN_ne_bot : N ≠ ⊥) (hW_atom : IsAtom W) (hWN : W ⊓ N = ⊥) :
    ∃ S : LieSubmodule ℂ sl2 V, IsCompl N S := by
  -- V/W has smaller dimension
  have hW_ne_bot := hW_atom.1
  have hW_pos : 0 < finrank ℂ (W : Submodule ℂ V) := by
    have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hW_ne_bot
    exact Module.finrank_pos (R := ℂ)
  have hVW_lt : finrank ℂ (V ⧸ W) < finrank ℂ V := by
    have h1 := Submodule.finrank_quotient_add_finrank W.toSubmodule
    have h2 : finrank ℂ (V ⧸ W) = finrank ℂ (V ⧸ W.toSubmodule) := rfl
    omega
  -- By induction, V/W is completely reducible
  have hVW_compl : ComplementedLattice (LieSubmodule ℂ sl2 (V ⧸ W)) :=
    ih (finrank ℂ (V ⧸ W)) (by omega) (V ⧸ W) (le_refl _)
  set π := LieSubmodule.Quotient.mk' W
  -- Image of N in V/W and its complement
  obtain ⟨S_bar, hS_bar⟩ := hVW_compl.exists_isCompl (LieSubmodule.map π N)
  -- Pull back S_bar to V
  refine ⟨LieSubmodule.comap π S_bar, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule]
  constructor
  · -- Disjoint: N ∩ comap π S_bar = ⊥
    rw [disjoint_iff_inf_le]
    intro v ⟨hvN, hvS⟩
    have hvS' : π v ∈ S_bar := hvS
    have hvNbar : π v ∈ LieSubmodule.map π N :=
      LieSubmodule.mem_map_of_mem (N := N) hvN
    have hπv0 : π v = 0 := by
      have : (π v : V ⧸ W) ∈ (LieSubmodule.map π N ⊓ S_bar : LieSubmodule ℂ sl2 (V ⧸ W)) :=
        ⟨hvNbar, hvS'⟩
      rw [hS_bar.inf_eq_bot, LieSubmodule.mem_bot] at this
      exact this
    have hv_W : (v : V) ∈ (W : LieSubmodule ℂ sl2 V) := by
      rwa [LieSubmodule.Quotient.mk_eq_zero] at hπv0
    have : (v : V) ∈ (W ⊓ N : LieSubmodule ℂ sl2 V) := ⟨hv_W, hvN⟩
    rw [hWN, LieSubmodule.mem_bot] at this
    exact Submodule.mem_bot ℂ |>.mpr this
  · -- Codisjoint: N ⊔ comap π S_bar = ⊤
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv_top : π v ∈ (⊤ : LieSubmodule ℂ sl2 (V ⧸ W)) := LieSubmodule.mem_top _
    rw [← hS_bar.sup_eq_top, LieSubmodule.mem_sup] at hv_top
    obtain ⟨a, ha, b, hb, hab⟩ := hv_top
    rw [LieSubmodule.mem_map] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    have hvn : v - n ∈ (LieSubmodule.comap π S_bar : LieSubmodule ℂ sl2 V) := by
      show π (v - n) ∈ S_bar
      rw [map_sub, ← hab, add_sub_cancel_left]
      exact hb
    exact Submodule.mem_sup.mpr ⟨n, hn, v - n, hvn, by abel⟩

/-- Given 0 → N → E → W → 0 where W is irreducible and N is an atom and dim E ≤ d,
N has a complement in E. This is the key splitting lemma for complete reducibility.

We use the Casimir to construct complements:
- If C has different eigenvalues on N and W: `casimir_eigenspace_complement` directly.
- If C has same eigenvalue λ ≠ 0 and C ≠ λ on E: section via Schur + (C-λ).
- If C = λ on E with λ ≠ 0: use primitive vector (weight-n argument).
- If λ = 0: trivial action by sl2_trivial_action_of_trivial_subquotients. -/
private lemma exists_complement_of_irreducible_quotient.{u} (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V],
    finrank ℂ V ≤ d →
    ∀ N : LieSubmodule ℂ sl2 V, N ≠ ⊤ → IsAtom N →
    LieModule.IsIrreducible ℂ sl2 (V ⧸ N) →
    (∀ (d' : ℕ), d' < d →
      ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule sl2 W] [LieModule ℂ sl2 W],
      finrank ℂ W ≤ d' →
      ComplementedLattice (LieSubmodule ℂ sl2 W)) →
    ∃ S : LieSubmodule ℂ sl2 V, IsCompl N S := by
  intro V _ _ _ _ _ hd N hN_top hN_atom hirr ih
  -- V/N is irreducible, so Casimir acts as a scalar on V/N
  haveI : Nontrivial (V ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]; intro hs
    exact hN_top (by
      rw [eq_top_iff]; intro v _
      have := Subsingleton.elim (LieSubmodule.Quotient.mk' N v) 0
      rwa [LieSubmodule.Quotient.mk_eq_zero] at this)
  obtain ⟨m, μ, P⟩ := exists_primitiveVector hirr
  obtain ⟨n, hn⟩ := P.exists_nat; rw [hn] at P
  have hC := casimir_on_irreducible_scalar hirr m n P
  -- Casimir eigenvalue λ = n(n+2) on V/N
  set c_irr := (n : ℂ) * ((n : ℂ) + 2)
  -- Casimir acts as c_irr on V/N
  have hQ_casimir : ∀ v : V ⧸ N, sl2_casimir (V := V ⧸ N) v = c_irr • v := by
    intro v
    have h := LinearMap.congr_fun hC v
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
    exact h
  -- (C - c_irr) maps V into N
  have hImg : ∀ v : V, sl2_casimir v - c_irr • v ∈ N.toSubmodule :=
    casimir_sub_maps_to_submodule N c_irr hQ_casimir
  -- Case split: is C - c_irr injective on N?
  by_cases hInj : ∀ v ∈ N.toSubmodule, sl2_casimir v = c_irr • v → v = 0
  · -- C - c_irr is injective on N: Casimir eigenspace complement
    exact casimir_eigenspace_complement N c_irr hInj hImg
  · -- C - c_irr is NOT injective on N.
    -- Sub-case: is C = c_irr on ALL of N AND c_irr = 0?
    by_cases hc_zero : c_irr = 0 ∧ ∀ v ∈ N.toSubmodule, sl2_casimir v = c_irr • v
    · -- c_irr = 0 and C = 0 on all of N: trivial action argument
      have hc := hc_zero.1
      have hAllN := hc_zero.2
      simp only [hc, zero_smul, sub_zero] at hImg hAllN hQ_casimir ⊢
      -- sl₂ acts trivially on N
      have hN_triv : ∀ (x : sl2) (v : ↥N), ⁅x, (v : V)⁆ = 0 := by
        have hCN : ∀ w : ↥N, sl2_casimir (V := ↥N) w = 0 := by
          intro w; apply Subtype.val_injective
          simp only [ZeroMemClass.coe_zero, sl2_casimir, LinearMap.add_apply,
            LinearMap.smul_apply, sq, Module.End.mul_apply,
            LieModule.toEnd_apply_apply]
          exact hAllN w.val w.property
        have := sl2_trivial_action_of_trivial_subquotients (fun _ v => hCN v)
        intro x w
        have h1 := this x w
        rw [← LieSubmodule.coe_bracket]; simp [h1]
      -- sl₂ maps V into N (quotient is trivial since C = 0 on V/N)
      have hQ_triv : ∀ (x : sl2) (v : V), (⁅x, v⁆ : V) ∈ N := by
        -- C = 0 on V/N (since c_irr = 0), so sl₂ acts trivially on V/N
        have hCQ : ∀ w : V ⧸ N, sl2_casimir (V := V ⧸ N) w = 0 := by
          intro w; have := hQ_casimir w; simp [hc] at this; exact this
        have hQ_act := sl2_trivial_action_of_trivial_subquotients (fun _ v => hCQ v)
        intro x v
        have h1 := hQ_act x (LieSubmodule.Quotient.mk' N v)
        rw [← (LieSubmodule.Quotient.mk' N).map_lie] at h1
        rwa [LieSubmodule.Quotient.mk_eq_zero] at h1
      -- By perfectness, sl₂ acts trivially on V
      have htriv := sl2_acts_trivially_of_quotient_and_sub N hN_triv hQ_triv
      exact (complementedLattice_of_trivial_action htriv).exists_isCompl N
    · -- N is an atom (irreducible). Casimir = c_irr on N. c_irr ≠ 0.
      -- Primitive vector argument: find v ∈ V with ev = 0, hv = nv, v ∉ N.
      have hN_irr := isAtom_isIrreducible hN_atom
      haveI hN_nt : Nontrivial ↥N :=
        (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hN_atom.1
      -- C = c_irr on all of N, via eigenspace intersection with atom
      push_neg at hInj
      obtain ⟨v₀, hv₀_mem, hv₀_C, hv₀_ne⟩ := hInj
      -- v₀ is in the Casimir c_irr-eigenspace (a Lie submodule of V)
      have hv₀_eigen : v₀ ∈ (sl2_casimir (V := V)).eigenspace c_irr :=
        Module.End.mem_eigenspace_iff.mpr hv₀_C
      -- Build the eigenspace as a Lie submodule
      let Ec : LieSubmodule ℂ sl2 V :=
        LieSubmodule.mk ((sl2_casimir (V := V)).eigenspace c_irr)
          (fun {x v} hv ↦ casimir_eigenspace_lie_invariant c_irr x v hv)
      -- Ec ∩ N contains v₀ ≠ 0, so since N is an atom, N ≤ Ec
      have hv₀_inter : v₀ ∈ (Ec ⊓ N : LieSubmodule ℂ sl2 V) := ⟨hv₀_eigen, hv₀_mem⟩
      have hEN_ne : Ec ⊓ N ≠ ⊥ := by
        intro h; rw [h, LieSubmodule.mem_bot] at hv₀_inter; exact hv₀_ne hv₀_inter
      have hN_le_Ec : N ≤ Ec := by
        rcases eq_or_lt_of_le (inf_le_right (a := Ec) (b := N)) with h | h
        · exact h ▸ inf_le_left
        · exact absurd (hN_atom.2 _ h) hEN_ne
      have hAllN : ∀ v ∈ N.toSubmodule, sl2_casimir v = c_irr • v := by
        intro w hw; exact Module.End.mem_eigenspace_iff.mp (hN_le_Ec hw)
      -- Get primitive vector of N (needed for complement construction)
      obtain ⟨mN, μN, PN⟩ := exists_primitiveVector hN_irr
      obtain ⟨nN, hnN⟩ := PN.exists_nat; rw [hnN] at PN
      -- nN = n: compute C·mN in V using primitive vector formulas
      have hmN_h : ⁅sl2_h, (mN : V)⁆ = (nN : ℂ) • (mN : V) := by
        have := congrArg Subtype.val PN.lie_h
        simp only [LieSubmodule.coe_bracket, LieSubmodule.coe_smul] at this; exact this
      have hmN_e : ⁅sl2_e, (mN : V)⁆ = 0 := by
        have := congrArg Subtype.val PN.lie_e
        simp only [LieSubmodule.coe_bracket, ZeroMemClass.coe_zero] at this; exact this
      have hCmN : sl2_casimir (V := V) (mN : V) = ((nN : ℂ) * ((nN : ℂ) + 2)) • (mN : V) := by
        have hH' : (toEnd ℂ sl2 V sl2_h) (mN : V) = (nN : ℂ) • (mN : V) := by
          change ⁅sl2_h, (mN : V)⁆ = _; exact hmN_h
        have hE' : (toEnd ℂ sl2 V sl2_e) (mN : V) = 0 := by
          change ⁅sl2_e, (mN : V)⁆ = _; exact hmN_e
        rw [sl2_casimir_eq]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, sq, Module.End.mul_apply,
          ← Nat.cast_smul_eq_nsmul ℂ, hE', map_zero, smul_zero, add_zero,
          hH', map_smul, smul_smul, ← add_smul]
        congr 1; push_cast; ring
      have hnn : (nN : ℂ) * ((nN : ℂ) + 2) = c_irr := by
        have h1 := hAllN (mN : V) mN.property
        rw [hCmN] at h1
        have hmN_ne : (mN : V) ≠ 0 := fun h => PN.ne_zero (Subtype.val_injective h)
        exact smul_left_injective ℂ hmN_ne h1
      have hnN_eq : nN = n := casimir_eigenvalue_injective hnn
      -- c_irr ≠ 0
      have hc_ne : c_irr ≠ 0 := fun hc => hc_zero ⟨hc, hAllN⟩
      -- n ≥ 1
      have hn_pos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · simp [c_irr] at hc_ne
        · exact h
      -- dim N = n + 1
      have hdimN : finrank ℂ ↥N = n + 1 := primitiveVector_dim hN_irr mN n (hnN_eq ▸ PN)
      -- Lift m ∈ V/N to some v₁ ∈ V
      obtain ⟨v₁, hv₁⟩ := LieSubmodule.Quotient.surjective_mk' N m
      -- Step 1: Show hv₁ - nv₁ ∈ N and ev₁ ∈ N
      set π := LieSubmodule.Quotient.mk' N
      have hw_mem : ⁅sl2_h, v₁⁆ - (n : ℂ) • v₁ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, map_smul, π.map_lie, hv₁,
          sub_eq_zero]
        exact P.lie_h
      set w := ⁅sl2_h, v₁⁆ - (n : ℂ) • v₁
      -- Step 2: f^{n+1} kills all of N (acting on V)
      have hfN_zero : ∀ u ∈ N.toSubmodule,
          ((toEnd ℂ sl2 V sl2_f) ^ (n + 1)) u = 0 := by
        -- f^{n+1} mN = 0 in N (from primitive vector property)
        have hPN' := (hnN_eq ▸ PN : sl2_triple.HasPrimitiveVectorWith mN (n : ℂ))
        have hPN_kill : ((toEnd ℂ sl2 N sl2_f) ^ (n + 1)) mN = 0 :=
          hPN'.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)
        -- f^{n+1+k} mN = 0 for all k (by induction)
        have hfk_kill : ∀ k, ((toEnd ℂ sl2 N sl2_f) ^ (n + 1 + k)) mN = 0 := by
          intro k; induction k with
          | zero => simpa using hPN_kill
          | succ k ih =>
            rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega,
              pow_succ', Module.End.mul_apply, ih, map_zero]
        -- (toEnd N f)^{n+1} = 0 as endomorphism (kills every basis element)
        have hfN_nil : (toEnd ℂ sl2 (↥N) sl2_f) ^ (n + 1) = 0 := by
          let bN := primitiveOrbit_basis hN_irr mN n hPN'
          apply bN.ext; intro ⟨k, hk⟩
          rw [LinearMap.zero_apply,
            show bN ⟨k, hk⟩ = ((toEnd ℂ sl2 N sl2_f) ^ k) mN from Basis.mk_apply _ _ _,
            ← Module.End.mul_apply, ← pow_add]
          exact hfk_kill k
        -- Coercion: (toEnd V f)^k on N = coercion of (toEnd N f)^k
        -- (uses LieSubmodule.coe_bracket = rfl)
        intro u hu
        suffices h : ∀ (k : ℕ) (v : N),
            ((toEnd ℂ sl2 V sl2_f) ^ k) (v : V) = (((toEnd ℂ sl2 N sl2_f) ^ k) v : V) by
          rw [h (n + 1) ⟨u, hu⟩, hfN_nil, LinearMap.zero_apply, ZeroMemClass.coe_zero]
        intro k v; induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]; rfl
      -- Step 3: Primitive vector adjustment argument
      have hPN' := (hnN_eq ▸ PN : sl2_triple.HasPrimitiveVectorWith mN (n : ℂ))
      -- Helper: if u ∈ N with h·u = μ·u and μ not a weight of N, then u = 0
      have weight_vanish : ∀ (u : V), u ∈ N → ∀ μ : ℂ, ⁅sl2_h, u⁆ = μ • u →
          (∀ k : Fin (n + 1), μ ≠ (n : ℂ) - 2 * ↑k.val) → u = 0 := by
        intro u hu μ heigen hweights
        have h_mem : (⟨u, hu⟩ : N) ∈ (toEnd ℂ sl2 N sl2_h).eigenspace μ := by
          rw [Module.End.mem_eigenspace_iff]; apply Subtype.val_injective
          simp only [LieSubmodule.coe_smul]; exact heigen
        have h_bot := eigenspace_eq_bot_of_not_weight hN_irr mN n hPN' μ hweights
        rw [h_bot, Submodule.mem_bot] at h_mem; exact congr_arg Subtype.val h_mem
      -- ev₁ ∈ N
      have hev₁ : ⁅sl2_e, v₁⁆ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, π.map_lie, hv₁]; exact P.lie_e
      -- π commutes with f^k
      have hπ_f : ∀ (k : ℕ) (u : V), π (((toEnd ℂ sl2 V sl2_f) ^ k) u) =
          ((toEnd ℂ sl2 (V ⧸ N) sl2_f) ^ k) (π u) := by
        intro k u; induction k with
        | zero => simp
        | succ k ih =>
          simp only [pow_succ', Module.End.mul_apply, ← ih]
          exact (π.map_lie sl2_f _).symm
      -- f^{n+1}v₁ ∈ N
      have hfn1v₁_mem : ((toEnd ℂ sl2 V sl2_f) ^ (n + 1)) v₁ ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, hπ_f, hv₁]
        exact P.pow_toEnd_f_eq_zero_of_eq_nat (by norm_cast)
      -- h(f^{n+1}v₁) = -(n+2) • f^{n+1}v₁
      have hfn1_eigen : ⁅sl2_h, ((toEnd ℂ sl2 V sl2_f) ^ (n + 1)) v₁⁆ =
          (-(n : ℂ) - 2) • ((toEnd ℂ sl2 V sl2_f) ^ (n + 1)) v₁ := by
        rw [h_comm_pow_f (n + 1) v₁]
        have hw_eq : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [hw_eq, map_add, map_smul, hfN_zero w hw_mem, zero_add]; module
      -- f^{n+1}v₁ = 0 (-(n+2) not a weight of N)
      have hfn1v₁ : ((toEnd ℂ sl2 V sl2_f) ^ (n + 1)) v₁ = 0 :=
        weight_vanish _ hfn1v₁_mem _ hfn1_eigen (by
          intro k heq
          have h1 : (2 : ℂ) * ↑k.val = 2 * ↑n + 2 := by linear_combination heq
          have h2 : 2 * (k.val : ℤ) = 2 * (n : ℤ) + 2 := by exact_mod_cast h1
          omega)
      -- f^n(w) = 0 via e_f_pow_succ_comm
      have hfnw : ((toEnd ℂ sl2 V sl2_f) ^ n) w = 0 := by
        have h1 := e_f_pow_succ_comm n v₁
        rw [hfn1v₁, lie_zero, hfN_zero _ hev₁, zero_add] at h1
        have hw_eq : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [hw_eq, map_add, map_smul, add_sub_cancel_right] at h1
        have hn1_ne : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        exact (smul_eq_zero.mp h1.symm).resolve_left hn1_ne
      -- Construct n₀ ∈ N with (h-n)n₀ = w
      obtain ⟨n₀, hn₀_mem, h_adj⟩ :
          ∃ n₀ : V, n₀ ∈ N ∧ ⁅sl2_h, n₀⁆ - (n : ℂ) • n₀ = w := by
        -- Basis of N from primitive vector
        let bN := primitiveOrbit_basis hN_irr mN n hPN'
        set cw := bN.repr ⟨w, hw_mem⟩
        -- bN k = f^k mN
        have hbN : ∀ k : Fin (n + 1), bN k = ((toEnd ℂ sl2 N sl2_f) ^ (k : ℕ)) mN :=
          fun k => Basis.mk_apply _ _ _
        -- Coercion: (toEnd V f)^k on N elements = coercion of (toEnd N f)^k
        have hcoerce : ∀ (k : ℕ) (u : N),
            ((toEnd ℂ sl2 V sl2_f) ^ k) (u : V) = (((toEnd ℂ sl2 N sl2_f) ^ k) u : V) := by
          intro k u; induction k with
          | zero => simp
          | succ k ih =>
            rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]; rfl
        -- f^{n+1} kills all of N (as endomorphism)
        have hfN_nil : (toEnd ℂ sl2 N sl2_f) ^ (n + 1) = 0 := by
          ext v; simp only [LinearMap.zero_apply]
          have h1 := hcoerce (n + 1) v
          rw [hfN_zero v.val v.property] at h1
          exact_mod_cast h1.symm
        -- f^n(w) = 0 implies cw(0) = 0
        have hcw0 : cw ⟨0, Nat.zero_lt_succ n⟩ = 0 := by
          -- f^n w = 0 in N
          have hfnw_N : ((toEnd ℂ sl2 N sl2_f) ^ n) ⟨w, hw_mem⟩ = 0 := by
            have h1 := hcoerce n ⟨w, hw_mem⟩; rw [hfnw] at h1; exact_mod_cast h1.symm
          -- Expand w = Σ cw(k) • bN(k), apply f^n
          rw [show (⟨w, hw_mem⟩ : N) = ∑ k, cw k • bN k from (bN.sum_repr _).symm,
            map_sum] at hfnw_N
          simp only [map_smul, hbN, ← Module.End.mul_apply, ← pow_add] at hfnw_N
          -- Isolate k=0 term; k≥1 terms vanish
          rw [Finset.sum_eq_single_of_mem ⟨0, Nat.zero_lt_succ n⟩ (Finset.mem_univ _)
            (fun k _ hk => by
              have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
              rw [show n + (k : ℕ) = (n + 1) + ((k : ℕ) - 1) from by omega, pow_add,
                Module.End.mul_apply, hfN_nil, LinearMap.zero_apply, smul_zero])] at hfnw_N
          simp only [Fin.val_mk, Nat.add_zero] at hfnw_N
          exact (smul_eq_zero.mp hfnw_N).resolve_right
            (hPN'.pow_toEnd_f_ne_zero_of_eq_nat (by norm_cast) (by omega))
        -- Define n₀ as "inverse" of (h - n·id) on w
        let n₀_N : ↥N := ∑ k : Fin (n + 1),
          (if (k : ℕ) = 0 then (0 : ℂ) else cw k / (-(2 * (k : ℂ)))) • bN k
        refine ⟨(n₀_N : V), n₀_N.property, ?_⟩
        -- Prove (h - n)(n₀_N) = w in N, then coerce
        suffices h_N : ⁅sl2_h, n₀_N⁆ - (n : ℂ) • n₀_N = ⟨w, hw_mem⟩ from
          congrArg Subtype.val h_N
        -- Eigenvalue of (h - n) on basis vectors (within N)
        have heigen : ∀ k : Fin (n + 1),
            ⁅sl2_h, bN k⁆ - (n : ℂ) • bN k = (-(2 * (k : ℂ))) • bN k := by
          intro k; rw [hbN k, hPN'.lie_h_pow_toEnd_f]; module
        -- Expand ⁅h, n₀_N⁆ - n • n₀_N and simplify each summand
        simp only [n₀_N, lie_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        -- Each summand: (if ... • ⁅h, bN k⁆) - (n • (if ... • bN k))
        -- = if ... • (⁅h, bN k⁆ - n • bN k)  by distributing
        -- = if ... • (-(2k) • bN k)  by heigen
        -- = (if ... * -(2k)) • bN k
        -- = cw k • bN k  by hcoeff
        refine ((bN.sum_repr ⟨w, hw_mem⟩).symm.trans (Finset.sum_congr rfl fun k _ => ?_)).symm
        -- Goal: cw k • bN k = coeff • ⁅h, bN k⁆ - n • (coeff • bN k)
        set ck := (if (k : ℕ) = 0 then (0 : ℂ) else cw k / (-(2 * (k : ℂ)))) with hck_def
        -- Rewrite ⁅h, bN k⁆ using heigen
        have h1 : ⁅sl2_h, bN k⁆ = (-(2 * (k : ℂ))) • bN k + (n : ℂ) • bN k := by
          have := heigen k; rw [sub_eq_iff_eq_add] at this; exact this
        rw [lie_smul, h1, smul_add, smul_smul, smul_smul, smul_smul]
        -- Goal: cw k • bN k = (ck * -(2k)) • bN k + (ck * n) • bN k - (n * ck) • bN k
        rw [show ck * (n : ℂ) = (n : ℂ) * ck from mul_comm _ _, add_sub_cancel_right]
        -- Goal: cw k • bN k = (ck * -(2k)) • bN k
        congr 1
        -- Goal: cw k = ck * -(2k)
        rw [hck_def]
        -- cw k = ck * -(2k), where ck = if k.val=0 then 0 else cw k / -(2k)
        -- After congr 1, goal is (bN.repr ⟨w,hw_mem⟩) k = ck * -(2k)
        -- Since cw = bN.repr ⟨w,hw_mem⟩, change to cw k = ck * -(2k)
        change cw k = ck * (-(2 * (k : ℂ)))
        rw [hck_def]
        by_cases hk0 : (k : ℕ) = 0
        · have hk_eq : k = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hk0
          subst hk_eq
          simp only [Fin.val_mk, ↓reduceIte, zero_mul, Nat.cast_zero, mul_zero, neg_zero]
          exact hcw0
        · simp only [hk0, ↓reduceIte]
          have : (k.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
          field_simp
      -- Set v = v₁ - n₀
      set v := v₁ - n₀ with hv_def
      -- hv = nv
      have hv_h : ⁅sl2_h, v⁆ = (n : ℂ) • v := by
        simp only [hv_def, lie_sub, smul_sub]
        have : ⁅sl2_h, v₁⁆ = w + (n : ℂ) • v₁ := by simp [w]
        rw [this, ← h_adj]; abel
      -- ev = 0 (n+2 not a weight of N)
      have hπn₀ : π n₀ = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hn₀_mem
      have hv_e : ⁅sl2_e, v⁆ = 0 := by
        have hev_mem : ⁅sl2_e, v⁆ ∈ N := by
          rw [← LieSubmodule.Quotient.mk_eq_zero, π.map_lie, hv_def, map_sub, hπn₀, sub_zero,
            hv₁]
          exact P.lie_e
        have hev_eigen : ⁅sl2_h, ⁅sl2_e, v⁆⁆ = ((n : ℂ) + 2) • ⁅sl2_e, v⁆ := by
          rw [leibniz_lie, sl2_triple.lie_h_e_nsmul, hv_h, nsmul_lie, lie_smul,
            ← Nat.cast_smul_eq_nsmul ℂ (2 : ℕ), ← add_smul]
          ring_nf
        exact weight_vanish _ hev_mem _ hev_eigen (by
          intro k heq
          have h1 : (2 : ℂ) * ↑k.val + 2 = 0 := by linear_combination heq
          have h2 : 2 * (k.val : ℤ) + 2 = 0 := by exact_mod_cast h1
          omega)
      -- v ≠ 0
      have hv_ne : v ≠ 0 := by
        intro h
        have : π v = 0 := by rw [h, map_zero]
        rw [hv_def, map_sub, hπn₀, sub_zero, hv₁] at this
        exact P.ne_zero this
      -- Build HasPrimitiveVectorWith and f-orbit span
      have Pv : sl2_triple.HasPrimitiveVectorWith v (n : ℂ) := ⟨hv_ne, hv_h, hv_e⟩
      let S : LieSubmodule ℂ sl2 V := LieSubmodule.mk
        (Submodule.span ℂ (Set.range (fun k : Fin (n + 1) ↦
          ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) v)))
        (fun {x u} hu ↦ primitiveOrbit_lieInvariant v n Pv x u hu)
      -- S ∩ N = ⊥ (π injective on S)
      -- π maps f^k v to f^k m
      have hπ_fkv : ∀ k : Fin (n + 1), π (((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) v) =
          ((toEnd ℂ sl2 (V ⧸ N) sl2_f) ^ (k : ℕ)) m := by
        intro k; rw [hπ_f, hv_def, map_sub, hπn₀, sub_zero, hv₁]
      -- {f^k v} is linearly independent (since {f^k m} is and π is linear)
      let fkv : Fin (n + 1) → V := fun k ↦ ((toEnd ℂ sl2 V sl2_f) ^ (k : ℕ)) v
      have hli_v : LinearIndependent ℂ fkv := by
        have hli_m := primitiveOrbit_linearIndependent m n P
        have : (fun k : Fin (n + 1) ↦ ((toEnd ℂ sl2 (V ⧸ N) sl2_f) ^ (k : ℕ)) m) =
            π.toLinearMap ∘ fkv :=
          funext (fun k => (hπ_fkv k).symm)
        rw [this] at hli_m
        exact hli_m.of_comp _
      have hSN : S ⊓ N = ⊥ := by
        rw [eq_bot_iff]; intro u ⟨huS, huN⟩
        rw [LieSubmodule.mem_bot]
        have hπu : π u = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr huN
        -- u ∈ span of {f^k v}
        have huS' : u ∈ Submodule.span ℂ (Set.range fkv) := huS
        rw [Submodule.mem_span_range_iff_exists_fun] at huS'
        obtain ⟨c, rfl⟩ := huS'
        -- π(Σ cₖ f^k v) = Σ cₖ f^k m = 0
        simp only [map_sum, map_smul, hπ_fkv] at hπu
        -- By linear independence of {f^k m}, all cₖ = 0
        let fkm : Fin (n + 1) → V ⧸ N := fun k ↦ ((toEnd ℂ sl2 (V ⧸ N) sl2_f) ^ (k : ℕ)) m
        have hli_m := primitiveOrbit_linearIndependent m n P
        have hπu' : ∑ i, c i • fkm i = 0 := by
          simp only [fkm, ← hπ_fkv]; exact hπu
        have hc : ∀ i, c i = 0 :=
          (Fintype.linearIndependent_iffₛ (v := fkm)).mp hli_m c 0
            (by simp [hπu'])
        simp [show c = 0 from funext hc]
      -- S ≠ ⊥
      have hS_ne : S ≠ ⊥ := by
        intro h; apply hv_ne
        have : v ∈ (⊥ : LieSubmodule ℂ sl2 V) := h ▸ (show v ∈ S from
          Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ n⟩, by simp⟩)
        rwa [LieSubmodule.mem_bot] at this
      -- Get atom W ≤ S, show W ⊓ N = ⊥
      obtain ⟨W, hW_atom, hW_le⟩ := (eq_bot_or_exists_atom_le S).resolve_left hS_ne
      have hWN : W ⊓ N = ⊥ :=
        eq_bot_iff.mpr (le_trans (inf_le_inf_right N hW_le) (le_of_eq hSN))
      exact complement_case_disjoint d ih hd N W hN_atom.1 hW_atom hWN

/-- Helper: If W ⊆ N ⊆ V with W an atom (irreducible), then N has a complement in V,
given that all strictly smaller-dimensional modules are completely reducible. -/
private lemma complement_case_sub.{u} (d : ℕ)
    (ih : ∀ d' < d, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [LieRingModule sl2 W] [LieModule ℂ sl2 W],
      finrank ℂ W ≤ d' → ComplementedLattice (LieSubmodule ℂ sl2 W))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V]
    (hd : finrank ℂ V ≤ d)
    (N W : LieSubmodule ℂ sl2 V) (hN_ne_top : N ≠ ⊤) (hW_atom : IsAtom W) (hWN : W ≤ N) :
    ∃ S : LieSubmodule ℂ sl2 V, IsCompl N S := by
  have hW_ne_bot := hW_atom.1
  have hW_pos : 0 < finrank ℂ (W : Submodule ℂ V) := by
    have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hW_ne_bot
    exact Module.finrank_pos (R := ℂ)
  -- V/W has strictly smaller dimension
  have hVW_lt : finrank ℂ (V ⧸ W) < finrank ℂ V := by
    have h1 := Submodule.finrank_quotient_add_finrank W.toSubmodule
    have h2 : finrank ℂ (V ⧸ W) = finrank ℂ (V ⧸ W.toSubmodule) := rfl
    omega
  -- By induction, V/W has ComplementedLattice
  have hVW_compl : ComplementedLattice (LieSubmodule ℂ sl2 (V ⧸ W)) :=
    ih (finrank ℂ (V ⧸ W)) (by omega) (V ⧸ W) (le_refl _)
  set π := LieSubmodule.Quotient.mk' W
  -- Image of N in V/W and its complement
  obtain ⟨T_bar, hT_bar⟩ := hVW_compl.exists_isCompl (LieSubmodule.map π N)
  -- Pull back to T in V
  set T := LieSubmodule.comap π T_bar
  -- Key facts: N ⊓ T = W and N ⊔ T = ⊤
  have hW_le_T : W ≤ T := by
    intro w hw
    show π w ∈ T_bar
    have : π w = 0 := (LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr hw
    rw [this]; exact T_bar.zero_mem
  have hNT_inf : N ⊓ T = W := by
    apply le_antisymm
    · intro v ⟨hvN, hvT⟩
      have hvN_bar : π v ∈ LieSubmodule.map π N := LieSubmodule.mem_map_of_mem hvN
      have : π v ∈ (LieSubmodule.map π N ⊓ T_bar : LieSubmodule ℂ sl2 (V ⧸ W)) :=
        ⟨hvN_bar, hvT⟩
      rw [hT_bar.inf_eq_bot, LieSubmodule.mem_bot] at this
      exact (LieSubmodule.Quotient.mk_eq_zero (N := W)).mp this
    · exact le_inf hWN hW_le_T
  have hNT_sup : N ⊔ T = ⊤ := by
    rw [eq_top_iff]; intro v _
    have hv_top : π v ∈ (⊤ : LieSubmodule ℂ sl2 (V ⧸ W)) := LieSubmodule.mem_top _
    rw [← hT_bar.sup_eq_top, LieSubmodule.mem_sup] at hv_top
    obtain ⟨a, ha, b, hb, hab⟩ := hv_top
    rw [LieSubmodule.mem_map] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    have hvn : v - n ∈ (T : LieSubmodule ℂ sl2 V) := by
      show π (v - n) ∈ T_bar
      rw [map_sub, ← hab, add_sub_cancel_left]; exact hb
    rw [show v = n + (v - n) by abel, LieSubmodule.mem_sup]
    exact ⟨n, hn, v - n, hvn, rfl⟩
  -- Case split: N = W or W < N
  by_cases hNW : N = W
  · -- N is an atom (irreducible submodule). Reduce to finding a disjoint atom.
    rw [hNW]
    by_cases hirr : LieModule.IsIrreducible ℂ sl2 (V ⧸ W)
    · -- V/W irreducible: use the splitting lemma directly
      exact exists_complement_of_irreducible_quotient d hd W (hNW ▸ hN_ne_top) hW_atom hirr ih
    · -- V/W not irreducible: find an atom W' disjoint from W
      haveI : Nontrivial (V ⧸ W) := by
        rw [← not_subsingleton_iff_nontrivial]; intro hs
        exact (hNW ▸ hN_ne_top) (by
          rw [eq_top_iff]; intro v _
          have := Subsingleton.elim (LieSubmodule.Quotient.mk' W v) 0
          rwa [LieSubmodule.Quotient.mk_eq_zero] at this)
      -- V/W has a proper nonzero submodule (not irreducible)
      have hnotirr : ¬∀ S : LieSubmodule ℂ sl2 (V ⧸ W), S = ⊥ ∨ S = ⊤ := by
        intro hall; exact hirr (LieModule.IsIrreducible.mk (fun S hS => (hall S).resolve_left hS))
      push_neg at hnotirr
      obtain ⟨S_bar, hS_ne_bot, hS_ne_top⟩ := hnotirr
      -- Pull back S_bar to get E with W ⊊ E ⊊ V
      set E := LieSubmodule.comap π S_bar
      have hW_le_E : W ≤ E := fun w hw => by
        show π w ∈ S_bar
        rw [(LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr hw]; exact S_bar.zero_mem
      have hE_ne_top : (E : LieSubmodule ℂ sl2 V) ≠ ⊤ := by
        intro h; apply hS_ne_top; rw [eq_top_iff]; intro v _
        obtain ⟨v₀, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W v
        exact (h ▸ LieSubmodule.mem_top v₀ : v₀ ∈ E)
      have hW_ne_E : W ≠ E := by
        intro h; apply hS_ne_bot; rw [eq_bot_iff]; intro v hv
        obtain ⟨v₀, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W v
        have : v₀ ∈ E := hv
        rw [← h] at this
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero (N := W)).mpr this
      have hW_lt_E : W < E := lt_of_le_of_ne hW_le_E hW_ne_E
      -- dim E < dim V
      have hE_lt : finrank ℂ (E : Submodule ℂ V) < finrank ℂ V := by
        have h1 : E.toSubmodule ≠ ⊤ := by
          intro h; apply hE_ne_top
          rw [eq_top_iff]; intro v _
          show v ∈ E.toSubmodule; rw [h]; trivial
        have h2 := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr h1)
        rwa [finrank_top] at h2
      -- E is completely reducible by ih
      have hE_compl : ComplementedLattice (LieSubmodule ℂ sl2 E) :=
        ih (finrank ℂ (E : Submodule ℂ V)) (by omega) E le_rfl
      -- W inside E
      set W_E := LieSubmodule.comap (E : LieSubmodule ℂ sl2 V).incl W
      -- W_E ≠ ⊤ (since W ⊊ E)
      have hW_E_ne_top : W_E ≠ ⊤ := by
        intro h; exact absurd (le_antisymm (fun v hv => by
          have : (⟨v, hv⟩ : E) ∈ W_E := h ▸ LieSubmodule.mem_top _
          exact this) hW_le_E) (ne_of_lt hW_lt_E).symm
      -- Get complement of W_E in E
      obtain ⟨C_E, hC_E⟩ := hE_compl.exists_isCompl W_E
      have hC_E_ne_bot : C_E ≠ ⊥ := by
        intro h; exact hW_E_ne_top (by rw [← hC_E.sup_eq_top, h, sup_bot_eq])
      -- Map C_E to V
      set C_V := LieSubmodule.map (E : LieSubmodule ℂ sl2 V).incl C_E
      -- C_V ⊓ W = ⊥
      have hC_V_disj : C_V ⊓ W = ⊥ := by
        rw [eq_bot_iff]; intro v ⟨hvC, hvW⟩
        have hvC' : v ∈ (C_V : LieSubmodule ℂ sl2 V) := hvC
        rw [LieSubmodule.mem_map] at hvC'
        obtain ⟨c, hc, rfl⟩ := hvC'
        have hcW : c ∈ W_E := hvW
        have : c ∈ (W_E ⊓ C_E : LieSubmodule ℂ sl2 E) := ⟨hcW, hc⟩
        rw [hC_E.inf_eq_bot, LieSubmodule.mem_bot] at this
        simp [this]
      -- C_V ≠ ⊥
      have hC_V_ne_bot : C_V ≠ ⊥ := by
        intro h; apply hC_E_ne_bot; rw [eq_bot_iff]; intro c hc
        have : (E : LieSubmodule ℂ sl2 V).incl c ∈ C_V :=
          LieSubmodule.mem_map_of_mem hc
        rw [h, LieSubmodule.mem_bot] at this
        rw [LieSubmodule.mem_bot]
        exact Subtype.val_injective this
      -- Get atom W' ≤ C_V
      obtain ⟨W', hW'_atom, hW'_le⟩ :=
        (eq_bot_or_exists_atom_le C_V).resolve_left hC_V_ne_bot
      -- W' ⊓ W = ⊥ (since W' ≤ C_V and C_V ⊓ W = ⊥)
      have hW'_disj : W' ⊓ W = ⊥ :=
        eq_bot_iff.mpr (le_trans (inf_le_inf_right W hW'_le) (le_of_eq hC_V_disj))
      -- Apply complement_case_disjoint with the new atom
      exact complement_case_disjoint d ih hd W W' hW_ne_bot hW'_atom hW'_disj
  · -- W < N strictly. T has smaller dimension than V.
    have hW_lt_N : W < N := lt_of_le_of_ne hWN (Ne.symm hNW)
    have hfW_lt_N : finrank ℂ (W : Submodule ℂ V) < finrank ℂ (N : Submodule ℂ V) :=
      Submodule.finrank_lt_finrank_of_lt (show W.toSubmodule < N.toSubmodule from hW_lt_N)
    -- dim T < dim V by the inf/sup dimension formula
    have hfT_lt : finrank ℂ (T : Submodule ℂ V) < finrank ℂ V := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq N.toSubmodule T.toSubmodule
      have h2 : N.toSubmodule ⊔ T.toSubmodule = ⊤ := by
        have := congrArg LieSubmodule.toSubmodule hNT_sup
        rwa [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule] at this
      have h3 : N.toSubmodule ⊓ T.toSubmodule = W.toSubmodule := by
        have := congrArg LieSubmodule.toSubmodule hNT_inf
        rwa [LieSubmodule.inf_toSubmodule] at this
      rw [h2, h3, finrank_top] at h1; omega
    -- By induction, T is completely reducible
    have hT_compl : ComplementedLattice (LieSubmodule ℂ sl2 T) :=
      ih (finrank ℂ (T : Submodule ℂ V)) (by omega) T (le_refl _)
    -- W viewed inside T
    set W_T := LieSubmodule.comap T.incl W
    -- Get complement of W_T in T
    obtain ⟨U_T, hU_T⟩ := hT_compl.exists_isCompl W_T
    -- Map U_T back to V
    set U := LieSubmodule.map T.incl U_T
    refine ⟨U, ?_⟩
    rw [← LieSubmodule.isCompl_toSubmodule]
    constructor
    · -- Disjoint: N ∩ U = ⊥
      rw [disjoint_iff_inf_le]
      intro v ⟨hvN, hvU⟩
      -- v ∈ U = map T.incl U_T, so v = T.incl u for some u ∈ U_T
      have hvU' : v ∈ (U : LieSubmodule ℂ sl2 V) := hvU
      rw [LieSubmodule.mem_map] at hvU'
      obtain ⟨u, hu, rfl⟩ := hvU'
      -- T.incl u ∈ N ∩ T = W
      have h1 : T.incl u ∈ (N ⊓ T : LieSubmodule ℂ sl2 V) :=
        ⟨hvN, u.property⟩
      rw [hNT_inf] at h1
      -- u ∈ W_T ⊓ U_T = ⊥
      have h3 : u ∈ (W_T ⊓ U_T : LieSubmodule ℂ sl2 T) := ⟨h1, hu⟩
      rw [hU_T.inf_eq_bot, LieSubmodule.mem_bot] at h3
      simp [h3]
    · -- Codisjoint: N ⊔ U = ⊤
      rw [codisjoint_iff, eq_top_iff]
      intro v _
      -- v ∈ N ⊔ T = ⊤, so v = n + t
      have hv_NT : v ∈ (N ⊔ T : LieSubmodule ℂ sl2 V) := hNT_sup ▸ LieSubmodule.mem_top v
      rw [LieSubmodule.mem_sup] at hv_NT
      obtain ⟨n, hn, t_val, ht, rfl⟩ := hv_NT
      -- t ∈ T, decompose in T: t = w + u (W_T ⊔ U_T = ⊤)
      have ht_WT : (⟨t_val, ht⟩ : T) ∈ (W_T ⊔ U_T : LieSubmodule ℂ sl2 T) :=
        hU_T.sup_eq_top ▸ LieSubmodule.mem_top _
      rw [LieSubmodule.mem_sup] at ht_WT
      obtain ⟨w, hw, u, hu, hwu⟩ := ht_WT
      -- T.incl w ∈ W ≤ N
      have hw_N : (T.incl w : V) ∈ N := hWN hw
      -- t = w + u (as elements of V), so n + t = (n + w) + u ∈ N + U
      have ht_eq : t_val = (w : V) + (u : V) := by
        have := congrArg Subtype.val hwu
        simp only [LieSubmodule.incl_apply, AddSubmonoid.mk_add_mk] at this
        exact this.symm
      rw [ht_eq, show n + ((w : V) + (u : V)) = (n + (w : V)) + (u : V) by abel]
      exact Submodule.add_mem_sup (N.add_mem hn hw_N) (LieSubmodule.mem_map_of_mem hu)

private lemma complementedLattice_sl2_aux (d : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V],
    finrank ℂ V ≤ d →
    ComplementedLattice (LieSubmodule ℂ sl2 V) := by
  induction d using Nat.strongRecOn with | ind d ih => ?_
  intro V _ _ _ _ _ hd
  constructor
  intro N
  by_cases hNbot : N = ⊥
  · exact ⟨⊤, hNbot ▸ isCompl_bot_top⟩
  by_cases hNtop : N = ⊤
  · exact ⟨⊥, hNtop ▸ isCompl_top_bot⟩
  haveI hnt : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]; intro hs
    exact hNbot (by ext v; simp [Subsingleton.elim v 0])
  obtain ⟨W, hW_atom⟩ := exists_irreducible_lieSubmodule (V := V)
  by_cases hWN : W ≤ N
  · exact complement_case_sub d ih hd N W hNtop hW_atom hWN
  · have hWN_bot : W ⊓ N = ⊥ :=
      (hW_atom.le_iff.mp inf_le_left).resolve_right (fun h => hWN (h ▸ inf_le_right))
    exact complement_case_disjoint d ih hd N W hNbot hW_atom hWN_bot

/-- Part (ii): Any finite-dimensional representation of sl(2, ℂ) is completely reducible.
Every Lie submodule has a complementary Lie submodule, i.e., the lattice of Lie submodules
is complemented. This is equivalent to saying every finite-dimensional representation
decomposes as a direct sum of irreducible representations.
(Etingof Theorem 2.1.1(ii)) -/
theorem Theorem_2_1_1_ii (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V] :
    ComplementedLattice (LieSubmodule ℂ sl2 V) :=
  complementedLattice_sl2_aux (finrank ℂ V) V le_rfl

end CompleteReducibility

end Etingof
