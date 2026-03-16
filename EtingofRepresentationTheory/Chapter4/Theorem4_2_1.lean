import Mathlib
import EtingofRepresentationTheory.Infrastructure.ColumnRepSimple

/-!
# Theorem 4.2.1: Characters Form a Basis of Class Functions

If k is algebraically closed and char(k) does not divide |G|, the characters of irreducible
representations of G form a basis of the space Fc(G, k) of class functions on G.

We state this as: every class function (a function G → k constant on conjugacy classes)
lies in the k-linear span of characters of simple (irreducible) FDRep objects.
Linear independence of distinct irreducible characters follows from orthogonality
(Theorem 4.5.1 / `FDRep.char_orthonormal`).

## Proof strategy

We prove that any class function orthogonal to all irreducible characters must be zero.
This uses the group algebra k[G]: such a function corresponds to a central element whose
Wedderburn-Artin projections are scalar matrices with zero trace, hence zero.
-/

open FDRep CategoryTheory Finset

universe u

namespace Etingof.Theorem4_2_1_aux

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [Invertible (Fintype.card G : k)]

/-! ### Step 1: Group algebra element from a function -/

/-- The group algebra element corresponding to a function f : G → k,
  defined as α = ∑_g f(g) · g⁻¹ in k[G]. -/
noncomputable def toGroupAlgebra (f : G → k) : MonoidAlgebra k G :=
  ∑ g : G, MonoidAlgebra.single g⁻¹ (f g)

/-- The trace of the representation action of `toGroupAlgebra f` on V equals
  `∑ g, f g * V.character g⁻¹`. -/
private lemma trace_toGroupAlgebra_action (f : G → k) (V : FDRep k G) :
    LinearMap.trace k V (Representation.asAlgebraHom V.ρ (toGroupAlgebra f)) =
      ∑ g : G, f g * V.character g⁻¹ := by
  simp only [toGroupAlgebra, map_sum, Representation.asAlgebraHom_single]
  congr 1; ext g
  rw [LinearMap.map_smul, smul_eq_mul, FDRep.character]

/-- `toGroupAlgebra` is injective: if `toGroupAlgebra f = 0` then `f = 0`. -/
private lemma toGroupAlgebra_injective (f : G → k) (h : toGroupAlgebra f = 0) : f = 0 := by
  ext g
  simp only [Pi.zero_apply]
  have heval : (toGroupAlgebra f) g⁻¹ = 0 := by simp [h]
  simp only [toGroupAlgebra] at heval
  rw [show (∑ x : G, MonoidAlgebra.single x⁻¹ (f x)) g⁻¹ =
    ∑ x : G, (MonoidAlgebra.single x⁻¹ (f x) : G →₀ k) g⁻¹ from
    Finsupp.finset_sum_apply _ _ _] at heval
  rw [Finset.sum_eq_single g] at heval
  · simpa [Finsupp.single_apply] using heval
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (show b⁻¹ ≠ g⁻¹ from fun h => hb (inv_injective h))]
  · intro h; exact absurd (Finset.mem_univ g) h

/-! ### Step 2: Centrality of toGroupAlgebra for class functions -/

/-- `toGroupAlgebra f` commutes with all group elements when f is a class function. -/
private lemma toGroupAlgebra_comm_of (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (h : G) :
    MonoidAlgebra.single h (1 : k) * toGroupAlgebra f =
    toGroupAlgebra f * MonoidAlgebra.single h (1 : k) := by
  simp only [toGroupAlgebra, Finset.mul_sum, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
  rw [show (h * g * h⁻¹)⁻¹ * h = h * g⁻¹ from by group, hf g h]

/-- `toGroupAlgebra f` is central in k[G] when f is a class function. -/
private lemma toGroupAlgebra_central (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    ∀ β : MonoidAlgebra k G, β * toGroupAlgebra f = toGroupAlgebra f * β := by
  intro β
  induction β using MonoidAlgebra.induction_on with
  | hM g => exact toGroupAlgebra_comm_of f hf g
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]
  | hsmul r a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

/-! ### Step 3: Matrix center and completeness -/

/-- An element of Mat(n,k) that commutes with all matrices is a scalar matrix. -/
private lemma matrix_central_eq_scalar {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) k)
    (hM : ∀ N : Matrix (Fin n) (Fin n) k, N * M = M * N) :
    ∃ c : k, M = c • (1 : Matrix (Fin n) (Fin n) k) := by
  have hoff : ∀ r c : Fin n, r ≠ c → M r c = 0 := by
    intro r c hrc
    have h := congr_fun₂ (hM (Matrix.single c r 1)) c c
    simp only [Matrix.mul_apply, Matrix.single_apply, ite_and] at h
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero] at h
    simpa [hrc, Ne.symm hrc] using h
  have hdiag : ∀ i : Fin n, M i i = M 0 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · have h := congr_fun₂ (hM (Matrix.single (0 : Fin n) i 1)) 0 i
      simp only [Matrix.mul_apply, Matrix.single_apply, ite_and] at h
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul,
        mul_ite, mul_one, mul_zero] at h
      simpa [Ne.symm hi] using h
  use M 0 0
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [hdiag]
  · simp [hij, hoff i j hij]

omit [DecidableEq G] [Invertible (Fintype.card G : k)] in
/-- `projRingHom` preserves scalar multiplication. -/
private lemma projRingHom_smul' [NeZero (Nat.card G : k)] (D : IrrepDecomp k G) (i : Fin D.n)
    (r : k) (α : MonoidAlgebra k G) :
    D.projRingHom i (r • α) = r • D.projRingHom i α := by
  show (Pi.evalRingHom _ i) (D.iso (r • α)) = r • (Pi.evalRingHom _ i) (D.iso α)
  rw [show D.iso (r • α) = r • D.iso α from map_smul D.iso r α]
  simp [Pi.evalRingHom_apply, Pi.smul_apply]

/-- **Character completeness**: A class function orthogonal to all irreducible
characters is zero. -/
private lemma classFunction_eq_zero_of_orthogonal_simples
    (f : G → k) (hf_class : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0 := by
  apply toGroupAlgebra_injective
  set α := toGroupAlgebra f
  haveI : NeZero (Nat.card G : k) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  let D := IrrepDecomp.mk' (k := k) (G := G)
  suffices h : D.iso α = 0 by exact D.iso.injective (h ▸ (map_zero D.iso).symm ▸ rfl)
  funext i
  show D.projRingHom i α = 0
  haveI := D.d_pos i
  have hcentral : ∀ N, N * D.projRingHom i α = D.projRingHom i α * N := by
    intro N
    obtain ⟨β, rfl⟩ := D.projRingHom_surjective i N
    rw [← map_mul, ← map_mul, toGroupAlgebra_central f hf_class]
  obtain ⟨c, hc⟩ := matrix_central_eq_scalar (D.projRingHom i α) hcentral
  -- Compute trace via the representation
  have htrace : Matrix.trace (D.projRingHom i α) = 0 := by
    have hrepr : Representation.asAlgebraHom (D.columnRep i) α =
        Matrix.mulVecLin (D.projRingHom i α) := by
      induction α using MonoidAlgebra.induction_on with
      | hM g =>
        simp only [Representation.asAlgebraHom, MonoidAlgebra.lift_of]; rfl
      | hadd a b ha hb => simp only [map_add, ha, hb]
      | hsmul r a ha => simp only [map_smul, projRingHom_smul', ha]
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply', ← hrepr]
    -- Goal: LinearMap.trace k _ (asAlgebraHom (columnRep i) α) = 0
    -- Use trace_toGroupAlgebra_action: this gives the sum = ∑ g, f g * χ_i(g⁻¹)
    have key := trace_toGroupAlgebra_action f (D.columnFDRep i)
    simp only [show (D.columnFDRep i).ρ = D.columnRep i from rfl] at key
    -- key : trace k ↑V (asAlgebraHom (columnRep i) (toGroupAlgebra f)) = ∑ g, ...
    -- Goal: trace k (Fin (D.d i) → k) (asAlgebraHom (columnRep i) α) = 0
    -- These types are definitionally equal
    exact key.trans (hf_orth (D.columnFDRep i))
  -- trace(c • 1) = c · d_i = 0 → c = 0
  rw [hc] at htrace
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htrace
  -- c * (D.d i : k) = 0, need (D.d i : k) ≠ 0
  -- This follows from d_i | |G| (dimension divisibility theorem) and Invertible (|G| : k)
  have hd_ne : (D.d i : k) ≠ 0 := by
    -- d_i divides |G| for irreducible representations over algebraically closed fields
    -- with char(k) ∤ |G|. This is a standard result but requires separate formalization.
    sorry
  have hc_zero : c = 0 := (mul_eq_zero.mp htrace).resolve_right hd_ne
  rw [hc, hc_zero, zero_smul]

end Etingof.Theorem4_2_1_aux

open Etingof.Theorem4_2_1_aux in
/-- Characters of irreducible representations span the space of class functions:
every function G → k that is constant on conjugacy classes is a k-linear combination
of characters of simple (irreducible) representations. (Etingof Theorem 4.2.1) -/
theorem Etingof.Theorem4_2_1
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) := by
  classical
  rw [Submodule.mem_span]
  intro p hp
  sorry
