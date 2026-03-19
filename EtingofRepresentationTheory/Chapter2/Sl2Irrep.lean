import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis
import EtingofRepresentationTheory.Chapter2.Theorem2_1_1

/-!
# Construction of irreducible sl(2) representations

We construct the d-dimensional irreducible representation V_d of sl(2, ℂ)
and prove the sl(2) triple relations.

The key idea is to define a Lie algebra homomorphism ρ : sl(2) → End(V_d),
where V_d = Fin d → ℂ. The Leibniz identity then follows automatically
from `LieRingModule.compLieHom`.

The representation action (on components) is:
- (ρ(h) · v)_k = (d - 1 - 2k) · v_k     (h acts diagonally)
- (ρ(e) · v)_k = (k+1) · v_{k+1}         (e picks up v_{k+1})
- (ρ(f) · v)_k = (d - k) · v_{k-1}       (f picks up v_{k-1})

## Blocked

The Leibniz identity proof (`rho_map_lie`) requires verifying that the representation
map preserves Lie brackets. This reduces to 9 generator pairs but each involves
intricate casework on boundary conditions (k=0, k+1=d, nested boundaries).
Similarly, irreducibility requires showing that any nonzero invariant subspace is the
whole space. Both require significant additional work.

Complete reducibility (Theorem 2.1.1(ii)) requires Weyl's complete reducibility theorem
for semisimple Lie algebras, which is not in Mathlib.
-/

open scoped Matrix
open Etingof

namespace Etingof.Sl2Irrep

/-! ## The standard sl(2) triple -/

/-- The standard basis element e₁₂ of sl(2). -/
noncomputable def sl2_e : sl2 :=
  LieAlgebra.SpecialLinear.single 0 1 (by omega) 1

/-- The standard basis element e₂₁ of sl(2). -/
noncomputable def sl2_f : sl2 :=
  LieAlgebra.SpecialLinear.single 1 0 (by omega) 1

/-- The standard diagonal element h = e₁₁ - e₂₂ of sl(2). -/
noncomputable def sl2_h : sl2 :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1

private theorem sl2_ext {A B : sl2} (h : A.val = B.val) : A = B :=
  Subtype.ext h

/-- [e, f] = h -/
theorem lie_e_f : ⁅sl2_e, sl2_f⁆ = sl2_h := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, sl2_e, sl2_f, sl2_h,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Fin.sum_univ_two]

/-- [h, e] = 2e -/
theorem lie_h_e : ⁅sl2_h, sl2_e⁆ = 2 • sl2_e := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, sl2_e, sl2_h,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Fin.sum_univ_two]

/-- [h, f] = -2f -/
theorem lie_h_f : ⁅sl2_h, sl2_f⁆ = -(2 • sl2_f) := by
  apply sl2_ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, sl2_f, sl2_h,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.sub_apply, Matrix.mul_apply,
    Matrix.single, Matrix.smul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- h ≠ 0. -/
theorem sl2_h_ne_zero : sl2_h ≠ 0 := by
  intro h
  have : (sl2_h : sl2).val 0 0 = (0 : sl2).val 0 0 := by rw [h]
  simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.sub_apply,
    Matrix.single] at this

/-- The standard sl(2) triple. -/
theorem sl2_triple : IsSl2Triple sl2_h sl2_e sl2_f where
  h_ne_zero := sl2_h_ne_zero
  lie_e_f := lie_e_f
  lie_h_e_nsmul := lie_h_e
  lie_h_f_nsmul := lie_h_f

/-! ## Tracelessness -/

/-- The (1,1) entry of an sl(2) matrix equals the negative of the (0,0) entry. -/
theorem sl2_traceless (X : sl2) : X.val 1 1 = -X.val 0 0 := by
  have h2 : X.val 0 0 + X.val 1 1 = 0 := by
    have h3 : Matrix.trace X.val = 0 := X.property
    have h4 : Matrix.trace X.val = X.val 0 0 + X.val 1 1 := by
      show ∑ i : Fin 2, X.val i i = _; rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simp at this; exact this

/-! ## The d-dimensional irreducible representation

We define ρ : sl(2) → End(V_d) as a Lie algebra homomorphism, then use
`LieRingModule.compLieHom` to get the Lie module structure on V_d.

The representation decomposes as ρ(X) = X₀₀·H + X₀₁·E + X₁₀·F where
H, E, F are the diagonal, raising, and lowering endomorphisms. The Lie
bracket preservation follows from the commutator identities
[E,F] = H, [H,E] = 2E, [H,F] = -2F. -/

/-- Diagonal (h-weight) endomorphism: H(v)_k = (d-1-2k)·v_k. -/
private noncomputable def rhoH (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' r w := by ext k; simp [mul_comm r, mul_assoc, smul_eq_mul]

/-- Raising endomorphism: E(v)_k = (k+1)·v_{k+1}, with v_d = 0. -/
private noncomputable def rhoE (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := (↑(k : ℕ) + 1) * if h : (k : ℕ) + 1 < d then v ⟨k + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- Lowering endomorphism: F(v)_k = (d-k)·v_{k-1}, with v_{-1} = 0. -/
private noncomputable def rhoF (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - ↑(k : ℕ)) * if h : 0 < (k : ℕ) then v ⟨k - 1, by omega⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- [H, E] = 2E: the diagonal and raising endomorphisms satisfy this commutator. -/
private theorem lie_rhoH_rhoE (d : ℕ) :
    ⁅rhoH d, rhoE d⁆ = (2 : ℂ) • rhoE d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, rhoH, rhoE, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k : ℕ) + 1 < d
  · simp only [he, dite_true, show (⟨k.val + 1, he⟩ : Fin d).val = k.val + 1 from rfl]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero, mul_comm 2]

/-- [H, F] = -2F: the diagonal and lowering endomorphisms satisfy this commutator. -/
private theorem lie_rhoH_rhoF (d : ℕ) :
    ⁅rhoH d, rhoF d⁆ = -((2 : ℂ) • rhoF d) := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, rhoH, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hf : 0 < (k : ℕ)
  · simp only [hf, dite_true]
    have hle : 1 ≤ (k : ℕ) := by omega
    simp only [Nat.cast_sub hle]
    ring
  · simp only [hf, dite_false, mul_zero, sub_zero, neg_zero]

/-- [E, F] = H: the raising and lowering endomorphisms satisfy this commutator.
    Proof: E(F(v))_k - F(E(v))_k = (k+1)(d-k-1)v_k - k(d-k)v_k = (d-1-2k)v_k = H(v)_k
    after handling boundary conditions. -/
private theorem lie_rhoE_rhoF (d : ℕ) :
    ⁅rhoE d, rhoF d⁆ = rhoH d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    rhoH, rhoE, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  -- Helper: any ⟨k.val, _⟩ : Fin d equals k
  have hfin_k : ∀ (h : (k : ℕ) < d), (⟨(k : ℕ), h⟩ : Fin d) = k := fun _ => by ext; rfl
  by_cases he : (k : ℕ) + 1 < d <;> by_cases hf : 0 < (k : ℕ)
  · -- Interior: k+1 < d, k > 0
    simp only [he, hf, k.isLt, dite_true,
      show (⟨(k : ℕ) + 1, he⟩ : Fin d).val = (k : ℕ) + 1 from rfl,
      show (⟨(k : ℕ) - 1, by omega⟩ : Fin d).val = (k : ℕ) - 1 from rfl,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      show (k : ℕ) - 1 + 1 < d from by omega,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      show (k : ℕ) < d from k.isLt, dite_true,
      hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    push_cast; ring
  · -- k+1 < d, k = 0
    have hk0 : (k : ℕ) = 0 := by omega
    simp only [he, hf, k.isLt, dite_true, dite_false, mul_zero, sub_zero,
      show (⟨(k : ℕ) + 1, he⟩ : Fin d).val = (k : ℕ) + 1 from rfl,
      show 0 < (k : ℕ) + 1 from by omega,
      show (k : ℕ) + 1 - 1 = (k : ℕ) from by omega,
      show (k : ℕ) < d from k.isLt, dite_true,
      hfin_k k.isLt]
    simp [hk0]
  · -- k+1 ≥ d (k = d-1), k > 0
    simp only [he, hf, k.isLt, dite_true, dite_false, mul_zero, zero_sub,
      show (⟨(k : ℕ) - 1, by omega⟩ : Fin d).val = (k : ℕ) - 1 from rfl,
      show (k : ℕ) - 1 + 1 < d from by omega,
      show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega,
      show (k : ℕ) < d from k.isLt, dite_true,
      hfin_k k.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k : ℕ) from by omega)]
    have hkd1 : (k : ℕ) + 1 = d := by omega
    push_cast [Nat.cast_sub (show 1 ≤ d from by omega), ← hkd1]; ring
  · -- k+1 ≥ d, k = 0 ⟹ d ≤ 1
    have hk0 : (k : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    simp only [he, hf, dite_false, mul_zero, zero_sub, neg_zero]
    subst hd1; simp [hk0]

/-- The representation map ρ : sl(2) → End(V_d) as a Lie hom.
    ρ(X)(v)_k = X₀₀·(d-1-2k)·v_k + X₀₁·(k+1)·v_{k+1} + X₁₀·(d-k)·v_{k-1}. -/
private theorem sl2_val_add (X Y : sl2) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem sl2_val_smul (r : ℂ) (X : sl2) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl

noncomputable def rhoLieHom (d : ℕ) : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ) where
  toFun X := X.val 0 0 • rhoH d + X.val 0 1 • rhoE d + X.val 1 0 • rhoF d
  map_add' X Y := by
    simp only [sl2_val_add, add_smul]; abel
  map_smul' r X := by
    simp only [sl2_val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    -- Use tracelessness to compute bracket matrix entries
    have htX : X.val 1 1 = -X.val 0 0 := sl2_traceless X
    have htY : Y.val 1 1 = -Y.val 0 0 := sl2_traceless Y
    -- Expand the Lie bracket using bilinearity and the three commutator identities
    -- [H,E]=2E, [H,F]=-2F, [E,F]=H, [E,H]=-2E, [F,H]=2F, [F,E]=-H
    -- Then match coefficients with the bracket matrix entries.
    -- Goal: toFun ⁅X,Y⁆ = ⁅toFun X, toFun Y⁆
    -- i.e., [X,Y]₀₀•H + [X,Y]₀₁•E + [X,Y]₁₀•F =
    --   ⁅X₀₀•H + X₀₁•E + X₁₀•F, Y₀₀•H + Y₀₁•E + Y₁₀•F⁆
    -- Expand RHS by Lie algebra axioms:
    have hEH : ⁅rhoE d, rhoH d⁆ = -((2 : ℂ) • rhoE d) := by
      rw [← lie_skew, lie_rhoH_rhoE]
    have hFH : ⁅rhoF d, rhoH d⁆ = (2 : ℂ) • rhoF d := by
      rw [← lie_skew, lie_rhoH_rhoF, neg_neg]
    have hFE : ⁅rhoF d, rhoE d⁆ = -(rhoH d) := by
      rw [← lie_skew, lie_rhoE_rhoF]
    -- Compute bracket matrix entries
    have hbr00 : ⁅X, Y⁆.val 0 0 =
        X.val 0 1 * Y.val 1 0 - Y.val 0 1 * X.val 1 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hbr01 : ⁅X, Y⁆.val 0 1 =
        2 * X.val 0 0 * Y.val 0 1 - 2 * Y.val 0 0 * X.val 0 1 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring
    have hbr10 : ⁅X, Y⁆.val 1 0 =
        2 * X.val 1 0 * Y.val 0 0 - 2 * Y.val 1 0 * X.val 0 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring
    -- Expand the Lie bracket on Module.End by bilinearity
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add,
      lie_rhoH_rhoE, lie_rhoH_rhoF, lie_rhoE_rhoF, hEH, hFH, hFE,
      smul_neg, neg_smul, smul_smul, hbr00, hbr01, hbr10]
    module

/-- V_d is a Lie ring module over sl(2), via the representation ρ. -/
noncomputable instance irrepLieRingModule (d : ℕ) : LieRingModule sl2 (Fin d → ℂ) :=
  LieRingModule.compLieHom (Fin d → ℂ) (rhoLieHom d)

/-- V_d is a Lie module over ℂ. -/
noncomputable instance irrepLieModule (d : ℕ) : @LieModule ℂ sl2 (Fin d → ℂ) _ _ _ _ _
    (irrepLieRingModule d) :=
  LieModule.compLieHom (Fin d → ℂ) (rhoLieHom d)

/-- V_d has the correct dimension. -/
theorem irrep_finrank (d : ℕ) [NeZero d] :
    Module.finrank ℂ (Fin d → ℂ) = d := by
  simp

/-- V_d is irreducible as an sl(2)-module (for d ≥ 1).

    The proof would show that any nonzero sl(2)-invariant subspace W ⊂ V_d must be all of V_d,
    by using the h-eigenvalue decomposition and the raising/lowering operators e, f. -/
theorem irrep_isIrreducible (d : ℕ) [NeZero d] :
    letI := irrepLieRingModule d
    letI := irrepLieModule d
    LieModule.IsIrreducible ℂ sl2 (Fin d → ℂ) := sorry

end Etingof.Sl2Irrep
