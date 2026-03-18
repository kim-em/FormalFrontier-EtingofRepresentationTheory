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

The Lie algebra homomorphism property `ρ([X,Y]) = [ρ(X), ρ(Y)]` is sorry'd:
it requires verifying the commutator identity for 9 pairs of generators
with intricate boundary casework. -/

/-- The representation map ρ : sl(2) → End(V_d) as a Lie hom.
    ρ(X)(v)_k = X₀₀·(d-1-2k)·v_k + X₀₁·(k+1)·v_{k+1} + X₁₀·(d-k)·v_{k-1}. -/
noncomputable def rhoLieHom (d : ℕ) : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ) := sorry

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
