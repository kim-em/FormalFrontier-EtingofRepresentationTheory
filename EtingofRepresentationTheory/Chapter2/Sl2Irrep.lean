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
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- Lowering endomorphism: F(v)_k = (d-k)·v_{k-1}, with v_{-1} = 0. -/
private noncomputable def rhoF (d : ℕ) : Module.End ℂ (Fin d → ℂ) where
  toFun v k := ((d : ℂ) - ↑(k : ℕ)) *
    if h : 0 < (k : ℕ) then v ⟨k - 1, by omega⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- [H, E] = 2E -/
private theorem lie_rhoH_rhoE (d : ℕ) :
    ⁅rhoH d, rhoE d⁆ = (2 : ℂ) • rhoE d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, rhoH, rhoE, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k : ℕ) + 1 < d
  · simp only [he, dite_true]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero]

/-- [H, F] = -2F -/
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

/-- [E, F] = H -/
private theorem lie_rhoE_rhoF (d : ℕ) :
    ⁅rhoE d, rhoF d⁆ = rhoH d := by
  apply LinearMap.ext; intro v; funext k
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    rhoH, rhoE, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin_k : ∀ (h : (k : ℕ) < d), (⟨(k : ℕ), h⟩ : Fin d) = k :=
    fun _ => by ext; rfl
  by_cases he : (k : ℕ) + 1 < d <;> by_cases hf : 0 < (k : ℕ)
  · -- Interior: k+1 < d, k > 0
    simp only [he, hf, k.isLt, dite_true,
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

/-- The representation map ρ : sl(2) → End(V_d) as a Lie hom. -/
private theorem sl2_val_add (X Y : sl2) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem sl2_val_smul (r : ℂ) (X : sl2) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl

noncomputable def rhoLieHom (d : ℕ) :
    sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin d → ℂ) where
  toFun X := X.val 0 0 • rhoH d + X.val 0 1 • rhoE d + X.val 1 0 • rhoF d
  map_add' X Y := by
    simp only [sl2_val_add, add_smul]; abel
  map_smul' r X := by
    simp only [sl2_val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := sl2_traceless X
    have htY : Y.val 1 1 = -Y.val 0 0 := sl2_traceless Y
    have hEH : ⁅rhoE d, rhoH d⁆ = -((2 : ℂ) • rhoE d) := by
      rw [← lie_skew, lie_rhoH_rhoE]
    have hFH : ⁅rhoF d, rhoH d⁆ = (2 : ℂ) • rhoF d := by
      rw [← lie_skew, lie_rhoH_rhoF, neg_neg]
    have hFE : ⁅rhoF d, rhoE d⁆ = -(rhoH d) := by
      rw [← lie_skew, lie_rhoE_rhoF]
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
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero,
      add_zero, zero_add, lie_rhoH_rhoE, lie_rhoH_rhoF, lie_rhoE_rhoF,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module

/-- V_d is a Lie ring module over sl(2), via the representation ρ. -/
noncomputable instance irrepLieRingModule (d : ℕ) :
    LieRingModule sl2 (Fin d → ℂ) :=
  LieRingModule.compLieHom (Fin d → ℂ) (rhoLieHom d)

/-- V_d is a Lie module over ℂ. -/
noncomputable instance irrepLieModule (d : ℕ) :
    @LieModule ℂ sl2 (Fin d → ℂ) _ _ _ _ _ (irrepLieRingModule d) :=
  LieModule.compLieHom (Fin d → ℂ) (rhoLieHom d)

/-- V_d has the correct dimension. -/
theorem irrep_finrank (d : ℕ) [NeZero d] :
    Module.finrank ℂ (Fin d → ℂ) = d := by
  simp

/-- rhoLieHom maps sl2_h to rhoH. -/
private lemma rhoLieHom_sl2_h_eq (d : ℕ) : rhoLieHom d sl2_h = rhoH d := by
  have h00 : sl2_h.val 0 0 = 1 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h01 : sl2_h.val 0 1 = 0 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h10 : sl2_h.val 1 0 = 0 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have key : rhoLieHom d sl2_h =
    sl2_h.val 0 0 • rhoH d + sl2_h.val 0 1 • rhoE d +
      sl2_h.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp

/-- rhoLieHom maps sl2_e to rhoE. -/
private lemma rhoLieHom_sl2_e_eq (d : ℕ) : rhoLieHom d sl2_e = rhoE d := by
  have h00 : sl2_e.val 0 0 = 0 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : sl2_e.val 0 1 = 1 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : sl2_e.val 1 0 = 0 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : rhoLieHom d sl2_e =
    sl2_e.val 0 0 • rhoH d + sl2_e.val 0 1 • rhoE d +
      sl2_e.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp

/-- rhoLieHom maps sl2_f to rhoF. -/
private lemma rhoLieHom_sl2_f_eq (d : ℕ) : rhoLieHom d sl2_f = rhoF d := by
  have h00 : sl2_f.val 0 0 = 0 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : sl2_f.val 0 1 = 0 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : sl2_f.val 1 0 = 1 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : rhoLieHom d sl2_f =
    sl2_f.val 0 0 • rhoH d + sl2_f.val 0 1 • rhoE d +
      sl2_f.val 1 0 • rhoF d := rfl
  rw [key, h00, h01, h10]; simp

/-- Standard basis vector e_k in Fin d → ℂ. -/
private def e_basis (d : ℕ) (k : Fin d) : Fin d → ℂ := Pi.single k 1

private theorem e_basis_apply (d : ℕ) (k j : Fin d) :
    e_basis d k j = if j = k then 1 else 0 := by
  simp [e_basis, Pi.single_apply]

/-- V_d is irreducible as an sl(2)-module (for d ≥ 1). -/
theorem irrep_isIrreducible (d : ℕ) [NeZero d] :
    letI := irrepLieRingModule d
    letI := irrepLieModule d
    LieModule.IsIrreducible ℂ sl2 (Fin d → ℂ) := by
  letI := irrepLieRingModule d
  letI := irrepLieModule d
  apply LieModule.IsIrreducible.mk
  intro N hN
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push_neg at hN
  obtain ⟨w, hw_mem, hw_ne⟩ := hN
  -- Key connection: ⁅sl2_h, v⁆ k = (d-1-2k) * v k
  have lie_h_comp : ∀ (v : Fin d → ℂ) (k : Fin d),
      ((rhoLieHom d sl2_h) v) k = ((d : ℂ) - 1 - 2 * ↑(k : ℕ)) * v k := by
    intro v k; rw [rhoLieHom_sl2_h_eq]; rfl
  -- Helper: scalar-extract from N
  have smul_extract : ∀ (c : ℂ) (v : Fin d → ℂ), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h1 : c⁻¹ • (c • v) ∈ N := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  -- Suffices to get all basis vectors in N
  suffices basis_in_N : ∀ k : Fin d, e_basis d k ∈ N by
    rw [eq_top_iff]; intro v _
    have decomp : v = Finset.univ.sum (fun k : Fin d => v k • e_basis d k) := by
      ext j; simp [Finset.sum_apply, e_basis_apply]
    rw [decomp]
    refine Finset.sum_induction _
      (· ∈ (N : Set (Fin d → ℂ))) (fun a b ha hb => ?_) ?_
      (fun k _ => ?_)
    · exact N.add_mem ha hb
    · exact N.zero_mem
    · exact N.smul_mem _ (basis_in_N k)
  -- Step A: Extract one basis vector from N
  have extract : ∃ k : Fin d, e_basis d k ∈ N := by
    suffices ∀ (n : ℕ) (w : Fin d → ℂ), w ∈ N → w ≠ 0 →
        (Finset.univ.filter (fun k => w k ≠ 0)).card ≤ n →
        ∃ k : Fin d, e_basis d k ∈ N by
      exact this _ w hw_mem hw_ne le_rfl
    intro n
    induction n with
    | zero =>
      intro w _ hw_ne hn
      exfalso; apply hw_ne; ext k
      by_contra hk
      have : k ∈ Finset.univ.filter (fun k => w k ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      exact absurd (Finset.card_pos.mpr ⟨k, this⟩) (by omega)
    | succ n ih =>
      intro w hw_mem hw_ne hn
      by_cases hn1 : (Finset.univ.filter (fun k => w k ≠ 0)).card ≤ 1
      · -- At most one nonzero component: w = w(k) • e_k
        have hcard := Finset.card_le_one.mp hn1
        have hne : (Finset.univ.filter (fun k => w k ≠ 0)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro hempty
          apply hw_ne; ext k
          by_contra hk
          have : k ∈ (∅ : Finset (Fin d)) :=
            hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
          simp at this
        obtain ⟨k, hk_mem⟩ := hne
        have hk : k ∈ Finset.univ ∧ w k ≠ 0 := Finset.mem_filter.mp hk_mem
        refine ⟨k, ?_⟩
        have hw_eq : w = w k • e_basis d k := by
          ext j
          simp only [Pi.smul_apply, e_basis_apply, smul_eq_mul]
          by_cases hjk : j = k
          · subst hjk; simp
          · have : w j = 0 := by
              by_contra hj
              exact hjk (hcard j
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) k hk_mem)
            simp [this, hjk]
        rw [hw_eq] at hw_mem
        exact smul_extract _ _ hk.2 hw_mem
      · -- Multiple nonzero components: reduce using h-eigenvalue
        push_neg at hn1
        obtain ⟨j₁, hj₁_mem, j₂, hj₂_mem, hne⟩ :=
          Finset.one_lt_card.mp hn1
        have hj₁ := (Finset.mem_filter.mp hj₁_mem).2
        have hj₂ := (Finset.mem_filter.mp hj₂_mem).2
        let c : ℂ := (d : ℂ) - 1 - 2 * ↑(j₁ : ℕ)
        have hw'_mem :
            (fun i => ((rhoLieHom d sl2_h) w) i - c * w i) ∈ N := by
          change (rhoLieHom d sl2_h) w - c • w ∈ (N : Set _)
          exact N.sub_mem (N.lie_mem hw_mem) (N.smul_mem c hw_mem)
        have hw'_val : ∀ i : Fin d,
            ((rhoLieHom d sl2_h) w i - c * w i) =
            (2 * (↑(j₁ : ℕ) - ↑(i : ℕ))) * w i := by
          intro i; rw [lie_h_comp]; ring
        have hw'_ne : (fun i => (rhoLieHom d sl2_h) w i - c * w i) ≠ 0 := by
          intro h
          have := congr_fun h j₂
          rw [hw'_val] at this
          simp at this
          rcases this with h1 | h2
          · have : (j₁ : ℕ) = (j₂ : ℕ) := by exact_mod_cast sub_eq_zero.mp h1
            exact hne (Fin.ext this)
          · exact hj₂ h2
        have hw'_fewer :
            (Finset.univ.filter (fun k =>
              (rhoLieHom d sl2_h) w k - c * w k ≠ 0)).card ≤ n := by
          have hssub : (Finset.univ.filter (fun k =>
              (rhoLieHom d sl2_h) w k - c * w k ≠ 0)) ⊂
            (Finset.univ.filter (fun k => w k ≠ 0)) := by
            constructor
            · intro i hi
              rw [Finset.mem_filter] at hi ⊢
              refine ⟨Finset.mem_univ i, ?_⟩
              rw [hw'_val i] at hi
              exact (mul_ne_zero_iff.mp hi.2).2
            · intro hsub
              have hj₁_in := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j₁, hj₁⟩)
              rw [Finset.mem_filter] at hj₁_in
              have habs := hj₁_in.2
              rw [hw'_val] at habs
              simp at habs
          linarith [Finset.card_lt_card hssub]
        exact ih _ hw'_mem hw'_ne hw'_fewer
  obtain ⟨k₀, hk₀⟩ := extract
  -- Step B: Propagate from k₀ to all basis vectors using e and f
  -- step_down: rhoE(e_{m+1}) has coeff (m+1) at position m
  have step_down : ∀ (m : ℕ) (hm : m + 1 < d),
      e_basis d ⟨m + 1, by omega⟩ ∈ N →
      e_basis d ⟨m, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (rhoLieHom d sl2_e) (e_basis d ⟨m + 1, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (rhoLieHom d sl2_e) (e_basis d ⟨m + 1, by omega⟩) =
        (↑(m + 1) : ℂ) • e_basis d ⟨m, by omega⟩ := by
      rw [rhoLieHom_sl2_e_eq]
      ext k
      simp only [rhoE, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, e_basis, Pi.single_apply]
      by_cases hk : (k : ℕ) + 1 < d
      · simp only [hk, dite_true]
        by_cases hkm : (k : ℕ) = m
        · subst hkm; simp
        · have hne1 : ¬((k : ℕ) + 1 = m + 1) := by omega
          simp [Fin.ext_iff, hkm]
      · simp only [hk, dite_false, mul_zero]
        by_cases hkm : (k : ℕ) = m
        · exfalso; omega
        · simp [Fin.ext_iff, hkm]
    rw [lie_eq] at lie_in_N
    exact smul_extract _ _ (Nat.cast_ne_zero.mpr (by omega)) lie_in_N
  -- step_up: rhoF(e_m) has coeff (d-m-1) at position m+1
  have step_up : ∀ (m : ℕ) (hm : m + 1 < d),
      e_basis d ⟨m, by omega⟩ ∈ N →
      e_basis d ⟨m + 1, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (rhoLieHom d sl2_f) (e_basis d ⟨m, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (rhoLieHom d sl2_f) (e_basis d ⟨m, by omega⟩) =
        ((d : ℂ) - ↑(m + 1)) • e_basis d ⟨m + 1, by omega⟩ := by
      rw [rhoLieHom_sl2_f_eq]
      ext k
      simp only [rhoF, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, e_basis, Pi.single_apply]
      by_cases hk : 0 < (k : ℕ)
      · simp only [hk, dite_true]
        by_cases hkm : (k : ℕ) = m + 1
        · have hksub : (k : ℕ) - 1 = m := by omega
          have hkeq : k = ⟨m + 1, by omega⟩ := Fin.ext (by omega)
          simp [hkeq]
        · have : (k : ℕ) - 1 ≠ m := by omega
          simp [Fin.ext_iff, this, hkm]
      · simp only [hk, dite_false, mul_zero]
        push_neg at hk
        simp [Fin.ext_iff, show (k : ℕ) ≠ m + 1 from by omega]
    rw [lie_eq] at lie_in_N
    have hc : ((d : ℂ) - ↑(m + 1)) ≠ 0 := by
      rw [Ne, sub_eq_zero]; exact_mod_cast (by omega : d ≠ m + 1)
    exact smul_extract _ _ hc lie_in_N
  -- Get e_0 ∈ N by stepping down from k₀
  have hd_pos : 0 < d := NeZero.pos d
  have e0_mem : e_basis d ⟨0, hd_pos⟩ ∈ N := by
    suffices ∀ (m : ℕ) (hm : m < d),
        e_basis d ⟨m, hm⟩ ∈ N → e_basis d ⟨0, hd_pos⟩ ∈ N from
      this k₀.val k₀.isLt hk₀
    intro m hm
    induction m with
    | zero => exact id
    | succ m ihm => intro hmem; exact ihm (by omega) (step_down m (by omega) hmem)
  -- Get all basis vectors by stepping up from e_0
  intro k
  suffices ∀ (j : ℕ) (hj : j < d), e_basis d ⟨j, hj⟩ ∈ N from
    this k.val k.isLt
  intro j hj
  induction j with
  | zero => exact e0_mem
  | succ j ih => exact step_up j hj (ih (by omega))

end Etingof.Sl2Irrep
