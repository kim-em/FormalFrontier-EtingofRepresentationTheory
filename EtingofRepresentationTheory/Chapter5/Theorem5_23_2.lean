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
    IsSemisimpleModule k Y := by
  sorry

/-- The coordinate ring of `GL_n(k)`: the polynomial ring `k[Xᵢⱼ, D]` where `D`
represents `1/det`. This models the algebra `R` of regular (polynomial) functions
on `GL_n(k)`. -/
noncomputable abbrev GLCoordinateRing (n : ℕ) (k : Type*) [Field k] :=
  MvPolynomial (GLCoordVars n) k

/-- A dominant weight for `GL_n` is a weakly decreasing sequence of integers
`(λ₁ ≥ λ₂ ≥ ⋯ ≥ λ_n)`. -/
def DominantWeight (n : ℕ) := { lam : Fin n → ℤ // Antitone lam }

/-- The irreducible algebraic representation of `GL_n(k)` with highest weight `λ`,
extended from `SchurModule` to integer weights via twisting by powers of the
determinant character. Returns the underlying `k`-module.
(See discussion after Definition 5.23.1.) -/
noncomputable def AlgIrrepGL (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type :=
  sorry

noncomputable instance AlgIrrepGL.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGL n lam k) := sorry

noncomputable instance AlgIrrepGL.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGL n lam k) := sorry

noncomputable instance AlgIrrepGL.finite (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module.Finite k (AlgIrrepGL n lam k) := sorry

/-- The contragredient (dual) representation `L*_λ`. -/
noncomputable def AlgIrrepGLDual (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type :=
  sorry

noncomputable instance AlgIrrepGLDual.addCommGroup (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (AlgIrrepGLDual n lam k) := sorry

noncomputable instance AlgIrrepGLDual.module (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (AlgIrrepGLDual n lam k) := sorry

/-- **Theorem 5.23.2 (ii)** (Peter-Weyl for GL(V)): The coordinate ring `R` of
`GL_n(k)`, as a representation of `GL_n(k) × GL_n(k)` via `(g,h) · φ(x) = φ(g⁻¹xh)`,
decomposes as `R ≅ ⊕_λ L*_λ ⊗ L_λ`, where the sum ranges over all dominant weights
`λ = (λ₁ ≥ ⋯ ≥ λ_n)` with `λᵢ ∈ ℤ`, and `L*_λ` is the contragredient of `L_λ`.

Stated as a `k`-linear isomorphism between the coordinate ring and the direct sum.
The equivariance with respect to the `GL_n × GL_n`-action is part of the proof
obligation.
(Etingof Theorem 5.23.2, part ii) -/
theorem Theorem5_23_2_ii
    (n : ℕ) :
    Nonempty (GLCoordinateRing n k ≃ₗ[k]
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k))) := by
  sorry

end Etingof
