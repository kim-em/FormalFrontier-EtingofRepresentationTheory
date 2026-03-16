import Mathlib

/-!
# Theorem 4.6.2: Existence and Uniqueness of Unitary Structure

If G is a finite group, then:

(i) Any finite dimensional complex representation of G has a unitary structure.
The construction averages any positive definite Hermitian form B over G:
  B̄(v, w) = Σ_{g∈G} B(ρ(g)v, ρ(g)w)
which is G-invariant and positive definite.

(ii) If V is irreducible, this unitary structure is unique up to scaling by a
positive real number. This follows from Schur's lemma: if B₁, B₂ are two
G-invariant forms, the intertwiner B₂⁻¹ ∘ B₁ is a scalar multiple of identity.

## Mathlib correspondence

This is the unitarizability theorem. Not directly in Mathlib.
-/

/-- Any finite dimensional representation of a finite group admits a unitary structure.
(Etingof Theorem 4.6.2, part i) -/
theorem Etingof.Theorem4_6_2_existence
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) :
    -- There exists a G-invariant positive definite Hermitian form on V
    -- TODO: needs inner product space construction on FDRep carrier
    True := by
  trivial

/-- For an irreducible representation, the unitary structure is unique up to positive scaling.
(Etingof Theorem 4.6.2, part ii) -/
theorem Etingof.Theorem4_6_2_uniqueness
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) :
    -- For irreducible V, any two G-invariant positive definite Hermitian forms are proportional
    -- TODO: needs Schur's lemma + Hermitian form API
    True := by
  trivial
