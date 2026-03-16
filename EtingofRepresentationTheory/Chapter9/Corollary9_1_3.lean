import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Corollary 9.1.3: Lifting complete systems of orthogonal idempotents

A complete system of orthogonal idempotents in A/I (where I is a nilpotent ideal)
can be lifted to a complete system of orthogonal idempotents in A.

## Proof sketch

Use induction on the number of idempotents and Proposition 9.1.1.

## Implementation

This follows directly from Mathlib's `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`,
applied to the quotient ring homomorphism `Ideal.Quotient.mk I`.
-/

/-- Complete systems of orthogonal idempotents can be lifted through nilpotent ideals.
(Etingof Corollary 9.1.3)

Given a ring `A`, a nilpotent two-sided ideal `I`, and a complete system of orthogonal
idempotents `ebar` in `A/I`, there exists a complete system of orthogonal idempotents
`e` in `A` that lifts `ebar`. -/
theorem Etingof.lift_complete_orthogonal_idempotents {A : Type*} [Ring A]
    {I : Ideal A} [I.IsTwoSided] (hI : IsNilpotent I)
    {ι : Type*} [Fintype ι] {ebar : ι → A ⧸ I}
    (h_coi : CompleteOrthogonalIdempotents ebar) :
    ∃ e : ι → A, CompleteOrthogonalIdempotents e ∧
      ∀ i, Ideal.Quotient.mk I (e i) = ebar i := by
  obtain ⟨n, hn⟩ := hI
  have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk I), IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact ⟨n, by
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      exact Ideal.mem_bot.mp this⟩
  obtain ⟨e, he_coi, he_lift⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
      (Ideal.Quotient.mk I) hker h_coi (fun i => Ideal.Quotient.mk_surjective (ebar i))
  exact ⟨e, he_coi, fun i => congr_fun he_lift i⟩
