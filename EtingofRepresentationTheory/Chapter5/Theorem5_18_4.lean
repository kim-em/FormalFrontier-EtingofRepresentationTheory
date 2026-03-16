import Mathlib

/-!
# Theorem 5.18.4: Schur-Weyl Duality

The fundamental Schur-Weyl duality theorem for V^⊗n:

(i) Let A = Im(k[S_n] → End(V^⊗n)) and B = Im(U(gl(V)) → End(V^⊗n)).
    Then A = End_B(V^⊗n) and B = End_A(V^⊗n).

(ii) Both A and B are semisimple, and V^⊗n is a semisimple gl(V)-module.

(iii) As an (A ⊗ B)-module:
      V^⊗n ≅ ⊕_λ V_λ ⊗ L_λ
      where V_λ ranges over Specht modules of S_n and L_λ are the
      corresponding irreducible polynomial representations of GL(V).

## Mathlib correspondence

Schur-Weyl duality is a deep theorem connecting representation theory of S_n
and GL(V). This requires tensor power modules, the double centralizer theorem,
and the classification of polynomial representations.
-/

/-- Schur-Weyl duality: the images of k[S_n] and U(gl(V)) in End(V^⊗n)
are mutual centralizers. (Etingof Theorem 5.18.4, part i) -/
theorem Etingof.Theorem5_18_4_centralizers
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- Im(k[S_n]) and Im(U(gl(V))) are mutual centralizers in End(V^⊗n)
    (sorry : Prop) := by
  sorry

/-- Schur-Weyl duality: V^⊗n is a semisimple gl(V)-module.
(Etingof Theorem 5.18.4, part ii) -/
theorem Etingof.Theorem5_18_4_semisimple
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- V^⊗n is semisimple as a gl(V)-module
    (sorry : Prop) := by
  sorry

/-- Schur-Weyl duality: V^⊗n ≅ ⊕_λ V_λ ⊗ L_λ.
(Etingof Theorem 5.18.4, part iii) -/
theorem Etingof.Theorem5_18_4_decomposition
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- V^⊗n ≅ ⊕_λ V_λ ⊗ L_λ as (k[S_n] ⊗ U(gl(V)))-module
    (sorry : Prop) := by
  sorry
