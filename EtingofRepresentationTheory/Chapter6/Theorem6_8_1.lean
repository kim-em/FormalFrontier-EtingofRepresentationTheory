import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_5
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5

/-!
# Theorem 6.8.1: Reaching Simple Roots via Reflection Functors

There exists m ∈ ℕ such that d(V⁽ᵐ⁾) = αₚ for some vertex p, where V⁽ⁱ⁾ is the
sequence obtained by repeatedly applying reflection functors.

The proof: if V⁽ⁱ⁾ is surjective at the appropriate vertex k, then
d(V⁽ⁱ⁺¹⁾) = sₖ d(V⁽ⁱ⁾). By Lemma 6.7.2, this cannot continue indefinitely
(dimension vectors must remain non-negative). When it stops, by Proposition 6.6.5,
d(V⁽ⁱ⁾) = αₚ for some p.

This is the key technical step toward Gabriel's theorem.

## Mathlib correspondence

Requires the full infrastructure of reflection functors (Def 6.6.3-4),
dimension vectors, Propositions 6.6.5-6.6.8, and Lemma 6.7.2.
Not in Mathlib.
-/

/-- Iterated application of simple reflections to a vector. Given a list of vertex
indices, applies the corresponding simple reflections in order. -/
def Etingof.iteratedSimpleReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (vertices : List (Fin n)) (v : Fin n → ℤ) : Fin n → ℤ :=
  vertices.foldl (fun d i => Etingof.simpleReflection n A i d) v

/-- For any indecomposable representation V of a Dynkin quiver, repeated application
of reflection functors eventually produces a representation whose dimension vector
is a simple root αₚ.

Concretely: there exists a list of vertex indices [i₁, …, iₘ] and a vertex p
such that sᵢₘ ⋯ sᵢ₁(d(V)) = αₚ, where sᵢ are simple reflections associated
to the Cartan matrix A = 2·Id - adj.
(Etingof Theorem 6.8.1) -/
theorem Etingof.Theorem6_8_1
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((Etingof.cartanMatrix n adj).mulVec d) = 2) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      Etingof.iteratedSimpleReflection n (Etingof.cartanMatrix n adj) vertices d =
        Etingof.simpleRoot n p :=
  sorry
