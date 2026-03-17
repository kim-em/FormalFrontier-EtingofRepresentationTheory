import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_7_1

/-!
# Lemma 6.7.2: Coxeter Element Produces Negative Coefficients

Let β = Σᵢ kᵢ αᵢ with kᵢ ≥ 0 (not all zero). Then there exists N ∈ ℕ such that
cᴺβ has at least one strictly negative coefficient.

The proof shows that 1 is not an eigenvalue of the Coxeter element c. Since
c ∈ W (a finite group), cᴹ = 1 for some M, so 1 + c + c² + ⋯ + cᴹ⁻¹ = 0
as operators on ℝⁿ. If cv = v, then sᵢv = v for all i, implying B(v, αᵢ) = 0
for all i, contradicting nondegeneracy of B.

## Mathlib correspondence

Requires Coxeter groups, simple reflections, the bilinear form B, and its
nondegeneracy for Dynkin diagrams. Mathlib has Coxeter systems but the specific
eigenvalue argument needs custom development.

## Formalization note

The Coxeter element c acts on ℤⁿ as the composition of simple reflections
sₙ ∘ ⋯ ∘ s₁. Iterating c means composing with itself N times. We formalize
this using the existing `simpleReflection` (Definition 6.4.10) and
`coxeterElement` (Definition 6.7.1) infrastructure.
-/

/-- The action of the Coxeter element on a vector in ℤⁿ. The Coxeter element
c = sₙ ∘ ⋯ ∘ s₁ acts by composing all simple reflections in order, where
sᵢ is the simple reflection associated to the Cartan matrix A = 2·Id - adj. -/
def Etingof.coxeterAction (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  let A := Etingof.cartanMatrix n adj
  (List.ofFn (fun i : Fin n => Etingof.simpleReflection n A i)).foldr (· ∘ ·) id v

/-- Iterated action of the Coxeter element: c^N applied to a vector. -/
def Etingof.coxeterActionIter (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (N : ℕ) (v : Fin n → ℤ) : Fin n → ℤ :=
  (Etingof.coxeterAction n adj)^[N] v

/-- For a positive linear combination of simple roots (not all zero), some power of
the Coxeter element produces a vector with a negative coefficient.

Specifically: if β ∈ ℤⁿ with all coordinates nonneg and β ≠ 0, then there
exists N such that c^N(β) has at least one strictly negative coordinate, where
c is the Coxeter element (product of all simple reflections) associated to
the Dynkin diagram.
(Etingof Lemma 6.7.2) -/
theorem Etingof.Lemma6_7_2
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj)
    (β : Fin n → ℤ)
    (hβ_nonneg : ∀ i, 0 ≤ β i)
    (hβ_nonzero : β ≠ 0) :
    ∃ N : ℕ, ∃ i : Fin n,
      Etingof.coxeterActionIter n adj N β i < 0 :=
  sorry
