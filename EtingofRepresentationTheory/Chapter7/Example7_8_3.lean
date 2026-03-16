import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Example 7.8.3: Split Exact Sequences

The sequence 0 → X → X ⊕ Z → Z → 0 with the obvious morphisms is a short exact
sequence. Such a sequence is called **split**. It corresponds to the trivial
extension of Z by X.

## Mathlib correspondence

Split exact sequences are available in Mathlib. `CategoryTheory.ShortComplex.Splitting`
captures the notion of a splitting of a short complex.
-/

open CategoryTheory CategoryTheory.Limits

/-- A split short exact sequence: 0 → X → X ⊕ Z → Z → 0.
(Etingof Example 7.8.3)

In any preadditive category with binary biproducts and kernels/cokernels,
the short complex `X --inl→ X ⊞ Z --snd→ Z` admits a splitting
(and is therefore short exact). -/
noncomputable def Etingof.split_exact_sequence
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [HasKernels C] [HasCokernels C]
    (X Z : C) : (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) biprod.snd (by simp)).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Z).shortExact
