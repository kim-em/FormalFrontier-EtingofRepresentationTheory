import Mathlib.Algebra.Homology.HomologySequence

/-!
# Definition 7.8.6: Connecting Homomorphism and Long Exact Sequence of Cohomology

Given a short exact sequence of complexes 0 → A• → B• → C• → 0, the **connecting
homomorphism** c_i : H^i(C•) → H^{i+1}(A•) fits into the **long exact sequence
of cohomology**:

⋯ → H^i(A•) → H^i(B•) → H^i(C•) →^{c_i} H^{i+1}(A•) → ⋯

## Mathlib correspondence

The connecting homomorphism is `CategoryTheory.ShortComplex.ShortExact.δ` in Mathlib,
constructed via the snake lemma. The long exact sequence is witnessed by three exactness
lemmas: `homology_exact₁`, `homology_exact₂`, and `homology_exact₃`.
-/

open CategoryTheory

/-- The connecting homomorphism in the long exact sequence of cohomology,
in the sense of Etingof Definition 7.8.6.

Given a short exact sequence S of homological complexes over an abelian category,
with consecutive indices i and j, this is the map H^i(S.X₃) → H^j(S.X₁)
constructed via the snake lemma. -/
noncomputable abbrev Etingof.connectingHomomorphism
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- The long exact sequence of cohomology: exactness at the first position.
Given a short exact sequence S of complexes and the connecting homomorphism
δ : H^i(C•) → H^j(A•), the sequence H^i(C•) → H^j(A•) → H^j(B•) is exact. -/
theorem Etingof.long_exact_seq_exact₁
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  hS.homology_exact₁ i j hij

/-- The long exact sequence of cohomology: exactness at the second position.
The sequence H^i(A•) → H^i(B•) → H^i(C•) is exact. -/
theorem Etingof.long_exact_seq_exact₂
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  hS.homology_exact₂ i

/-- The long exact sequence of cohomology: exactness at the third position.
The sequence H^i(B•) → H^i(C•) → H^j(A•) is exact. -/
theorem Etingof.long_exact_seq_exact₃
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  hS.homology_exact₃ i j hij
