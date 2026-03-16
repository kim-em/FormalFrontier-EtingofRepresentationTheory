import Mathlib

/-!
# Infrastructure: Wedderburn-Artin Decomposition for Group Algebras

This file connects Mathlib's Wedderburn-Artin theorem to the representation theory
of finite groups. For a finite group G over an algebraically closed field k with
char(k) ∤ |G|, we establish:

1. `MonoidAlgebra k G` is a finite-dimensional semisimple k-algebra
2. By Wedderburn-Artin, `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`
3. The dimension formula `|G| = Σ i, (d i)²`
4. The number of components `n` corresponds to the number of isomorphism classes
   of simple `FDRep k G` objects

## References

- Etingof, *Introduction to Representation Theory*, Theorem 4.1.1
- Mathlib: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
- Mathlib: `Rep.equivalenceModuleMonoidAlgebra`
-/

open CategoryTheory

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

/-! ### Finite-dimensionality and semisimplicity of k[G] -/

omit [Fintype G] in
noncomputable instance MonoidAlgebra.instFiniteDimensional [Finite G] :
    FiniteDimensional k (MonoidAlgebra k G) :=
  inferInstance

omit [Fintype G] in
instance MonoidAlgebra.instIsSemisimpleRing [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

/-! ### Wedderburn-Artin decomposition -/

omit [Fintype G] in
/-- The Wedderburn-Artin decomposition of `k[G]`: there exist `n` matrix blocks of sizes
`d i` such that `k[G] ≃ₐ[k] Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`.
This is a direct application of `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`. -/
theorem MonoidAlgebra.wedderburnArtin [Finite G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    (F := k) (R := MonoidAlgebra k G)

/-! ### IrrepDecomp structure -/

/-- Bundled Wedderburn-Artin decomposition data for the group algebra `k[G]`.
Packages the number of irreducible representations `n`, their dimensions `d`,
and the algebra isomorphism. -/
structure IrrepDecomp (k G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] where
  /-- Number of isomorphism classes of irreducible representations -/
  n : ℕ
  /-- Dimensions of the irreducible representations -/
  d : Fin n → ℕ
  /-- Each dimension is positive -/
  d_pos : ∀ i, NeZero (d i)
  /-- The Wedderburn-Artin algebra isomorphism -/
  iso : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k

/-- Existence of the irreducible decomposition. -/
noncomputable def IrrepDecomp.mk' [NeZero (Nat.card G : k)] :
    IrrepDecomp k G := by
  choose n d hd he using MonoidAlgebra.wedderburnArtin (k := k) (G := G)
  exact ⟨n, d, hd, he.some⟩

/-! ### Dimension formula -/

omit [IsAlgClosed k] [Group G] in
/-- The dimension of `k[G]` equals `|G|`. -/
theorem MonoidAlgebra.finrank_eq_card :
    Module.finrank k (MonoidAlgebra k G) = Fintype.card G := by
  change Module.finrank k (G →₀ k) = _
  simp

omit [IsAlgClosed k] [Group G] [Fintype G] in
/-- The dimension of a product of matrix algebras is the sum of squares of the sizes. -/
theorem finrank_pi_matrix (n : ℕ) (d : Fin n → ℕ) :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) =
      ∑ i, (d i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  congr 1
  ext i
  simp [Module.finrank_matrix, Fintype.card_fin, sq]

/-- **Sum-of-squares formula**: `|G| = Σ i, (d i)²` where `d i` are the dimensions of the
irreducible representations of G. This is the key dimension identity from Theorem 4.1.1(ii). -/
theorem IrrepDecomp.sum_sq_eq_card [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∑ i, (D.d i) ^ 2 = Fintype.card G := by
  have hfr := MonoidAlgebra.finrank_eq_card (k := k) (G := G)
  have hiso := D.iso.toLinearEquiv.finrank_eq
  rw [hfr] at hiso
  rw [finrank_pi_matrix] at hiso
  omega

/-! ### Connection to FDRep -/

/-- The number of Wedderburn-Artin components equals the number of isomorphism classes
of simple `FDRep k G` objects. This is a key structural result connecting the algebraic
decomposition to the representation-theoretic classification.

The proof requires establishing that simple `MonoidAlgebra k G`-modules correspond
bijectively to simple objects in `FDRep k G`. Mathlib provides the equivalence
`Rep.equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat k[G]` but the finite-dimensional
restriction `FDRep k G ≌ FGModuleCat k[G]` is not yet formalized. -/
theorem IrrepDecomp.n_eq_card_simples [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    ∃ (V : Fin D.n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) := by
  sorry

/-- Each dimension `d i` in the Wedderburn-Artin decomposition equals the
`Module.finrank k` of the corresponding irreducible representation. -/
theorem IrrepDecomp.d_eq_finrank [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∀ i, D.d i = Module.finrank k (V i) := by
  sorry
