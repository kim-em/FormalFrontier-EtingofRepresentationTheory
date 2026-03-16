import Mathlib

/-!
# Theorem 4.2.1: Characters Form a Basis of Class Functions

If k is algebraically closed and char(k) does not divide |G|, the characters of irreducible
representations of G form a basis of the space Fc(G, k) of class functions on G.

We state this as: every class function (a function G → k constant on conjugacy classes)
lies in the k-linear span of characters of simple (irreducible) FDRep objects.
Linear independence of distinct irreducible characters follows from orthogonality
(Theorem 4.5.1 / `FDRep.char_orthonormal`).

## Mathlib correspondence

Mathlib has `FDRep.character`, `FDRep.char_conj` (characters are class functions),
and `FDRep.char_orthonormal` (orthonormality). The spanning/basis property is not yet
in Mathlib.

## Proof strategy

We prove that any class function orthogonal to all irreducible characters must be zero.
This uses the group algebra k[G]: such a function corresponds to a central element that
acts by zero on every simple module (via Schur + trace + dim invertible), hence is zero
by semisimplicity (Maschke). The spanning property follows from completeness + the
`Submodule.mem_span` characterization.
-/

open FDRep CategoryTheory Finset

universe u

namespace Etingof.Theorem4_2_1_aux

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [Invertible (Fintype.card G : k)]

/-! ### Step 1: Group algebra element from a function -/

/-- The group algebra element corresponding to a function f : G → k,
  defined as α = ∑_g f(g) · g⁻¹ in k[G]. -/
noncomputable def toGroupAlgebra (f : G → k) : MonoidAlgebra k G :=
  ∑ g : G, MonoidAlgebra.single g⁻¹ (f g)

/-- The trace of the representation action of `toGroupAlgebra f` on V equals
  `∑ g, f g * V.character g⁻¹`. -/
private lemma trace_toGroupAlgebra_action (f : G → k) (V : FDRep k G) :
    LinearMap.trace k V (Representation.asAlgebraHom V.ρ (toGroupAlgebra f)) =
      ∑ g : G, f g * V.character g⁻¹ := by
  simp only [toGroupAlgebra, map_sum, Representation.asAlgebraHom_single]
  congr 1; ext g
  rw [LinearMap.map_smul, smul_eq_mul, FDRep.character]

/-- `toGroupAlgebra` is injective: if `toGroupAlgebra f = 0` then `f = 0`. -/
private lemma toGroupAlgebra_injective (f : G → k) (h : toGroupAlgebra f = 0) : f = 0 := by
  ext g
  simp only [Pi.zero_apply]
  -- Evaluate toGroupAlgebra f at g⁻¹: this picks out f(g) via Finsupp.single
  have heval : (toGroupAlgebra f) g⁻¹ = 0 := by simp [h]
  simp only [toGroupAlgebra] at heval
  rw [show (∑ x : G, MonoidAlgebra.single x⁻¹ (f x)) g⁻¹ =
    ∑ x : G, (MonoidAlgebra.single x⁻¹ (f x) : G →₀ k) g⁻¹ from
    Finsupp.finset_sum_apply _ _ _] at heval
  rw [Finset.sum_eq_single g] at heval
  · simpa [Finsupp.single_apply] using heval
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (show b⁻¹ ≠ g⁻¹ from fun h => hb (inv_injective h))]
  · intro h; exact absurd (Finset.mem_univ g) h

/-! ### Step 2: Completeness — key infrastructure lemma

The following lemma is the core of the proof. It states that a class function
orthogonal to all irreducible characters must be zero. The proof goes via the
group algebra: the corresponding central element α acts by zero on all simple
k[G]-modules (Schur's lemma + trace = 0 + dim invertible), hence α = 0 by
semisimplicity (Maschke's theorem).

This requires connecting FDRep simple objects to simple k[G]-modules, which
uses the equivalence `Rep.equivalenceModuleMonoidAlgebra` and the fact that
categorical equivalences preserve simplicity.
-/

/-- **Character completeness**: A class function orthogonal to all irreducible
characters is zero. This is the key step in proving that irreducible characters
span the space of class functions. -/
private lemma classFunction_eq_zero_of_orthogonal_simples
    (f : G → k) (hf_class : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0 := by
  apply toGroupAlgebra_injective
  set α := toGroupAlgebra f
  -- Step: α acts by zero on each simple k[G]-module.
  -- For any simple FDRep V:
  -- - ρ_V(α) is a G-equivariant endomorphism of V
  -- - End_G(V) is 1-dimensional (Schur over algebraically closed k)
  -- - So ρ_V(α) = c · id for some scalar c
  -- - trace(ρ_V(α)) = c · dim(V) = ∑_g f(g) χ_V(g⁻¹) = 0
  -- - dim(V) > 0 and invertible in k, so c = 0
  -- - Hence ρ_V(α) = 0
  --
  -- Step: α = 0 by semisimplicity
  -- - α is central in k[G] (from f being a class function)
  -- - Left multiplication by α is k[G]-linear (centrality)
  -- - ker(L_α) contains every simple submodule of k[G]
  -- - sSup of simples = ⊤ (k[G] is semisimple by Maschke)
  -- - So L_α = 0, hence α = L_α(1) = 0
  sorry

end Etingof.Theorem4_2_1_aux

open Etingof.Theorem4_2_1_aux in
/-- Characters of irreducible representations span the space of class functions:
every function G → k that is constant on conjugacy classes is a k-linear combination
of characters of simple (irreducible) representations. (Etingof Theorem 4.2.1) -/
theorem Etingof.Theorem4_2_1
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) := by
  classical
  -- Strategy: show that any submodule containing all simple characters must contain f.
  -- If f ∉ span(S), there exists a linear functional vanishing on S but not on f.
  -- But any such functional defines a "dual" class function orthogonal to all simples,
  -- which must be zero by the completeness lemma — contradiction.
  rw [Submodule.mem_span]
  intro p hp
  -- We use the completeness lemma: the "projection" of f onto the orthogonal complement
  -- of span(S) in the class function space is zero.
  -- This means f is already in span(S), hence in any submodule containing S.
  sorry
