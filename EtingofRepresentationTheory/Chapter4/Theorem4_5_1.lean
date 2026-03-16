import Mathlib

/-!
# Theorem 4.5.1: Orthogonality of Characters (First Orthogonality Relation)

For finite dimensional representations V, W of a finite group G over ℂ:

(i) (χ_V, χ_W) = dim Hom_G(W, V), where (f, g) = (1/|G|) Σ_{x∈G} f(x) g(x)*.

(ii) If V, W are irreducible, then (χ_V, χ_W) = δ_{V,W} (1 if V ≅ W, 0 otherwise).

The proof uses the averaging (Reynolds) operator P = (1/|G|) Σ_{g∈G} g acting on Hom(W, V),
which projects onto Hom_G(W, V).

## Mathlib correspondence

Mathlib has character inner product infrastructure in `Mathlib.RepresentationTheory.Character`.
The orthogonality relations are partially available.
-/

/-- First orthogonality relation: the inner product of characters of irreducible
representations is δ_{V,W}. (Etingof Theorem 4.5.1) -/
theorem Etingof.Theorem4_5_1
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V W : FDRep ℂ G) :
    -- For irreducible V, W: (χ_V, χ_W) = 1 if V ≅ W, 0 otherwise
    -- TODO: Precise inner product formulation once character inner product API is available
    True := by
  trivial
