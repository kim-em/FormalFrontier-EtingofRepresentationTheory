import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Combinatorics.Quiver.Basic

/-!
# Definition 2.8.3: Representation of a Quiver

A **representation of a quiver** Q is an assignment to each vertex i ∈ I of a
vector space Vᵢ and to each edge h ∈ E of a linear map xₕ : V_{h'} → V_{h''}.

## Mathlib correspondence (partial)

Quiver representations can be modeled as functors from the free category on the quiver
to ModuleCat k. We define it directly as a bundled structure.
-/

/-- A representation of a quiver over a commutative semiring k,
in the sense of Etingof Definition 2.8.3.
Assigns a k-module to each vertex and a k-linear map to each arrow. -/
structure Etingof.QuiverRepresentation (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] where
  /-- The underlying type family -/
  obj : Q → Type*
  [instAddCommMonoid : ∀ v, AddCommMonoid (obj v)]
  [instModule : ∀ v, Module k (obj v)]
  /-- The linear map assigned to each arrow -/
  mapLinear : ∀ {v w : Q}, (v ⟶ w) → obj v →ₗ[k] obj w

attribute [instance] Etingof.QuiverRepresentation.instAddCommMonoid
attribute [instance] Etingof.QuiverRepresentation.instModule
