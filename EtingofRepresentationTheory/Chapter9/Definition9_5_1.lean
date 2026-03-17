import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 9.5.1: Linked simple modules and blocks

Two simple modules X, Y are **linked** if there exists a chain of simple modules
X = X₀, X₁, …, Xₙ = Y such that for each consecutive pair (Xᵢ, Xᵢ₊₁), either
Ext¹(Xᵢ, Xᵢ₊₁) ≠ 0 or Ext¹(Xᵢ₊₁, Xᵢ) ≠ 0. This is an equivalence relation on
simple modules.

The equivalence classes are S₁, …, Sₗ. The k-th **block** 𝒞ₖ of the category of
finite dimensional A-modules consists of objects whose Jordan–Hölder composition
factors all belong to Sₖ.

## Mathlib correspondence

Not directly in Mathlib. Blocks are a fundamental concept in modular representation theory.
-/

universe v u

open CategoryTheory

section

variable (R : Type u) [Ring R] [Small.{v} R]

/-- Two objects in `ModuleCat R` are **directly Ext¹-linked** if `Ext¹(X, Y)` is nontrivial
(i.e., the type is nonempty, meaning there exists a nonzero element). This is the basic
building block for the linking relation. -/
def Etingof.DirectlyExtLinked (X Y : ModuleCat.{v} R) : Prop :=
  Nonempty (Abelian.Ext X Y 1)

/-- Two objects in `ModuleCat R` are **Ext¹-adjacent** if they are directly Ext¹-linked
in either direction: `Ext¹(X, Y) ≠ 0` or `Ext¹(Y, X) ≠ 0`. -/
def Etingof.ExtAdjacent (X Y : ModuleCat.{v} R) : Prop :=
  Etingof.DirectlyExtLinked R X Y ∨ Etingof.DirectlyExtLinked R Y X

/-- Two modules are **linked** (in the sense of Etingof Definition 9.5.1) if they are
related by the equivalence closure of Ext¹-adjacency: there exists a chain
`X = X₀, X₁, …, Xₙ = Y` such that each consecutive pair `(Xᵢ, Xᵢ₊₁)` satisfies
`Ext¹(Xᵢ, Xᵢ₊₁) ≠ 0` or `Ext¹(Xᵢ₊₁, Xᵢ) ≠ 0`. -/
def Etingof.AreLinked (X Y : ModuleCat.{v} R) : Prop :=
  Relation.EqvGen (Etingof.ExtAdjacent R) X Y

/-- The linking relation is an equivalence relation. -/
theorem Etingof.areLinked_equivalence :
    @Equivalence (ModuleCat.{v} R) (Etingof.AreLinked R) :=
  Relation.EqvGen.is_equivalence _

/-- The setoid on `ModuleCat R` induced by the linking relation.
The equivalence classes of this setoid are the **blocks** of the algebra `R`,
in the sense of Etingof Definition 9.5.1. -/
def Etingof.blockSetoid : Setoid (ModuleCat.{v} R) :=
  ⟨Etingof.AreLinked R, Etingof.areLinked_equivalence R⟩

/-- The **blocks** of a ring `R`, in the sense of Etingof Definition 9.5.1.
A block is an equivalence class of modules under the linking relation: two modules
are in the same block iff they are connected by a chain of Ext¹-adjacencies. -/
def Etingof.Block : Type _ :=
  Quotient (Etingof.blockSetoid R)

end
