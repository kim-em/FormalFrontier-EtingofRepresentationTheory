import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_3_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Definition6_5_1

/-!
# Example 6.8.5: Reflection Functors on D₄

Demonstrates reflection functors on the D₄ quiver with all arrows pointing towards
vertex 4 (the central node).

Starting with the 1-dimensional representation V_{α₄} at vertex 4:
- Apply F⁻₃ F⁻₂ F⁻₁ to get V_{α₁+α₂+α₃+α₄}
- Apply F⁻₄ to get V_{α₁+α₂+α₃+2α₄}

The final representation is the inclusion of three lines into the plane, which is
the most complicated indecomposable representation of D₄.

## Mathlib correspondence

D₄ is available as `DynkinDiagram.D 4` in Mathlib. The specific reflection
functor computations require the custom functor infrastructure from Definitions
6.6.3-6.6.4.

## Formalization approach

We state the example as a theorem about dimension vectors: starting from the
simple representation at vertex 4 (dimension vector α₄ = (0,0,0,1) in the
(V₁,V₂,V₃,V₄) basis), successive applications of reflection functors F⁻ᵢ
transform the dimension vector according to the simple reflection formula
sᵢ(d)_j = d_j - A_ij · d_i. We state the concrete computation results:
  F⁻₁ F⁻₂ F⁻₃ (α₄) = α₁ + α₂ + α₃ + α₄ = (1,1,1,1)
  F⁻₄ F⁻₁ F⁻₂ F⁻₃ (α₄) = α₁ + α₂ + α₃ + 2α₄ = (1,1,1,2)
and that the final dimension vector (1,1,1,2) corresponds to an indecomposable
(being the maximal positive root of D₄).
-/

/-- The adjacency matrix of the D₄ graph: vertex 4 (index 3) is connected to
vertices 1, 2, 3 (indices 0, 1, 2). -/
def Etingof.D₄_adj : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 0, 1;
     0, 0, 0, 1;
     1, 1, 1, 0]

/-- The Cartan matrix of D₄: A = 2·Id - adj. -/
def Etingof.D₄_cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 0, 0, -1;
     0, 2, 0, -1;
     0, 0, 2, -1;
     -1, -1, -1, 2]

/-- The simple reflection sᵢ on dimension vectors for the D₄ Cartan matrix:
sᵢ(x)_j = x_j for j ≠ i, sᵢ(x)_i = x_i - Σ_k A_{ik} x_k.
Equivalently, sᵢ(x) = x - (Aᵢ · x) eᵢ where Aᵢ is the i-th row of A. -/
def Etingof.D₄_simpleReflection (i : Fin 4) (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun j => if j = i then x i - Finset.univ.sum (fun k => Etingof.D₄_cartan i k * x k)
           else x j

/-- The dimension vector α₄ = (0,0,0,1): the simple root at vertex 4. -/
def Etingof.D₄_α₄ : Fin 4 → ℤ := ![0, 0, 0, 1]

/-- **Example 6.8.5, Part 1 (Etingof)**: Applying the sequence of simple reflections
s₁, s₂, s₃ (corresponding to reflection functors F⁻₁, F⁻₂, F⁻₃) to the dimension
vector α₄ = (0,0,0,1) yields the dimension vector (1,1,1,1) = α₁+α₂+α₃+α₄. -/
theorem Etingof.Example6_8_5_part1 :
    Etingof.D₄_simpleReflection 0
      (Etingof.D₄_simpleReflection 1
        (Etingof.D₄_simpleReflection 2 Etingof.D₄_α₄)) =
    ![1, 1, 1, 1] := by
  decide

/-- **Example 6.8.5, Part 2 (Etingof)**: Further applying the simple reflection s₄
(corresponding to reflection functor F⁻₄) to the dimension vector (1,1,1,1) yields
the dimension vector (1,1,1,2) = α₁+α₂+α₃+2α₄, the maximal positive root of D₄. -/
theorem Etingof.Example6_8_5_part2 :
    Etingof.D₄_simpleReflection 3
      (Etingof.D₄_simpleReflection 0
        (Etingof.D₄_simpleReflection 1
          (Etingof.D₄_simpleReflection 2 Etingof.D₄_α₄))) =
    ![1, 1, 1, 2] := by
  decide

/-- **Example 6.8.5, Part 3 (Etingof)**: The final dimension vector (1,1,1,2) is the
dimension vector of the maximal indecomposable representation of D₄ — the inclusion
of three lines into the plane. It corresponds to (dim V₁, dim V₂, dim V₃, dim V) =
(1,1,1,2) in D₄Rep notation, which is (2,1,1,1) = (center, arm₁, arm₂, arm₃).

In the D₄Rep convention from Example 6.3.1, the center has dimension 2 and
each arm has dimension 1. -/
theorem Etingof.Example6_8_5_maximal_indecomposable :
    (2, 1, 1, 1) ∈ D₄_indecomposable_dimVectors := by
  decide
