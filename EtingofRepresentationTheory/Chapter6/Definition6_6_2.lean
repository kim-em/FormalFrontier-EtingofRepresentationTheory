import Mathlib.Combinatorics.Quiver.Basic

/-!
# Definition 6.6.2: Reversed Quiver at a Vertex

Given a quiver Q and a vertex i, Q̄ᵢ is the quiver obtained from Q
by reversing all arrows incident to i (i.e., arrows where exactly one endpoint is i).

## Mathlib correspondence

Mathlib has `Quiver.reverse` which reverses ALL edges, but not vertex-local reversal.
This requires a custom definition that selectively reverses edges at a single vertex.
-/

/-- The type of arrows in the quiver obtained by reversing all arrows incident to vertex `i`.
For arrows not touching `i`, the type is unchanged. For arrows from `i` to `b` (with `b ≠ i`),
the type is `Hom_Q(b, i)` (reversed). For arrows from `a` to `i` (with `a ≠ i`),
the type is `Hom_Q(i, a)` (reversed). Self-loops at `i` are unchanged. -/
def Etingof.ReversedAtVertexHom (V : Type*) [DecidableEq V] [Quiver V] (i : V)
    (a b : V) : Type _ :=
  if a = i then
    if b = i then (a ⟶ b)  -- self-loop at i: unchanged
    else (b ⟶ i)            -- arrow from i to b: was b→i in Q
  else
    if b = i then (i ⟶ a)   -- arrow from a to i: was i→a in Q
    else (a ⟶ b)             -- neither endpoint is i: unchanged

/-- The quiver obtained by reversing all arrows incident to vertex `i`.
For a sink, this reverses all incoming arrows; for a source, all outgoing arrows.
(Etingof Definition 6.6.2) -/
noncomputable def Etingof.reversedAtVertex
    (V : Type*) [DecidableEq V] [Quiver V] (i : V) : Quiver V :=
  ⟨fun a b => Etingof.ReversedAtVertexHom V i a b⟩
