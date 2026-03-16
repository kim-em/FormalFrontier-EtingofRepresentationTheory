import Mathlib.Combinatorics.Quiver.Basic

/-!
# Example 2.8.2: A Quiver

An example of a quiver with 4 vertices and 3 arrows:

```
• → • ← •
↑
•
```

## Mathlib correspondence

Mathlib has `Quiver` as a class. Concrete quiver examples can be constructed.
-/

/-- A concrete quiver with 4 vertices and 3 arrows. (Etingof Example 2.8.2) -/
instance Etingof.Example_2_8_2 : Quiver (Fin 4) where
  Hom a b :=
    -- Arrow 0 → 1, Arrow 2 → 1, Arrow 3 → 0
    if a = 0 ∧ b = 1 then Unit
    else if a = 2 ∧ b = 1 then Unit
    else if a = 3 ∧ b = 0 then Unit
    else Empty
