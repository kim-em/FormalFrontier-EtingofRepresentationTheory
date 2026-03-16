# References: Existence of filtration with irreducible successive quotients

## External Dependencies

- **Rings and ideals: definition of rings, two-sided ideals, quotient rings, nilpotent ideals, Jacobson radical** (undergraduate_prerequisite)
  Mathlib (exact): `Ring`, `Ideal`, `Ideal.Quotient`, `IsNilpotent`, `Ideal.jacobson`
  Complete ring theory. `IsNilpotent` for elements; nilpotent ideals expressible as `∀ x ∈ I, IsNilpotent x` or via `I ^ n = ⊥`. Jacobson radical via `Ideal.jacobson`.
- **Nilpotent ideals and nilpotency: a nilpotent ideal I satisfies I^n = 0 for some n; properties of nilpotent elements in algebras** (folklore)
  Mathlib (partial): `IsNilpotent`, `Ideal.jacobson`
  `IsNilpotent` for elements. Nilpotent ideals can be expressed as `I ^ n = ⊥`. The Jacobson radical contains all nilpotent ideals. Some connecting lemmas may need to be proved.
  External source [natural_language]: Lam, 'A First Course in Noncommutative Rings' — Chapter 2
