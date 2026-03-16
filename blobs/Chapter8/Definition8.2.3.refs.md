# References: Tor functors

## Mathlib Coverage (partial)

- `Tor`

Mathlib has `Tor` in `Mathlib.Algebra.Homology.DerivedCategory.Basic` but the API may be limited. The derived functor construction exists but concrete Tor computations may need work.

## External Sources (definition gap)

- **[natural_language]** Weibel, 'An Introduction to Homological Algebra' — Chapter 3
  Tor as derived functor of tensor product; long exact sequences; explicit computations
- **[natural_language]** Rotman, 'An Introduction to Homological Algebra' — Chapter 7
  Accessible treatment with detailed proofs of Tor properties

## External Dependencies

- **Ext functors: definition as derived functors of Hom, long exact sequence in Ext, Ext^1 classifies extensions** (external_result)
  Mathlib (partial): `Ext`, `CategoryTheory.ProjectiveResolution`
  `Ext` is defined as a functor in Mathlib via projective resolutions. The long exact sequence in Ext exists. The classification of extensions by Ext^1 may not be fully stated.
  External source [natural_language]: Weibel, 'An Introduction to Homological Algebra' — Chapter 3
  External source [natural_language]: Rotman, 'An Introduction to Homological Algebra' — Chapters 6-7
