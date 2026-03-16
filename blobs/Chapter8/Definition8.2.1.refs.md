# References: Projective resolution

## Mathlib Coverage (exact)

- `CategoryTheory.ProjectiveResolution`

`CategoryTheory.ProjectiveResolution X` is a projective resolution of X in an abelian category.

## External Dependencies

- **Hom functor and its properties: Hom_A(M,N) as a vector space, left exactness, contravariance in first argument** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.yoneda`, `CategoryTheory.coyoneda`, `LinearMap`
  Yoneda embedding provides the Hom functor abstractly. For modules, `LinearMap` (i.e., `M →ₗ[R] N`) is the Hom. Left exactness of Hom available.
- **Ext functors: definition as derived functors of Hom, long exact sequence in Ext, Ext^1 classifies extensions** (external_result)
  Mathlib (partial): `Ext`, `CategoryTheory.ProjectiveResolution`
  `Ext` is defined as a functor in Mathlib via projective resolutions. The long exact sequence in Ext exists. The classification of extensions by Ext^1 may not be fully stated.
  External source [natural_language]: Weibel, 'An Introduction to Homological Algebra' — Chapter 3
  External source [natural_language]: Rotman, 'An Introduction to Homological Algebra' — Chapters 6-7
