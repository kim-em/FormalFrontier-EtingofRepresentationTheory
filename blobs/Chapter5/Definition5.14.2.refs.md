# References: Kostka numbers K_{mu,lambda}

## Mathlib Coverage (gap)

Kostka numbers (number of semistandard Young tableaux of shape λ and weight μ) are not in Mathlib. Needs definition using `SemistandardYoungTableau`.

## External Sources (definition gap)

- **[natural_language]** Fulton, 'Young Tableaux' (LMS Student Texts) — Chapter 1-2
  Comprehensive development of Young tableaux, semistandard tableaux, and Kostka numbers with combinatorial proofs
- **[natural_language]** Stanley, 'Enumerative Combinatorics Vol. 2' — Section 7.10
  Kostka numbers, Schur polynomials, and their combinatorial properties
- **[natural_language]** Sagan, 'The Symmetric Group' — Chapter 2
  Young tableaux and Kostka numbers in context of symmetric group representations

## External Dependencies

- **Symmetric polynomials and power sums: elementary symmetric polynomials, power sum symmetric polynomials, Newton's identities** (undergraduate_prerequisite)
  Mathlib (partial): `MvPolynomial.esymm`, `MvPolynomial.psum`
  `MvPolynomial.esymm` and `MvPolynomial.psum` provide elementary symmetric and power sum polynomials. Newton's identities (relating esymm and psum) may not be fully proved in Mathlib. Schur polynomials are NOT in Mathlib.
  External source [natural_language]: Macdonald, 'Symmetric Functions and Hall Polynomials' — Chapter I
  External source [natural_language]: Stanley, 'Enumerative Combinatorics Vol. 2' — Chapter 7
