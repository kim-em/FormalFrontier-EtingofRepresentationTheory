# References: a_lambda x b_lambda = l_lambda(x) c_lambda where l_lambda is a linear function

## External Dependencies

- **Symmetric group: permutations, cycle decomposition, conjugacy classes of S_n, sign homomorphism** (undergraduate_prerequisite)
  Mathlib (exact): `Equiv.Perm`, `Equiv.Perm.cycleType`, `Equiv.Perm.sign`
  Symmetric group as `Equiv.Perm (Fin n)`. Cycle decomposition, sign homomorphism, and conjugacy class characterization all present.
- **Combinatorics of partitions and Young diagrams: partitions of integers, Young tableaux, hook lengths, content of a cell** (undergraduate_prerequisite)
  Mathlib (partial): `Nat.Partition`, `YoungDiagram`
  `Nat.Partition` and `YoungDiagram` exist. However, Young tableaux (standard/semistandard), hook lengths, and content of cells are NOT in Mathlib. These will need custom definitions for the representation theory of S_n.
  External source [natural_language]: Fulton, 'Young Tableaux' — Chapters 1-4
  External source [natural_language]: Sagan, 'The Symmetric Group' — Chapter 2
  External source [lean_library]: Mathlib Nat.Partition and YoungDiagram — partial coverage
