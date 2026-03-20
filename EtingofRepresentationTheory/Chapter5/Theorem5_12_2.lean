import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Distinct
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Classification

/-!
# Theorem 5.12.2: Classification of Irreducible Representations of S_n (Specht Modules)

For each partition λ of n, the subspace V_λ = ℂ[S_n] · c_λ is an irreducible
representation of S_n (where c_λ is the Young symmetrizer). Moreover, every
irreducible representation of S_n over ℂ is isomorphic to V_λ for a unique
partition λ. These representations are called **Specht modules**.

This file re-exports the three sub-files:
- `Theorem5_12_2_Irreducible`: Core definitions (`SymGroupAlgebra`, `SpechtModule`)
  and irreducibility (`Theorem5_12_2_irreducible`)
- `Theorem5_12_2_Distinct`: Distinctness (`Theorem5_12_2_distinct`) and center
  dimension bounds
- `Theorem5_12_2_Classification`: Wedderburn block machinery and classification
  (`Theorem5_12_2_classification`)
-/
