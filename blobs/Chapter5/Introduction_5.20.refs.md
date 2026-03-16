# References: Section 5.20: Historical interlude — Hermann Weyl

## External Dependencies

- **Topological groups and Lie groups: continuous group homomorphisms, examples (GL_n(R), SO(n), U(n))** (undergraduate_prerequisite)
  Mathlib (partial): `IsTopologicalGroup`, `ContinuousMonoidHom`, `GroupTopology`
  Topological groups via `IsTopologicalGroup`. Continuous homomorphisms via `ContinuousMonoidHom`. However, Lie groups as smooth manifolds with group structure are NOT in Mathlib. The book uses Lie groups informally; the topological group API suffices for most needs.
  External source [natural_language]: Bröcker & tom Dieck, 'Representations of Compact Lie Groups' — Chapter I
- **Schur-Weyl duality: the commuting actions of GL(V) and S_n on V^{⊗n} give a double centralizer relationship** (external_result)
  Schur-Weyl duality is NOT in Mathlib. The ingredients (representations, symmetric group, tensor products) exist, but the double centralizer theorem and Schur-Weyl duality are absent.
