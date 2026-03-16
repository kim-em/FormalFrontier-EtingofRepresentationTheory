**Theorem 4.6.2.** *If $G$ is finite, then any finite dimensional representation of $G$ has a unitary structure. If the representation is irreducible, this structure is unique up to scaling by a positive real number.*

**Proof.** Take any positive definite Hermitian form $B$ on $V$ and define another Hermitian form $\mathbf{B}$ on $V$ as follows:

$$\mathbf{B}(v, w) = \sum_{g \in G} B(\rho_V(g)v, \rho_V(g)w).$$

Then $\mathbf{B}$ is a positive definite $G$-invariant Hermitian form on $V$.

If $V$ is an irreducible representation and $B_1, B_2$ are two positive definite $G$-invariant Hermitian forms on $V$, then $B_1(v, w) = B_2(Av, w)$ for some linear map $A : V \to V$ (since any positive definite Hermitian form is nondegenerate), and moreover $A$ is also $G$-invariant, i.e., is a homomorphism of representations. Then by Schur's lemma, $A = \lambda \mathrm{Id}$, and clearly $\lambda > 0$. $\square$

