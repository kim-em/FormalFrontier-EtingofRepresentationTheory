## 4.4. Duals and tensor products of representations

If $V$ is a representation of a group $G$, then $V^*$ is also a representation, via

$$\rho_{V^*}(g) = (\rho_V(g)^*)^{-1} = (\rho_V(g)^{-1})^* = \rho_V(g^{-1})^*.$$

The character is $\chi_{V^*}(g) = \chi_V(g^{-1})$.

We have $\chi_V(g) = \sum \lambda_i$, where the $\lambda_i$ are the eigenvalues of $g$ in $V$. If $G$ is finite, these eigenvalues must be roots of unity because $\rho(g)^{|G|} = \rho(g^{|G|}) = \rho(e) = \mathrm{Id}$. Thus for complex representations

$$\chi_{V^*}(g) = \chi_V(g^{-1}) = \sum \lambda_i^{-1} = \sum \overline{\lambda_i} = \overline{\sum \lambda_i} = \overline{\chi_V(g)}.$$

In particular, $V \cong V^*$ as representations (not just as vector spaces) if and only if $\chi_V(g) \in \mathbb{R}$ for all $g \in G$.

If $V, W$ are representations of $G$, then $V \otimes W$ is also a representation, via

$$\rho_{V \otimes W}(g) = \rho_V(g) \otimes \rho_W(g).$$

Therefore, $\chi_{V \otimes W}(g) = \chi_V(g)\chi_W(g)$.

An interesting problem discussed below is decomposing $V \otimes W$ (for irreducible $V, W$) into the direct sum of irreducible representations.

