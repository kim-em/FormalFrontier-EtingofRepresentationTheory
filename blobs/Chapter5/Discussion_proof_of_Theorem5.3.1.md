Now, consider

$$\sum_i \lambda_i \overline{\chi_V(g_{C_i})}.$$

This is an algebraic integer, since:

(i) $\lambda_i$ are algebraic integers by Proposition 5.3.2,

(ii) $\overline{\chi_V(g_{C_i})}$ is a sum of roots of unity (it is the sum of eigenvalues of the matrix of $\rho(g_{C_i})$, and since $g_{C_i}^{|G|} = e$ in $G$, the eigenvalues of $\rho(g_{C_i})$ are roots of unity), and

(iii) $\overline{\mathbb{Z}}$ is a ring (Proposition 5.2.4).

On the other hand, from the definition of $\lambda_i$,

$$\sum_{C_i} \lambda_i \overline{\chi_V(g_{C_i})} = \sum_i \frac{|C_i| \chi_V(g_{C_i}) \overline{\chi_V(g_{C_i})}}{\dim V}.$$

Recalling that $\chi_V$ is a class function, this is equal to

$$\sum_{g \in G} \frac{\chi_V(g) \overline{\chi_V(g)}}{\dim V} = \frac{|G|(\chi_V, \chi_V)}{\dim V}.$$

Since $V$ is an irreducible representation, $(\chi_V, \chi_V) = 1$, so

$$\sum_{C_i} \lambda_i \overline{\chi_V(g_{C_i})} = \frac{|G|}{\dim V}.$$
Since $\frac{|G|}{\dim V} \in \mathbb{Q}$ and $\sum_{C_i} \lambda_i \overline{\chi_V(g_{C_i})} \in \overline{\mathbb{Z}}$, by Proposition 5.2.5, $\frac{|G|}{\dim V} \in \mathbb{Z}$. $\square$

