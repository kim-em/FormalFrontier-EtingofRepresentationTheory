**Proposition 5.21.2.**

$$
S_\lambda(1, z, z^2, \ldots, z^{N-1}) = \prod_{1 \leq i < j \leq N} \frac{z^{\lambda_i - i} - z^{\lambda_j - j}}{z^{-i} - z^{-j}}.
$$

*Therefore,*

$$
S_\lambda(1, \ldots, 1) = \prod_{1 \leq i < j \leq N} \frac{\lambda_i - \lambda_j + j - i}{j - i}.
$$

**Proof.** First, $D_\lambda(1, z, \ldots, z^{N-1})$ is a Vandermonde determinant evaluated at $(z^{\lambda_i + N - i})_{1 \leq i \leq N}$, so it equals $\prod_{i < j} (z^{\lambda_i + N - i} - z^{\lambda_j + N - j})$. Dividing by the same formula with $\lambda = 0$ yields the formula for $S_\lambda(1, z, \ldots, z^{N-1})$. Now take $\lim_{z \to 1}$ and apply L'Hopital's rule. $\square$

