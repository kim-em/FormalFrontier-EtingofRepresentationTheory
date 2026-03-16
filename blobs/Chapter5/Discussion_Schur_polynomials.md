Let $\lambda = (\lambda_1, \ldots, \lambda_p)$ be a partition of $n$, and let $N \geq p$. Let

$$
D_\lambda(x) = \sum_{s \in S_N} (-1)^s \prod_{j=1}^{N} x_{s(j)}^{\lambda_j + N - j} = \det(x_i^{\lambda_j + N - j}).
$$

Define the polynomials

$$
S_\lambda(x) := \frac{D_\lambda(x)}{D_0(x)}
$$

(clearly $D_0(x)$ is just $\Delta(x)$). It is easy to see that these are indeed polynomials, as $D_\lambda$ is antisymmetric and therefore must be divisible by $\Delta$. The polynomials $S_\lambda$ are called the **Schur polynomials**.

