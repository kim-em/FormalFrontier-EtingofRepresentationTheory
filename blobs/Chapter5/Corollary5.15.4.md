$N(N-1)$. This implies that the right-hand side and the left-hand side are proportional. The proportionality coefficient (which is equal to 1) is found by induction by multiplying both sides by $z_N - y_N$ and then setting $z_N = y_N$. $\square$

Now setting $z_i = 1/x_i$ in the lemma, we get

**Corollary 5.15.4** (Cauchy identity).

$$R(x, y) = \det\left(\frac{1}{1 - x_i y_j}\right) = \sum_{\sigma \in S_N} \frac{(-1)^\sigma}{\prod_{j=1}^N (1 - x_j y_{\sigma(j)})}.$$

Corollary 5.15.4 easily implies that the coefficient of $x^{\lambda+\rho} y^{\lambda+\rho}$ is 1. Indeed, if $\sigma \neq 1$ is a permutation in $S_N$, the coefficient of this monomial in $\prod_j \frac{1}{(1 - x_j y_{\sigma(j)})}$ is obviously zero, since the coordinates of $\lambda + \rho$ are strictly decreasing and hence distinct. $\square$

