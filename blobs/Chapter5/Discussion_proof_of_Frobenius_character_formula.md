agree that $U_{\lambda+\rho-\sigma(\rho)} := U_{\langle\lambda+\rho-\sigma(\rho)\rangle}$). Now note that $\mu = \langle\lambda + \rho - \sigma(\rho)\rangle$ is obtained from $\lambda$ by adding vectors of the form $e_i - e_j$, $i < j$, which implies that $\mu > \lambda$ or $\mu = \lambda$, and the case $\mu = \lambda$ arises only if $\sigma = 1$. ${}^2$ Therefore, the above claim follows from Proposition 5.14.1.

Therefore, to show that $\theta_\lambda = \chi_\lambda$, by Lemma 5.7.2, it suffices to show that $(\theta_\lambda, \theta_\lambda) = 1$.

We have
$$(\theta_\lambda, \theta_\lambda) = \frac{1}{n!} \sum_{\mathbf{i}} |C_{\mathbf{i}}| \theta_\lambda(C_{\mathbf{i}})^2.$$

Using that
$$|C_{\mathbf{i}}| = \frac{n!}{\prod_m m^{i_m} i_m!},$$
we conclude that $(\theta_\lambda, \theta_\lambda)$ is the coefficient of $x^{\lambda+\rho} y^{\lambda+\rho}$ in the series $R(x, y) = \Delta(x)\Delta(y)S(x, y)$, where
$$S(x, y) = \sum_{\mathbf{i}} \prod_m \frac{(\sum_j x_j^m)^{i_m} (\sum_k y_k^m)^{i_m}}{m^{i_m} i_m!} = \sum_{\mathbf{i}} \prod_m \frac{(\sum_{j,k} x_j^m y_k^m / m)^{i_m}}{i_m!}.$$

Summing over $\mathbf{i}$ and $m$, we get
$$S(x, y) = \prod_m \exp\Bigl(\sum_{j,k} x_j^m y_k^m / m\Bigr)$$
$$= \exp\Bigl(-\sum_{j,k} \log(1 - x_j y_k)\Bigr) = \prod_{j,k} (1 - x_j y_k)^{-1}.$$

Thus,
$$R(x, y) = \frac{\prod_{i<j}(x_i - x_j)(y_i - y_j)}{\prod_{i,j}(1 - x_i y_j)}.$$

Now we need the following lemma.

