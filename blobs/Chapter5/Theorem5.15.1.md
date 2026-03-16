## 5.15. The Frobenius character formula

Let $\Delta(x) = \prod_{1 \leq i < j \leq N} (x_i - x_j)$. Recall that $\Delta(x)$ is the Vandermonde determinant, $\det(x_i^{N-j})$. Let $\rho = (N-1, N-2, \ldots, 0) \in \mathbb{C}^N$. The following theorem, due to Frobenius, gives a character formula for the Specht modules $V_\lambda$.

**Theorem 5.15.1.** *Let $N \geq p$. Then $\chi_{V_\lambda}(C_\mathbf{i})$ is the coefficient of $x^{\lambda+\rho} := \prod x_j^{\lambda_j + N - j}$ in the polynomial*

$$\Delta(x) \prod_{m \geq 1} H_m(x)^{i_m}.$$

