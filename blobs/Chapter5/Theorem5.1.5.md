**Theorem 5.1.5** (Frobenius-Schur). *The number of involutions (= elements of order $\leq 2$) in $G$ is equal to $\sum_V \dim(V) FS(V)$, i.e., the sum of dimensions of all representations of $G$ of real type minus the sum of dimensions of its representations of quaternionic type.*

**Proof.** Let $A : V \to V$ have eigenvalues $\lambda_1, \lambda_2, \ldots, \lambda_n$. We have

$$\operatorname{Tr}|_{S^2V}(A \otimes A) = \sum_{i \leq j} \lambda_i \lambda_j,$$

$$\operatorname{Tr}|_{\Lambda^2V}(A \otimes A) = \sum_{i < j} \lambda_i \lambda_j.$$
Thus,

$$\operatorname{Tr}|_{S^2V}(A \otimes A) - \operatorname{Tr}|_{\Lambda^2V}(A \otimes A) = \sum_{1 \leq i \leq n} \lambda_i^2 = \operatorname{Tr}(A^2).$$

Thus for $g \in G$ we have

$$\chi_V(g^2) = \chi_{S^2V}(g) - \chi_{\Lambda^2V}(g).$$

Therefore, setting $P = |G|^{-1} \sum_{g \in G} g$, we get

$$|G|^{-1} \chi_V\!\left(\sum_{g \in G} g^2\right) = \chi_{S^2V}(P) - \chi_{\wedge^2 V}(P) = \dim(S^2 V)^G - \dim(\wedge^2 V)^G$$

$$= \begin{cases} 1 & \text{if } V \text{ is of real type,} \\ -1 & \text{if } V \text{ is of quaternionic type,} \\ 0 & \text{if } V \text{ is of complex type.} \end{cases}$$

Finally, the number of involutions in $G$ equals

$$\frac{1}{|G|} \sum_V \dim V \, \chi_V\!\left(\sum_{g \in G} g^2\right) = \sum_{\text{real } V} \dim V - \sum_{\text{quat. } V} \dim V.$$

$\square$

