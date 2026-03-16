**Lemma 6.4.2.** (1) *$B$ is positive definite.*

(2) *$B(x, x)$ takes only even values for $x \in \mathbb{Z}^n$.*

**Proof.** (1) This follows by definition, since $\Gamma$ is a Dynkin diagram.

(2) By the definition of the Cartan matrix we get

$$
B(x, x) = x^T A x = \sum_{i,j} x_i a_{ij} x_j = 2 \sum_i x_i^2 + \sum_{i,j,\ i \neq j} x_i a_{ij} x_j
$$

$$
= 2 \sum_i x_i^2 + 2 \cdot \sum_{i < j} a_{ij} x_i x_j,
$$

which is even. $\square$

