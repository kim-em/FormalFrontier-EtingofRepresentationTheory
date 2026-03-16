**Proposition 5.2.4.** *(i) $\overline{\mathbb{Z}}$ is a ring.*

*(ii) $\overline{\mathbb{Q}}$ is a field. Namely, it is an algebraic closure of the field of rational numbers.*

**Proof.** We will be using Definition 5.2.2. Let $\alpha$ be an eigenvalue of

$$\mathcal{A} \in \mathrm{Mat}_n(\mathbb{C})$$

with eigenvector $v$, and let $\beta$ be an eigenvalue of

$$\mathcal{B} \in \mathrm{Mat}_m(\mathbb{C})$$
with eigenvector $w$. Then $\alpha \pm \beta$ is an eigenvalue of

$$\mathcal{A} \otimes \mathrm{Id}_m \pm \mathrm{Id}_n \otimes \mathcal{B},$$

and $\alpha\beta$ is an eigenvalue of

$$\mathcal{A} \otimes \mathcal{B}.$$

The corresponding eigenvector is in both cases $v \otimes w$. This shows that both $\overline{\mathbb{Z}}$ and $\overline{\mathbb{Q}}$ are rings. To show that the latter is a field, it suffices to note that if $\alpha \neq 0$ is a root of a polynomial $p(x)$ of degree $d$, then $\alpha^{-1}$ is a root of $x^d p(1/x)$. The last statement is easy, since a number $\alpha$ is algebraic if and only if it defines a finite extension of $\mathbb{Q}$. $\square$

