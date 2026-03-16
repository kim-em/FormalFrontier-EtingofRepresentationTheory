**Problem 4.12.2.** Let $p$ be a prime. Let $G$ be the group of $3 \times 3$ matrices over $\mathbb{F}_p$ which are upper triangular and have 1's on the diagonal, under multiplication (its order is $p^3$). It is called the **Heisenberg group**. For any complex number $z$ such that $z^p = 1$, we define a representation of $G$ on the space $V$ of complex functions on $\mathbb{F}_p$ by

$$(\rho \begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix} f)(x) = f(x - 1),$$
$$(\rho \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1 & 1 \\ 0 & 0 & 1 \end{pmatrix} f)(x) = z^x f(x)$$

(note that $z^x$ makes sense since $z^p = 1$).

(a) Show that such a representation exists and is unique, and compute $\rho(g)$ for all $g \in G$.

(b) Denote this representation by $R_z$. Show that $R_z$ is irreducible if and only if $z \neq 1$.

(c) Classify all 1-dimensional representations of $G$. Show that $R_1$ decomposes into a direct sum of 1-dimensional representations, where each of them occurs exactly once.

(d) Use (a)—(c) and the "sum of squares" formula to classify all irreducible representations of $G$.

