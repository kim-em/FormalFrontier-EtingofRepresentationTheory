**Lemma 4.10.3.** *Let $Y$ be an $n \times n$ matrix with entries $y_{ij}$. Then $\det Y$ is an irreducible polynomial of $\{y_{ij}\}$.*

**Proof.** Let $X = t \cdot \mathrm{Id} + \sum_{i=1}^{n} x_i E_{i,i+1}$, where $i + 1$ is computed modulo $n$, and $E_{i,j}$ are the elementary matrices. Then $\det(X) = t^n - (-1)^n x_1 \ldots x_n$, which is obviously irreducible. Hence $\det(Y)$ is irreducible (since it is so when $Y$ is specialized to $X$, and since irreducible factors of a homogeneous polynomial are homogeneous, so cannot specialize to nonzero constants). $\square$

