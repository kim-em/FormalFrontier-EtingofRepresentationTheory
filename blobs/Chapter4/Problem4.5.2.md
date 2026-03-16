**Problem 4.5.2.** Let $G$ be a finite group. Let $V_i$ be the irreducible complex representations of $G$.
For every $i$, let

$$\psi_i = \frac{\dim V_i}{|G|} \sum_{g \in G} \chi_{V_i}(g) \cdot g^{-1} \in \mathbb{C}[G].$$

(i) Prove that $\psi_i$ acts on $V_j$ as the identity if $j = i$, and as the null map if $j \neq i$.

(ii) Prove that $\psi_i$ are **idempotents**; i.e., $\psi_i^2 = \psi_i$ for any $i$, and $\psi_i \psi_j = 0$ for any $i \neq j$.

Hint: In (i), notice that $\psi_i$ commutes with any element of $k[G]$ and thus acts on $V_j$ as an intertwining operator. Corollary 2.3.10 thus yields that $\psi_i$ acts on $V_j$ as a scalar. Compute this scalar by taking its trace in $V_j$.

