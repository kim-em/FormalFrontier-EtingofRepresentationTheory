Now we are ready to proceed to the proof of Theorem 4.10.2.

**Proof.** Let $V = \mathbb{C}[G]$ be the regular representation of $G$. Consider the operator-valued polynomial

$$L(\mathbf{x}) = \sum_{g \in G} x_g \rho(g),$$
where $\rho(g) \in \mathrm{End}\, V$ is induced by $g$. The action of $L(\mathbf{x})$ on an element $h \in G$ is

$$L(\mathbf{x})h = \sum_{g \in G} x_g \rho(g) h = \sum_{g \in G} x_g g h = \sum_{z \in G} x_{zh^{-1}} z.$$

So the matrix of the linear operator $L(\mathbf{x})$ in the basis $g_1, g_2, \ldots, g_n$ is $X_G$ with permuted columns and hence has the same determinant up to sign.

Further, by Maschke's theorem, we have

$$\det_V L(\mathbf{x}) = \prod_{i=1}^{r} (\det_{V_i} L(\mathbf{x}))^{\dim V_i},$$

where $V_i$ are the irreducible representations of $G$. We set $P_i = \det_{V_i} L(\mathbf{x})$. Let $\{e_{im}\}$ be bases of $V_i$ and let $E_{i,jk} \in \mathrm{End}\, V_i$ be the matrix units in these bases. Then $\{E_{i,jk}\}$ is a basis of $\mathbb{C}[G]$ and

$$L(\mathbf{x})|_{V_i} = \sum_{j,k} y_{i,jk} E_{i,jk},$$

where $y_{i,jk}$ are new coordinates on $\mathbb{C}[G]$ related to $x_g$ by a linear transformation. Then

$$P_i(\mathbf{x}) = \det|_{V_i} L(\mathbf{x}) = \det(y_{i,jk}).$$

Hence, $P_i$ are irreducible (by Lemma 4.10.3) and not proportional to each other (as they depend on different collections of variables $y_{i,jk}$). The theorem is proved. $\square$

