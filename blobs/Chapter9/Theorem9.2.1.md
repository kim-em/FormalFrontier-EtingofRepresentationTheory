**Theorem 9.2.1.** *(i) For each $i = 1, \ldots, n$ there exists a unique indecomposable finitely generated projective module $P_i$ such that*

$$
\dim \operatorname{Hom}(P_i, M_j) = \delta_{ij}.
$$
*(ii)* $A = \bigoplus_{i=1}^n (\dim M_i) P_i$.

*(iii) Any indecomposable finitely generated projective module over $A$ is isomorphic to $P_i$ for some $i$.*

**Proof.** Recall that $A / \operatorname{Rad}(A) = \bigoplus_{i=1}^n \operatorname{End}(M_i)$ and that $\operatorname{Rad}(A)$ is a nilpotent ideal. Pick a basis of $M_i$, and let $e_{ij}^0 = E_{jj}^i$, the rank 1 projectors projecting to the basis vectors of this basis ($j = 1, \ldots, \dim M_i$). Then $e_{ij}^0$ are orthogonal idempotents in $A / \operatorname{Rad}(A)$. So by Corollary 9.1.3 we can lift them to orthogonal idempotents $e_{ij}$ in $A$. Now define $P_{ij} = Ae_{ij}$. Then $A = \bigoplus_i \bigoplus_{j=1}^{\dim M_i} P_{ij}$, so $P_{ij}$ are projective. Also, we have $\operatorname{Hom}(P_{ij}, M_k) = e_{ij} M_k$, so $\dim \operatorname{Hom}(P_{ij}, M_k) = \delta_{ik}$. Finally, $P_{ij}$ is independent of $j$ up to an isomorphism, as $e_{ij}$ for fixed $i$ are conjugate under $A^\times$ by Proposition 9.1.1; thus we will denote $P_{ij}$ by $P_i$.

We claim that $P_i$ is indecomposable. Indeed, if $P_i = Q_1 \oplus Q_2$, then $\operatorname{Hom}(Q_l, M_j) = 0$ for all $j$ either for $l = 1$ or for $l = 2$, so either $Q_1 = 0$ or $Q_2 = 0$.

Also, there can be no other indecomposable finitely generated projective modules, since any indecomposable projective module has to occur in the decomposition of $A$. The theorem is proved. $\square$

