Proposition 5.21.1 allows us to calculate the characters of the representations $L_\lambda$.

Namely, let $\dim V = N$, let $g \in GL(V)$, and let $x_1, \ldots, x_N$ be the eigenvalues of $g$ on $V$. To compute the character $\chi_{L_\lambda}(g)$ as a function of $x_1, \ldots, x_N$, let us calculate $\operatorname{Tr}_{V^{\otimes n}}(g^{\otimes n} s)$, where $s \in S_n$. If $s \in C_\mathbf{i}$, we easily get that this trace equals

$$
\prod_m \operatorname{Tr}(g^m)^{i_m} = \prod_m H_m(x)^{i_m}.
$$

On the other hand, by the Schur-Weyl duality

$$
\operatorname{Tr}_{V^{\otimes n}}(g^{\otimes n} s) = \sum_\lambda \chi_\lambda(C_\mathbf{i}) \operatorname{Tr}_{L_\lambda}(g).
$$

Comparing this to Proposition 5.21.1 and using linear independence of columns of the character table of $S_n$, we obtain

