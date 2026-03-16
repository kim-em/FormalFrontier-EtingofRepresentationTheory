
If $V$ is finite dimensional with basis $e_i$, $i = 1, \ldots, N$, and $e^i$ is the dual basis of $V^*$, then a basis of $E$ is the set of vectors

$$
e_{i_1} \otimes \cdots \otimes e_{i_n} \otimes e^{j_1} \otimes \cdots \otimes e^{j_m},
$$

and a typical element of $E$ is

$$
\sum_{i_1, \ldots, i_n, j_1, \ldots, j_m = 1}^{N} T^{i_1 \ldots i_n}_{j_1 \ldots j_m} e_{i_1} \otimes \cdots \otimes e_{i_n} \otimes e^{j_1} \otimes \cdots \otimes e^{j_m},
$$

where $T$ is a multidimensional table of numbers.

Physicists define a tensor as a collection of such multidimensional tables $T_B$ attached to every basis $B$ in $V$, which change according to a certain rule when the basis $B$ is changed (derive this rule!). Here it is important to distinguish upper and lower indices, since lower indices of $T$ correspond to $V$ and upper ones to $V^*$. The physicists don't write the sum sign, but remember that one should sum over indices that repeat twice — once as an upper index and once as lower. This convention is called the *Einstein summation*, and it also stipulates that if an index appears once, then there is no summation over it, while no index is supposed to appear more than once as an upper index or more than once as a lower index.
