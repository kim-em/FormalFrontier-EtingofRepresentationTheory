**Example 6.4.9.** (1) Let $\Gamma$ be of the type $A_{N-1}$. Then the lattice $L = \mathbb{Z}^{N-1}$ can be realized as a subgroup of the lattice $\mathbb{Z}^N$ by letting $L \subseteq \mathbb{Z}^N$ be the subgroup of all vectors $(x_1, \ldots, x_N)$ such that

$$
\sum_i x_i = 0.
$$

The vectors

$$
\alpha_1 = (1, -1, 0, \ldots, 0),
$$

$$
\alpha_2 = (0, 1, -1, 0, \ldots, 0),
$$

$$
\vdots
$$

$$
\alpha_{N-1} = (0, \ldots, 0, 1, -1)
$$

naturally form a basis of $L$. Furthermore, the standard inner product

$$
(x, y) = \sum x_i y_i
$$

on $\mathbb{Z}^N$ restricts to the inner product $B$ given by $\Gamma$ on $L$, since it takes the same values on the basis vectors:

$$
(\alpha_i, \alpha_i) = 2,
$$

$$
(\alpha_i, \alpha_j) = \begin{cases} -1, & i, j \text{ are adjacent}, \\ 0, & \text{otherwise}. \end{cases}
$$

This means that vectors of the form

$$
(0, \ldots, 0, 1, 0, \ldots, 0, -1, 0, \ldots, 0) = \alpha_i + \alpha_{i+1} + \cdots + \alpha_{j-1}
$$
and

$$
(0, \ldots, 0, -1, 0, \ldots, 0, 1, 0, \ldots, 0) = -(\alpha_i + \alpha_{i+1} + \cdots + \alpha_{j-1})
$$

are the roots of $L$. Therefore the number of positive roots in $L$ equals

$$
\frac{N(N-1)}{2}.
$$

Thus, $A_n$ has $n(n+1)/2$ positive roots.

(2) As a fact, we also state the number of positive roots in the other Dynkin diagrams:

- $D_n$: $n(n-1)$ roots,
- $E_6$: 36 roots,
- $E_7$: 63 roots,
- $E_8$: 120 roots.

