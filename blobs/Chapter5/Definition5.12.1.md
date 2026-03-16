**Definition 5.12.1.** A **partition** $\lambda$ of $n$ is a representation of $n$ in the form $n = \lambda_1 + \lambda_2 + \cdots + \lambda_p$, where $\lambda_i$ are positive integers and $\lambda_i \geq \lambda_{i+1}$.
To such $\lambda$ we will attach a **Young diagram** $Y_\lambda$, which is the union of rectangles $-j \leq y \leq -j + 1$, $0 \leq x \leq \lambda_j$ in the coordinate plane, for $j = 1, \ldots, p$. Clearly, $Y_\lambda$ is the union of $n$ unit squares $(i, j) := \{(x, y) \in \mathbb{R}^2 \mid -j \leq x \leq -j + 1, i - 1 \leq x \leq i\}$, $j = 1, \ldots, p$, $i = 1, \ldots, \lambda_j$. A **Young tableau** corresponding to $Y_\lambda$ is the result of filling the numbers $1, \ldots, n$ into the squares of $Y_\lambda$ in some way (without repetitions). For example, we will consider the Young tableau $T_\lambda$ obtained by filling in the numbers in increasing order, left to right, top to bottom.

We can define two subgroups of $S_n$ corresponding to $T_\lambda$:

1. The row subgroup $P_\lambda$: the subgroup which maps every element of $\{1, \ldots, n\}$ into an element standing in the same row in $T_\lambda$.

2. The column subgroup $Q_\lambda$: the subgroup which maps every element of $\{1, \ldots, n\}$ into an element standing in the same column in $T_\lambda$.

Clearly, $P_\lambda \cap Q_\lambda = \{1\}$.

