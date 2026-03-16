In this problem you will prove the "only if" direction of this theorem (i.e., why other quivers are NOT of finite type).

(a) Suppose $Q$ has $n$ vertices and no self-loops. Show that for any rational numbers $x_i$, $1 \leq i \leq n$, which are not simultaneously zero, one has $q(x_1, \ldots, x_n) > 0$, where

$$
q(x_1, \ldots, x_n) := \sum_{i \in D} x_i^2 - \sum_{i,j \in D} b_{ij} x_i x_j.
$$

Hint: It suffices to check the result for integers: $x_i = m_i$. First assume that $m_i \geq 0$, and consider the space $W$ of representations $V$ of $Q$ such that $\dim V_i = m_i$. Show that the group $\prod_i GL_{m_i}(k)$ acts with finitely many orbits on $W \oplus k$, and use Problem 6.1.2 to derive the inequality. Then deduce the result in the case when $m_i$ are arbitrary integers.

(b) Deduce that $q$ is a positive definite quadratic form.

Hint: Use the fact that $\mathbb{Q}$ is dense in $\mathbb{R}$.

(c) Show that a quiver of finite type can have no self-loops. Then, using Problem 6.1.3, deduce the theorem.

