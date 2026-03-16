**Problem 6.9.1.** Let $Q_n$ be the **cyclic quiver** of length $n$, i.e., $n$ vertices connected by $n$ oriented edges forming a cycle. Obviously, the classification of indecomposable representations of $Q_1$ is given by the Jordan normal form theorem. Obtain a similar classification of indecomposable representations of $Q_2$. In other words, classify pairs of linear operators $A : V \to W$ and $B : W \to V$ up to isomorphism. Namely:

(a) Consider the following pairs (for $n \geq 1$):

(1) $E_{n,\lambda}$: $V = W = \mathbb{C}^n$, $A$ is the Jordan block of size $n$ with eigenvalue $\lambda$, $B = 1$ ($\lambda \in \mathbb{C}$).

(2) $E_{n,\infty}$: is obtained from $E_{n,0}$ by exchanging $V$ with $W$ and $A$ with $B$.
(3) $H_n$: $V = \mathbb{C}^n$ with basis $v_i$, $W = \mathbb{C}^{n-1}$ with basis $w_i$, $Av_i = w_i$, $Bw_i = v_{i+1}$ for $i < n$, and $Av_n = 0$.

(4) $K_n$ is obtained from $H_n$ by exchanging $V$ with $W$ and $A$ with $B$.

Show that these are indecomposable and pairwise nonisomorphic.

(b) Show that if $E$ is a representation of $Q_2$ such that $AB$ is not nilpotent, then $E = E' \oplus E''$, where $E'' = E_{n,\lambda}$ for some $\lambda \neq 0$.

(c) Consider the case when $AB$ is nilpotent, and consider the operator $X$ on $V \oplus W$ given by $X(v, w) = (Bw, Av)$. Show that $X$ is nilpotent and admits a basis consisting of chains (i.e., sequences $u, Xu, X^2 u, \ldots X^{l-1} u$ where $X^l u = 0$) which are compatible with the direct sum decomposition (i.e., for every chain $u \in V$ or $u \in W$). Deduce that (1)—(4) are the only indecomposable representations of $Q_2$.

(d) (Harder!) Generalize this classification to the Kronecker quiver, which has two vertices 1 and 2 and two edges both going from 1 to 2.

(e) (Still harder!) Can you generalize this classification to $Q_n$, $n > 2$ with any orientation? (Easier version: consider only the cyclic orientation).

