**Theorem 6.8.1.** *There exists $m \in \mathbb{N}$, such that*

$$
d\left(V^{(m)}\right) = \alpha_p
$$

*for some $p$.*

**Proof.** If $V^{(i)}$ is surjective at the appropriate vertex $k$, then

$$
d\left(V^{(i+1)}\right) = d\left(F_k^+ V^{(i)}\right) = s_k d\left(V^{(i)}\right).
$$

This implies that if $V^{(0)}, \ldots, V^{(i-1)}$ are surjective at the appropriate vertices, then

$$
d\left(V^{(i)}\right) = \ldots s_{n-1} s_n d(V).
$$

By Lemma 6.7.2 this cannot continue indefinitely, since $d\left(V^{(i)}\right)$ may not have any negative entries. Let $i$ be the smallest number such that $V^{(i)}$ is not surjective at the appropriate vertex. By Proposition 6.6.7 it is indecomposable. So, by Proposition 6.6.5, we get

$$
d(V^{(i)}) = \alpha_p
$$

for some $p$. $\square$

