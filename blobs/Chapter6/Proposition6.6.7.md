**Proposition 6.6.7.** *Let $Q$ be a quiver, and let $V$ be an indecomposable representation of $Q$. Then $F_i^+ V$ and $F_i^- V$ (whenever defined) are either indecomposable or $0$.*

**Proof.** We prove the proposition for $F_i^+ V$; the case $F_i^- V$ follows similarly. By Proposition 6.6.5 it follows that either

$$
\varphi : \bigoplus_{j \to i} V_j \to V_i
$$

is surjective or $\dim V_i = 1$, $\dim V_j = 0$, $j \neq i$. In the last case

$$
F_i^+ V = 0.
$$

So we can assume that $\varphi$ is surjective. In this case, assume that $F_i^+ V$ is decomposable as

$$
F_i^+ V = X \oplus Y
$$
with $X, Y \neq 0$. But $F_i^+ V$ is injective at $i$, since the maps are canonical projections, whose direct sum is the tautological embedding. Therefore $X$ and $Y$ also have to be injective at $i$ and hence (by Proposition 6.6.6)

$$
F_i^+ F_i^- X = X, \quad F_i^+ F_i^- Y = Y.
$$

In particular

$$
F_i^- X \neq 0, \quad F_i^- Y \neq 0.
$$

Therefore

$$
V = F_i^- F_i^+ V = F_i^- X \oplus F_i^- Y,
$$

which is a contradiction, since $V$ was assumed to be indecomposable. So we can infer that

$$
F_i^+ V
$$

is indecomposable. $\square$

