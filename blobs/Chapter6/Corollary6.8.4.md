**Corollary 6.8.4.** *For every positive root $\alpha$, there is an indecomposable representation $V$ with*

$$
d(V) = \alpha.
$$

**Proof.** Consider the sequence

$$
s_n \alpha, s_{n-1} s_n \alpha, \ldots.
$$

Consider the first element of this sequence which is a negative root (this has to happen by Lemma 6.7.2) and look at one step before that, calling this element $\beta$. So $\beta$ is a positive root and $s_i \beta$ is a negative root for some $i$. But since the $s_i$ only change one coordinate, we get

$$
\beta = \alpha_i
$$

and

$$
(s_q \ldots s_{n-1} s_n) \alpha = \alpha_i.
$$
Let $Q'$ be the quiver $Q$ with orientation modified by the element $s_q \ldots s_{n-1} s_n$. We let $k_{(i)}$ be the representation of $Q'$ having dimension vector $\alpha_i$. Then we define

$$
V = F_n^- F_{n-1}^- \ldots F_q^- k_{(i)}.
$$

This is an indecomposable representation of $Q$ and

$$
d(V) = \alpha.
$$

$\square$

