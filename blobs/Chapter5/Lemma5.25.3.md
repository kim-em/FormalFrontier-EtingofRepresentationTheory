
**Lemma 5.25.3.** *Let $\chi$ be the character of the virtual representation defined above. Then*

$$
\langle \chi, \chi \rangle = 1
$$

*and*

$$
\chi(1) > 0.
$$

**Proof.**

$$
\chi(1) = q(q + 1) - (q + 1) - q(q - 1) = q - 1 > 0.
$$

We now compute the inner product $\langle \chi, \chi \rangle$. Since $\alpha(x)$ is a root of unity, this will be equal to

$$
\frac{1}{(q - 1)^2 q(q + 1)} \Big[ (q - 1) \cdot (q - 1)^2 \cdot 1 + (q - 1) \cdot 1 \cdot (q^2 - 1) + \frac{q(q - 1)}{2} \cdot \sum_{\zeta \text{ elliptic}} (\nu(\zeta) + \nu^q(\zeta)) \overline{(\nu(\zeta) + \nu^q(\zeta))} \Big].
$$

Because $\nu$ is also a root of unity, the last term of the expression evaluates to

$$
\sum_{\zeta \text{ elliptic}} (2 + \nu^{q-1}(\zeta) + \nu^{1-q}(\zeta)).
$$

Let's evaluate the last summand.
Since $\mathbb{F}_{q^2}^\times$ is cyclic and $\nu^q \neq \nu$,

$$\sum_{\zeta \in \mathbb{F}_{q^2}^\times} \nu^{q-1}(\zeta) = \sum_{\zeta \in \mathbb{F}_{q^2}^\times} \nu^{1-q}(\zeta) = 0.$$

Therefore,

$$\sum_{\zeta \text{ elliptic}} (\nu^{q-1}(\zeta) + \nu^{1-q}(\zeta)) = -\sum_{\zeta \in \mathbb{F}_q^\times} (\nu^{q-1}(\zeta) + \nu^{1-q}(\zeta)) = -2(q - 1)$$

since $\mathbb{F}_q^\times$ is cyclic of order $q - 1$. Therefore,

$$\langle \chi, \chi \rangle = \frac{1}{(q - 1)^2 q(q + 1)} \Big( (q - 1) \cdot (q - 1)^2 \cdot 1 + (q - 1) \cdot 1 \cdot (q^2 - 1) + \frac{q(q - 1)}{2} \cdot (2(q^2 - q) - 2(q - 1)) \Big) = 1.$$

$\square$

