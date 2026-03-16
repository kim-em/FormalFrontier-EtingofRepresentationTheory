**Lemma 3.8.2.** *Let $W$ be a finite dimensional indecomposable representation of $A$. Then:*

*(i) Any homomorphism $\theta : W \to W$ is either an isomorphism or nilpotent.*

*(ii) If $\theta_s : W \to W$, $s = 1, \ldots, n$, are nilpotent homomorphisms, then so is $\theta := \theta_1 + \cdots + \theta_n$.*
**Proof.** (i) Generalized eigenspaces of $\theta$ are subrepresentations of $W$, and $W$ is their direct sum. Thus, $\theta$ can have only one eigenvalue $\lambda$. If $\lambda$ is zero, $\theta$ is nilpotent; otherwise it is an isomorphism.

(ii) The proof is by induction in $n$. The base is clear. To make the induction step ($n - 1$ to $n$), assume that $\theta$ is not nilpotent. Then by (i), $\theta$ is an isomorphism, so $\sum_{i=1}^n \theta^{-1} \theta_i = 1$. The morphisms $\theta^{-1} \theta_i$ are not isomorphisms, so they are nilpotent. Thus $1 - \theta^{-1} \theta_n = \theta^{-1} \theta_1 + \cdots + \theta^{-1} \theta_{n-1}$ is an isomorphism, which is a contradiction to the induction assumption. $\square$

By the lemma, we find that for some $s$, $\theta_s$ must be an isomorphism; we may assume that $s = 1$. In this case, $V'_1 = \operatorname{Im}(p'_1 i_1) \oplus \ker(p_1 i'_1)$, so since $V'_1$ is indecomposable, we get that $f := p'_1 i_1 : V_1 \to V'_1$ and $g := p_1 i'_1 : V'_1 \to V_1$ are isomorphisms.

