**Proposition 5.19.1.** *The image of $GL(V)$ in $\operatorname{End}(V^{\otimes n})$ spans $B$.*

**Proof.** Recall that $B$ is spanned by the elements $g^{\otimes n}$, $g \in \operatorname{End} V$. Denote the span of $g^{\otimes n}$, $g \in GL(V)$, by $B'$. Let $b \in \operatorname{End} V$ be any element.

We claim that $B'$ contains $b^{\otimes n}$. Indeed, for all values of $t$ but finitely many, $t \cdot \operatorname{Id} + b$ is invertible, so $(t \cdot \operatorname{Id} + b)^{\otimes n}$ belongs to $B'$. This implies that this is true for all $t$, in particular $t = 0$, since $(t \cdot \operatorname{Id} + b)^{\otimes n}$ is a polynomial of $t$. More precisely, if $f$ is a linear function on $\operatorname{End}(V^{\otimes n})$ that vanishes on $B'$ then $f((t \cdot \operatorname{Id} + b)^{\otimes n})$ is a scalar-valued polynomial of $t$ which vanishes for almost all $t \in k$, hence is identically zero.

The rest follows from Lemma 5.18.3. $\square$
