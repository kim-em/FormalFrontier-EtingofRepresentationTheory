**Proposition 9.1.1.** Let $e_0 \in A/I$ be an idempotent, i.e., $e_0^2 = e_0$. There exists an idempotent $e \in A$ which is a lift of $e_0$ (i.e., it projects to $e_0$ under the reduction modulo $I$). This idempotent is unique up to conjugation by an element of $1 + I$.

**Proof.** Let us first establish the statement in the case when $I^2 = 0$. Note that in this case $I$ is a left and right module over $A/I$. Let $e_*$ be any lift of $e_0$ to $A$. Then $e_*^2 - e_* = a \in I$, and $e_0 a = a e_0$. We look for $e$ in the form $e = e_* + b$, $b \in I$. The equation for $b$ is

$$
e_0 b + b e_0 - b = -a.
$$

Set $b = (1 - 2e_0)a$. Then

$$
e_0 b + b e_0 - b = -2e_0 a - (1 - 2e_0)a = -a,
$$
so $e$ is an idempotent. To classify other solutions, set $e' = e + c$. For $e'$ to be an idempotent, we must have $ec + ce - c = 0$. This is equivalent to saying that $ece = 0$ and $(1 - e)c(1 - e) = 0$, so $c = ec(1 - e) + (1 - e)ce = [e, [e, c]]$. Hence $e' = (1 + [c, e])e(1 + [c, e])^{-1}$.

Now, in the general case, we prove by induction in $k$ that there exists a lift $e_k$ of $e_{k-1}$ to $A/I^{k+1}$, and it is unique up to conjugation by an element of $1 + I^k$ (this is sufficient as $I$ is nilpotent). Assume it is true for $k = m - 1$, and let us prove it for $k = m$. So we have an idempotent $e_{m-1} \in A/I^m$, and we have to lift it to $A/I^{m+1}$. But $(I^m)^2 = 0$ in $A/I^{m+1}$, so we are done. $\square$

