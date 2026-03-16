**Lemma 6.4.6.** *Let $\alpha$ be a root, $\alpha = \sum_{i=1}^n k_i \alpha_i$. Then either $k_i \geq 0$ for all $i$ or $k_i \leq 0$ for all $i$.*

**Proof.** Assume the contrary, i.e., $k_i > 0$, $k_j < 0$. Without loss of generality, we can also assume that $k_s = 0$ for all $s$ between $i$ and $j$. We can identify the indices $i, j$ with vertices of the graph $\Gamma$:

$$
\bullet \longrightarrow \bullet_i \xrightarrow{\epsilon} \bullet^{i'} \longrightarrow \bullet \longrightarrow \bullet_j \longrightarrow \bullet \longrightarrow \bullet
$$

Next, let $\epsilon$ be the edge connecting $i$ with the next vertex towards $j$ and let $i'$ be the vertex on the other end of $\epsilon$. We then let $\Gamma_1, \Gamma_2$ be the graphs obtained from $\Gamma$ by removing $\epsilon$. Since $\Gamma$ is supposed to be a Dynkin diagram — and therefore has no cycles or loops — both $\Gamma_1$ and $\Gamma_2$ will be connected graphs which are not connected to each other:

$$
\boxed{\bullet \longrightarrow \bullet_i}_{\Gamma_1} \qquad \boxed{\bullet \longrightarrow \bullet \longrightarrow \bullet_j \longrightarrow \bullet \longrightarrow \bullet}_{\Gamma_2}
$$

Then we have $i \in \Gamma_1$, $j \in \Gamma_2$. We define

$$
\beta = \sum_{m \in \Gamma_1} k_m \alpha_m, \quad \gamma = \sum_{m \in \Gamma_2} k_m \alpha_m.
$$

With this choice we get

$$
\alpha = \beta + \gamma.
$$

Since $k_i > 0$, $k_j < 0$, we know that $\beta \neq 0$, $\gamma \neq 0$ and therefore

$$
B(\beta, \beta) \geq 2, \quad B(\gamma, \gamma) \geq 2.
$$
Furthermore,

$$
B(\beta, \gamma) = -k_i k_{i'}
$$

since $\Gamma_1, \Gamma_2$ are only connected at $\epsilon$. But this has to be a nonnegative number, since $k_i > 0$ and $k_{i'} \leq 0$. This yields

$$
B(\alpha, \alpha) = B(\beta + \gamma, \beta + \gamma) = \underbrace{B(\beta, \beta)}_{\geq 2} + 2 \underbrace{B(\beta, \gamma)}_{\geq 0} + \underbrace{B(\gamma, \gamma)}_{\geq 2} \geq 4.
$$

But this is a contradiction, since $\alpha$ was assumed to be a root. $\square$

