**Proof.** For a right $H$-coset $\sigma$ of $G$, let us define

$$V_\sigma = \{f \in \operatorname{Ind}_H^G V \mid f(g) = 0 \ \forall g \notin \sigma\}.$$

Then one has

$$\operatorname{Ind}_H^G V = \bigoplus_\sigma V_\sigma,$$

and so

$$\chi(g) = \sum_\sigma \chi_\sigma(g),$$

where $\chi_\sigma(g)$ is the trace of the diagonal block of $\rho(g)$ corresponding to $V_\sigma$.

Since $g(\sigma) = \sigma g$ is a right $H$-coset for any right $H$-coset $\sigma$, $\chi_\sigma(g) = 0$ if $\sigma \neq \sigma g$.

Now assume that $\sigma = \sigma g$. Then $x_\sigma g = h x_\sigma$ where $h = x_\sigma g x_\sigma^{-1} \in H$. Consider the map $\alpha : V_\sigma \to V$ defined by $\alpha(f) = f(x_\sigma)$. Since $f \in V_\sigma$ is uniquely determined by $f(x_\sigma)$, $\alpha$ is an isomorphism. We have

$$\alpha(gf) = g(f)(x_\sigma) = f(x_\sigma g) = f(h x_\sigma) = \rho_V(h) f(x_\sigma) = h\alpha(f),$$

and $gf = \alpha^{-1} h \alpha(f)$. This means that $\chi_\sigma(g) = \chi_V(h)$. Therefore

$$\chi(g) = \sum_{\sigma \in H \backslash G, \sigma g = \sigma} \chi_V(x_\sigma g x_\sigma^{-1}).$$
$\square$

