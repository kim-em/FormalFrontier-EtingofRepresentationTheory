**Theorem 4.5.4.** *Let $g, h \in G$, and let $Z_g$ denote the centralizer of $g$ in $G$. Then*

$$\sum_V \chi_V(g)\overline{\chi_V(h)} = \begin{cases} |Z_g|, & \text{if } g \text{ is conjugate to } h, \\ 0, & \text{otherwise,} \end{cases}$$

*where the summation is taken over all irreducible representations of $G$.*

**Proof.** As noted above, $\overline{\chi_V(h)} = \chi_{V^*}(h)$, so the left-hand side equals (using Maschke's theorem):

$$\sum_V \chi_V(g)\chi_{V^*}(h) = \operatorname{Tr}|_{\bigoplus_V V \otimes V^*}(g \otimes (h^*)^{-1})$$

$$= \operatorname{Tr}|_{\bigoplus_V \operatorname{End} V}(x \mapsto gxh^{-1}) = \operatorname{Tr}|_{\mathbb{C}[G]}(x \mapsto gxh^{-1}).$$

