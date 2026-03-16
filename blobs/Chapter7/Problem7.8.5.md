**Problem 7.8.5.** Let $D_\bullet$ be a complex of abelian groups with differentials $d_i$, $i \in \mathbb{Z}$, let $C_\bullet$ be a subcomplex of $D_\bullet$ (i.e. a collection of subgroups $C_i \subset D_i$ such that $d_i(C_i) \subset C_{i+1}$), and let $E_\bullet = D_\bullet / C_\bullet$ be the quotient complex (i.e., $E_i = D_i / C_i$ with differentials induced by $d_i$).

Define a homomorphism $c_i : H^i(E) \to H^{i+1}(C)$ as follows. Given $x \in H^i(E)$, pick a representative $x'$ of $x$ in $E_i$. Let $x''$ be a lift of $x'$ to $D_i$. Let $y' = dx'' \in D_{i+1}$ (we abbreviate the notation, denoting $d_i$ just by $d$). Since $dx' = 0$, $y' = dx'' \in C_{i+1}$. Also, $dy' = d^2 x'' = 0$. So $y'$ represents an element $y \in H^{i+1}(C)$. We will set $c_i(x) = y$.

(i) Show that $c_i$ is well defined, i.e., $c_i(x)$ does not depend on the choice of $x'$ and $x''$.

(ii) Show that the sequence

(7.8.1) $\ldots H^{i-1}(E) \to H^i(C) \to H^i(D) \to H^i(E) \to H^{i+1}(C) \ldots,$

where the first map is $c_{i-1}$, the middle two maps are induced by the maps $C_i \to D_i \to E_i$, and the last map is $c_i$, is exact.

