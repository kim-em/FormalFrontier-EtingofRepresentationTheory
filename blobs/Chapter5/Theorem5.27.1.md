**Theorem 5.27.1.** *(i) The representations $V_{(O,U)}$ are irreducible.*

*(ii) They are pairwise nonisomorphic.*

*(iii) They form a complete set of irreducible representations of $G \ltimes A$.*

*(iv) The character of $V = V_{(O,U)}$ is given by the Frobenius-type formula*

$$
\chi_V(a, g) = \frac{1}{|G_x|} \sum_{h \in G: hgh^{-1} \in G_x} x(h(a)) \chi_U(hgh^{-1}).
$$

**Proof.** (i) Let us decompose $V = V_{(O,U)}$ as an $A$-module. Then we get

$$
V = \bigoplus_{y \in O} V_y,
$$

where $V_y = \{v \in V_{(O,U)} | av = y(a)v, a \in A\}$. (Equivalently, $V_y = \{v \in V_{(O,U)} | v(g) = 0 \text{ unless } gy = x\}$.) So if $W \subset V$ is a subrepresentation, then $W = \bigoplus_{y \in O} W_y$, where $W_y \subset V_y$. Now, $V_y$ is a representation of $G_y$, which goes to $U$ under any isomorphism $G_y \to G_x$ determined by $g \in G$ mapping $x$ to $y$. Hence, $V_y$ is irreducible over $G_y$, so $W_y = 0$ or $W_y = V_y$ for each $y$. Also, if $hy = z$, then $hW_y = W_z$, so either $W_y = 0$ for all $y$ or $W_y = V_y$ for all $y$, as desired.
(ii) The orbit $O$ is determined by the $A$-module structure of $V$, and the representation $U$ is determined by the structure of $V_x$ as a $G_x$-module.

(iii) We have

$$
\sum_{U, O} \dim V_{(U, O)}^2 = \sum_{U, O} |O|^2 (\dim U)^2 =
$$

$$
\sum_O |O|^2 |G_x| = \sum_O |O| |G/G_x| |G_x| = |G| \sum_O |O| = |G| |A^\vee| = |G \ltimes A|.
$$

(iv) The proof is essentially the same as that of the Frobenius formula. $\square$

