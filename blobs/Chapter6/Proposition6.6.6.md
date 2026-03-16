**Proposition 6.6.6.** *Let $Q$ be a quiver, and let $V$ be a representation of $Q$.*

*(1) If*

$$
\varphi : \bigoplus_{j \to i} V_j \to V_i
$$

*is surjective, then*

$$
F_i^- F_i^+ V = V.
$$

*(2) If*

$$
\psi : V_i \to \bigoplus_{i \to j} V_j
$$

*is injective, then*

$$
F_i^+ F_i^- V = V.
$$

**Proof.** In the following proof, by $i \to j$ we will always mean that $i$ points into $j$ in the original quiver $Q$. We only establish the first statement and we also restrict ourselves to showing that the spaces of $V$ and $F_i^- F_i^+ V$ are the same. It is enough to do so for the $i$th space. Let

$$
\varphi : \bigoplus_{j \to i} V_j \to V_i
$$

be surjective and let

$$
K = \ker \varphi.
$$
When applying $F_i^+$, the space $V_i$ gets replaced by $K$. Furthermore, let

$$
\psi : K \to \bigoplus_{j \to i} V_j.
$$

After applying $F_i^-$, $K$ gets replaced by

$$
K' = \left( \bigoplus_{j \to i} V_j \right) / (\operatorname{Im} \psi).
$$

But

$$
\operatorname{Im} \psi = K
$$

and therefore

$$
K' = \left( \bigoplus_{j \to i} V_j \right) / \left( \ker(\varphi : \bigoplus_{j \to i} V_j \to V_i) \right) = \operatorname{Im}(\varphi : \bigoplus_{j \to i} V_j \to V_i)
$$

by the homomorphism theorem. Since $\varphi$ was assumed to be surjective, we get

$$
K' = V_i.
$$

$\square$

