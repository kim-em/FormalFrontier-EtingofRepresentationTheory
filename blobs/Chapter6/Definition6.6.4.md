**Definition 6.6.4.** Let $Q$ be a quiver, and let $i \in Q$ be a source. Let $V$ be a representation of $Q$. Let $\psi$ be the canonical map

$$
\psi : V_i \to \bigoplus_{i \to j} V_j.
$$

Then we define the reflection functor

$$
F_i^- : \operatorname{Rep} Q \to \operatorname{Rep} \overline{Q}_i
$$

by the rule

$$
F_i^-(V)_k = V_k \quad \text{if } k \neq i,
$$

$$
F_i^-(V)_i = \operatorname{Coker}(\psi) = \left( \bigoplus_{i \to j} V_j \right) / \operatorname{Im} \psi.
$$

Again, all maps stay the same except those now pointing into $i$; these are replaced by the compositions of the inclusions $V_k \to \bigoplus_{i \to j} V_j$ with the natural map $\bigoplus_{i \to j} V_j \to \bigoplus_{i \to j} V_j / \operatorname{Im} \psi$.

