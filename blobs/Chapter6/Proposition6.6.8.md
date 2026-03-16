**Proposition 6.6.8.** *Let $Q$ be a quiver and let $V$ be a representation of $Q$.*

*(1) Let $i \in Q$ be a sink and let $V$ be surjective at $i$. Then*

$$
d(F_i^+ V) = s_i(d(V)).
$$

*(2) Let $i \in Q$ be a source and let $V$ be injective at $i$. Then*

$$
d(F_i^- V) = s_i(d(V)).
$$

**Proof.** We only prove the first statement; the second one follows similarly. Let $i \in Q$ be a sink and let

$$
\varphi : \bigoplus_{j \to i} V_j \to V_i
$$

be surjective. Let $K = \ker \varphi$. Then

$$
\dim K = \sum_{j \to i} \dim V_j - \dim V_i.
$$

Therefore we get

$$
\left( d(F_i^+ V) - d(V) \right)_i = \sum_{j \to i} \dim V_j - 2 \dim V_i = -B(d(V), \alpha_i)
$$

and

$$
\left( d(F_i^+ V) - d(V) \right)_j = 0, \quad j \neq i.
$$
This implies

$$
d(F_i^+ V) - d(V) = -B(d(V), \alpha_i) \alpha_i
$$

$$
\iff d(F_i^+ V) = d(V) - B(d(V), \alpha_i) \alpha_i = s_i(d(V)).
$$

$\square$

