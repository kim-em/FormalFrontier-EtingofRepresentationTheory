Let $B = \bigoplus_{j>1} V_j$, $B' = \bigoplus_{j>1} V'_j$; then we have $V = V_1 \oplus B = V'_1 \oplus B'$. Consider the map $h : B \to B'$ defined as a composition of the natural maps $B \to V \to B'$ attached to these decompositions. We claim that $h$ is an isomorphism. To show this, it suffices to show that $\ker h = 0$ (as $h$ is a map between spaces of the same dimension). Assume that $v \in \ker h \subset B$. Then $v \in V'_1$. On the other hand, the projection of $v$ to $V_1$ is zero, so $gv = 0$. Since $g$ is an isomorphism, we get $v = 0$, as desired.

Now by the induction assumption, $m = n$, and $V_j \cong V'_{\sigma(j)}$ for some permutation $\sigma$ of $2, \ldots, n$. The theorem is proved. $\square$

**Problem 3.8.3.** The above proof of Lemma 3.8.2 uses the condition that $k$ is an algebraically closed field. Prove Lemma 3.8.2 (and hence the Krull-Schmidt theorem) without this condition.

