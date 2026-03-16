**Lemma 5.13.1.** *Let $x \in \mathbb{C}[S_n]$. Then $a_\lambda x b_\lambda = \ell_\lambda(x) c_\lambda$, where $\ell_\lambda$ is a linear function.*

**Proof.** If $g \in P_\lambda Q_\lambda$, then $g$ has a unique representation as $pq$, $p \in P_\lambda$, $q \in Q_\lambda$, so $a_\lambda g b_\lambda = (-1)^q c_\lambda$. Thus, to prove the required statement, we need to show that if $g$ is a permutation which is not in $P_\lambda Q_\lambda$, then $a_\lambda g b_\lambda = 0$.

To show this, it is sufficient to find a transposition $t$ such that $t \in P_\lambda$ and $g^{-1}tg \in Q_\lambda$; then

$$a_\lambda g b_\lambda = a_\lambda t g b_\lambda = a_\lambda g (g^{-1}tg) b_\lambda = -a_\lambda g b_\lambda,$$

so $a_\lambda g b_\lambda = 0$. In other words, we have to find two elements $i, j$ standing in the same row in the tableau $T = T_\lambda$ and in the same column in the tableau $T' = gT$ (where $gT$ is the tableau of the same shape as $T$ obtained by permuting the entries of $T$ by the permutation $g$). Thus, it suffices to show that if such a pair does not exist, then $g \in P_\lambda Q_\lambda$, i.e., there exists $p \in P_\lambda$, $q' \in Q'_\lambda := gQ_\lambda g^{-1}$ such that $pT = q'T'$ (so that $g = pq^{-1}$, $q = g^{-1}q'g \in Q_\lambda$).
