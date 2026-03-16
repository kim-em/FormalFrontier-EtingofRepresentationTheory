**Lemma 3.1.6.** *There exists a subset $J \subseteq I$ such that $V_J := \bigoplus_{i \in J} V_i$ is mapped isomorphically by $f$ onto $U$.*

**Proof.** Let $J$ be a maximal subset such that $f|_{V_J}$ is injective. If $f(V_J) \neq U$, then there exists $i \in I$ such that $f(V_i)$ is not contained in $f(V_J)$. Then the map $V_i \to U/f(V_J)$ is nonzero, and hence injective by Schur's lemma. Let $J' = J \cup \{i\}$; then $f$ is injective on $V_{J'}$, contradicting the maximality of $J$, which proves the lemma. $\square$

