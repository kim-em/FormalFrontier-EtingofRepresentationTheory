**Theorem 5.18.1.** *Let $A$, $B$ be two subalgebras of the algebra $\operatorname{End} E$ of endomorphisms of a finite dimensional vector space $E$, such that $A$ is semisimple and $B = \operatorname{End}_A E$. Then:*

*(i) $A = \operatorname{End}_B E$ (i.e., the centralizer of the centralizer of $A$ is $A$).*

*(ii) $B$ is semisimple.*

*(iii) As a representation of $A \otimes B$, $E$ decomposes as*

$$
E = \bigoplus_{i \in I} V_i \otimes W_i,
$$

*where $V_i$ are all the irreducible representations of $A$ and $W_i$ are all the irreducible representations of $B$. In particular, we have a natural bijection between irreducible representations of $A$ and $B$.*

**Proof.** Since $A$ is semisimple, we have a natural decomposition $E = \bigoplus_{i \in I} V_i \otimes W_i$, where $W_i := \operatorname{Hom}_A(V_i, E)$ and $A = \bigoplus_i \operatorname{End} V_i$. Note that $W_i \neq 0$, since the action of $A$ on $E$ is faithful. Therefore, by
Schur's lemma, $B = \operatorname{End}_A(E)$ is naturally identified with $\bigoplus_i \operatorname{End}(W_i)$. This implies all the statements of the theorem. $\square$

