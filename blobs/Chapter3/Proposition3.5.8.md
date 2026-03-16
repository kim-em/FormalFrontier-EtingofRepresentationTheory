**Proposition 3.5.8.** *For a finite dimensional algebra $A$, the following are equivalent:*

*(1) $A$ is semisimple.*

*(2) $\sum_i (\dim V_i)^2 = \dim A$, where the $V_i$'s are the irreducible representations of $A$.*

*(3) $A \cong \bigoplus_i \operatorname{Mat}_{d_i}(k)$ for some $d_i$.*

*(4) Any finite dimensional representation of $A$ is completely reducible (that is, isomorphic to a direct sum of irreducible representations).*

*(5) $A$ is a completely reducible representation of $A$.*

**Proof.** As $\dim A - \dim \operatorname{Rad}(A) = \sum_i (\dim V_i)^2$, clearly $\dim A = \sum_i (\dim V_i)^2$ if and only if $\operatorname{Rad}(A) = 0$. Thus, $(1) \Leftrightarrow (2)$.

By Theorem 3.5.4, if $\operatorname{Rad}(A) = 0$, then clearly $A \cong \bigoplus_i \operatorname{Mat}_{d_i}(k)$ for $d_i = \dim V_i$. Thus, $(1) \Rightarrow (3)$.

Next, $(3) \Rightarrow (4)$ by Theorem 3.3.1. Clearly $(4) \Rightarrow (5)$.

[^4]: In particular, the algebra $A = 0$ is semisimple, although it is not simple. Every representation of this algebra is zero, so it does not have any irreducible or indecomposable representations. It is, nevertheless, a direct sum of an (empty) collection of matrix algebras.
To see that $(5) \Rightarrow (1)$, note that if $A$ is a completely reducible representation of $A$, then each element of $\operatorname{Rad}(A)$ kills it, but the only element that kills $1 \in A$ is $0$; thus $\operatorname{Rad}(A) = 0$, so $A$ is semisimple. $\square$

