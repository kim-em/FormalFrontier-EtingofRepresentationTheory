**Theorem 5.23.2.** *(i) Every finite dimensional algebraic representation of $GL(V)$ is completely reducible, and decomposes into summands of the form $L_\lambda$ (which are pairwise nonisomorphic).*

*(ii) (The Peter-Weyl theorem for $GL(V)$) Let $R$ be the algebra of polynomial functions on $GL(V)$. Then as a representation of $GL(V) \times GL(V)$ (with action $(\rho(g, h)\phi)(x) = \phi(g^{-1}xh)$, $g, h, x \in GL(V)$, $\phi \in R$), $R$ decomposes as*

$$
R = \bigoplus_\lambda L_\lambda^* \otimes L_\lambda,
$$

*where the summation runs over all $\lambda$.*
**Proof.** (i) Let $Y$ be an algebraic representation of $GL(V)$. We have an embedding $\xi : Y \to Y \otimes R$ given by $(u, \xi(v))(g) := u(gv)$, $u \in Y^*$. It is easy to see that $\xi$ is a homomorphism of representations (where the action of $GL(V)$ on the first component of $Y \otimes R$ is trivial). Thus, it suffices to prove the theorem for a subrepresentation $Y \subset R^m$. Now, every element of $R$ is a polynomial of $g_{ij}$ times a nonpositive power of $\det(g)$. Thus, $R$ is a quotient of a direct sum of representations of the form $S^r(V \otimes V^*) \otimes (\wedge^N V^*)^{\otimes s}$, where the group action on $V^*$ in the product $V \otimes V^*$ is trivial. So we may assume that $Y$ is contained in a quotient of a (finite) direct sum of such representations. Thus, $Y$ is contained in a direct sum of representations of the form $V^{\otimes n} \otimes (\wedge^N V^*)^{\otimes s}$, and we are done.

(ii) Let $Y$ be an algebraic representation of $GL(V)$, and let us regard $R$ as a representation of $GL(V)$ via $(\rho(h)\phi)(x) = \phi(xh)$. Then $\operatorname{Hom}_{GL(V)}(Y, R)$ is the space of polynomial functions $f$ on $GL(V)$ with values in $Y^*$ which are right $GL(V)$-equivariant (i.e., such that $f(xg) = g^{-1}f(x)$). This space is naturally identified with $Y^*$. Taking into account the proof of (i), we deduce that $R$ has the required decomposition, which is compatible with the second action of $GL(V)$ (by left multiplications). This implies the statement. $\square$

