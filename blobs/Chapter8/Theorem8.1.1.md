**Theorem 8.1.1.** *The following properties of $P$ are equivalent:*

*(i) If $\alpha : M \to N$ is a surjective morphism and $\nu : P \to N$ is any morphism, then there exists a morphism $\mu : P \to M$ such that $\alpha \circ \mu = \nu$.*

*(ii) Any surjective morphism $\alpha : M \to P$ splits; i.e., there exists $\mu : P \to M$ such that $\alpha \circ \mu = \operatorname{id}$.*

*(iii) There exists another $A$-module $Q$ such that $P \oplus Q$ is a free $A$-module, i.e., a direct sum of copies of $A$.*

*(iv) The functor $\operatorname{Hom}_A(P, ?)$ on the category of $A$-modules is exact.*

**Proof.** To prove that (i) implies (ii), take $N = P$. To prove that (ii) implies (iii), take $M$ to be free (this can always be done since any module is a quotient of a free module). To prove that (iii) implies (iv), note that the functor $\operatorname{Hom}_A(P, ?)$ is exact if $P$ is free (as
$\operatorname{Hom}_A(A, N) = N$), so the statement follows, since if the direct sum of two complexes is exact, then each of them is exact. To prove that (iv) implies (i), let $K$ be the kernel of the map $\alpha$, and apply the exact functor $\operatorname{Hom}_A(P, ?)$ to the exact sequence

$$0 \to K \to M \to N \to 0.$$

$\square$

