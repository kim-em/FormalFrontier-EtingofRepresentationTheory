**Theorem 4.2.1.** *If the characteristic of $k$ does not divide $|G|$, characters of irreducible representations of $G$ form a basis in the space $F_c(G, k)$.*
**Proof.** By the Maschke theorem, $k[G]$ is semisimple, so by Theorem 3.6.2, the characters are linearly independent and are a basis of $(A/[A, A])^*$, where $A = k[G]$. It suffices to note that, as vector spaces over $k$,

$$(A/[A, A])^* \cong \{\varphi \in \operatorname{Hom}_k(k[G], k) \mid gh - hg \in \ker \varphi \ \forall g, h \in G\}$$

$$\cong \{f \in F(G, k) \mid f(gh) = f(hg) \ \forall g, h \in G\},$$

which is precisely $F_c(G, k)$. $\square$

