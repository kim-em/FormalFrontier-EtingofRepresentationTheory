**Theorem 8.1.5.** *The following properties of $I$ are equivalent:*

*(i) If $\alpha : N \to M$ is an injective morphism and $\nu : N \to I$ is any morphism, then there exists a morphism $\mu : M \to I$ such that $\mu \circ \alpha = \nu$.*

*(ii) Any injective morphism $\alpha : I \to M$ splits; i.e., there exists $\mu : M \to I$ such that $\mu \circ \alpha = \operatorname{id}$.*
*(iii) The functor $\operatorname{Hom}_A(?, I)$ on the category of A-modules is exact.*

**Proof.** The proof of the implications "(i) implies (ii)" and "(iii) implies (i)" is similar to the proof of Theorem 8.1.1. Let us prove that (ii) implies (iii). Let

$$
0 \to N \to M \to K \to 0
$$

be an exact sequence. Denote the embedding $N \to M$ by $j$. Consider the corresponding sequence

$$
0 \to \operatorname{Hom}(K, I) \to \operatorname{Hom}(M, I) \to \operatorname{Hom}(N, I) \to 0.
$$

Let $f \in \operatorname{Hom}(N, I)$, and define the module $E := (M \oplus I)/N$, where $N$ is embedded into $M \oplus I$ via $x \mapsto (j(x), -f(x))$. Clearly, we have an inclusion $I \to E$, since the image of $N \oplus I$ in $E$ is naturally identified with $I$. So there is a splitting $E \to I$ of this inclusion, i.e., a map $M \oplus I \to I$, $(m, i) \mapsto g(m) + i$ such that $g(j(x)) - f(x) = 0$. This means that the map $j^* : \operatorname{Hom}(M, I) \to \operatorname{Hom}(N, I)$ is surjective, i.e., the functor $\operatorname{Hom}(?, I)$ is exact, as desired. $\square$

