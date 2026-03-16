**Problem 9.6.5.** Let $G : B\text{-fmod} \to \mathcal{C}$ be the functor defined by $G(X) := P \otimes_B X$, where $P \otimes_B X$ is the cokernel of the morphism $\psi : P \otimes B \otimes X \to P \otimes X$ given by $\psi = a_P \otimes \operatorname{Id} - \operatorname{Id} \otimes a_X$ (where $a_P : P \otimes B \to P$, $a_X : B \otimes X \to X$ are the morphisms representing the actions of $B$ on $P$ and $X$).

(i) Show that $F \circ G \cong \operatorname{Id}$. That is, for every $X \in B\text{-fmod}$, show that $X$ is naturally isomorphic to $\operatorname{Hom}(P, P \otimes_B X)$. (For this you should only need that $P$ is a nonzero projective object.)

(ii) For any $X \in \mathcal{C}$, construct a natural morphism

$$
\xi : P \otimes_B \operatorname{Hom}(P, X) \to X,
$$

and show that it is surjective.

(iii) Show that $G \circ F \cong \operatorname{Id}$. To this end, consider the short exact sequence

$$
0 \to K \to P \otimes_B \operatorname{Hom}(P, X) \to X \to 0,
$$

where the third map is $\xi$. Apply the functor $F$ to this sequence and use (i) to conclude that $K = 0$ and hence $\xi$ is an isomorphism. Conclude that the functors $G$ and $F$ are quasi-inverse to each other and hence are equivalences of categories.
