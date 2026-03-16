**Example 7.2.2.** 1. A (locally small) category $\mathcal{C}$ with one object $X$ is the same thing as a monoid. A functor between such categories is a homomorphism of monoids.

2. Forgetful functors

$$
\mathbf{Groups} \to \mathbf{Sets}, \qquad \mathbf{Rings} \to \mathbf{AbelianGroups}.
$$

3. The opposite category of a given category $\mathcal{C}$, denoted by $\mathcal{C}^{\mathrm{op}}$, is the same category with the order of arrows and compositions reversed. Then $V \mapsto V^*$ is a functor $\mathbf{Vect}_k \to \mathbf{Vect}_k^{\mathrm{op}}$.

4. The Hom functors: if $\mathcal{C}$ is a locally small category, then we have the functor $\mathcal{C} \to \mathbf{Sets}$ given by $Y \mapsto \operatorname{Hom}(X, Y)$ and $\mathcal{C}^{\mathrm{op}} \to \mathbf{Sets}$ given by $Y \mapsto \operatorname{Hom}(Y, X)$.

5. The assignment $X \mapsto \operatorname{Fun}(X, \mathbb{Z})$ is a functor $\mathbf{Sets} \to \mathbf{Rings}^{\mathrm{op}}$.

6. Let $Q$ be a quiver. Consider the category $\mathcal{C}(Q)$ whose objects are the vertices and morphisms are oriented paths between them. Then functors from $\mathcal{C}(Q)$ to $\mathbf{Vect}_k$ are representations of $Q$ over $k$.

7. Let $K \subset G$ be groups. Then we have the induction functor $\operatorname{Ind}_K^G : \operatorname{Rep}(K) \to \operatorname{Rep}(G)$ and the restriction functor $\operatorname{Res}_K^G : \operatorname{Rep}(G) \to \operatorname{Rep}(K)$.

8. We have an obvious notion of the Cartesian product of categories (obtained by taking the Cartesian products of the classes of objects and morphisms of the factors). The functors of direct sum and tensor product are then functors $\mathbf{Vect}_k \times \mathbf{Vect}_k \to \mathbf{Vect}_k$. Also the operations $V \mapsto V^{\otimes n}$, $V \mapsto S^n V$, $V \mapsto \wedge^n V$ are functors on $\mathbf{Vect}_k$. More generally, if $\pi$ is a representation of $S_n$, we have functors $V \mapsto \operatorname{Hom}_{S_n}(\pi, V^{\otimes n})$. Such functors are called the **Schur functors**. Thus, the irreducible Schur functors are labeled by Young diagrams.

9. The reflection functors $F_i^\pm : \operatorname{Rep}(Q) \to \operatorname{Rep}(\overline{Q}_i)$ are functors between representation categories of quivers.
