Let $G, A$ be groups and let $\phi : G \to \operatorname{Aut}(A)$ be a homomorphism. For $a \in A$, denote $\phi(g)a$ by $g(a)$. The **semidirect product** $G \ltimes A$ is defined to be the product $A \times G$ with multiplication law

$$(a_1, g_1)(a_2, g_2) = (a_1 g_1(a_2), g_1 g_2).$$

Clearly, $G$ and $A$ are subgroups of $G \ltimes A$ in a natural way.

We would like to study irreducible complex representations of $G \ltimes A$. For simplicity, let us do it when $A$ is abelian.

In this case, irreducible representations of $A$ are 1-dimensional and form the character group $A^\vee$, which carries an action of $G$. Let $O$ be an orbit of this action, $x \in O$ a chosen element, and $G_x$ the
stabilizer of $x$ in $G$. Let $U$ be an irreducible representation of $G_x$. Then we define a representation $V_{(O,U)}$ of $G \ltimes A$ as follows.

As a representation of $G$, we set

$$
V_{(O,x,U)} = \operatorname{Ind}_{G_x}^G U = \{f : G \to U | f(hg) = hf(g), h \in G_x\}.
$$

Next, we introduce an additional action of $A$ on this space by $(af)(g) = x(g(a))f(g)$. Then it is easy to check that these two actions combine into an action of $G \ltimes A$. Also, it is clear that this representation does not really depend on the choice of $x$, in the following sense. Let $x, y \in O$ and $g \in G$ be such that $gx = y$, and let $g(U)$ be the representation of $G_y$ obtained from the representation $U$ of $G_x$ by the action of $g$. Then $V_{(O,x,U)}$ is (naturally) isomorphic to $V_{(O,y,g(U))}$. Thus we will denote $V_{(O,x,U)}$ by $V_{(O,U)}$ (remembering, however, that $x$ has been fixed).

