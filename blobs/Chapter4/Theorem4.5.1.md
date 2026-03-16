**Theorem 4.5.1.** *For any representations $V, W$*

$$(\chi_V, \chi_W) = \dim \mathrm{Hom}_G(W, V),$$

*and*

$$(\chi_V, \chi_W) = \begin{cases} 1, & \text{if } V \cong W, \\ 0, & \text{if } V \not\cong W \end{cases}$$

*if $V, W$ are irreducible.*

**Proof.** By the definition

$$(\chi_V, \chi_W) = \frac{1}{|G|} \sum_{g \in G} \chi_V(g)\overline{\chi_W(g)} = \frac{1}{|G|} \sum_{g \in G} \chi_V(g)\chi_{W^*}(g)$$

$$= \frac{1}{|G|} \sum_{g \in G} \chi_{V \otimes W^*}(g) = \operatorname{Tr}|_{V \otimes W^*}(P),$$

where $P = \frac{1}{|G|} \sum_{g \in G} g \in Z(\mathbb{C}[G])$. (Here $Z(\mathbb{C}[G])$ denotes the center of $\mathbb{C}[G]$.) If $X$ is an irreducible representation of $G$, then

$$P|_X = \begin{cases} \mathrm{Id} & \text{if } X = \mathbb{C}, \\ 0, & X \neq \mathbb{C}. \end{cases}$$

Therefore, for any representation $X$ the operator $P|_X$ is the $G$-invariant projector onto the subspace $X^G$ of $G$-invariants in $X$. Thus,

$$\operatorname{Tr}|_{V \otimes W^*}(P) = \dim \mathrm{Hom}_G(\mathbb{C}, V \otimes W^*)$$

$$= \dim(V \otimes W^*)^G = \dim \mathrm{Hom}_G(W, V).$$

$\square$

