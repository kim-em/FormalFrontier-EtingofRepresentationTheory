**Definition 7.1.1.** A **category** $\mathcal{C}$ is the following data:

(i) A class of objects $Ob(\mathcal{C})$.
(ii) For every objects $X, Y \in Ob(\mathcal{C})$, the class $\operatorname{Hom}_\mathcal{C}(X, Y) = \operatorname{Hom}(X, Y)$ of morphisms (or arrows) from $X, Y$ (for $f \in \operatorname{Hom}(X, Y)$, one may write $f : X \to Y$).

(iii) For any objects $X, Y, Z \in Ob(\mathcal{C})$, a composition map

$$
\operatorname{Hom}(Y, Z) \times \operatorname{Hom}(X, Y) \to \operatorname{Hom}(X, Z), \quad (f, g) \mapsto f \circ g.
$$

This data is required to satisfy the following axioms:

1. The composition is associative, i.e., $(f \circ g) \circ h = f \circ (g \circ h)$.

2. For each $X \in Ob(\mathcal{C})$, there is a morphism $1_X \in \operatorname{Hom}(X, X)$, called the **unit morphism**, such that $1_X \circ f = f$ and $g \circ 1_X = g$ for any $f, g$ for which compositions make sense.

