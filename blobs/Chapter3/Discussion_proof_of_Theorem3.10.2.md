**Proof.** (i) By the density theorem, the maps $A \to \operatorname{End} V$ and $B \to \operatorname{End} W$ are surjective. Therefore, the map $A \otimes B \to \operatorname{End} V \otimes \operatorname{End} W = \operatorname{End}(V \otimes W)$ is surjective. Thus, $V \otimes W$ is irreducible.

(ii) First we show the existence of $V$ and $W$. Let $A', B'$ be the images of $A, B$ in $\operatorname{End} M$. Then $A', B'$ are finite dimensional algebras, and $M$ is a representation of $A' \otimes B'$, so we may assume without loss of generality that $A$ and $B$ are finite dimensional.

In this case, we claim that

$$\operatorname{Rad}(A \otimes B) = \operatorname{Rad}(A) \otimes B + A \otimes \operatorname{Rad}(B).$$
Indeed, denote the latter by $J$. Then $J$ is a nilpotent ideal in $A \otimes B$, as $\operatorname{Rad}(A)$ and $\operatorname{Rad}(B)$ are nilpotent. On the other hand, $(A \otimes B)/J = (A/\operatorname{Rad}(A)) \otimes (B/\operatorname{Rad}(B))$, which is a product of two semisimple algebras, hence semisimple. This implies $J \supset \operatorname{Rad}(A \otimes B)$. Altogether, by Proposition 3.5.3, we see that $J = \operatorname{Rad}(A \otimes B)$, proving the claim.

Thus, we see that

$$(A \otimes B)/\operatorname{Rad}(A \otimes B) = A/\operatorname{Rad}(A) \otimes B/\operatorname{Rad}(B).$$

Now, $M$ is an irreducible representation of $(A \otimes B)/\operatorname{Rad}(A \otimes B)$, so it is clearly of the form $M = V \otimes W$, where $V$ is an irreducible representation of $A/\operatorname{Rad}(A)$ and $W$ is an irreducible representation of $B/\operatorname{Rad}(B)$. Also, $V, W$ are uniquely determined by $M$ (as all of the algebras involved are direct sums of matrix algebras). $\square$
