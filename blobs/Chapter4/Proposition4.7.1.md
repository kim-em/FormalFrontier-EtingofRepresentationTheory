**Proposition 4.7.1.** *(i) Matrix elements of nonisomorphic irreducible representations are orthogonal in $F(G, \mathbb{C})$ under the form $(f, g) = \frac{1}{|G|} \sum_{x \in G} f(x)\overline{g(x)}$.*

*(ii) One has $(t^V_{ij}, t^V_{i'j'}) = \delta_{ii'}\delta_{jj'} \cdot \frac{1}{\dim V}$.*

*Thus, matrix elements of irreducible representations of $G$ form an orthogonal basis of $F(G, \mathbb{C})$.*

**Proof.** Let $V$ and $W$ be two irreducible representations of $G$. Take $\{v_i\}$ to be an orthonormal basis of $V$ and $\{w_i\}$ to be an orthonormal basis of $W$ under their positive definite invariant Hermitian forms. Let $w^*_i \in W^*$ be the linear function on $W$ defined by taking the inner product with $w_i$: $w^*_i(u) = (u, w_i)$. Then for $x \in G$ we have
$(xw^*_i, w^*_j) = \overline{(xw_i, w_j)}$. Therefore, putting $P = \frac{1}{|G|} \sum_{x \in G} x$, we have

$$(t^V_{ij}, t^W_{i'j'}) = |G|^{-1} \sum_{x \in G} (xv_i, v_j)\overline{(xw_{i'}, w_{j'})}$$

$$= |G|^{-1} \sum_{x \in G} (xv_i, v_j)(xw^*_{i'}, w^*_{j'}) = (P(v_i \otimes w^*_{i'}), v_j \otimes w^*_{j'}).$$

If $V \neq W$, this is zero, since $P$ projects to the trivial representation, which does not occur in $V \otimes W^*$. If $V = W$, we need to consider $(P(v_i \otimes v^*_{i'}), v_j \otimes v^*_{j'})$. We have a $G$-invariant decomposition

$$V \otimes V^* = \mathbb{C} \oplus L,$$

$$\mathbb{C} = \operatorname{span}(\sum v_k \otimes v^*_k),$$

$$L = \operatorname{span}_{a: \sum_k a_{kk} = 0}(\sum_{k,l} a_{kl} v_k \otimes v^*_l),$$

and $P$ projects to the first summand along the second one. The projection of $v_i \otimes v^*_{i'}$ to $\mathbb{C} \subset \mathbb{C} \oplus L$ is thus

$$\frac{\delta_{ii'}}{\dim V} \sum v_k \otimes v^*_k.$$

This shows that

$$(P(v_i \otimes v^*_{i'}), v_j \otimes v^*_{j'}) = \frac{\delta_{ii'}\delta_{jj'}}{\dim V},$$

which finishes the proof of (i) and (ii). The last statement follows immediately from the sum of squares formula. $\square$

