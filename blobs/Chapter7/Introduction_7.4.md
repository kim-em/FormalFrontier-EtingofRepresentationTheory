## 7.4. Equivalence of categories

When two algebraic or geometric objects are isomorphic, it is usually not a good idea to say that they are equal (i.e., literally the same). The reason is that such objects are usually equal in many different ways, i.e., there are many ways to pick an isomorphism, but by saying that the objects are equal, we are misleading the reader or listener into thinking that we are providing a certain choice of the identification, which we actually do not do. A vivid example of this is a finite dimensional vector space $V$ and its dual space $V^*$.

For this reason, in category theory, most of the time one tries to avoid saying that two objects or two functors are equal. In particular, this applies to the definition of isomorphism of categories.

Namely, the naive notion of isomorphism of categories is defined in the obvious way: a functor $F : \mathcal{C} \to \mathcal{D}$ is an isomorphism if there exists $F^{-1} : \mathcal{D} \to \mathcal{C}$ such that $F \circ F^{-1}$ and $F^{-1} \circ F$ are equal to the identity functors. But this definition is not very useful. We might suspect so since we have used the word "equal" for objects of a category (namely, functors) which we are not supposed to do. In fact, here is an example of two categories which are "the same for all practical purposes" but are not isomorphic; it demonstrates the deficiency of our definition.

Namely, let $\mathcal{C}_1$ be the simplest possible category: $Ob(\mathcal{C}_1)$ consists of one object $X$, with $\operatorname{Hom}(X, X) = \{1_X\}$. Also, let $\mathcal{C}_2$ have two objects $X, Y$ and four morphisms: $1_X, 1_Y, a : X \to Y$, and $b : Y \to X$. So we must have $a \circ b = 1_Y$, $b \circ a = 1_X$.

It is easy to check that for any category $\mathcal{D}$, there is a natural bijection between the collections of isomorphism classes of functors $\mathcal{C}_1 \to \mathcal{D}$ and $\mathcal{C}_2 \to \mathcal{D}$ (both are identified with the collection of isomorphism classes of objects of $\mathcal{D}$). This is what we mean by saying that $\mathcal{C}_1$ and $\mathcal{C}_2$ are "the same for all practical purposes". Nevertheless they are not isomorphic, since $\mathcal{C}_1$ has one object and $\mathcal{C}_2$ has two objects (even though these two objects are isomorphic to each other).

This shows that we should adopt a more flexible and less restrictive notion of isomorphism of categories. This is accomplished by the definition of an equivalence of categories.
