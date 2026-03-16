**Example 7.3.2.** 1. Let $\mathbf{FVect}_k$ be the category of finite dimensional vector spaces over $k$. Then the functors id and $**$ on this category are isomorphic. The isomorphism is defined by the standard maps $a_V : V \to V^{**}$ given by $a_V(u)(f) = f(u)$, $u \in V$, $f \in V^*$. But these two functors are not isomorphic on the category of all vector spaces $\mathbf{Vect}_k$, since for an infinite dimensional vector space $V$, $V$ is not isomorphic to $V^{**}$.

2. Let $\mathbf{FVect}_k'$ be the category of finite dimensional $k$-vector spaces, where the morphisms are the isomorphisms. We have a functor $F$ from this category to itself sending any space $V$ to $V^*$ and any morphism $a$ to $(a^*)^{-1}$. This functor satisfies the property that $V$ is isomorphic to $F(V)$ for any $V$, but it is not isomorphic to the identity functor. This is because the isomorphism $V \mapsto F(V) = V^*$ cannot be chosen to be compatible with the action of $GL(V)$, as $V$ is not isomorphic to $V^*$ as a representation of $GL(V)$.

3. Let $A$ be an algebra over a field $k$, and let $F : A - \mathbf{mod} \to \mathbf{Vect}_k$ be the forgetful functor. Then as follows from Problem 2.3.17, $\operatorname{End} F = \operatorname{Hom}(F, F) = A$.

4. The set of endomorphisms of the identity functor on the category $A - \mathbf{mod}$ is the center of $A$ (check it!).
