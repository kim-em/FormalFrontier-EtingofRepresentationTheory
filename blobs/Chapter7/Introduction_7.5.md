## 7.5. Representable functors

A fundamental notion in category theory is that of a **representable functor**. Namely, let $\mathcal{C}$ be a (locally small) category, and let $F : \mathcal{C} \to \mathbf{Sets}$ be a functor. We say that $F$ is **representable** if there exists an object $X \in \mathcal{C}$ such that $F$ is isomorphic to the functor $\operatorname{Hom}(X, ?)$. More precisely, if we are given such an object $X$, together with an isomorphism $\xi : F \cong \operatorname{Hom}(X, ?)$, we say that the functor $F$ is **represented by** $X$ (using $\xi$).

In a similar way, one can talk about representable functors from $\mathcal{C}^{\mathrm{op}}$ to **Sets**. Namely, one calls such a functor representable if it is of the form $\operatorname{Hom}(?, X)$ for some object $X \in \mathcal{C}$, up to an isomorphism.

Not every functor is representable, but if a representing object $X$ exists, then it is unique. Namely, we have the following lemma.

