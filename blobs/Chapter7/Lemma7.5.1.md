**Lemma 7.5.1** (The Yoneda Lemma). *If a functor $F$ is represented by an object $X$, then $X$ is unique up to a unique isomorphism. I.e., if $X, Y$ are two objects in $\mathcal{C}$, then for any isomorphism of functors*
$\phi : \operatorname{Hom}(X, ?) \to \operatorname{Hom}(Y, ?)$ *there is a unique isomorphism $a_\phi : X \to Y$ inducing $\phi$.*

**Proof (Sketch).** One sets $a_\phi = \phi_Y^{-1}(1_Y)$ and shows that it is invertible by constructing the inverse, which is $a_\phi^{-1} = \phi_X(1_X)$. It remains to show that the composition both ways is the identity, which we will omit here. This establishes the existence of $a_\phi$. Its uniqueness is verified in a straightforward manner. $\square$

