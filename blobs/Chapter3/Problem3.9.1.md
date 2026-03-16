**Problem 3.9.1. Extensions of representations.** Let $A$ be an algebra, and let $V, W$ be a pair of representations of $A$. We would like to classify representations $U$ of $A$ such that $V$ is a subrepresentation of $U$ and $U/V = W$. Of course, there is an obvious example $U = V \oplus W$, but are there any others?

Suppose we have a representation $U$ as above. As a vector space, it can be (nonuniquely) identified with $V \oplus W$, so that for any $a \in A$ the corresponding operator $\rho_U(a)$ has block triangular form

$$\rho_U(a) = \begin{pmatrix} \rho_V(a) & f(a) \\ 0 & \rho_W(a) \end{pmatrix},$$

where $f : A \to \operatorname{Hom}_k(W, V)$ is a linear map.

(a) What is the necessary and sufficient condition on $f(a)$ under which $\rho_U(a)$ is a representation? Maps $f$ satisfying this condition are
called **1-cocycles** (of $A$ with coefficients in $\operatorname{Hom}_k(W, V)$). They form a vector space denoted by $Z^1(W, V)$.

(b) Let $X : W \to V$ be a linear map. The coboundary of $X$, $dX$, is defined to be the function $A \to \operatorname{Hom}_k(W, V)$ given by $dX(a) = \rho_V(a)X - X\rho_W(a)$. Show that $dX$ is a cocycle which vanishes if and only if $X$ is a homomorphism of representations. Thus coboundaries form a subspace $B^1(W, V) \subset Z^1(W, V)$, which is isomorphic to $\operatorname{Hom}_k(W, V)/\operatorname{Hom}_A(W, V)$. The quotient $Z^1(W, V)/B^1(W, V)$ is denoted by $\operatorname{Ext}^1(W, V)$.

(c) Show that if $f, f' \in Z^1(W, V)$ and $f - f' \in B^1(W, V)$, then the corresponding extensions $U, U'$ are isomorphic representations of $A$. Conversely, if $\phi : U \to U'$ is an isomorphism such that

$$\phi = \begin{pmatrix} 1_V & * \\ 0 & 1_W \end{pmatrix},$$

then $f - f' \in B^1(V, W)$. Thus, the space $\operatorname{Ext}^1(W, V)$ "classifies" extensions of $W$ by $V$.

(d) Assume that $W, V$ are finite dimensional irreducible representations of $A$. For any $f \in \operatorname{Ext}^1(W, V)$, let $U_f$ be the corresponding extension. Show that $U_f$ is isomorphic to $U_{f'}$ as representations if and only if $f$ and $f'$ are proportional. Thus isomorphism classes (as representations) of nontrivial extensions of $W$ by $V$ (i.e., those not isomorphic to $W \oplus V$) are parametrized by the projective space $\mathbb{P}\operatorname{Ext}^1(W, V)$. In particular, every extension is trivial if and only if $\operatorname{Ext}^1(W, V) = 0$.

