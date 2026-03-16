**Problem 2.11.6.** Throughout this problem, we let $k$ be an arbitrary field (not necessarily of characteristic zero and not necessarily algebraically closed).

If $A$ and $B$ are two $k$-algebras, then an $(A, B)$**-bimodule** will mean a $k$-vector space $V$ with both a left $A$-module structure and a right $B$-module structure which satisfy $(av) b = a (vb)$ for any $v \in V$, $a \in A$, and $b \in B$. Note that both the notions of "left $A$-module" and "right $A$-module" are particular cases of the notion of bimodules; namely, a left $A$-module is the same as an $(A, k)$-bimodule, and a right $A$-module is the same as a $(k, A)$-bimodule.

Let $B$ be a $k$-algebra, $W$ a left $B$-module, and $V$ a right $B$-module. We denote by $V \otimes_B W$ the $k$-vector space $(V \otimes_k W) / \langle vb \otimes w - v \otimes bw \mid v \in V, w \in W, b \in B \rangle$. We denote the projection of a pure tensor $v \otimes w$ (with $v \in V$ and $w \in W$) onto the space $V \otimes_B W$ by $v \otimes_B w$. (Note that this tensor product $V \otimes_B W$ is the one defined in Remark 2.11.4.)

If, additionally, $A$ is another $k$-algebra and if the right $B$-module structure on $V$ is part of an $(A, B)$-bimodule structure, then $V \otimes_B W$ becomes a left $A$-module by $a (v \otimes_B w) = av \otimes_B w$ for any $a \in A$, $v \in V$, and $w \in W$.

Similarly, if $C$ is another $k$-algebra, and if the left $B$-module structure on $W$ is part of a $(B, C)$-bimodule structure, then $V \otimes_B W$ becomes a right $C$-module by $(v \otimes_B w) c = v \otimes_B wc$ for any $c \in C$, $v \in V$, and $w \in W$.
If $V$ is an $(A, B)$-bimodule and $W$ is a $(B, C)$-bimodule, then these two structures on $V \otimes_B W$ can be combined into one $(A, C)$-bimodule structure on $V \otimes_B W$.

(a) Let $A$, $B$, $C$, $D$ be four algebras. Let $V$ be an $(A, B)$-bimodule, $W$ a $(B, C)$-bimodule, and $X$ a $(C, D)$-bimodule. Prove that $(V \otimes_B W) \otimes_C X \cong V \otimes_B (W \otimes_C X)$ as $(A, D)$-bimodules. The isomorphism (from left to right) is given by the formula

$$
(v \otimes_B w) \otimes_C x \mapsto v \otimes_B (w \otimes_C x)
$$

for all $v \in V$, $w \in W$, and $x \in X$.

(b) If $A$, $B$, $C$ are three algebras and if $V$ is an $(A, B)$-bimodule and $W$ an $(A, C)$-bimodule, then the vector space $\operatorname{Hom}_A(V, W)$ (the space of all left $A$-linear homomorphisms from $V$ to $W$) canonically becomes a $(B, C)$-bimodule by setting $(bf)(v) = f(vb)$ for all $b \in B$, $f \in \operatorname{Hom}_A(V, W)$, and $v \in V$ and setting $(fc)(v) = f(v) c$ for all $c \in C$, $f \in \operatorname{Hom}_A(V, W)$ and $v \in V$.

Let $A$, $B$, $C$, $D$ be four algebras. Let $V$ be a $(B, A)$-bimodule, $W$ a $(C, B)$-bimodule, and $X$ a $(C, D)$-bimodule. Prove that

$$
\operatorname{Hom}_B(V, \operatorname{Hom}_C(W, X)) \cong \operatorname{Hom}_C(W \otimes_B V, X)
$$

as $(A, D)$-bimodules. The isomorphism (from left to right) is given by

$$
f \mapsto (w \otimes_B v \mapsto f(v) w)
$$

