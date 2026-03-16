
**Problem 2.13.1.** It is known that if $A$ and $B$ are two polygons of the same area, then $A$ can be cut by finitely many straight cuts into pieces from which one can make $B$ (check it — it is fun!). David Hilbert asked in 1900 whether it is true for polyhedra in three dimensions. In particular, is it true for a cube and a regular tetrahedron of the same volume?

The answer is "no", as was found by Dehn in 1901. The proof is very beautiful. Namely, to any polyhedron $A$, let us attach its "Dehn invariant" $D(A)$ in $V = \mathbb{R} \otimes (\mathbb{R}/\mathbb{Q})$ (the tensor product of $\mathbb{Q}$-vector spaces). Namely,

$$D(A) = \sum_a l(a) \otimes \frac{\beta(a)}{\pi},$$

where $a$ runs over edges of $A$ and $l(a), \beta(a)$ are the length of $a$ and the dihedral angle at $a$.
(a) Show that if you cut $A$ into $B$ and $C$ by a straight cut, then $D(A) = D(B) + D(C)$.

(b) Show that $\alpha = \arccos(1/3)/\pi$ is not a rational number.

Hint: Assume that $\alpha = 2m/n$, for integers $m, n$. Deduce that roots of the equation $x + x^{-1} = 2/3$ are roots of unity of degree $n$. Then show that $x^k + x^{-k}$ has denominator $3^k$ and get a contradiction.

(c) Using (a) and (b), show that the answer to Hilbert's question is negative. (Compute the Dehn invariant of the regular tetrahedron and the cube.)

