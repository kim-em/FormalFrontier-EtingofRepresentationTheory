**Example 4.8.1.** The following three character tables are of $Q_8$, $S_4$, and $A_5$, respectively:
| $Q_8$ | 1 | $-1$ | $i$ | $j$ | $k$ |
|---|---|---|---|---|---|
| # | 1 | 1 | 2 | 2 | 2 |
| $\mathbb{C}_{++}$ | 1 | 1 | 1 | 1 | 1 |
| $\mathbb{C}_{+-}$ | 1 | 1 | 1 | $-1$ | $-1$ |
| $\mathbb{C}_{-+}$ | 1 | 1 | $-1$ | 1 | $-1$ |
| $\mathbb{C}_{--}$ | 1 | 1 | $-1$ | $-1$ | 1 |
| $\mathbb{C}^2$ | 2 | $-2$ | 0 | 0 | 0 |

| $S_4$ | Id | (12) | (12)(34) | (123) | (1234) |
|---|---|---|---|---|---|
| # | 1 | 6 | 3 | 8 | 6 |
| $\mathbb{C}_+$ | 1 | 1 | 1 | 1 | 1 |
| $\mathbb{C}_-$ | 1 | $-1$ | 1 | 1 | $-1$ |
| $\mathbb{C}^2$ | 2 | 0 | 2 | $-1$ | 0 |
| $\mathbb{C}^3_+$ | 3 | $-1$ | $-1$ | 0 | 1 |
| $\mathbb{C}^3_-$ | 3 | 1 | $-1$ | 0 | $-1$ |

| $A_5$ | Id | (123) | (12)(34) | (12345) | (13245) |
|---|---|---|---|---|---|
| # | 1 | 20 | 15 | 12 | 12 |
| $\mathbb{C}$ | 1 | 1 | 1 | 1 | 1 |
| $\mathbb{C}^3_+$ | 3 | 0 | $-1$ | $\frac{1+\sqrt{5}}{2}$ | $\frac{1-\sqrt{5}}{2}$ |
| $\mathbb{C}^3_-$ | 3 | 0 | $-1$ | $\frac{1-\sqrt{5}}{2}$ | $\frac{1+\sqrt{5}}{2}$ |
| $\mathbb{C}^4$ | 4 | 1 | 0 | $-1$ | $-1$ |
| $\mathbb{C}^5$ | 5 | $-1$ | 1 | 0 | 0 |

Indeed, the computation of the characters of the 1-dimensional representations is straightforward.

The character of the 2-dimensional representation of $Q_8$ is obtained from the explicit formula (4.3.1) for this representation, or by using orthogonality.

For $S_4$, the 2-dimensional irreducible representation is obtained from the 2-dimensional irreducible representation of $S_3$ via the surjective homomorphism $S_4 \to S_3$, which allows one to obtain its character from the character table of $S_3$.

The character of the 3-dimensional representation $\mathbb{C}^3_+$ is computed from its geometric realization by rotations of the cube. Namely, by rotating the cube, $S_4$ permutes the main diagonals. Thus $(12)$ is
the rotation by $180^0$ around an axis that is perpendicular to two opposite edges, $(12)(34)$ is the rotation by $180^0$ around an axis that is perpendicular to two opposite faces, $(123)$ is the rotation around a main diagonal by $120^0$, and $(1234)$ is the rotation by $90^0$ around an axis that is perpendicular to two opposite faces; this allows us to compute the traces easily, using the fact that the trace of a rotation by the angle $\phi$ in $\mathbb{R}^3$ is $1 + 2\cos\phi$. Now the character of $\mathbb{C}^3_-$ is found by multiplying the character of $\mathbb{C}^3_+$ by the character of the sign representation.

Finally, we explain how to obtain the character table of $A_5$ (even permutations of five items). The group $A_5$ is the group of rotations of the regular icosahedron. Thus it has a 3-dimensional "rotation representation" $\mathbb{C}^3_+$, in which $(12)(34)$ is the rotation by $180^0$ around an axis perpendicular to two opposite edges, $(123)$ is the rotation by $120^0$ around an axis perpendicular to two opposite faces, and $(12345)$, $(13254)$ are the rotations by $72^0$, respectively $144^0$, around axes going through two opposite vertices. The character of this representation is computed from this description in a straightforward way.

Another representation of $A_5$, which is also 3-dimensional, is $\mathbb{C}^3_+$ twisted by the automorphism of $A_5$ given by conjugation by $(12)$ inside $S_5$. This representation is denoted by $\mathbb{C}^3_-$. It has the same character as $\mathbb{C}^3_+$, except that the conjugacy classes $(12345)$ and $(13245)$ are interchanged.

There are two remaining irreducible representations, and by the sum of squares formula their dimensions are 4 and 5. So we call them $\mathbb{C}^4$ and $\mathbb{C}^5$.

The representation $\mathbb{C}^4$ is realized on the space of functions on the set $\{1, 2, 3, 4, 5\}$ with zero sum of values, where $A_5$ acts by permutations (check that it is irreducible!). The character of this representation is equal to the character of the 5-dimensional permutation representation minus the character of the 1-dimensional trivial representation (constant functions). The former at an element $g$ is equal to the number of items among 1, 2, 3, 4, 5 which are fixed by $g$.

The representation $\mathbb{C}^5$ is realized on the space of functions on pairs of opposite vertices of the icosahedron which has zero sum of
values (check that it is irreducible!). The character of this representation is computed similarly to the character of $\mathbb{C}^4$, or from the orthogonality formula.

