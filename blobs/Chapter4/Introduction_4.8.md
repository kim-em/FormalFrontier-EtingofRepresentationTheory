## 4.8. Character tables, examples

The characters of all the irreducible representations of a finite group can be arranged into a **character table**, with conjugacy classes of elements as the columns and characters as the rows. More specifically, the first row in a character table lists representatives of conjugacy classes, the second one lists the numbers of elements in the conjugacy classes, and the other rows list the values of the characters on the conjugacy classes. Due to Theorems 4.5.1 and 4.5.4, the rows and columns of a character table are orthonormal with respect to the appropriate inner products.

Note that in any character table, the row corresponding to the trivial representation consists of ones, and the column corresponding
to the neutral element consists of the dimensions of the representations.

Here is, for example, the character table of $S_3$:

| $S_3$ | Id | (12) | (123) |
|---|---|---|---|
| # | 1 | 3 | 2 |
| $\mathbb{C}_+$ | 1 | 1 | 1 |
| $\mathbb{C}_-$ | 1 | $-1$ | 1 |
| $\mathbb{C}^2$ | 2 | 0 | $-1$ |

It is obtained by explicitly computing traces in the irreducible representations.

For another example consider $A_4$, the group of even permutations of four items. There are three 1-dimensional representations (as $A_4$ has a normal subgroup $\mathbb{Z}_2 \oplus \mathbb{Z}_2$ and $A_4/(\mathbb{Z}_2 \oplus \mathbb{Z}_2) = \mathbb{Z}_3$). Since there are four conjugacy classes in total, there is one more irreducible representation of dimension 3. Finally, the character table is

| $A_4$ | Id | (123) | (132) | (12)(34) |
|---|---|---|---|---|
| # | 1 | 4 | 4 | 3 |
| $\mathbb{C}$ | 1 | 1 | 1 | 1 |
| $\mathbb{C}_\epsilon$ | 1 | $\epsilon$ | $\epsilon^2$ | 1 |
| $\mathbb{C}_{\epsilon^2}$ | 1 | $\epsilon^2$ | $\epsilon$ | 1 |
| $\mathbb{C}^3$ | 3 | 0 | 0 | $-1$ |

where $\epsilon = \exp(\frac{2\pi i}{3})$.

The last row can be computed using the orthogonality of rows. Another way to compute the last row is to note that $\mathbb{C}^3$ is the representation of $A_4$ by rotations of the regular tetrahedron: in this case $(123), (132)$ are the rotations by $120^0$ and $240^0$ around a perpendicular to a face of the tetrahedron, while $(12)(34)$ is the rotation by $180^0$ around an axis perpendicular to two opposite edges.

