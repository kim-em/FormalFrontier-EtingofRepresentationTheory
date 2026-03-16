(2) The symmetric group $S_3$. In the symmetric group $S_n$, conjugacy classes are determined by cycle decomposition sizes: two permutations are conjugate if and only if they have the same number of cycles of each length. For $S_3$, there are three conjugacy classes, so there are three different irreducible representations over $\mathbb{C}$. If their dimensions are $d_1, d_2, d_3$, then $d_1^2 + d_2^2 + d_3^2 = 6$, so $S_3$ must have two 1-dimensional and one 2-dimensional representations. The 1-dimensional representations are the trivial representation $\mathbb{C}_+$ given by $\rho(\sigma) = 1$ and the sign representation $\mathbb{C}_-$ given by $\rho(\sigma) = (-1)^\sigma$.

The 2-dimensional representation can be visualized as representing the symmetries of the equilateral triangle with vertices 1, 2, 3 at the points $(\cos 120°, \sin 120°)$, $(\cos 240°, \sin 240°)$, $(1, 0)$ of the coordinate plane, respectively. Thus, for example,

$$\rho((12)) = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \qquad \rho((123)) = \begin{pmatrix} \cos 120° & -\sin 120° \\ \sin 120° & \cos 120° \end{pmatrix}.$$

To show that this representation is irreducible, consider any subrepresentation $V$. The space $V$ must be the span of a subset of the eigenvectors of $\rho((12))$, which are the nonzero multiples of $(1, 0)$ and $(0, 1)$. Also, $V$ must be the span of a subset of the eigenvectors of $\rho((123))$, which are different vectors. Thus, $V$ must be either $\mathbb{C}^2$ or $0$.

