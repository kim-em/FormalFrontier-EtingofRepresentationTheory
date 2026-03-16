**Proposition 5.2.3.** *Definitions (5.2.1) and (5.2.2) are equivalent.*

**Proof.** To show that the condition of Definition 5.2.2 implies the condition of Definition 5.2.1, notice that $z$ is a root of the characteristic polynomial of the matrix (a monic polynomial with rational, respectively integer, coefficients). To establish the converse, suppose $z$ is a root of

$$p(x) = x^n + a_1 x^{n-1} + \ldots + a_{n-1} x + a_n.$$

Then the characteristic polynomial of the following matrix (called the **companion matrix**) is $p(x)$:

$$\begin{pmatrix} 0 & 0 & 0 & \ldots & 0 & -a_n \\ 1 & 0 & 0 & \ldots & 0 & -a_{n-1} \\ 0 & 1 & 0 & \ldots & 0 & -a_{n-2} \\ & & & \vdots & & \\ 0 & 0 & 0 & \ldots & 1 & -a_1 \end{pmatrix}.$$

Since $z$ is a root of the characteristic polynomial of this matrix, it is an eigenvalue of this matrix. $\square$

