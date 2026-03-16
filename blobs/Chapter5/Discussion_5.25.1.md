**5.25.1. Conjugacy classes in $GL_2(\mathbb{F}_q)$.** Let $\mathbb{F}_q$ be a finite field of size $q$ of characteristic other than 2 and $G = GL_2(\mathbb{F}_q)$. Then

$$
|G| = (q^2 - 1)(q^2 - q),
$$

since the first column of an invertible $2 \times 2$ matrix must be nonzero and the second column may not be a multiple of the first one. Factoring,

$$
|GL_2(\mathbb{F}_q)| = q(q + 1)(q - 1)^2.
$$
The goal of this section is to describe the irreducible representations of $G$.

To begin, let us find the conjugacy classes in $GL_2(\mathbb{F}_q)$.

| Representatives | Number of elements in a conjugacy class | Number of classes |
|---|---|---|
| Scalar $\begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix}$ | 1 (this is a central element) | $q - 1$ (one for every nonzero $x$) |
| Parabolic $\begin{pmatrix} x & 1 \\ 0 & x \end{pmatrix}$ | $q^2 - 1$ (elements that commute with this one are of the form $\begin{pmatrix} t & u \\ 0 & t \end{pmatrix}$, $t \neq 0$) | $q - 1$ (one for every nonzero $x$) |
| Hyperbolic $\begin{pmatrix} x & 0 \\ 0 & y \end{pmatrix}$, $y \neq x$ | $q^2 + q$ (elements that commute with this one are of the form $\begin{pmatrix} t & 0 \\ 0 & u \end{pmatrix}$, $t, u \neq 0$) | $\frac{1}{2}(q - 1)(q - 2)$ ($x, y \neq 0$ and $x \neq y$) |
| Elliptic $\begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix}$, $x \in \mathbb{F}_q$, $y \in \mathbb{F}_q^\times$, $\varepsilon \in \mathbb{F}_q \setminus \mathbb{F}_q^2$ (characteristic polynomial over $\mathbb{F}_q$ is irreducible) | $q^2 - q$ (the reason will be described below) | $\frac{1}{2}q(q - 1)$ (matrices with $y$ and $-y$ are conjugate) |

Let us explain the structure of the conjugacy class of elliptic matrices in more detail. These are the matrices whose characteristic polynomial is irreducible over $\mathbb{F}_q$ and which therefore don't have eigenvalues in $\mathbb{F}_q$. Let $A$ be such a matrix, and consider a quadratic extension of $\mathbb{F}_q$, namely, $\mathbb{F}_q(\sqrt{\varepsilon})$, where $\varepsilon \in \mathbb{F}_q \setminus \mathbb{F}_q^2$. Over this field, $A$ will have eigenvalues

$$
\alpha = \alpha_1 + \sqrt{\varepsilon}\,\alpha_2
$$

and

$$
\bar{\alpha} = \alpha_1 - \sqrt{\varepsilon}\,\alpha_2,
$$
with corresponding eigenvectors

$$
v, \bar{v} \quad (Av = \alpha v, \, A\bar{v} = \bar{\alpha}\bar{v}).
$$

Choose a basis

$$
\{e_1 = v + \bar{v}, \, e_2 = \sqrt{\varepsilon}(v - \bar{v})\}.
$$

In this basis, the matrix $A$ will have the form

$$
\begin{pmatrix} \alpha_1 & \varepsilon \alpha_2 \\ \alpha_2 & \alpha_1 \end{pmatrix},
$$

justifying the description of representative elements of this conjugacy class.

In the basis $\{v, \bar{v}\}$, matrices that commute with $A$ will have the form

$$
\begin{pmatrix} \lambda & 0 \\ 0 & \bar{\lambda} \end{pmatrix},
$$

for all

$$
\lambda \in \mathbb{F}_{q^2}^\times,
$$

so the number of such matrices is $q^2 - 1$.

