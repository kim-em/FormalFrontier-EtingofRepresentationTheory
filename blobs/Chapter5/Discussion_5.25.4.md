**5.25.4. Complementary series representations.** Let $\mathbb{F}_{q^2} \supset \mathbb{F}_q$ be a quadratic extension $\mathbb{F}_q(\sqrt{\varepsilon})$, $\varepsilon \in \mathbb{F}_q \setminus \mathbb{F}_q^2$. We regard this as a 2-dimensional vector space over $\mathbb{F}_q$; then $G$ is the group of linear transformations of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$. Let $K \subset G$ be the cyclic group of multiplications by elements of $\mathbb{F}_{q^2}^\times$,

$$
K = \left\{ \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix} \right\}, \qquad |K| = q^2 - 1.
$$

For $\nu : K \to \mathbb{C}^\times$ a homomorphism, let

$$
Y_\nu = \operatorname{Ind}_K^G \mathbb{C}_\nu.
$$
This representation, of course, is reducible. Let us compute its character, using the Frobenius formula. We get

$$
\chi \begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix} = q(q - 1)\nu(x),
$$

$$
\chi(A) = 0 \quad \text{for } A \text{ parabolic or hyperbolic},
$$

$$
\chi \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix} = \nu \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix} + \nu \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix}^q.
$$

The last assertion holds because if we regard the matrix as an element of $\mathbb{F}_{q^2}$, conjugation is an automorphism of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$, but the only nontrivial automorphism of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$ is the $q$th power map.

We thus have

$$
\operatorname{Ind}_K^G \mathbb{C}_{\nu^q} \cong \operatorname{Ind}_K^G \mathbb{C}_\nu
$$

because they have the same character. Therefore, for $\nu^q \neq \nu$ we get $\frac{1}{2}q(q - 1)$ representations.

Next, we look at the tensor product

$$
W_1 \otimes V_{\alpha, 1},
$$

where $1$ is the trivial character and $W_1$ is defined as in the previous section. The character of this representation is

$$
\chi \begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix} = q(q + 1)\alpha(x),
$$

$$
\chi(A) = 0 \quad \text{for } A \text{ parabolic or elliptic},
$$

$$
\chi \begin{pmatrix} x & 0 \\ 0 & y \end{pmatrix} = \alpha(x) + \alpha(y).
$$

Thus the "virtual representation"

$$
W_1 \otimes V_{\alpha, 1} - V_{\alpha, 1} - \operatorname{Ind}_K^G \mathbb{C}_\nu,
$$
where $\alpha$ is the restriction of $\nu$ to scalars, has the character

$$
\chi \begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix} = (q - 1)\alpha(x),
$$

$$
\chi \begin{pmatrix} x & 1 \\ 0 & x \end{pmatrix} = -\alpha(x),
$$

$$
\chi \begin{pmatrix} x & 0 \\ 0 & y \end{pmatrix} = 0,
$$

$$
\chi \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix} = -\nu \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix} - \nu^q \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix}.
$$

In all that follows, we will have $\nu^q \neq \nu$.

The following two lemmas will establish that the inner product of this character with itself is equal to 1 and that its value at 1 is positive. As we know from Lemma 5.7.2, these two properties imply that it is the character of an irreducible representation of $G$.
