**Theorem 5.25.2.** *(1) $\lambda_1 \neq \lambda_2 \Rightarrow V_{\lambda_1, \lambda_2}$ is irreducible.*

*(2) $\lambda_1 = \lambda_2 = \mu \Rightarrow V_{\lambda_1, \lambda_2} = \mathbb{C}_\mu \oplus W_\mu$, where $W_\mu$ is a $q$-dimensional irreducible representation of $G$.*

*(3) $W_\mu \cong W_\nu$ if and only if $\mu = \nu$; $V_{\lambda_1, \lambda_2} \cong V_{\lambda_1', \lambda_2'}$ if and only if $\{\lambda_1, \lambda_2\} = \{\lambda_1', \lambda_2'\}$ (in the second case, $\lambda_1 \neq \lambda_2$, $\lambda_1' \neq \lambda_2'$).*

**Proof.** From the Frobenius formula, we have

$$\operatorname{Tr}_{V_{\lambda_1, \lambda_2}}(g) = \frac{1}{|B|} \sum_{a \in G,\, aga^{-1} \in B} \lambda(aga^{-1}).$$

If

$$g = \begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix},$$

the expression on the right evaluates to

$$\lambda(g) \frac{|G|}{|B|} = \lambda_1(x)\lambda_2(x)(q + 1).$$

If

$$g = \begin{pmatrix} x & 1 \\ 0 & x \end{pmatrix},$$

the expression evaluates to

$$\lambda(g) \cdot 1,$$

since here $aga^{-1} \in B \Rightarrow a \in B$.

If

$$g = \begin{pmatrix} x & 0 \\ 0 & y \end{pmatrix},$$
the expression evaluates to

$$\left(\lambda_1(x)\lambda_2(y) + \lambda_1(y)\lambda_2(x)\right) \cdot 1,$$

since here $aga^{-1} \in B$ implies that $a \in B$ or $a$ is an element of $B$ multiplied by the transposition matrix.

If

$$g = \begin{pmatrix} x & \varepsilon y \\ y & x \end{pmatrix}, \quad x \neq y,$$

the expression on the right evaluates to 0 because matrices of this type do not have eigenvalues over $\mathbb{F}_q$ (and thus cannot be conjugated into $B$). From the definition, $\lambda_i(x)$ for $i = 1, 2$ is a root of unity, so

$$|G|\langle \chi_{V_{\lambda_1, \lambda_2}}, \chi_{V_{\lambda_1, \lambda_2}} \rangle = (q + 1)^2(q - 1) + (q^2 - 1)(q - 1)$$

$$+ 2(q^2 + q)\frac{(q - 1)(q - 2)}{2} + (q^2 + q) \sum_{x \neq y} \lambda_1(x)\lambda_2(y)\overline{\lambda_1(y)\lambda_2(x)}.$$

The last two summands come from the expansion

$$|a + b|^2 = |a|^2 + |b|^2 + a\overline{b} + \overline{a}b.$$

If

$$\lambda_1 = \lambda_2 = \mu,$$

the last term is equal to

$$(q^2 + q)(q - 2)(q - 1),$$

and the total in this case is

$$(q+1)(q-1)[(q+1)+(q-1)+2q(q-2)] = (q+1)(q-1)2q(q-1) = 2|G|,$$

so

$$\langle \chi_{V_{\lambda_1, \lambda_2}}, \chi_{V_{\lambda_1, \lambda_2}} \rangle = 2.$$

Clearly,

$$\mathbb{C}_\mu \subseteq \operatorname{Ind}_B^G \mathbb{C}_{\mu,\mu},$$

since

$$\operatorname{Hom}_G(\mathbb{C}_\mu, \operatorname{Ind}_B^G \mathbb{C}_{\mu,\mu}) = \operatorname{Hom}_B(\mathbb{C}_\mu, \mathbb{C}_\mu) = \mathbb{C} \text{ (Theorem 5.10.1).}$$

Therefore, $\operatorname{Ind}_B^G \mathbb{C}_{\mu,\mu} = \mathbb{C}_\mu \oplus W_\mu$; $W_\mu$ is irreducible; and the character of $W_\mu$ is different for distinct values of $\mu$, proving that $W_\mu$ are distinct.
If $\lambda_1 \neq \lambda_2$, let $z = xy^{-1}$. Then the last term of the summation is

$$
(q^2 + q) \sum_{x \neq y} \lambda_1(z) \overline{\lambda_2(z)} = (q^2 + q) \sum_{\substack{x, \\ z \neq 1}} \frac{\lambda_1}{\lambda_2}(z) = (q^2 + q)(q - 1) \sum_{z \neq 1} \frac{\lambda_1}{\lambda_2}(z).
$$

Since

$$
\sum_{z \in \mathbb{F}_q^\times} \frac{\lambda_1}{\lambda_2}(z) = 0,
$$

because the sum of all roots of unity of a given order $m > 1$ is zero, the last term becomes

$$
-(q^2 + q)(q - 1) \frac{\lambda_1}{\lambda_2}(1) = -(q^2 + q)(q - 1).
$$

The difference between this case and the case of $\lambda_1 = \lambda_2$ is equal to

$$
(q^2 + q)[(q - 2)(q - 1) + (q - 1)] = |G|,
$$

so this is an irreducible representation by Lemma 5.7.2.

To prove the third assertion of the theorem, we look at the characters on hyperbolic elements and note that the function

$$
\lambda_1(x)\lambda_2(y) + \lambda_1(y)\lambda_2(x)
$$

determines $\lambda_1, \lambda_2$ up to permutation. $\square$

