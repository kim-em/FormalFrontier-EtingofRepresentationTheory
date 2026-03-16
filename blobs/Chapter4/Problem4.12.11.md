**Problem 4.12.11.** This problem is about an application of representation theory to physics (elasticity theory). We first describe the physical motivation and then state the mathematical problem.

Imagine a material which occupies a certain region $U$ in the physical space $V = \mathbb{R}^3$ (a space with a positive definite inner product). Suppose the material is deformed. This means, we have applied a diffeomorphism (= change of coordinates) $g : U \to U'$. The question in elasticity theory is how much stress in the material this deformation will cause.

For every point $P \in U$, let $A_P : V \to V$ be defined by $A_P = dg(P)$. Here $A_P$ is nondegenerate, so it has a polar decomposition $A_P = D_P O_P$, where $O_P$ is orthogonal and $D_P$ is symmetric. The matrix $O_P$ characterizes the rotation part of $A_P$ (which clearly produces no stress), and $D_P$ is the distortion part, which actually causes stress. If the deformation is small, $D_P$ is close to 1, so $D_P = 1 + d_P$, where $d_P$ is a small symmetric matrix, i.e., an element of $S^2V$. This matrix is called the **deformation tensor** at $P$.

Now we define the stress tensor, which characterizes stress. Let $v$ be a small nonzero vector in $V$, and let $\sigma$ be a small disk perpendicular to $v$ centered at $P$ of area $||v||$. Let $F_v$ be the force with which the part of the material on the $v$-side of $\sigma$ acts on the part on the opposite
side. It is easy to deduce from Newton's laws that $F_v$ is linear in $v$, so there exists a linear operator $S_P : V \to V$ such that $F_v = S_P v$. It is called **the stress tensor**.

An elasticity law is an equation $S_P = f(d_P)$, where $f$ is a function. The simplest such law is a linear law (Hooke's law): $f : S^2V \to \operatorname{End}(V)$ is a linear function. In general, such a function is defined by $9 \cdot 6 = 54$ parameters, but we will show there are actually only two essential ones — the **compression modulus** $K$ and the **shearing modulus** $\mu$. For this purpose we will use representation theory.

Recall that the group $SO(3)$ of rotations acts on $V$, so $S^2V$, $\operatorname{End}(V)$ are representations of this group. The laws of physics must be invariant under this group (Galileo transformations), so $f$ must be a homomorphism of representations.

(a) Show that $\operatorname{End}(V)$ admits a decomposition $\mathbb{R} \oplus V \oplus W$, where $\mathbb{R}$ is the trivial representation, $V$ is the standard 3-dimensional representation, and $W$ is a 5-dimensional representation of $SO(3)$. Show that $S^2V = \mathbb{R} \oplus W$.

(b) Show that $V$ and $W$ are irreducible, even after complexification. Deduce using Schur's lemma that $S_P$ is always symmetric, and for $x \in \mathbb{R}, y \in W$ one has $f(x + y) = Kx + \mu y$ for some real numbers $K, \mu$.

In fact, it is clear from physics that $K, \mu$ are positive. Physically, the compression modulus $K$ characterizes resistance of the material to compression or dilation, while the shearing modulus $\mu$ characterizes its resistance to changing the shape of the object without changing its volume. For instance, clay (used for sculpting) has a large compression modulus but a small shearing modulus.

