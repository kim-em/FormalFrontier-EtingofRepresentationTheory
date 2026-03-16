**Problem 7.8.7.** Let $C_\bullet$ and $D_\bullet$ be complexes of modules over a commutative ring $A$. Define the tensor product complex $(C \otimes D)_\bullet$ by the formula

$$
(C \otimes D)_i = \bigoplus_{j+m=i} C_j \otimes_A D_m,
$$

with differentials

$$
d_i^{C \otimes D}|_{C_j \otimes D_m} = d_j^C \otimes 1 + (-1)^j \cdot 1 \otimes d_m^D.
$$
(i) Show that this is a complex.

Now assume that $A = k$ is a field.

(ii) Show that if $C$ or $D$ is an exact sequence, then so is $C \otimes D$.

Hint: Use the decomposition of Exercise 7.8.4.

(iii) Show that any complex $C$ can be identified with a direct sum of an exact sequence and the complex consisting of $H^i(C)$ with the zero differentials, in such a way that the induced isomorphism $H^i(C) \to H^i(C)$ is the identity.

(iv) Show that there is a natural isomorphism of vector spaces

$$
H^i(C \otimes D) \cong \bigoplus_{j+m=i} H^j(C) \otimes H^m(D).
$$

This is the **Künneth** formula.

