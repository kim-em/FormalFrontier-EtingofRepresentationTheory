This is well defined because if $\pi(a) = \pi(a')$, then

$$
\pi(a'b) = \pi(ab + (a' - a)b) = \pi(ab) + \pi((a' - a)b) = \pi(ab)
$$

because $(a' - a)b \in Ib \subseteq I = \ker \pi$, as $I$ is a right ideal; similarly, if $\pi(b) = \pi(b')$, then

$$
\pi(ab') = \pi(ab + a(b' - b)) = \pi(ab) + \pi(a(b' - b)) = \pi(ab)
$$

because $a(b' - b) \in aI \subseteq I = \ker \pi$, as $I$ is also a left ideal. Thus, $A/I$ is an algebra.

Similarly, if $V$ is a representation of $A$ and $W \subset V$ is a subrepresentation, then $V/W$ is also a representation. Indeed, let $\pi : V \to V/W$ be the quotient map, and set $\rho_{V/W}(a)\pi(x) := \pi(\rho_V(a)x)$.

Above we noted that left ideals of $A$ are subrepresentations of the regular representation of $A$, and vice versa. Thus, if $I$ is a left ideal in $A$, then $A/I$ is a representation of $A$.

