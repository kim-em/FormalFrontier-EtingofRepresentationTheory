**Example 6.2.4** ($A_3$). The quiver $A_3$ consists of three vertices and two connections between them. So we have to choose between two possible orientations:

$$
\bullet \to \bullet \to \bullet \qquad \text{or} \qquad \bullet \to \bullet \leftarrow \bullet.
$$

**(1)** We first look at the orientation

$$
\bullet \to \bullet \to \bullet.
$$

Then a representation of this quiver looks like

$$
\overset{V}{\bullet} \xrightarrow{A} \overset{W}{\bullet} \xrightarrow{B} \overset{Y}{\bullet}.
$$

As in Example 6.2.3 we first split away

$$
\overset{\ker A}{\bullet} \xrightarrow{0} \overset{0}{\bullet} \xrightarrow{0} \overset{0}{\bullet}.
$$

This object is a multiple of $1 \to 0 \to 0$. Next, let $Y'$ be a complement of $\operatorname{Im} B$ in $Y$. Then we can also split away

$$
\overset{0}{\bullet} \xrightarrow{0} \overset{0}{\bullet} \xrightarrow{0} \overset{Y'}{\bullet}
$$
which is a multiple of the object $0 \to 0 \to 1$. This results in a situation where the map $A$ is injective and the map $B$ is surjective (we rename the spaces to simplify notation):

$$
\overset{V}{\bullet} \xhookrightarrow{A} \overset{W}{\bullet} \xtwoheadrightarrow{B} \overset{Y}{\bullet}.
$$

Next, let $X = \ker(B \circ A)$ and let $X'$ be a complement of $X$ in $V$. Let $W'$ be a complement of $A(X)$ in $W$ such that $A(X') \subset W'$. Then we get

$$
\overset{V}{\bullet} \xhookrightarrow{A} \overset{W}{\bullet} \xtwoheadrightarrow{B} \overset{Y}{\bullet}
$$

$$
= \overset{X}{\bullet} \xrightarrow{A} \overset{A(X)}{\bullet} \xrightarrow{B} \overset{0}{\bullet} \oplus \overset{X'}{\bullet} \xhookrightarrow{A} \overset{W'}{\bullet} \xtwoheadrightarrow{B} \overset{Y}{\bullet}.
$$

The first of these summands is a multiple of $1 \xrightarrow{\sim} 1 \to 0$. Looking at the second summand, we now have a situation where $A$ is injective, $B$ is surjective, and furthermore $\ker(B \circ A) = 0$. To simplify notation, we redefine

$$
V = X', \qquad W = W'.
$$

Next we let $X = \operatorname{Im}(B \circ A)$ and let $X'$ be a complement of $X$ in $Y$. Furthermore, let $W' = B^{-1}(X')$. Then $W'$ is a complement of $A(V)$ in $W$. This yields the decomposition

$$
\overset{V}{\bullet} \xhookrightarrow{A} \overset{W}{\bullet} \xtwoheadrightarrow{B} \overset{Y}{\bullet}
$$

$$
= \overset{V}{\bullet} \xrightarrow[\sim]{A} \overset{A(V)}{\bullet} \xrightarrow[\sim]{B} \overset{X}{\bullet} \oplus \overset{0}{\bullet} \to \overset{W'}{\bullet} \xtwoheadrightarrow{B} \overset{X'}{\bullet}.
$$

Here, the first summand is a multiple of $1 \xrightarrow{\sim} 1 \xrightarrow{\sim} 1$. By splitting away the kernel of $B$, the second summand can be decomposed into multiples of $0 \to 1 \xrightarrow{\sim} 1$ and $0 \to 1 \to 0$. So, on the whole, this quiver has six indecomposable representations:

$$
1 \to 0 \to 0, \quad 0 \to 0 \to 1, \quad 1 \xrightarrow{\sim} 1 \to 0,
$$

$$
1 \xrightarrow{\sim} 1 \xrightarrow{\sim} 1, \quad 0 \to 1 \xrightarrow{\sim} 1, \quad 0 \to 1 \to 0.
$$

**(2)** Now we look at the orientation

$$
\bullet \to \bullet \leftarrow \bullet.
$$
Very similarly to the other orientation, we can split away objects of the type

$$1 \xrightarrow{} 0 \xleftarrow{} 0 , \quad 0 \xrightarrow{} 0 \xleftarrow{} 1 ,$$

which results in a situation where both $A$ and $B$ are injective:

$$\overset{\bullet}{V} \xhookrightarrow{A} \overset{\bullet}{W} \xleftarrow{B} \overset{\bullet}{Y} .$$

By identifying $V$ and $Y$ as subspaces of $W$, this leads to the problem of classifying pairs of subspaces of a given space $W$ up to isomorphism (the **pair of subspaces problem**). To do so, we first choose a complement $W'$ of $V \cap Y$ in $W$ and set $V' = W' \cap V$, $Y' = W' \cap Y$. Then we can decompose the representation as follows:

$$\overset{\bullet}{V} \xhookrightarrow{} \overset{\bullet}{W} \xleftarrow{} \overset{\bullet}{Y} = \overset{\bullet}{V'} \xhookrightarrow{} \overset{\bullet}{W'} \xleftarrow{} \overset{\bullet}{Y'} \oplus \overset{\bullet}{V \cap Y} \xrightarrow{\sim} \overset{\bullet}{V \cap Y} \xleftarrow{\sim} \overset{\bullet}{V \cap Y} .$$

The second summand is a multiple of the object $1 \xrightarrow{\sim} 1 \xleftarrow{\sim} 1$. We go on decomposing the first summand. Again, to simplify notation, we let

$$V = V', \quad W = W', \quad Y = Y'.$$

We can now assume that $V \cap Y = 0$. Next, let $W'$ be a complement of $V \oplus Y$ in $W$. Then we get

$$\overset{\bullet}{V} \xhookrightarrow{} \overset{\bullet}{W} \xleftarrow{} \overset{\bullet}{Y} = \overset{\bullet}{V} \xhookrightarrow{} \overset{\bullet}{V \oplus Y} \xleftarrow{} \overset{\bullet}{Y} \oplus \overset{\bullet}{0} \xrightarrow{} \overset{\bullet}{W'} \xleftarrow{} \overset{\bullet}{0} .$$

The second of these summands is a multiple of the indecomposable object $0 \xrightarrow{} 1 \xleftarrow{} 0$. The first summand can be further decomposed as follows:

$$\overset{\bullet}{V} \xhookrightarrow{} \overset{\bullet}{V \oplus Y} \xleftarrow{} \overset{\bullet}{Y} = \overset{\bullet}{V} \xrightarrow{\sim} \overset{\bullet}{V} \xleftarrow{} \overset{\bullet}{0} \oplus \overset{\bullet}{0} \xrightarrow{} \overset{\bullet}{Y} \xleftarrow{\sim} \overset{\bullet}{Y} .$$

These summands are multiples of

$$1 \xrightarrow{} 1 \xleftarrow{} 0 , \quad 0 \xrightarrow{} 1 \xleftarrow{} 1$$
So — as in the other orientation — we get six indecomposable representations of $A_3$:

$$
1 \longrightarrow 0 \longleftarrow 0, \quad 0 \longrightarrow 0 \longleftarrow 1, \quad 1 \xrightarrow{\sim} 1 \xleftarrow{\sim} 1,
$$

$$
0 \longrightarrow 1 \longleftarrow 0, \quad 1 \longrightarrow 1 \longleftarrow 0, \quad 0 \longrightarrow 1 \longleftarrow 1.
$$

