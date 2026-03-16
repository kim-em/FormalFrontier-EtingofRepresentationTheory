**Example 6.2.3** ($A_2$). The quiver $A_2$ consists of two vertices connected by a single edge:

$$\bullet \xrightarrow{} \bullet$$
A representation of this quiver consists of two vector spaces $V, W$ and an operator $A : V \to W$:

$$
\overset{V}{\bullet} \xrightarrow{A} \overset{W}{\bullet}.
$$

To decompose this representation, we first let $V'$ be a complement to the kernel of $A$ in $V$ and let $W'$ be a complement to the image of $A$ in $W$. Then we can decompose the representation as follows:

$$
\overset{V}{\bullet} \xrightarrow{A} \overset{W}{\bullet} = \overset{\ker A}{\bullet} \xrightarrow{0} \overset{0}{\bullet} \oplus \overset{V'}{\bullet} \xrightarrow[\sim]{A} \overset{\operatorname{Im} A}{\bullet} \oplus \overset{0}{\bullet} \xrightarrow{0} \overset{W'}{\bullet}.
$$

The first summand is a multiple of the object $1 \to 0$, the second a multiple of $1 \xrightarrow{\sim} 1$, and the third of $0 \to 1$. We see that the quiver $A_2$ has three indecomposable representations, namely

$$
1 \to 0, \quad 1 \xrightarrow{\sim} 1, \quad \text{and} \quad 0 \to 1.
$$

Note that this statement is just the Gauss elimination theorem for matrices.

