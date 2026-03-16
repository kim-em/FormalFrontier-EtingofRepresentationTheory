**Example 6.3.1** ($D_4$). We restrict ourselves to the orientation

$$
\begin{array}{ccc}
& \bullet & \\
\bullet \longrightarrow & \bullet & \longleftarrow \bullet \\
& \uparrow & \\
& \bullet &
\end{array}.
$$

So a representation of this quiver looks like

$$
\begin{array}{ccc}
& V & \\
V_1 \xrightarrow{A_1} & \bullet & \xleftarrow{A_3} V_3 \\
& \uparrow A_2 & \\
& V_2 &
\end{array}.
$$

The first thing we can do is — as usual — split away the kernels of the maps $A_1$, $A_2$, $A_3$. More precisely, we split away the representations

$$
\begin{array}{ccc}
& 0 & \\
\ker A_1 \xrightarrow{0} & \bullet & \longleftarrow 0 \\
& \uparrow & \\
& 0 &
\end{array},
\quad
\begin{array}{ccc}
& 0 & \\
0 \longrightarrow & \bullet & \longleftarrow 0 \\
& \uparrow 0 & \\
& \ker A_2 &
\end{array},
$$
$$
\overset{0}{\bullet} \to \overset{0}{\bullet} \leftarrow \overset{\ker A_3}{\bullet}
$$

$$
\uparrow
$$

$$
\overset{0}{\bullet}
$$

These representations are multiples of the indecomposable objects

$$
\overset{1}{\bullet} \xrightarrow{0} \overset{0}{\bullet} \leftarrow \overset{0}{\bullet}
$$

$$
\uparrow
$$

$$
\overset{0}{\bullet}
$$

$$
\overset{0}{\bullet} \to \overset{0}{\bullet} \leftarrow \overset{0}{\bullet}
$$

$$
\uparrow 0
$$

$$
\overset{1}{\bullet}
$$

$$
\overset{0}{\bullet} \to \overset{0}{\bullet} \xleftarrow{0} \overset{1}{\bullet}
$$

$$
\uparrow
$$

$$
\overset{0}{\bullet}
$$

So we get to a situation where all of the maps $A_1, A_2, A_3$ are injective:

$$
\overset{V_1}{\bullet} \xrightarrow{A_1} \overset{V}{\bullet} \xleftarrow{A_3} \overset{V_3}{\bullet}
$$

$$
\uparrow A_2
$$

$$
\overset{V_2}{\bullet}
$$

As in Example 6.2.4, we can then identify the spaces $V_1, V_2, V_3$ with subspaces of $V$. So we get to the **triple of subspaces problem** of classifying triples of subspaces of a given space $V$.
The next step is to split away a multiple of

$$
\begin{array}{ccc}
& 1 & \\
0 \longrightarrow & \bullet & \longleftarrow 0 \\
& \uparrow & \\
& 0 &
\end{array}
$$

to reach a situation where

$$
V_1 + V_2 + V_3 = V.
$$

By letting $Y = V_1 \cap V_2 \cap V_3$, choosing a complement $V'$ of $Y$ in $V$, and setting $V_i' = V' \cap V_i$, $i = 1, 2, 3$, we can decompose this representation into

$$
\begin{array}{ccc}
& V' & \\
V_1' \hookrightarrow & \bullet & \hookleftarrow V_3' \\
& \uparrow & \\
& V_2' &
\end{array}
\quad \oplus \quad
\begin{array}{ccc}
& Y & \\
Y \xrightarrow{\sim} & \bullet & \xleftarrow{\sim} Y \\
& \uparrow \wr & \\
& Y &
\end{array},
$$

The last summand is a multiple of the indecomposable representation

$$
\begin{array}{ccc}
& 1 & \\
1 \xrightarrow{\sim} & \bullet & \xleftarrow{\sim} 1 \\
& \uparrow \wr & \\
& 1 &
\end{array}.
$$

So — considering the first summand and renaming the spaces to simplify notation — we are in a situation where

$$
V = V_1 + V_2 + V_3, \quad V_1 \cap V_2 \cap V_3 = 0.
$$

As a next step, we let $Y = V_1 \cap V_2$ and we choose a complement $V'$ of $Y$ in $V$ such that $V_3 \subset V'$ and set $V_1' = V' \cap V_1$, $V_2' = V' \cap V_2$. This
yields the decomposition

$$
\begin{array}{ccc}
& V & \\
V_1 \hookrightarrow & \bullet & \hookleftarrow V_3 \\
& \uparrow & \\
& V_2 &
\end{array}
\quad = \quad
\begin{array}{ccc}
& V' & \\
V_1' \hookrightarrow & \bullet & \hookleftarrow V_3 \\
& \uparrow & \\
& V_2' &
\end{array}
\quad \oplus \quad
\begin{array}{ccc}
& Y & \\
Y \xrightarrow{\sim} & \bullet & \longleftarrow 0 \\
& \uparrow \wr & \\
& Y &
\end{array}.
$$

The second summand is a multiple of the indecomposable object

$$
\begin{array}{ccc}
& 1 & \\
1 \xrightarrow{\sim} & \bullet & \longleftarrow 0 \\
& \uparrow \wr & \\
& 1 &
\end{array}.
$$

In the resulting situation we have $V_1 \cap V_2 = 0$. Similarly we can split away multiples of

$$
\begin{array}{ccc}
& 1 & \\
1 \xrightarrow{\sim} & \bullet & \xleftarrow{\sim} 1 \\
& \uparrow & \\
& 0 &
\end{array}
\qquad \text{and} \qquad
\begin{array}{ccc}
& 1 & \\
0 \longrightarrow & \bullet & \xleftarrow{\sim} 1 \\
& \uparrow \wr & \\
& 1 &
\end{array}
$$

to reach a situation where the spaces $V_1, V_2, V_3$ do not intersect pairwise:

$$
V_1 \cap V_2 = V_1 \cap V_3 = V_2 \cap V_3 = 0.
$$

If $V_1 \not\subset V_2 \oplus V_3$, we let $Y = V_1 \cap (V_2 \oplus V_3)$. We let $V_1'$ be a complement of $Y$ in $V_1$. Since then $V_1' \cap (V_2 \oplus V_3) = 0$, we can select a complement
$V'$ of $V_1'$ in $V$ which contains $V_2 \oplus V_3$. This gives us the decomposition

$$
\begin{array}{ccc}
& V & \\
V_1 \hookrightarrow & \bullet & \hookleftarrow V_3 \\
& \uparrow & \\
& V_2 &
\end{array}
$$

$$
= \quad
\begin{array}{ccc}
& V_1' & \\
V_1' \xrightarrow{\sim} & \bullet & \longleftarrow 0 \\
& \uparrow & \\
& 0 &
\end{array}
\quad \oplus \quad
\begin{array}{ccc}
& V' & \\
Y \hookrightarrow & \bullet & \hookleftarrow V_3 \\
& \uparrow & \\
& V_2 &
\end{array}.
$$

The first of these summands is a multiple of

$$
\begin{array}{ccc}
& 1 & \\
1 \xrightarrow{\sim} & \bullet & \longleftarrow 0 \\
& \uparrow & \\
& 0 &
\end{array}.
$$

By splitting these away, we get to a situation where $V_1 \subseteq V_2 \oplus V_3$. Similarly, we can split away objects of the type

$$
\begin{array}{ccc}
& 1 & \\
0 \longrightarrow & \bullet & \longleftarrow 0 \\
& \uparrow \wr & \\
& 1 &
\end{array}
\qquad \text{and} \qquad
\begin{array}{ccc}
& 1 & \\
0 \longrightarrow & \bullet & \xleftarrow{\sim} 1 \\
& \uparrow & \\
& 0 &
\end{array}
$$

to reach a situation in which the following conditions hold:

(1) $V_1 + V_2 + V_3 = V$.

(2) $V_1 \cap V_2 = 0$, $\quad V_1 \cap V_3 = 0$, $\quad V_2 \cap V_3 = 0$.

(3) $V_1 \subseteq V_2 \oplus V_3$, $\quad V_2 \subseteq V_1 \oplus V_3$, $\quad V_3 \subseteq V_1 \oplus V_2$.

But this implies that

$$
V_1 \oplus V_2 = V_1 \oplus V_3 = V_2 \oplus V_3 = V.
$$

So we get

$$
\dim V_1 = \dim V_2 = \dim V_3 = n
$$
and

$$
\dim V = 2n.
$$

Since $V_3 \subseteq V_1 \oplus V_2$, we can write every element of $V_3$ in the form

$$
x \in V_3, \quad x = (x_1, x_2), \, x_1 \in V_1, \, x_2 \in V_2.
$$

We then can define the projections

$$
B_1 : V_3 \to V_1, \quad (x_1, x_2) \mapsto x_1,
$$

$$
B_2 : V_3 \to V_2, \quad (x_1, x_2) \mapsto x_2.
$$

Since $V_3 \cap V_1 = 0$ and $V_3 \cap V_2 = 0$, these maps have to be injective and therefore are isomorphisms. We then define the isomorphism

$$
A = B_2 \circ B_1^{-1} : V_1 \to V_2.
$$

Let $e_1, \ldots, e_n$ be a basis for $V_1$. Then we get

$$
V_1 = k\,e_1 \oplus k\,e_2 \oplus \cdots \oplus k\,e_n,
$$

$$
V_2 = k\,Ae_1 \oplus k\,Ae_2 \oplus \cdots \oplus k\,Ae_n,
$$

$$
V_3 = k\,(e_1 + Ae_1) \oplus k\,(e_2 + Ae_2) \oplus \cdots \oplus k\,(e_n + Ae_n).
$$

So we can think of $V_3$ as the graph of an isomorphism $A : V_1 \to V_2$.

From this we obtain the decomposition

$$
\begin{array}{ccc}
& V & \\
V_1 \longrightarrow & \bullet & \longleftarrow V_3 \\
& \uparrow & \\
& V_2 &
\end{array}
\quad = \quad \bigoplus_{j=1}^n
\begin{array}{ccc}
& k^2 & \\
k(1,0) \longrightarrow & \bullet & \longleftarrow k(1,1) \\
& \uparrow & \\
& k(0,1) &
\end{array}.
$$

These correspond to the indecomposable object

$$
\begin{array}{ccc}
& 2 & \\
1 \longrightarrow & \bullet & \longleftarrow 1 \\
& \uparrow & \\
& 1 &
\end{array}.
$$

Thus the quiver $D_4$ with the selected orientation has 12 indecomposable objects. If one were to explicitly decompose representations for the other possible orientations, one would also find 12 indecomposable objects.
