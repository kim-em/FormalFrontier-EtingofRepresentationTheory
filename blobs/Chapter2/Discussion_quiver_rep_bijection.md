We now justify our statement that a representation of a quiver is the same thing as a representation of the path algebra of a quiver.

Let $\mathbf{V}$ be a representation of the path algebra $P_Q$. From this representation, we can construct a representation of $Q$ as follows: let $V_i = p_i \mathbf{V}$, and for any edge $h$, let $x_h = a_h|_{p_{h'} \mathbf{V}} : p_{h'} \mathbf{V} \longrightarrow p_{h''} \mathbf{V}$ be the operator corresponding to the one-edge path $h$.

Similarly, let $(V_i, x_h)$ be a representation of a quiver $Q$. From this representation, we can construct a representation of the path algebra

$^2$An oriented path is specified by a nonnegative integer $n$, a sequence of vertices $i_0, \ldots, i_n$, and a sequence of edges $e_1, \ldots, e_n$ such that each $e_r$ has source $i_{r-1}$ and target $i_r$. In particular, when $n = 0$, one still must choose one vertex $i_0$, which explains why there is one $p_i$ for each $i \in I$. Two paths $a, b$ can be concatenated to form the path $ab$ if and only if the final target of $a$ equals the first source of $b$.
$P_Q$: let $\mathbf{V} = \bigoplus_i V_i$, let $p_i : \mathbf{V} \to V_i \to \mathbf{V}$ be the projection onto $V_i$, and for any path $p = h_1 \ldots h_m$ let $a_p = x_{h_1} \ldots x_{h_m} : V_{h'_m} \to V_{h''_1}$ be the composition of the operators corresponding to the edges occurring in $p$ (and the action of this operator on the other $V_i$ is zero).

It is clear that the above assignments $\mathbf{V} \mapsto (p_i \mathbf{V})$ and $(V_i) \mapsto \bigoplus_i V_i$ are inverses of each other. Thus, we have a bijection between isomorphism classes of representations of the algebra $P_Q$ and of the quiver $Q$.

