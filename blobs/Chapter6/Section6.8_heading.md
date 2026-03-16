## 6.8. Proof of Gabriel's theorem

Let $V$ be an indecomposable representation of $Q$. We introduce a fixed labeling $1, \ldots, n$ on $Q$, such that $i < j$ if one can reach $j$ from $i$. This is possible, since we can assign the highest label to any sink, remove this sink from the quiver, assign the next highest label to a sink of the remaining quiver, and so on. This way we create a labeling of the desired kind.

We now consider the sequence

$$
V^{(0)} = V, \quad V^{(1)} = F_n^+ V, \quad V^{(2)} = F_{n-1}^+ F_n^+ V, \quad \ldots.
$$

This sequence is well defined because of the selected labeling: $n$ has to be a sink of $Q$, $n-1$ has to be a sink of $\overline{Q}_n$ (where $\overline{Q}_r$ is obtained from $Q$ by reversing all the arrows at the vertex $r$) and so on. Furthermore, we note that $V^{(n)}$ is a representation of $Q$ again, since every arrow has been reversed twice (since we applied a reflection functor to every vertex). This implies that we can define

$$
V^{(n+1)} = F_n^+ V^{(n)}, \ldots
$$

and continue the sequence to infinity.
