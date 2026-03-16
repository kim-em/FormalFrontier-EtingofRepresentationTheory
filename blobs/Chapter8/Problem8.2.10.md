**Problem 8.2.10.** Let $V$ be a finite dimensional vector space over a field $k$. Let $C_i = SV \otimes \wedge^i V$. We can view $C_i$ as the space of polynomial functions on $V^*$ with values in $\wedge^i V$. Define the differential $d_i : C_i \to C_{i-1}$ by the formula

$$
d_i(f)(u) = \iota_u f(u), \quad u \in V^*,
$$

where $\iota_u : \wedge^i V \to \wedge^{i-1} V$ is the contraction defined by the formula

$$
\iota_u(v_1 \wedge \cdots \wedge v_i) = \sum_{j=1}^{i} (-1)^j u(v_j) v_1 \wedge \ldots \hat{v}_j \cdots \wedge v_i.
$$

(i) Show that $C_\bullet$ is a projective (in fact, free) resolution of $k$ (with trivial action of $V$) as an $SV$-module. (It is called the **Koszul resolution**.)

(ii) Let $V = U \oplus W$. Then we can view $SW$ as an $SV$-module ($U$ acts by zero). Construct a resolution of $SW$ by free $SV$-modules whose terms are $C_i = SV \otimes \wedge^i U$.

Hint: Tensor the Koszul resolution of $k$ as an $SU$-module by $SW$.

(iii) Regard $SV$ as an $S(V \oplus V) = SV \otimes SV$-module using left and right multiplication. Construct a free resolution of $SV$ as an $SV \otimes SV$-module with terms $C_i = SV \otimes \wedge^i V \otimes SV$ (called the Koszul bimodule resolution).

(iv) By tensoring the resolution of (iii) over $SV$ with any $SV$-module $M$, construct a projective (in fact, free) resolution $P_\bullet$ of $M$ with $P_i = 0$ for $i > \dim V$. Deduce that for any $SV$-module $N$ and any $i > \dim V$, one has

$$
\mathrm{Tor}_i^{SV}(M, N) = \mathrm{Ext}^i_{SV}(M, N) = 0
$$

(the **Hilbert syzygies theorem**).

(v) Compute $\mathrm{Ext}^i_{SV}(k, k)$ and $\mathrm{Tor}_i^{SV}(k, k)$.
[Blank page]
