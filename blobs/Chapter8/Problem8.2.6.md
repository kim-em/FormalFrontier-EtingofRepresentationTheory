**Problem 8.2.6.** (i) Show that $\mathrm{Tor}_0(M, N) = M \otimes_A N$ and that $\mathrm{Ext}^0(M, N) = \mathrm{Hom}_A(M, N)$.

(ii) Show that the group $\mathrm{Ext}^1(M, N)$ as defined here is canonically isomorphic to the one defined in Problem 3.9.1.

(iii) Let

$$0 \to N_1 \to N_2 \to N_3 \to 0$$

be a short exact sequence of left $A$-modules.

Show that there are long exact sequences

$$0 \to \mathrm{Hom}_A(M, N_1) \to \mathrm{Hom}_A(M, N_2) \to \mathrm{Hom}_A(M, N_3) \to$$

$$\mathrm{Ext}^1(M, N_1) \to \mathrm{Ext}^1(M, N_2) \to \mathrm{Ext}^1(M, N_3) \to \mathrm{Ext}^2(M, N_1) \to \ldots$$

and

$$\ldots \to \mathrm{Tor}_2(M, N_3) \to \mathrm{Tor}_1(M, N_1) \to \mathrm{Tor}_1(M, N_2) \to \mathrm{Tor}_1(M, N_3)$$

$$\to M \otimes_A N_1 \to M \otimes_A N_2 \to M \otimes_A N_3 \to 0.$$

This shows that, as we mentioned above, the Tor and Ext groups "quantify" the extent to which the functors $M \otimes_A$ and $\mathrm{Hom}_A(M, ?)$ are not exact.

Hint: Use Problem 7.8.5.

(iv) Show that $\mathrm{Tor}_i^A(M, N)$ can be computed by taking a projective resolution of $N$, tensoring it with $M$, and computing cohomology.
Hint: Show first that $\operatorname{Tor}_i^A(M, N)$ can be computed by tensoring two projective resolutions, for $M$ and for $N$, and computing cohomology.

(v) Let $0 \to M_1 \to M_2 \to M_3 \to 0$ be a short exact sequence of left $A$-modules. Let $P_\bullet^1$ and $P_\bullet^3$ be projective resolutions of $M_1$ and $M_3$. Construct a projective resolution of $M_2$ with terms $P_i^2 := P_i^1 \oplus P_i^3$ (use Exercise 8.1.4). Use it to show that for any left $A$-module $N$ there are long exact sequences

$$
0 \to \operatorname{Hom}_A(M_3, N) \to \operatorname{Hom}_A(M_2, N) \to \operatorname{Hom}_A(M_1, N) \to
$$

$$
\operatorname{Ext}^1(M_3, N) \to \operatorname{Ext}^1(M_2, N) \to \operatorname{Ext}^1(M_1, N) \to \operatorname{Ext}^2(M_3, N) \to \ldots
$$

and

$$
\cdots \to \operatorname{Tor}_2(M_3, N) \to \operatorname{Tor}_1(M_1, N) \to \operatorname{Tor}_1(M_2, N) \to \operatorname{Tor}_1(M_3, N)
$$

$$
\to M_1 \otimes_A N \to M_2 \otimes_A N \to M_3 \otimes_A N \to 0.
$$

