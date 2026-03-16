**Problem 8.2.5.** In this problem we will show that the cohomology groups $\mathrm{Tor}_i$ and $\mathrm{Ext}^i$ don't really depend on the projective resolution $P_\bullet$, in a fairly strong sense, which justifies the fact that we don't mention $P_\bullet$ in the notation for them.

Let $P_\bullet$, $Q_\bullet$ be two projective resolutions of $M$. Let $d^P_i : P_i \to P_{i-1}$, $d^Q_i : Q_i \to Q_{i-1}$ be the corresponding differentials; in particular, $d^P_0 : P_0 \to M$, $d^Q_0 : Q_0 \to M$.

(i) Show that there exists a homomorphism $f_0 : P_0 \to Q_0$ such that $d^Q_0 \circ f_0 = d^P_0$.

(ii) Proceed to show by induction in $j$ that there exists a homomorphism $f_j : P_j \to Q_j$ such that $d^Q_j \circ f_j = f_{j-1} \circ d^P_j$.
The collection of homomorphisms satisfying the conditions of (i) and (ii) is called a **morphism of resolutions**, $f : P_\bullet \to Q_\bullet$.

(iii) Clearly, such a morphism $f$ defines a linear map $\psi_i(P, Q, f) : \mathrm{Tor}_i^P(M, N) \to \mathrm{Tor}_i^Q(M, N)$, where the superscripts $P$ and $Q$ mean that the Tor groups are defined using the resolutions $P_\bullet$ and $Q_\bullet$. Show that the maps $\psi_i(P, Q, f)$ don't really depend on $f$ (so they can be denoted by $\psi_i(P, Q)$).

(iv) Deduce that $\psi_i(P, Q)$ are isomorphisms (use that $\psi_i(P, P) = \mathrm{id}$ and $\psi_i(Q, R) \circ \psi_i(P, Q) = \psi_i(P, R)$).

(v) Define similar maps $\xi_i(Q, P, f) : \mathrm{Ext}^i_P(M, N) \to \mathrm{Ext}^i_Q(M, N)$ and show that they are independent on $f$ and are isomorphisms.

