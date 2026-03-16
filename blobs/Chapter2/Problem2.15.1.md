**Problem 2.15.1.** According to the above, a representation of $\mathfrak{sl}(2)$ is just a vector space $V$ with a triple of operators $E, F, H$ such that $HE - EH = 2E$, $HF - FH = -2F$, $EF - FE = H$ (the corresponding map $\rho$ is given by $\rho(e) = E$, $\rho(f) = F$, $\rho(h) = H$).
Let $V$ be a finite dimensional representation of $\mathfrak{sl}(2)$ (the ground field in this problem is $\mathbb{C}$).

(a) Take eigenvalues of $H$ and pick one with the biggest real part. Call it $\lambda$. Let $\bar{V}(\lambda)$ be the generalized eigenspace corresponding to $\lambda$. Show that $E|_{\bar{V}(\lambda)} = 0$.

(b) Let $W$ be any representation of $\mathfrak{sl}(2)$ and let $w \in W$ be a nonzero vector such that $Ew = 0$. For any $k > 0$ find a polynomial $P_k(x)$ of degree $k$ such that $E^k F^k w = P_k(H)w$. (First compute $EF^k w$; then use induction in $k$.)

(c) Let $v \in \bar{V}(\lambda)$ be a generalized eigenvector of $H$ with eigenvalue $\lambda$. Show that there exists $N > 0$ such that $F^N v = 0$.

(d) Show that $H$ is diagonalizable on $\bar{V}(\lambda)$. (Take $N$ to be such that $F^N = 0$ on $\bar{V}(\lambda)$, and compute $E^N F^N v$, $v \in \bar{V}(\lambda)$, by (b). Use the fact that $P_k(x)$ does not have multiple roots.)

(e) Let $N_v$ be the smallest $N$ satisfying (c). Show that $\lambda = N_v - 1$.

(f) Show that for each $N > 0$, there exists a unique up to isomorphism irreducible representation of $\mathfrak{sl}(2)$ of dimension $N$. Compute the matrices $E, F, H$ in this representation using a convenient basis. (For $V$ finite dimensional irreducible take $\lambda$ as in (a) and $v \in V(\lambda)$ an eigenvector of $H$. Show that $v, Fv, \ldots, F^\lambda v$ is a basis of $V$, and compute the matrices of the operators $E, F, H$ in this basis.)

Denote the $(\lambda + 1)$-dimensional irreducible representation from (f) by $V_\lambda$. Below you will show that any finite dimensional representation is a direct sum of $V_\lambda$.

(g) Show that the operator $C = EF + FE + H^2/2$ (the so-called **Casimir operator**) commutes with $E, F, H$ and equals $\frac{\lambda(\lambda+2)}{2} \operatorname{Id}$ on $V_\lambda$.

Now it is easy to prove the direct sum decomposition. Namely, assume the contrary, and let $V$ be a reducible representation of the smallest dimension, which is not a direct sum of smaller representations.

(h) Show that $C$ has only one eigenvalue on $V$, namely $\frac{\lambda(\lambda+2)}{2}$ for some nonnegative integer $\lambda$ (use the fact that the generalized
eigenspace decomposition of $C$ must be a decomposition of representations).

(i) Show that $V$ has a subrepresentation $W = V_\lambda$ such that $V/W = nV_\lambda$ for some $n$ (use (h) and the fact that $V$ is the smallest reducible representation which cannot be decomposed).

(j) Deduce from (i) that the eigenspace $V(\lambda)$ of $H$ is $(n+1)$-dimensional. If $v_1, \ldots, v_{n+1}$ is its basis, show that $F^j v_i$, $1 \leq i \leq n+1$, $0 \leq j \leq \lambda$, are linearly independent and therefore form a basis of $V$ (establish that if $Fx = 0$ and $Hx = \mu x$ for $x \neq 0$, then $Cx = \frac{\mu(\mu-2)}{2} x$ and hence $\mu = -\lambda$).

(k) Define $W_i = \operatorname{span}(v_i, Fv_i, \ldots, F^\lambda v_i)$. Show that $W_i$ are subrepresentations of $V$ and derive a contradiction to the fact that $V$ cannot be decomposed.

(l) (Jacobson-Morozov lemma) Let $V$ be a finite dimensional complex vector space and $A : V \to V$ a nilpotent operator. Show that there exists a unique, up to an isomorphism, representation of $\mathfrak{sl}(2)$ on $V$ such that $E = A$. (Use the classification of the representations and the Jordan normal form theorem.)

(m) (Clebsch-Gordan decomposition) Find the decomposition of the representation $V_\lambda \otimes V_\mu$ of $\mathfrak{sl}(2)$ into irreducible components.

Hint: For a finite dimensional representation $V$ of $\mathfrak{sl}(2)$ it is useful to introduce the character $\chi_V(x) = Tr(e^{xH})$, $x \in \mathbb{C}$. Show that $\chi_{V \oplus W}(x) = \chi_V(x) + \chi_W(x)$ and $\chi_{V \otimes W}(x) = \chi_V(x)\chi_W(x)$. Then compute the character of $V_\lambda$ and of $V_\lambda \otimes V_\mu$ and derive the decomposition. This decomposition is of fundamental importance in quantum mechanics.

(n) Let $V = \mathbb{C}^M \otimes \mathbb{C}^N$ and $A = J_{0,M} \otimes \operatorname{Id}_N + \operatorname{Id}_M \otimes J_{0,N}$, where $J_{0,n}$ is the Jordan block of size $n$ with eigenvalue zero (i.e., $J_{0,n} e_i = e_{i-1}$, $i = 2, \ldots, n$, and $J_{0,n} e_1 = 0$). Find the Jordan normal form of $A$ using (l) and (m).

