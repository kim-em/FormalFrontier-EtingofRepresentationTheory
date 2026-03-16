**Theorem 3.6.2.** *(i) Characters of (distinct) irreducible finite dimensional representations of $A$ are linearly independent.*

*(ii) If $A$ is a finite dimensional semisimple algebra, then these characters form a basis of $(A/[A, A])^*$.*

**Proof.** (i) If $V_1, \ldots, V_r$ are nonisomorphic irreducible finite dimensional representations of $A$, then the map

$$\rho_{V_1} \oplus \cdots \oplus \rho_{V_r} : A \to \operatorname{End} V_1 \oplus \cdots \oplus \operatorname{End} V_r$$

is surjective by the density theorem, so $\chi_{V_1}, \ldots, \chi_{V_r}$ are linearly independent. (Indeed, if $\sum \lambda_i \chi_{V_i}(a) = 0$ for all $a \in A$, then $\sum \lambda_i \operatorname{Tr}(M_i) = 0$ for all $M_i \in \operatorname{End}_k V_i$. But each $\operatorname{Tr}(M_i)$ can range independently over $k$, so it must be that $\lambda_1 = \cdots = \lambda_r = 0$.)

(ii) First we prove that $[\operatorname{Mat}_d(k), \operatorname{Mat}_d(k)] = \mathfrak{sl}_d(k)$, the set of all matrices with trace $0$. It is clear that $[\operatorname{Mat}_d(k), \operatorname{Mat}_d(k)] \subseteq \mathfrak{sl}_d(k)$. If we denote by $E_{ij}$ the matrix with $1$ in the $i$th row of the $j$th column and $0$'s everywhere else, we have $[E_{ij}, E_{jm}] = E_{im}$ for $i \neq m$ and $[E_{i,i+1}, E_{i+1,i}] = E_{ii} - E_{i+1,i+1}$. Now $\{E_{im}\} \cup \{E_{ii} - E_{i+1,i+1}\}$ forms a basis in $\mathfrak{sl}_d(k)$, so indeed $[\operatorname{Mat}_d(k), \operatorname{Mat}_d(k)] = \mathfrak{sl}_d(k)$, as claimed.

By semisimplicity, we can write $A = \operatorname{Mat}_{d_1}(k) \oplus \cdots \oplus \operatorname{Mat}_{d_r}(k)$. Then $[A, A] = \mathfrak{sl}_{d_1}(k) \oplus \cdots \oplus \mathfrak{sl}_{d_r}(k)$, and $A/[A, A] \cong k^r$. By Theorem
3.3.1, there are exactly $r$ irreducible representations of $A$ (isomorphic to $k^{d_1}, \ldots, k^{d_r}$, respectively) and therefore $r$ linearly independent characters on the $r$-dimensional vector space $A/[A, A]$. Thus, the characters form a basis. $\square$

