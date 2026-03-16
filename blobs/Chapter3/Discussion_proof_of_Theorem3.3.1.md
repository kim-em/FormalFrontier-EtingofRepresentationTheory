**Proof of Theorem 3.3.1.** First, the given representations are clearly irreducible, since for any $v \neq 0$, $w \in V_i$, there exists $a \in A$ such that $av = w$. Next, let $X$ be an $n$-dimensional representation of $A$. Then, $X^*$ is an $n$-dimensional representation of $A^{\mathrm{op}}$. But $(\operatorname{Mat}_{d_i}(k))^{\mathrm{op}} \cong \operatorname{Mat}_{d_i}(k)$ with isomorphism $\varphi(X) = X^T$, as $(BC)^T = C^T B^T$. Thus, $A \cong A^{\mathrm{op}}$ and $X^*$ may be viewed as an $n$-dimensional representation of $A$. Define

$$\phi : \underbrace{A \oplus \cdots \oplus A}_{n \text{ copies}} \longrightarrow X^*$$

by

$$\phi(a_1, \ldots, a_n) = a_1 y_1 + \cdots + a_n y_n$$

where $\{y_i\}$ is a basis of $X^*$. The map $\phi$ is clearly surjective, as $k \subset A$. Thus, the dual map $\phi^* : X \longrightarrow A^{n*}$ is injective. But $A^{n*} \cong A^n$ as representations of $A$ (check it!). Hence, $\operatorname{Im} \phi^* \cong X$ is a subrepresentation of $A^n$. Next, $\operatorname{Mat}_{d_i}(k) = d_i V_i$, so $A = \bigoplus_{i=1}^r d_i V_i$, $A^n = \bigoplus_{i=1}^r n d_i V_i$, as a representation of $A$. Hence by Proposition 3.1.4, $X = \bigoplus_{i=1}^r m_i V_i$, as desired. $\square$
