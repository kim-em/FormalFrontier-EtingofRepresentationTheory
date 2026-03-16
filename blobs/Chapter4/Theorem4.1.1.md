**Theorem 4.1.1** (Maschke). *Let $G$ be a finite group and let $k$ be a field whose characteristic does not divide $|G|$. Then:*

*(i) The algebra $k[G]$ is semisimple.*

*(ii) There is an isomorphism of algebras $\psi : k[G] \to \bigoplus_i \operatorname{End} V_i$ defined by $g \mapsto \bigoplus_i g|_{V_i}$, where $V_i$ are the irreducible representations of $G$. In particular, this is an isomorphism of representations of $G$ (where $G$ acts on both sides by left multiplication). Hence, the regular representation $k[G]$ decomposes into irreducibles as $\bigoplus_i \dim(V_i) V_i$, and one has the "sum of squares formula"*

$$|G| = \sum_i \dim(V_i)^2.$$
**Proof.** By Proposition 3.5.8, (i) implies (ii), and to prove (i), it is sufficient to show that if $V$ is a finite dimensional representation of $G$ and $W \subset V$ is any subrepresentation, then there exists a subrepresentation $W' \subset V$ such that $V = W \oplus W'$ as representations.

Choose any complement $\widehat{W}$ of $W$ in $V$. (Thus $V = W \oplus \widehat{W}$ as *vector spaces*, but not necessarily as *representations*.) Let $P$ be the projection along $\widehat{W}$ onto $W$, i.e., the operator on $V$ defined by $P|_W = \operatorname{Id}$ and $P|_{\widehat{W}} = 0$. Let

$$\overline{P} := \frac{1}{|G|} \sum_{g \in G} \rho(g) P \rho(g^{-1}),$$

where $\rho(g)$ is the action of $g$ on $V$, and let

$$W' = \ker \overline{P}.$$

Now $\overline{P}|_W = \operatorname{Id}$ and $\overline{P}(V) \subseteq W$, so $\overline{P}^2 = \overline{P}$, and so $\overline{P}$ is a projection along $W'$. Thus, $V = W \oplus W'$ as vector spaces.

Moreover, for any $h \in G$ and any $y \in W'$,

$$\overline{P}\rho(h)y = \frac{1}{|G|} \sum_{g \in G} \rho(g) P \rho(g^{-1}h) y$$

$$= \frac{1}{|G|} \sum_{\ell \in G} \rho(h\ell) P \rho(\ell^{-1}) y = \rho(h) \overline{P} y = 0,$$

so $\rho(h)y \in \ker \overline{P} = W'$. Thus, $W'$ is invariant under the action of $G$ and is therefore a subrepresentation of $V$. Thus, $V = W \oplus W'$ is the desired decomposition into subrepresentations. $\square$

