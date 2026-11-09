# w47-mu: does a graph family force HJ's enumeration channel?

Moonshot memo, branch `w47-mu`, 2026-11-09. HJ = Hajiaghayi–JafariRaviz, arXiv:2611.01399 (LaTeX source; line numbers `L…`). Every statement about "HJ" is about the algorithm **as written** and assumes that each recursive call returns the exact coset it is specified to return (hypothesis (H0): HJ is correct; it is unrefereed). Nothing here is machine-checked. Labels: **[PROVEN]** (full argument here, given cited results and HJ as written), **[SKETCH]** (argument with named gaps), **[CONDITIONAL: …]**, **[SPECULATION]**. "Not found" means not found in the searches of §7. Code: `docs/w47-code/`.

## 0. Summary

**Outcome: a graph family, not a barrier.** The incidence graphs $X_m$ of $\mathrm{PG}(m-1,2)$, the same family as w18's Theorem B1, force HJ as written to enumerate a primitive quotient isomorphic to $\mathrm{GL}(m-2,2)$ of degree $\Theta(n)$. So the enumeration (Lie-rank) channel is real on graphs for HJ as written, with $\mu=(\tfrac18+o(1))\log_2 N$, and on this family it is larger than the proved $\sigma$ chain. The mechanism is the left projection of the first-rectangle answer: a coloring-stabilizer group that appears only *after* a recursive answer is imposed.

| # | Statement | Status |
|---|---|---|
| A | For $m\ge\max(\kappa,7,m_0)$ and $Y\cong X_m$, HJ on $(X_m,Y)$ reaches a `Continue` node that enumerates $P\cong\mathrm{GL}(m-2,2)$ on the $2$-subspaces of $\mathbb F_2^{m-2}$, creating $\vert P\vert\ge 0.288\cdot2^{(m-2)^2}=n^{(1/4)\log_2 n-O(1)}=N^{(1/16)\log_2 N-O(1)}$ children | **[PROVEN, given HJ as written and (H0)]** §3 |
| A′ | Same count on the Grassmann graphs $J_2(m,2)$ (the block graphs of $\mathrm{PG}(m-1,2)$) | **[PROVEN, given HJ as written and (H0)]** §3.6 |
| L | For $m\ge5$, $\mathrm{Aut}(W,R;\text{meet})\cong\mathrm{GL}(V)_\ell$, acting faithfully on $W$ (the first rectangle of $\mathrm{PG}(m-1,2)$) | **[PROVEN]** §3.3; exact checks $m=5,\dots,8$ |
| B | The action of $\mathrm{GL}(V)_\ell$ on $W$ has exactly one nontrivial block system, with primitive quotient $\mathrm{GL}(m-2,2)$ on $2$-spaces | **[PROVEN]** §3.4; exact checks $m=5,6$ |
| C | Answer-free nodes have only natural or $2$-subset giants as primitive quotients, so enumeration there costs $O(1)$ per node. A superconstant enumeration needs an answer-group ancestor (window automorphism group, rectangle projection, or configuration answer) | **[PROVEN]** §2 |
| D | Automorphism pruning removes the enumeration on $X_m$: the image of $F_\ell$ is all of $P$ | **[PROVEN]** §5.1 |
| E | No theorem "enumerated quotients on graphs have order $\exp(o(\log^2 N))$" can hold for HJ as written | **[PROVEN, given A]** |
| F | Enumeration survives on graphs with non-trivial but structured $\chi$ (T2 family) | **[SKETCH]** §4 |
| G | Whether any graph forces a superpolynomial enumeration *after* automorphism pruning | **open**; candidate obstruction in §5.3 **[SPECULATION]** |

**What this does and does not say.** Theorem A bounds HJ's dispatcher. It is not a lower bound for GI: $X_m$ is a fixed projective geometry, recognizable in polynomial time, and pruning kills the cost (D). So the evidence "graphs are easier than strings because enumeration cannot be forced on them" is not available for HJ as written. The question whether GI is easier than string isomorphism under general groups is untouched (§6).

---

## 1. Literature and context

The enumeration test, the charge and the dispatcher are as in `docs/moonshot-theory.md` §2.5 (L1766–1772, L1494–1504, L3067–3087). Prop 2 there forces enumeration for *strings* under $\mathrm{AGL}(k,2)$. `docs/w18-latin.md` Theorem B1 forces the $\sigma x$ channel on $X_m$. `docs/hardness.md` found no enumeration in experiments at $n\le300$. Neither the campaign's earlier documents nor the searches of §7 give a graph family for the enumeration channel.

Neuen's survey Q4.8 asks for an fpt reduction from SI (parameter: composition width) to GI (parameter: degree). That is a different question: $X_m$ has maximum degree $\Theta(n^{1/2})$ and composition width $2^m-1=\Theta(n^{1/2})$ (the alternating width is $\Theta(m)$), so it is outside the bounded-parameter regime of Q4.8.

---

## 2. How groups evolve on a graph input

Root: $G=\mathrm{Sym}(n)$ on $\Omega=[n]^2$ (L585–600), processed orbit by orbit, largest first (L621–626), so the off-diagonal orbit $\Omega_1$ comes first. Every group at a later node is produced from the parent's by one of the following.

| op | what | group-theoretic effect |
|---|---|---|
| O1 | fresh `Solve` | faithful image only |
| O2 | orbit chain | restriction to an orbit; later orbits under conditional coset |
| O3 | kernels | enumeration children under $\ker\rho$; certificate $N_i=\ker(\phi_T\vert_{A_i})$; sign kernel of normalization |
| O4 | product refinement | kernel of the top permutation of product coordinates |
| O5 | Young preimage | balanced partition overcoset, or Case 2a large-symmetry subgroup: $\pi^{-1}$ of a product of symmetric groups on label classes |
| O6 | row step | change of coordinates, retained row/column partitions (L1260ff) |
| O7 | rectangle query | $\mathrm{Sym}(W)\times\mathrm{Sym}(R)$ on $W\times R$ (query child only, L1051–1055) |
| **A1** | window update | $A_{i+1}=\mathrm{Aut}_{A_i}^{V_i}(x)$, the partial automorphism group of the marked window (L791–793) |
| **A2** | rectangle continuation | $H=\pi^{-1}(L\times\mathrm{Sym}(\Gamma\setminus W))$, $L$ the left projection of $\mathrm{Aut}(W,R;\text{matrix})$ (L1056, L4538ff) |
| **A3** | configuration continuation | $\pi^{-1}$ of $K_C=\mathrm{Aut}(C)$ extended, $q\le\lambda$ (L1048–1050, Lemma exact-configuration) |

Operations A1–A3 are the *answer* operations: they replace a group by the stabilizer of data that was just verified, so the resulting group is a function of the input. O1–O7 depend on the input only through the choice of label classes.

**Definition.** A permutation group is *Young* if it is, up to the sign kernels of O3, a product $\prod_i\mathrm{Sym}(\Gamma_i)$ acting on an orbit of ordered pairs of $\bigsqcup\Gamma_i$. A node is *answer-free* if the path from the root uses only O1–O7.

**Theorem C. [PROVEN, given HJ as written.]** Let $v$ be an answer-free node. Then the group at $v$ is Young, and every primitive quotient exposed at $v$ is $\mathrm{Alt}(\Gamma_i)$ or $\mathrm{Sym}(\Gamma_i)$ in its natural action or on $2$-subsets, or has bounded degree. Consequently the enumeration test at $v$ accepts only groups of bounded order: a giant of degree $q$ passes $|P|\le\exp(a\log^2d)$ only for $q\le q_1(a)$, a constant depending only on $a$.

*Proof.* The root is Young. O2 and O3 send Young groups to Young groups: orbits on pairs are $\Gamma_i\times\Gamma_j$ or the off-diagonal of $\Gamma_i^2$; kernels of natural actions and sign maps drop a factor or pass to the sign kernel. O5 refines the partition of labels. O6 is a change of coordinates of the same product. O7 is $\mathrm{Sym}(W)\times\mathrm{Sym}(R)$ on $W\times R$. The block systems of $\mathrm{Sym}(\Gamma_i)\times\mathrm{Sym}(\Gamma_j)$ on $\Gamma_i\times\Gamma_j$ are the two coordinate partitions, and those of $\mathrm{Sym}(\Gamma_i)$ on ordered pairs are the two coordinate partitions and the unordered-pair partition. Hence the top actions are natural giants or $2$-subset giants of Johnson type. A giant of degree above $q_1$ fails the enumeration test (L1766–1772), in its natural or its $2$-subset action, and the remaining case is bounded degree. ∎

**Corollary.** A primitive quotient that is not a giant of degree $\le q_1$ can be enumerated only at a descendant of an answer operation. So on graphs, the $\mu$ charge at a node is a function of the sections of its *answer* ancestors. For strings under $\mathrm{AGL}(k,2)$ (Prop 2) this ancestor is the input group itself, with no answer needed. This is the exact sense in which enumeration on graphs could fail to be forced: it must be manufactured.

**What is known about the answer groups.** A1 groups along the $\sigma$ chain of B1 stay close to Young groups ($\mathrm{Sym}(Q_j)$ tops with translations, §2.2 of w18); their primitive quotients are giants. A2 and A3 groups can be classical, and that is the content of §3. I do not have a classification of all $L$ and $K_C$ that arise: they can a priori be any group that is the automorphism group of a bipartite graph between label subsets, or of a configuration, respectively, with the restriction that $L$ is the left projection of an *exact* $\mathrm{Aut}$. The families here realize $\mathrm{GL}(k,2)$ on $2$-spaces and, with the changes of §3.6, other classical quotients of unbounded rank **[SKETCH]**.

---

## 3. Theorem A: the rectangle forces $\mathrm{GL}(m-2,2)$

### 3.1 Notation and theorem

$V=\mathbb F_2^m$, $P=V\setminus0$ points, $\mathcal L$ lines (triples $\{a,b,a+b\}$), $X_m$ the incidence graph on $\Gamma=P\sqcup\mathcal L$, $n=|P|+|\mathcal L|$, $|\mathcal L|=(2^m-1)(2^{m-1}-1)/3$. $\mathrm{Aut}(X_m)=\mathrm{GL}(V)$ for $m\ge4$. Fix $\ell\in\mathcal L$, and let $W$ be the lines skew to $\ell$, $R$ the lines meeting $\ell$ in one point: $|W|=(2^m-4)(2^m-8)/6$, $|R|=3(2^{m-1}-2)$. Let $B=(W,R;\text{meet})$.

**Theorem A.** Let $\kappa$ be HJ's certificate size. There is $m_0$, depending only on HJ's constants, such that for $m\ge\max(\kappa,7,m_0)$ and $Y\cong X_m$, the recursion tree of HJ on $(X_m,Y)$ contains a `Continue` node with group $H\vert_{O_{\mathrm{gen}}}\cong\mathrm{GL}(V)_\ell$ whose dispatcher enumerates $P\cong\mathrm{GL}(m-2,2)$ on the $2$-subspaces of $\mathbb F_2^{m-2}$, degree $d=(2^{m-2}-1)(2^{m-3}-1)/3$, creating $|P|=\prod_{i=0}^{m-3}(2^{m-2}-2^i)\ge0.288\cdot2^{(m-2)^2}$ children.

With $\kappa=64$ this means $m\ge64$, so $n\ge2^{125}$. It says nothing about feasible inputs.

Since $d=n/16\,(1+o(1))$ and $N=n(n-1)$: $\log_2|P|=(m-2)^2-O(1)$, $\log_2N=4m-5.17+o(1)$, and $\mu=\log|P|/\log d=(\tfrac18+o(1))\log_2N$ (`path_numbers.py`).

### 3.2 The trace

The step numbers refer to Algorithm `main-recursion` (L1136–1178) and Algorithm `auxiliary` (L1033–1063).

**Step 0: root.** $N=n(n-1)>N_0$ for $m\ge m_0$; the largest orbit of $\mathrm{Sym}(n)$ on $[n]^2$ is $\Omega_1$, the ordered pairs of distinct labels, processed first (L621–626). $\mathrm{Sym}(n)$ on $\Omega_1$ is transitive; the tower has top partition one of: first coordinate, second coordinate, or unordered pair. Its primitive quotient is $\mathrm{Sym}(n)$ on $n$ labels or $2$-subsets; not small; a single alternating factor; `GiantStep` with $\Gamma=[n]$, $q=n>\lambda=N^\alpha$ (since $2\alpha<1$). The physical map is two-label, so no `RowStep` (L1165–1168).

**Step 1: a full test.** Let $T\subset P$ be $\kappa$ linearly independent points ($m\ge\kappa$). $\mathrm{GL}(V)$ induces $\mathrm{Sym}(T)$ on $T$, and $\mathrm{Aut}_{P_T}(x)\le A_i$ for every window, so $\phi_T(A_i)=\mathrm{Alt}(T)$ at every stage. `LocalCertificate` (L781–794) therefore ends `Full`, with $K(T)\le\mathrm{Aut}_G(x)$ and $\phi_T(K(T))=\mathrm{Alt}(T)$. In particular $K(T)\neq1$.

**Step 2: $F=\mathrm{GL}(V)$.** Certificates are equivariant under parent isomorphisms (Lemma local-test; L2723ff), so $F=\langle K(T):T\text{ full}\rangle\trianglelefteq\mathrm{Aut}(X_m)=\mathrm{GL}(V)$, which is simple. Hence $F=\mathrm{GL}(V)$, and it lies in $\mathrm{Alt}(n)$ (GL simple), so the normalization coset containing the isomorphisms is unaffected.

**Step 3: aggregation is Case 2b.** $\mathrm{supp}\,F=\Gamma$. The $F$-orbits on $\Gamma$ are $P$ and $\mathcal L$, and $|\mathcal L|>|\Gamma|/2$ for $m\ge4$; this is Case 2 of Helfgott §6.2 (`BDHv8.tex` L1878ff). $F\vert_{\mathcal L}$ is not a giant, so it is Case 2b, not 2a. $F$ on $\mathcal L$ has rank $3$ (orbitals: equal, meet, skew; $\mathrm{GL}$ is transitive on ordered meeting pairs and on ordered skew pairs), so its transitivity degree is $d=1$ and no anchors are needed (L2798–2807). Choose a proper orbital $O$; both are single orbitals, meet or skew. Its canonical coherent refinement (L2805–2813) is the rank-3 Grassmann scheme: the meet graph on $\mathcal L$ is strongly regular, so its $2$-WL stable coloring is exactly (diagonal, meet, skew). This configuration is homogeneous and primitive (both graphs connected for $m\ge4$).

**Step 4: first rectangle.** $q=n>\lambda$, so the `else` branch of `AuxiliaryReduction` runs (L1047ff). Lemma first-soj-rectangle (L4494): the configuration is primitive; choose the source vertex $\ell$, with target $\ell'$ (below we work in the branch $\ell'=\ell$, $Y=X_m$; other aligned branches are conjugate). Color classes: $\{\ell\}$, $O_1(\ell)$ (lines meeting $\ell$, $=R$, size $3(2^{m-1}-2)$), $O_2(\ell)$ (skew lines, $=W$). $|W|>\eta|C|$ for $m$ large, so there is no balanced partition. In Helfgott's Theorem 5.3 proof (aqua $=O_2$, $x=\ell$): every $y$ with $c(x,y),c(z,y)\ne$ aqua has $c(x,y)=c(z,y)=O_1$ (note $y=x$ is excluded because $c(z,x)=$ aqua), so beige $=$ cyan $=O_1$ and the bipartite graph is $B=(W,R;\text{meet})$ (or its complement, with the same automorphism group). It is nonempty, noncomplete and semiregular.

**Step 5: the rectangle answer.** Lemma inherited-support-two-rectangle (L4407): $\Delta=W\times R\subseteq\Omega_1$ is one orbit of $\phi^{-1}(\mathrm{Sym}(W)\times\mathrm{Sym}(R)\times\mathrm{Sym}(Y))$, $Y=\Gamma\setminus(W\cup R)=P\cup\{\ell\}$, $|Y|\ge2$, so the permitted group on $W\times R$ is the full $\mathrm{Sym}(W)\times\mathrm{Sym}(R)$ (L4480). `Continue` returns the exact $\mathrm{Aut}(B)$ (by (H0)). Its left projection is $L=\mathrm{GL}(V)_\ell$ on $W$ (§3.3).

**Step 6: continuation.** `LiftAndContinue` (L1076ff) calls `Continue` under $H=(L\times\mathrm{Sym}(\Gamma\setminus W))\cap\mathrm{Alt}(n)$. $H$ is intransitive on $\Omega_1$; orbit chain, largest orbit first. $H$ has image all of $L$ on $W$ because the sign can be corrected on $\Gamma\setminus W$ ($|\Gamma\setminus W|\ge2$). Orbits on $W\times W$ are the orbitals of $\mathrm{GL}(V)_\ell$ on $W$; the *generic* orbital $O_{\mathrm{gen}}=\{(w_1,w_2):\dim(\ell+w_1+w_2)=6\}$ has size $|W|(2^m-16)(2^m-32)/6$, and it is the unique largest orbit of $H$ on $\Omega_1$ for $m\ge7$ (`path_numbers.py`: e.g. at $m=7$, $1792>687$ and $1792>314$; $|W\times(\Gamma\setminus W)|$ and $(\Gamma\setminus W)^2$ are smaller). So the first child is `Continue` on $O_{\mathrm{gen}}$ with faithful group $\mathrm{GL}(V)_\ell$. $|O_{\mathrm{gen}}|>N^\gamma$ for $m$ large, so it stays in the phase.

**Step 7: the dispatcher enumerates.** On $O_{\mathrm{gen}}$ the inherited tower has top partition one of: first coordinate, second coordinate, unordered pair (restricted). "Expose" takes the coarsest $G$-invariant partition coarser than the fine end of the top interval (L3176; Lean `Algorithm/Expose.lean`, `Dispatch.lean`). By §3.4 the top partition's quotient has a unique nontrivial system when the top is a coordinate, namely the fibres of $w\mapsto w+\ell$, and the exposed primitive quotient is $P=\mathrm{GL}(U)$ on the $2$-subspaces of $U=V/\ell$. In the unordered-pair tower the exposed primitive quotient is a primitive action of $\mathrm{GL}(U)$ of the same order (§3.4, Remark). $P$ is not Cameron-large (socle $\mathrm{PSL}(m-2,2)$, not an alternating power), and $|P|\le\exp(a\log^2 d)$ holds for every $a\ge1$ and large $m$ ($\log_2|P|\approx(m-2)^2$, $\log_2 d\approx 2m-5$; HJ's $a$ is much larger). So **the enumeration branch of the dispatcher fires** (L1154–1156; Lean `PrimitiveQuotient.dispatch`), creating one `Continue` child per coset of $\ker\rho$, $|P|$ in all. There is no early exit (redteam-w1-fpt §1.5). ∎

### 3.3 Lemma L: $\mathrm{Aut}(B)$

Write $U'=(V/\ell)\setminus0$; for $r\in R$ write $r=\langle p,x\rangle$, $p=p(r)\in\ell\setminus0$, $x\notin\ell$, and $u(r)=\bar x\in U'$. Then $r$ has exactly two points outside $\ell$, namely $x$ and $x+p$. For $r\ne r'$ in $R$ let $\lambda(r,r')=|N_B(r)\cap N_B(r')|$.

**Lemma 3.1 (codegrees). [PROVEN]** For $m\ge5$, and $r\neq r'$ in $R$:
* $u(r)\neq u(r')$: $\lambda=4$;
* $u(r)=u(r')$, $p(r)=p(r')$: $\lambda=0$;
* $u(r)=u(r')$, $p(r)\neq p(r')$: $\lambda=2^{m-1}-4$;

and the three values are distinct for $m\ge5$.

*Proof.* A common neighbor $w\in W$ meets $r$ in exactly one point (it is skew to $\ell\ni p(r)$) and meets $r'$ in exactly one point. If $u(r)\ne u(r')$, each of the $2\times2$ choices $q\in r\setminus\{p(r)\}$, $q'\in r'\setminus\{p(r')\}$ gives a distinct line $w=\langle q,q'\rangle$ skew to $\ell$ (since $\bar q\ne\bar q'$), so $\lambda=4$. If $u(r)=u(r')$ and $q\neq q'$ then $q+q'\in\ell\setminus0$, so $\langle q,q'\rangle$ meets $\ell$: no such $w$. Hence $w$ must pass through a common point of $r,r'$. If $p(r)=p(r')$ the lines $r\ne r'$ meet only in $p(r)$, so $\lambda=0$. If $p(r)\ne p(r')$, then $r\cap r'$ is one point $z$ (the cosets of $\langle p(r)\rangle$ and $\langle p(r')\rangle$ in $\ell$ meet once), and $w$ can be any line through $z$ other than the three $\langle z,p_i\rangle$: $2^{m-1}-1-3=2^{m-1}-4$. ∎

So every $\sigma\in\mathrm{Aut}(B)$ permutes the classes $Y_u=\{r:u(r)=u\}$, each of size $6$, and preserves the perfect matching on $Y_u$ given by $\lambda=0$ (same $p$).

For a triple in $Y_u$ with pairwise distinct $p$ (recognizable: no $\lambda=0$ pairs), the common neighbors are the lines through the common point if the triple is concurrent, $2^{m-1}-4>0$ of them, and none otherwise (the same argument: $w$ must pass through each pairwise intersection, and two distinct such points give a line meeting $\ell$). So $\sigma$ preserves concurrency. The four concurrent triples of $Y_u$ correspond to the four points of $V\setminus\ell$ above $u$. This defines a permutation $\psi=\psi_\sigma$ of $V\setminus\ell$ preserving the fibres over $V/\ell$.

For $w\in W$, $N_B(w)$ is the union of the three concurrent triples of its three points. So $\psi$ maps the point set of $w$ to the point set of $\sigma(w)$: $\psi$ preserves lines skew to $\ell$.

**Additivity.** For $x,y\notin\ell$ with $\bar x\neq\bar y$, the line $\langle x,y\rangle$ is skew to $\ell$, so $\psi(x+y)=\psi(x)+\psi(y)$. Fix $p\in\ell\setminus0$. A *pair of label $p$* is $\{x,x+p\}$, $x\notin\ell$. Define $f(\{x,x+p\})=\psi(x)+\psi(x+p)$; it lies in $\ell\setminus0$ since $\psi$ preserves fibres and is injective. For $x'$ with $\bar x'\ne\bar x$,
$$\psi(x+x')+\psi(x+x'+p)=\psi(x)+\psi(x+p),$$
using additivity twice ($\psi(x+x')=\psi(x)+\psi(x')$, $\psi(x+p+x')=\psi(x+p)+\psi(x')$). So $f$ is invariant under translating the pair by any $x'$ with $\bar x'\ne\bar x$. Any two pairs of label $p$ are connected by such translations: from a pair over $u$ to either pair over $t\ne u$, translate by a lift of $u+t$ (the four lifts cover both pairs); and two pairs over the same $u$ are joined through a third fibre. So $f\equiv\pi(p)$ is constant on pairs of label $p$. By Lemma 3.1 (same $u$, different $p$ have $\lambda\ne0$), $\pi$ is a permutation of $\ell\setminus0$, hence linear. Extending $\psi$ by $\pi$ on $\ell\setminus0$ and $0\mapsto0$ gives an additive bijection of $V$ fixing $\ell$: a linear map $g\in\mathrm{GL}(V)_\ell$ inducing $\sigma$ on $W$ and on $R$.

**Lemma L. [PROVEN]** For $m\ge5$, restriction gives $\mathrm{Aut}(B)\cong\mathrm{GL}(V)_\ell$, and the action on $W$ is faithful. (A $g$ fixing all lines skew to $\ell$ fixes every point of $V\setminus\ell$, as an intersection of two such lines, hence $g=1$.) The converse is immediate. ∎

Machine check: `rect_check.py` compares nauty's $|\mathrm{Aut}(B)|$ to $|\mathrm{GL}(m,2)|/\#\text{lines}$ exactly for $m=5,6,7$ (exact, also on $W$), and $m=8$ (floating); `lambda_check.py` confirms all codegrees for $m=5,6$.

### 3.4 Block systems of $\mathrm{GL}(V)_\ell$ on $W$

**Lemma B. [PROVEN]** Let $k=m-2\ge3$, $V=\ell\oplus U$, $A=\mathrm{GL}(V)_\ell$. $A$ on $W$ has exactly one nontrivial block system, the fibres of $w\mapsto\bar w\in G_2(V/\ell)$ (size $16$). The block action is $P=\mathrm{GL}(U)$ on $G_2(U)$, primitive of order $|\mathrm{GL}(k,2)|$ ($k\ge3$).

*Proof.* Let $Q=\mathrm{Hom}(U,\ell)\trianglelefteq A$, $A/Q\cong\mathrm{GL}(\ell)\times\mathrm{GL}(U)$. For $w\in W$ with image $\bar w$, $A_w\cap Q=\mathrm{Hom}(U/\bar w,\ell)$ and $A_wQ/Q=\mathrm{GL}(\ell)\times\mathrm{GL}(U)_{\bar w}$. Let $A_w\le T\le A$. $M=T\cap Q$ is $A_w$-invariant, and $M/\mathrm{Hom}(U/\bar w,\ell)$ is a $(\mathrm{GL}(\bar w)\times\mathrm{GL}(\ell))$-submodule of $\mathrm{Hom}(\bar w,\ell)$. This module is the tensor product of two absolutely irreducible $2$-dimensional modules, hence irreducible, so $M=\mathrm{Hom}(U/\bar w,\ell)$ or $M=Q$. Since $\mathrm{GL}(U)_{\bar w}$ is a maximal parabolic, $TQ/Q$ is either $\mathrm{GL}(\ell)\times\mathrm{GL}(U)_{\bar w}$ or all of $A/Q$. If $M=Q$ this gives $T=A_wQ$ or $T=A$. If $M=\mathrm{Hom}(U/\bar w,\ell)$ and $TQ/Q$ is all of $A/Q$, then $M$ would be $\mathrm{GL}(U)$-invariant, which is false for $k\ge3$; so $TQ/Q=A_wQ/Q$ and $T=A_w$. Thus the only proper intermediate subgroup is $A_wQ$, the fibre stabilizer. The block action is that of $\mathrm{GL}(U)$ on $G_2(U)$, where $\mathrm{GL}(U)_{\bar w}$ is maximal. ∎

**Remark (the tower does not matter). [PROVEN]** If the inherited top partition of $O_{\mathrm{gen}}$ is the unordered-pair partition, the exposed primitive quotient is again $\mathrm{GL}(U)$ in a primitive action, for $k\ge5$. Indeed a maximal $T\supseteq A_{\{w_1,w_2\}}$ with $T\not\supseteq Q$ has $TQ=A$, so $T\cap Q$ is $A$-invariant in the irreducible module $Q$, so $T\cap Q=0$; but $A_{\{w_1,w_2\}}\cap Q=\mathrm{Hom}(U/(\bar w_1+\bar w_2),\ell)\neq0$. So $T\supseteq Q$, and $T/Q$ contains the $\mathrm{GL}(\ell)$ factor, so the action is that of $\mathrm{GL}(U)$ on the cosets of a maximal subgroup, faithful by simplicity of $\mathrm{GL}(k,2)$, $k\ge3$. Its degree is at most $s$; since $\mathrm{GL}(k,2)$ has minimal degree $2^k-1$, the Small test holds for $a\ge1/\ln2$ for every primitive action, and HJ's $a$ is larger. The block-system count in Lemma B also holds for every choice of first or second coordinate.

Machine check: `rect_check.py` exhibits, for $m=5,6$, minimal blocks of sizes exactly $16$ and $|W|$ (Atkinson over all points) and $P$ of the expected order, primitive.

### 3.5 What is and is not assumed

(1) (H0) is used in Steps 1, 5, 7: the local certificates and `Solve` calls return exact answers. Without (H0) HJ may not reach this node. (2) "As written" includes: no automorphism pruning, the Case 2b rule and its orbital branching (L2798–2830), and the first-rectangle rule. These are read from the text and from Helfgott's proof; the sentence "selects a different color class and an edge color" is resolved by the unique choice of Step 4. (3) Only the existence of one `Full` test is used, so the conclusion does not depend on the unknown cost of certificates or the $\sigma$ chain. (4) Theorem A counts the *children created*; this is the same standard as Prop 2 and Theorem B1. The children are not all expensive: each is a `Continue` on kernel orbits under a small group.

### 3.6 Variants

* **$J_2(m,2)$ (Grassmann graph of $\mathrm{PG}(m-1,2)$), Theorem A′.** Same trace: $\Gamma=\mathcal L$, $\mathrm{Aut}=\mathrm{GL}(V)$ for $m\ne4$ (Chow), $F=\mathrm{GL}(V)$, CC $=$ the graph's own rank-3 scheme, and $Y=\{\ell\}$ so $|Y|=1$: the permitted group is the even-product-sign subgroup of $\mathrm{Sym}(W)\times\mathrm{Sym}(R)$ (L4482). The left projection $L$ then has index $\le2$ in $\mathrm{GL}(V)_\ell$; since $\mathrm{GL}(m-2,2)$ is perfect the image in $P$ is unaffected and the count is the same. **[PROVEN, given HJ as written and (H0)]**, with the same $m_0$ dependence.
* **$J_q(m,2)$, fixed $q$.** Expect $P=\mathrm{PGL}(m-2,q)$ on lines, order $n^{\Theta(\log n)}$. Lemma 3.1 must be redone for $q>2$ (the point sets of $r$ and the codegree values change). **[SKETCH]**
* **Lines of polar spaces** ($W(2k-1,2)$, $Q^\pm(2k-1,2)$). Rank $>3$ on lines but the same mechanism is likely. **[SPECULATION]**

Other candidates: see §4.

---

## 4. Other candidates (Task 2)

| family | HJ at the root | outcome |
|---|---|---|
| $X_m$, $J_2(m,2)$ | Case 2b, unbalanced rank 3 | Theorem A, A′ |
| T2 $X_\chi$, $\chi$ constant | $X_\chi=\mathrm{PG}(d+2,2)$, i.e. $X_{d+3}$ | Theorem A |
| T2 $X_\chi$, $\chi=\mathbf 1_{W_0}$ (subspace) | $\mathrm{Aut}=$ parabolic of $W_0$ extended by gauge $\mathrm{Hom}(V/W_0,Z)$; expected Case 2b on generic lines with $F=\mathrm{Aut}$ | enumeration of the Levi quotient, of order $2^{\Omega(d^2)}$, expected, with $L$ realized by $F$ **[SKETCH]**: not done are the check that generic lines are one $F$-orbit of more than half of $\Gamma$, and the rectangle automorphism computation |
| T2 $X_\chi$, $\chi$ generic | rigid, $F=1$; Case 3 with fine tuple colors (windows see $\chi$ at the first Step-4 orbit, §5.3) | balanced colored partitions, Young continuation, no large Lie quotient **[SKETCH]** |
| $\mathrm{VO}^\pm(2m,2)$, Sylvester Hadamard | valency $\approx n/2$: first color classes are balanced, so a Young overcoset, not a rectangle | not traced further; balanced Young steps precede any rectangle. **[SPECULATION]** that a deeper rectangle reappears |
| GQ point graphs, Paley, cyclotomic Cayley | $\vert\mathrm{Aut}\vert=n^{O(1)}$, or solvable | enumerated quotients of order $n^{O(1)}$ at most, no $N^{\Omega(\log N)}$ |
| Kerdock, generic Cayley on $\mathbb F_2^k$ | $\mathrm{Aut}$ small | no full tests or small $F$; no large $L$ expected **[SPECULATION]** |

The recipe that emerges: *unbounded Lie rank over a bounded field, and a dominant skew-type orbital so that the first rectangle is unbalanced.*

---

## 5. Pruning, and the barrier that remains

### 5.1 Proposition D: pruning kills the enumeration on $X_m$. **[PROVEN]**

$F_\ell=\mathrm{GL}(V)_\ell\le H$, it preserves $x$, and its image in $P$ is all of $P$. So at the enumeration node every coset of $\ker\rho$ meets $F_\ell$ and all children but one are redundant under known automorphisms. This is the automorphism pruning of w28, now applied at the enumeration node as well as at tests and aggregation branches. Note that the required automorphisms are available: $F$ was computed at the root.

So Theorem A and Theorem B1 of w18 have the same status: they are lower bounds on HJ as written, with the channel removable on this family by certified automorphisms.

### 5.2 Barrier attempt, refuted as stated

**Statement attempted.** "On graph inputs, every enumerated quotient has order $\exp(o(\log^2N))$." This is **false for HJ as written** (Theorem A, E).

**Surviving form.** Replace "enumerated" by "enumerated after pruning by certified automorphisms".

### 5.3 The remaining question: enumeration not covered by automorphisms

To force enumeration against pruning one needs $L$ with a large classical quotient not realized by $\mathrm{Aut}(X)$.

* **Case 2b.** $F\le\mathrm{Aut}(X)$ and the configuration is the coherent closure of an $F$-orbital. For the Grassmann scheme, $F$ must be transitive on an orbital (meeting pairs or skew pairs of lines). I expect this to force $F\ge\mathrm{SL}(V)$ for large $m$, by Cameron–Kantor-style classification, but I did not check that this orbital-transitivity implies antiflag-transitivity, and the classification is cited from memory **[SPECULATION]**. If so, $F_\ell$ covers $P$ and no gap between $F$ and $L$ is available on this scheme. The general question is whether $\mathrm{Aut}(O)/F$ can be superpolynomial for orbitals of $F$ with classical $\mathrm{Aut}(O)$ of unbounded rank. **[SPECULATION: no, by rank-3 classification style arguments, for Schurian closures.]**
* **Case 3** ($F$ small). Tuple colors come from the windows. For *rigid* $X$, a generic test is sent to `Nonfull` only when a window sees asymmetric data; on $X_{m,R}$ or generic $X_\chi$, that window contains a large orbit and the color is fine, so the Design Lemma yields a balanced partition rather than a coarse configuration. **[SKETCH]** Coarse configurations need tuple colors that are local (generic tests `Nonfull` at bounded depth). That requires dense patterns (edge density at least a constant, and below $1-\eta$ so the rectangle is unbalanced). Then $R$ has constant density, and I expect that $B$ determines $X$, as it does for the Grassmann rectangle, so that $L$ is $\mathrm{Aut}(X)$-covered **[SPECULATION]**; no general rigidity statement is proved here.

**Conjecture (obstruction for pruned HJ). [SPECULATION]** At every node of HJ on a graph input where a Cameron-small quotient $P$ is enumerated after a rectangle continuation, $|P|\le N^{O(1)}\cdot|\text{image of }\mathrm{Aut}_H(x)\text{ in }P|$.

This is the concrete statement that would give "enumeration is automorphism-prunable on graphs". I have no proof; a counterexample would be a graph, locally like $\mathrm{PG}$, with a rectangle having large classical symmetry that is not global. The natural test family is T2 with $\chi$ of intermediate structure, which is where I would look next.

---

## 6. Consequences

**About HJ (proven, given (H0) and HJ as written).**
1. The enumeration term of the exponent $O(\log N(\log w+\mu+\log\log N))$ is attained on graph inputs: $\mu=\Theta(\log N)$ on $X_m$, the charge at that node is $\Theta(\log^2N)$ of potential (L1494–1504), and the single enumeration creates $\exp(\Theta(\log^2N))$ children.
2. The two channels are both real on graphs, and on $X_m$ the enumeration count $2^{(m-2)^2-O(1)}$ exceeds the certificate-chain count $2^{m^2/2-O(m)}$ of B1. So "HJ is $n^{\Theta(\log n)}$ on graphs" now has a certificate of the enumeration kind as well, with constant $\tfrac14$ in place of $\tfrac18$ in the exponent.
3. Theorem C locates the channel: enumeration on graphs needs an answer group. The rectangle continuation (A2) produces it.

**About the problem.** Nothing is proved about GI. $X_m$ is easy (bounded-depth recognition and linear algebra). Prop D shows the enumeration is not needed on $X_m$ even within HJ's framework.

**GI versus string isomorphism.** The conjectured escape "enumeration cannot be forced on graphs, because graph-derived groups cannot have large affine or classical quotients" is false for HJ as written, since $\mathrm{GL}(m-2,2)$ is the quotient of a graph-derived group. This removes one candidate piece of evidence for a separation; it is not evidence against one. A separation could still come from: (a) automorphism pruning on graph instances (§5.3), or (b) non-HJ methods. Neuen Q4.8 (fpt reductions, degree vs. composition width) is not addressed.

---

## 7. Experiments and what they do not show

* `docs/w47-code/rect_check.py` (pynauty + sympy): $m=5,\dots,8$: $|\mathrm{Aut}(B)|=|\mathrm{GL}(V)_\ell|$; exact on $W$ for $m\le7$; for $m=5,6$: block systems unique, $P$ primitive of order $168$, $20160$.
* `docs/w47-code/lambda_check.py`: all codegrees and concurrency counts of §3.3 at $m=5,6$.
* `docs/w47-code/path_numbers.py`: sizes along the trace, the $O_{\mathrm{gen}}$ condition ($m\ge7$), the exponents.

**The Python solver (`gi/`).** Run on $X_3$ and $J_2(4,2)$ with `ir=0, refine="none", staged=False`: it answers through the Young-label step (`young_root`, `young_ind`), with at most $9$ small enumerations. It does not implement the Case 2b orbital, the coherent refinement, or the first rectangle, and $\kappa=3$ is far below any size where a full independent test exists at relevant scale. So it does not exercise this path, and the absence of enumeration in `docs/hardness.md` is not evidence about it. What transfers: only the group-theoretic facts in §3.3–3.4, which are checked exactly.

**Limits.** Theorem A needs $m\ge\kappa=64$ for HJ's constants. No experiment reaches the regime; the path has no instance below $n\approx2^{125}$ except by lowering $\kappa$, which changes the algorithm.

**Novelty searches (2026-11-09).** Web searches for analyses of HJ's dispatcher and for lower bounds of Luks-style enumeration on graph families returned nothing relevant; the HJ paper itself did not surface. I claim "not found", not "new". The reconstruction in Lemma L is elementary and I would not be surprised to find it in the design-theory literature. The observation that a Luks enumeration step can fire on Grassmann instances in Babai-type algorithms is also not found stated, and may be folklore.

---

## 8. Leads

1. **T2 with structured $\chi$** (§4): complete the Case 2b trace for $\chi=\mathbf 1_{W_0}$, and find the first $\chi$ with $\mathrm{Aut}$ small where the configuration stays coarse. This is the direct test of the conjecture of §5.3.
2. **A rectangle-automorphism theorem**: when does a first rectangle determine its graph? Give a general form of Lemma L for rank-3 schemes.
3. **Pruned HJ.** Combine w28's P1 with the enumeration pruning of Prop D into one modified algorithm and redo its potential: is the per-phase exponent improved on any class?
4. **Case 2b rigidity**: is $[\mathrm{Aut}(\text{closure of }O):F]$ polynomial for unbounded-rank classical closures? (§5.3)
5. **Nested enumeration:** after the first enumeration, is there any graph with a second superconstant enumeration on the path (a tower of two Lie-type quotients)?

Sources: arXiv:2611.01399 (local LaTeX) · [Helfgott, arXiv:1710.04574](https://arxiv.org/abs/1710.04574) (local source) · [Babai, arXiv:1512.03547](https://arxiv.org/abs/1512.03547) · Neuen, Comput. Sci. Rev. 60 (2026), Q4.8 (local copy) · Cameron–Kantor, *2-transitive and antiflag transitive collineation groups*, J. Algebra (1979), from memory, not re-read for this memo.
