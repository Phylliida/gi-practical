# w30-sts: Steiner triple systems, rank, and the $n^{\log n}$ barrier

Moonshot memo, branch `w30-sts`, 2026-11-09. Code: `docs/w30-sts-code/` (§10). A1, A2, A3 = `docs/w18-latin.md` as corrected by `docs/redteam-w18-latin.md`. Theorem B of w17 = `docs/w17-affine.md`. Nothing here is machine-checked; proofs below are hand proofs. Labels: **[PROVEN]** (complete argument here, given cited results), **[SKETCH]** (argument with named gaps), **[CONDITIONAL: …]**, **[SPECULATION]**. "Not found" refers only to the searches recorded in §1.

## 0. Summary

**The target was not reached.** There is no $n^{o(\log n)}$ algorithm for STS isomorphism here. What the attempt produced: the dichotomy in the brief is proved at the top of the rank range, and its "algebraic" side turns out to contain a problem at least as hard as the campaign's existing barrier, so the dichotomy cannot by itself give an $n^{o(\log n)}$ algorithm.

| # | Statement | Status |
|---|---|---|
| L1 | Rank–closure duality: $\mathrm{rk}(X)=\min_{T}\big(\rho(T)+\lfloor\log_2\frac{n+1}{|T|+1}\rfloor\big)$, minimum over subsystems $T$ | **[PROVEN]** §2 |
| T1 | Every STS is a $\mathrm{PG}(d-1,2)$-fibration above any maximizer $S$ of $\Psi_\lambda(T)=\log_2(|T|+1)-\lambda\rho(T)$, $1<\lambda<\tfrac13\log_2 9$. $S\neq X$ whenever $\mathrm{rk}(X)>\log_2(n+1)/\lambda$; so $\mathrm{rk}\ge 0.947\log_2(n+1)$ forces a nontrivial quotient, with $d\ge \mathrm{rk}-\frac{c}{\lambda-1}$, $c=\log_2(n+1)-\mathrm{rk}$ | **[PROVEN]** §3 |
| P1 | Converse: a $\mathrm{PG}(d-1,2)$-fibration with hole has rank $\ge d$ | **[PROVEN]** §3 |
| T3 | Same theorem over $\mathbb F_q$, $q\ge 2$ an integer, under an index-gap hypothesis above $S$: the cosets form $\mathrm{PG}(d-1,q)$ | **[PROVEN]** §4 |
| T2 | **Barrier.** Linear equivalence of Boolean functions on $\mathbb F_2^d$ reduces in polynomial time to STS isomorphism with $n=2^{d+3}-1$ and $\mathrm{rk}\ge\log_2(n+1)-3$. So $n^{o(\log n)}$ for STS implies $2^{o(d^2)}$ for string isomorphism under $\mathrm{GL}(d,2)$, open in this campaign | **[PROVEN]** §6 |
| T5 | A natural $n^{o(\log n)}$ class: an STS within $D=n^{o(1)}$ blocks of a $\mathrm{PG}$ (canonical decoding, then defect matching in $(6D)^{\min(m,6D)}\mathrm{poly}(n)$) | **[PROVEN]** §7 |
| C4 | Lead from w18: "rank $\Omega(\log n)$ implies locally algebraic" is **false** as stated; the correct form is a *projective quotient*, not local algebra | **[PROVEN]** §5 |
| O | Dichotomy for $\mathrm{rk}\ge\varepsilon\log n$, every fixed $\varepsilon$: open. For slope above $\lambda_0$ I have no structure theorem | open, conjecture in §9 |

Reading of T1+T2 together: above rank $0.947\log_2 n$ "algebraic structure" is a theorem, but it is a projective *base* with arbitrary fibre data. Handling it is exactly string isomorphism under $\mathrm{GL}(d,2)$ plus a gauge problem, and T2 shows no method can avoid the $\mathrm{GL}$ part. Any claimed $n^{o(\log n)}$ for STS should be read as a claim of $2^{o(d^2)}$ for Boolean-function linear equivalence, and is at least that hard.

## 1. State of the art (checked 2026-11-09)

* **Upper bounds.** Miller 1978: $n^{\log_2 n+O(1)}$ via generators [cited in several sources below]. Steiner 2-designs (Babai–Wilmes STOC 2013, improving Spielman): $n^{O(\log n)}$ canonical form. Campaign A1: $n^{(1/2)\log_2 n+O(1)}$ deterministic. No $n^{o(\log n)}$ for STS, Latin squares, or conference graphs was found.
* **Complexity-class refinements** (not better $n$-dependence): Levet ($\exists^{\log^2 n}\mathrm{AC}^0$, as cited in the next paper), Collins–Grochow–Levet–Weiß arXiv:2402.00133 (quasi-$\mathrm{AC}^0$ for STS and related).
* **Average case.** Gill–Mammoliti–Wanless arXiv:2402.06205: uniform Latin squares a.a.s. have no subsquare of order above $n^{1/2}\log^{1/2+\varepsilon}n$, and average polynomial-time canonical labelling; the abstract says this applies to objects encoded by Latin squares including STS. *The average there is over Latin squares, not over STS*, so this does not give a statement about random STS. I read only the abstract and did not extract the mechanism. Almost all STS are rigid (Babai) and a.a.s. contain many Pasch configurations (Kwan). No a.a.s. statement on generation by few points was found.
* **Structure.** Doyen–Hubaut–Vandensavel 1978: $p$-rank of $\mathrm{STS}(v)$ is below $v$ only for $p=2,3$; 2-rank equals $v-\log_2(\#\text{maximal subsystems}+1)$ [via secondary sources]; equality with $2^m-m-1$ iff $\mathrm{PG}$. Tonchev, Jungnickel, Zinoviev, Shi–Xu–Krotov: counts by 2-rank and 3-rank. Grishkov–Rasskazova–Rasskazova–Stuhl, arXiv:1508.03399: central extensions of $\mathbb F_2$-spaces by Steiner loop cocycles $f(v_1+v_2,v_2)=f(v_1,v_2)$, the cocycle description used in §6. So **the cocycle description is not new**. Colbourn–Dinitz 2000: bounded-depth "$k$-generating sets", not rank-versus-structure.
* **WL.** No statement of the WL dimension of STS was found; only group/quasigroup analogues (Brachter–Schweitzer; Grochow–Levet; Johnson–Levet–Vojtěchovský–Widholm arXiv:2508.06478). Observed here (§8): pair-refinement sees no difference between STS at individualization depth $\le 1$.

**Novelty hedge.** Searches on (rank, generators, closure growth, doubling, Fano/Veblen–Young, subsystem generation) found nothing stating T1, T3 or T2. The ingredients are classical: Veblen–Young, doubling, the 2-rank/character connection. T1's proof is short and could exist in an old paper I did not reach. The reduction T2 was not found under any phrasing I tried. Treat T1, T2, T3 as "not found", not as new.

## 2. Setting and closure–rank duality

An STS$(n)$ is $(X,\mathcal B)$; $x\cdot y$ is the third point on the block through $x\neq y$, $x\cdot x=x$. A *subsystem* is a subset closed under $\cdot$. $\rho(T)$ is the minimum size of a generating set of the subsystem $T$ (so $\rho(\emptyset)=0$, $\rho(\{p\})=1$); $\mathrm{rk}(X)=\rho(X)$.

**Doubling.** If $S\subsetneq X$ is a subsystem and $x\notin S$ then $x\notin xS$ and $xS\cap S=\emptyset$, so $|\langle S,x\rangle|\ge 2|S|+1$, i.e. $|\langle S,x\rangle|+1\ge 2(|S|+1)$. Hence a proper subsystem has $|S|+1\le (n+1)/2$.

**Lemma 1 (duality) [PROVEN].** For every subsystem $T$: $\mathrm{rk}(X)\le\rho(T)+\lfloor\log_2\frac{n+1}{|T|+1}\rfloor$. Hence $\mathrm{rk}(X)=\min_T\big(\rho(T)+\lfloor\log_2\frac{n+1}{|T|+1}\rfloor\big)$, the minimum attained at $T=X$.

*Proof.* Extend $T$ by adding points outside the current subsystem. After $t$ additions $|T_t|+1\ge 2^t(|T|+1)$. If $T_t\neq X$ then $2^t(|T|+1)\le(n+1)/2$. So with $t=\lfloor\log_2\frac{n+1}{|T|+1}\rfloor$ we have $2^t(|T|+1)>(n+1)/2$, hence $T_t=X$; thus rank $\le\rho(T)+t$. Equality at $T=X$ is trivial. ∎

Write $\phi(T)=\log_2(|T|+1)-\rho(T)$, $\ell=\log_2(n+1)$, $r=\mathrm{rk}(X)$, $c=\ell-r=\phi(X)$. Lemma 1 gives $r-\rho(T)\le\log_2\frac{n+1}{|T|+1}$, i.e.

$$\phi(T)\le\phi(X)=c\quad\text{for every subsystem }T.\tag{1}$$

Equivalently: **every $\rho$-generated subsystem has size $\le 2^{\rho+c}-1$.** So "rank $\ge\ell-c$" and "closures grow like $2^{\rho+c}$ at most" are one statement. In particular the small-generators-generate-little condition of the brief is exactly the rank condition. (Lemma 1 agreed with exact rank on the systems of order $\le 31$ in `check_theorem1.py` whose rank was within the search bound $4$; the $T$ range there is subsystems generated by at most 4 points.)

**Corollary (classical).** $\mathrm{rk}(X)\le\log_2(n+1)$, with equality iff $X\cong\mathrm{PG}(m-1,2)$. Equality means $c=0$; then (1) with $\rho=3$ gives $|T|\le7$ for every triangle closure, so every triangle closes to a Fano plane, and Veblen–Young gives $\mathrm{PG}$ (the Steiner loop is then associative: any three elements lie in a Fano subsystem, whose loop is $\mathbb F_2^3$; an associative exponent-2 loop is elementary abelian). This is the "rigidity" the campaign wanted checked: it is correct, and the Veblen–Young step is elementary.

## 3. Theorem 1: projective quotient above a potential maximizer

Set $\lambda_0=\tfrac13\log_29\approx1.05664$. For $\lambda\in(1,\lambda_0)$ let $\Psi_\lambda(T)=\log_2(|T|+1)-\lambda\rho(T)$ on subsystems $T$ (including $\emptyset$, $\Psi_\lambda(\emptyset)=0$). Fix a maximizer $S$, $s=|S|$.

**Theorem 1 [PROVEN].** If $S\ne X$ there are $a\ge s+1$ and a partition $X\setminus S=\bigsqcup_{i}C_i$ into sets of size $a$ ("cosets") such that $S\cup C_i$ is a subsystem for every $i$, and the cosets form the points of a $\mathrm{PG}(d-1,2)$ with: for a line $\{i,j,l\}$, $x\in C_i$, $y\in C_j$, we have $x\cdot y\in C_l$. So $n=s+a(2^d-1)$. Moreover:
1. $\rho(S)\le c/(\lambda-1)$ and $\log_2(s+1)\le\rho(S)+c$.
2. $\mathrm{rk}(X)\le\rho(S)+d$, so $d\ge r-\rho(S)\ge r-c/(\lambda-1)$; and $2^d(s+1)\le n+1$.
3. $S\ne X$ whenever $\lambda r>\ell$; i.e. whenever $r>\ell/\lambda$. Taking $\lambda\to\lambda_0$: a quotient of dimension $d\ge r-17.7\,c$ exists as soon as $r>0.9464\,\ell$.

So if $r\ge(1-\varepsilon)\ell$ with $\varepsilon<0.0536$, then $X$ is a $\mathrm{PG}(d-1,2)$-fibration with $d\ge(1-18.7\varepsilon)\ell$ and $|S|\le n^{18.7\varepsilon}$.

*Proof.* Let $x\notin S$, $T_x=\langle S,x\rangle$. Since $\Psi_\lambda(T)\le\Psi_\lambda(S)$ and $\rho(T)\le\rho(S)+t$ when $T=\langle S,x_1,\dots,x_t\rangle$:
$$|T|+1\le 2^{\lambda t}(s+1).\tag{2}$$
Let $\beta_t=2^{\lambda t}$; then $\beta_1<2.08$, $\beta_2<4.33$, $\beta_3<9$.

*Minimality.* If $S\subsetneq R\subsetneq T_x$, doubling gives $|T_x|+1\ge4(s+1)$, contradicting (2). So $T_x$ is a minimal extension of $S$. Thus $x\sim y\iff T_x=T_y$ partitions $X\setminus S$ into classes $C_x=T_x\setminus S$, $|C_x|\ge s+1$, and two distinct $T_x,T_y$ meet exactly in $S$.

*Lines.* Let $x\in C_1$, $y\in C_2$, $C_1\ne C_2$, $z=x\cdot y$. If $z\in S\cup C_1$ then $y=x\cdot z\in T_x$, contradiction; similarly $z\notin C_2$. So $z$ is in a third coset. Let $U=\langle S,x,y\rangle$; it is a union of $S$ and $m_U$ cosets, each of size $\ge s+1$. By (2), $m_U(s+1)\le|U|-s<(\beta_2-1)(s+1)<4(s+1)$, so $m_U=3$. Hence $U$ determines a unique third coset $C_3$, and $x\cdot y\in C_3$ for all $x\in C_1,y\in C_2$ ($\langle S,x',y'\rangle=U$ for $x'\in C_1,y'\in C_2$). Cosets with these lines form an STS $P$ on $p$ points. Since $y\mapsto x\cdot y$ is injective from $C_2$ to $C_3$ and the roles are symmetric, $|C_1|=|C_2|=|C_3|$, so all cosets have one size $a$.

*Planes.* For a triangle of $P$ with representatives $x,y,z$, $W=\langle S,x,y,z\rangle$ has $m_W(s+1)\le|W|-s<(\beta_3-1)(s+1)<8(s+1)$, so $m_W\le7$. The cosets of $W$ form a subsystem of $P$ containing a triangle, so it is Fano. Thus every triangle of $P$ generates a Fano plane, so $P\cong\mathrm{PG}(d-1,2)$ by Veblen–Young, $p=2^d-1$.

*The numerics.* $\Psi_\lambda(S)\ge\Psi_\lambda(\emptyset)=0$ gives $\lambda\rho(S)\le\log_2(s+1)$; with (1), $\log_2(s+1)\le\rho(S)+c$, so $(\lambda-1)\rho(S)\le c$. Generators of $S$ plus lifts of a basis of $P$ generate $X$ (each coset meeting the generated subsystem $R\supseteq S$ lies in $R$, since $T_w\subseteq R$), so $r\le\rho(S)+d$. Summing sizes, $n+1=s+1+a(2^d-1)\ge2^d(s+1)$. Finally $\Psi_\lambda(\emptyset)=0>\ell-\lambda r=\Psi_\lambda(X)$ when $\lambda r>\ell$, so then $S\ne X$. ∎

**Remarks.**
* The quotient need not be a Steiner-loop quotient: if $a>s+1$ the cosets contain internal blocks. This requires $s\ge24$, since $a-(s+1)$ is even and $a\le(\beta_1-1)(s+1)<1.081(s+1)$. If $a=s+1$, then $S\cup\{e\}$ is a normal subloop of the Steiner loop with quotient $\mathbb F_2^d$, so $d$ is at most the 2-rank deficiency (DHV), and the base is a quotient of the $\mathbb F_2$-character quotient, computable by linear algebra.
* For $c=0$ the theorem recovers PG with $S=\emptyset$.

**Converse (Proposition 1) [PROVEN].** Suppose $X\setminus S$ is partitioned into cosets with $S\cup C_i$ subsystems, and cosets carry a $\mathrm{PG}(d-1,2)$ with $C_iC_j\subseteq C_l$ on lines. Then $\mathrm{rk}(X)\ge d$.
*Proof.* Let $G$ generate $X$; let $B$ be the subsystem of $P$ generated by the images of $G\setminus S$. Then $S\cup\bigcup_{i\in B}C_i$ is closed under $\cdot$ and contains $G$, so it equals $X$; so the images generate $P$, which needs $d$ points. ∎

So for $r\ge(1-\varepsilon)\ell$, $\varepsilon<0.0536$, "rank is near $\ell$" and "$X$ fibres over a large $\mathrm{PG}$" are equivalent up to the constant $18.7$ in $\varepsilon$.

Checks of the conclusion, with $S$ chosen by hand (exhaustive for that $S$, in `check_fibration.py`; these $S$ are not claimed to be $\Psi$-maximizers): central extensions $X_g$ of $\mathrm{PG}(d-1,2)$ by $\mathbb F_2$ with random cochain, $d=5,6,7$: the closure $S$ of a non-associative triangle has order 15, and $X\setminus S$ is 3, 7, 15 cosets of size 16, quotient $\mathrm{PG}(d-4,2)$; $X_\chi$ of §6 for $d=4,5$: $S=\mathbb F_2^3\setminus0$, quotient $\mathrm{PG}(d-1,2)$. Theorem check at $\lambda=1.05$, maximizing over subsystems generated by at most 4 points, on the systems of order $\le31$ with rank at most 4: every conclusion held, with $S=X$ for the random and $\mathrm{AG}$ systems, as the theorem allows. (PG(4,2), rank 5, is outside the search bound.) These checks are consistent with the proof and are not evidence for the asymptotic statement.

## 4. Theorem 3: other fields, under an index gap

For $q\ge2$ an integer, consider $\Psi^q_\lambda(T)=\log_q|T|-\lambda\rho(T)$ on *nonempty* subsystems. Put $\lambda_q=\min\{\tfrac12\log_q(q^2+q-1),\ \tfrac13\log_q(q^3+q-1),\ \log_q(q+1-1/q)\}$.

**Theorem 3 [PROVEN].** Let $S$ maximize $\Psi^q_\lambda$, $1<\lambda<\lambda_q$, $S\ne X$, and suppose **every chain $S\subseteq R\subsetneq R'$ of subsystems has $|R'|\ge q|R|$** (index gap above $S$). Then the classes $T_x\setminus S$ partition $X\setminus S$, and with the lines $\langle S,x,y\rangle$ they form a linear space in which every line has $q+1$ points and every plane is a projective plane of order $q$; hence a projective space $\mathrm{PG}(d-1,q)$ (Veblen–Young), with $q$ a prime power when $d\ge4$. $\mathrm{rk}(X)\le\rho(S)+d$.

*Proof.* As Theorem 1, with (2) replaced by $|T|\le q^{\lambda t}|S|$. Minimality: $\lambda<2$. Lines: $m_U\le(q^{2\lambda}-1)/(q-1)<q+2$, and $|U|\ge q^2s$ with $|C|\le(q^\lambda-1)s$ gives $m_U>q$, so $m_U=q+1$. Two cosets determine $U$ (if $\langle S,C,C'\rangle\subsetneq U$ then $|U|\ge q^3s>q^{2\lambda}s$). Planes: $m_W<q^2+q+2$, and a line plus a point off it force $\ge q^2+q+1$ points, so $m_W=q^2+q+1$ and $W$ is a projective plane. ∎

Examples: $\mathrm{AG}(m,3)$, $q=3$, $S$ a point, gives $\mathrm{PG}(m-1,3)$ as the coset geometry. Bose over $\mathbb Z_p^d$, $q=p$, $S=$ (affine line)$\times\mathbb Z_3$: the Bose subsystems of the form (flat)$\times\mathbb Z_3$ give $\mathrm{PG}(d-2,p)$ if $S$ is a maximizer and the index gap holds above it. I did not prove either for the Bose system, and the code does not check this example.

**Status of the dichotomy.** Unconditionally only $q=2$. The index gap is what is missing for general $q$: an STS may mix indices 2, 3, $\dots$ in different directions. For the slope range $(\lambda_0,\log_23)$ I have no structure theorem. This is the open core (§9).

## 5. Correcting the w18 lead

w18 asked whether every rank-$\Omega(\log n)$ quasigroup is locally algebraic (every small subset generates a section isotopic to a group or Moufang loop).

**Proposition 2 [PROVEN].** No. For every $d\ge3$ the STS $X_g$ (central extension of $\mathrm{PG}(d-1,2)$ by $\mathbb F_2$, §6) with a cochain $g$ not coboundary on some plane has rank $\ge d=\log_2(n+1)-1$, and contains a 3-generated subsystem whose Steiner loop is non-associative of order 16. A Steiner loop that is Moufang is an elementary abelian 2-group, so this section is not isotopic to a group or a Moufang loop.

*Proof.* Rank: Prop. 1. Associator: the Steiner loop $L_g$ has $a(x,y,z)=g(x,y)+g(x+y,z)+g(y,z)+g(x,y+z)$, the sum of $g$ over the four lines of the Pasch configuration in the plane $E=\langle x,y,z\rangle$ missing $x+z$. If $g|_E$ is not a coboundary, some Pasch sum is nonzero, so $L_g$ restricted to $E$ is non-associative. (Commutative Moufang loops satisfy $(xx)(yz)=(xy)(xz)$; with $x^2=e$ and $x(xy)=y$ this gives $(xy)z=y(xz)$, and exchanging $x,y$ gives associativity. A loop isotopic to a group is a group (Albert) and a loop isotopic to a Moufang loop is Moufang (Bruck), both from memory, so isotopy to a group or Moufang loop is excluded.) ∎

The correct form is that high rank comes with a projective *quotient geometry* (Theorem 1), not with local algebra. Note the doubling towers: a random tower has a chain of length $\log_2 n$ with every step of index 2 and rank $3$ (observed, §8). So the chain length in A1 and the rank are different parameters.

## 6. Theorem 2: the barrier lives on the algebraic side

Let $V=\mathbb F_2^d$, $d\ge2$, $Z=\mathbb F_2^3$. Fix a 1-factorization $F^1=(F^1_z)_{z\in Z\setminus0}$ of $K_Z$ such that (a) the STS $T^1$ on $(Z\setminus0)\sqcup Z$ with Fano on $Z\setminus 0$ and factors $F^1_z$ is not $\mathrm{PG}(3,2)$, and (b) $\{a+b+z:\{a,b\}\in F^1_z\}$ spans $Z$. An explicit one (seeded output of the script; both properties verified by machine):

```
F1_1 = 05 12 34 67    F1_2 = 02 16 37 45    F1_3 = 07 15 24 36    F1_4 = 04 17 23 56
F1_5 = 01 27 35 46    F1_6 = 06 13 25 47    F1_7 = 03 14 26 57
```

For $\chi:V\setminus0\to\{0,1\}$ define $X_\chi$ on points $Z\setminus 0\ \sqcup\ (V\setminus0)\times Z$ with blocks: (i) the lines of $Z\setminus0$; (ii) $\{z,(c,a),(c,b)\}$ for $\{a,b\}\in F^{\chi(c)}_z$, where $F^0_z=\{\{a,a+z\}\}$; (iii) $\{(c_1,a),(c_2,b),(c_3,a+b)\}$ for lines $\{c_1,c_2,c_3\}$ of $\mathrm{PG}(V)$. Pair-coverage is immediate: this is an STS of order $n=8\cdot2^d-1$. (General form, with one-factorizations $F_c$ and arbitrary Latin squares on lines, gives all PG-fibrations with $a=s+1$; these data are independent, which is why fibre data is unconstrained.)

**Theorem 2 [PROVEN].** For non-constant $\chi,\chi'$: $X_\chi\cong X_{\chi'}$ iff there is $A\in\mathrm{GL}(V)$ with $\chi'\circ A=\chi$. Consequently linear equivalence of Boolean functions on $\mathbb F_2^d$ (constant colourings and the value at $0$ handled directly) reduces in $\mathrm{poly}(2^d)$ time to STS isomorphism on $n=2^{d+3}-1$ points, on instances with $\mathrm{rk}\ge\log_2(n+1)-3$.

*Proof.* ($\Leftarrow$) $z\mapsto z$, $(c,a)\mapsto(Ac,a)$ is an isomorphism (check blocks). ($\Rightarrow$) Characters: a function $f:X_\chi\to\mathbb F_2$ with sum $0$ on every block has $f|_{Z\setminus0}=\lambda$ linear, and (iii) forces $f(c,a)=v(c)+\mu(a)$ with $\mu,v$ linear and $\mu$ independent of $c$ (set $b=0$ and $a=0$ on a line, using that every two points of $\mathrm{PG}(V)$ are collinear). Type (ii) on a fibre with $\chi(c)=0$ gives $\lambda=\mu$; on a fibre with $\chi(c)=1$, $\mu(a+b+z)=0$ for all pairs, so $\mu=0$ by (b). Since $\chi$ is non-constant both fibres occur, so the character space is exactly $V^*$, independent of $\chi$. Its common kernel in the Steiner loop is the canonical normal subloop with non-identity elements $S=Z\setminus0$, and the quotient is $V$. So an isomorphism $\varphi$ preserves $S$, induces $A\in\mathrm{GL}(V)$ on quotients, and sends $S\cup C_c$ to $S\cup C'_{Ac}$. These are $\mathrm{PG}(3,2)$ iff the colour is $0$, by (a), so $\chi(c)=\chi'(Ac)$. Rank: Prop. 1 gives $\ge d=\log_2(n+1)-3$. ∎

**Consequence.** An $n^{o(\log n)}$ algorithm for STS isomorphism would give $2^{o(d^2)}$ string isomorphism under $\mathrm{GL}(d,2)$ on binary strings; this is at the level of the campaign's barrier in `docs/moonshot-theory.md` §3.3 and Theorem B of w17 (best known $2^{d^2/4+O(d)}\mathrm{poly}(2^d)$). Worse for the stated plan: Theorem 1 says the hardest instances are recognisably PG-fibred, but this theorem says that recognising the structure does not simplify them, since fibres can encode an arbitrary string on the points of the base. **Handling the "algebraic" side by algebra alone is exactly the barrier.**

Machine check (`check_reduction2.py`): for $d=3$ all 9 $\mathrm{GL}(3,2)$-orbits on nonzero colourings; the explicit map verified block-by-block on 6 samples; a two-point-individualization 2-WL invariant distinguishes all 9 orbits pairwise (certifying non-isomorphism, up to 64-bit hash collisions) and agrees on equivalent colourings in 2 further random pairs. (`nauty` stalls on these graphs at $n=63$; the invariant takes its place.) Non-isomorphism across orbits is exhaustive at $d=3$ (including the orbit of the all-ones colouring). The forward direction was sampled (6 random pairs), and it is a two-line proof. Nothing is checked at $d\ge4$.

**Why bilinear cocycles do not help: [PROVEN].** For the central extension by $\mathbb F_2^k$ with cochain $g$ on the lines (this is the description of Grishkov et al.), alternating bilinear $g$ is always a coboundary ($g=\delta Q$ for a quadratic form $Q$ polarizing to $g$), so the group-like residue on $\mathbb F_2$ is empty. And no nonzero alternating *trilinear* associator exists: the associator on a plane $E$ is $a(x,y,z)=\lambda_E(x)+\lambda_E(z)$, where $\lambda_E:E\to\mathbb F_2^k$ is the linear map sending $w$ to the Pasch sum missing $w$ (linear because $1_{P_w}+1_{P_{w'}}=1_{P_{w+w'}}$ as sets of lines in a Fano plane). If $a(x,y,z)$ were alternating trilinear and nonzero, $\lambda_E(w)=t$ would be a fixed nonzero value on every nonzero $w\in E$, contradicting linearity. So at $p=2$ there is no tensor-like core to feed to Sun-type methods. (At $p=3$ there is: Hall triple systems have a trilinear associator by Bruck.)

**The near-top upper bound [SKETCH].** For $c=O(1)$: $|S|$ and $a$ are $O(1)$, enumerate $S$ in $n^{O(c)}$, then $X$ is a string under $\mathrm{GL}(d,2)\ltimes\mathrm{Sym}(a)^{2^d-1}$. Flags and bidirectional collision from w17 Theorem B, with $\mathrm{Sym}(a)^{\cdots}$ absorbed in the Babai–Luks canonical form for $\Gamma_a$, should give $2^{d^2/4+O(d)}n^{O_a(1)}$, i.e. $n^{(1/4+o(1))\log_2 n}$ on this class. *Gap:* I did not write out the canonical-form argument with the gauge action. Note the phrase "reduces to string isomorphism" is only for this GL-with-gauge group, not plain GL, for $a>2$.

## 7. A natural subclass with $n^{o(\log n)}$

**Corollary (trivial).** If every proper subsystem has order $\le s$ then $\mathrm{rk}\le\lfloor\log_2(s+1)\rfloor+1$, so Miller runs in $n^{\log_2 s+O(1)}$; $n^{o(\log n)}$ when $s=n^{o(1)}$. [PROVEN]

**Theorem 5 (near-PG) [PROVEN].** Let $n=2^m-1$. Suppose an STS $X$ has the same point set as some $\mathrm{PG}(m-1,2)$ structure $\pi$ and $|X\setminus\pi|=|\pi\setminus X|=D<(n-2)/24$. Then $\pi$ is unique and computable in polynomial time, and $X\cong X'$ can be decided in time $(6D)^{\min(m,6D)}\mathrm{poly}(n)$. So for $D=n^{o(1)}$ the running time is $n^{o(\log n)}$.

*Proof.* Let $M(x,y)$ be the plurality over $z\ne x,y$ of $Q(Q(x,z),Q(y,z))$. If $z$ and $x+z$ avoid the $\le6D$ points on differing blocks then $Q(x,z)=x+z$, $Q(y,z)=y+z$ and $Q(x+z,y+z)=x+y$, using cleanliness of $z$ and of $x+z$. So at least $n-2-12D>(n-2)/2$ values of $z$ give $x+y$, and $M(x,y)=x+y$ exactly. This recovers the $\mathbb F_2$-structure from $X$ alone; uniqueness follows. An isomorphism preserves $M$, so is $A\in\mathrm{GL}(m,2)$, and carries $X\setminus\pi$ to $X'\setminus\pi'$ and $\pi\setminus X$ to $\pi'\setminus X'$; the converse is immediate. A basis of the span of the defect points (at most $\min(m,6D)$ of them, all defect points) must map into defect points of $X'$, so enumerate $\le(6D)^{\min(m,6D)}$ images, check the defect sets, extend $A$ arbitrarily outside the span. ∎

This is easy (the group $\mathrm{GL}$ is enumerated only on a small span) but it is unconditional. The bound is $n^{\Omega(\log n)}$ once $D=n^{\Omega(1)}$, and at $D=\Theta(n)$ arbitrary point-colourings of the base appear: $X_\chi$ differs from $\mathrm{PG}(d+2,2)$ in $\Theta(|\chi^{-1}(1)|)$ blocks. Random defects destroy the projective structure quickly: 40 Pasch switches on $\mathrm{PG}(6,2)$ gave rank upper bound 3 and $d_2=0$ (§8).

## 8. Experiments

`experiments.py`, one process under `nice`, whole run $<$ 1 minute: PG, AG, a Hall triple system of order 81 (from a loop of Bruck recalled from memory; every one of its 84240 triangles closes to order 9, checked exhaustively, and rank at most 4 $<5=\mathrm{rk}\,\mathrm{AG}(4,3)$ shows it is non-affine), Bose over $\mathbb Z_p^d$, Skolem, product, doubling towers, $X_g$ (random cochain), $X_\chi$ (random colouring), Pasch-switched PG, Stinson hill-climbing. Measured: $d_2$ = dimension of $\mathbb F_2$-characters, $d_3$ = dimension of $\mathbb F_3$-characters minus 1, an upper bound on rank by greedy max-growth chains (30 candidates per step, 3 restarts), closure sizes from 40/30/15 random 3/5/8-seeds, greedy individualization depth under 1-WL (point/block incidence) and 2-WL on the Steiner quasigroup. Selected rows:

| family ($n$) | $d_2$ | $d_3$ | rank UB | closure med. $t=3,5,8$ | 1-WL depth | 2-WL depth, trace of point classes |
|---|---|---|---|---|---|---|
| PG(6,2) (127) | 7 | 0 | 7 | 7, 31, 127 | 7 | 7: $1,2,4,8,16,32,64,127$ |
| PG(7,2) (255) | 8 | 0 | 8 | 7, 31, 255 | 8 | 8 |
| AG(5,3) (243) | 0 | 5 | 6 | 9, 81, 243 | 6 | 6 |
| HTS(81) non-affine | 0 | 3 | 4 | 9, 81, 81 | 4 | 5: $1,2,4,19,29,81$ |
| Bose $\mathbb Z_3^3$ (81) | 0 | 3 | 4 | 27, 81, 81 | 5 | 5 |
| Bose $\mathbb Z_5^3$ (375) | 0 | n/a | 4 | 75, 375, 375 | 5 | not run |
| Bose $\mathbb Z_7^2$ (147) | 0 | 0 | 3 | 147, 147, 147 | 4 | 4 |
| Skolem (61) | 0 | 0 | 3 | 61, 61, 61 | 3 | 2 |
| $X_g$, $d=5$ (63) random cochain | 5 | 0 | 5 | 15, 31, 63 | 6 | 6: $1,2,4,27,39,47,63$ |
| $X_g$, $d=7$ (255) | 7 | 0 | 7 | 15, 63, 255 | 8 | 8: $1,2,4,131,135,143,159,191,255$ |
| $X_\chi$, $d=5$ (255) random colouring | 5 | 0 | 6 | 7, 127, 255 | 8 | 3: $1,2,191,255$ |
| PG(6,2)+3 Pasch switches (127) | 4 | 0 | 5 | 7, 31, 127 | 5 | 3 |
| PG(6,2)+40 switches (127) | 0 | 0 | 3 | 7, 127, 127 | 4 | 2 |
| doubling tower, height 4 (127) | 1 | 0 | 3 | 127, 127, 127 | 7 | 2 |
| random STS hill-climbing (63, 127, 255, 301) | 0 | 0 (n/a at 301) | 3 | $n,n,n$ | 3 | 2 (not run at 301) |

Observations, labelled as such:

* Hill-climbing STS: the closure of a random triple is everything, except when the triple happens to be a block (minimum 3 at $n=63,127$), rank upper bound 3, 2-WL depth 2. Consistent with "random STS have rank $3$", which I cannot prove.
* Depth differs from hardness. $X_g$'s 2-WL depth is $d+1$: the point classes jump to about $n/2$ after 3 individualizations and the remaining depth just breaks the gauge automorphisms ($\mathrm{Hom}(V,\mathbb F_2)$, order $2^d$). So individualization depth overstates search difficulty on this family. The tree size with automorphism pruning was not measured.
* $X_\chi$ with a random colouring is broken by 2-WL at shallow depth, consistent with w17 Theorem D's $2^{k\log k}$ for random strings. T2's hardness is about adversarial colourings; a random reduction instance is easy. The hard instances from T2 are structured colourings (this is the barrier).
* Pair-refinement sees nothing at individualization depth $\le 1$ on the $X_\chi$ tested (all $H_0$ and $H_1$ hashes agreed). With one individualized point the visible structure is a perfect matching, the same for every system of a given order (observed; I did not prove stability). Depth-2 invariants (cycle structure of $M_v\cup M_w$) were the first to distinguish them.

**What the experiments cannot show.** Sizes are at most a few hundred, far below any asymptotic regime. Rank figures are upper bounds; only systems of order $\le31$ were exhaustively enumerated, and those are verified exactly. The "non-iso" certification of T2 is for $d=3$ only. No statement about scaling of WL dimension follows; no lower bound on WL dimension was obtained. None of the theorems above was machine-checked. The 64-bit hashing can only under-report refinement.

## 9. Attempts and the open core

| Idea | Exact lemma needed | Where it broke |
|---|---|---|
| Closure-size expansion: $o(\log n)$ points generate everything unless structure | Dichotomy: $\mathrm{rk}\ge\varepsilon\log n\Rightarrow$ PG-type quotient of dimension $\Omega_\varepsilon(\log n)$ | Proved only for slope $<\lambda_0$, i.e. rank above $0.947\log_2 n$ (T1). Below that, mixing of extension indices 2 and $>2$ is not controlled; T3 needs an index gap |
| Low-depth generation: words of depth $o(\log n)$ | Generators of bounded depth (Colbourn–Dinitz) | Depth does not bound Miller's branching; the "$n^r$" is about the count of generators. Nothing to gain |
| WL dimension of STS | Find $k$ with $k$-WL + $o(\log n)$ individualizations identifying all STS | Trivial upper bound $O(\log n)$ by generators. All STS look alike to pair refinement at depth $\le1$; no lower bound beyond small examples was found. $X_g$ is CFI-like over the PG base but its nonisomorphism witnesses sit behind the GL action |
| HJ-style constant-size local certificates on points | Local certificate with $n^{O(1)}$ branching per factor-2 shrink | Refuted for HJ's algorithm by B1 (`w18-latin.md`); and any such certificate would, via T2, produce $2^{o(d^2)}$ linear equivalence |
| Group techniques on residue | Trilinear or bilinear core at $p=2$ | No bilinear or trilinear core exists at $p=2$ (§6). Sun/IMQSZ need bilinear maps; the line cocycle is not one |
| Treat the base GL by Luks-type splitting | Flags with Borel $2$-group, then bidirectional | Works but gives only the constant in the exponent (1/4 versus 1/2): same as w17 Theorem B |
| Counting random STS for rank 3 | A.a.s. bound on the number of subsystems | I did not find or prove the count needed |

**Barriers check.** T2's reduction: the same gadget gives quasigroup isomorphism $\ge$ linear equivalence (Steiner quasigroups are quasigroups) immediately. Latin-square *isotopy* [SKETCH]: replace blocks by the Cayley table of $\mathbb F_2^{d+3}$ with subsquares changed according to $\chi$ and use the three-sorted character space to recover the base; not written out. **Conference graphs:** nothing here applies; no $\mathbb F_2$-quotient structure is available.

**Conjecture (dichotomy, [SPECULATION]).** There is a function $q(\varepsilon)$ so that $\mathrm{rk}(X)\ge\varepsilon\log_2n$ implies a subsystem $S$ with $\rho(S)=o(\log n)$ whose coset interval is a direct sum of projective geometries $\mathrm{PG}(d_i-1,q_i)$ with $q_i\le q(\varepsilon)$ and $\sum d_i=\Omega_\varepsilon(\log n)$. This is the Zil'ber-type structure (Cherlin–Mills–Zil'ber, from memory) one would expect for a locally finite modular-like pregeometry. Evidence is limited to T1, T3 and the extremal examples. Note that even if true, T2 means this would not yield an algorithm without further progress on the GL string problem.

**Leads.**
1. Extend T1's slope past $\lambda_0$: analyse cosets when lines have 4 to 7 cosets. Even a clean statement for $\lambda<\log_23$ would be new.
2. Determine whether $\Psi_\lambda$ has a well-defined filtration (a Harder–Narasimhan polygon) with uniqueness of maximizers; log-size is subadditive for subsystems in the modular case, but this needs real proof.
3. For $k=1$ central extensions: the invariant data is the function $\lambda_E$ on planes. A radical reduction ($u$ with vanishing Pasch sums through all planes containing $u$ yields a factor $L_{g_0}\times\mathbb F_2$; [SKETCH]) reduces to radical-free cocycles. The radical-free, structured case is the pure core of T2.
4. Mixed triangles: can an STS have every triangle generating order 7 or 9 with both occurring? (Unknown to me; relevant to the band $1.0566<\lambda<1.153$ where the planes argument gives order at most 9.)

## 10. Reproduction

```sh
cd docs/w30-sts-code
gcc -O2 -march=native -o /tmp/wl wl.c   # or set WLBIN to the compiled path
WLBIN=/tmp/wl nice -n 19 python3 experiments.py        # section 8 table
WLBIN=/tmp/wl nice -n 19 python3 check_theorem1.py     # Lemma 1, Theorem 1 small cases
WLBIN=/tmp/wl nice -n 19 python3 check_fibration.py    # Theorem 1 conclusions with nontrivial quotients
WLBIN=/tmp/wl nice -n 19 python3 check_reduction2.py   # Theorem 2, d=3, invariants (several minutes)
```

`runwl.py` has a default binary path pointing at this campaign's scratch location; set `WLBIN` elsewhere. `check_reduction.py` (nauty certificates) stalls at the fourth $\mathrm{GL}(3,2)$ orbit on $n=63$ and is kept only to record that fact; run it with a `pynauty` interpreter and a time limit if at all.

Sources: [Miller 1978 generator bound, as cited in arXiv:1006.5892](https://arxiv.org/pdf/1006.5892) · [Babai–Wilmes 2013](https://people.cs.uchicago.edu/~laci/papers/13stoc-steiner-iso.pdf) · [Collins–Grochow–Levet–Weiß](https://arxiv.org/abs/2402.00133) · [Gill–Mammoliti–Wanless](https://arxiv.org/abs/2402.06205) · [Kwan, Pasch in random STS](https://math.mit.edu/~msimkin/files/papers/pasch_in_sts.pdf) · [Grishkov et al., Steiner loops class 2](https://arxiv.org/pdf/1508.03399) · [Doyen–Hubaut–Vandensavel 1978](https://geodesic.mathdoc.fr/item/MZ_1978__163_172756) · [Jungnickel–Tonchev](https://arxiv.org/pdf/1709.06044) · [Shi–Xu–Krotov](https://www.arxiv.org/pdf/1806.00009) · [Colbourn–Dinitz 2000](https://site.uvm.edu/jdinitz/files/2021/04/generating.sets_.pdf) · [Johnson–Levet–Vojtěchovský–Widholm](https://arxiv.org/abs/2508.06478)
