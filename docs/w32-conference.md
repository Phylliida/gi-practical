# w32-conference: isomorphism of conference graphs below n^(log n)

Worktree `w32-conference`. Moonshot record: target not reached. Labels: **[PROVEN]**, **[SKETCH]**, **[CONDITIONAL]**, **[SPECULATION]**, **[DATA]**. Code and data: `docs/w32-code/`.

## 0. Summary

| # | Claim | Status |
|---|---|---|
| S1 | No $n^{o(\log n)}$ bound for the class of all conference graphs is known. Best: $n^{2\log_2 n+O(1)}$ (Babai 1980, distinguishing sets, Levet 2023 quotes it as still the best). Levet asks explicitly whether an individualization set of size $O(1)$, or even $o(\log n)$, exists (Question 6.5). | Literature, checked (§1) |
| S2 | Exact identities for the triple correlation $T(a,b,v)=\sum_x C(a,x)C(b,x)C(v,x)$: $\sum_v T(a,b,v)^2=n^2-2n-1$; $T\equiv 2\pmod 4$; $T\bmod 8$ determined by the triangle on $\{a,b,v\}$. | **[PROVEN]** (§2) |
| S3 | The 2-rank of $A$ is $(n-1)/2$ ($n\equiv1\bmod 8$) or $n-1$ ($n\equiv 5\bmod 8$); the first case is Brouwer–van Eijl. | **[PROVEN]** (§2.4) |
| S4 | **Bad-pair reduction.** A set of $2\lceil 3/c\rceil$ vertices leaves, after two 1-WL rounds, only cells that are cliques of the "bad pair" graph $B_c=\{(v,w): p(v,w)\ge n^{-c}\}$. | **[PROVEN]** (Thm 3.2) |
| S5 | **Uniform anti-concentration (the most natural lemma) is false.** Iterated Turyn products of $P(9)$ give pairs $x\neq y$ with collision probability $\ge 0.049$ for all $n$ (at $n=6561$, $p$ reaches $0.28$ vs. $1/\sqrt n=0.012$). | **[PROVEN]** (Thm 4.2) |
| S6 | Paley $P(q)$: individualizing $O(1)$ vertices makes 1-WL discrete in two rounds, via Deligne–Katz Sato–Tate equidistribution. | **[SKETCH]** (Thm 5.1) |
| S7 | Over all available conference graphs (Spence's lists; Paley for all prime powers $q\equiv1\bmod 4$ up to 1097; Peisert; Peisert-type; uniform cyclotomic; Turyn to $n=6561$), the exact minimum 1-WL individualization depth is 2 or 3. Depth 3 occurred only where every 2-point stabilizer is nontrivial (checked for the symmetric families), and for the algebraic families the 1-WL partition after individualizing 2 vertices equals the orbit partition of the pair stabilizer on all tested pairs. | **[DATA]** (§6) |
| S8 | Dichotomy of the form "either small-depth refinement or recognizable algebraic structure": reduction proved, structure side open. | Open (§4) |

**Bottom line.** Nothing beats $n^{2\log_2 n}$ for the whole class. The statements S2–S5 are the honest yield: exact control of the first nontrivial refinement round, and a clean proof that the natural pointwise anti-concentration statement fails on a family that is itself solved in practice.

## 1. State of the art (checked)

* **Babai 1980** (SIAM J. Comput. 9): distinguishing sets. Any two vertices of a conference graph are distinguished (exactly $(n-1)/2$ outside vertices are adjacent to exactly one of them), so a random set of size $2\log_2 n+O(1)$ distinguishes all pairs; Levet quotes "almost all such subsets of this size are distinguishing" (Levet 2207.05930, §5, [Bab80, Lemma 3.2]). Two rounds of count-free refinement then finish. Time $n^{2\log_2 n+O(1)}$.
* **Levet 2023** (AJC 87): conference-graph isomorphism in $\beta_2\mathrm{AC}^0$, no further runtime improvement known ("to the best of my knowledge"); Question 6.5 asks for an $O(1)$ set, and says $o(\log n)$ "would be a major advance".
* **General SRG.** Spielman 1996: $\exp(\tilde O(n^{1/3}))$. Babai–Chen–Sun–Teng–Wilmes (FOCS 2013): $\exp(\tilde O(n^{1/5}))$. Babai 1980: $\exp(\tilde O(n/\rho))$ for degree $\rho<n/2$; for $\rho\approx n/2$ this is the quasipolynomial bound above. Conference graphs are a named Neumaier class, handled by the 1980 observation rather than by the BCSTW machinery. Babai–Wilmes and Chen–Sun–Teng (STOC 2013) treat Steiner designs. I could not open the FOCS 2013 PDF (HTTP 401) nor Babai's own server (DNS failure); the bounds above come from the search-engine extracts and from Levet and Ponomarenko.
* **WL dimension.** Paley graphs have WL dimension $\le 3$ with finitely many possible exceptions ($q\in\{3^4,3^6,3^8,3^{10},5^4,5^6\}$), Ponomarenko, arXiv 2006.13592 Theorem 1.3. Generalized Paley $GP(q,(q-1)/k)$: $\mathrm{Aut}\le A\Gamma L(1,q)$, WL dimension $\le 5$, for $q$ large relative to $k$ (Ponomarenko 2511.18304, using the Babai–Gál–Wigderson Weil bound on Paley-type systems). Cai–Guo–Gavrilyuk–Ponomarenko 2312.00460: Fon-Der-Flaass-type SRG families with WL dimension $\le 4$ — not conference parameters, relevant only as a method.
* **Paley recognition/isomorphism.** Follows from the WL bound: $X\cong P(q)$ can be tested with constant-dimensional WL (Ponomarenko 2006.13592). Circulant SRGs are characterized by Bridges–Mena and Ma (cited in the search results; not re-verified here); general circulant isomorphism is polynomial (Evdokimov–Ponomarenko, Muzychuk).
* **Constructions.** Paley; Peisert $P^*(q)$; Peisert-type unions of $(q+1)/2$ lines through the origin in $\mathbb F_q^2$; uniform cyclotomic unions; Mathon $pq^2$ (Canad. J. Math. 30, 1978); **Turyn products** (Mathon's Theorem 1.3 and eq. 1.10: $W=V\otimes V+I\otimes J-J\otimes I$ from a symmetric or skew conference-type $V$, $W$ symmetric of order $v^2$). Paley-type partial difference sets in abelian groups: orders prime power, $n^4$ or $9n^4$ (Wang 1908.07055, Polhill). Spence's lists: $n=25$ (15), $29$ (41), $37$ ($\ge6760$), two-graph classes at 42, 46, 50.
* **Subclass $n^{o(\log n)}$ results.** Paley, generalized Paley (polynomial via WL). Nothing found for general Cayley conference graphs over abelian groups, nor for the class.
* **Lower bounds on individualization.** Only base size of $\mathrm{Aut}$ (§3.3); no proven lower bound beyond the group-theoretic one found.
* Sibling w30-sts (not yet merged at time of writing): used only for code style.

Search dates: 2026-11-09. Levet's Question 6.5 remained open in everything found.

## 2. Exact identities

$X$ a conference graph, $n\equiv1\bmod 4$, $A$ adjacency, Seidel-type $C=J-I-2A$ ($-1$ for edges). Then $C=C^T$, zero diagonal, $C\mathbf 1=0$, $C^2=nI-J$. $C_a$ = row $a$. $T(a,b,v):=\sum_x C_a(x)C_b(x)C_v(x)$.

### 2.1 $L^2$ identity

**Lemma 2.1 [PROVEN].** For $a\neq b$: $\sum_v T(a,b,v)^2=n(n-2)-1$, $\sum_vT(a,b,v)=0$.

*Proof.* $g=C_a\circ C_b$ has $\|g\|^2=n-2$ and $\mathbf 1^Tg=(C^2)_{ab}=-1$. $T(a,b,\cdot)=Cg$; $\|Cg\|^2=g^T(nI-J)g=n(n-2)-1$. $\square$

So every pair $(a,b)$ produces a signal of variance $\approx n$ (typical $|T|\approx\sqrt n$). The one-step-bit view (Babai) throws this away.

### 2.2 $T$ is never zero

**Lemma 2.2 [PROVEN].** For distinct $a,b,v$, with $s=C_{ab},t=C_{av},u=C_{bv}$:
$$T(a,b,v)\equiv 6-n+2(s+t+u)+(st+su+tu)\pmod 8,$$
in particular $T(a,b,v)\equiv2\pmod4$, so $T\neq 0$.

*Proof.* On $U=V\setminus\{a,b,v\}$ we have $(1+C_a)(1+C_b)(1+C_v)\in\{0,8\}$. Summing over $U$, use $\sum_xC_a=0$ and $\sum_x C_aC_b=-1$ to reduce every term except $T$; and $T$ is unchanged by restricting to $U$. Then $8N=(n-3)-2(s+t+u)-3-(st+su+tu)+T$. For the mod-4 claim: $s+t+u$ is odd, $st+su+tu\equiv3\pmod4$, $n\equiv1\pmod 4$. $\square$

Numerically verified on 24 graphs (`check_lemmas.py`, 0 violations of the $L^2$, mod-8 and mod-4 statements). No source found for the congruence; it is short and likely folklore. Consequence: the exact "bent" extreme $T(a,b,\cdot)\in\{\pm\sqrt n\}$ is impossible (values are $\equiv 2\pmod 4$, $\sqrt n$ is odd).

### 2.3 What round 2 sees

**Lemma 2.3 [PROVEN].** Individualize $S$; let $\mathcal P$ be the round-1 partition of $V\setminus S$ by sign patterns against $S$. For $v,w$ in one cell of $\mathcal P$, round 2 does not separate them iff $\sum_{x\in Q}(C_v(x)-C_w(x))=0$ for every cell $Q$ of $\mathcal P$.

*Proof.* $c_Q(v):=|N(v)\cap Q|$ satisfies $\sum_{x\in Q}C_v(x)=|Q|-2c_Q(v)-[v\in Q]$. If $v,w$ are in the same cell $Q_0$, the $[v\in Q]$ terms agree. $\square$

So with $D_{vw}=C_v-C_w$ and $g_I=\prod_{i\in I}C_{a_i}$, non-separation is exactly $\langle D_{vw},g_I\rangle=0$ for all $I\subseteq[k]$ — this is the only structure a 2-round argument can use. For $|I|=1$ this is automatic up to bounded error (strong regularity); $|I|=2$ is the first nontrivial level: $\langle D_{vw},g_{\{i,j\}}\rangle=T(a_i,a_j,v)-T(a_i,a_j,w)$.

**Lemma 2.4 [PROVEN].** $M_v:=C\,\mathrm{diag}(C_v)\,C$ has entries $T(\cdot,\cdot,v)$ and $\langle M_v,M_w\rangle_F=(n^2-2n)\langle C_v,C_w\rangle$; hence $\|M_v-M_w\|_F^2=2n^2(n-2)$ for $v\neq w$.

*Proof.* $\mathrm{tr}(D_vC^2D_wC^2)$ with $C^2=nI-J$, $D_v=\mathrm{diag}(C_v)$, row sums of $C$ zero. $\square$

Writing $\rho(v,w)=\Pr_{(a,b)\in V^2}[T(a,b,v)\ne T(a,b,w)]$ and bounding entries by $|T|\le B$: $\rho(v,w)\ge 2n^2(n-2)/(n^2\cdot4B^2)=(n-2)/(2B^2)$. For Paley, Weil gives $B=2\sqrt q$, so $\rho\ge\frac18(1-\frac2q)$: an elementary proof of $p(v,w)\le 7/8+o(1)$ **[PROVEN, Weil]**. In general only $B=n$ is available: $\rho\ge (n-2)/(2n^2)$. A $\sqrt n\,\mathrm{polylog}$ bound on $|T|$ is false for general conference graphs: Lemma 4.1 gives $\max|T^{W(V,V)}|\ge(\max|T^V|)^2-12$, so starting from $\max|T^{P_9}|=6$ the Turyn iterates have $\max|T|\ge 564$ at $n=6561$, i.e. $n^{0.72}$ (measured $894=n^{0.77}$, sampled).

Also: $\rho$ is a pseudometric on $V$ (transitivity of equality; $\rho(u,w)\le\rho(u,v)+\rho(v,w)$); on a Cayley graph it is translation invariant, $\rho(d)=\rho(0,d)$, $\rho(d+d')\le\rho(d)+\rho(d')$ — the set of near-twin differences behaves like a norm ball. **[PROVEN, trivial.]**

### 2.4 2-rank

**Proposition 2.5 [PROVEN].** If $n\equiv1\pmod 8$: $\mathrm{rank}_2(A)=(n-1)/2$, $\mathrm{rank}_2(A+I)=(n+1)/2$. If $n\equiv 5\pmod 8$: $\mathrm{rank}_2(A)=n-1$, $\mathrm{rank}_2(A+I)=n$.

*Proof.* $n$ odd splits $\mathbb Z_2^n=\mathbb Z_2\mathbf1\oplus\mathbf1^\perp$; $A$ acts by $2t$ on $\mathbf 1$ and satisfies $A^2+A=t$ on $\mathbf 1^\perp$, with multiplicities $(n-1)/2$ for both eigenvalues. If $t$ is even, $X^2+X-t$ has 2-adic roots $r$ (unit), $s$ (non-unit), and $r-s=\sqrt n$ is a unit, so the eigenspace splitting is integral; then $A$ has $(n-1)/2$ unit eigenvalues, $A+I$ has eigenvalues $r+1=-s$ (non-unit), $s+1=-r$ (unit), $2t+1$ (unit). If $t$ is odd the polynomial is irreducible mod 2, so $A$ is a unit on $\mathbf 1^\perp$ over the unramified extension, and $k=2t$ has valuation 1. $\square$

The first case is Brouwer–van Eijl (cited via 2407.07689; the code generated is the QR code for Paley). Checked on all tested graphs. Relevance: a conference graph cannot have the "rows closed under pointwise product" structure of a character table over $\mathbb F_2$, which would be the exact group-like extreme of §3.2.

## 3. Individualization: what is really needed

Recap. **One step** (Babai): colors after individualizing $S$ are sign vectors; need $2^{|S|}\ge n$, and a random set needs $2\log_2 n$. **Iterated:** after individualizing $a_1,\dots,a_k$, the 2nd round sees $T$ for all pairs (and higher products), each of $\Theta(\sqrt n)$ size. In the Paley-like case a pair test takes $\Theta(\sqrt n)$ values, so a few tests carry enough information. All data (§6) says: 2 or 3 vertices suffice in practice.

### 3.1 Bad-pair reduction

Let $p(v,w)=\Pr_{(a,b)\in V^2}[(a,b)\text{ does not test }(v,w)]$ where $(a,b)$ *tests* $(v,w)$ iff $a\ne b$, $a,b\notin\{v,w\}$, $T(a,b,v)\ne T(a,b,w)$. By Lemma 2.3, a testing pair among individualized vertices separates $v,w$ after two rounds.

**Theorem 3.2 [PROVEN].** Let $c>0$, $m=\lceil 3/c\rceil$, $B_c=\{\{v,w\}:p(v,w)\ge n^{-c}\}$. There is $S$ with $|S|\le 2m$ such that after individualizing $S$ and two 1-WL rounds, every cell is a clique of $B_c$. Consequently, if $B_c$ has no clique larger than $L$, the isomorphism problem for $X$ is in $n^{O(1/c)}\cdot\tau(L,n)$, where $\tau(L,n)$ is bounded-colour-class isomorphism with classes of size $\le L$.

*Proof.* $m$ independent uniform pairs: a non-bad pair survives untested with probability $\le p(v,w)^m\le n^{-3}$; union over $\binom n2$ pairs. $\square$

Trivial, but it isolates the exact statement: all difficulty is in $B_c$ for $c<1/2$ (random-like graphs have $p\approx 1/\sqrt n$, §6). For Paley, Thm 5.1 sketches $p\le q^{-\delta}$, so $B_c=\emptyset$.

### 3.3 Lower bounds and extremes

* $I(X)\ge\mathrm{base}(\mathrm{Aut}\,X)\ge\log_n|\mathrm{Aut}\,X|$ **[PROVEN, trivial]**. Motion of any non-identity automorphism is $\ge(n+3)/2$ (fixed points cannot distinguish $v$ from $\sigma v$) **[PROVEN, Babai's argument]**. So base size $\le\log_2|\mathrm{Aut}|+O(1)$.
* $P(q^2)$: every pair has nontrivial stabilizer ($x\mapsto g^{1-p}x^p$ for $(0,g)$), so $I\ge3$ **[PROVEN]**.
* The largest $\log_n|\mathrm{Aut}|$ seen is Turyn iterates ($\log_n|\mathrm{Aut}|\to\approx2.26$, §4.2), forcing $I\ge 3$. No family with $\mathrm{base}\ge4$ found **[DATA]**. No proven super-constant lower bound; **I found none in the literature either**.
* Heuristic only: where $T(a,b,\cdot)$ takes $\Theta(\sqrt n)$ values (Paley, data), two rounds with $k=2$ cannot be injective; 1-WL needs more rounds or $k\ge3$ there (in practice 3–5 rounds, §6).

## 4. Dichotomy attempts

### 4.1 Attempt 1: uniform anti-concentration

**Needed lemma (Lemma X).** There is $\omega(n)\to\infty$ such that $p(v,w)\le\exp(-\omega(n))$ for all $v\neq w$ and all conference graphs; then $k=O(\log n/\omega(n))=o(\log n)$ random vertices would separate all pairs, giving $n^{o(\log n)}$. Natural, and true for random-like graphs and Paley (§5).

**Status: false.** For all $n$ in an infinite family (Thm 4.2) some pairs have $p\ge c>0$ constant. Where it breaks: such a pair differs in a single tensor coordinate, and the test on that coordinate is a test on a small graph.

### 4.2 Turyn iterates

For symmetric or skew $V$ of order $v$ with $VV^T=vI-J$, zero diagonal, $V\mathbf 1=0$, the Turyn product is $W(V,V')=V\otimes V'+I\otimes J-J\otimes I$. It is a symmetric conference matrix of order $v^2$ (verified by `check_lemmas.py`/`gen.py`). $\mathrm{Aut}(W)\supseteq\mathrm{Aut}(V)\times\mathrm{Aut}(V')$ (and in the examples $|\mathrm{Aut}(W(V,V))|=2|\mathrm{Aut}(V)|^2$ from level 1 on) **[DATA]**.

**Lemma 4.1 (multiplicativity) [PROVEN].** Let $V_1,V_2$ be symmetric, $W=W(V_1,V_2)$, and $a=(a_1,a_2)$, $b=(b_1,b_2)$, $x=(x_1,x_2)$ with $a_1,b_1,x_1$ distinct and $a_2,b_2,x_2$ distinct. Then
$$T^W(a,b,x)=T^{V_1}(a_1,b_1,x_1)\,T^{V_2}(a_2,b_2,x_2)+R,$$
$$R=-(st+su+tu)+(s't'+s'u'+t'u')-(st'+su'+ts'+tu'+us'+ut'),$$
where $s,t,u$ are the $V_1$-entries on $\{a_1,b_1,x_1\}$ and $s',t',u'$ the $V_2$-entries on $\{a_2,b_2,x_2\}$.

*Proof.* Expand the $3\times3$ product of $W_a=f g+\delta-\varepsilon$ etc.; 14 of the 27 terms vanish on distinct triples, one is the main term, the other 12 give $R$; the rest are computed from $\langle V_{i,a},V_{i,b}\rangle=-1$. (Verified on 1000 random generic triples for $v\in\{5,9,13\}$: 0 mismatches.) $\square$

Sign convention: stated for $B$-type (+1 adjacency); $T$ flips by a global sign under $C=-B$, irrelevant below.

**Definition.** A *collision* in $V$ is a tuple $(a,b;x,y)$ of distinct vertices with $T^V(a,b,x)=T^V(a,b,y)$, $V(a,x)=V(a,y)$, $V(b,x)=V(b,y)$. Let $P_V(x,y)$ be the fraction of $(a,b)\in V^2$ giving a collision.

**Theorem 4.2 (Turyn lift) [PROVEN].** Let $V$ be symmetric of order $v$. Set $W_0=V$, $W_{L+1}=W(W_L,W_L)$, $v_L=v^{2^L}$. For $x=(x_1,x_2)$, $y=(x_1,y_2)$ in $W_{L+1}$ with $x_2\neq y_2$:
$$P_{W_{L+1}}(x,y)\ge\Bigl(1-\frac1{v_L}\Bigr)\Bigl(1-\frac2{v_L}\Bigr)P_{W_L}(x_2,y_2).$$
Hence if $V$ has a collision pair $(x_0,y_0)$, then for all $L$ there is a pair in $W_L$ with
$$p(x,y)\ge P_V(x_0,y_0)\prod_{i\ge0}\Bigl(1-\frac1{v_i}\Bigr)\Bigl(1-\frac2{v_i}\Bigr)>0.$$

*Proof.* Lemma 4.1: when $(a_2,b_2;x_2,y_2)$ is a collision in $W_L$ and $a_1,b_1,x_1$ are distinct, $T^W(x)-T^W(y)=T^{V_1}\,(T^{V_2}(x_2)-T^{V_2}(y_2))+R_x-R_y=0$, because $s,t,u,s'$ agree and $t',u'$ agree by the sign conditions. And $W(a,x)=V_1(a_1,x_1)V_2(a_2,x_2)=W(a,y)$, same for $b$. So $(a,b;x,y)$ is a collision in $W_{L+1}$. Counting pairs $(a_1,b_1)$ gives the factor. $\square$

Numerics: $P(9)$ has a collision with $P_V=6/81$, so $c\ge0.049$ uniformly in $L$; the lifted inequality was checked (no lift violations on 90 samples, `check_lemmas.py`). Measured $\max p$ on Turyn iterates: $0.28$ at $n=81,6561$ (base $P(9)$-type), $0.24$ at $n=625$, against $1/\sqrt n$.

So Lemma X is false. Note this is not an individualization lower bound: the Turyn graphs have tiny exact depth (§6). It only says *that proof route* cannot work, and identifies what any correct proof has to handle: collision events that are the same for many pairs (they depend only on one tensor coordinate), so a union bound over $n^2$ pairs is wasteful. Random tuples may need depth growing with the number of coordinates $m=2^L$ on these (sampled trend §6; a $\Theta(\log m)=\Theta(\log\log n)$ scaling is **[SPECULATION]**), while a suitable fixed tuple needed depth 3 at every tested level.

### 4.3 Attempt 2: structure of large cliques in $B_c$

**Target.** If $Q$ is a clique in $B_c$, $|Q|\ge L(n)$, then $X$ has a recognizable product/group structure on a substantial part. Then either cells are small (Thm 3.2) or recursion.

**Where it breaks.** A clique in $B_c$ is a set of rows $C_v$ whose pairwise differences $D_{vw}$ are balanced on a noticeable fraction of the "$C_a\circ C_b$-cuts". $M_{vw}=C\,\mathrm{diag}(D_{vw})\,C$ has Frobenius mass $2n^2(n-2)$, and the zero entries of $M_{vw}$ are $T$-coincidences. The only known handle on zeros of a bilinear form in rows of a flat matrix is the uncertainty principle for group Fourier transforms; here the hypothesis $\Pr[M_{ab}=0]\ge n^{-c}$ is too weak to apply it. No BSG/Freiman-type machinery works because $p$ can be as small as $n^{-c}$ and the "additive" object is a set of ±1 vectors in the Hamming cube of dimension $n$. **Exact missing lemma**: "a set $Q$ of $L$ rows of a conference matrix with $\Pr_{a,b}[T(a,b,v)=T(a,b,w)]\ge n^{-c}$ for all $v,w\in Q$ forces (tensor/net/product structure)". I found no proof, and Turyn shows the structured side must include tensor products and is therefore not a single "group".

### 4.4 Attempt 3: approximate $\mathbb F_2$-linearity of rows

The extreme of the $T$-tensor with collisions at scale $T\approx n$ is $C_a\circ C_b=\pm C_{v(a,b)}$ ("rows closed under product"), a character-table structure. Prop 2.5 forbids it globally. A local/approximate version ("if many $(a,b)$ have some $v$ with $|T(a,b,v)|\ge\delta n$ then a large sub-collection of rows lies in a small $\mathbb F_2$ space") is a 1%-regime approximate-homomorphism problem in the Hamming metric; polynomial Freiman–Ruzsa (Gowers–Green–Manners–Tao) handles exact sets, but I could not make the Hamming-noise version bite. Observed extremes: Paley: $\max|T|\le2\sqrt q$ (Weil). Turyn: $|T|$ up to $n^{0.72}$–$n^{0.8}$ at $n\le 6561$ ($894=0.136n$; $30=0.37n$ at $n=81$), produced by $(a,b)$ with coordinate structure; no conference graph with $|T|\ge n^{1-o(1)}$ at growing $n$ was seen **[DATA]**.

### 4.5 Attempt 4: growth of the stable algebra

The stable partition of 1-WL corresponds to the smallest algebra $W\subseteq\mathbb R^V$ (pointwise mult.) containing $e_{a_i}$ and closed under $A$. On $W\cap\mathbf1^\perp$, $C^2=n$, so the quotient integer matrix $M=2Q+I$ has $M^2=nI-\cdots$. Needed: $\dim W\ge\min(n,\dim(\text{round-1 cells})^{1+\epsilon})$ (a growth lemma, in the spirit of Bourgain-type sum-product or Babai's growth). The integrality gives no obstruction to small $W$ in general (the data shows small $W$ exists only under large $\mathrm{Aut}$; Turyn at $k=2$: $\approx n^{0.8}$ cells, matching $|\mathrm{Aut}|$ of the point-stabilizer). Status: open, no attempt reached a statement.

### 4.6 Status of a dichotomy

Provable shape: Thm 3.2 (reduce to the structure of cliques of $B_c$). Unprovable-by-me: the structure side. **[SPECULATION]** the right structure is "tensor/Turyn-like decomposition detectable by 2-WL after one individualization" (data §6: Turyn rows and columns are visible as cells of size $v-1$), and random-like otherwise. Tested families don't contradict this, but tested families are small and few.

## 5. Subclasses

**Theorem 5.1 (Paley, 1-WL, $O(1)$ individualizations) [SKETCH].** There is an absolute constant $k_0$ such that for all large prime powers $q\equiv1\pmod4$, $P(q)$ has a set $S$ of $k_0$ vertices such that 1-WL after individualizing $S$ is discrete after two rounds.

*Sketch.* By Theorem 3.2 it suffices that $p(v,w)\le q^{-\delta}$ for all $v\neq w$ and a fixed $\delta>0$. $T(a,b,v)=\sum_x\chi((x-a)(x-b)(x-v))=-a_q(E_{a,b,v})$, with $E_{a,b,v}:y^2=(x-a)(x-b)(x-v)$, a quadratic twist of the Legendre curve at $\lambda=(b-v)/(a-v)$. On $U=\{(a,b): a,b,v,w\text{ distinct}\}$ the rank-2 sheaves $\mathcal F_v,\mathcal F_w$ have geometric monodromy $\mathrm{SL}_2$ (Legendre; Kummer twist by $a-v$ does not change it), and are not isomorphic up to rank-1 twist because $\lambda_v,\lambda_w$ are algebraically independent on $U$ (no modular correspondence). Goursat–Kolchin–Ribet gives $\mathrm{SL}_2\times\mathrm{SL}_2$. Deligne's equidistribution theorem (Katz) with bounded Betti numbers yields, for each nontrivial irreducible $\rho$, a power-saving $O(\dim(\rho)^{O(1)}q^{-1/2})$; an Erdős–Turán argument on $SU(2)^2$ then gives discrepancy $q^{-\delta_0}$ and the diagonal mass bound $\Pr[a_q(E_v)=a_q(E_w)]\le q^{-\delta}$. **Not written with constants.** This is the Sato–Tate-in-families route; the input (Deligne/Katz) is standard.

Relation to Ponomarenko 2006.13592 / 2511.18304: those give constant WL dimension and base number $\le 3$ (for GP). Theorem 5.1 is the color-refinement (1-WL) analogue with a much worse constant, by different means. Campaign data: the exact minimum depth is $2$ for prime $q$ and $3$ for non-prime $q$, all prime powers $q\equiv1\bmod4$ up to 1097 **[DATA]** (matching $\mathrm{base}(\mathrm{Aut})$: prime $q$: 2; $q=p^e$, $e\ge2$: pair stabilizers contain a Frobenius twist, §3.3).

**Generalized Paley, Peisert, Van Lint–Schrijver.** Polynomial via Ponomarenko **[Literature]**.

**Cayley conference graphs over abelian groups.** $C$ is a function on $A$ with $\widehat C=\pm\sqrt n$ off $0$ ("bent"-type; $n$ prime power or $n^4$, $9n^4$, Wang). The pseudometric $\rho$ becomes translation-invariant and $\rho(d+d')\le\rho(d)+\rho(d')$ **[PROVEN]**, and $\rho(d)>0$ for $d\neq0$ (Lemma 2.4). But $\rho(d)$ bounded away from 1 occurs (Turyn over Cayley bases), so even this class does not satisfy Lemma X. **No $n^{o(\log n)}$ for this class reached.** A natural target, undone: recursion when $\rho$ has a large ball (Hamming-type geometry).

**Turyn-decomposable graphs.** **[SKETCH, data-supported]** One individualized vertex plus 2-WL detects rows and columns as cells (sizes $v-1$; `other_runs.txt`). Given the grid, $W$ restricted to two rows gives $\pm V_2$; recursion reduces isomorphism of products to factor isomorphism up to sign, polynomially many branches for fixed base. Not proved, not the moonshot target.

## 6. Experiments

Code: `docs/w32-code/{conf.c,gen.py,drive.py,check_lemmas.py}`; results in `docs/w32-code/results/`. Exact 1-WL min depth: enumerate $k$-subsets with $\mathrm{Aut}$ orbit reductions (nauty/pynauty). 64-bit hashing (collisions could only overstate depth). All runs single-process, `nice`, seconds to minutes.

Exact minimum depth to 1-WL discreteness (MIN), $\mathrm{Aut}$ orders from nauty:

| Family | $n$ range | MIN | Notes |
|---|---|---|---|
| Paley prime $q$ | 5–1097 (all primes $\equiv1\bmod4$ tested) | 2 | both pair orbits discrete |
| Paley $q=p^{e}$, $e\ge2$ | all such $q\le 961$ (9,25,49,81,121,125,169,289,361,529,625,729,841,961) | 3 | $k=2$ fails for all pairs (matches Frobenius stabilizer, §3.3) |
| Spence, $n=25$ (15), 29 (41), 37 (400 of 6760), 41 (16 two-graph reps), 45 (50), 49 (30) | 25–49 | 2 (only $P(25)$, $P(49)$: 3) | $\mathrm{Aut}$ mostly trivial |
| Peisert $P^*(q)$ | 9,49,81,121,361 | 3,3,3,2,2 | |
| Peisert-type line unions, random | 25–361 | 3 for $q\le 9$, 2 for $q\ge11$ | |
| Uniform cyclotomic unions | 25–361 | 2 or 3 | |
| Turyn iterates | 9,81,6561 (base 3); 25,625 (P5); 81 (P9) | 3 | $k=2$ excluded by $|\mathrm{Aut}|>n^2$ at $n=81,625,6561$ (and exhaustively at 9,25,81,625); $k=3$ found by sampling |
| Turyn, base $q\ge 11$ | 121 (skew 11), 169 (P13) | 2 | |

So the exact depth in every tested graph is 2 or 3. For the symmetric families every graph with depth 3 has all 2-point stabilizers nontrivial, so depth 3 is exactly $\mathrm{base}(\mathrm{Aut})$ there; for graphs with depth 2 (and nontrivial Aut) some pair has trivial stabilizer. Exact comparison on all pairs through one vertex (Peisert $\le121$, lines $\le81$, cyclotomic $\le121$, Turyn $\le81$, Paley $\le 100$; 2208 pairs): #1-WL cells after individualizing the pair $=$ #orbits of the pair stabilizer in every case. For Spence graphs (trivial Aut, random-like) the 1-WL partition can be strictly coarser than orbits for some pairs (e.g. 7 cells on a graph with trivial stabilizer), but depth 2 is still reached at other pairs.

*Random tuples on Turyn* (fraction of random $k$-sets that are discrete): base 3 at $n=9$: $k=3$: 27/30, $k=4$: 30/30; $n=81$: $k=3$: 16/30, $k=4$: 24/30, $k=5$: 29/30; $n=6561$: $k=3$: 4/30, $k=4$: 15/30, $k=5$: 27/30, $k=6$: 29/30. So the size at which random tuples are usually discrete grows slowly (around 3, then 5, 5–6), while a good tuple of size 3 exists at every level tested **[DATA, three sizes; growth rate not determined]**.

*2-WL depth:* asymmetric graphs: 1. Symmetric: 2 or 3 (2-WL with $k=1$ gives $\mathrm{Aut}$-orbit-like cells, e.g. Paley: 3 cells).

*Triple-correlation statistics* ($S=300$–$400$ sampled pairs, all $(v,w)$): zero fraction 0 everywhere (Lemma 2.2); Paley $q=197$: mean $p=0.115$, max $0.185$, $1/\sqrt q=0.071$; Spence $n=37$: mean $0.195$, max $\approx 0.29$; Turyn at $n=6561$: mean $0.040$, max $0.28$, $1/\sqrt n=0.012$; high-$p$ pairs ($p\ge0.2$) at $n=6561$: 33057 of $2.15\cdot10^7$, consistent with single-coordinate pairs.

**What the data cannot show.** Small $n$ only (largest $6561$, a very structured family). No conference graphs known to me at $n\sim10^4$–$10^6$ that are "random" (constructions are all algebraic or product). Exact min depth at $k\ge4$ was not enumerated for large $n$. Non-Paley exact-min statements cover only Spence's lists up to 49 plus a few algebraic samples. Depth 2–3 throughout is consistent with $I(X)=O(1)$ for all conference graphs, but this data cannot distinguish $O(1)$ from slowly growing. Hash-based WL can only overestimate depth.

## 7. Where attempts broke, and leads

Broke: (i) Lemma X — false by Theorem 4.2; (ii) moment methods on $T$ (L² gives Lemma 2.1, L⁴/Hausdorff–Young is extremal for characters, gives nothing without a non-group hypothesis); (iii) structure of $B_c$-cliques — no inverse theorem at hypothesis $p\ge n^{-c}$; (iv) dimension growth — no mechanism.

Leads, ranked:
1. Replace the union bound by a set-system bound: $S$ only needs to hit the sets $\{(a,b):T(a,b,v)\ne T(a,b,w)\}$; Haussler–Welzl gives $O(d\log(1/\rho)/\rho)$ pairs where $d$ is the VC dimension of $\{E_{vw}\}$. Turyn events are the same for many pairs. Need: $d=o(\log n)$ in general (the trivial bound is $d\le2\log_2 n$, recovering Babai).
2. Grid/tensor detection by 2-WL as the structured side of a dichotomy (§5); test on more families (Mathon-type).
3. A growth lemma for the stable algebra $W$ (§4.5).
4. Paley-type recursion on $\widehat C=\pm\sqrt n$ for Cayley conference graphs with non-trivial $\rho$-balls.

## 8. Claim status

| Claim | Status |
|---|---|
| $I(X)\ge2$ always (1 vertex leaves the equitable 3-part partition) | [PROVEN], trivial |
| $\sum_v T(a,b,v)^2=n^2-2n-1$; $T\equiv2\pmod 4$; mod-8 formula | [PROVEN]; no source found, likely folklore |
| Round-2 criterion (Lemma 2.3); $M_v$ quasi-orthogonality (Lemma 2.4) | [PROVEN] |
| 2-rank (Prop 2.5) | [PROVEN]; first case known (Brouwer–van Eijl) |
| Thm 3.2 bad-pair reduction | [PROVEN]; shape not found in literature, trivial |
| Lemma 4.1 Turyn multiplicativity, Thm 4.2 lift, failure of Lemma X | [PROVEN]; checked numerically; not found in literature |
| Thm 5.1 Paley $O(1)$ for 1-WL | [SKETCH]; Deligne–Katz input standard |
| Weil bound $p\le 7/8+o(1)$ for Paley | [PROVEN] (standard) |
| Turyn iterates: exact depth 3, random depth $\Theta(\log\log n)$ | [DATA]/[SPECULATION] |
| $n^{o(\log n)}$ for conference graphs | Not reached |
| Dichotomy | Reduction proved, structure side open |

## 9. References

Levet, *On the complexity of identifying strongly regular graphs*, arXiv 2207.05930 (AJC 87 (2023)). Babai, *On the complexity of canonical labeling of strongly regular graphs*, SIAM J. Comput. 9 (1980). Spielman (STOC 1996). Babai–Chen–Sun–Teng–Wilmes (FOCS 2013). Ponomarenko, arXiv 2006.13592, 2511.18304, 2206.15028. Cai–Guo–Gavrilyuk–Ponomarenko, arXiv 2312.00460. Mathon, *Symmetric conference matrices of order pq²+1*, Canad. J. Math. 30 (1978). Wang, arXiv 1908.07055. Binary LCD codes, arXiv 2407.07689. Haemers–Peeters–van Rijckevorsel (cited there). Spence, Glasgow SRG and two-graph tables.
