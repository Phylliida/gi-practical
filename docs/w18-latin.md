# w18-latin: Latin squares, Steiner triple systems, conference graphs, and HJ on graphs

Moonshot memo, branch `w18-latin`, 2026-11-08. HJ = Hajiaghayi–JafariRaviz, arXiv:2611.01399
(LaTeX source, line numbers `L…` as in `docs/moonshot-theory.md`). Every statement about "HJ" is about
the algorithm **as written** in that source and assumes HJ is correct (it is unrefereed; see
`docs/moonshot-theory.md`). Labels: **[PROVEN]** (full argument here, given cited results / HJ as
written), **[SKETCH]** (argument with listed gaps), **[CONDITIONAL]**, **[SPECULATION]**. Novelty
claims are hedged: "not found" means not found in the search recorded in §1.

## 0. Summary

| # | Result | Status |
|---|---|---|
| B1 | **HJ is $n^{\Omega(\log n)}$ on an explicit graph family**: on the point–line incidence graph $X_m$ of $\mathrm{PG}(m-1,2)$ ($n\approx 2^{2m}/6$, the Steiner triple system of $\mathbb F_2^m$), HJ creates at least $2^{m^2/2-O_\kappa(m)}=n^{(1/8)\log_2 n-O_\kappa(1)}$ recursive calls, for every fixed certificate size $\kappa$. Channel: the $\sigma x$ ("visible unaffected orbit") term, **not** the Maróti-enumeration channel. | **[PROVEN, given HJ as written]** (§2) |
| B2 | Latin-square graphs of $\mathbb Z_2^m$ and block graphs of $\mathrm{PG}(m-1,2)$: same chain ($2^{\Omega(m^2)}$). Window sequence of the first levels confirmed by exact computation at small size. | **[SKETCH]** (§2.7) |
| B3 | Conference graphs: Paley graphs never reach the chain ($\mathrm{Aut}$ solvable, every test nonfull within $\le 2$ window updates). | **[SKETCH]** (§2.8) |
| B4 | So the "GI might be easier than string isomorphism for HJ" escape **fails**: HJ is $n^{\Theta(\log n)}$ on graphs. The family is easy for other reasons (it is a fixed elementary-abelian object), so this bounds HJ, not GI. | **[PROVEN, given HJ as written]** (§2.9) |
| A1 | Quasigroup isomorphism, Latin-square isotopy/paratopy, Latin-square graphs and STS isomorphism in $n^{(1/2)\log_2 n+O(1)}$ time and space (bidirectional collision detection). Halves Miller's exponent in the quasigroup/LS setting. | **[PROVEN]**; novelty: extension of Rosenbaum (2013), not found stated for quasigroups (§3.1) |
| A2 | Quasigroup isomorphism in $\mathrm{poly}(n,M,A)$, where $M$ bounds the number of subquasigroups and $A$ their automorphism groups (DP over the subquasigroup lattice). With Lemma A3 ($d(Q)\le\log_2 M$) this separates "many subquasigroups" from "rank". | **[PROVEN]**; not found (§3.2) |
| A3 | Structural lemmas: $M\ge 2^{d(Q)}$; generation chains have at most $\log_b n$ steps of index $\ge b$; index-2 steps are normal; hard cases need $n^{\Omega(1)}$ subquasigroups. | **[PROVEN]** (§3.3) |
| A4 | No $n^{o(\log n)}$ algorithm for general Latin squares or STS. Attempts (§3.4) break at named points. | honest negative |

**Best Target A result.** A1 is the only unconditional improvement of the $n^{\log n}$ exponent; A2 gives
genuine polynomial time on a structurally defined subclass of rank-$\Theta(\log n)$ quasigroups.

**Target B answer.** Yes: a graph family forces $n^{\Omega(\log n)}$ on HJ.

---

## 1. State of the art (literature pass, 2026-11-08)

Tags: **[V]** statement read in abstract/source; **[S]** via citing text only (original not read). The survey was done by a delegated agent (sources in `scratchpad/w18-src/`); I read Rosenbaum §§1–3 and the Gill et al. bounds myself, and took the rest from its report.

**Latin squares / quasigroups / Latin-square graphs.**
* Miller, STOC 1978: $n^{\log n+O(1)}$ (generator enumeration); still the best general bound. [S]
* Gill–Mammoliti–Wanless, arXiv:2402.06205, RSA 2025: canonical labelling average $O(n^5)$, worst $O(n^{\log_2 n-\log_2\ell(L)+3})$, $\ell$ the longest row cycle; "worst case no better than previous algorithms". [V]
* Colbourn–Colbourn, Ars Combin. 9 (1980): $2^{O(\log^2 n)}$; polynomial if proper subquasigroups have bounded size. [S]
* Chattopadhyay–Torán–Wagner, TOCT 2013; Wolf 1994; Collins–Grochow–Levet–Weiß, arXiv:2402.00133 (TheoretiCS 2025): low-depth circuit bounds, size $n^{O(\log n)}$. [S/V]
* Levet, arXiv:2207.05930, AJC 87 (2023): quasigroup/isotopy/Steiner/conference-graph reductions; $n^{\Theta(\log n)}$ "little improvement". [V]
* Rosenbaum, arXiv:1304.3935: $n^{(1/2)\log_p n+O(1)}$ for **groups** by bidirectional collision; Rosenbaum–Wagner p-groups; Le Gall–Rosenbaum arXiv:1609.08253 §2.2 $n^{(1/4)\log_p n}$, group-specific (Luks composition series). No source applies these to quasigroups. [V]
* Central quasigroups (incl. medial): NC, Johnson–Levet–Vojtěchovský–Widholm arXiv:2508.06478. Grochow–Kardeş–Levet arXiv:2608.26257: no other non-group family known to have even a poly-time test (their barrier for depth-2 circuits). [V]
* Zhao preprint (Preprints.org 202510.0113) claims polynomial time for Latin squares; unreviewed, not checked; treated as unestablished.

**Steiner systems.** STS: $n^{O(\log n)}$ (Miller, via Steiner quasigroup). Steiner 2-designs $n^{O(\log n)}$: Babai–Wilmes STOC 2013, Chen–Sun–Teng STOC 2013 ($O(\log n)$ individualizations plus 2-WL). Bounded block size: Babai–Luks 1983. Projective/affine planes $n^{O(\log\log n)}$ (Miller). No $n^{o(\log n)}$ for STS found. [S mostly]

**SRG / conference graphs.** Babai 1980 ($n^{O(\log n)}$ for conference graphs, distinguishing sets); Spielman 1996; Babai–Chen–Sun–Teng–Wilmes 2013 ($\exp(\tilde O(n^{1/5}))$); WL dimension of many SRG subfamilies bounded (Cai et al. 2312.00460, Ponomarenko 2511.18304). No $n^{o(\log n)}$ for conference graphs found. [S/V]

**HJ on these classes.** arXiv:2611.01399 never mentions quasigroups, Latin squares, Steiner systems, conference graphs; no third-party analysis found. [V]

**Reading.** Sun/IMQSZ do not help non-associative structure; the combinatorial $n^{\Theta(\log n)}$ barrier stands. The only cheap progress below $\log n$ is on constants (A1) and on subclasses.

---

## 2. Target B: the $\sigma$-channel chain on graphs

### 2.1 The family and the theorem

$V=\mathbb F_2^m$, $k=2^m$. Points $P=V\setminus\{0\}$, blocks $B=\{\{a,b,a+b\}\}$ (the lines of
$\mathrm{PG}(m-1,2)$, equivalently the Steiner triple system on $P$). $X_m$ is the incidence graph on
$P\sqcup B$; $n=|P|+|B|\approx k^2/6$. HJ's root works on $\Omega=$ ordered vertex pairs (L589–600) with $G=\mathrm{Sym}(n)$.
Let $\kappa$ be HJ's certificate size ($\kappa=64$ in HJ; only $\kappa\ge 5$ and "fixed" are used), and $q_0$ its absolute degree cutoff.

**Theorem B1. [PROVEN, given HJ as written.]** For $Y\cong X_m$ and any fixed $\kappa\ge 5$, the recursion tree of
HJ on $(X_m,Y)$ has at least
$$\prod_{j=0}^{J-1}\tfrac12\binom{2^{m-j\kappa}-1}{\kappa}\ \ge\ 2^{m^2/2-O_\kappa(m)}\ =\ n^{\frac18\log_2 n-O_\kappa(1)}$$
nodes (calls of `Continue`), where $J=\lfloor (m-c)/\kappa\rfloor$, $c=\lceil\log_2 q_0\rceil+\kappa+3$.

The proof tracks one chain of nested certificate calls.

### 2.2 The level state

Fix $j$. A **level-$j$ state** consists of a subspace $D_j\le V$ of dimension $j\kappa$, a set $Z_j\subseteq D_j$,
a group $\mathcal U_j\le \mathrm{GL}(D_j)$ preserving $Z_j$, and:

* $P_j=V\setminus D_j$; $Q_j=(V/D_j)\setminus\{0\}$, $|Q_j|=2^{r_j}-1$, $r_j=m-j\kappa$;
* $\widetilde W_j=\{$blocks disjoint from $D_j\setminus Z_j\}$;
* $H_j=\{\rho\in\mathrm{Sym}(P_j):\exists\tau\in\mathcal U_j\ \forall v\in P_j,d\in D_j:\ \rho(v+d)=\rho(v)+\tau(d)\}$;
* $G_j=\mathrm{Sym}(\widetilde W_j)\times H_j$ acting on $\Omega_j=\widetilde W_j\times P_j$, string $x=$ incidence.

$H_j$ permutes the $D_j$-cosets and maps $H_j\twoheadrightarrow\mathrm{Sym}(Q_j)$. Level 0: $D_0=0$, $Z_0=\emptyset$, $\mathcal U_0=1$, $H_0=\mathrm{Sym}(P)$.

The state may in fact be any group $G$ with $[G_j,G_j]\le G\le G_j$ ("normalization may have cut parity").
**Parity lemma. [PROVEN]** All image statements below are unaffected: if $S\triangleleft S'$ has abelian quotient and $\phi:S'\to\mathrm{Alt}(T)$ is onto with $|T|\ge5$, then $\phi(S)=\mathrm{Alt}(T)$, because $\mathrm{Alt}(T)$ is perfect. Transitivity also survives, since $[G_j,G_j]\supseteq\mathrm{Alt}(\widetilde W_j)\times[H_j,H_j]$ and $[H_j,H_j]$ is transitive on $P_j$ (zero-sum translation tuples, $\mathrm{Alt}(Q_j)$).

### 2.3 Level step

**Lemma 1. [PROVEN]** Let $r_j\ge\kappa+c_1$ with $2^{r_j}-1>q_0$. Let $T\subseteq Q_j$ be a $\kappa$-subset,
linearly independent in $V/D_j$, with coset representatives $a_c$ ($c\in T$). Put
$$D_{j+1}=D_j\oplus\langle a_c\rangle,\quad \Sigma=\textstyle\sum_{c}a_c+D_j,\quad Z_{j+1}=Z_j\cup\Sigma,$$
$$\mathcal U_{j+1}=\{\tilde\tau\in\mathrm{GL}(D_{j+1}):\tilde\tau|_{D_j}\in\mathcal U_j,\ \tilde\tau(a_c)\in a_c+D_j\}.$$
Then HJ's `LocalCertificate` (Algorithm 3) for $T$ on the level-$j$ state adds windows exactly
$$V_0=\widetilde W_j\times(T+D_j),\quad V_1=W^{(1)}\times\big(P_j\setminus(T+D_j)\big),\quad V_2=W(\emptyset)\times D^*,\quad V_3=W^{(2)}\times(P_{j+1}\cup\Sigma),$$
where $T+D_j$ abbreviates the union of the cosets $c\in T$, $W^{(1)}=\{w\in\widetilde W_j: w\cap(T+D_j)\ne\emptyset\}$, $W(\emptyset)=\widetilde W_j\setminus W^{(1)}$, $D^*=D_{j+1}\setminus(D_j\cup(T+D_j)\cup\Sigma)$, $W^{(2)}=\{w\in W(\emptyset):w\cap D^*\ne\emptyset\}$. No nonfull termination occurs, and the group at each stage has image $\mathrm{Alt}(T)$. After $V_3$ no position is affected, step 3 fails, and step 4 selects a union of visible orbits containing
$$\Delta=\widetilde W_{j+1}\times P_{j+1}=\Omega_{j+1}$$
(the largest orbit in that union). On $\Delta$ the kernel $N$ of $\phi_T$ acts as a level-$(j+1)$ state on $\Omega_{j+1}$, in particular transitively; HJ calls `Continue` on it (identity coset, orbit-chain first child).

*Proof.* Write $A^{(i)}$ for the partial automorphism group after $i$ updates and $\phi$ for its action on $T$. Elements are pairs $(\rho_W,\rho)$.

*Full image at every stage.* For $\sigma\in\mathrm{Alt}(T)$ let $g$ be a linear map of $V$ that is the identity on $D_j$, sends $a_c\mapsto a_{\sigma c}$ (independent modulo $D_j$), and fixes a complement of $D_{j+1}$ pointwise; adjusting $g$ on the complement we may also require it to fix a chosen vector outside $D_{j+1}$. Then $g\in H_j$ ($\tau=\mathrm{id}$), $g$ preserves $Z_j$ and the block set $\widetilde W_j$, and preserves incidence, so $(g,g)$ lies in every $A^{(i)}$ (Parity lemma for $G$). Hence $\phi(A^{(i)})=\mathrm{Alt}(T)$ and no nonfull return happens.

*$V_0$.* A position $(w,p)$ has a proper stabilizer image iff it fixes a coset in $T$, i.e. $p\in T+D_j$; otherwise take $g$ fixing $p$ and $\rho_W$ fixing $w$ (the $\widetilde W_j$ factor is free). After $V_0$ every block $w$ has a recorded set $S=w\cap(T+D_j)$ with $|S|\le 2$ when $w$ has three points in $P_j$ (no $w$ has two points in one coset of $D_j$ unless its third point lies in $Z_j\subseteq D_j$; then $S$ is a pair in one coset), and $\rho_W$ must send $W(S)$ to $W(\rho S)$, where $\rho$ on $T+D_j$ is $\rho(a_c+d)=\rho(a_c)+\tau(d)$, $\rho(a_c)=a_{\sigma c}+\delta_c$.

*$V_1$.* Positions with $w\in W^{(1)}$ have proper images (the stabilizer of $w$ fixes $S$ setwise). The remaining positions are unaffected: for $w\in W(\emptyset)$ the free factor on $W(\emptyset)$ and the free choice of $\rho$ outside $T+D_j$ leave the full image. Imposing $V_1$: a block through $u\in T+D_j$ and $p\notin T+D_j$ forces $\rho(p+u)=\rho(p)+\rho(u)$; similarly for $|S|=2$. Induction over the coordinates of $e$ gives, for every $\rho$, a map $\tilde\tau\in\mathrm{GL}(D_{j+1})$ with $\tilde\tau|_{D_j}=\tau$, $\tilde\tau(a_c)=\rho(a_c)$, and
$$\rho(v+e)=\rho(v)+\tilde\tau(e)\quad(v\in V\setminus D_{j+1},\ e\in D_{j+1}),\qquad \rho|_{D_{j+1}\setminus D_j}=\tilde\tau.\tag{$\star$}$$
Conversely any $\tilde\tau$ of this form extended by any $\rho$ satisfying $(\star)$ (arbitrary permutation of the $D_{j+1}$-cosets $\ne D_{j+1}$, arbitrary translation in each) occurs; the factor on $W(\emptyset)$ stays free.

*$V_2$.* For $w\in W(\emptyset)$ and $p\in D_{j+1}\setminus(D_j\cup(T+D_j))$, the stabilizer fixes $\tilde\tau(p)=p$. If $p\in D^*$, writing $p=\sum_{c\in I}a_c+d$ with $2\le|I|<\kappa$, the image lies in the stabilizer of $I$: proper. If $p\in\Sigma$ ($I=T$), $\tilde\tau(p)=p$ only constrains $\sum\delta_c$: full image. For $p\notin D_{j+1}$: full image (choose $\rho$ fixing $p$ and $\rho_W$ free). Imposing $V_2$ partitions $W(\emptyset)$ by $S'=w\cap D^*$ and adds no constraint on $\rho$.

*$V_3$.* If $w\in W^{(2)}$ then the stabilizer of $w$ preserves $S'$, which contains some $p\in D^*$: proper. Blocks $w\in\widetilde W_{j+1}=W(\emptyset)\setminus W^{(2)}$ have $S'=\emptyset$, and the positions over them are not yet constrained: unaffected. Imposing $V_3$ forces $\rho_W(w)$ on $W^{(2)}$ and nothing new on $\rho$. Positions left: $U=\widetilde W_{j+1}\times(P_{j+1}\cup\Sigma)$, all unaffected.

*Steps 3–4.* A map fixing $U$ pointwise fixes every point of $P_{j+1}$, so by $(\star)$ $\tilde\tau=\mathrm{id}$ and $\sigma=1$: $\phi(K)=1\ne\mathrm{Alt}(T)$. The $A$-orbits in $U$ include $\Delta$ (transitive: $\rho_W$ free on $\widetilde W_{j+1}$, $\rho$ transitive on $P_{j+1}$). Pointwise stabilizer of $\Delta$ fixes $P_{j+1}$, so $\phi=1$: $\Delta$ is selected. The orbit(s) over $\Sigma$ have full image (not selected at this step). $N=\ker\phi$ acts on $\Delta$ as $\mathrm{Sym}(\widetilde W_{j+1})\times H_{j+1}$ with $\mathcal U_{j+1}$ as defined (since $\sigma=1$ forces $\tilde\tau(a_c)\in a_c+D_j$, and $\tilde\tau|_{D_j}\in\mathcal U_j$; $\Sigma$-points are preserved, giving $Z_{j+1}$). Note: blocks in $\widetilde W_{j+1}$ meeting $Z_{j+1}$ meet $P_{j+1}$ in fewer than 3 points, consistent with the state definition. ∎

**Remark (no chain rule obstruction).** Within $V$, $\Delta$ is the largest orbit (the others are smaller by a factor $\ge 2^{r_{j+1}}$), so it is processed first and the child group is unrestricted (L1123; L622–624, "We process a largest orbit ... first").

### 2.4 Root entry

**Lemma 2. [PROVEN, given HJ as written.]** At the root, for a linearly independent $\kappa$-set $T\subseteq P$, HJ's certificate for $T$ reaches `Continue`/`Solve` on a level-1 state $\Omega_1$ via a first child.

*Proof.* The root is $\mathrm{Sym}(n)$ on ordered pairs; the largest orbit is off-diagonal, transitive; HJ exposes the quotient on $[n]$, $q=n>\lambda=N^\alpha$, with two-label kernel orbits, so no `RowStep`, and the certificates run (L1168, L1221). Windows (write $D=\langle T\rangle=D_1$, $\Sigma=\{\sum_T t\}$, $D^*=D\setminus(\{0\}\cup T\cup\Sigma)$): $V_0$ = positions touching $T$. Classes on $[n]\setminus T$ are by neighborhood in $T$: blocks meeting $T$, and one class $C_\emptyset=(P\setminus T)\sqcup W(\emptyset)$ with $W(\emptyset)$ the blocks avoiding $T$. $V_1$ = positions touching $W^{(1)}$ (blocks meeting $T$): affected as in Lemma 1, and $(p,v)$ with $p\in C_\emptyset$ are not. After $V_1$, $C_\emptyset$ splits ($P\setminus T$ has neighbors in $W^{(1)}$, $W(\emptyset)$ none) and $(\star)$ holds on $P$ exactly as in Lemma 1 with $D_0=0$. $V_2$ = positions touching $D^*$ together with point pairs $(p,p+d)$, $p\in P_1$, $d\in D\setminus\{0,\Sigma\}$ (these point pairs are affected because fixing $p$ and $p+d$ forces $\tilde\tau(d)=d$, proper for such $d$; the positions carry only "non-adjacent" colors, so they add no constraint). $V_3$ = positions touching $W^{(2)}$ (blocks in $W(\emptyset)$ meeting $D^*$), forcing $\rho_W$ on $W^{(2)}$. Remaining positions are unaffected (the argument of Lemma 1, $V_2$/$V_3$ cases, verbatim). Step 3 fails ($(\star)$ with all of $P_1$ fixed forces $\sigma=1$). Step 4 selects among other orbits $\widetilde W_1\times P_1$, $P_1\times\widetilde W_1$ and the point pairs; block pairs are not visible. The largest is $\widetilde W_1\times P_1$ (or its mirror, same form) of size $\Theta(k^3)$. $|\Delta_1|\le N^{\gamma}$ for $\gamma=9/10$ since $k^3\ll N^{0.9}=k^{3.6}$, so `Continue` issues `Solve` (fresh phase, $N'\approx k^3/6$). ∎

### 2.5 Dispatcher path at level $j\ge1$, and counting

At a level-$j$ state: $G_j$ is transitive. Its coarsest block systems give the primitive quotients. Two possibilities, both reach the same place **[PROVEN]**:

* **Column-first tower** (the block system $\{$cosets of $D_j\}$ top): quotient $\mathrm{Sym}(Q_j)$, degree $q_j=|Q_j|$.
* **Row-first tower** ($\{w\}\times P_j$ top): quotient $\mathrm{Sym}(\widetilde W_j)$, degree $\Theta(k^2)>\lambda$, one-label; no rows retained (Step-4 children clear them, L1207), so `RowStep`. The row normal form (Theorem at L3530) has $H=H_j$ on $B=P_j$, $K$ diagonal, $N=N^*=1$, so $L=1$ intransitive; columns are singletons; `Continue` then exposes $H_j$ on $P_j$, whose coarsest quotient is $\mathrm{Sym}(Q_j)$.

Neither enumeration nor product refinement applies ($\mathrm{Sym}(q_j)$, $q_j>q_0$, order above $\exp(a\log^2q_j)$; $r=1$). After normalization (two cosets; Parity lemma) `GiantStep` runs with $\Gamma=Q_j$, $q_j\le k<\lambda$, and HJ computes `LocalCertificate` for **every** $\kappa$-subset $T\subseteq Q_j$ (L359, L705, Algorithm 3, L1168); the algorithm specifies no memoization. By Lemma 1 each independent $T$ produces a level-$(j+1)$ child. Independent $T$ number at least $\frac12\binom{q_j}{\kappa}$ for $r_j\ge\kappa+2$. With no sharing, the tree has at least $\prod_{j<J}\frac12\binom{q_j}{\kappa}$ leaves, and $\sum_{j<J}\log_2\binom{q_j}{\kappa}\ge\sum_{j<J}\big(\kappa(m-j\kappa)-O_\kappa(1)\big)=m^2/2-O_\kappa(m)$. ∎ (Theorem B1)

**Sanity check of the charging.** Each level costs a $\sigma$-drop of exactly $\kappa$ (L2718–2726), total $\kappa J\approx m=\Theta(\log N)$, within budget $\sigma=O(\log N)$; the multiplicity per level is $q_j^{\kappa}$, so this is the $\sigma x$ term of `docs/moonshot-theory.md` §2.3 being tight: "$\Theta(\log N/\kappa)$ nested visible unaffected steps while giants of degree $N^{\Omega(1)}$ are present". No instance was known; now one is.

### 2.6 Exact computation

`docs/w18-latin-sim.py` runs the actual window loop (exact group images via nauty; affected tests sampled per position-type, stable across samples). Levels and windows match Lemma 1 exactly:

```
PG, root, k=3 (w18-latin-sim-root.py, all orbits, no sampling): V_0,V_1 at m=5 (timed out in V_2);
                        V_0..V_3 at m=4, including the 48 point pairs (p,p+d) of Lemma 2. Step 4 not reached at root.
PG, level 0, m=5, k=3:  V: (b,T+D)→(bT,*)→(bFree∪bS∪bD*,pD*)→(bD*,P+∪pS)
                        step 3 proper; step 4 VISIBLE: (bF∪bS)×P+ ; invisible: (bF∪bS)×pS
                        |A| at step 4 = 3.48e115 = 6·8^3·3!·76!  (predicted)
PG, level 1, m=7, k=3:  same pattern on Wt1×P1 with H_1, |Wt1|=2300; step 4 VISIBLE (bF∪bS)×P+, pS invisible
LS(Z_2^5) level 0, k=3: same pattern; step 4 VISIBLE (bF∪bS)×P+ on all three lines
STS-block m=6, k=3:     Step 4 VISIBLE reached as predicted (coarse typing).
```
(Commands in §5.) These are $\kappa=3$ runs; $\mathrm{Alt}(3)$ is abelian so "visibility" is formal there, but the window structure is what is being checked.

### 2.7 Latin-square graphs and STS block graphs [SKETCH]

**Claim.** HJ on the Latin-square graph of $\mathbb Z_2^m$ ($n=4^m$) and on the block graph of $\mathrm{PG}(m-1,2)$ also has $2^{\Omega(m^2)}$ calls.

*Trace.* Latin-square graph root: $T$ generic cells, $\phi$ full at $A_1$ (GL-symmetry). Lines through $T$ are affected; the first orbit child is $C_\emptyset\times C_t$ under $\mathrm{Sym}\times\mathrm{Sym}$, positions $\approx k^2\cdot 3k$, where $C_t$ is the cells on the three lines through a test cell. This is a hypergraph: for a cell $w=(a,b)$ the 6-set $\{R:b,R:a{+}b,C:a,C:a{+}b,S:a,S:b\}$ (three copies of $V$). Taking tests on one line, the same window analysis as Lemma 1 runs on three copies of $V$ with translations by $D$ on each line (the simulation at $m=5$, $\kappa=3$, confirms the window pattern and final Step-4 orbit). Block graph: first child is (blocks disjoint from a test block) $\times$ (blocks through its points); tests in one pencil play the role of points; simulation at $m=6$ confirms.

*Gaps.* (i) $C_t$ is the line-cell set minus $O(\kappa)$ cells (lines of other test cells), so the level state must be stated with $O(\kappa j)$ deleted cells on each line; the Lemma 1 analysis should survive (those cells are affected and are absorbed in windows). (ii) Whether $\phi$ maps onto $\mathrm{Alt}(T)$ via a partial automorphism at every window step needs the same exhibit-a-linear-map argument with deletions; done only in the clean PG case. (iii) Line-permuting elements ($S_3$) in the kernel at Step 4 change $H_j$ by a bounded factor; not tracked.

### 2.8 Conference graphs [SKETCH]

Paley graph $P(q)$: $\mathrm{Aut}(X)\le\mathrm{A\Gamma L}(1,q)$ is solvable, so no $\kappa$-set ($\kappa\ge5$) has $\mathrm{Alt}(T)$ induced by automorphisms. Every $T$ is nonfull: if $T$ survives the first window (homogeneous, and neighbor-pattern counts $\mathrm{Alt}$-invariant), its affected set is all positions except $C_\emptyset\times C_\emptyset$, of size $(1-4^{-\kappa})q^2$, and the next $\phi$ is already proper. So no Step-4 chain. Aggregation is Case 3 (no full certificates): tuple colors from comparisons, Design Lemma, branches over few anchors, and a balanced coloring into small classes (Paley colors are nearly discrete). Non-image anchor targets die at color-histogram mismatch; so effective branching is $\le|\mathrm{Aut}|$. Conclusion: HJ on Paley graphs is $n^{O(\kappa)}$ polynomial [SKETCH: the Design/aggregation branch accounting is not carried out; nothing about general conference graphs is claimed].

Reading across §2: **the chain needs partial-automorphism groups that realize $\mathrm{Alt}(T)$ with a deep visible tower**, i.e. local elementary-abelian symmetry. Quasirandom SRGs are not hard for HJ; algebraic ones are.

### 2.9 What this says, and does not say

* Theorem B1 refutes the possibility that HJ's $n^{\log n}$ tightness is confined to string isomorphism. HJ is $n^{\Theta(\log n)}$ on graphs, with the tight channel being $\sigma x$ **[PROVEN, given HJ as written]**.
* This does not separate GI from string isomorphism and gives **no lower bound for GI**: $X_m$ is trivially isomorphism-solvable (it is the fixed geometry $\mathrm{PG}(m-1,2)$; $\mathrm{GL}(m,2)$ is its automorphism group).
* Whether a modified HJ avoids it: **every independent $T$ is a full certificate** on $X_m$, so an automorphism-pruning variant (skip $T$ in the $\langle$known automorphisms$\rangle$-orbit of a processed test) would collapse each level to $O(1)$ tests on $X_m$. **Robust variant [SKETCH]:** switch a single far-away block of $X_m$ (kill $\mathrm{Aut}$); for all chains $(T_0,\dots,T_{J-1})$ whose spans avoid the switched block, the windows only see unperturbed blocks, Lemma 1 applies unchanged (the linear maps $g$ need only preserve windows), so the lower bound persists for a rigid graph where orbit pruning has nothing to use. Gap: the "far-away" count must be checked at the last levels, where spans reach dimension $\sim m/2$ (a fixed block avoids a random such span with probability $1-2^{-\Omega(m)}$, so it should be fine).

---

## 3. Target A

### 3.1 A1: bidirectional collision for quasigroups [PROVEN]

**Theorem A1.** Isomorphism of two quasigroups of order $n$ given by Cayley tables, in deterministic time and space $n^{(1/2)\log_2 n+O(1)}$. Same for Latin-square isotopy, paratopy (and Latin-square graphs of order $k$ above a constant, recovering the net via Bruck's theorem (from memory), in $N^{(1/4)\log_2 N+O(1)}$ for $N=k^2$ vertices), and STS isomorphism (Steiner quasigroup).

*Proof.* (Adapting Rosenbaum 2013, §§2–3, which is stated for groups.) (i) A finite subset closed under the product is a subquasigroup. Proper subquasigroups have order $\le n/2$: for $x\notin S$, $xS\cap S=\emptyset$. So a sequence $x_1,x_2,\dots$ with $x_{i+1}\notin\langle x_1,\dots,x_i\rangle$ has length $\le \log_2 n+1$. (ii) An ordered generating tuple $g$ determines a canonical labelled Cayley table $\Phi_Q(g)$ (close under products in a fixed order) in polynomial time, and $\Phi_Q(g)=\Phi_{Q'}(h)$ iff $g_i\mapsto h_i$ extends to an isomorphism. (iii) Let $d=\lceil\frac12(\log_2 n+1)\rceil$. If $Q$ has a generating set of size $\le d$ (checkable in $n^{d}$), enumerate as in Miller. Otherwise, Alice lists all strictly increasing chains of length $d$ in $Q$ and extends each to a generating tuple arbitrarily; Bob fixes one strictly increasing chain of length $d$ in $Q'$ and lists all its strictly increasing extensions to generating tuples. If $\varphi:Q\to Q'$ is an isomorphism, the preimage of Bob's chain is one of Alice's chains, and $\varphi$ of her extension is one of Bob's. Sorting $\{\Phi_Q(\cdot)\}$ and $\{\Phi_{Q'}(\cdot)\}$ and testing for a collision gives the bound $n^{d}+n^{\log_2n+1-d}$. For isotopy/paratopy: use the three-sorted closure (a closed triple $(R,C,S)$ has $|R|=|C|=|S|$, and a proper one has order $\le n/2$), generators drawn from $\le3n$ elements, $3^{O(\log n)}=n^{O(1)}$. ∎

Novelty: Rosenbaum states groups, rings, GI. We found no source for quasigroups. The extension is immediate; it is included because the "$n^{\log n}$" of the barrier in `docs/moonshot-theory.md` §3.2 is actually $n^{(1/2)\log n}$ deterministically (with large space). Levet's "little improvement" statement concerns $\Theta(\log n)$ in the exponent, and remains true.

The group-specific fourth-root speedup does not transfer: it uses Luks' composition-series algorithm, for which quasigroups have no analogue (§3.4).

### 3.2 A2: DP over the subquasigroup lattice [PROVEN]

**Theorem A2.** Let $\mathcal S(Q),\mathcal S(Q')$ be the sets of subquasigroups, $|\mathcal S|\le M$, with $|\mathrm{Aut}(S)|\le A$ for all $S\in\mathcal S$. Then isomorphism of $Q,Q'$, and computing all isomorphisms, takes $\mathrm{poly}(n,M,A)$.

*Proof.* Enumerate $\mathcal S(Q)$ by repeatedly closing $\langle S,x\rangle$; this finds every subquasigroup (build it by generators) in $\mathrm{poly}(n,M)$. For each pair $(S,S')$, $|S|=|S'|$, in increasing size, compute the list $I(S,S')$ of isomorphisms. If $S=\langle x\rangle$, try $x\mapsto x'$. Otherwise pick a maximal proper $T<S$ and $x\in S\setminus T$, so $S=\langle T,x\rangle$. Every isomorphism $S\to S'$ maps $T$ to a maximal $T'<S'$ and is determined by its restriction $\psi\in I(T,T')$ and $x'=\varphi(x)$: test all $(T',\psi,x')$ by closure. Since $I(S,S')$ is a coset of $\mathrm{Aut}(S)$, $|I|\le A$. ∎

Combined with $r:=d(Q)\le\log_2 M$ (Lemma A3a), Miller gives $n^{\log_2M}$; A2 improves this to polynomial when $A$ and $M$ are polynomial. The bound is in $M$ and $A$, not in rank: e.g. a direct product $Q=Q_1\times\dots\times Q_t$ of pairwise non-isomorphic rigid loops with no proper nontrivial subloops has exactly $2^t$ subloops (Goursat's lemma in the Mal'cev variety of loops, from memory), $A=1$, rank $t$. It is polynomial under A2, while Miller is $n^{t}$; since pairwise non-isomorphic factors must have slowly growing order, $t=o(\log n)$ here, so this separates A2 from Miller only as "polynomial versus superpolynomial $n^{o(\log n)}$" [CONDITIONAL on the existence of such loop families, not checked].

### 3.3 A3: structural lemmas [PROVEN]

* (a) If $x_1,\dots,x_r$ is irredundant, the $2^r$ subsets generate pairwise distinct subquasigroups; so $d(Q)\le\log_2 M$. In particular $M=n^{o(1)}$ implies Miller runs in $n^{o(\log n)}$.
* (b) In any strictly increasing generating chain with $r$ steps, at most $\log_b n$ steps have index $\ge b$; so rank $r\ge2\log_b n$ forces $\ge r/2$ steps of index $<b$. Corollary: if every subquasigroup chain step has index $\ge b$ (hereditary index gap), Miller runs in $n^{\log_b n+O(1)}$, i.e. $n^{o(\log n)}$ for $b=\omega(1)$.
* (c) A subquasigroup of index 2 is normal (block structure $\mathbb Z_2$). So a generation chain with long stretches of index-2 steps is a tower of $\mathbb Z_2$-extensions, each carrying **three arbitrary Latin squares** $T\times T\to S,S\times T\to T,T\times S\to T$ on $|S|$ points: associativity is not forced.

### 3.4 Attempts and where they break

| idea | exact statement needed | where it breaks |
|---|---|---|
| Sharper generator enumeration (lattice DP without A) | Replace the enumeration of $I(T,T')$ by a coset representation $\mathrm{Aut}(T)\psi$; extension test as coset condition | [PROVEN obstruction to the naive route] Extending $\psi\alpha$ ($\alpha\in\mathrm{Aut}(T)$) with $x\mapsto x'$ is a string-isomorphism condition under $\mathrm{Aut}(T)$ on a structure depending on $(x,x')$; for $|\mathrm{Aut}(T)|=n^{\Theta(\log n)}$ this is as hard as the original, and there are $M$ pairs $(T,T')$ and $n$ images $x'$. Solvable $\mathrm{Aut}(T)$ would help via Luks, but only index-2 extensions admit the needed "labelling of $R\setminus S$ by $S$" (see (c)); general minimal extensions need nested words. |
| Bounded-depth / chain enumeration top-down (choose index-2 subsquares first, $\le n$ per level) | $\prod_i|S_i|$ choices of chains $\cdot\prod_i|S_i|$ images of generators | Gives exactly $n^{(1/2)\log n}\cdot n^{(1/2)\log n}$: the same Miller bound; only bidirectional splitting (A1) halves it. |
| HJ-style constant-size local certificates on natural labels | Certificates reduce branching from $n$ to $O(1)$ per doubling | **Refuted for HJ's form by Theorem B1**: on $\mathbb Z_2^m$ the certificate tree itself has $n^{\Omega(\log n)}$ nodes. |
| Sun individualize-then-average | Multiplication behaves linearly over a field after individualizing $\tilde O(\sqrt\ell)$ vectors, so the remaining group action is by linear maps and can be averaged | No linear structure exists in a quasigroup: the only natural linearization is the $n\times n\times n$ Cayley permutation tensor, under monomial (not $\mathrm{GL}$) action; tensor isomorphism under $\mathrm{GL}$ does not preserve Latin squares (we know no precise statement relating $\mathrm{GL}$-isomorphism of the Cayley tensor to isotopy). Sun's averaging has nothing to act on. Applies only to group isotopes: For Latin squares given by tables and isotopic to groups, Albert's theorem reduces isotopy to group isomorphism, so IMQSZ gives $n^{\tilde O(\sqrt{\log n})}$ when the group is a Frattini-class-2 $p$-group [PROVEN by composition of cited results; IMQSZ read only in citing text]. Not for quasigroup isomorphism of isotopes, which adds an arbitrary string constraint under $\mathrm{Iso}(G,G')$. |
| "Hard cases are group-like" (reduce to group progress) | Rank-$\Theta(\log n)$ quasigroups have a large normal section isotopic to a group | **Not established, and (c) suggests false as a general statement**: long index-2 towers carry non-associative data. Evidence the other way: rank-$\Omega(\log n)$ examples we can construct are algebraic (elementary abelian, Hall triple systems / commutative Moufang). Whether every rank-$\Omega(\log n)$ quasigroup is "locally algebraic" is open; this is the sharpest formulation of "non-algebraic hard case" we found. [SPECULATION] |
| Reduction Latin square → group | Polynomial reduction to group isomorphism | None known (Levet shows GI is not AC⁰-reducible to isotopy, which is a separate direction); we did not find one and have no candidate. |

---

## 4. Consequences for the campaign

1. **Moonshot-theory §2.3/§2.4 speculations resolved.** The forcing shape of §2.3 ("visible unaffected steps with polynomial-degree giants") occurs on $X_m$. $\sigma=\Theta(\log N)$ with $q^{\kappa}$ multiplicity is genuinely attained on graphs **[PROVEN, given HJ as written]**.
2. **The dissection exponent $\log N\cdot(\log w+\mu+\log\log N)$ is tight in the $\log w$ factor via $\sigma$**, independently of $\mu$ (on $X_m$, the chain hits giants of degree $\ge\sqrt k$ for the first half of the levels; enumeration is not used).
3. **Barrier statement to record**: any improvement of HJ below $n^{\log n}$ must change the certificate-level recursion at step 4 (or prune/memoize its tests); a "better potential" cannot help, since the calls exist. Lemma J and the §4.1 (H2) grouping of `docs/moonshot-theory.md` are unaffected (they bound, not lower-bound).
4. **Target A leaves the $n^{\Theta(\log n)}$ barrier for general quasigroups, STS and conference graphs intact.** A1 is the "constant in the exponent" analogue of Rosenbaum for quasigroups.

---

## 5. Reproduction

`docs/w18-latin-sim.py` (needs pynauty; run under `nice`):

```sh
PY=../r2-hybrid/.venv/bin/python
nice -n 19 $PY docs/w18-latin-sim.py 0 5 3 2     # PG, level 0, m=5, kappa=3
nice -n 19 $PY docs/w18-latin-sim.py 1 7 3 1     # PG, level 1, m=7, kappa=3 (~4 min)
nice -n 19 $PY docs/w18-latin-sim.py ls 5 3 1    # LS(Z_2^5), level 0
nice -n 19 $PY docs/w18-latin-sim.py stsb 6 3    # STS block graph, level 0
timeout 170 nice -n 19 $PY docs/w18-latin-sim-root.py root 5 3   # root model, stops by timeout in V_2
timeout 60  nice -n 19 $PY docs/w18-latin-sim-root.py root 4 3   # root model, through V_3
```

In `w18-latin-sim.py`, affected status is tested on 1–2 random positions per position-type; the group and image computations are exact. All runs use $\kappa=3$ and $m\le7$, far below $\kappa=64$: they check the window structure of Lemmas 1–2 and cannot check the asymptotic count. The level-0 run at $m=5$ prints $|A|=3.48\cdot10^{115}$ at step 4, against the predicted $6\cdot8^3\cdot3!\cdot76!=3.475\cdot10^{115}$.

## 6. Leads for follow-up

1. Turn §2.7 (LS and block graph) into [PROVEN]: state the level with deleted cells; straightforward but careful.
2. Check the rigid-variant count (§2.9) at the last levels; then a robust $n^{\Omega(\log n)}$ for HJ on rigid graphs, ruling out automorphism pruning.
3. Is every rank-$\Omega(\log n)$ quasigroup "locally algebraic" (every small subset generates a section isotopic to a group or Moufang loop)? A structure theorem here would decide whether Sun-type methods can in principle reach the barrier.
4. Can HJ's certificate step be restricted to test sets chosen by a canonical rule (Design-Lemma-driven) so that each level has $O(1)$ tests? That targets the $\sigma$ channel directly and is the most direct way to beat Theorem B1 without new group theory.

## 7. Ledger

| statement | status |
|---|---|
| Theorem B1 (PG incidence graphs force HJ $\ge n^{(1/8-o(1))\log_2 n}$) | [PROVEN, given HJ as written] |
| Lemma 1 (level step), Lemma 2 (root) | [PROVEN, given HJ as written] (windows also checked exactly at small size) |
| Dispatcher paths (§2.5) | [PROVEN, given HJ as written] |
| Simulation agreement (§2.6) | exact group computation; affected-test sampled; small $m$ only |
| LS($\mathbb Z_2^m$), STS block graph chains | [SKETCH], gaps listed |
| Paley graphs polynomial for HJ | [SKETCH] |
| Rigid robust variant | [SKETCH] |
| Theorem A1 ($n^{(1/2)\log n}$ for quasigroups) | [PROVEN]; extension of Rosenbaum |
| Theorem A2, Lemma A3 | [PROVEN]; not found in literature |
| Attempts §3.4 | negative, break points stated |
| No $n^{o(\log n)}$ for general LS/STS/conference graphs | honest negative |
