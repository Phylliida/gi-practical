# w34-vc: VC dimension, nets and tensor structure for conference graphs

Moonshot follow-up to `docs/w32-conference.md` (Levet's Question 6.5). Branch `w34-vc`, 2026-11-09. Code and data: `docs/w34-code/`. Labels: **[PROVEN]**, **[SKETCH]**, **[CONDITIONAL]**, **[SPECULATION]**, **[DATA]**.

**Bottom line.** Nothing below improves $n^{2\log_2 n}$ for all conference graphs. The VC/$\varepsilon$-net route cannot do it as stated: the separation systems have VC dimension $\Theta(\log n)$, for every conference graph in the one-round case and on iterated Turyn products in the multi-round case. What survives is an exact reduction (Thm 4.1): individualization depth is bounded by $O(\log n/\log(1/\tau))+O(d(\tau))$, where $d(\tau)$ is the VC dimension of the *bad-pair* subsystem at threshold $\tau$. Whether $d(\tau)=o(\log n)$ for some $\tau\to0$ is the open question this memo isolates. It is proved for no non-trivial family.

## 0. Summary

| # | Claim | Status |
|---|---|---|
| A | For every conference graph, $\lfloor\frac12\log_2 n\rfloor-4\le \mathrm{VC}(\mathcal E^1)<2\log_2 n$, where $\mathcal E^1$ is the one-round separation system. The neighbourhood system satisfies the same lower bound. | **[PROVEN]** Thm 2.1 |
| B | On iterated Turyn products $W_L$ over a symmetric base of order $v\ge5$ ($n=v^{2^L}$), the separation system of $k$-tuples after $r$ rounds has VC dimension $\ge 2^L-1=\log_v n-1$, for every $r\in\mathbb N\cup\{\infty\}$ and $k\le v-2$. So no fixed-round or stable-refinement VC bound is $o(\log n)$ for the class. | **[PROVEN]** Thm 3.2, checked at $n=625,6561$ |
| C | Hybrid reduction: depth $\le 2\lceil 3\ln n/\ln(1/\tau)\rceil+88\,d(\tau)+22$ for all $\tau\in(0,1)$. | **[PROVEN]** Thm 4.1 (easy) |
| D | On Turyn iterates $d(\tau)\ge\frac14\log_v(1/\tau)-O(1)$, so C cannot beat $\Theta(\sqrt{\log n})$ on them. | **[PROVEN]** Prop 4.2 |
| E | If $d(\tau)=o(\log n)$ for some $\tau\to 0$ (uniformly over conference graphs), then depth is $o(\log n)$ and isomorphism is in $n^{o(\log n)}$. Stronger: $d(\tau)\le A\log_2(1/\tau)$ gives depth $O(\sqrt{A\log n})$. | **[CONDITIONAL]**; the hypothesis is open, verified only trivially on Paley and on small data |
| F | Product coarsening: $r$-round 1-WL on $W(V_1,V_2)$ is at least as coarse as the product of the factors' partitions. Hence depth$(W)\ge\max$ depth of the factors. The converse (projections discrete $\Rightarrow$ $W$ discrete) is false. | **[PROVEN]** Prop 3.1, Cor 5.1; **[DATA]** |
| G | Exact formula for $T$ on a row pair of $W(V,V')$: $T(a,x,y)=-v f(y_2)-V(y_1,a_1)T'+O(1)$ generically. | **[PROVEN]** Prop 5.2, checked on 7846 triples |
| H | Energy identity $\sum_R b_{QR}^2/|R|=n/|Q|-1$ for equitable partitions; cell bound $|Q|\le n/(k+1)$; for non-square $n$ the cell count is odd and the quotient trace is $0$. No growth lemma follows. | **[PROVEN]** §6 |
| I | Latin square graphs of $\mathbb Z_2^k$ have depth $\Omega(\log n)$ by base size, so the Latin-square analogue of Question 6.5 has a negative answer. No such barrier is known for conference graphs. | **[PROVEN]**, elementary (§7) |

Status of the leads: (1) VC: answered negatively, with the hybrid reduction as the replacement. (2) Grid detection: exact formula only; large-$B_c$-clique $\Rightarrow$ grid is not proved. (3) Growth: no lemma. (4) Turyn: lower bounds and structure, no upper bound on depth. (5) Conditional: E.

## 1. Set systems

$X$ is a conference graph on $n$ vertices, $C=J-I-2A$, $C^2=nI-J$, $C\mathbf1=0$. For $x\ne y$ exactly $(n-3)/2$ vertices $u\notin\{x,y\}$ have $C_u(x)=C_u(y)$, and $(n-1)/2$ have $C_u(x)\neq C_u(y)$.

* **One round:** ground set $V$; $E^1_{xy}=\{u: C_x(u)\ne C_y(u)\}$ (this contains $x$ and $y$), of size $(n+3)/2$.
* **Two rounds on pairs:** ground set $G=\binom V2$. $F_{xy}\subseteq G$ is the set of *collision* tests: $\{a,b\}\cap\{x,y\}=\emptyset$, $C_a(x)=C_a(y)$, $C_b(x)=C_b(y)$, $T(a,b,x)=T(a,b,y)$. Its complement is $E_{xy}$. By w32 Lemma 2.3, a test in $E_{xy}$ whose two vertices are individualized separates $x,y$ within two 1-WL rounds, whatever else is individualized. Set $p_2(x,y)=|F_{xy}|/|G|$.
* **General:** ground set $V^k$; $F^{r,k}_{xy}$ is the set of $k$-tuples after whose individualization $x,y$ have equal colour after $r$ 1-WL rounds ($r=\infty$: stable).

**Prop 1.1 [PROVEN].** $p_2(x,y)\le\frac{(n-3)(n-5)}{4n(n-1)}<\frac14$. Every set $E_{xy}$ has density $>3/4$. (Both test vertices must lie in the agree-set of size $(n-3)/2$.)

$\mathrm{VC}(\mathcal F)=\mathrm{VC}(\mathcal E)$ (complements). All systems have at most $\binom n2$ sets, so VC $\le\log_2\binom n2<2\log_2 n$. This trivial bound is Babai's bound in VC language.

## 2. One round: VC dimension $\Theta(\log n)$ for every conference graph

**Thm 2.1 [PROVEN].** For every conference graph on $n$ vertices there is $D\subseteq V$ with $|D|=d:=\lfloor\frac12\log_2 n\rfloor-4$ such that every sign pattern in $\{\pm1\}^D$ is realized by at least two vertices outside $D$. Consequently $\mathrm{VC}(\mathcal E^1)\ge d$, and the neighbourhood set system also has VC dimension $\ge d$.

*Proof.* Build $D$ greedily. Let $\mathcal P_i$ be the partition of $V\setminus D_i$ by sign pattern on $D_i$, and let $\Psi_i=\sum_{Q\in\mathcal P_i}1/|Q|$. For $x\in V$ and $Q\subseteq V$: $\frac1n\sum_x\langle C_x,\mathbf 1_Q\rangle^2=\frac1n\mathbf 1_Q^T(nI-J)\mathbf 1_Q\le|Q|$. So $\mathbb E_{x\in V}\sum_Q\langle C_x,\mathbf1_Q\rangle^2/|Q|^2\le\Psi_i$, and some $x\notin D_i$ has this sum $\le 2\Psi_i$ (for $i\le n/2$). Add $x$ to $D$. Each cell $Q$ splits into $Q^\pm$ with $|Q^\pm|\ge\frac12(|Q|(1-\sqrt{2\Psi_i})-1)$. Suppose all $2^i$ cells have size $\ge n/2^{i+1}$. Then $\Psi_i\le 2\cdot4^i/n$, so $\sqrt{2\Psi_i}\le 2^{i+1}/\sqrt n$. Writing $t_i=2^i s_i/n$ for the minimum cell size $s_i$, this gives $t_{i+1}\ge t_i(1-2^{i+1}/\sqrt n)-2^i/n$. With $2^d\le\sqrt n/16$, $\sum_{i<d}2^{i+1}/\sqrt n\le 1/8$, so $t_i\ge 1/2$ throughout. Final cells have size $\ge n/2^{d+1}\ge 8\sqrt n\geq 2$. For $Y\subseteq D$ pick $v\ne w\notin D$ with patterns differing exactly on $Y$; then $E^1_{vw}\cap D=Y$. $\square$

The argument only uses $\|C\|\le\sqrt n$. For Paley graphs it recovers the $\frac12\log_2 q$ lower bound of McDonald–Sahay–Wyman (arXiv 2210.03789, via Weil, for the neighbourhood system), from which this is a routine variant. That paper conjectures $(1+o(1))\log_2 q$ for the Paley neighbourhood system. I did not find this for general conference graphs.

**[DATA]** exact $\mathrm{VC}(\mathcal E^1)$ (`vctool.c vc1`): Paley $q=13,17,25,29,37$: $4,5,6,6,7$; $q=41,53,61,73$: $\ge8,8,9,9$ (capped); Spence $n=25$ samples and Turyn $n=25$: all $6$.

So the one-round system never has $o(\log n)$ VC dimension. This is also forced by counting: a one-round distinguishing set needs $\ge\log_2 n$ vertices. Multi-round refinement must be used.

## 3. Iterated refinement: Turyn products are extremal

$W(V_1,V_2)=V_1\otimes V_2+I\otimes J-J\otimes I$ (equal orders; symmetric conference matrices if the $V_i$ are symmetric conference-type). $W_0=V$, $W_{L+1}=W(W_L,W_L)$, coordinates in $[v]^m$, $m=2^L$.

**Prop 3.1 (product coarsening) [PROVEN].** Let $S\subseteq V_1\times V_2$ with projections $S_i$, and let $P^r(\cdot)$ be the partition after $r$ 1-WL rounds with individualized vertices ($r=\infty$: stable). Each cell of $P^r(V_1,S_1)\times P^r(V_2,S_2)$ lies in one cell of $P^r(W,S)$. Iterating, the analogous statement holds for $W_L$ with $m$ coordinates.

*Proof.* Induction on $r$. At $r=0$: a product cell is either a single $S$ vertex or disjoint from $S$. Step: for product cells $Q_1\times Q_2$, $\sum_{y\in Q_1\times Q_2}W(x,y)=(\sum_{Q_1}V_1(x_1,\cdot))(\sum_{Q_2}V_2(x_2,\cdot))+[x_1\in Q_1]|Q_2|-|Q_1|[x_2\in Q_2]$. This depends only on the cells and counts of $x_i$ in the factors. Hence equal round-$(r+1)$ factor data give equal counts into every product cell, and a fortiori into every cell of $P^r(W,S)$, which is a union of product cells. $\square$

**Thm 3.2 [PROVEN].** Let $W_L$ be built on a symmetric conference-type $V$ of order $v\ge5$, $n=v^{m}$, $m=2^L$. For every $r\in\mathbb N\cup\{\infty\}$ and $k\le v-2$ (tuples with pairwise distinct entries),
$$\mathrm{VC}(\mathcal F^{r,k}(W_L))\ge m-1=\log_v n-1.$$
For $k>v-2$ the same holds with $m-1-\lceil\log_{v-1}k\rceil$. In particular the two-round $T$-system has VC dimension $\Omega(\log n)$, even though these graphs have exact depth $3$ at every level tested (w32 §6).

*Proof.* Fix $s\ne t$; choose $\alpha\notin\{s,t\}$ with $V(\alpha,s)=V(\alpha,t)$ and $\alpha'_1\notin\{s,t\}$ with $V(\alpha'_1,s)\ne V(\alpha'_1,t)$. These exist because $v\ge5$. Choose distinct $\alpha'_2,\dots,\alpha'_k\notin\{s,t\}$. For $i\in[m-1]$, the tuple $a^i\in V^k$ has $\rho$-th entry equal to $\alpha$ at every coordinate $j\ne i$ and $\alpha'_\rho$ at coordinate $i$. For $Y\subseteq[m-1]$: $x^Y,y^Y$ agree, equal to $s$, on coordinates in $Y$, and are $(s,t)$ on coordinates in $[m]\setminus Y$ (coordinate $m$ is always a witness, so $x^Y\ne y^Y$).

If $i\in Y$: at coordinate $j\ne i$ the projected tuple is $(\alpha,\dots,\alpha)$, one individualized vertex, whose stable partition puts $s,t$ together; at coordinate $i$, $x_i=y_i$. By Prop 3.1, $x,y$ get the same colour for all $r$.

If $i\notin Y$, take the entry $a=a^{i,1}$. Since $a_j\ne x_j,y_j$ at all coordinates, $W_L(a,x)W_L(a,y)=\prod_j V(a_j,x_j)V(a_j,y_j)=-1$, so $x,y$ are separated in round $1$.

Hence $D=\{a^i\}$ is shattered by $(x^Y,y^Y)$. For large $k$ reserve spare coordinates, where $x_j=y_j$, to make entries distinct. $\square$

The base needs no collision pair: this works for $P(5)$. Measured at $L=2$: base $P(9)$, $n=6561$, $d=3$, all $8$ subsets with $T$-tests; base $P(5)$, $n=625$, $d=3$, $r=2$ and $r=\infty$ (`turyn_shatter.py`, `grid_detect.py`). Also $L=1$ at $n=81,169$.

**Lemma 3.3 (collision lifting) [PROVEN].** Let $W=W(V_1,V_2)$ with $V_i$ symmetric, and suppose $a_i,b_i,x_i$ and $a_i,b_i,y_i$ are distinct triples in each factor. If in each factor either $x_i=y_i$ or $(a_i,b_i;x_i,y_i)$ is a collision (equal signs and equal $T$), then $(a,b;x,y)$ is a collision in $W$. Moreover, if in exactly one factor the signs of $a_i$ on $x_i,y_i$ differ, and in the other they agree, then $W(a,x)
eq W(a,y)$. *Proof.* w32 Lemma 4.1 gives $T^W(a,b,x)=T_1(x_1)T_2(x_2)+R$ with $R$ a function of signs only; the products are equal and the signs agree, so $R$ agrees. For the sign claim use $W(a,x)=V_1(a_1,x_1)V_2(a_2,x_2)$ at generic triples. $\square$

**Answer to the VC question.** VC dimension $o(\log n)$ is false: for one round on every conference graph, and for every fixed $(r,k)$ on iterated Turyn products. The extremal structure is the tensor coordinates: a shattered test per coordinate. Thm 3.2 uses tests of tiny measure, so it obstructs VC as a proof technique, not hitting sets of small size: Turyn graphs do have small distinguishing sets, by exact computation. The gap $\mathrm{depth}\ll\mathrm{VC}$ on Turyn is exactly the looseness of the ε-net theorem in this setting.

## 4. What replaces VC: the bad-pair subsystem

For $\tau\in(0,1)$ let $B(\tau)=\{xy:p_2(x,y)\ge\tau\}$, and let $d(\tau)=\mathrm{VC}(\{E_{xy}:xy\in B(\tau)\})$ (ground set $\binom V2$; $d(\tau)=0$ if $B(\tau)=\emptyset$).

**Thm 4.1 (hybrid net/union bound) [PROVEN].** For every conference graph and $\tau\in(0,1)$,
$$\mathrm{depth}(X)\le 2\Bigl\lceil\frac{3\ln n}{\ln(1/\tau)}\Bigr\rceil+88\,d(\tau)+22,$$
with discreteness after two 1-WL rounds.

*Proof.* Pairs outside $B(\tau)$: $T=\lceil 3\ln n/\ln(1/\tau)\rceil$ uniformly random tests fail on a fixed such pair with probability $<\tau^T\le n^{-3}$; union over $<n^2/2$ pairs. Pairs in $B(\tau)$: by Prop 1.1 every range $E_{xy}$ has density $\ge3/4$, so by the $\varepsilon$-net theorem (Blumer–Ehrenfeucht–Haussler–Warmuth 1989; Haussler–Welzl) a random sample of $\max(11,44d(\tau))$ tests hits all of them. Each test contributes two vertices; separation is by w32 Lemma 2.3. $\square$

Trivial as a statement, but it is the right form of the union-bound/VC split: VC is needed only on pairs that are bad. It is a corollary, not a new tool. Note $d(\tau)\le\log_2|B(\tau)|$.

**Consequence.** (E1) If some $\tau=\tau(n)\to0$ has $d(\tau)=o(\log n)$ uniformly over conference graphs, then depth is $o(\log n)$ and isomorphism is in $n^{o(\log n)}$. (E2) If $d(\tau)\le A\log_2(1/\tau)$ for $\tau\in[n^{-1},1/5]$, then depth is $O(\sqrt{A\log n})$. **[CONDITIONAL]** on those hypotheses. Paley ($q$ prime): $B(\tau)=\emptyset$ for $\tau>q^{-\delta}$ by w32 Thm 5.1 **[SKETCH]**, so the hypothesis holds trivially.

**Prop 4.2 (the hypothesis cannot be improved on Turyn) [PROVEN].** Let $V$ be a symmetric conference-type matrix with a collision configuration (a test and a pair as in w32 Thm 4.2; e.g. $P(9)$), of order $v$, and $L\ge\ell\ge1$. Let $r=2^\ell-1$. Then on $W_L$, $d(\tau)\ge r$ whenever $\tau\le 2C_0v^{-2^{\ell+1}}$, where $C_0=\prod_{i\ge0}(1-v_i^{-1})(1-2v_i^{-1})>0$ and $v_i=v^{2^i}$. Equivalently, $d(\tau)\ge\frac14\log_v(1/\tau)-O(1)$.

*Proof.* Let $B=W_\ell$, of order $v^{r+1}$. Apply Thm 3.2 to $B$ with $k=2$, $r=2$, taking $(s,t)$ from the collision configuration: a shattered set $D$ of size $r$ in $\binom{B}{2}$, shattering pairs $(x^Y,y^Y)$ in $B$. Each such pair has $P_B(x^Y,y^Y)\ge\binom{|B|}{2}^{-1}$, using a collision test built from the configuration at the differing coordinates (w32 Lemma 4.1 and Lemma 3.3 and the base collision configuration, applied at every base coordinate). Lift to $W_L=W_{L-\ell}(B)$ by w32 Thm 4.2 applied in one $B$-coordinate: the pair lifts with collision probability $\ge C_0 P_B$. The shattering lifts by the same collision-lifting (the non-collisions in Thm 3.2 are sign mismatches at one coordinate, which lift). $\square$

So on Turyn iterates the best Thm 4.1 can give is $\Theta(\sqrt{\log n})$ (optimize $\log n/\log(1/\tau)+\log(1/\tau)$). If $d(\tau)$ were close to its lower bound, this would still be $o(\log n)$. **Open:** an upper bound on $d(\tau)$ on Turyn iterates. Reason it is hard: for pairs differing on $J$, $T^W(x)-T^W(y)$ involves $\prod_{j\in J}T_j(x_j)-\prod_{j\in J}T_j(y_j)$, where coincidences occur among products, and tests have coordinate coincidences at small levels. The likely-true statement ($p_2$ decays with $|J|$ only polynomially, Littlewood–Offord-type) is unproved **[SPECULATION]**.

**A false hope (for the record).** Stronger hypothesis: $\sum_{y'\in Q}p_2(y,y')\le|Q|^{1-\delta}$ for all $Q\ni y$, $|Q|\ge$ polylog. It would imply, by a per-vertex Markov argument, depth $O(\log n/(\delta\log\log n))$ to reach polylog cells, then bounded-color-class isomorphism **[SKETCH]**. It is **false on Turyn iterates**: for $Q$ a Hamming ball of radius $\rho$, $\sum_{y'}p_2\approx|Q|c^{\rho}$, and $c^\rho\ge|Q|^{-\delta}$ once $m$ is large. So any useful condition has to admit the tensor structure.

## 5. Turyn structure

**Cor 5.1 [PROVEN].** depth$(W(V_1,V_2))\ge\max(\text{depth}(V_1),\text{depth}(V_2))$; a set discrete on $W$ projects to sets discrete on the factors (Prop 3.1). So depth is non-decreasing up the tower.

The converse fails **[DATA]**: base $P(5)$ at $k=2$: 181 tuples have discrete projections, none is $W$-discrete; at $k=3$: 253 projection-discrete, 230 $W$-discrete. Base $P(9)$: no $k=2$; at $k=3$ all 44 projection-discrete tuples are discrete. So a depth recursion cannot be coordinatewise in general.

**Prop 5.2 (row-pair formula) [PROVEN].** Let $V,V'$ be symmetric of order $v$, $W=W(V,V')$. For $a=(a_1,a_2)$, $x=(a_1,x_2)$ with $a_2\ne x_2$, set $\varepsilon=V'(a_2,x_2)$, $f(z)=V'(a_2,z)V'(x_2,z)$, $T'=T^{V'}(a_2,x_2,y_2)$, $I'=v-1$ if $y_1=a_1$ and $-1$ otherwise. Then $T(a,x,y)=A+B+C$ with
$$A=-1-vf(y_2),$$
$$B=V(y_1,a_1)\bigl(-V'(y_2,a_2)-V'(y_2,x_2)-T'\bigr)+[y_1=a_1](v-1)-\bigl(1-f(y_2)\bigr)[y_2\notin\{a_2,x_2\}],$$
$$C=-\varepsilon\bigl(I'(V'(y_2,a_2)+V'(y_2,x_2))+2V(a_1,y_1)\bigr).$$
For generic $y$ ($y_1\ne a_1$, $y_2\notin\{a_2,x_2\}$), $T=-vf(y_2)-V(y_1,a_1)T'+O(1)$, i.e. $|T|\ge v-|T'|-O(1)$. Direct expansion of $W=V\otimes V'+I\otimes J-J\otimes I$; checked on 7846 random triples, bases $P(9)$ and $P(13)$, 0 mismatches.

So for $y$ outside the row, $T(a,x,\cdot)$ on a row pair is "almost $\pm v$", a bent-like signal. The T-profile separates row/column pairs from other pairs on one-level products, in the tested cases only **[DATA]** ($P(9)$, $P(13)$ bases: distinct $T$ values 7 vs 10, 11 vs 14). This is the mechanism behind w32's "2-WL sees rows after one vertex". Iterated products break the simple statement, since pairs in rows of both factors also get $|T|\approx v$.

**Cliques and grids.** Rows and columns are Delsarte cocliques/cliques (size $\sqrt n$, the Delsarte bound), each outside vertex with fixed counts. So Turyn products are conference graphs with an orthogonal pair of Delsarte spreads. **[SPECULATION]** the class of "grid" conference graphs is larger than tensor products (blocks $M^{ii'}$ with constant row/column sums, analogous to Bush-type Hadamard matrices), and tensor recursion would not extend to it. Conversion of a large $B_c$-clique into a grid is not proved, and I do not have a route. Non-square $n$ excludes Turyn products and Delsarte cliques, which singles out non-square orders as the natural place to look for $\tau\to 0$ anti-concentration; no result. Note $P(q^2)$ has Delsarte lines but is not a tensor product in this sense, and $n$ non-square does not imply anything proved here.

## 6. Growth of the stable algebra

**Prop 6.1 (energy identity) [PROVEN].** If $\mathcal P$ is an equitable partition with $b_{QR}=\sum_{z\in R}C_x(z)$ ($x\in Q$), then for each cell $Q$: $\sum_R b_{QR}^2/|R|=n/|Q|-1$.

*Proof.* $\|C\mathbf 1_Q\|^2=\sum_R|R|b_{RQ}^2$, with $|R|b_{RQ}=|Q|b_{QR}$; also $\|C\mathbf1_Q\|^2=n|Q|-|Q|^2$. $\square$

**Cor 6.2 [PROVEN].** (i) If $\mathcal P$ has $k$ singleton cells outside $Q$, then $|Q|\le n/(k+1)$ (the singletons contribute $1$ each). (ii) If $n$ is not a square, $B=(b_{QR})$ has eigenvalues $0$ and $\pm\sqrt n$ with equal multiplicities, so the number of cells is odd and $\sum_Qb_{QQ}=0$. Checked on Paley and Spence partitions, 0 failures (`identities.py`).

Summed over cells the identity is equivalent to monotonicity of cell counts, and each term is tight: it encodes $C^2=nI-J$ on the quotient and is consistent with no growth at all. There can be no unconditional per-round growth statement: one individualization is stable with 3 cells; with $k=2$ on Turyn the stable partition equals the orbit partition of the pair stabilizer in w32's data. **Status: no growth lemma.** The obstacle is the same as w32 §4.5: nothing forces a fake equitable partition to be coarse only for symmetry reasons.

## 7. Related classes

**Latin square graphs.** For the Cayley table of $\mathbb Z_2^k$ ($n=4^k$), the autotopism group contains $\mathrm{AGL}$-type maps, $|\mathrm{Aut}|\ge 2^{k^2}$ (up to lower order). Base size is at least $\log_n|\mathrm{Aut}|=\Omega(\log n)$, so depth is $\Omega(\log n)$ **[PROVEN, elementary]**. So the analogue of Levet's question has a negative answer for Latin squares (Miller's $\log n$ is tight on this family, for individualization, not for isomorphism: w18 covers the algorithmic side). Conference graphs differ: motion $\ge (n+3)/2$ excludes the $\mathbb F_2$-transvection behaviour, and I know of no conference graph with base $\ge4$. No general bound on $|\mathrm{Aut}|$ beyond the motion argument was found. (Babai 2014's minimal-degree bound $n/8$ for SRG concerns a different question, cited via arXiv 1802.06959.)

**General SRG.** As I recall them (from w32's reading and citing text; the FOCS 2013 PDF was not re-read here), Spielman and BCSTW use a distinguishing-number union bound ($D(x,y)$ large $\Rightarrow$ one-round separation) plus Neumaier/Metsch clique-geometry casework. In VC language this is one-round, $\varepsilon\sim k/n$. They do not use set-system bounds beyond that, and for $k\sim n/2$ the clique-geometry case does not apply. Latin square graphs are the clique-geometric extreme; Turyn is the conference analogue, but with Delsarte spreads instead of a full net.

## 8. Experiments and their limits

All single-process under `nice`, minutes. Code: `docs/w34-code/` (`vctool.c`, `collide.c`, `build.py`, `turyn_shatter.py`, `turyn_structure.py`, `grid_detect.py`, `identities.py`); outputs in `results/`.

* Two-round VC, exact where not marked (`vc2`): Paley $q=13,17,25,29,37$: $2,3,3,4,4$. $q=41$: $\ge4$. Spence $n=25$ (4 graphs): $4$. Spence $n=29$ (2 graphs): $4$. Turyn $n=25$: $3$. Turyn base order-3 level 2 ($n=81$): $\ge5$ (cap 25 s per threshold).
* $d(\tau)$: at $n\le81$ typical $p_2$ is $0.05$--$0.15$, so the thresholds that matter asymptotically are not reachable; the table is in `results/`.
* $p_2$ versus number $r$ of differing coordinates at $n=6561$, base $P(9)$, $m=4$: means $0.147,0.054,0.022,0.019$ for $r=1,\dots,4$ (500 tests per pair, 40 pairs per $r$). Base order 3, $m=8$: $0.149,0.060,0.035,0.023,\dots,0.02$. Too few coordinates to tell exponential from polynomial decay.
* Limits: the data cannot test Conjecture E; the interesting regime is $n\gg10^4$ and no random-like conference graphs are known there.

## 9. What remains

1. An upper bound on $d(\tau)$ for Turyn iterates; if $d(\tau)=O(\log(1/\tau)\,\mathrm{polylog}\log n)$ this gives depth $o(\log n)$ on that family via Thm 4.1 **[SPECULATION]**.
2. Any non-trivial general bound on $d(\tau)$ or $|B(\tau)|$; none is available. A bound on the number of near-twin pairs would be the first step. Nothing like it is proved.
3. Inverse theorem from a large $B(\tau)$-clique to Delsarte/grid structure (w32 Attempt 2); not attempted beyond §5.
4. Whether non-square orders satisfy strong anti-concentration.

## 10. Novelty check (2026-11-09)

Web searches: VC dimension of Paley/SRG neighbourhoods; individualization/distinguishing sets with VC or $\varepsilon$-nets; Turyn/Delsarte/spread/Bush for conference graphs; conference graph automorphism bounds. Found McDonald–Sahay–Wyman (Paley neighbourhood VC, $\frac12\log_2q$ lower bound, conjecture $(1+o(1))\log_2 q$) and Dahan–Grohe–Neuen–Novotný arXiv 2604.12584 (VC bounds for robust GI, not exact conference-graph questions). I found no statement of Thm 3.2, Prop 4.2, Prop 5.2 or Thm 4.1, but these are short, the search was limited, and the Levet, Spielman and BCSTW bounds come from w32's reading. Treat as likely folklore-adjacent.

## References

Levet arXiv 2207.05930. Babai 1980. Spielman 1996. BCSTW FOCS 2013. Haussler–Welzl 1987; Blumer–Ehrenfeucht–Haussler–Warmuth JACM 1989. McDonald–Sahay–Wyman arXiv 2210.03789. Dahan–Grohe–Neuen–Novotný arXiv 2604.12584. Mathon 1978; w32-conference.md (Lemma 2.3, 4.1, Thm 4.2, 5.1), w18-latin.md.
