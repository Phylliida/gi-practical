# w1-structure: the enumeration channel of Theorem R\*

Branch `w1-structure`, 2026-11-04. Wave 1 of the overnight campaign (`overnight-log.md`).

The task was to attack the second $n^{\log d}$ channel of Theorem R\*: the enumeration of
non-Cameron primitive quotients $P$ with $|P|\le d'^{\,c_1\log d+c_2}$ (GNS Thm 3.13, option 1).
Concretely:

1. classify which primitive $\hat\Gamma_d$ groups reach $d'^{\Theta(\log d)}$;
2. replace enumeration by structure;
3. work out the consequences;
4. check the literature.

**Labels.**
* **[PROVEN]**: a complete argument is given here, relying only on the cited published results.
* **[SKETCH]**: the argument is given, with its gaps listed.
* **[CONDITIONAL: …]**: proven or sketched under the named hypothesis.
* **[SPECULATION]**: an opinion or a conjecture.

(H0) is the standing assumption "HJ (arXiv:2611.01399) is correct as written". VR is
`verify-theorem-R.md`, RT is `redteam-theorem-R.md`, MT is `moonshot-theory.md`, and FPT is
`w1-fpt.md` (branch `w1-fpt`, commit 4eb2ccc), which was written in parallel and overlaps §4.5.
"L…" is a line of HJ's LaTeX source and "G…" a line of GNS's source (arXiv:1802.04659v3).

**Sources read for this memo.** Each was downloaded into its own new directory under
`scratchpad/r4-sources/w1s-*` and only read; no code from them was run.
* Schweitzer–Wiebking, *A unifying method for the design of algorithms canonizing combinatorial
  objects*, arXiv:1806.07466 (STOC 2019); "S-W" below. Read: Theorem `theo:obj`, Lemmas
  `canSetHyper`, `canMatch` and `canInt`, the transitive-case macro, and the runtime proofs.
* Wiebking, arXiv:1904.10454 (SODA 2020), introduction and technique.
* arXiv:2504.19777 (Fitting-free group isomorphism in AC³). It restates Babai–Codenotti–Qiao
  ICALP 2012 Thm 5 = Codenotti thesis Thm 4.2.1 (twisted code equivalence) with its proof.
* arXiv:2604.13953, introduction.

Also re-read: GNS §2–3 (G440–945), Neuen arXiv:2002.06997 introduction, HJ L1140–1180,
L1416–1540, L1760–1775 and L3055–3087, and FPT.

Luks, *Hypergraph isomorphism and structural equivalence of Boolean functions* (STOC 1999) could
not be obtained: it is ACM only and is not on Luks's page. Its content is used here only as
described by S-W ("in a dynamic programming fashion, he computed the isomorphisms by intersecting
cosets of isomorphisms between already computed subhypergraphs"), by Neuen 2020, and by Luks's
2000 Oregon talk abstract.

No Lean and no solver code was run. One 30-line log-gamma script was run to produce the
numbers in Table 2.3; it took about a millisecond.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Which non-Cameron primitive $P\in\hat\Gamma_d$ reach $d'^{\omega(1)}$? | Write $\mu(P)=\log\lvert P\rvert/\log d'$. Outside GNS structural option 2: $\mu(P)\le C\,(1+\lambda(P)+\min\{\log d,\log\log d'\})$. Here $\lambda(P)\le\log_2d+O(1)$ is the largest dimension of the natural module of a classical composition factor. There are two mechanisms. **(α) alternating / top-group driven:** a section $S_k$ with $k=O(\log d')$ acting on $2^{\Theta(k)}$ points. Examples: heart modules $\mathbb F_2^{m-1}{\rtimes}S_m$, monomial groups, Johnson groups with $t\approx m/2$, bisections, $S_5\wr S_k$ in product action, diagonal $A_5^k.(2\times S_k)$. These reach $\Theta(\log d)$ **only** when $d'\ge2^{d^{\Omega(1)}}$. **(β) Lie-rank driven:** $\mathrm{AGL}(r,2)$, $\mathrm{PGL}(r,2)$ on points, $\mathrm{ASL}(r,q)$ and their products, with $\mu\approx r+1\approx\log_2(d+1)+1$ already at $d'\approx d$. | **[SKETCH]** bound (§2.2); **[PROVEN]** examples (§2.3) |
| 2 | Is channel 2 the bottleneck? | Only through its Lie part. The (α) part of enumeration, and the top-group part of product refinement (a third $\log d$ channel), each cost $\le C\min(\log w,\log\log N)$ per unit of $\log N$, where $w$ is the alternating width. So they never exceed the giant channel. **Theorem R\*\*:** for groups whose alternating factors have degree $\le w$ and whose classical factors have dimension $\le\lambda$, HJ+(M′) runs in $\exp(O(\log N\cdot(\log w+\lambda+1)))$. This is a BCP-type class, which GNS 3.13 does not cover (GNS Rem. 3.14). | **[CONDITIONAL: (H0)]** + §2.2 sketch (§3) |
| 3 | "Recurse on $H$" instead of enumerating $V\rtimes H$? | **The trap is real, twice.** Heart: the point stabiliser $S_m$ has Johnson orbits with $t$ up to $m/2$, and (M′) enumerates those at cost $m!$. $\mathrm{AGL}(r,2)$: recursing gives $\mathrm{PSL}(r,2)$ on points, i.e. $d'^{\Theta(\log d')}$ again. HJ's potential also cannot pay the $d'$-fold individualisation (children shrink by only $\sqrt m$), and HJ's own budget for a $t=\Theta(m)$ Johnson level is $\Theta(\log m!)$, no better than enumerating. | **[PROVEN]** (§4.2–4.4) |
| 4 | Structure that does work | **Simply exponential canonisation** (Luks 1999 → Arvind–Das–Köbler–Toda → Babai–Codenotti–Qiao → Schweitzer–Wiebking) plus a new ingredient: **equivariant orbit-objects for the local solvable part**. **Theorem L:** for *level-synchronised towers* $G=(R_1\wr\cdots\wr R_L)\cdot S$ with small local groups $R_j$ and coordinatewise $S$, string isomorphism takes $2^{O(k)}N^{O(1)}$, where $k$ is the orbit size of $S$ on a small ground set. This covers $\mathrm{AGL}(r,2)$-towers in $2^{O(d)}N^{O(1)}$, on which HJ+(M′) needs $\ge N^{\log_2(d+1)+1-o(1)}$ branches. Example $G_{r,L}$ has **unbounded non-abelian entanglement** and **no faithful action with orbits $<N/(dL)$**, yet it is FPT. So the "hard family" criterion of FPT §0 is not sufficient. | **[PROVEN mod S-W Thm `theo:obj`]** (§4.5–4.6) |
| 5 | Does it compose inside HJ's Λ-potential? | **Partly.** A node whose kernel is a full product of its block restrictions becomes $\le4d'^2$ block-size children plus one terminal "twisted" $P$-level instance. The children are paid with $\Lambda=O(1)$. Theorem L and S-W are *canonisation* algorithms and do not plug into HJ, which is isomorphism-only. That integration is the main gap. | **[PROVEN]** row (§4.7); gap (§4.8) |
| 6 | Finer parameter; $d=O(\log n)$ | With the alternating part of channel 2 removed, what remains is $\log N\cdot(g(w)+\lambda)$, where $g$ is whatever the giant channel costs. **For GI of degree $d$ this is still $\Theta(\log d)$** because $\lambda$ can be $\log_2d$. $d=O(\log n)$: R\* gives $n^{O(\log\log n)}$. All decoupled, product and level-synchronised families are polynomial there ($2^{O(d)}N^{O(1)}$). The general coupled case is open. | §5 |

**Verdict.**
* *Classification.* The enumeration channel splits cleanly. Its alternating-driven half is
  never worse than the giant channel. It can be removed by simply exponential (Luks-1999-type)
  methods wherever the coupling between blocks is decoupled or level-synchronised. Its Lie-rank
  half is the real independent source of $n^{\log d}$.
* *The Lie half is not intrinsic on any family I could build.* Product towers,
  level-synchronised affine towers and full wreath towers are all $f(d)\cdot\mathrm{poly}(N)$.
  On the first two, HJ+(M′) provably pays $N^{\log_2(d+1)+1-o(1)}$.
* *What remains.* The obstruction is reduced to **non-laminar coupling of non-abelian sections
  across blocks**, together with the integration of canonisation into HJ. I could not construct
  a convincing hard instance for the former (§4.8). Nothing here removes $\log d$ from R\* for
  general degree-$d$ graphs.

---

## 1. The channel, exactly

R\*'s potential is $\Phi_\Lambda=A(\Lambda x+\Lambda\rho+\Lambda\sigma+Q_d)+Bh$ with
$\Lambda=\log(8\tilde d)$ (VR §4.2, RT §1.3). Four rows of the table need $\Lambda\gtrsim\log d$:

| row | multiplicity | why it needs $\log d$ |
|---|---|---|
| (E1) enumeration, GNS option 1 | $\lvert P\rvert\le d'^{\,c_1\log d+c_2}$ | the exponent itself |
| (E2) enumeration, option 2 with $m\le q_0$ | $(q_0!)^k\lvert K\rvert$ with $\lvert K\rvert\le\tilde d^{\,k-1}$ | top group $K\le S_k$ |
| (PR) product refinement, $k\ge2$, $m>q_0$ | $2^k\lvert K\rvert\le2^k\tilde d^{\,k-1}$ | top group $K\le S_k$ (BCP) |
| giant rows (affected, unaffected, caps) | $q^{O(\kappa)}$, $q\le\mathrm{aw}$ | $\log q$ (channel 1, not studied here) |

Channel 2 consists of (E1) and (E2). Row (PR) is a **third** $\log d$ source of the same top-group
nature, so I treat it together with channel 2 and call it channel 2′. All three come from bounding
$\log\lvert P\rvert$ or $\log\lvert K\rvert$ by $\log d$ per unit of $\log d'$ or of $k$.

---

## 2. Classification

### 2.1 Notation

For a primitive $P$ of degree $d'$ put $\mu(P)=\log\lvert P\rvert/\log d'$, so enumeration costs
$d'^{\mu}$.

* $\lambda(P)$ is the largest $r$ such that $P$ has a composition factor that is a classical group
  with natural module of dimension $r$; it is 0 if there is none.
* $w(P)$ is the largest $m$ with $A_m$ a composition factor; it is 0 if there is none.
* By Cooperstein / Kleidman–Liebeck (GNS Lemma 3.8, G657–667), a classical group of dimension
  $r$ over $\mathbb F_q$ has minimal degree $\ge c\,q^{r-1}$ (for unitary groups $q^{2r-3}$), so
  $\lambda(P)\le\log_2d+O(1)$ for $P\in\hat\Gamma_d$.
* Exception: $\mathrm{GL}(4,2)\cong A_8$, so $\mathrm{AGL}(4,2)\in\hat\Gamma_8$.

### 2.2 The bound

**Proposition 2.1.** **[SKETCH]** There is an absolute $C$ with the following property. Let
$P\le\mathrm{Sym}(d')$ be primitive with alternating factors of degree $\le w$ ($w\ge6$) and
classical factors of dimension $\le\lambda$. Suppose $P$ is not of structural option 2 (socle
$(A_m^{(t)})^k$ in product action with $m>4\log_2\binom mt$, RT §9(b)). Then
$$\mu(P)\ \le\ C\bigl(1+\lambda+\min\{\log w,\ \log\log d'\}\bigr).$$
In particular, for $P\in\hat\Gamma_d$: $\mu(P)\le C(1+\lambda(P)+\min\{\log d,\log\log d'\})$.

*Proof sketch, by O'Nan–Scott type, following GNS §3.* The top-group bound used throughout is
BCP: a $K\le S_k$ without alternating factors of degree $>w$ has $\lvert K\rvert\le w^{k-1}$
(GNS Lemma 2.2; Maróti Cor. 1.5; RT §6). Its hypothesis concerns **alternating factors only**.
Trivially also $\lvert K\rvert\le k!$.

* **Type I, $H=P_0\le\mathrm{GL}(V)$ primitive linear.** By Liebeck–Shalev 2014 as used in GNS
  Thm 3.7 (G632–655), $b(H)\le c$, or $b\le c_2r+c_3$ with $\mathrm{Cl}_r\trianglelefteq H$ ($r\le\lambda$),
  or $b\le c_2\log m+c_3$ with $A_m\trianglelefteq H$. In the last case $A_m$ acts faithfully on $V$,
  so $\dim V\ge m-2$ and $\log m\le\log\log d'+O(1)$; also $m\le w$. Then use
  $\lvert P\rvert\le d'^{\,b(H)+1}$.
* **Type I, $H$ imprimitive linear.** $V=W^\ell$ and $H\le H_0\wr K$ with $H_0$ primitive linear
  on $W$ (as in GNS Thm 3.9, G696–710). Then
  $\lvert P\rvert\le d'\cdot\lvert W\rvert^{\ell\,b(H_0)}\cdot\lvert K\rvert$, with
  $\log\lvert K\rvert\le\min\{(\ell-1)\log w,\ \ell\log\ell\}$ and $\ell\le\log_2d'$. So
  $\mu\le1+b(H_0)+\min\{\log w,\log\log d'\}$.
* **Type II.** Use Liebeck's theorem (GNS Thm 3.10, G711–730) together with $\lvert\mathrm{Out}\,T\rvert=O(\log\lvert T\rvert)$.
  * Either $\lvert P\rvert\le d'^9$;
  * or Johnson $A_m^{(t)}$ outside option 2, which forces $m\le4\log_2d'$, so
    $\mu\le\log m!/\log d'=O(\log m)$ with $\log m\le\log\log d'+2$;
  * or $A_m$ on partitions, with $d'=2^{\Omega(m)}$ (GNS G758–762) and the same conclusion;
  * or a classical group of dimension $r$ on subspaces, with $\lvert T\rvert\le q^{r^2}$ and
    $d'\ge q^{r-1}$, so $\mu\le2r+O(1)$.
* **Type III (diagonal).** $d'=\lvert T\rvert^{k-1}$ and
  $\lvert P\rvert\le\lvert T\rvert^k\lvert\mathrm{Out}\,T\rvert\lvert K\rvert$. So
  $\mu\le2+O(1)+\min\{\log w,\log k\}/\log60$, with $k\le1+\log_{60}d'$.
* **Type IV (product).** $P\le Q\wr K$ with $Q$ of type II or III and degree $m'\ge5$. Then
  $\mu(P)\le\mu(Q)+\min\{\log w,\log k\}/\log m'$, with $k\le\log_5d'$. A component $Q$ with
  Johnson socle is either outside option 2 (handled above) or makes $P$ structural option 2.
* **Type V (twisted wreath).** $\lvert P\rvert=d'\lvert K\rvert$ and $d'=\lvert T\rvert^k$, so
  $\mu\le1+\min\{\log w,\log k\}/\log60$.

*Gaps.* The Liebeck–Shalev, Liebeck and GSS-type inputs are taken as stated in GNS [TRUST]. I did
not re-derive the imprimitive-linear base bound for the BCP class. GNS state it for $\hat\Gamma_d$
via GSS98 Lemma 4.2(a), and I assume its $\log d$ comes from the top group only, i.e. that it is
an alternating-only bound. ∎

**Proposition 2.2 (large degree means coordinate type).** **[SKETCH]** Let $P\in\hat\Gamma_d$ be
as in Prop. 2.1 with $\mu(P)>C_0$. If $d'>2^{C_1d\log d}$, then $P$ has a **coordinate structure**:
a normal subgroup $P_1$ and an action $P\to K\le S_k$ on $k\le C\log d'$ "coordinates" with
$P_1=\ker$. Concretely:
* product action $P\le Q\wr K$;
* affine imprimitive-linear: $P\le\mathrm{AGL}(W)\wr K$ in product action;
* diagonal or twisted wreath with socle $T^k$.

In each case the components have degree and order $\le f(d)$.

*Reason.* In every other case of the proof above, $d'$ is bounded by a function of $d$:
* heart-type and other primitive linear $A_m$: $d'\le p^{m}$ with $m\le d$, and $p\le d$ because
  $C_p$ is a composition factor of $V$;
* classical natural modules: $d'\le q\,d$;
* tensor-decomposable classical modules: $d'\le q^{\lambda^2}\le d^{O(\log d)}$;
* almost simple: $d'\le\lvert P\rvert\le d!^{O(1)}$.

This confirms FPT's lead-2 speculation [SPECULATION in FPT §6], with diagonal and twisted-wreath
types added. **Consequence:** every quotient with $d'>f(d)$ and large order is a $k$-coordinate
structure. Quotients with $d'\le f(d)$ cost at most $\lvert P\rvert\le f(d)$ each, so their only
danger is *compounding* across levels.

### 2.3 Extremal examples

| group $P$ | type | $d$ (class) | $\log_2d'$ | $\mu$ | $\log_2d$ | $\log_2\log_2d'$ |
|---|---|---|---|---|---|---|
| heart $\mathbb F_2^{m-1}\rtimes S_m$, $m=257$ | I, prim. linear | 257 | 256 | 7.61 | 8.01 | 8.00 |
| heart, $m=1025$ | I | 1025 | 1024 | 9.57 | 10.0 | 10.0 |
| monomial $\mathbb F_3^\ell\rtimes(2\wr S_\ell)$, $\ell=512$ | I, imprim. linear | 512 | 811 | 6.41 | 9.0 | 9.66 |
| $S_m$ on $\binom{[m]}{m/2-1}$, $m=320$ | II (not option 2) | 320 | 316 | 6.99 | 8.32 | 8.30 |
| $S_5\wr S_k$ product, $k=512$ | IV ($m=5\le q_0$) | 512 | 1189 | 6.23 | 9.0 | 10.2 |
| diagonal $A_5^k.(2\times S_k)$, $k=512$ | III | 512 | 3018 | 2.29 | 9.0 | 11.6 |
| $\mathrm{AGL}(r,2)$, $r=12$ | I, $H=\mathrm{GL}$ | $2^{12}-1$ | 12 | 12.85 | 12.0 | 3.58 |
| $\mathrm{PGL}(r,2)$ on points, $r=12$ | II | $2^{12}-1$ | 12 | 11.85 | 12.0 | 3.58 |

The numbers are exact formulas: $\log_2 m!$ via log-gamma and $\lvert\mathrm{GL}(r,2)\rvert=\prod(2^r-2^i)$.
The irreducibility facts are standard [PROVEN]:
* For $m$ odd, the even-weight module $E$ is an irreducible $\mathbb F_2S_m$-module (FPT §3.1(a)).
* The monomial group is irreducible on $\mathbb F_3^\ell$: every invariant subspace is a sum of
  coordinate lines, because the sign characters are distinct, and $S_\ell$ is transitive on them.

**Which reach $d'^{\Theta(\log d)}$?**
* **(α) alternating / top-group types** (the first six rows). $\mu\approx\log_2 d\approx\log_2\log_2d'$:
  both are tight at once. Their order comes from $S_k$, $k\le\min(d,C\log d')$, acting on
  $2^{\Theta(k)}$ points.
* **(β) Lie-rank types** (the last two rows). $\mu\approx r+1=\log_2(d+1)+1$ while
  $\log\log d'$ is tiny. These are the only ones with $\mu=\Theta(\log d)$ at $d'=\mathrm{poly}(d)$.
  Products $\mathrm{AGL}(r,2)\wr K$ carry the same $\mu\approx r$ to every $d'\ge d$.
* Solvable point stabilisers give $\mu\le3.25$ (Pálfy 1982; Wolf 1982), bounded-base groups give
  $\mu=O(1)$, and exceptional Lie types have $\mu=O(1)$.

---

## 3. Consequence for R\*: the parameters separate

**Theorem R\*\*.** **[CONDITIONAL: (H0); uses Prop. 2.1, which is a SKETCH]** Let
$G\le\mathrm{Sym}(\Omega)$ with $\lvert\Omega\rvert=N$, all alternating composition factors of degree
$\le w$ ($w\ge6$), and all classical composition factors of dimension $\le\lambda$. Then HJ with
dispatcher (M′) (RT §9(b)) solves string isomorphism in
$$\exp\Bigl(O\bigl(\log(N+2)\cdot(\log w+\lambda+1)\bigr)\Bigr).$$

*Proof.* Rerun VR §4 with $\Lambda:=C(\log w+\lambda+1)$, using the following facts.
* The class is closed under sections. Giants have $q\le w$. Caps can be initialised at
  $\min(d_i,w)$, so $Q\le\log N\log w$.
* (PR) and (E2) need only $\log\lvert K\rvert\le(k-1)\log w$, by BCP's alternating-only hypothesis.
* (E1) needs $\log\lvert P\rvert\le C(1+\lambda+\log w)\log d'$, by Prop. 2.1.
* Configuration calls use $\mathrm{Sym}(C)$ with $\lvert C\rvert\le q\le w$, which lies in the class.
* Phases with $w>N^\alpha$ run HJ verbatim, at cost $e^{C\log^2N}\le e^{(C/\alpha)\log N\log w}$.
* Nothing else in VR §4 used $\mathrm{cw}$. ∎

**Corollary 3.1 (how the exponent splits).** **[CONDITIONAL, as above]** Per unit of $\log N$:

| channel | rows | cost |
|---|---|---|
| giant | x, σ, caps | $\log w$ |
| top groups (2′) | (PR), (E2) | $\le C\min(\log w,\log\log N)$ |
| alternating enumeration | (E1) α-part | $\le C\min(\log w,\log\log N)$ |
| Lie enumeration | (E1) β-part | $C(\lambda+1)$ |

So **channel 2 exceeds channel 1 only through $\lambda$.** For GI of degree $d$ (class
$\hat\Gamma_{d-1}$) both $\log w$ and $\lambda$ are $\Theta(\log d)$, so R\*\* = R\* there.

*Novelty.* GNS Rem. 3.14 says their Thm 3.13 fails for the BCP class $\Gamma_d$, because of
$\mathrm{AGL}(d,p)$. No statement separating $\log w$ from $\lambda$ was found (sources in §6).
It is a routine refinement of R\* and is only as strong as (H0).

---

## 4. Replacing enumeration by structure

### 4.1 The translation part (standard)

**[PROVEN]** Let $P=V\rtimes H$ and let $M$ be the preimage of $V$, so $M\trianglelefteq G$ and $M/K\cong V$
is regular on $\mathfrak B$. Then:
* $\mathrm{Iso}_G=\bigcup_{h\in H}\mathrm{Iso}_{M\sigma_h}$;
* each $M$-coset problem refines along a chain of hyperplanes of $V$ (Luks's solvable case),
  costing $\le d'^{2}$ calls of size $s/d'$.

The total is $\lvert H\rvert\,d'^{O(1)}T(s/d')$. This saves only the factor $\lvert V\rvert=d'$:
$\mu$ drops by 1.

### 4.2 "Recurse on $H$": the trap materialises

**Heart, $P=E\rtimes S_m$.** **[PROVEN]**
* Individualise one block $B_0$ ($d'=2^{m-1}$ branches). Then $G_{B_0}$ acts on $\mathfrak B$ through
  $S_m$, with orbits the weight layers $L_{2j}$.
* On $L_{2j}$ the action is the Johnson action $S_m^{(2j)}$.
* For $2j\gtrsim m/(4\log m)$ these are *not* option 2 ($m\le4\log_2\binom m{2j}$), so (M′)
  enumerates them at cost $m!=d'^{\log_2m-O(1)}$.
* If the strings on the small layers are symmetric (constant, say), the residual group still
  maps onto $S_m$ when the middle layer is reached. Recursing on $H$ re-creates exactly the
  enumeration it was meant to avoid.

**$\mathrm{AGL}(r,2)$.** **[PROVEN]** (MT §4.2) $H=\mathrm{GL}(r,2)$ is transitive on $V\setminus0$,
with quotient $\mathrm{PSL}(r,2)$ on $2^r-1$ points. Individualising again gives $T(d')\approx d'\,T(d'/2)$,
so $d'^{\Theta(\log d')}=d^{\Theta(\log d)}$.

### 4.3 HJ's potential cannot pay the individualisation

**[PROVEN, with explicit constants up to $O(1)$]** In the heart case, individualising $B_0$ has
multiplicity $d'=2^{m-1}$, so a drop of $\Phi_\Lambda$ by $\ge(m-1)\ln2+H_*$ is needed.

The children are the $G_{B_0}$-orbits. The largest is the middle layer, of size
$\approx s\cdot2\sqrt{2/(\pi m)}$. Its potential drops as follows:
* $x$ drops by $\le\tfrac12\ln m$;
* $\rho$: the level's term $2\lfloor\log_2d'\rfloor-1$ becomes $2\lfloor\log_2\binom m{(m-1)/2}\rfloor-1$,
  a drop of $\le\log_2m+2$;
* $Q_d$ drops by $\le\tfrac12\ln m\cdot\ln\tilde d$;
* $\sigma$ and $h$ do not help.

So the drop is $O(A\log d\log m)$, and the step is payable iff $m=O(A\log d\log m)$. For $m$ near
$d$ it fails. (The other children shrink more, but Lemma 7.1 needs *every* child of the class to
drop.)

In Luks-style accounting the same procedure *would* be fine: after the $S_m$ part is resolved, the
leaves are block-size problems, giving
$T(s)\le d'\cdot[\text{giant cost}]\cdot d'\,T(s/d')$. HJ's per-edge potential charges the $d'$ too
early. This is a defect of the analysis, but see §4.4.

### 4.4 Even full Johnson recognition plus HJ giants does not beat $m!$ when $t=\Theta(m)$

**[PROVEN, as a statement about the analysis]**
* Suppose (M′) were extended to recognise $A_m^{(t)}$ for every $t$ and run `GiantStep`.
* For a level of degree $d'=\binom mt=2^{\Theta(m)}$, the potential $\Phi_\Lambda$ allots
  $\Lambda\log d'$ (from $x$) $+\,2\Lambda\log d'$ (from $\rho$) $+\,\log d'\log\tilde d$ (from $Q_d$),
  i.e. $\Theta(m\log d)=\Theta(\log m!)$ when $m\approx d$.
* Equivalently, $\Theta(m)$ constant-factor shrinks, each with multiplicity $m^{O(\kappa)}$.

So the analysis certifies nothing better than enumeration for large-$t$ Johnson levels.
**[SPECULATION]** HJ's actual behaviour is no better either: its giant machinery is efficient
exactly when $\log d'=O(\log q)$.

This matches GNS's cut: option 2 is $m>4\log\binom mt$, i.e. $2^{m/4}>d'$. **The complementary
tool is simply exponential:** $2^{O(m)}$ is $\mathrm{poly}(d')$ precisely outside option 2.
* HJ giants ($m^{O(\log m)}$) serve option 2.
* S-W / Luks 1999 ($2^{O(m)}$) serve the (α) quotients.

### 4.5 What does work: simply exponential canonisation

**Theorem (S-W, `theo:obj`).** [TRUST, statement read] Let $\Delta\le\mathrm{Sym}(U)$ be given by
generators and let $X$ be a hereditarily finite object over $U$ whose atoms are points of $U$ or
labelling cosets. A canonical labelling of $(X,\Delta\rho)$ can be computed in time
$2^{O(k)}n^{O(1)}$, where $n$ is the input size and $k$ the largest $\Delta$-orbit on $U$.

**Proposition 4.1 (small-orbit encodings).** **[PROVEN mod S-W]** Let $\Delta\le\mathrm{Sym}(U)$ have
largest orbit $k$. Let $\Delta$ act on a set $\Omega$ through an injective $\Delta$-equivariant map
$\iota:\Omega\to\mathrm{HF}(U)$ with $\lvert\iota(\omega)\rvert\le c$. Then string isomorphism under
$\Delta$ on $\Omega$ takes $2^{O(k)}\mathrm{poly}(\lvert\Omega\rvert c+\lvert U\rvert)$.

*Proof.*
1. Encode $x$ as $X_x=\{(\iota(\omega),\ulcorner x(\omega)\urcorner)\}$, where the
   $\ulcorner\cdot\urcorner$ are distinct pure sets.
2. Since $\iota$ is injective and equivariant, $\delta\in\Delta$ maps $X_x$ to $X_y$ iff its induced
   permutation of $\Omega$ maps $x$ to $y$.
3. Canonise both objects with respect to $\Delta\rho$ and compare. The isomorphism coset is
   $\mathrm{Aut}(X_x,\Delta\rho)\lambda_x\lambda_y^{-1}$, by S-W (CL1)–(CL2). ∎

Every transitive $\Delta$-set has such an encoding: map $\omega=\omega_0^g$ to the labelling-coset
atom $g^{-1}\Delta_{\omega_0}\rho$. It is well defined, injective and equivariant, and its size is
$\mathrm{poly}(\lvert U\rvert)$.

**Corollaries.** **[PROVEN mod S-W, or mod BCQ12 Thm 5 where marked]**

| instance | ground set $U$ | cost |
|---|---|---|
| (a) $E\rtimes S_m$ or $2\wr S_m$ on $2^m$ points (Boolean functions up to NP-equivalence) | $2m$ literals | $2^{O(m)}=\mathrm{poly}(d')$; this is Luks 1999's result, recovered |
| (b) any $\Delta\le\prod_{i\le L}\mathrm{Sym}(M_i)$ preserving the axes, in product action on $\prod M_i$ | $\bigsqcup M_i$ | $2^{O(\max\lvert M_i\rvert)}N^{O(1)}$ |
| (c) $Q\wr S_k$ in product action, $Q\le\mathrm{Sym}(M)$ (twisted code equivalence, DP over partial strings; BCQ12, Codenotti Thm 4.2.1, as restated in arXiv:2504.19777 Thm 5) | — | $2^{O(k)}\mathrm{poly}(\lvert M\rvert^k\lvert Q\rvert)=\mathrm{poly}(d')\cdot\lvert Q\rvert^{O(1)}$ |

Row (b) covers $\mathrm{AGL}(r,2)^L$ and $(E\rtimes S_m)^L$ in product action, coupled ones such as
$V^L\rtimes\mathrm{GL}_{\rm diag}$, and with literals for (α) components, $2^{O(d)}N^{O(1)}$.

In (c) the component order appears **once**, not $k$ times; a subgroup $K<S_k$ needs a final
coset intersection on $k\lvert M\rvert$ points [SKETCH]. Caveat on (c): I read BCQ's theorem only
in the form restated by arXiv:2504.19777, which has length $O(\log n)$ and groups given by
multiplication tables. Its DP has $\le((\lvert M\rvert+1)^k)^2$ table entries. I did not re-derive
the serial dependence on $\lvert M\rvert$ and $\lvert Q\rvert$ of its coset-intersection steps.

These are the *trivial-kernel* (or product) cases. FPT §3.2 proves the product case with a top
group by a prefix DP plus ADKT (Arvind–Das–Köbler–Toda, Algorithmica 2015: colored hypergraph
isomorphism in $2^{O(b)}N^{O(1)}$).

### 4.6 Theorem L: level-synchronised towers are FPT, despite entanglement and large orbits

This is the main new structural statement. It handles a family that is out of reach of S-W
applied directly, of FPT's Theorem E, and of plain DP.

**Setting.** Let $C_1,\dots,C_L$ be finite sets and $\Omega=C_1\times\cdots\times C_L$. For each $j$ let
$R_j\le\mathrm{Sym}(C_j)$ and $S_j\le N_{\mathrm{Sym}(C_j)}(R_j)$.
* **Local part.** $R=R_1\wr\cdots\wr R_L$ in imprimitive action. It is generated by the local
  moves $\tau_{j,p,\varrho}$ ($p\in C_1\times\cdots\times C_{j-1}$, $\varrho\in R_j$), which apply $\varrho$
  to coordinate $j$ of the points with prefix $p$ and fix all other points.
* **Synchronised part.** $S\le S_1\times\cdots\times S_L$ acts coordinatewise, on all nodes of a
  level at once.
* $G=RS$. Here $R\trianglelefteq G$, because $s_j\varrho s_j^{-1}\in R_j$.
* Each $S_j$ acts on a set $U_j$ with an injective equivariant $\iota_j:C_j\to\mathrm{HF}(U_j)$
  ($U_j=C_j$ is allowed). Let $k$ be the largest $S$-orbit on $U=\bigsqcup U_j$.

**Theorem L.** **[PROVEN mod S-W `theo:obj` for the decision version; SKETCH for assembling the
isomorphism coset]** String isomorphism under $G$ on $\Omega$ takes
$2^{O(k)}\cdot\mathrm{poly}\bigl(\prod_j\lvert R_j\rvert\lvert C_j\rvert\bigr)$. If
$\lvert R_j\rvert\le\lvert C_j\rvert^{c}$ for all $j$, this is $2^{O(k)}N^{O(c+1)}$.

*Proof.* Define orbit-objects bottom-up, for prefixes $p$:
$$\mathrm{Obj}_x(p)=\ulcorner x(p)\urcorner\ (\lvert p\rvert=L),\qquad
\mathrm{Obj}_x(p)=\Bigl\{\bigl\{(\iota_j(c),\ \mathrm{Obj}_x(p\cdot\varrho(c))):c\in C_j\bigr\}:\varrho\in R_j\Bigr\}\ (\lvert p\rvert=j-1).$$

1. *$R$-invariance.* The local move $\tau_{j,p,\sigma}$ replaces child $c$ of $p$ by child
   $\sigma^{-1}(c)$. This permutes the inner sets by $\varrho\mapsto\sigma^{-1}\varrho$, so
   $\mathrm{Obj}(p)$ is unchanged. Deeper moves leave the child objects unchanged, by induction.
   Shallower moves only relocate $p$'s subtree.
2. *Completeness.* If $\mathrm{Obj}_x(p)=\mathrm{Obj}_y(p')$, then the $\varrho=1$ arrangement of $x$
   equals some arrangement $\varrho$ of $y$. Since $\iota_j$ is injective,
   $\mathrm{Obj}_x(pc)=\mathrm{Obj}_y(p'\varrho(c))$ for all $c$. By induction the subtrees are
   $R$-equivalent, and composing with $\varrho$ at $p$ gives local moves mapping $x|_p$ to $y|_{p'}$.
3. *$S$-equivariance.* For $s\in S$: $\mathrm{Obj}_{x^s}(p)=\mathrm{Obj}_x(s^{-1}p)^{s}$. Substitute
   $c=s_j(c')$ and $\varrho'=s_j^{-1}\varrho s_j\in R_j$, which is where the normaliser condition is
   used, and use $\iota_j(s_jc')=\iota_j(c')^{s_j}$.
4. *Conclusion.* From 1–3, $x\cong_Gy$ iff $\mathrm{Obj}_x(\varnothing)^s=\mathrm{Obj}_y(\varnothing)$
   for some $s\in S$. That is object isomorphism under the labelling coset $S\rho$ on $U$.
5. *Cost.* Written as a tree, the object has size $\le\prod_j(\lvert R_j\rvert\lvert C_j\rvert)\cdot c$.
   Apply S-W.
6. *Coset version.* Take $s_0$ from S-W, solve $\mathrm{Iso}_R(x,y^{s_0^{-1}})$ by witness
   tracking in step 2, and lift generators of $\mathrm{Aut}_S(\mathrm{Obj}_x)$ the same way [SKETCH]. ∎

**Example C (synchronised affine tower).** Take $C_j=X=\mathbb F_2^r$, $R_j=X$ (translations) and
$S=\mathrm{GL}(r,2)^L$. Call the result $G_{r,L}=R\rtimes\mathrm{GL}(r,2)^L$, with $N=2^{rL}$.
* $G_{r,L}$ is transitive. Its block tree is given by prefixes, every primitive quotient is
  $\mathrm{AGL}(r,2)$, and $G_{r,L}\in\hat\Gamma_{2^r-1}$ ($r\ne4$). **[PROVEN]**
* **Theorem L:** $2^{O(2^r)}N^{O(1)}=2^{O(d)}N^{O(1)}$.
* The same holds with $E\rtimes S_m$ in place of $\mathrm{AGL}$ ($U_j$ = literals): $2^{O(m)}N^{O(1)}$.

**Proposition 4.2 (HJ lower bound).** **[PROVEN, given HJ's pseudocode L1140–1180 and (M′)]**
On string isomorphism under $G_{r,L}$, and under $\mathrm{AGL}(r,2)^L$ in product action, with
constant strings, HJ+(M′) creates
$$\ge\lvert\mathrm{AGL}(r,2)\rvert^{L-O(1)}\ \ge\ N^{\,r+1-2/r-o(1)}=N^{\log_2(d+1)+1-o(1)}$$
coset branches, where $d=2^r-1$.

*Proof.*
* The coarsest block system is $x_1$-fibres. The quotient is $\mathrm{AGL}(r,2)$: not option 2,
  and $\le\exp(a\log^2d')$, so both HJ and (M′) enumerate it.
* The kernel acts on the fibre $\{x_1=a\}$ as all of $G_{r,L-1}$ (respectively
  $\mathrm{AGL}^{L-1}$). Every coset branch's orbit chain makes this call unconditionally, so
  $T(L)\ge\lvert\mathrm{AGL}\rvert\,T(L-1)$ above $N_0$.
* $\lvert\mathrm{AGL}(r,2)\rvert\ge0.288\cdot2^{r(r+1)}$ and $L=\log_2N/r$. ∎

This is the Lie analogue of FPT's Prop. 3.1, which uses the heart and gets $N^{\log_2D-0.45}$. Here
the exponent is larger ($\log_2(d+1)+1$) and $d'\approx d$.

**Lemma 4.3 (no small faithful domain).** **[PROVEN]** Every faithful permutation representation
of $G_{r,L}$ has an orbit of size $\ge2^{r(L-1)}/L\ge N/(dL)$. So S-W or ADKT applied to any
faithful domain costs $2^{\Omega(N/(dL))}$.

*Proof.*
1. Let $T_L\trianglelefteq G$ be the level-$L$ translations. As a module for the 2-group $R_{<L}$
   (lower translations, transitive on the prefix set $Y$), $T_L\cong\mathbb F_2[Y]\otimes X$.
2. A nonzero $R_{<L}$-submodule has nonzero fixed points (a $p$-group on an $\mathbb F_p$-module).
   The fixed points lie in $\mathbf 1_Y\otimes X$, by transitivity.
3. $\mathrm{GL}(X)$ is irreducible on $X$. So every nonzero $G$-invariant subgroup of $T_L$ contains
   $Z=\mathbf 1_Y\otimes X$.
4. In a faithful action, $Z$ acts nontrivially on some orbit $O$. The kernel of $T_L$ on $O$ is
   $G$-invariant and misses $Z$, so it is trivial.
5. A faithful action of $T_L$ (rank $R=r2^{r(L-1)}$) on one orbit has at most $\lvert O\rvert$
   distinct point stabilisers, each of codimension $\le\log_2\lvert O\rvert$. Their intersection is
   0, so $R\le\lvert O\rvert\log_2\lvert O\rvert$, and hence $\lvert O\rvert\ge R/\log_2R\ge2^{r(L-1)}/L$. ∎

**Entanglement.** At depth $j-1$ the kernel synchronises $\mathrm{GL}^{L-j}$ across all
$2^r$ children. Its index in the product of its projections is
$\lvert\mathrm{GL}(r,2)\rvert^{(L-j)(2^r-1)}$, which is unbounded non-abelian entanglement in FPT's
sense. **So $G_{r,L}$ has unbounded non-abelian entanglement and unbounded orbits, and it is
still FPT.** FPT §0 names exactly these two features as the profile of the natural hard family.
Theorem L shows that they are not sufficient. The missing ingredient is the *pattern* of coupling
(§4.8).

### 4.7 Inside HJ: decoupled nodes compose with $\Lambda=O(1)$

**Proposition 4.4.** **[PROVEN, given HJ's Lemma 7.1 framework, i.e. (H0) for the composition]**

*Setup.* At a transitive node with blocks $\mathfrak B$, quotient $P$ and kernel $K$, suppose
$K=\prod_BK^B$. This can be tested in polynomial time by checking $\lvert K\rvert=\prod\lvert K^B\rvert$.
Transport everything to $B_0$, so that $G\le G_0\wr P$ with $G_0=G_{B_0}^{B_0}$ and
$K=K_0^{\mathfrak B}$ (Krasner–Kaloujnine). Put $Q=G_0/K_0$.

*Reduction.* $\mathrm{Iso}_G(x,y)$ reduces to:
* $\le4d'^2$ string-isomorphism calls of size $s/d'$, under $G_0$ on pairs of blocks. These give
  the cosets $C(B,B')\subseteq Q$ of the $K_0$-orbit matchings.
* One **twisted $P$-level instance**: $\bar G\cong G/K\cong P$ acting on $\mathfrak B\times Q$. It
  asks for $(q_B;\sigma)\in\bar G$ with $q_B\in C(B,B^\sigma)$ for every $B$.
* Polynomial assembly: the fibre over each solution is a coset of $\prod_B(\mathrm{Aut}_{G_0}(x_B)\cap K_0)$.

*Cost in HJ's potential.* The $4d'^2$ children drop by $\ge\tfrac A3\Lambda\log d'$, so
$\Lambda=O(1)$ pays them. The twisted instance is terminal (no recursion). It costs
$\le\lvert P\rvert\mathrm{poly}(s)$, or $2^{O(k_0)}\mathrm{poly}(d')$ when $P$ has a faithful action
with orbits $\le k_0$ ([SKETCH]: encode the cosets $C(B,\cdot)$ as labelling-coset atoms).

*What it buys.* This replaces "$\lvert P\rvert\cdot d'$ children of size $s/d'$" by additive work. It
is FPT's block-pair memoisation (FPT §4.1, Thm E with $\varepsilon=1$) written as an HJ row.

### 4.8 Where it breaks

1. **Integration with HJ.** Theorem L, S-W, BCQ and ADKT are canonisation algorithms over a small
   ground set, applied *globally*. HJ is an isomorphism-only, node-local recursion. To use
   Theorem L on a subgroup that HJ meets, one would need either (i) a canonical form version of HJ
   (Babai 2019 exists for Babai's algorithm, nothing comparable for HJ), or (ii) a dispatcher that
   recognises a level-synchronised tower *globally* in the current group. Neither exists.
   **[SPECULATION]** (ii) is feasible: compute the solvable radical, the block tree, and the action
   of $G/O_\infty(G)$ on levels.
2. **Relative S-W.** I tried running S-W's `canSetHyper` over the coordinate literals of an (α)
   quotient, with block contents attached as labelling-coset atoms. It fails at the leaves.
   S-W's `canInt` is coset intersection on the whole ground set. If $\Omega$ is part of it,
   orbits have size $s$; if it is not, the atoms cannot express the block contents. The leaves
   would need Luks-style coset intersection for the residual group (quotient $P_1$ on blocks),
   recursively, inside a framework whose counting is designed for halving orbits. I could not
   close the recursion. **[SKETCH of the failure.]**
3. **Non-laminar coupling.** Theorem L needs every non-abelian section of a level to be
   synchronised across the *whole* level, or more generally along a laminar family plus DP.
   Candidate obstruction, Example X: $C_j=\mathbb F_2^r$, with $\mathrm{GL}$ at level $j$
   synchronised only between nodes $p$ and $p+(e_j,0,\dots,0)$, where the $e_j$ span $X$. The
   coupling graph on level-1 subtrees is then a Cayley graph of $X$, not a tree.
   * Level-1 translations permute the synchronisation classes, so they cannot be used as atoms:
     orbits on any useful ground set are large.
   * Kernels are entangled, so Theorem E fails.
   * It is not level-synchronised, so Theorem L fails.
   * HJ pays $N^{\Theta(r)}$.

   **[SPECULATION]** But the coupling is *aligned*: partners occupy the same position in their
   subtrees. A DP over aligned positions with local groups of size $\lvert\mathrm{GL}\rvert^{O(2^r)}$
   looks plausible, giving $2^{O(d^2\log d)}\mathrm{poly}(N)$. So I could not certify Example X as
   hard. I found no G-invariant coupling pattern that is both non-aligned and non-laminar. Such
   patterns are forced to be "Cayley-like" by equivariance.

### 4.9 A lead on the alternating part: HJ's σ-machinery on non-Cameron giants

Grohe–Neuen (arXiv:2011.01366 §4.4) note that the Unaffected Stabilizers Theorem fails for
$\hat\Gamma_d$ with $t=O(\log d)$, citing Neuen's thesis Ex. 5.5.10. **[SPECULATION]** That example
is likely heart-type: $P\to S_m$ with $m=\log_2d'+1$, just below Babai's threshold
$2+\log_2d'$. HJ replace that theorem by the extra-orbit rule plus the σ-budget, but apply giant
steps only to Cameron constituents with block maps (L3067–3071).

*Question.* Does HJ's certificate and σ machinery go through for the non-Cameron giant
homomorphism $G\to S_m$ of a heart-type quotient? There is no equivariant map
$\Omega\to\binom{[m]}t$; the windows would come from literals. If it does, the (α) quotients
could be routed to the giant channel without individualising.

---

## 5. Consequences

### 5.1 Is there a finer parameter?

Yes. By §3 the right parameters are the alternating width $w$ (for giants, top groups and
(α)-enumeration) and the classical dimension $\lambda$ (for (β)-enumeration). Removing channel 2's
alternating part does **not** change the exponent's form $\log N(\log w+\lambda)$, because that part
is already $\le\log w$. Removing its Lie part would give $\exp(O(\log N\log w))$.
* At a single level that is unproblematic: one quotient costs $d^{O(\log d)}=f(d)$.
* Across levels it needs non-compounding treatment of coupled classical sections. Theorem L does
  this for synchronised couplings; the non-laminar case is open (§4.8).

| scenario | per-unit-$\log N$ exponent | status |
|---|---|---|
| R\* today | $C(\log w+\lambda+1)\le C'\log d$ | (H0) |
| channel 1 improved to $g(w)$ | $C(g(w)+\min(\log w,\log\log N)+\lambda+1)$ | — |
| + (α)/top groups simply exponential (relative S-W) | $C(g(w)+\lambda+1)$ | needs §4.8.1–2 |
| + Lie part non-compounding | $f(d)\cdot\exp(O(\log N\,g(w)))$ | needs §4.8.3 |

So "channel 2 removed" alone gives nothing for degree-$d$ GI unless channel 1 also improves.

### 5.2 The regime $d=O(\log n)$

R\* gives $n^{O(\log\log n)}$. Polynomial time needs $f(d)=2^{O(d)}$, so even $d!$ is too much.
* Positive: every family in §4.5–4.6 costs $2^{O(d)}N^{O(1)}$, which is polynomial at
  $d=O(\log N)$. This covers product towers and synchronised affine and heart towers. On these,
  HJ+(M′) pays $N^{\Theta(\log\log N)}$ (Prop. 4.2; FPT Prop. 3.1).
* Negative: no general statement. These are string-isomorphism families. Whether degree-$d$ graphs
  produce them through the Babai–Luks reduction is open (FPT Cor. 3.2(3), lead 4).

### 5.3 Graph regimes

"Graphs whose automorphism groups have small alternating sections" is the wrong measure. The
groups that HJ meets are the Luks-tower groups $\mathrm{Aut}_e(X_r)$, not $\mathrm{Aut}(X)$, and for
degree $d$ these contain $S_{d-1}$ sections generically. **[SPECULATION]** The natural graph
analogue of "level-synchronised" is a graph whose radius-$r$ balls are glued by isomorphisms
that are consistent along whole BFS layers. Testing $\varepsilon$ and the coupling pattern on real
towers is FPT's lead 3.

---

## 6. Literature and novelty

| work | relevance | checked |
|---|---|---|
| Luks 1982 | Primitive solvable groups have polynomial order (Pálfy, Wolf: $\le24^{-1/3}n^{3.25}$), so string isomorphism for solvable groups is polynomial; $\Gamma_d$ gives $n^{O(d)}$ via BCP | known |
| Babai–Luks 1983 | canonical forms via cosets; tournaments in $n^{O(\log n)}$ through odd-order (solvable) groups. Tournaments are outside small $\mathrm{cw}$: prime factors up to $n$ | from memory |
| Babai–Kantor–Luks 1983 | degree $d$ in $n^{O(d/\log d)}$ | known |
| Babai–Luks–Seress 1987 | NC structure; Johnson identification (GNS Lemma 4.4) | as cited by GNS |
| Kantor; Kantor–Luks 1990; Kantor–Seress | Sylow subgroups, quotients and socle in polynomial time; constructive recognition of classical groups. **Recognition is not the obstacle** for (β): the isomorphism problem is | from memory |
| Miller 1983 | hypergraph isomorphism for $\Gamma_d$ in $(n+m)^{O(d)}$ | via Neuen 2020 |
| **Luks 1999** | hypergraph isomorphism in $2^{O(n)}$; Boolean functions in polynomial time (DP plus coset intersection) | abstract and descriptions only |
| **Arvind–Das–Köbler–Toda** (FSTTCS 2010 / Algorithmica 2015) | colored hypergraph isomorphism in $2^{O(b)}N^{O(1)}$, with Luks-like divide and conquer | ECCC abstract |
| **Babai–Codenotti–Grochow–Qiao** (SODA 2011), **BCQ** (ICALP 2012) | code equivalence in simply exponential time; twisted code equivalence; Fitting-free group isomorphism in P. **Direct precedent**: simply exponential DP over $O(\log n)$ coordinates removes a $\log\log$ factor | restated in arXiv:2504.19777 |
| **Schweitzer–Wiebking 2019** | canonisation of HF objects in $2^{O(k)}n^{O(1)}$, used throughout §4.5–4.6 | read |
| Wiebking 2020 | normalisers and permutational isomorphism in $2^{O(n)}$ | read (intro) |
| GNS 2018; Neuen 2020; Grohe–Neuen–Wiebking 2020; Neuen 2022; Neuen survey 2026 | $n^{\mathrm{polylog}\,d}$ and relatives; FPT by degree "wide open" | VR, RT, FPT |
| HJ 2026 | no degree corollary; no non-Cameron giants | VR |
| Lokshtanov et al. 2022 | FPT for excluded minors; max degree listed as open | web abstract |

**Novelty.**
* Prop. 2.1 / 2.2 assemble known bounds; the explicit (α)/(β) split and the
  $\min(\log d,\log\log d')$ term were not found stated.
* Theorem R\*\*: not found; routine given R\*.
* Theorem L, Example C, Lemma 4.3 and Prop. 4.2 (Lie case): not found. Theorem L is a short
  combination of S-W with orbit-objects, and experts may regard it as routine. Its value is that
  it **refutes the "entangled plus large orbits implies hard" heuristic**.
* Prop. 4.4 is FPT §4.1 as an HJ row.

---

## 7. Where the attempts broke

1. *Recurse on $H$*: Johnson layers with large $t$, enumerated at $m!$; for $\mathrm{AGL}$, $\mathrm{PSL}$
   on points (§4.2).
2. *Pay the individualisation in $\Phi_\Lambda$*: children shrink by $\sqrt m$; the drop is
   $O(\log d\log m)$ against $m$ needed (§4.3).
3. *Route large-$t$ Johnson to HJ giants*: the budget is $\Theta(\log m!)$ (§4.4).
4. *Relative S-W*: the leaf `canInt` is coset intersection on $\Omega$ (§4.8.2).
5. *Find a hard coupled family*: Example C fell to Theorem L, and Example X looks DP-able along
   aligned positions (§4.8.3).
6. *Single-level Lie cost*: $\mathrm{AGL}(r,2)$ string isomorphism in $\mathrm{poly}(2^r)$ is Boolean
   affine equivalence in $2^{o(r^2)}$. No such algorithm is known (MT §3.3). It is harmless for
   FPT ($f(d)=d^{O(\log d)}$), but it blocks any $n^{o(\log d)}$ bound at $d'\approx d$ with
   $N=\mathrm{poly}(d)$.

---

## 8. Leads for a follow-up agent

1. **Global dispatcher for level-synchronised structure.** Given $G$ with its block tree:
   compute the solvable radical; test whether each level's non-abelian part acts the same way on
   all nodes, i.e. synchronised; then apply Theorem L to that part and HJ elsewhere. This needs a
   precise "laminar coupling" definition and a proof that mixed instances recurse.
2. **Example X**, or a better non-aligned coupling. Either give the aligned-position DP (a positive
   result covering Cayley-coupled towers) or find an equivariant coupling pattern that defeats
   alignment. This is the sharpest open target on the Lie side. It complements FPT's tree-group CI
   problem, which is the giant side.
3. **HJ's σ-machinery on heart-type giants** (§4.9). Read HJ App. A against Neuen's Ex. 5.5.10.
4. **Make Prop. 2.1 rigorous for the BCP class.** Check GSS98 Lemma 4.2(a) and LS14 Prop. 2, so
   that Theorem R\*\* becomes conditional on (H0) only.
5. **Canonical HJ.** Everything simply exponential in §4 needs canonical forms of sub-instances.
   A canonical version of HJ would let Theorem L and FPT's block-pair memoisation run inside the
   recursion.
6. **Graphs.** Does any bounded-degree family hand HJ a $G_{r,L}$ section (affine-plane gadgets
   on a tree, with layer-wise gluing)? If so, Prop. 4.2 is a graph lower bound for HJ+(M′), and
   Theorem L shows those graphs are FPT.

---

## 9. Ledger

| item | status |
|---|---|
| Prop. 2.1 ($\mu$ bound), Prop. 2.2 (coordinate type) | **[SKETCH]**; inputs LS14, Liebeck 1984, GSS98 [TRUST via GNS] |
| Table 2.3 examples, irreducibility | **[PROVEN]** |
| Theorem R\*\*, Cor. 3.1 | **[CONDITIONAL: (H0)]** + Prop. 2.1 |
| §4.1 translation part | **[PROVEN]** (standard) |
| §4.2 trap (heart, $\mathrm{AGL}$) | **[PROVEN]** |
| §4.3 individualisation not payable in $\Phi_\Lambda$ | **[PROVEN]** |
| §4.4 HJ budget for large-$t$ Johnson $=\Theta(\log m!)$ | **[PROVEN]** about the analysis; behaviour **[SPECULATION]** |
| Prop. 4.1 and corollaries | **[PROVEN mod S-W]**; (c) mod BCQ12 Thm 5 |
| Theorem L | decision **[PROVEN mod S-W]**; coset assembly **[SKETCH]** |
| Example C facts, Lemma 4.3, entanglement index | **[PROVEN]** |
| Prop. 4.2 (HJ $\ge N^{\log_2(d+1)+1-o(1)}$ on $G_{r,L}$, $\mathrm{AGL}^L$) | **[PROVEN]** from HJ's pseudocode; independent of (H0) |
| Prop. 4.4 (decoupled row, $\Lambda=O(1)$) | **[PROVEN]**; composition needs (H0) |
| §4.8 failures; Example X | **[SKETCH]** / **[SPECULATION]** |
| Luks 1999 content | second-hand (S-W, Neuen 2020, Oregon abstract) |
| No Lean was built; no solver was run | — |
