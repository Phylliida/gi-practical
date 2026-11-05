# w1-fpt: Is degree-$d$ graph isomorphism FPT? Attacks, barriers, and where $\log d$ comes from

Branch `w1-fpt`, 2026-11-04. This continues Theorem R\*: string isomorphism for $\hat\Gamma_d$ in
$\exp(O(\log(N+2)\log(d+2)))$, hence graph isomorphism of maximum degree $d$ in $n^{O(\log(d+2))}$,
conditional on HJ (arXiv:2611.01399). See `verify-theorem-R.md` and `redteam-theorem-R.md`.
Notation follows those memos. $\hat\Gamma_d$ is the class of groups all of whose composition
factors embed in $S_d$. "HJ+(M′)" is HJ's algorithm with the structural dispatcher (M′) of
`redteam-theorem-R.md` §9(b).

**Labels.**

* **[PROVEN]**: a complete argument is given here. It uses only cited published results and the
  standard polynomial-time permutation-group toolkit (Schreier–Sims, pointwise stabilizers,
  restriction homomorphisms and their preimages, intersection with a normal subgroup).
* **[PROVEN mod X]**: complete, except that the published result X is used without re-proof.
* **[SKETCH]**: an argument is given with gaps, and the gaps are named.
* **[CONDITIONAL: H]**: holds under hypothesis H.
* **[SPECULATION]**: opinion or conjecture.

Sources read are listed in §8. New downloads went into `scratchpad/r4-sources/w1fpt-*`. Nothing
was executed except a PDF-to-text conversion, and no benchmarks or Lean were run.

---

## 0. Summary

| # | question | answer here | label |
|---|---|---|---|
| 1 | Literature status of FPT by max degree | **Open.** It is posed in Downey–Fellows, in GNS's conclusion and in Grohe–Neuen 2021 (open question 4). Neuen's 2026 survey calls it "wide open". The same holds for string isomorphism parameterized by composition width, and the survey asks (Q4.8) whether the two are even FPT-equivalent. No W-hardness and no lower bound for any group-theoretic algorithm class is known. All known lower bounds (CFI/WL, IR, proof systems) already hold at degree 3, so they say nothing about the dependence on $d$. | lit. (§1) |
| 2 | Is R\* tight for its own algorithm? | **Yes, for every fixed $d$.** For every odd $D\ge3$ there are $\hat\Gamma_D$ string-isomorphism instances of every size $N=2^{(D-1)m}$ on which HJ+(M′), and HJ verbatim, create at least $N^{\log_2D-0.45}$ coset branches, whatever the strings. So R\*'s exponent $O(\log d)$ cannot be improved by re-analysis: the algorithm must change. The same family shows that the exponent $c_1\log d$ in GNS Thm 3.13 is sharp for each fixed $d$. | **[PROVEN]** (§3.1) |
| 3 | Is that floor intrinsic? | **No.** The same family is solved in $2^{2^{O(D)}}\cdot N^{O(1)}$ by a dynamic program over prefix blocks that uses the FPT coset intersection of Arvind–Das–Köbler–Toda for bounded orbits. So "branch over cosets, recurse, never memoize" is what costs $N^{\log d}$. | **[PROVEN mod ADKT Thm 5]** (§3.2) |
| 4 | Can giant-step branching be made additive across levels? | **Yes, at a price.** Memoize partial isomorphisms between all pairs of blocks of one block hierarchy; there are $O(N^2)$ of them. Every giant then costs $q!\le d!$ once per block pair, additively. All the difficulty moves into one combine primitive: intersecting a kernel coset with a product of child cosets (PCI, §4.1). | **[PROVEN]** (§4.1–4.2) |
| 5 | FPT subclass | **Theorem E.** Suppose every primitive component has order at most $\pi_0$ and every kernel $K_B$ has index at most $\varepsilon$ in the direct product of its projections to the child blocks ("entanglement index"). Then string isomorphism runs in $\pi_0\cdot\varepsilon\cdot\mathrm{poly}(N)$. For tree groups of node degree $\le b$ this is $b!\,\varepsilon\,\mathrm{poly}(N)$. It covers all iterated wreath products, and the iterated "GI-gadget" wreath family of §3.3. | **[PROVEN]** (§4.3) |
| 6 | The core open problem, isolated | For tree groups (subgroups of iterated wreath products of $S_b$, acting on leaves), string isomorphism is FPT in $b$ **iff** coset intersection is FPT in $b$. | **[PROVEN]** (§4.4) |
| 7 | Barrier for the branching channel | The reduction is: no-memo top-down recursion over $L=\log_qN$ levels pays $c(q)^L=N^{\log c(q)/\log q}$. So it is FPT only if a single level costs $q^{O(1)}$, and on one-level instances that is digraph isomorphism of $q$ vertices in $q^{O(1)}$. The applicability to HJ is conditional: if HJ's giant handling is $q^{\Omega(\log q)}$ on some $q$-vertex family $\mathcal C$, then HJ is $N^{\Omega(\log q)}$ on iterated wreath products over $\mathcal C$, which Theorem E solves in $q!\cdot\mathrm{poly}(N)$. | reduction **[PROVEN]**; HJ link **[CONDITIONAL]** (§3.3) |
| 8 | Polynomial for $d=O(\log n)$; $n^{O(\log d/\log\log d)}$ | **Not achieved.** Item 2 rules out both for HJ+(M') at the level of string isomorphism. Any route must replace enumeration of product-action affine quotients, which item 3 shows is possible, *and* handle entangled kernels. | §5 |

**One-paragraph verdict.** The $\log d$ in R\* has two sources, and both are multiplicative.
1. *Enumeration*: product-action affine quotients of order $N^{\Theta(\log d)}$ already exist
   at fixed $d$, and HJ+(M′) provably pays for them.
2. *Giants*: Babai-type giant handling is compounded over about $\log_qN$ hierarchy levels.

Memoization over block pairs removes the multiplicativity of both whenever the "combine" step,
a coset intersection with an entangled kernel, is cheap. That happens when the kernel is
unentangled or boundedly entangled (Theorem E, new), when it has bounded orbits on a small
faithful domain (ADKT), or when it is abelian (linear algebra). The FPT question for tree groups
is *equivalent* to FPT coset intersection for tree groups. The natural candidate hard family has
unbounded non-abelian entanglement and unbounded orbits: product actions of many deep tree groups
(§6). I found no way through it, and no lower-bound technique that applies to it.

---

## 1. Literature status

### 1.1 The FPT question

* **Downey–Fellows** (1999 monograph) asked for FPT algorithms for GI parameterized by maximum
  degree and by tree width. Quoted in the Neuen 2026 survey, p. 1, and in ADKT (ECCC TR09-093)
  p. 3.
* **GNS** (arXiv:1802.04659v3, conclusion G2276–2280): "Another related problem that we leave open
  is whether the graph isomorphism problem parameterized by the maximum degree of the input graphs
  is fixed-parameter tractable."
* **Grohe–Neuen 2021** (arXiv:2011.01366, open questions, text L2111–2124): question 4, "Is GI
  parameterized by maximum degree fixed-parameter tractable?"
* **Neuen 2026** (Comput. Sci. Rev. 60, 100918, §4.1): "the long-standing open question of whether
  isomorphism testing parameterized by the maximum degree is fpt … remains wide open". He then
  asks **Question 4.8**: is there an fpt-reduction from string isomorphism parameterized by
  composition width to GI parameterized by maximum degree? (The converse is a polynomial-time
  Turing reduction, Lemma 4.5.) He also notes that set-of-strings isomorphism reduces to string
  isomorphism in polynomial time, but no fpt reduction is known.
* **Neuen ICALP'20 / TALG** (arXiv:2002.06997, conclusion): hypergraph isomorphism for
  $\hat\Gamma_d$ in $(n+m)^{O((\log d)^c)}$. It asks for $n^{O((\log d)^c)}m^{O(1)}$, not for FPT.
* **Web searches** (2026-11-04, standard and extended) found no paper after the 2026 survey
  claiming progress on FPT by degree, and no improvement on $n^{\mathrm{polylog}\,d}$ other than
  this campaign's conditional R\*. One GitHub "problem" page (`tangle-solve`) restates the
  question; it is low-authority and its attribution is wrong (see `verify-theorem-R.md` §7).

**Best known bounds**, string isomorphism for $\hat\Gamma_d$ and GI of degree $d$:
* Luks: $n^{O(d)}$.
* Babai–Kantor–Luks: $n^{O(d/\log d)}$.
* GNS: $n^{O((\log d)^c)}$.
* This campaign, conditional on HJ: $n^{O(\log d)}$.

None is FPT. GNS state no explicit $c$; from their proof (`verify-theorem-R.md` §1.1) $c\ge4$.

### 1.2 FPT results that use the same group-theoretic machinery

These matter because they are the only FPT mechanisms known inside Luks-style recursion.

* **Bounded color classes.**
  * Graphs: Babai 1979 and Furst–Hopcroft–Luks 1980 give $O(b!)\,n^{O(1)}$. The halving trick
    improves this to $2^{O(b)}n^{O(1)}$ (ADKT p. 2).
  * Hypergraphs, **Arvind–Das–Köbler–Toda (ADKT)**, Algorithmica 71 (2015), ECCC TR09-093 rev. 1:
    $2^{O(b)}N^{O(1)}$, read in full.
  * Canonization of the same in matching time: Schweitzer–Wiebking STOC'19 (abstract only).

  The ADKT ingredients are exactly the ones used in §3.2 and §4:
  * (i) Set Transporter and **Coset Intersection for groups all of whose orbits have size
    $\le b$** in $2^{O(b)}n^{O(1)}$ (Thms 3 and 5, via Luks's halving and "restricted set
    stabilizer").
  * (ii) **dynamic programming over "$(i)$-blocks"**: the hyperedges agreeing on the first $i$
    color classes. A table stores the isomorphism coset between every pair of blocks, and parents
    are combined by coset intersection (Thm 6).

  ADKT p. 3 also remark: "an fpt algorithm for Set Transporter w.r.t. groups in $\Gamma_d$ (with
  $d$ as parameter) would result in an fpt algorithm for testing isomorphism of graphs of degree
  $\le d$."
* **Luks 1999** (STOC, "Hypergraph isomorphism and structural equivalence of Boolean functions";
  known only through ADKT and Schweitzer–Wiebking): hypergraph isomorphism in $c^n$ by dynamic
  programming with coset intersection. Hence equivalence of Boolean functions under variable
  permutations runs in time polynomial in the truth-table size. The group there is $S_k$ on
  $\{0,1\}^k$ with $N=2^k$, so it has composition width $k=\log_2N$. A group of composition width
  $\Theta(\log N)$ can thus have polynomial-time string isomorphism, through memoization rather
  than branching.
* **Other FPT parameterizations** (survey §1, §5): eigenvalue multiplicity (Evdokimov–Ponomarenko,
  $2^{O(k\log k)}n^{O(1)}$), feedback vertex number, tree depth, tree width ($2^{k\,\mathrm{polylog}\,k}n^3$,
  Grohe–Neuen–Schweitzer–Wiebking), genus, and excluded minors (Lokshtanov–Pilipczuk–Pilipczuk–Saurabh).
  None uses bounded composition width as the source of FPT.

### 1.3 Hardness and lower bounds

* **W-hardness.** None is known for GI under any of the classical parameters. Otachi–Schweitzer
  (arXiv:1403.7238) name "the uncertainty whether the standard reduction techniques, like showing
  W[1]-hardness, can be applied" as an obstacle. W[1]-hardness is known only for exotic
  automorphism variants: exact-weight hypergraph automorphisms with colour constraints,
  Arvind–Köbler–Kuhnert–Torán (STACS'17, IPEC'17), found by search.

  A W[1]-hardness proof for GI parameterized by degree would also need a parameter blow-up of at
  least $2^{k^{\Omega(1)}}$. Otherwise GNS's $n^{\mathrm{polylog}\,d}$ would solve $k$-clique in
  $f(k)N^{k^{o(1)}}$, contradicting ETH. **[PROVEN under ETH, one line]**
* **Lower bounds for algorithm classes.** All known ones hold at bounded degree, so the classes
  they defeat are not even XP in $d$:
  * Cai–Fürer–Immerman: WL dimension $\Omega(n)$ on degree-3 graphs.
  * Neuen–Schweitzer (STOC'18, arXiv:1705.03283): individualization-refinement trees of size
    $2^{\Omega(n)}$. Their graphs have bounded colour classes (stated in the paper), so simple
    group theory solves them.
  * Resolution and algebraic proof-system lower bounds on CFI graphs: Torán; Berkholz–Grohe
    (ICALP'15); arXiv:2407.17947. Cited from memory or abstract.

  **No lower bound is known for any class containing Luks-type coset recursion.** The only
  algorithm-specific bounds are the moonshot memo's Proposition 2 (HJ on $\mathrm{AGL}(k,2)$,
  $d\approx N$) and the red team's remark on $\mathbb F_2^k\rtimes S_{k+1}$ ($d=\log_2N+1$). §3.1
  below gives the fixed-$d$ version.
* **WL dimension growing with $d$** is not meaningful: it is already unbounded at $d=3$.
* **Known obstruction to the natural certificate route.** Neuen's thesis Example 5.5.10, via
  Grohe–Neuen 2021 §4.4, shows that the Unaffected Stabilizers Theorem fails for $\hat\Gamma_d$
  with $t=O(\log d)$. HJ's constant $\kappa$ plus the σ-budget claims to bypass it
  (`redteam-theorem-R.md` §7).

---

## 2. Where the $\log d$ comes from in the branching channel

### 2.1 Chains, levels and the threshold $q_0$

In Lemma 7.1's framework, cost is at most $\mathrm{poly}\cdot e^{\Phi(\text{root})}$, and along
any chain of nested charged steps $\sum_j\log M_j\le\Phi(\text{root})$. In R\*,
$\Phi_\Lambda(\text{root})=\Theta(\Lambda\log N)$ with $\Lambda=\Theta(\log\tilde d)$.

**Observation 2.1** (accounting) **[PROVEN, elementary]**.
* Suppose a charged step has $M\ge\binom q\kappa$ branches, and its only decreasing resource is
  the domain, with children of size $\le\theta s$. A potential that is linear in $x=\log s$ with
  coefficient $\alpha$ pays it only if $\alpha\log(1/\theta)\ge\kappa\log(q/\kappa)$.
* Hence $\Phi(\text{root})\ge\alpha\log N=\Omega(\kappa\log q\log N/\log(1/\theta))$.
* An FPT-type analysis, $\Phi(\text{root})\le C\log N+g(d)$ with $C$ absolute, therefore needs
  every giant step with $q^{\Omega(1)}$ branches to have children of size $\le s\cdot q^{-\Omega(1)}$
  on average along chains. Otherwise the number of such steps per chain must be $g(d)$-bounded.

**Which HJ steps violate this.** Rows refer to `redteam-theorem-R.md` §1.3; the geometric case
is Lemma J of `moonshot-theory.md` §2.1.

| step | branches | children | polynomial in $q$ shrink? |
|---|---|---|---|
| geometrically affected certificate children (block meets $T$) | $q^{O(\kappa)}$ | $\le(t/q)s$ | **yes** if $t\le\sqrt q$ (Lemma J); fine |
| algebraically affected children | $q^{O(\kappa)}$ | $\le s/\kappa$ only | **no** |
| extra-orbit (σ) steps | $q^{O(\kappa)}$ | same domain, $\sigma\to\sigma-\kappa$, with $\sigma=\Theta(\log N)$ possible | **no** |
| cap contraction ($Q$) | $q^{a}$ | same domain, cap $q\to\beta q$ | **no**: the analysis budgets $q^{\Theta(\log q)}$ per interval |
| large-symmetry (aggregation) | $q^{O(1)}$ | $\le s/2$ | **no** |
| product refinement | $2^k\lvert K\rvert\le 2^k\tilde d^{\,k-1}$ | same domain, $\rho\to\rho-(k-1)$, $\rho\le2\log_2N$ | **no**: this is a third $\Lambda\log N$ channel |
| enumeration of non-Cameron $P$ | $\lvert P\rvert\le d'^{O(\log d)}$ | $\le s/d'$ | **no** in general (§3.1) |

**For $d\le q_0$ there are no giant steps at all** (`redteam-theorem-R.md` §3). The FPT question
for R\* concerns $d\to\infty$, and for any fixed $d$ the enumeration row alone already gives
$N^{\Omega(\log d)}$ (§3.1).

---

## 3. Barriers

### 3.1 HJ+(M′) is $N^{\Omega(\log d)}$ at every fixed $d$

**Construction.**
* Let $D=d+1\ge3$ be odd, $W=\{w\in\mathbb F_2^{D}:\sum w_i=0\}\cong\mathbb F_2^{d}$, and
  $P_d=W\rtimes S_D$, with $S_D$ permuting coordinates and $W$ acting by translation on $W$.
* Let $\Delta=W$, so $b:=|\Delta|=2^d$. For $m=2^j$ let $K=C_m$ (regular on $[m]$), and let
  $$G_{d,m}=P_d\wr_{[m]}K\quad\text{in product action on }\Omega=\Delta^m,\qquad N=|\Omega|=2^{dm}.$$

**Proposition 3.1.** **[PROVEN]**
1. $G_{d,m}$ is primitive, its socle is elementary abelian, $G_{d,m}\in\hat\Gamma_D$, and
   $|G_{d,m}|\ge N^{\log_2D-0.443}$.
2. On $\mathrm{SI}(G_{d,m},x,y)$ the following algorithms all create at least $|G_{d,m}|$ coset
   children, for every pair of strings: HJ+(M′), HJ verbatim, and every Luks-type algorithm that
   enumerates primitive quotients outside GNS option 2. If an implementation adds a colour-count
   pre-check, the bound holds for every pair with equal colour multisets, in particular whenever
   $x\cong_Gy$.

*Proof.*

(a) *$P_d$ is primitive and non-regular.* For $D$ odd, $\mathbb F_2^D=\langle\mathbf 1\rangle\oplus W$,
and $W$ is an irreducible faithful $\mathbb F_2S_D$-module for $D\ge3$. This is standard: the
permutation module of $S_D$ over $\mathbb F_2$ has exactly the submodules $0,\langle\mathbf1\rangle,W,\mathbb F_2^D$,
and a non-identity permutation moves some $e_i+e_j\in W$. An affine group $V\rtimes H$ is
primitive iff $H$ is irreducible on $V$. So $P_d$ is primitive, and $|P_d|=2^dD!>2^d$ shows it is
not regular. For $D=3$, $P_2=\mathrm{AGL}(2,2)\cong S_4$.

(b) *Primitivity of $G_{d,m}$.* By Dixon–Mortimer Lemma 2.7A, $H\wr K$ in product action is
primitive iff $H$ is primitive and not regular and $K$ is transitive. Moreover $G_{d,m}=W^m\rtimes(S_D\wr K)$
is affine with translation group $W^m$. For a primitive affine group the translation group is the
unique minimal normal subgroup. So $\mathrm{Soc}(G_{d,m})\cong\mathbb F_2^{dm}$, which is not a
product of alternating groups.

(c) *Class.* The composition factors are $C_2$ (from $W$, from $S_D/A_D$ and from $C_{2^j}$) and
$A_D$. All embed in $S_D$.

(d) *Order.*
$$\log_N|G_{d,m}|=1+\frac{\log_2D!}{D-1}+\frac{\log_2m}{(D-1)m}\ \ge\ 1+\log_2\frac De=\log_2D-0.4427,$$
using $D!\ge(D/e)^D$ and $\frac{\log_2D!}{D-1}\ge\frac{\log_2D!}{D}$.

(e) *The trace is that of `moonshot-theory.md` Prop. 2.*
* `Solve` uses the faithful action. For $N>N_0$, `Continue` sees a transitive group with no
  column floor.
* The exposed primitive quotient (L1153) is $G_{d,m}$ itself on singletons.
* (M′) enumerates every primitive quotient that is not GNS option 2 with $m'>q_0$
  (`redteam-theorem-R.md` §9(b)). Option 2 requires socle $(A_{m'}^{(t)})^k$, so by (b) it
  enumerates. HJ verbatim enumerates when $|P|\le\exp(a\log^2d')$ (L1766–1772), which holds once
  $a\log N\ge\log_2D+2$.
* (M′) is used in phases with $d\le N^\alpha$, which holds for large $N$.
* Enumeration "partitions the allowed relabelings into exhaustive cosets" (L1365–1367). The kernel
  is trivial, so there are $|G_{d,m}|$ children, each solved by its own `Continue` call. ∎

**Remarks.**
* *A variant without primitivity.* Take $K=1$, i.e. $P_d^m$ on $\Delta^m$. The maximal block
  system projects onto one coordinate, and the kernel orbits are slices $\{a\}\times\Delta^{m-1}$
  on which the kernel acts as $P_d^{m-1}$. HJ's orbit chain fully recurses into the first slice in
  every one of the $|P_d|$ cosets. This gives $T(m)\ge|P_d|\,T(m-1)$, the same bound
  $N^{\log_2D-0.443}$, again for all strings. That argument uses more of HJ's recursion
  (L1205–1212), so (e) is the cleaner statement.
* *Exponents for small $D$.* At $D=3,5,9,33$ the exponent $\log_{2^d}|P_d|$ is $2.29$, $2.73$, $3.31$,
  $4.83$.

**Corollary 3.2.** **[PROVEN]**
1. *R\* is tight for HJ+(M′) up to the constant in the exponent, for every fixed $D$.* The
   upper bound is $\exp(O(\log N\log D))$ and the lower bound is $N^{\log_2D-0.45}$. No re-analysis
   of HJ+(M′) gives $n^{o(\log d)}$, $n^{O(\log d/\log\log d)}$ or FPT for string isomorphism over
   $\hat\Gamma_d$.
2. *GNS Thm 3.13(1) is sharp for every fixed $d$:* the primitive $\hat\Gamma_D$ groups $G_{d,m}$
   have order $n^{\log_2D-O(1)}$ for infinitely many $n$. GNS's Remark 3.14 shows only
   $\mathrm{AGL}(d,p)\notin\hat\Gamma_d$. The red team's example had $d\approx\log n$. The product
   construction is standard, but I did not find it stated as a sharpness example.
3. *Scope caveat.* This is a string-isomorphism lower bound. Transferring it to *graphs* of
   degree $O(D)$ would need the Babai–Luks reduction to produce $G_{d,m}$ (or $P_d^m$) as a
   section that HJ meets. Q4.8 is open, and product actions of unbounded arity look hard to
   realize at bounded degree (§6, lead 4). **The corollary for GI is not claimed.**

### 3.2 The same family is FPT: the floor is a no-memo artifact

**Proposition 3.3.** **[PROVEN mod ADKT Thm 5]** Let $G=P\wr_{[m]}K$ act in product action on
$\Delta^m$, with $|\Delta|=b$, $P\le\mathrm{Sym}(\Delta)$ and $K\le S_m$, given with its product
structure. Then $\mathrm{SI}(G,x,y)$ is solvable in
$|K|\cdot|P|\cdot2^{O(b)}\cdot N^{2}\cdot\mathrm{poly}(bm)$. For $G_{d,m}$ this is
$2^{2^{O(D)}}N^{2+o(1)}$, since $|K|=m\le\log N$. More generally, $K\in\hat\Gamma_D$ transitive
gives $|K|\le D^{m-1}\le N^{\log_2D/(D-1)}\le N$ by BCP.

*Proof.* The idea is ADKT's DP, written for strings.
* Enumerate $k\in K$ and replace $y$ by $y^k$, so it suffices to solve $\mathrm{SI}(P^m,x,y)$.
* For $0\le i\le m$ and $u,u'\in\Delta^i$ let $x_u(z)=x(u,z)$ and $y_{u'}(z)=y(u',z)$ for
  $z\in\Delta^{m-i}$. Let $\mathrm{ISO}_i(u,u')\subseteq W_i:=P^{m-i}$ be the set of $w$ with
  $y_{u'}(w(z))=x_u(z)$ for all $z$. It is empty or a coset of $\mathrm{Aut}_{W_i}(x_u)$.
* Splitting $w=(p,w')$ with $p\in P$ acting on the first coordinate,
  $$\mathrm{ISO}_i(u,u')=\bigcup_{p\in P}\{p\}\times\bigcap_{a\in\Delta}\mathrm{ISO}_{i+1}(ua,\,u'p(a)).$$
* $W_{i+1}$ acts faithfully on $V_{i+1}=\bigsqcup_{j>i+1}\Delta_j$, which has $\le bm$ points, and
  every $\Delta_j$ is invariant with $|\Delta_j|=b$. The intersection of $b$ cosets is therefore
  $b-1$ instances of ADKT's Coset-Inter, each in $2^{O(b)}(bm)^{O(1)}$.
* The union over $p$ is a coset (it is an iso set). Generators: one element $(p,w_p)$ per
  feasible $p$, plus generators of the $p=1$ part.
* The table has $\sum_i b^{2i}\le2N^2$ entries, and $\mathrm{ISO}_0(\varnothing,\varnothing)$ is
  the answer. ∎

So HJ+(M′) pays $N^{\log_2D-0.45}$ on a family that is FPT. The cheap algorithm memoizes the
$O(N^2)$ pairwise slice isomorphisms. It intersects cosets **on the small faithful domain** $V$
($bm=b\log_bN$ points, orbits of size $b$), never on $\Omega$.

**Remark (small faithful degree).** **[PROVEN mod Luks 1999]** If, as here, $\Omega$ consists of
transversal subsets of a $G$-set $V$ on which $G$ acts faithfully, then Luks's $c^{|V|}$
hypergraph DP gives $\mathrm{SI}$ in $c^{|V|}\mathrm{poly}(N)$. When $|V|=O(\log N)$ this is
polynomial. For example, take $P=A_5$ and any $K$, so $|V|=5\log_5N$. This includes
$A_5\wr(\text{iterated wreath products of }S_D)$, whose order is $N^{\Theta(\log D)}$. Such groups
are a second, top-group route to the enumeration floor (through the enumeration row when
$m\le q_0$, or the $\rho$ row when $m>q_0$) and are equally easy for memoizing algorithms.

### 3.3 The branching (giant) channel: compounding

**The reduction.** **[PROVEN, elementary]** Consider an algorithm that solves a hierarchy of $L$
levels top-down, handling each level's giant with branching $c(q)$, and fully re-solving the
lower levels in each branch (no memoization). On $L$-level instances its cost is at least
$c(q)^L$.
* With $L=\log_qN$ this is $N^{\log c(q)/\log q}$, so it is FPT iff $c(q)\le q^{O(1)}$ with an
  absolute exponent.
* A one-level instance can be digraph isomorphism on $q$ vertices: $G=S_q$ on ordered pairs, which
  is a tree group of node degree $\le q$ (rows, then points).
* So a uniform $q^{O(1)}$ level handler is a polynomial-time GI algorithm. The quasi-polynomial
  handler $c(q)=q^{O(\log q)}$ compounds to exactly $N^{O(\log q)}$, the form of R\*.

**The family that separates memoization from compounding.** Let $\mathcal W_L$ be the $L$-fold
imprimitive wreath power of ($S_q$ on ordered pairs), with level strings encoding $q$-vertex
digraphs.
* $\mathcal W_L$ is a tree group with every kernel the full direct product of its projections
  ($\varepsilon=1$).
* Theorem E (§4.3) solves it in $q!\cdot\mathrm{poly}(N)$, which is FPT.
* A compounding algorithm needs $c(q)^{L}$.

**Does HJ compound here?** **[CONDITIONAL: HJ's giant handling costs $q^{\Omega(\log q)}$ on some
$q$-vertex digraph family $\mathcal C$, e.g. conference graphs; this is the memo's §2.4
speculation, unproven] [SKETCH]**
* HJ resolves a giant by cap-contraction continuations and aggregation branches on the *same*
  domain (`LiftAndContinue`).
* Each surviving branch then recurses into all kernel orbits, which here are the lower levels.
* Taking level strings from $\mathcal C$, HJ's cost is $\ge(q^{\Omega(\log q)})^{L}=N^{\Omega(\log q)}$,
  while Theorem E gives $q!\,\mathrm{poly}(N)$.

Gap: I did not verify that the cap chain's branches all survive to the kernel recursion. Note
also that if HJ's children were all geometric (shrink by $q$), its constant $\kappa$ would give
$N^{O(\kappa)}$ on $\mathcal W_L$: polynomial with an absolute exponent. The $\log q$ must come
from same-domain steps.

### 3.4 Why I could not prove a lower bound for a general coset-branching model

The natural model allows the following, with cost equal to the number of leaves:
* split a coset $H\sigma$ into the cosets of any subgroup $L\le H$;
* apply the orbit chain rule, where the later orbits use the answer-dependent stabilizer coset;
* prune by local string checks;
* no memoization.

It contains Luks and every "enumerate primitive quotients" algorithm, but not HJ, whose Babai
machinery builds canonical relational structures and runs WL.

On $P_d^m$ even this model is cheap for **generic** strings. Split on the point stabilizer of one
coordinate ($b$ cosets) and solve the first slice ($T(m-1)$). If the slice is rigid, the
remaining slices are under a group of order $\le|P_d|$. So $T(m)\le b\,T(m-1)+|P_d|\,b\,\mathrm{poly}$,
which gives $f(d)\cdot N$.

A lower bound therefore needs adversarial strings: slices that are pairwise isomorphic, with
large automorphism groups that nevertheless do not decouple. Proving that *every* splitting
strategy then has $N^{\Omega(\log d)}$ leaves is a tree-like proof-complexity statement
(prover–delayer style), and I did not find one. **[open]**

---

## 4. Attacks

### 4.1 Memoization over block pairs

**Setting.**
* Fix, for each orbit of $G\le\mathrm{Sym}(\Omega)$, a $G$-invariant **maximal** chain of block
  systems. Together these form a rooted tree $\mathcal T$ of blocks, with a virtual root whose
  children are the orbits. $G$ acts on $\mathcal T$.
* For a block $B$ with children $C_1,\dots,C_r$, let:
  * $H_B=G_B|_B$, the setwise stabilizer restricted to $B$;
  * $P_B\le\mathrm{Sym}(\{C_i\})$, the action on children. It is primitive, or trivial at the
    virtual root;
  * $K_B\trianglelefteq H_B$, the kernel of that action;
  * $\pi_i$, restriction to $C_i$.
* For blocks $B,B'$ at the same level, let
  $\mathrm{Iso}(B,B')=\{g|_B: g\in G,\ B^g=B',\ y(\omega^g)=x(\omega)\ \forall\omega\in B\}$.
  It is empty or a coset of $\mathrm{Aut}(B):=\mathrm{Iso}(B,B)\le H_B$.

**Proposition 4.1 (DP).** **[PROVEN]**
1. *Recurrence.* For $h_0\in H_B$-translates inducing a bijection $\sigma:\{C_i\}\to\{C'_j\}$,
   $$\mathrm{Iso}(B,B')=\bigcup_{\sigma}\Big(K_Bh_\sigma\ \cap\ \Pi_\sigma\Big),\qquad
   \Pi_\sigma=\{f: f|_{C_i}\in\mathrm{Iso}(C_i,C'_{\sigma(i)})\ \forall i\}.$$
   The union runs over the at most $|P_B|$ bijections induced by $H_Bh_0$. Each $\Pi_\sigma$ is a
   coset of $\prod_i\mathrm{Aut}(C_i)$.
2. *Table size.* There are at most $(\sum_j|\mathfrak B_j|)^2\le4N^2$ block pairs, since a
   maximal chain at least doubles the number of blocks per level.
3. *Consequence.* $\mathrm{SI}(G,x,y)$ reduces to at most $4N^2\max_B|P_B|$ instances of
   **product-coset intersection**:

   > **PCI**: given $K\le\prod_iR_i$ with $R_i=\pi_i(K)$, and cosets $A_iz_i$ with $A_i\le H_{C_i}$,
   > compute $K\cap\prod_iA_iz_i$.

   It also costs $\mathrm{poly}(N)$ per instance for bookkeeping.

*Proof.* Let $h=g|_B$ with $g\in G$ and $B^g=B'$. Then $h\in\mathrm{Iso}(B,B')$ iff the string
condition holds on every $C_i$. That condition depends only on $g|_{C_i}$. Moreover
$g|_{C_i}\in\mathrm{Iso}(C_i,C_i^g)$ iff the condition holds on $C_i$: for "if", take $g$ itself;
for "only if", any $g'$ with the same restriction transports $x|_{C_i}$ identically.

Group $h$ by its induced bijection $\sigma$; those $h$ form the coset $K_Bh_\sigma$. Translate by
$h_\sigma^{-1}$ to get the PCI form. Each $a_i(h_\sigma|_{C_i})^{-1}$ lies in $H_{C_i}$, because
$G_{C_i}\le G_B$.

For the count: $|\mathfrak B_{j+1}|\ge2|\mathfrak B_j|$ and $|\mathfrak B_h|=N$, so
$\sum_j|\mathfrak B_j|\le2N$. ∎

**What this achieves.** Luks, GNS and HJ pay the primitive quotient (or giant step) at a block
*once per branch that reaches it*, so costs multiply down the hierarchy. The DP pays it *once
per block pair*, so costs add. The number of distinct sub-instances is $O(N^2)$, which settles
the task's "only $f(d)\,\mathrm{poly}(n)$ types?" question **[PROVEN]**. **The difficulty is not
the number of types; it is entirely in PCI.**

### 4.2 Using $q\le d$

In the DP, a giant quotient $P_B$ with alternating or symmetric socle of degree $q\le d$ (natural
or Johnson action on $\binom qt$ children) can simply be **enumerated**: $|P_B|\le d!$ per block
pair, additively.

**[PROVEN]** So for groups whose primitive components are all giants of degree $\le d$ or have
order $\le f(d)$ (for example tree groups of node degree $\le d$), the *entire* giant/branching
channel of R\* costs only $d!\cdot4N^2$ in the DP. Everything left is PCI.

Product-action quotients $(A_m^{(t)})^k\rtimes K_{\rm top}$ are not covered: their order is not
$f(d)$-bounded. They need the product treatment of §3.2 or GNS-style unfolding into a tree.

### 4.3 Theorem E: bounded entanglement is FPT

For a block $B$ let the **entanglement index** be $\varepsilon_B:=|\prod_i\pi_i(K_B):K_B|$, and let
$\varepsilon(G)=\max_B\varepsilon_B$ over the blocks of $\mathcal T$, including the virtual root.
It does not depend on any ordering of the children. $\varepsilon_B=1$ iff $K_B$ is the full
direct product of its projections.

**Theorem E.** **[PROVEN]** Let every primitive component of $\mathcal T$ have order
$\le\pi_0$. Then $\mathrm{SI}(G,x,y)$ is solvable in $\pi_0\cdot\varepsilon(G)\cdot\mathrm{poly}(N)$.
For tree groups of node degree $\le b$ (subgroups of iterated wreath products of $S_b$ acting on
leaves) this is $b!\,\varepsilon\,\mathrm{poly}(N)$.

*Proof.* By Prop. 4.1 it suffices to solve PCI, $K\cap\prod_{i\le r}A_iz_i$, in
$r\,\varepsilon\,\mathrm{poly}(N)$.

*Notation.*
* $R_i=\pi_i(K)$. Since $G_{C_i}\le G_B$ normalizes $K_B$, $R_i\trianglelefteq H_{C_i}$.
* $K_{\ge i}=\{k\in K:\pi_j(k)=1\ \forall j<i\}$ (a pointwise stabilizer), and
  $M_i=\pi_i(K_{\ge i})\trianglelefteq R_i$.
* $K_{\ge i}/K_{\ge i+1}\cong M_i$, so $|K|=\prod_i|M_i|$ and $\prod_i|R_i:M_i|=\varepsilon_B$.
  In particular $|R_i:M_i|\le\varepsilon_B$.

*Iteration.* Start with $L_0w_0=K$. For $i=1,\dots,r$ compute
$L_iw_i=\{k\in L_{i-1}w_{i-1}:\pi_i(k)\in A_iz_i\}$. The group part
$L_{i-1}=\{k\in K:\pi_j(k)\in A_j,\ j<i\}$ contains $K_{\ge i}$, so $X:=\pi_i(L_{i-1})$ satisfies
$M_i\le X\le R_i$. Put $\zeta=\pi_i(w_{i-1})$. Step $i$ has three parts.

1. *Normal part.* $w_{i-1}\in K$, so $\zeta\in R_i$ and $X\zeta\subseteq R_i$, with
   $R_i\trianglelefteq H_{C_i}$. Compute $A_iz_i\cap R_i=(A_i\cap R_i)\,a^*z_i$ or $\varnothing$. This is the intersection with a
   normal subgroup plus constructive membership in $A_iR_i$, both polynomial (Luks 1993;
   Seress 2003, ch. 6) [standard toolkit]. Write the result as $Yw$ with $Y=A_i\cap R_i$.
2. *Bounded part.* Put $c=w\zeta^{-1}\in R_i$. Then $X\zeta\cap Yw=\{yw: y\in Y,\ yc\in X\}$.
   * If $y,y'$ both qualify, then $y'y^{-1}\in X\cap Y=:Y_0$, so the solution set is one coset
     $Y_0y_jw$.
   * $|Y:Y_0|=|YX|/|X|\le|R_i:X|\le|R_i:M_i|\le\varepsilon$.
   * Membership in $Y_0$ is membership in $X$ (Schreier–Sims). So a transversal of $Y_0$ in $Y$
     and generators of $Y_0$ come from Schreier's lemma with $\le\varepsilon$ cosets (ADKT
     Thm 1). Testing $y_jc\in X$ for each representative takes $\varepsilon\cdot\mathrm{poly}$.
3. *Lift.* $Y_0\le X=\pi_i(L_{i-1})$. So $L_i=\langle\ker(\pi_i|_{L_{i-1}}),\text{lifts of generators of }Y_0\rangle$
   and $w_i=\ell\,w_{i-1}$, where $\pi_i(\ell)=y_jc$. The kernel is a pointwise stabilizer;
   lifts are constructive membership for a restriction homomorphism (Schreier–Sims with a base
   starting in $C_i$).

After $r$ steps, $L_rw_r=K\cap\prod_iA_iz_i$. ∎

**Instances.**
* $\varepsilon=1$: iterated wreath products of primitive groups of degree $\le b$, and every
  "wreath-closed" group. This gives $b!\,\mathrm{poly}(N)$, including the GI-gadget family
  $\mathcal W_L$ of §3.3.
* Parity-type entanglement (kernel $=\{k\in\prod R_i:\prod\phi_i(k_i)=1\}$ with $\phi_i:R_i\to C_2$):
  $\varepsilon_B=2$.
* **[SKETCH]** If each $R_i/M_i$ is abelian of any order, step 2 becomes linear algebra in an
  abelian quotient. That needs abelian-quotient computations for permutation groups (Kantor–Luks
  1990) [TRUST], so arbitrary *abelian* entanglement is also polynomial.

**Novelty.** Prop. 4.1 is the block-hierarchy version of ADKT/Luks-1999 dynamic programming. I
found Theorem E and the parameter $\varepsilon$ in none of the sources of §8. The proof is
elementary and the $\varepsilon=1$ case is folklore-level. I would not call Theorem E deep; its
value is that it **locates** the multiplicative cost precisely in large non-abelian entanglement.

### 4.4 The core problem: coset intersection for tree groups

**Proposition 4.2.** **[PROVEN]** For tree groups of node degree $\le b$ on $N$ leaves:
$$\mathrm{SI}(b,N)\ \le\ 4N^2\,b!\cdot\mathrm{CI}(b,N),\qquad \mathrm{CI}(b,N)\ \le\ \mathrm{SI}(b,N^2).$$
Hence string isomorphism for tree groups is FPT in $b$ iff coset intersection is.

*Proof.*

(⇒) By Prop. 4.1, with $|P_B|\le b!$. Each PCI instance intersects two tree groups on
$\mathcal T_B$: $K_B$, and $\prod_i\mathrm{Aut}(C_i)$, which fixes every child and is a tree group
on $\mathcal T_B$.

(⇐) Let $G_1a\cap G_2c$ with $G_1,G_2\le\mathrm{Aut}(\mathcal T)$.
* $(G_1\times G_2)(a,c)$ acts on pairs of leaves. Pairs of equal-depth nodes, with an interleaved
  refinement (first split the left coordinate, then the right), form a tree of node degree
  $\le b$ with $N^2$ leaves. $G_1\times G_2$ preserves it.
* $(g_1,g_2)$ maps the diagonal $\{(\omega,\omega)\}$ to itself iff $g_1=g_2$, because the action
  on leaves is faithful.
* So $G_1a\cap G_2c$ is the transporter of the diagonal indicator string: a coset instance of SI,
  which translates to a group instance in the usual way. ∎

So the task's "make giant branching additive" reduces, for tree groups (the cleanest home of the
branching channel: no large primitive pieces at all), to an FPT algorithm for coset
intersection of tree groups. Known solvable cases:
* bounded entanglement (Thm E);
* bounded orbits on a small faithful domain (ADKT Thm 5);
* abelian entanglement (Thm E sketch).

Luks gives $N^{O(b)}$; HJ+(M′)'s analysis gives $N^{O(\log b)}$. I found no statement of this
tree-group question in the literature.

### 4.5 Other attacks and exactly where they break

| idea | needed lemma | result | breaks at |
|---|---|---|---|
| **Potential amortization** | an FPT potential $C\log N+g(d)$ paying every charged step | Obs. 2.1: needs polynomial-in-$q$ shrink for every $q^{\Omega(1)}$-branching step | the same-domain or constant-fraction rows of §2.1 (σ, cap, algebraically affected, large symmetry, $\rho$). To remove them, giant breaking would have to shrink polynomially, which for $q=n$ is the memo's "polynomial-shrinking Split-or-Johnson" and would beat the 1978–80 bounds for conference graphs and Latin squares. |
| **Canonization instead of cosets** (Babai 2019, Schweitzer–Wiebking) | the canonical form of a parent is a function of the children's canonical forms | true for $\varepsilon=1$ (sort the children's forms); **[PROVEN]** false in general: for a diagonal kernel $\{(h,h)\}$ the parent's form depends on the *joint* orbit of $(x_1,x_2)$ under $H$, not on the two separate forms | entanglement, the same place as PCI |
| **Memoizing types** | $f(d)\,\mathrm{poly}(n)$ sub-instances | **[PROVEN]** $O(N^2)$ block-pair sub-instances (Prop. 4.1) | combining them is PCI |
| **DP over the inherited hierarchy** | additive giants | **[PROVEN]** Prop. 4.1, §4.2 | PCI; product-action quotients of unbounded arity |
| **$q\le d$** | afford $q!$ per giant | **[PROVEN]** in the DP (§4.2) | in no-memo recursion, $q!$ (or $q^{\log q}$) compounds over $\log_qN$ levels (§3.3) |
| **Diagonal kernels via product alphabets** | for $K=\{(h,\dots,h)\}$, solve one child with $r$-tuple strings | correct, and shrinks the domain by $r$ | with a giant $P_B=S_r$ on top, each $\sigma$ gives a *different* tuple string: $r!$ non-memoizable child problems. This is **set-of-strings isomorphism** on the child (Neuen's SSI), for which no fpt reduction to SI is known. Iterating gives $S_b^L$ on $[b]^L$, which ADKT does solve, because the diagonal kernel has bounded orbits on a small faithful domain. |

---

## 5. Intermediate targets

* **Polynomial for $d=O(\log n)$.** Not achieved. Prop. 3.1 with $D\approx\log n$ shows that
  HJ+(M′) is $n^{\Omega(\log\log n)}$ at the string level. Any route must avoid enumerating
  affine product-action quotients, which §3.2 does (FPT), and must solve PCI. For tree groups of
  node degree $O(\log n/\log\log n)$ with bounded (or abelian) entanglement, Thm E gives
  polynomial time **[PROVEN]**. That class is artificial.
* **$n^{O(\log d/\log\log d)}$.** Impossible for HJ+(M′) (Cor. 3.2). No other route found.
* **FPT subclasses.** Theorem E: tree groups with bounded entanglement (node degree $\le b$:
  $b!\,\varepsilon\,\mathrm{poly}$), plus the abelian-entanglement sketch. Prop. 3.3: product
  actions of bounded-degree factors with a top group of polynomial order. ADKT: bounded orbits.
* **"Bounded-degree graphs whose automorphism groups have bounded alternating width."** I found
  no handle. The groups that matter are the intermediate Luks-tower groups $\mathrm{Aut}_e(X_r)$,
  not $\mathrm{Aut}(X)$, and $\mathrm{aw}$ bounds do not control entanglement. For $d\le q_0$
  there are no giants anyway, and the cost is pure enumeration and entanglement.
  **[SPECULATION]**: a graph-side parameter that bounds $\varepsilon$ of the tower, such as
  "each new BFS layer is attached through vertex sets with boundedly synchronized subtrees", is
  the right kind of hypothesis. I did not find a natural one.

---

## 6. Leads for a follow-up agent (ranked)

1. **Coset intersection for tree groups (Prop. 4.2), with node degree $b$.** This is the cleanest
   FPT question for the branching channel.
   * The smallest unresolved family is the **product action of $L$ copies of a depth-$h$ tree
     group**, $T_{b,h}^{\,L}$ on $\mathrm{Leaves}^L$ with $h,L\to\infty$. Here:
     * ADKT costs $2^{O(b^h)}$;
     * Theorem E fails because $\varepsilon$ is huge (diagonal);
     * Luks costs $N^{O(b)}$ and HJ+(M′) $N^{O(\log b)}$.

     Already $L=2$ (a matrix with tree-structured rows and columns) is equivalent to tree-group
     CI.
   * Try halving along the tree, à la ADKT's restricted set stabilizer. Naive tree-aligned
     halving costs $f(b)$ per halving and compounds over $h\log b$ halvings. A real idea is
     needed.
   * Conversely, an adversary argument showing that every *coset-splitting* strategy needs
     $N^{\Omega(\log b)}$ on this family would be the first lower bound for a group-theoretic
     model.
2. **Plug Prop. 3.3 into the dispatcher (coordinate with w1-structure).**
   * The dispatcher should recognize product-action primitive quotients $P\wr K$ with
     $\deg P\le f(d)$ and solve them by the prefix DP, not by enumeration.
   * **[SPECULATION]** Every primitive $\hat\Gamma_d$ group of order $>d'^{C}$ is, up to bounded
     index, inside such a product action, or tensor-induced with small order. For affine groups
     this is the imprimitive-linear case; Aschbacher-type analysis should give it.
   * Combined with Prop. 4.1 this would make the **enumeration channel** additive. The giant
     channel would remain.
3. **Measure $\varepsilon$ on real Luks towers.** Compute $\varepsilon_B$ for $\mathrm{Aut}_e(X_r)$
   on the campaign's bounded-degree families: CFI, multipedes, Johnson gadgets, random regular.
   If it is small or abelian in practice, Theorem E is a practical algorithm too. This is cheap
   to prototype in `gi-practical`, but it was **not run here** because of the CPU rule.
4. **Transfer Prop. 3.1 to graphs.** Does some degree-$\mathrm{poly}(D)$ graph family make the
   Babai–Luks reduction hand HJ+(M′) a section $P_d^m$?
   * The halved $D$-cube realizes $P_d$ as an automorphism group at degree $\binom D2$ (I believe
     its full automorphism group is $2^{D-1}{:}S_D$ for $D\ge5$; not checked), and CFI gadgets
     realize it at degree $2^{D-2}$.
   * Product actions need unbounded arity, so this may fail. If it fails, that is evidence for a
     *negative* answer to Q4.8: degree-$d$ GI may be strictly easier than string isomorphism
     for $\hat\Gamma_d$. **[SPECULATION]**
5. **Set-of-strings isomorphism.** §4.5 shows SSI on a child is exactly the combine problem for
   diagonal kernels with giant tops. An fpt reduction SSI → SI (open, survey §4.1) would plug
   into Prop. 4.1.

---

## 7. Ledger

| item | status |
|---|---|
| FPT open, no W-hardness, no group-theoretic lower bounds | literature, §1 |
| Prop. 3.1, Cor. 3.2 (HJ+(M′) $\ge N^{\log_2D-0.45}$; GNS 3.13 sharp at fixed $d$) | **[PROVEN]**; GI transfer not claimed |
| Prop. 3.3 (family is FPT) | **[PROVEN mod ADKT Thm 5]** |
| small-faithful-degree remark | **[PROVEN mod Luks 1999]** |
| §3.3 compounding reduction / HJ compounding | **[PROVEN]** / **[CONDITIONAL + SKETCH]** |
| Obs. 2.1 accounting | **[PROVEN]** |
| Prop. 4.1 (DP, $O(N^2)$ types, combine = PCI) | **[PROVEN]** |
| Theorem E | **[PROVEN]** (standard toolkit incl. normal-subgroup intersection) |
| abelian entanglement | **[SKETCH]** (Kantor–Luks) |
| Prop. 4.2 (SI ⇔ CI for tree groups) | **[PROVEN]** |
| FPT for $\hat\Gamma_d$ or for degree-$d$ GI | **not achieved** |

---

## 8. Sources

Read in full or in the relevant parts:
* HJ LaTeX: L1136–1215, L1365–1367, L1755–1780, L3060–3095.
* `moonshot-theory.md`, `verify-theorem-R.md`, `redteam-theorem-R.md`.
* GNS v3 source: Thm 3.13, Rem. 3.14, conclusion.
* Neuen 2002.06997 source: conclusion.
* Neuen 2026 survey, text: §1, §4.1, Q4.8.
* Grohe–Neuen 2011.01366, text: §4.4, open questions.
* **ADKT, ECCC TR09-093 rev. 1** (new download: `r4-sources/w1fpt-adkt/`), read in full.

Abstracts or search results only:
* Neuen–Schweitzer arXiv:1705.03283;
* Otachi–Schweitzer arXiv:1403.7238;
* Schweitzer–Wiebking arXiv:1806.07466;
* Arvind–Köbler–Kuhnert–Torán (STACS'17, IPEC'17);
* Luks STOC'99 (via ADKT and Schweitzer–Wiebking);
* arXiv:2407.17947.

Cited from memory: Dixon–Mortimer, *Permutation Groups*, Lemma 2.7A; the $\mathbb F_2S_n$
permutation-module submodule lattice; Luks 1993 (DIMACS) and Seress 2003 for intersection with a
normal subgroup; Kantor–Luks 1990 (quotient groups); Cai–Fürer–Immerman 1992; Berkholz–Grohe
ICALP'15; Torán (resolution lower bounds on CFI).
