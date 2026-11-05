# w10-blackbox: the black box in Grohe–Neuen–Schweitzer, and the exponent c

Branch `w10-blackbox`, 2026-11-05. Wave 10. Not refereed, not red-teamed. No Lean was run. The only
computation is `docs/w10-blackbox-check.py` (standard library, about 4 s at `nice 19`): exponent
arithmetic and three elementary probability bounds.

**Labels.**
* **[PROVEN]**: a complete argument is given here. It relies only on the published results and
  repository results listed in §8.
* **[SKETCH]**: the argument is given and its gaps are named.
* **[CONDITIONAL: …]**: proven or sketched under the named hypothesis.
* **[SPECULATION]**: an opinion.

**Notation.** As in `docs/w8-gnsexp.md` ("w8").
* $L:=\log_2(d+2)$, $\ell:=\log_2 n$, regimes $\ell=L^x$ with $x\ge1$. "Exponent $c$" means time
  $n^{O(L^c)}$.
* "G L…" is a line of GNS's `bounded-degree-polylog-d.tex` (arXiv:1802.04659v3); "HBD L…" a line of
  Helfgott–Bajpai–Dona `BDHv8.tex` (arXiv:1710.04574); "B L…" a line of Babai's `main.tex`
  (arXiv:1512.03547).
* CB is `docs/canonization-bounded-degree.md`. B–H is Babai's algorithm with Helfgott's analysis,
  $\exp(O(\log^3 N))$ on $N$-vertex graphs.
* Theorem C, Lemma A and Prop. B are w8's (red-teamed in `docs/redteam-w8-gnsexp.md`). Theorem C:
  GNS's algorithm with the CB §7.3 fix runs in $n^{O(L^3)}\cdot(1+X(d))$, where $X(d)$ is the cost of
  one black-box call. Its almost-$d$-ary part: an instance on $N$ points with an almost $d$-ary
  sequence costs $N^{O(L^2)}\cdot(1+X)$.
* The **black box** is the call to Babai's isomorphism test in GNS Lemma 6.7 (G L1998–2029).
* $k$ is the giant degree at a GNS node, and $t:=\max\{9,3+\log_2 d\}$ (G L2100). For a structure,
  $m$ is its number of points.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | What does the black box decide? | Only GNS's case (v) is expensive. The input is two $t$-ary structures on $m>3k/4>7.5t$ points: every injective $t$-tuple is coloured by its comparison class, and the colours are named jointly for both strings. Downstream only needs the child coset to have no $\mathrm{Alt}(\Delta)$ with $\lvert\Delta\rvert>3k/4$ in its $\varphi$-image (Prop. B), so any canonical relaxation of $\mathrm{Iso}$ with that property would do. | [PROVEN] (§1.1–1.2) |
| 1′ | Can it be made binary? | **Not canonically.** There are instances in which the structure's automorphism group contains $\mathrm{PSL}(2,q)$, which is 2-transitive. Then every isomorphism-invariant binary (or 2-skeleton, or coherent-configuration) relaxation is trivial. Lowering the arity needs individualization, i.e. Babai's Design Lemma, at $k^{<t}=2^{\Theta(L^2)}$ branches. | [PROVEN] for GNS string-isomorphism instances (§1.3) |
| 2 | HJ as the black box | **Works but adds nothing.** The encoding is a graph on $M\le m^{2t}\mathrm{poly}(L)$ vertices, so $\log M=O(L^2)$ and the black box costs $2^{O(L^4)}$; the arity blow-up does not kill the gain. That gives $c=3$ for all $d$. But HJ applied to the whole input, together with the unconditional bound for $\log n\ge\log^3 d$, already gives $n^{O(\min(\log^3 d,\log n))}$, which is never worse. | [CONDITIONAL: HJ Lean `main_theorem`, 10 axioms] (§2) |
| 2′ | Does the Lean development state HJ Thm 1.2 (string isomorphism)? | Only at "stage 1": `GI.Paper.thm_main_string_stage1` covers the abstract recursion and carries hypotheses (`Supply`, `NodeBound`, `RootsOK`). Only the graph pair state discharges them. The machine-level verified statement is GI only. | checked by reading (§2.1) |
| 3 | **Black box in $2^{O(\log^5 d)}$, so $c=10/3$** | **Theorem X:** one Design-Lemma/Split-or-Johnson round on the structure, then GNS's own algorithm on the reduced instance (an almost $m$-ary instance on $m^t$ points). That algorithm's black-box calls are on $\le\frac34 m$ points. So $X(m,t)\le2^{O(t\log^3m)}X(\tfrac34m,\cdot)$, which unrolls to $2^{O(t\log^3 m+\log^5 m)}$. Hence degree-$d$ GI is in **$n^{O(\log^3 d)}\cdot2^{O(\log^5 d)}$**: $c=10/3$ for all $d$, and $c=3$ when $\log n\ge\log^2 d$. This makes w8's sketched 10/3 rigorous by a different route. | [PROVEN] (§3) |
| 4 | **No black box at all: $c=3$ for all $d$** | **Theorem G:** use the Design Lemma and Split-or-Johnson inside GNS's macro step, and charge their $2^{O(L^2)}$ branching to a hereditary tower potential (HBD's $\rho\le2\log N$) instead of resetting it every macro step. Each such round shrinks the domain by a factor $5/6$, inserts a tower level ($\rho$ drops by 1), or is a Johnson step ($k\to O(\sqrt k)$). This gives $N^{O(L^2)}=n^{O(L^3)}$. | [SKETCH] (§4) |
| 5 | Best bounds | Unconditional: **$c=10/3$ [PROVEN]**, **$c=3$ [SKETCH]**. Conditional on HJ's Lean theorem: $c=3$, and in fact $n^{O(\min(\log^3d,\log n))}$. The barrier "$c<2$ beats general GI" is unchanged; $c=3$ is the floor of GNS's architecture, and Theorem G reaches it. | §5 |
| 6 | Novelty | No explicit cost of the black box, and no analysis of the Design-Lemma variant, is in GNS, Neuen 2020, the 2021/2026 surveys, Pago or Wiebking. The 2021 survey names the option (G–N survey L1253: one "can simply rely on using Babai's algorithm as a black box instead" of the combinatorial subroutines) without analysing it. Theorems X and G and the HJ redundancy observation appear new. Neuen's thesis is still unread. | §6 |

**Exponent ladder (unconditional), extending w8's table.**

| version | black box | worst exponent over $d$ | exponent 3 when | label |
|---|---|---|---|---|
| GNS + count + B–H switch | $2^{O(L^6)}$ (B–H) | 4 | $x\le1.5$ | [PROVEN] (w8) |
| + Lemma A / Prop. B (w8 Theorem C) | $2^{O(L^6)}$ | 4 | $x\le1.5$ or $x\ge3$ | [PROVEN] (w8, red-teamed) |
| + Theorem X (this memo) | $2^{O(L^5)}$ | **10/3** | $x\le1.5$ or **$x\ge2$** | [PROVEN] |
| Theorem G (this memo) | none | **3** | all $x$ | [SKETCH] |
| HJ black box, or HJ switch | $2^{O(L^4)}$ | 3 | all $x$ (and $x$ itself when $x<3$) | [CONDITIONAL: HJ Lean] |

The profile is $\min\{\max(3,a-x),2x\}$ for a black box costing $2^{O(L^a)}$ (check script, part 1). So
$a\le4.5$ already suffices for $c=3$ for all $d$; $a=5$ gives $10/3$ at $x=5/3$.

---

## 1. What the black box decides (Task 1)

### 1.1 The call and its inputs

GNS Lemma 6.7 (G L1998–2029). Given the aggregation outcome "Option 1", with structures
$\mathfrak A_{i,j}$ ($i\in[2]$, $j\le r\le k^6$), it forms
$$H_jh_j=\{g\in G:\ D_1^{\varphi(g)}=D_{2,j},\ \varphi(g)|_{D_1}\in\mathrm{Iso}(\mathfrak A_1,\mathfrak A_{2,j})\}$$
and recurses on these $r$ subcosets. GNS: "the only place where we use Babai's quasipolynomial time
isomorphism test as a black box" (G L2029). Neuen 2020 copies this (`hypergraph-gamma-d.tex` L2621).

The structures come from GNS App. A (G L2330–2385). Let $F_i$ be the group generated by the fullness
certificates and $S_i$ the support of $F_i^\varphi$.

| case | condition | structure | cost of Iso |
|---|---|---|---|
| (i) | $k/4\le\lvert S_i\rvert\le3k/4$ | unary: the colouring $\{S_i,[k]\setminus S_i\}$ | polynomial |
| (ii) | $\lvert S_i\rvert>3k/4$, no $F_i^\varphi$-orbit $\ge3k/4$ | unary partition into $F_i^\varphi$-orbits | polynomial |
| (iii) | giant on an orbit $\ge3k/4$ | Option 2; no structure | — |
| (iv) | orbit $C\ge3k/4$, $F_i^\varphi$ transitive non-giant on it | after $\le4$ points, one orbital and one vertex are individualized ($\le k^6$ choices): a non-trivial regular graph on $C'$, or a 2-colouring | binary on $\le k$ points: B–H $2^{O(\log^3k)}$ |
| (v) | $\lvert S_i\rvert<k/4$ | **the comparison structure** (below) | B–H on Miller's graph with $k^{O(t)}$ vertices: $2^{O((t\log k)^3)}=2^{O(L^6)}$ |

**Case (v) precisely.** Put $D_i:=[k]\setminus S_i$, so $m:=\lvert D_i\rvert>3k/4>7.5t$. Every $t$-subset
of $D_i$ is non-full.
* The morphisms of GNS's category $\mathcal L$ are the cosets $M\sigma$ that Lemma 6.3 returns for pairs
  of test sets (G L1866–1880).
* Their equivalence classes $R_1,\dots,R_r$ partition the injective $t$-tuples of
  $D_1'\sqcup D_2'$. They are named **jointly**: $R_j(1)$ and $R_j(2)$ are the parts of one class.
* $\mathfrak A_i=(D_i';R_1(i),\dots,R_r(i))$. There is one structure per string, so $r=1$ in Lemma 6.7.

Facts used below:
* **(P1)** Every injective $t$-tuple of $D_i$ gets exactly one colour, and at most $2m^t$ colour names
  occur.
* **(P2)** For a $t$-set $T\subseteq D_i$, two orderings of $T$ share a colour iff they differ by an
  element of the non-giant group $M_T\le\mathrm{Sym}(T)$ of Lemma 6.3.
* **(P3)** If $\mathrm{Alt}(\Delta)\le\mathrm{Aut}(\mathfrak A_i)$ then $\lvert\Delta\rvert\le t+1$
  (CB Lemma T′.3; GNS state $\le t-1$, G L2383). In particular every twin class (a maximal set
  $\Delta$ with $\mathrm{Sym}(\Delta)\le\mathrm{Aut}$) has size $\le t+1<m/7$.
* **(P4)** Canonicity: $\mathfrak A(x^h)=\mathfrak A(x)^{\varphi(h)}$ (CB Lemma T′.1; GNS Lemma 6.6).
  Hence $\varphi(\mathrm{Aut}_H(x))|_{D}\le\mathrm{Aut}(\mathfrak A(x))$.

### 1.2 What the rest of the algorithm needs from the call [PROVEN]

The child coset enters the analysis only through Prop. B: the next giant satisfies $k'\le3k/4$,
because the child's $\varphi$-image contains no $\mathrm{Alt}(\Delta)$ with $\lvert\Delta\rvert>3k/4$.
GNS's own index bound $(4/3)^k$ also follows from this (Cor. 6.5).

So $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_{2,j})$ may be replaced by any family
$\{\mathrm{Rel}(\mathfrak A_1,\mathfrak A_2)\}$ with these properties:
* it is a union of at most $\mathrm{poly}(k)$ cosets of a single group $R\le\mathrm{Sym}(D_1)$;
* it contains $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$;
* $R$ contains no $\mathrm{Alt}(\Delta)$ with $\lvert\Delta\rvert>3k/4$.

The bound $\mathrm{poly}(k)$ keeps the outer branching at $d^{O(1)}$ per level, which Theorem C needs.

*Proof.* w8 Prop. B uses only this property of $\varphi(R)$, through Lemma A (red-team §3.1–3.2).
Correctness only needs $\mathrm{Iso}\subseteq\bigcup\mathrm{Rel}$. ∎

### 1.3 Arity cannot be lowered canonically [PROVEN for GNS string-isomorphism instances]

**Proposition 1.3.** There are instances of string isomorphism under $\hat\Gamma_d$ groups on which
GNS's algorithm reaches case (v) with $D=[k]$ and $\mathrm{Aut}(\mathfrak A)\ge\mathrm{PSL}(2,q)$,
$k=q+1$. For these:
* every isomorphism-invariant binary structure on $D$ computed from $\mathfrak A$ is trivial, i.e. has
  one off-diagonal colour;
* in particular the 2-skeleton of any Weisfeiler–Leman refinement of $\mathfrak A$ is trivial;
* the automorphism group of any such relaxation is $\mathrm{Sym}(D)$, so §1.2's requirement fails.

*Proof.* Let $q$ be a large prime power, $k=q+1$, $d=k$, and $t=\max\{9,3+\log_2 k\}$.
* *The instance.* Let $B$ colour each injective $t$-tuple of $\mathbb P^1(\mathbb F_q)$ by its
  $\mathrm{PGL}(2,q)$-orbit. Take $G=\mathrm{Sym}(k)$ acting on $\Omega=[k]^{\langle t\rangle}$, which
  is a $\hat\Gamma_k$ group with the almost $k$-ary coordinate sequence, and strings $x_1=x_2=B$.
* *The top node.* $\mathfrak B_1$ is the first coordinate, and $P=S_k$ is natural and large. Lemma 7.1
  gives $N\in\{A_k,S_k\}$ and $\varphi$ the identity on $[k]$. For large $q$ we have $k>10t$, so the
  node aggregates.
* *No test set is full.* $\mathrm{Aut}_{G_T}(x)=\mathrm{PGL}(2,q)_{\{T\}}$. An element of
  $\mathrm{PGL}(2,q)$ is determined by the images of 3 points, which must lie in $T$. So
  $\lvert\mathrm{PGL}(2,q)_{\{T\}}\rvert\le t^3<t!/2$. Hence $F=1$, $S=\emptyset$, and we are in case
  (v) with $D=[k]$.
* *The automorphism group.* By (P4), $\mathrm{Aut}(\mathfrak A)\ge\varphi(\mathrm{Aut}_{G'}(x))\ge\mathrm{PGL}(2,q)\cap A_k\ge\mathrm{PSL}(2,q)$,
  which is 2-transitive on $\mathbb P^1$.
* *Conclusion.* An isomorphism-invariant binary structure $Y$ computed from $\mathfrak A$ satisfies
  $\mathrm{Aut}(Y)\ge\mathrm{Aut}(\mathfrak A)$. A 2-transitive group has only two orbitals, so $Y$
  has one off-diagonal colour. ∎

*Remarks.*
* The same holds for every $\mathrm{poly}(k)$-size family produced without individualization, since
  the family is permuted by $\mathrm{Aut}(\mathfrak A)$.
* Individualizing 3 points kills $\mathrm{PSL}(2,q)$ here. In general, Babai's Design Lemma (HBD Prop.
  `design`, L1354) needs up to $t-1$ individualized points.
* Whether $O(1)$ individualizations always suffice for case-(v) structures is open (§7, lead 1).
  If they did, the black box would become binary ($2^{O(L^3)}$) at $\mathrm{poly}(k)$ outer branching,
  and $c=3$ would follow from Theorem C directly. [SPECULATION]
* The canonical-subcoset device of CB §4 only makes choices canonical. It computes the same $t$-ary
  colours (CB Lemma T″) and does not lower the arity. Coherent configurations give the $t$-ary WL
  closure, whose 2-skeleton is trivial in this example.

So arity reduction costs $k^{<t}=2^{\Theta(L^2)}$ branches.
* Inside the black box this cost is additive per outer node, which is affordable (Theorem X, §3).
* In the outer recursion it is multiplicative. w8's per-macro-step accounting turns it into $c=4$
  (w8 §5); a hereditary potential turns it into $c=3$ (Theorem G, §4).

---

## 2. HJ as the black box (Task 2)

### 2.1 What is verified

From `/home/bepis/math/GraphIsomorphismLog2`, read only:
* **The verified statement.** `Challenge.lean`'s `main_theorem` is
  `GI.Statement.GraphIsomorphismInQuasipolynomialTime` (`Workspace/Statement/Main.lean`). There is one
  program $p$ and one constant $C$ such that, on the adjacency matrices of two simple graphs on $n$
  vertices, $p$ outputs whether they are isomorphic, plus one isomorphism and generators of
  $\mathrm{Aut}(G)$. Its cost on a log-cost RAM is at most $\exp(C\log^2(n+2))$.
* **The axioms.** Ten literature axioms, all CFSG-based (`AXIOMS.md`): six structural ones and four
  polynomial-time permutation-group algorithms.
* **HJ Thm 1.2 (string isomorphism).** It appears as `GI.Paper.thm_main_string_stage1`
  (`Workspace/Paper/MainTheorem.lean` L138–168), a statement about the abstract recursion
  `GI.Algorithm.Run`. Its hypotheses are `Supply P`, `NodeBound w cw af` and root bounds `RootsOK`,
  and its cost bound holds only for runs with root bounds.
  * The assembly discharges these only for the graph pair state (`Workspace/Assembly/Build.lean`,
    `graphState`; `Assembly/Main.lean`).
  * So **the only verified black box is GI on uncoloured graphs.** String isomorphism under a group
    given by generators is not known to reduce to GI, so HJ's verified statement cannot replace
    GNS's string-isomorphism recursion.

### 2.2 Encoding the black box as GI [PROVEN]

**Proposition 2.2.** Let $\mathfrak A_1,\mathfrak A_2$ be case-(v) structures: $t$-ary on $m$ points,
with $R\le2m^t$ joint colour names. There are uncoloured graphs $\Gamma_1,\Gamma_2$ with the following
properties.
* They have $M\le m^{2t}\cdot(t\log m)^{O(1)}$ vertices.
* They are computable in time polynomial in $M$.
* Restricting graph isomorphisms to a canonically recognizable vertex set $V_E\cong D_i$ maps
  $\mathrm{Iso}(\Gamma_1,\Gamma_2)$ onto $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$, and
  $\mathrm{Aut}(\Gamma_1)$ homomorphically onto $\mathrm{Aut}(\mathfrak A_1)$.

*Construction.*
* *A vertex-coloured graph.* Let $B:=\lceil\log_2(R+1)\rceil\le t\log_2m+2$. The vertices are:
  * element vertices $v_a$ ($a\in D_i$), with colour E;
  * for each injective tuple $\tau$, a tuple vertex $w_\tau$ (colour T);
  * ports $p_{\tau,j}$ (colour $P_j$, $j\le t$), with edges $w_\tau p_{\tau,j}$ and $p_{\tau,j}v_{\tau_j}$;
  * code vertices $q_{\tau,b}$ ($b\le B$), with colour $Q_b^{\beta}$ where $\beta$ is bit $b$ of the
    colour index of $\tau$, and edges $w_\tau q_{\tau,b}$.

  This uses $c_0=2+t+2B$ colours and $M_0=m+m^t(1+t+B)$ vertices, with maximum degree
  $\Delta\le tm^{t-1}+t+B$.
* *Removing the colours.* Attach $\Delta+1+i$ new pendant leaves to each vertex of colour $i$.
  * Original vertices then have degree $\ge\Delta+2$ and leaves have degree 1, so the leaves are
    recognizable.
  * Each original vertex's colour is (number of leaf neighbours) $-\Delta-1$.
  * $M\le M_0(\Delta+c_0+2)\le m^{2t}(t\log m)^{O(1)}$.

*Correctness.*
* An isomorphism preserves colours, so it maps $v$'s to $v$'s, $w$'s to $w$'s, and ports by position.
* Each $w_\tau$ is determined by its ports' element neighbours, so the induced map $\pi$ on $D$ sends
  $\tau$ to $\tau^\pi$.
* The code vertices force $\tau$ and $\tau^\pi$ to have the same colour index.
* Conversely every structure isomorphism extends.
* From HJ's output (one isomorphism and generators of $\mathrm{Aut}(\Gamma_1)$), restriction to $V_E$
  gives $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$ as a coset with generators. ∎

**Corollary 2.3.** [CONDITIONAL: HJ's Lean `main_theorem` and its 10 axioms]
* The black box costs $\exp(C\log^2(M+2))=\exp(O((t\log m)^2))=2^{O(L^4)}$.
* With Theorem C, degree-$d$ GI is in $n^{O(L^3)}\cdot2^{O(L^4)}=n^{O(\log^3 d)}$ for all $d$.

The arity blow-up $N^a$ that the brief worries about is $m^t=2^{O(L^2)}$ here. HJ's exponent is
quadratic in $\log M$, so the encoding costs $L^4$, against $L^6$ for B–H. The gain survives the
encoding.

### 2.4 Why the HJ black box is redundant

**Proposition 2.4.** [CONDITIONAL: HJ's Lean `main_theorem`] Degree-$d$ GI is in
$n^{O(\min\{\log^3 d,\ \log n\})}$, without changing GNS's black box. The black-box route of
Corollary 2.3 is never better.

*Proof.*
* If $\ell\le L^3$, run HJ's program on the whole input: $\exp(O(\ell^2))=n^{O(\ell)}=n^{O(L^x)}$ with
  $x\le3$.
* If $\ell\ge L^3$, w8 Theorem C with the B–H black box gives $n^{O(L^3)}2^{O(L^6)}=n^{O(L^3)}$.
* Corollary 2.3 has exponent 3 for every $x$, while this has $\min(3,x)$ (check script, part 1). ∎

So HJ's verified graph theorem, used as an oracle, yields $c=3$ trivially, and the black-box
substitution adds nothing. Going below 3 would require changing GNS's main recursion
($e=1$, $a=2$, w8 §2.7). Its subproblems are string isomorphism under subgroups of $\hat\Gamma_d$
groups, which a GI oracle does not obviously serve. [SPECULATION] Exponents 2 and 1 are available only
through HJ's internals (w8 Corollary F; Theorem R\*), not through its verified statement.

---

## 3. Theorem X: the black box in $2^{O(\log^5 d)}$ [PROVEN]

### 3.1 Statement

Let $X(m,t)$ be the worst-case cost of computing $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$ for pairs
of $t$-ary structures on $\le m$ points that satisfy (P1) and have all twin classes of size
$\le\frac34m$. Case-(v) structures qualify, by (P3) and $t+1<m/7$.

**Theorem X.** [PROVEN, modulo §8]
$$X(m,t)\le 2^{O(t\log^3 m\ +\ \log^5 m)}.$$
In particular GNS's black box costs $X(d)\le2^{O(\log^5 d)}$.

**Corollary X.** [PROVEN, modulo §8] String isomorphism for $\hat\Gamma_d$ groups on $n$ points, and so
GI for graphs of maximum degree $d$, is decidable in time $n^{O(\log^3 d)}\cdot2^{O(\log^5 d)}$. Hence:
* $n^{O(\log^3d)}$ whenever $\log n\ge\log^2 d$, i.e. $d\le2^{(\log n)^{1/2}}$;
* with the B–H switch, $n^{O(\log^{10/3}d)}$ for all $d$, and $n^{O(\log^3d)}$ also when
  $d\ge2^{(\log n)^{2/3}}$.

*Proof of the corollary.* Use Theorem C with $X(d)$ from Theorem X. The exponent is
$\max(3,5-x)$, and $\min\{\max(3,5-x),2x\}\le10/3$, with equality at $x=5/3$ (check script, part 1). ∎

This replaces w8 row 2′ ("$10/3$, [SKETCH]", via a GNS run with the Design Lemma inside the inner
instance). The present route avoids the unverified pairwise use of the Design Lemma inside GNS's
aggregation. The Design Lemma and Split-or-Johnson are used only once per call, on a $t$-ary
structure under the full symmetric group, which is exactly HBD's setting (HBD §`subs:chasche`).

### 3.2 The algorithm BB

Input: $\mathfrak A_1,\mathfrak A_2$ on $D_1,D_2$. If $\lvert D_1\rvert\ne\lvert D_2\rvert$, output
$\emptyset$. Let $m=\lvert D_i\rvert$ and fix $\alpha=\alpha'=3/4$.

0. *Small case.* If $m\le 20t$, try all $m!\le2^{O(t\log t)}$ bijections.
1. *Weisfeiler–Leman.* Apply HBD's functors $F_3F_2F_1$ ($t$-ary WL, HBD L1338) to both structures,
   with one colour-naming scheme. This yields $t$-ary coherent configurations $\mathfrak X_i$ with
   $\mathrm{Aut}(\mathfrak X_i)=\mathrm{Aut}(\mathfrak A_i)$, in time $m^{O(t)}$.
2. *Design Lemma* (HBD Prop. `design`, L1354). Its hypotheses hold: $2\le t\le m/2$, and no twin class
   exceeds $\frac34m$. So there are $\ell<t$ and $\vec x\in D_1^\ell$ such that either:
   * (1) $\mathfrak X^{(1)}_{1,\vec x}$ has no $\frac34$-dominant colour; or
   * (2) it has a dominant class $C$ with $\lvert C\rvert\ge\frac34m$, and
     $\mathfrak X''_1:=\mathfrak X^{(2)}_{1,\vec x}[C]$ is not a clique.

   Take the lexicographically first such $\vec x$ (search $\le m^t$ tuples).
3. *The canonical structure* $Y_1$, relative to individualized points:
   * (1) $Y_1$ := the colouring $\mathfrak X^{(1)}_{1,\vec x}$ of $D_1$. All classes have size $<\frac34m$.
   * (2a) $\mathfrak X_1''$ imprimitive. Use the canonical equipartition of $C$ given by the first
     disconnected colour (HBD L1421): blocks of size $\le\lvert C\rvert/2$, at least 2 blocks. $Y_1$ is
     that equipartition together with the colouring.
   * (2b) $\mathfrak X''_1$ uniprimitive. Split-or-Johnson (HBD Thm `coupjohn`, L1423, with
     $\alpha'=3/4$) individualizes a tuple $\vec z$ with $\lvert\vec z\rvert=O(\log m)$. It yields
     either a coloured $\frac34$-partition of $C$ (blocks of size $\le\frac34\lvert C\rvert$, equal
     within a colour, HBD L486–500), or a Johnson scheme $\mathcal J(r,s)$, $s\ge2$, $r\ge2s+1$, on a
     canonical $\Gamma_0\subseteq C$ with $\lvert\Gamma_0\rvert\ge\frac34\lvert C\rvert$. That scheme is
     identified with the $s$-subsets of an explicit $r$-set $\Lambda$ (HBD §`subs:idgroup`).
4. *The other side.* For every $\vec y\in D_2^\ell$ and every $\vec z'$ of the same length, run the same
   deterministic procedure on $(\mathfrak X_2,\vec y,\vec z')$ to get $Y_2(\vec y,\vec z')$. That is at
   most $m^{t+O(\log m)}$ candidates. Discard candidates of a different type (class sizes, block
   parameters, $(r,s)$). Otherwise compute an aligning bijection $\tau$ with
   $(\vec x,\vec z,Y_1)^\tau=(\vec y,\vec z',Y_2)$.
5. *The reduced instance.* Let $H:=\mathrm{Aut}(Y_1)\cap\mathrm{Sym}(D_1)_{(\vec x,\vec z)}$; it has
   explicit generators. Compute $\mathrm{Iso}_{H\tau}(x_1,x_2)$, where $x_i$ is the colour string of
   $\mathfrak A_i$ on $\Omega:=D^{\langle t\rangle}$.
   * Use GNS's algorithm with parameter $d:=m$, the CB §7.3 fix, and the coordinate sequence
     $\mathfrak B_i$ := "agree on the first $i$ coordinates". This sequence is almost $m$-ary, and
     $H\le\mathrm{Sym}(D)$ lies in $\hat\Gamma_m$.
   * Each case-(v) black-box call of this run is answered by BB recursively.
6. *Combine.* All non-empty results are cosets $\rho_iK$ of the same group
   $K=\mathrm{Aut}_H(\mathfrak A_1)$. Output $\rho_0\langle K,\rho_0^{-1}\rho_i\rangle$, or $\emptyset$.

### 3.3 Correctness

* *Canonicity.* WL, the derived configurations $\mathfrak X_{\vec x}$, the first-disconnected-colour
  rule and the Split-or-Johnson procedure are deterministic functions of (configuration,
  individualized tuple) that commute with bijections. HBD's Split-or-Johnson is "canonical with
  respect to" a pointwise stabilizer.
* Hence every $\pi\in\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$ satisfies
  $Y_2(\vec x^\pi,\vec z^\pi)=Y_1^\pi$, so $\pi$ lies in the candidate $(\vec x^\pi,\vec z^\pi)$. This
  is HBD eq. (`kozron`).
* Conversely, every element of $\mathrm{Iso}_{H\tau}(x_1,x_2)$ is an isomorphism of the structures.
* So $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)=\bigcup_i\rho_iK$.
* This union is a coset of $\mathrm{Aut}(\mathfrak A_1)$ containing $\rho_0K$. Since
  $\rho_0^{-1}\rho_i\in\mathrm{Aut}(\mathfrak A_1)$, it equals $\rho_0\langle K,\rho_0^{-1}\rho_i\rangle$. ∎

### 3.4 The section bound

**Lemma S.** [PROVEN] Let $m$ be at least an absolute constant. If $A_j$ ($j\ge5$) is a composition
factor of a subgroup of $H$, then $j\le\frac34m$.

*Proof.*
* *Reduction.* By Jordan–Hölder through projection–kernel series, a composition factor of a subgroup
  of $\prod_iG_i$, or of $G_1\wr G_2$, is a composition factor of a subgroup of some $G_i$. And
  $A_j$ is a composition factor of a subgroup of $\mathrm{Sym}(c)$ only if $j!/2\le c!$, i.e. $j\le c$.
* *The groups.* Individualized points are fixed. The remaining possibilities for $H$ are:
  * (1): $H\le\prod\mathrm{Sym}(C_i)$ with $\lvert C_i\rvert<\frac34m$;
  * (2a): $H\le\mathrm{Sym}(D\setminus C)\times(\mathrm{Sym}(b)\wr\mathrm{Sym}(p))$ with $bp=\lvert C\rvert$,
    $b,p\ge2$ and $\lvert D\setminus C\rvert\le m/4$;
  * (2b) partition: $H\le\mathrm{Sym}(D\setminus C)\times\prod_j\mathrm{Sym}(b_j)\wr\mathrm{Sym}(p_j)$
    with $b_j\le\frac34\lvert C\rvert$ and $p_j\le\lvert C\rvert/2$;
  * (2b) Johnson: $H\le\mathrm{Sym}(D\setminus\Gamma_0)\times\mathrm{Aut}(\mathcal J(r,s))$, where
    $\mathrm{Aut}(\mathcal J(r,s))=\mathrm{Sym}(\Lambda)$ (HBD L805). Here
    $\lvert D\setminus\Gamma_0\rvert\le\frac7{16}m$, and $\binom r2\le\binom rs\le m$ gives
    $r\le1+\sqrt{2m}\le\frac34m$ (check script, part 5).
* In every case the relevant degrees are $\le\frac34m$. ∎

The GNS run of step 5 only ever uses sections of $H$: subgroups, their restrictions to invariant sets,
and cosets. Each giant $A_{k''}\le\varphi''(G'')$ is a composition factor of a section of $H$, hence of
a subgroup of $H$. So **every black-box call inside step 5 is on $\le k''\le\frac34m$ points**, with
arity $t'=\max\{9,3+\log_2m\}$. Its structures again satisfy (P1) and (P3), with
$m''>7.5t'$.

### 3.5 Cost

* *Steps 1–4.* WL and the Design-Lemma search take $m^{O(t)}$; there are $m^{t+O(\log m)}$ candidates.
* *Step 5, main recursion.* This is Theorem C's almost-$d$-ary part with $d=m$ and $N\le m^t$: at most
  $O(\log N)N^{K+1}$ macro nodes with $K=O(\log^2m)$, each with $2^{O(\log^2m)}$ tree nodes. Every
  tree node makes $\le k^6$ black-box calls and polynomial work.
* *Step 5, black boxes.* Case (iv) calls are binary, costing $2^{O(\log^3m)}$ by B–H. Case (v) calls
  cost $X(\frac34m,t')$.
* Hence
  $$X(m,t)\ \le\ m^{O(t+\log m)}\cdot 2^{O(t\log^3m)}\cdot\big(1+X(\tfrac34m,\ t')\big),\qquad t'\le4+\log_2 m.$$
* *Unrolling.* With $m_j=(3/4)^jm$, depth $\le\log_{4/3}m$:
  $$\log X(m,t)\le C\Big(t\log^3m+\sum_{j\ge1}(5+\log m_j)\log^3m_j\Big)=O(t\log^3m+\log^5m)$$
  (check script, part 2: the sum is about $0.6\log^5 m$). ∎

*Where the $L^5$ comes from.* The top level costs $t\log^3m=O(L^4)$. The self-similar tail (arity
$\approx\log m_j$ on $m_j$ points, $O(\log m)$ levels of $2^{O(\log^4m_j)}$ each) costs $\log^5m$. A
4.5 in place of 5 would already give $c=3$ for all $d$ (§0).

---

## 4. Theorem G: no black box, $c=3$ for all $d$ [SKETCH]

### 4.1 Statement and idea

**Theorem G.** [SKETCH] Consider GNS's algorithm (with the CB §7.3 fix and Prop. B) in which case (v)
is handled by Babai's route: Design Lemma, then Split-or-Johnson, then recursing on the child cosets
$\varphi^{-1}(\mathrm{Iso}((\vec x,Y_1),(\vec y,Y_2)))$. That is $\le k^{t+O(\log k)}=2^{O(L^2)}$
children, a "heavy round". This algorithm decides degree-$d$ GI in $n^{O(\log^3d)}$ for all $d$.

Why it is not already in w8: w8 §5 charged heavy rounds per macro step. There are $O(L)$ rounds of
$2^{O(L^2)}$ each, so $K=L^3$ and $c=4$. Here heavy rounds are charged to a **hereditary** potential,
which is not reset when a new macro step starts. This is HBD's device for Babai's algorithm, HBD
L2016–2046:
$$\rho(\mathfrak B_0\succ\dots\succ\mathfrak B_m)=\sum_i\big(2\lfloor\log_2 r_i\rfloor-1\big),\qquad r_i=\text{number of }\mathfrak B_{i}\text{-blocks per }\mathfrak B_{i-1}\text{-block}.$$
* $\rho\le2\log_2N$.
* $\rho$ does not increase under subgroups, restriction to invariant sets, or the GNS descent
  $G\to G'$, which inserts the levels $\mathcal C'$ and $\mathfrak B$ above $\mathfrak B_1$.
* Inserting a non-trivial level (both factors $\ge2$) lowers $\rho$ by $\ge1$, because
  $\lfloor a\rfloor+\lfloor b\rfloor\le\lfloor a+b\rfloor$.

### 4.2 The three outcomes of a heavy round

Setting: an aggregation node, with $G'$ transitive on $\Omega$ (otherwise all orbits are $\le n/2$),
$\varphi:G'\to S_k$, $\ker\varphi=G'_{(\mathcal C')}$, $\lvert\mathcal C'\rvert\le d$, and $k>10t$.

**Lemma 4.0 (classes are small subsets of $[k]$).** [PROVEN, modulo Dixon–Mortimer Thm 5.2B as used
by GNS, G L1950] There are $1\le s<t$ and a $\varphi(G')$-equivariant surjection
$\sigma:\mathcal C'\to\binom{[k]}{s}$ with fibres of equal size. The stabilizer of $c$ contains
$\mathrm{Alt}([k]\setminus\sigma(c))$.

*Proof.*
* $\varphi(G')\ge A_k$ acts transitively and faithfully on $\mathcal C'$, with point stabilizers of
  index $\le d<\binom kr$ for $r=\lceil\log_2d\rceil+1<k/2$.
* By DM 5.2B each stabilizer satisfies $A_{(\Sigma)}\le S_c\le S_{\{\Sigma\}}$ for a set $\Sigma$ with
  $\lvert\Sigma\rvert<r$.
* $\Sigma$ is unique: a second one $\Sigma'$ is stabilized by $A_{(\Sigma)}$, which forces
  $\Sigma'\subseteq\Sigma$, and symmetrically. Put $\sigma(c):=\Sigma$.
* $s=0$ is impossible, since $A_k$ would then act trivially. ∎

Let $L_Y=\mathrm{Aut}(Y_1)\cap\varphi(G')\cap(\text{stabilizer of the individualized points})$ and
$R=\varphi^{-1}(L_Y)$. $R$ permutes the $\mathcal C'$-classes through $\varphi(R)=L_Y$, so every
$R$-orbit on $\Omega$ is contained in the union of the classes over one $L_Y$-orbit of $s$-subsets.
The classes form an equipartition of $\Omega$. Call a round a **shrink** if every $R$-orbit has
$\le\frac56n$ points.

**Lemma O1 (colourings shrink).** [PROVEN] If $Y_1$ is a colouring with all classes $\le\frac34k$, the
round is a shrink.

*Proof.* Realize a uniform $s$-subset as a uniform injective tuple $(u_1,\dots,u_s)$ and condition on
$u_2,\dots,u_s$. A colour-count pattern then forces the colour of $u_1$. So
$$\Pr[\text{pattern}]\le\frac{\max_j\lvert C_j\rvert}{k-s+1}\le\frac{10}{9}\cdot\frac34=\frac56,$$
using $s<t<k/10$ (check script, part 3). ∎

**Lemma O2 (partitions shrink or refine the tower).** [SKETCH] Let $Y_1$ be a coloured partition with
all blocks $\le\frac34k$; this covers outcomes (2a) and (2b)-partition, and GNS case (ii). Then either
the round is a shrink, or the large $R$-orbit $\Omega'$ carries an $R$-invariant partition $\mathfrak E$
with $\mathcal C'[\Omega']\prec\mathfrak E\prec\{\Omega'\}$, both strictly. Inserting $\mathfrak E$
keeps the sequence almost $d$-ary and lowers $\rho$ by $\ge1$.

*Sketch.* Let $\Psi(S)$ be the function (block $\mapsto\lvert S\cap\text{block}\rvert$). It is
$L_Y$-equivariant.
* Apply O1's conditioning to blocks instead of colours: every fibre of $\Psi$ has probability
  $\le\frac56$. So a non-shrink orbit $P$ (probability $>\frac56$) is not inside one fibre, and
  $\mathfrak E:=$ the fibres of $\Psi\circ\sigma$ has $\ge2$ blocks.
* If some $\mathfrak E$-block were a single class, then (after even permutations inside blocks, which
  lie in $L_Y$) every $S\in P$ would be a union of whole blocks. Let $z$ be the number of points in
  singleton blocks. That event has probability $\le z/k+1/10$, and if $z>2k/3$ the colour classes are
  $\le k/3$ and O1 applies. Either way we get a shrink.
* Gap: the parity bookkeeping for blocks of size 2 is only sketched. ∎

**Lemma O3 (Johnson steps).** [SKETCH] Suppose $Y_1$ contains a Johnson scheme $\mathcal J(r,s')$ on
$\Gamma_0$, with the rest $O=[k]\setminus\Gamma_0$ coloured. Then either the round is a shrink, or the
next giant on the large orbit has degree $k'\le r\le1+\sqrt{2k}$.

*Sketch.*
* By O1, a non-shrink needs $\lvert\Gamma_0\rvert>\frac34k$.
* For $j\ge1$, the hypergeometric probability that exactly $j$ points of a uniform $s$-subset lie in
  $O$ is $\le5/6$ (check script, part 4: the largest value seen is $0.44$). So the large orbit
  consists of classes with $\sigma(c)\subseteq\Gamma_0$.
* On these classes $\mathrm{Alt}(O)\le S_c$ (Lemma 4.0), so the $O$-part of $L_Y$ acts through a
  2-group.
* The next giant is an alternating section of $(R^\circ)^{\mathcal C'[\Omega']}$ (CB fix, as in
  Prop. B). That group is a section of $\mathrm{Sym}(\Lambda)\times C_2^{O(1)}$, so $k'\le r$.
* Gap: the hypergeometric bound is checked numerically ($k\le300$) and argued asymptotically, not
  proved in closed form. ∎

GNS's other outcomes:
* Case (i) is O1.
* Case (iii) (Option 2, $\varphi(H)$ fixes $\Delta_1$ pointwise with $\lvert\Delta_1\rvert\ge3k/4$) is a
  strong shrink. An $L$-orbit of $s$-subsets fixes $S\cap\Delta_1$ and $j=\lvert S\setminus\Delta_1\rvert$,
  so it has probability $\le\binom{k/4}{j}/\binom ks\le1/4$ if $j\ge1$, and $1/\binom ks$ if $j=0$.
* Luks steps ($\lvert P\rvert\le d^{1+\log d}$, or $k\le10t$) are shrinks.
* Only case (iv) is a "light" round that may do none of the three. It keeps GNS's $\le k^6$
  individualization plus a binary B–H call ($2^{O(L^3)}$, additive).

### 4.3 Accounting [SKETCH]

* *Phases.* A **phase** is a maximal same-domain path segment with constant $\rho$. Within a phase:
  * light rounds and descents number $O(L)$ (Prop. B), each branching $\le d\,k^6$;
  * heavy rounds are Johnson steps (O3). Along the phase their giants satisfy
    $k_{i+1}\le1+\sqrt{2k_i}$, so their branching totals
    $\sum_i(t\log k_i+O(\log^2k_i))=O(t\log k+\log^2k)=O(L^2)$.

  So a phase has $2^{O(L^2)}$ nodes.
* *Ends of phases.* A phase ends with a shrink (children on $\le\frac56n$ points) or a heavy O2 round
  (children on the same domain, with $\rho-1$). Each node also has local-certificate exits summing to
  $2^{O(L^2)}n$, each $\le n/2$.
* *Recursion lemma.* $T(n,\rho)\le n^{A}2^{B\rho}$ with $A,B=O(L^2)$, by induction on $(n,\rho)$, as
  in CB Lemma 7.0. Here $(5/6)^{A-1}2^{O(L^2)}\le1/3$ absorbs the exits, and $B$ exceeds the log of the
  phase-and-heavy-round branching.
* *Total.* With $\rho\le2\log N$ and $N\le n^{O(L)}$ (w8 Prop. 2), the total is
  $N^{O(L^2)}=n^{O(L^3)}$. ∎

**Gaps (why this is a SKETCH).**
1. The pairwise use of the Design Lemma and Split-or-Johnson inside GNS's aggregation, i.e. the child
   cosets over the candidate family and their composition with case (iv)'s $k^6$ family. This is
   standard in Babai's algorithm but not written out for GNS.
2. Lemmas O2 and O3, as marked.
3. HBD's own $\rho$-accounting is itself appendix-level in HBD (L1969–2046). I re-derived the parts I
   use: monotonicity, the decrement on insertion, and the recursion lemma.
4. Nothing here has been red-teamed.

If Theorem G holds, GNS's black box is unnecessary, and $c=3$ (the floor of the architecture, w8 §2.7)
holds for all $d$.

---

## 5. Combinations and the best bounds (Task 3)

| # | bound | label | assumes |
|---|---|---|---|
| B1 | **$n^{O(\log^3 d)}\cdot2^{O(\log^5 d)}$**; so $c=10/3$ for all $d$, and $c=3$ for $d\le2^{\sqrt{\log n}}$ or $d\ge2^{(\log n)^{2/3}}$ | **[PROVEN]** | GNS (SICOMP 2023, CFSG); CB §7.3 fix; w8 Prop. 2 / G–N survey Thm 4.16 (domain $n^{O(\log d)}$); w8 Lemma A + Prop. B + Theorem C; HBD Design Lemma, Split-or-Johnson, Johnson identification, WL functors; B–H (binary black boxes and the switch) |
| B2 | $n^{O(\log^3d)}$ for all $d$, with no black box | [SKETCH] | B1's inputs, minus B–H for case (v); DM Thm 5.2B; Lemmas 4.0, O1–O3; HBD's $\rho$ |
| B3 | $n^{O(\min\{\log^3 d,\ \log n\})}$ | [CONDITIONAL: HJ Lean `main_theorem`, 10 axioms] | + w8 Theorem C (or B1) |
| B4 | black box $2^{O(\log^4 d)}$ via HJ, giving $c=3$ | [CONDITIONAL: HJ Lean] | Prop. 2.2; subsumed by B3 |
| (prior) | $n^{O(\log^2 d)}$ (w8 Cor. F), $n^{O(\log d)}$ (Theorem R\*) | [CONDITIONAL: HJ §§4–7 internals] | not re-examined here |

* The three unconditional ingredients interact as follows.
  * The domain count fixes $e=1$, i.e. $\log N=O(L\ell)$.
  * Lemma A fixes $a=2$ (tree size $2^{O(L^2)}$).
  * The black box then enters additively. A cost of $2^{O(L^a)}$ costs nothing extra exactly when
    $a\le4.5$.
* Theorem X gets $a=5$. Theorem G removes the term.
* CFSG enters only through GNS: Lemma 7.1 / Cameron, Thm 3.13, Thm A.2. Theorem X adds none, since
  HBD's combinatorial lemmas are CFSG-free.
* The HJ-conditional bound B3 uses only the verified statement, not HJ's internals.

---

## 6. Novelty (Task 4)

| source | what it says | how checked |
|---|---|---|
| GNS v3 / SICOMP | black box by design (G L2029); Lemma 6.7's cost displayed as $k^{O(t^c(\log k)^c)}$; $c$ unspecified | full v3 source; SICOMP abstract only (403) |
| Neuen 2020 (2002.06997) | the same black box (L2621) and the same potential | full source |
| Grohe–Neuen survey 2021 | L1205–1214 describe Babai's Design Lemma and Split-or-Johnson; L1253: GNS "does not exploit the combinatorial subroutines directly, but one can simply rely on using Babai's algorithm as a black box instead. In particular, this also simplifies the analysis." So the Design-Lemma variant is named as an option, with no exponent analysis | full TeX |
| Neuen 2026 survey | $n^{\mathrm{polylog}(d)}$ only | w9 red-team, full text |
| HBD (Astérisque 2019) | the $\rho$ potential, for Babai's algorithm with test sets $O(\log n)$; "with a little bit of work … $c=3$" | full source |
| Babai (1512.03547) | Design Lemma, Split-or-Johnson, the primitive case as hypergraphs (B L657–664) | searched |
| Pago (2302.05426), Wiebking (1911.11257) | Lemma A's relative (Pago); canonization framework with GNS/Babai as black boxes, polylog exponents (Wiebking) | searched |
| Neuen's thesis (RWTH 2019) | **not retrieved** (blocked; not bypassed) | — |

**Status.**
* *Not found anywhere:* the explicit cost of GNS's black box; the observation that only case (v) is
  expensive; Proposition 1.3 (no canonical low-arity relaxation); Theorem X and $c=10/3$; the hybrid
  of GNS's $O(\log d)$ test sets with HBD's hereditary potential (Theorem G); the redundancy of HJ as
  a black box.
* *Ingredients that are known:* HBD's $\rho$, Babai's lemmas, and the survey's remark that the
  combinatorial subroutines could replace the black box.
* *Residual risk:* Neuen's thesis, which might analyse the subroutine variant. Its author's 2021 and
  2026 surveys say $\mathrm{polylog}(d)$ only, and the 2021 survey explicitly prefers the black box.

---

## 7. Where attempts broke, and leads

**Broke.**
* *Canonical arity reduction* (binary, coherent-configuration skeleta, canonical subcosets):
  Proposition 1.3.
* *Several Design-Lemma rounds at the top of BB.* After one round the problem is string isomorphism
  under $\mathrm{Aut}(Y)$ acting on tuples, which is no longer structure isomorphism under a product of
  symmetric groups. Further rounds need local certificates, i.e. GNS again. This is why BB makes
  exactly one round.
* *Improving the tail of Theorem X.* In the self-similar regime (arity $\approx\log m$) every scheme I
  tried gives $\sum_j\log^4 m_j=\Theta(\log^5m)$. This includes HBD-refined B–H on the
  string-isomorphism formulation: $\exp(O(\log^2N\cdot\log m))$ with $N=m^t$, the same $L^5$ [SKETCH].
* *HJ inside GNS:* redundant (Prop. 2.4).

**Leads.**
1. **A bounded-individualization Design Lemma for case-(v) structures.** That is, $O(1)$
   individualized points plus WL give a non-trivial 2-skeleton on a large class. It would make the
   black box binary at $\mathrm{poly}(k)$ branching, so $c=3$ from Theorem C alone. Proposition 1.3
   shows $\ge1$ point is needed; I know no example needing $\omega(1)$ for these structures.
   [SPECULATION]
2. **Turn Theorem G into a proof:** gaps 1–2 of §4.3. This is the most direct route to an
   unconditional $c=3$.
3. **Canonization.** Theorems X and G should transfer to CB's canonical algorithm, with Babai's
   canonical forms in the role of B–H. Not checked.

---

## 8. Ledger

**Proven here.**
* §1.2 (what the call must deliver).
* Proposition 1.3 (for GNS string-isomorphism instances; I did not check that such an instance arises
  from a degree-$d$ graph).
* Proposition 2.2 (encoding).
* Theorem X, Lemma S, Corollary X.
* Lemmas 4.0 and O1.
* The exponent arithmetic (check script).

**Sketched.**
* Theorem G, Lemmas O2 and O3, and the phase accounting.
* The HBD-refined B–H estimate (§7).

**Conditional on HJ's Lean `main_theorem` (10 CFSG-based axioms).** Corollary 2.3, Proposition 2.4,
B3, B4.

**Trusted (published).**
* GNS (SICOMP 52(6), 2023): Lemma 6.3, 6.6, 6.7, 7.1, Thm 5.8, App. A, Thm 8.1.
* HBD (Astérisque 407, 2019): Prop. `design`, Thm `coupjohn` with Props `bicoup`/`cohcoup`, the WL
  functors, §`subs:idgroup`, and B–H's $\exp(O(\log^3N))$.
* Dixon–Mortimer Thm 5.2A,B, as cited by GNS.
* Miller-style encodings, used here in the explicit form of Prop. 2.2.

**Trusted (repository, red-teamed).**
* w8 Lemma A, Prop. B, Theorem C, Prop. 2 (`docs/redteam-w8-gnsexp.md`).
* CB §7.3 fix and Lemma 7.0 (`docs/redteam-gns-lemma72.md`).
* CB Lemma T′.

**Not checked.**
* Neuen's thesis.
* The SICOMP full text.
* Whether Proposition 1.3's instance arises from degree-$d$ GI.
* No Lean was run. The Lean facts in §2.1 come from reading the source files only.
