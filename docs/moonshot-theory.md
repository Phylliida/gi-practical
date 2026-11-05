# Can graph isomorphism beat $n^{O(\log n)}$? A dissection of the Hajiaghayi–JafariRaviz bound

Research memo, branch `r3-theory`, 2026-11-04.

Subject: Hajiaghayi and JafariRaviz, *Deterministic $n^{O(\log n)}$ Graph Isomorphism Algorithm via
Inherited Decompositions*, arXiv:2611.01399 (below "HJ"). Line numbers `L…` refer to the LaTeX
source `graph_isomorphism.tex` (4953 lines). Lean references are to
`~/math/GraphIsomorphismLog2/Workspace/…` (read only; nothing was built).

**Labels.** Each claim carries one of these tags:

* **[PROVEN]**: a complete argument is given here. It relies only on HJ as written and on cited
  published results.
* **[SKETCH]**: the argument is given and the gaps are listed explicitly.
* **[CONDITIONAL]**: proven or sketched under a stated hypothesis.
* **[SPECULATION]**: an opinion or a conjecture.

Every statement about HJ assumes that HJ is correct. HJ is a three-day-old, unrefereed preprint.
Its Lean development is a "stage 1" formalization of an abstract recursion. It takes Maróti's
theorem as an axiom, and it takes the subroutine interfaces (`Supply`, `RowTerminal`, `Aggregation`)
and a per-node work bound (`NodeBound`) as hypotheses (`Paper/MainTheorem.lean` header, lines 17–34;
`Paper/Algorithm.lean` lines 37–40, 60–62).

---

## 0. Summary

1. **The exponent factors as (depth) × (branching).** Inside a phase every charged step pays a
   multiplicity $M$ with a potential drop of at least $\log M$, and the root potential is
   $\Theta(\log^2 N)$. Rewriting the multiplicities that HJ bounds crudely by $N^a$ gives the
   following. **[SKETCH]** The per-phase exponent of the HJ algorithm is
   $$O\big(\log N\cdot(\log w+\mu+\log\log N)\big),$$
   where $w$ is the largest giant degree that can occur (the alternating width, or more robustly the
   composition width) and $\mu$ is the largest "order exponent" $\log|P|/\log\deg P$ of an
   enumerated primitive section. For general graph isomorphism $w\approx\sqrt N$ at the root and
   $\mu$ can be $\Theta(\log N)$, so both factors are $\Theta(\log N)$.

2. **Where the $\log^2$ actually lives.** One candidate source is pure slack, two shrink to
   $\log N\cdot\log w$, one is provably tight for the algorithm, and the giant-breaking core is open.
   * The hierarchy-rank term $\rho x$ is pure slack: $\rho\cdot O(\log\log N)$ suffices. **[PROVEN]**
   * The bound $Q\le\log^2 s$ shrinks to $Q\le\log N\log w$ by initializing caps at
     $\min(d_i,w)$. **[PROVEN]** The term $\sigma x$ shrinks to $\sigma\log w$. **[SKETCH: needs the
     call grouping (H2) of §4.1]**
   * The $x^2$ (domain) charge for the "geometrically affected" local-test children costs only
     $\exp(O(\log N\log\log N))$ in total. **[SKETCH]**
   * The enumeration of Maróti-small primitive quotients is **tight for the algorithm**. On string
     isomorphism with the input group $\mathrm{AGL}(k,2)$ ($N=2^k$), HJ performs at least
     $0.288\,N^{1+\log_2N}$ coset branches, whatever the colorings are. **[PROVEN]** So the
     $\exp(O(\log^2N))$ bound of HJ's Theorem 1.2 (string isomorphism) cannot be improved for HJ's
     algorithm.
   * The giant-breaking channels (cap contraction, rectangles, unaffected tests) are tight only if
     polynomial-degree giants survive $\Theta(\log N)$ rounds. That matches the 1978–80
     $n^{O(\log n)}$ barrier for conference graphs, Latin squares and Steiner triple systems. We
     found no proof that HJ actually spends that much on them. **[SPECULATION]**

3. **The barriers are concrete.** An $n^{o(\log n)}$ graph isomorphism algorithm would give
   $n^{o(\log n)}$ algorithms for all of the following. **[PROVEN reductions]**
   * group isomorphism (the best general bound is still $n^{c\log n}$, and only $c$ has improved
     since 1978);
   * quasigroup/Latin-square isomorphism, Steiner triple systems and conference graphs (the best
     bounds are still $n^{O(\log n)}$);
   * affine equivalence of arbitrary colorings of $\mathbb F_2^k$ (string isomorphism under
     $\mathrm{AGL}(k,2)$) in time $2^{o(k^2)}$.

   Sun's breakthrough (STOC 2023), and its improvement by Ivanyos–Mendoza–Qiao–Sun–Zhang (FOCS
   2024) to $N^{\tilde O(\sqrt{\log N})}$, covers p-groups of class 2 / Frattini class 2 and general
   3-tensor isomorphism. It does not touch the combinatorial classes, and it does not touch
   general colorings of $\mathbb F_2^k$.

4. **Most promising conditional result.** **[CONDITIONAL, SKETCH]** Assume HJ is correct and two
   checkable side conditions hold (§4.1). Then string isomorphism for groups of composition width
   $\le d$ (class $\hat\Gamma_d$) runs in $N^{O(\log d+\log\log N)}$. Hence graph isomorphism for
   maximum degree $d$ runs in $n^{O(\log d+\log\log n)}$. The best published bound is
   $n^{\mathrm{polylog}(d)}$ (Grohe–Neuen–Schweitzer 2018; Neuen's 2026 survey still lists it). This
   is new relative to the literature we could find, but it is only as good as HJ.

5. **Verdict.** Inside the HJ framework, beating $\log^2$ for general graph isomorphism needs two
   things. (a) A giant-breaking procedure using $o(\log n)$ nested rounds of polynomial branching.
   This would already beat Babai's 1980 bound for conference graphs. (b) A non-enumerative treatment
   of classical-group primitive sections. This would already give $2^{o(k^2)}$ affine equivalence
   of Boolean functions and improve general group isomorphism. Both are recognized open problems.
   Our attempts break exactly there (§4).

---

## 1. The accounting HJ uses

**Phases.** A phase starts at $N$ positions. Calls stay in it while $s>N^\gamma$. Fresh calls (at
the threshold $N^\gamma$, configurations on $\le N^{2\alpha}$ positions, row calls on $\le N^{1-\alpha}$
positions) start new phases (L1092–1107, L1616–1630). The recurrence is
$F(N)\le e^{C\log^2N}(1+F(N^\gamma))$ (L1722; Lean `Paper/RunningTime.lean:1101`
`main_recurrence_solution`).

**Potential** (L1416–1458; Lean `RunningTime.lean:38–56`):
$$\Phi=A\big(x^2+\rho x+\sigma x+Q\big)+Bh,\qquad x=\log(s+2),\qquad W=(s+2)^D e^{\Phi}.$$

* $\rho=\sum_i(2\lfloor\log_2 d_i\rfloor-1)\le2\log_2s$ (L1430; `RunningTimeInequalities.lean:25`).
* $\sigma\le C\log s$ is the hereditary budget (Thm A.9, L2474; `HereditaryBudget.lean:109`).
* $Q=\sum_i\log d_i\log\max(c_i,2)\le\log^2s$ (L1432; `RunningTimeInequalities.lean:52`).

**Charging table** (L1538–1555; Lean `Row.mult`/`Row.drop`, `RunningTime.lean:128–145`):

| row | multiplicity (HJ) | potential drop |
|---|---|---|
| affected test / rectangle | $N^a$ | $Ac_\theta x-2B$ |
| visible unaffected test | $N^a$ | $A\kappa x-2B$ |
| product refinement, $r\ge2$ | $N^a2^rr!$ | $A(r-1)x-2B$ |
| primitive enumeration, degree $d$ | $N^a e^{a\log^2d}$ | $\tfrac A3x\log d-2B$ |
| auxiliary-graph continuation | $q^a$ | $Ac_\beta\log q-2B$ |
| row event | $b_0$ | $B$ |

Lemma 7.1 (L1643–1714; `RunningTime.lean:851`) shows that each class of children carries at most
$W/(8J)$ of the parent weight. At a phase root every term of $\Phi$ is $O(\log^2N)$ (L1708–1711;
`RunningTime.lean:897–962`, `RootBounds`, `main_phase_root_potential`).

**What has to happen to beat $\log^2$.** The potential at a phase root is the total budget. Every
charged step must be paid by its drop. Write a worst-case chain of nested charged steps as
$(M_1,M_2,\dots)$. Then the analysis cannot give better than $\exp(\sum_j\log M_j)$. HJ has
$\Theta(\log N)$ steps on a chain (each removes a constant fraction of the domain or a constant
amount of a $\Theta(\log N)$ resource), and each has $\log M_j=\Theta(\log N)$. To beat $\log^2$, one
of the two factors must be $o(\log N)$ on every chain.

---

## 2. Dissection: every term that produces $\exp(\Theta(\log^2N))$ per phase

The table below summarizes the five terms; §2.1–§2.8 give the details.

| term | where (LaTeX / Lean) | true per-step multiplicity | what it costs | inherent? |
|---|---|---|---|---|
| $x^2$ (domain) | L1478–1491, L2683–2726; `eq_main_domain_payment` `RunningTimeInequalities.lean:122` | $C_\kappa q^{2\kappa}$, not $N^a$ ($q$ = current giant degree) | $\log N\cdot\log w$; geometric children only $\log N\log\log N$ | partly slack (§2.1) |
| $\rho x$ (hierarchy) | L1506–1517; `main_product_index_bound` `:186` | $2^r\lvert\mathrm{top}\rvert\le2^rr!$ | $\log N\log\log N$ | **slack** (§2.2) |
| $\sigma x$ (budget) | L1490–1492, L2697–2726; Thm A.9 L2474 | $C_\kappa q^{2\kappa}$ | $\log N\cdot\log w$ | slack to $\log w$ (§2.3) |
| $Q$ (caps) | L1520–1536; `eq_main_cap_payment` `:354` | $q^a$ | $\log N\cdot\log w$ | Babai-core; open (§2.4) |
| enumeration | L1494–1504, L3067–3087, L3270; `eq_main_enumeration_payment` `:149` | $\lvert P\rvert\le d^{1+\log_2 d}$ | $\log N\cdot\mu$ | **tight for HJ** (§2.5) |
| row terminal $E_N$ | L1633–1636, L3975–3990, L4025–4180 | additive $b^{2\log_2b}$ | $\log^2N$, only when $w>N^\alpha$ | enumeration-type (§2.6) |
| phase recurrence | L1722–1737; `:1101` | none | geometric sum | lossless (§2.7) |
| threshold $k>2+\log_2n$ | L3392–3410, L3445 (LG1), L2856–2864 | none (structural) | none | removed by HJ (§2.8) |

### 2.1 The domain term $x^2$

**Source.** Affected local-test calls, rectangle queries, large-symmetry calls and column entries
each shrink the domain by a constant factor ($s'\le\theta s$, or $s/\kappa$, or $s/2$). They are paid by
$x^2-\log^2(\theta s+2)\ge c_\theta x$ (eq. main-domain-payment, L1487). Their multiplicity is
bounded by $N^a$ (L1463–1472, "polynomial numbers of local and auxiliary calls").

**The real multiplicity is $q^{O(\kappa)}$, not $N^{O(1)}$.** The Lean counts are explicit
(`Paper/ScriptCalls.lean` header, lines 5–25):

* a certificate phase makes $\le2\binom q\kappa s\,\kappa!$ calls;
* a comparison phase makes $\le4q^{2\kappa}s$ calls;
* each aggregation item makes $\le3$ calls.

The factor $s$ counts window updates. The windows $V_i$ added by successive updates are disjoint
(L2669, "Every update adds a nonempty $A_i$-invariant set"). Within one coset of $N_i$ in
$A_i$ the calls are an orbit chain on disjoint domains. So all calls of one test form $\le\kappa!/2$
disjoint-domain families. The prefactor $(s+2)^D$ absorbs a disjoint-domain family exactly as it
does for orbit chains (eq. main-orbit-slack, L1588). Hence the multiplicity of the
affected/unaffected rows is $\le C_\kappa q^{2\kappa}$. The rectangle and large-symmetry rows
branch over the $q^{O(1)}$ aggregation choices (L2799–2822, L2976). HJ replaces $q$ by $N$
everywhere because $q\le s\le N$.

**Consequence.** The domain term only needs to be $x\cdot\Lambda$ with $\Lambda\gtrsim2\kappa\log q_{\max}$.
For general graph isomorphism $q_{\max}=n=\sqrt N$, so nothing is gained. When every giant has
small degree, the term is $\log N\cdot\log w$.

**Geometric versus algebraic affected points.** **[SKETCH]** HJ's giant always comes from a
Cameron constituent $\pi:G\twoheadrightarrow\mathrm{Alt}(\Gamma)$ with an equivariant block map
$p:\Omega\to\binom\Gamma t$, $t\le q/2$, with equal fibers (as in Lemma "large symmetry", L2868–2877).

*Lemma J.* Fix a test $T$ with $|T|=\kappa$ and a point $\omega$ with $p(\omega)\cap T\ne\emptyset$.
Every orbit of $J_T=G_{(T)}$, and so every orbit of $N_i\le J_T$, through $\omega$ has size at most
$(t/q)s$.

*Proof.* $J_T$ fixes $T$ pointwise, so it preserves $p(\omega)\cap T$. The relevant fiber fraction is
$\binom{q-\kappa}{t-j}/\binom qt\le\binom{q-1}{t-1}/\binom qt=t/q$, where $j=|p(\omega)\cap T|\ge1$
and $t-1\le(q-1)/2$. ∎

*Cost.* The multiplicity is $M\le C_\kappa q^{2\kappa}$.

* If $t\le\sqrt q$, each such child shrinks by $\ge\sqrt q$, so $\log M\le4\kappa\log(s/s')+O(1)$. A
  potential **linear** in $x$ pays.
* If $t>\sqrt q$, then $s\ge\binom qt\ge2^{\sqrt q}$, so $q\le\log_2^2s$ and
  $\log M=O(\log\log N)$ per constant-factor shrink.

So children of geometrically affected points (block meets $T$) cost $\exp(O(\log N\log\log N))$ in
total along any chain. The full $x^2$ charge is needed only for points that are affected
**algebraically**: $p(\omega)\cap T=\emptyset$, but the current partial-automorphism group $A_i$
correlates its action on $T$ with $\omega$'s orbit. Then only the index bound
$|a^{N_i}|\le|\Delta|/\kappa$ (L2683–2690) is available.

**Forcing shape.** To force $\log^2$ through this term, a chain of $\Theta(\log N)$ nested
algebraically affected steps is needed, each with index exactly $\Theta(1)$ and a giant of degree
$N^{\Omega(1)}$. We know no such instance. **[SPECULATION: probably slack.]**

Rectangle queries keep up to a constant fraction $\theta$ of the domain ($\theta>2\eta(1-\eta)$, L1762–1764), with $q^{O(1)}$ branching. A
nested chain of rectangles with $q$ going from $\sqrt N$ down to $\lambda=N^\alpha$ has
$\Theta((\tfrac12-\alpha)\log N)$ levels. That is $\exp(\Theta(\log^2N))$ in the worst case. This is
the same giant-breaking mechanism as $Q$ (§2.4).

### 2.2 The hierarchy rank $\rho x$: slack

**Lemma 1.** **[PROVEN, given HJ's step structure.]** In HJ's analysis, $\rho x$ can be replaced by
$\rho\,\ell_N$ with $\ell_N=2\log(2\log_2N)+c$. The $\rho$ term then contributes only
$\exp(O(\log N\log\log N))$.

*Proof.* $\rho$ is used in three places.

1. **Product refinement** (L1506–1517). The children are the $\le|G:\mathrm{Alt}(m)^r|\le2^rr!$
   coset continuations on the same domain (Algorithm 1 "Apply that reduction and solve its
   children", L1153–1156). The $N^a$ factor in the table is, in HJ's words, a "harmless upper bound"
   (L1557–1558). The drop is $\ge r-1$ (L3060–3062). Since $r\le\log_2s\le\log_2N$ and $r\le2(r-1)$,
   $$\log(2^rr!)\le r\log(2r)\le2(r-1)\log(2\log_2N).$$
   So $A(r-1)\ell_N-2B\ge\log(2^rr!)+\log 8J$ once $A\ge1$ and $c\ge2B+\log 8J$.
2. **Ordinary interval refinements** have multiplicity 1.
3. **Funding a counter reset** costs $2B$, a constant.

At the root, $\rho\ell_N\le2\log_2N\cdot\ell_N$. ∎

### 2.3 The budget term $\sigma x$: "each unaffected test pays the full log"

**Source.** An extra visible unaffected orbit gives $(s,\sigma)\mapsto(s,\sigma-\kappa)$ (`lem:main-local-test`,
L719–758; L2697–2726; `lem_budget_inheritance_decrease`, `HereditaryBudgetBasic.lean:55`). It is paid
by $\kappa x$ in $\sigma x$ against multiplicity $N^a$ (L1490–1492).

**Slack.** The multiplicity is $C_\kappa q^{2\kappa}$ (§2.1). So $\sigma\cdot\Lambda$ with
$\Lambda\approx2\log q_{\max}$ suffices, and $\sigma\Lambda\le C\log N\log w$ at the root. **[SKETCH:
relies on the call grouping (H2), §4.1.]**

**The bound $\sigma=O(\log N)$ is tight in general.** **[PROVEN]** Take
$G=\mathrm{Alt}(\kappa)^r_{\text{left}}\times\mathrm{Alt}(\kappa)^r_{\text{right}}$ acting on
$\Omega=\mathrm{Alt}(\kappa)^r$ by two-sided multiplication. Remove the left factors one at a time.
Each step is normal with quotient $\mathrm{Alt}(\kappa)$, and the kernel stays transitive (the right
regular action survives). The action is faithful, so every step is visible (`def:hereditary-budget`, L1952–1968).
Hence $\sigma\ge r\kappa$, while $\log N=r\log(\kappa!/2)$, so $\sigma=\Theta(\log N)$ for fixed
$\kappa$. This example has no large giant, however, so this channel is cheap on it.

**Forcing shape.** This term costs $\Theta(\log^2N)$ only if $\Theta(\log N/\kappa)$ nested visible
unaffected steps happen while giants of degree $N^{\Omega(1)}$ are present and their tests keep
correlating with the visible quotients. We know no instance. **[SPECULATION]**

### 2.4 The cap moment $Q$: the Babai core

**Source.** A configuration or rectangle answer contracts one interval cap from $\ge q$ to $\le\beta q$
and pays $q^a$ parent continuations (L1520–1536; `lem:exact-configuration`, L3103–3175;
`eq_main_cap_payment`, `RunningTimeInequalities.lean:354`).

**Slack in the bound $Q\le\log^2 s$.** Caps are analysis-only bounds on alternating width (L638–653).
Initializing them at $\min(d_i,w)$ with $w=\mathrm{aw}(G)$ is valid and gives
$Q\le\log N\cdot\log w$. For graph isomorphism the root group is $\mathrm{Sym}(n)$ on pairs:
$w=n=\sqrt N$ and $Q=\Theta(\log^2N)$.

**Is it inherent?** On one interval, $\Theta(\log q)$ successive contractions $q\to\beta q\to\beta^2q\to\cdots$
each cost $(\beta^jq)^{O(1)}$, for a total of $\exp(\Theta(\log^2q))$. This is the
individualization budget of Babai's Design Lemma and Split-or-Johnson. Each round individualizes
$O(1)$ labels (the $q^{O(1)}$ anchors, orbitals and Design tuples, L2799–2822) and guarantees only a
constant-fraction cap reduction ($\beta$ from L1757–1760 and L2840–2853).

**Forcing shape.** A family where every round of $O(1)$ individualizations leaves a homogeneous part
of size $\ge\beta q$ with alternating-section width $\ge\beta q$, and no full certificates appear.
Strongly-regular-type instances are the natural candidates: conference graphs, Latin-square graphs,
Steiner designs. Their best known worst-case bounds are $n^{O(\log n)}$, coming from $O(\log n)$-size
distinguishing sets or generating sets (§3.2). **[SPECULATION: HJ is $n^{\Theta(\log n)}$ on some
such family; not proved.]**

### 2.5 Enumeration of Maróti-small primitive quotients: tight for the algorithm

**Source.**

* Overview, L351–354 and L658–661: "the standard primitive-group reduction either enumerates its
  $d^{O(\log d)}$ relabelings or exposes a large alternating action".
* Charge: eq. main-enumeration-payment, L1494–1504; `RunningTimeInequalities.lean:149`; margin
  `RunningTimeParameters.lean:201`.
* The enumeration test accepts any quotient with $|P|\le\exp(a\log^2d)$ (L1766–1772).
* Exceptional Johnson-recognition range, also enumerated: L3067–3087.
* Fixed-floor version: L3270.
* Maróti's dichotomy, taken as an axiom: `Workspace/Cited/MarotiPrimitive.lean:76`. Either
  $|G|<n^{1+\lfloor\log_2n\rfloor}$, or $G$ is Cameron-large.

The drop $\tfrac13x\log d$ pays $a\log^2d$ only because $x\ge\log d$. When $d=N^{\Omega(1)}$ a
**single** step costs $\exp(\Theta(\log^2N))$. No potential can repair that; it is the step.

**Proposition 2.** **[PROVEN, given HJ's dispatcher as written.]** Let $k$ be large, $N=2^k$, and
$G=\mathrm{AGL}(k,2)$ acting on $\Omega=\mathbb F_2^k$. For every pair of colorings $x,y$, HJ's
`Solve`$(\Omega,G,x,y)$ creates at least
$$|G|=2^k\prod_{i=0}^{k-1}(2^k-2^i)=N^{k+1}\prod_{j=1}^k(1-2^{-j})\ge0.288\,N^{1+\log_2N}$$
coset branches.

*Proof.* Trace the phase recursion (`alg:main-recursion`, L1136–1172).

1. $N>N_0$. There is one orbit. In `Continue`, $s=N>N^\gamma$, the action is transitive and there is
   no column floor.
2. $G$ is 2-transitive, so primitive. The next primitive quotient is $G$ itself on $d=N$ singleton
   blocks.
3. $G$ is not Cameron-large: its socle is elementary abelian, not $\mathrm{Alt}(m)^r$, and it is not
   a Mathieu group. So no product refinement or giant step applies.
4. $|G|<N^{1+\log_2N}\le\exp(a\log^2N)$, because $a\ge1/\ln2+1/\ln N$ (HJ takes $a$ large;
   the Lean development uses $a\ge128$). So enumeration applies.
5. "Enumerating an actual quotient partitions the allowed relabelings into exhaustive cosets"
   (L1365–1367). The kernel is trivial, so each of the $|G|$ cosets is a branch, with an orbit
   chain on singleton kernel orbits. ∎

**Remarks.**

* $\mathrm{AGL}(k,2)$ attains Maróti's bound up to the constant factor $\prod_j(1-2^{-j})\approx0.2888$.
  So HJ's $\exp(a\log^2d)$ allowance is tight at exactly this group.
* $\mathrm{aw}(\mathrm{AGL}(k,2))=O(k)=O(\log N)$, since $\mathrm{Alt}(m)$ is a section of
  $\mathrm{GL}(k,2)$ only for $m=O(k)$ by Feit–Tits; even the trivial bound $O(k^2)$ is polylog.
  So **bounded (polylog) alternating width alone does not remove $\log^2$**.
* The same proof works for $\mathrm{PGL}(k,q)$ on projective points and for other classical groups
  in natural action.
* `gi-practical` dispatches "anything else → enumerate" (README, "Recognition of large primitive
  quotients"), so it behaves the same way.

**Forcing shape.** Classical groups in their natural (affine or projective) action on
$N^{\Omega(1)}$ points. These are exactly the groups behind Le Gall–Rosenbaum's identification of
$\mathrm{PSL}$ as "the main obstacle to faster algorithms for group isomorphism" (arXiv:1609.08253,
abstract).

### 2.6 The row terminal $E_N=\exp(c_T\log^2N)$

The transitive-kernel terminal (`thm:transitive-gat-terminal`, L4025–4180; `QuotientAlgorithms.lean:224`) enumerates the
radical-free part of the residual row action, $[H:R]\le b(Q)^2\le b^{2\log_2b}$ (L3986–3990;
`cor_transitive_kernel_multicoset`, `QuotientAlgorithms.lean:181`). The solvable remainder costs
$\exp(O(\log(b+M)\log b))$ (`thm:solvable-multicoset`, L3687–3910, Dixon's derived-length bound).

This is an enumeration-type cost. It arises only for natural giants of degree $q>\lambda=N^\alpha$,
so it is irrelevant whenever $w\le N^\alpha$. When it does arise, $\log w\ge\alpha\log N$ already.
It enters additively per node (Lean: per-node work $E_N$, `PhaseCost.lean` header lines 5–40).

### 2.7 The phase recurrence: lossless

**[PROVEN]** (L1722–1737; `main_recurrence_solution`.) A per-phase cost $\exp(C\Lambda_N\log N)$ with
$\Lambda_{N^\gamma}\le\Lambda_N$ sums to $\exp(O(\Lambda_N\log N))$, because
$\sum_j\hat\gamma^{j}=O(1)$. HJ's polynomial shrinking for fresh calls ($N\to N^\gamma$) costs only a
constant factor in the exponent. **No improvement can come from the outer recurrence.** It must come
from inside the phase, where the shrinking is by constant factors (or by $d$).

### 2.8 The logarithmic threshold $k>2+\log_2n$

In Babai/Helfgott the certificate size had to satisfy $k>2+\log_2 n$ (unaffected stabilizers
theorem). That made $\binom qk=q^{\Theta(\log n)}$ tests per level, which is the source of Helfgott's
third logarithm ($\exp(O(\log^3n))$, L124–130). HJ removes it: $\kappa=64$ is constant, and the
$\sigma$-budget pays the unaffected endpoint (L2593–2617; L2856–2864: the large-symmetry branch "does
not need the former certificate threshold").

The threshold survives only structurally:

* in Lemma "no large giant above a transitive kernel" (L3392–3410);
* in (LG1) for the row normal form (L3438–3447, L1838–1840).

Neither is a branching cost. **It is not a $\log^2$ source in HJ.**

### 2.9 Synthesis

The terms collapse to

$$\text{per-phase exponent}=O\Big(\underbrace{\log N}_{\text{chain length}}\cdot\big(\underbrace{\log w}_{\text{giant breaking: }x,\sigma,Q,\text{ rectangles}}+\underbrace{\mu}_{\text{enumeration, row terminal}}+\log\log N\big)\Big).$$

The $\mu$ part is attained (Prop. 2). The $\log w$ part is attained only if Babai's giant-breaking
genuinely needs $\Theta(\log q)$ rounds on some family (open; §2.4).

---

## 3. Barriers

### 3.1 Group isomorphism: the precise statement

**Reduction** (Miller 1979; standard). **[PROVEN]** A group or quasigroup of order $m$, given by its
Cayley table, becomes a graph $X$ with $O(m^2)$ vertices. There is one vertex per element and one per
pair $(a,b)$, joined to $a$, $b$ and $ab$ by three distinguishable edge types (encoded by
subdivisions). Graph isomorphisms are exactly the induced multiplication-preserving bijections.

So graph isomorphism in time $n^{f(n)}$ gives group isomorphism in $m^{O(f(m^2))}$, and
$f=o(\log n)$ gives **group isomorphism in $m^{o(\log m)}$**.

**What is known.**

* Generator enumeration gives $m^{\log_pm+O(1)}$ (Tarjan, via Miller 1978).
* Rosenbaum (2013) gives $m^{(1/2)\log_pm+O(1)}$ deterministically.
* Rosenbaum also gives $m^{(1/4)\log_pm+O(1)}$ (as cited by Le Gall–Rosenbaum §2.2 and Levet 2023;
  we could not confirm whether that bound is deterministic).
* The 2024 FOCS paper by Ivanyos, Mendoza, Qiao, Sun and Zhang (IMQSZ) states that "to now, only the
  constant before $\log N$ on the exponent has been improved".

**Special classes.**

* Sun (STOC 2023): p-groups of class 2 and exponent $p>2$ in $N^{O((\log N)^{5/6})}$.
* IMQSZ (FOCS 2024): $N^{\tilde O((\log N)^{1/2})}$, extended to Frattini class 2 for odd $p$.
  Their engine is a $q^{\tilde O(\ell^{1.5})}$ algorithm for **matrix-space equivalence, which is
  general 3-tensor isomorphism**.
* Dietrich–Wilson (FOCS 2021): nearly-linear time for most orders.
* An October 2026 preprint (arXiv:2610.00874) claims the same bound for 2-groups of Frattini class 2.
  We did not verify it.

**Reading.** The barrier holds but has softened. The class that used to be called hardest is now
$n^{o(\log n)}$. General group isomorphism is not. An $n^{o(\log n)}$ graph isomorphism algorithm
would have to contain a solution to general group isomorphism below $n^{\Theta(\log n)}$, and
Le Gall–Rosenbaum place the obstacle at $\mathrm{PSL}$ sections. In HJ's framework, that is exactly
the enumeration channel of §2.5.

### 3.2 Combinatorial $n^{\Theta(\log n)}$ classes (no algebra to exploit)

All of these reduce to graph isomorphism with polynomial blowup. Their best known worst-case bounds
are still $n^{O(\log n)}$ (Levet, *Australas. J. Combin.* 87 (2023), Introduction and Remark 1.10):

* **Quasigroup/Latin-square isomorphism** and **Latin-square graphs:** $n^{\log n+O(1)}$ (Miller
  1978). Gill (2025) gives average-case polynomial time and notes that the worst case still matches
  Miller.
* **Steiner triple systems:** $n^{O(\log n)}$ (Miller, via Steiner quasigroups).
* **Conference graphs** (strongly regular with Paley parameters): $n^{2\log n+O(1)}$ (Babai 1980,
  $O(\log n)$ distinguishing sets).

Levet writes that conference graphs and groups "admit $n^{\Theta(\log n)}$-time isomorphism tests that
have seen little improvement in the worst case in over 40 years".

Quasigroups contain groups, so this barrier is at least as strong as §3.1, and Sun-type linear
algebra has nothing to act on. **Any $n^{o(\log n)}$ graph isomorphism algorithm improves all of
these.** In HJ terms they are the natural candidates for the giant-breaking channel (§2.4): the
algorithm must spend $\Theta(\log n)$ individualizations of polynomial branching before refinement
separates them.

### 3.3 The string-isomorphism barrier and tensor encodings

**Proposition 3.** **[PROVEN]** String isomorphism under $\mathrm{AGL}(k,2)$ reduces to graph
isomorphism on $n=\Theta(N^3)$ vertices, where $N=2^k$.

*Proof.* For $k\ge3$, a permutation $\varphi$ of $\mathbb F_2^k$ preserves all affine planes
$\{a,b,c,a+b+c\}$ iff $\varphi(a+b+c)=\varphi(a)+\varphi(b)+\varphi(c)$ for all $a,b,c$, iff $\varphi$
is affine. Take the point–plane incidence graph and attach the colors with gadgets. ∎

So an $n^{o(\log n)}$ graph isomorphism algorithm decides **affine equivalence of arbitrary
$c$-colorings (truth tables) of $\mathbb F_2^k$ in $2^{o(k^2)}$**. The trivial bound is
$|\mathrm{AGL}(k,2)|\approx2^{k^2}$. We found no worst-case improvement. The literature on affine
equivalence of Boolean functions is practical, for $k\lesssim10$.

The same encoding (affine geometries for each tensor slot plus colored hyperedges for slot tuples)
puts $d$-tensor isomorphism over $\mathbb F_p$ of format $k^{\times d}$ into graph isomorphism on
$p^{O(dk)}$ vertices.

* For $d=3$, this is **no longer a barrier**: IMQSZ solve it in $p^{\tilde O(k^{1.5})}=n^{\tilde O(\sqrt{\log n})}$.
* For $d\ge4$, or for cubic and quartic forms (one shared $\mathrm{GL}$ on all slots), the known
  Grochow–Qiao reductions to 3-tensors blow the dimension up polynomially. IMQSZ then gives nothing
  better than brute force $p^{\Theta(k^2)}$, and we found no sub-brute-force algorithm.
  **[Hedged: absence of evidence after a short search.]**

### 3.4 Can the HJ framework express Sun/IMQSZ?

**No, not as it stands.** **[SKETCH of the reasons]**

1. *Representation.* HJ manipulates permutation groups by generators, plus colorings. It sees a
   linear structure only as a primitive affine or classical permutation group, and enumerates it
   (§2.5).
2. *Primitives Sun needs.*
   * **Matrix-space individualization:** fix $L,R$ with $s=\tilde O(\sqrt\ell)$ rows and columns,
     label $A$ by $LAR$, costing $q^{\tilde O(\ell^{1.5})}$.
   * **Low-rank / noncommutative-rank characterization** of the kernel space.
   * **Ivanyos–Qiao's polynomial-time alternating matrix-tuple congruence**, which solves for an
     algebraic group via $*$-algebras. Its solution set is never a permutation-group coset that is
     enumerated or recursed on.

   All three need **bilinear (degree-2) structure** in the data.
3. *Data at HJ's bottleneck.* At an enumeration node the "coloring" seen by the quotient $P$ is a
   multi-coset structure: for each coset there is an arbitrary recursive sub-instance on the kernel
   orbits. This is a Luks-style relative problem, not a bilinear map. Even a perfect 3-tensor
   isomorphism oracle does not plug in.
4. *What a port would need.* A recognizer that detects when the instance at an affine node is a
   tensor of degree $\le3$, followed by an IMQSZ call. This gives speedups only in cases already
   covered by direct group-isomorphism or tensor-isomorphism algorithms. The generic affine node
   (Prop. 2 with arbitrary colorings) stays out of reach.
5. *Missing potential.* HJ's resources ($s,\rho,\sigma,Q,h$) do not measure "linear rank". Sun's
   progress comes from individualizing $\tilde O(\sqrt\ell)$ vectors and then making no further
   branching progress at all (polynomial linear algebra). Charging that would need a new resource.

### 3.5 Other barriers

* **Neuen–Schweitzer (STOC 2018):** individualization-refinement algorithms take $2^{\Omega(n)}$ when
  their refinement, cell selector and invariants are within fixed-dimension WL. This rules out pure
  IR (nauty/Traces style, including `gi-practical`'s IR front end) as a route even to
  quasipolynomial time. It says nothing about Luks–Babai–HJ, which use group theory.
* **CFI (1992):** WL dimension $\Omega(n)$ for graphs, so WL alone is hopeless.
* **WL for groups:** whether finite groups have bounded WL dimension is open (Brachter's 2023
  thesis lists "potential sources for groups of unbounded WL dimension"). The trivial bound is
  $O(\log n)$. A bounded dimension would put group isomorphism in P. So there is no WL-based lower
  bound at the $\log n$ scale for the group barrier.
* **Lower bounds for group-theoretic algorithms:** we know none for Luks/Babai-type recursions.
  Prop. 2 is a lower bound for one specific algorithm (HJ), not for a model.

---

## 4. Attempts

### 4.1 Attempt A: a refined potential (works; gives the conditional result)

**Hypothesis class.** $\hat\Gamma_d$ is the class of groups whose composition factors embed in
$S_d$, i.e. composition width $\mathrm{cw}\le d$ (Grohe–Neuen–Schweitzer, Def. 2.3). It is closed
under subgroups, quotients and sections. In it, $\mathrm{aw}\le d$, so every giant has $q\le d$.

GNS Theorem 3.13 says a primitive $\hat\Gamma_d$ group either has order $\le n^{c_1\log d+c_2}$, or is
a Cameron group with $\mathrm{Alt}(m)$, $m\le d$, in a Johnson product action. GNS also remark that
the bound fails for the larger class $\Gamma_d$: $\mathrm{AGL}(d,p)\in\Gamma_d$ has order
$n^{\Omega(d)}$.

**Dispatcher modification (M).** At a primitive quotient, never enumerate a Cameron-large group
with $m>q_0$; always use product refinement, normalization and the giant step. Enumerate only
non-Cameron groups or $m\le q_0$. HJ's analysis already covers both branches. Under HJ's order
test (L1766–1772), Cameron groups $\mathrm{Alt}(m)^r$ with $r\gtrsim m/\log m$ get enumerated at
cost $\approx d^{m}$, which is too much here.

**Theorem R.** **[SKETCH, CONDITIONAL]** Assume (H0)–(H2):

* (H0) HJ is correct.
* (H1) Cameron-large primitive groups with $m>q_0$ can be constructively recognized
  deterministically in polynomial time. This replaces HJ's exceptional recognition range, which
  HJ enumerates (L3067–3087). GNS must handle the same groups; Babai's Johnson-scheme recognition
  is the expected tool. **Not checked.**
* (H2) The grouping in §2.1 holds: the $\le2\binom q\kappa s\kappa!$ and $\le4q^{2\kappa}s$ calls
  form $q^{O(\kappa)}$ disjoint-domain families.

Then for $G\in\hat\Gamma_d$ on $N$ positions, HJ with (M) solves string isomorphism in
$$\exp\big(O(\log N\cdot(\log d+\log\log N))\big)\cdot\mathrm{poly}(\text{input}).$$

*Proof sketch.* If $d>N^\alpha$ the claim is HJ's own bound, so assume $d\le N^\alpha=\lambda$.

1. **No wide giants.** `GiantStep` never takes the $q>\lambda$ branch. So there are no RowStep, no
   row terminal and no in-domain rectangles, and $E_N=1$. Configurations are fresh calls on
   $\mathrm{Sym}(C)$ acting on $C^2$ with $|C|\le q\le d$. They stay in $\hat\Gamma_d$.
2. **Potential.** Use $\Phi_\Lambda=A(x\Lambda+\rho\ell_N+\sigma\Lambda+Q_d)+Bh$ with
   $\Lambda=C_1(\log d+\log\log N+1)$. Here $\ell_N$ is from Lemma 1, and $Q_d$ uses caps
   initialized at $\min(d_i,d)$.
3. **Row by row** (as in L1795–1820):
   * *Affected test, large symmetry:* multiplicity $\le C_\kappa d^{2\kappa}$, drop
     $\ge A\Lambda c_\theta$. In-domain rectangles need $q>\lambda$, so they do not occur.
   * *Unaffected test:* multiplicity $C_\kappa d^{2\kappa}$, drop $A\kappa\Lambda$.
   * *Product refinement:* Lemma 1.
   * *Enumeration of non-Cameron $P$:* $|P|\le d'^{c_1\log d+c_2}$ (GNS 3.13); the drop
     $A\Lambda(x-\log(s/d'+2))\ge\tfrac A3\Lambda\log d'$ pays.
   * *Enumeration of small Cameron $P$ ($m\le q_0$):* $|P|\le(q_0!)^r2^rr!$ with $d'\ge5^r$; this
     needs $\Lambda\gtrsim\log r$, which $\log\log N$ covers.
   * *Continuation:* $q^a$ with $q\le d$, against $Q_d$'s drop $\ge c_\beta\log q$ (eq.
     main-cap-payment, using only "old cap $\ge q$").
   * *Row events:* not reached.
4. **Root.** $\Phi_\Lambda\le A\big(\log N\cdot\Lambda+2\log_2N\,\ell_N+C\log N\cdot\Lambda+\log N\log d\big)+2B$,
   which is $O(\Lambda\log N)$.
5. **Phase and recurrence.** Lemma 7.1's induction goes through verbatim. The weight prefactor
   $(s+2)^D$ still pays the polynomial node toll, since $s>N^\gamma$. So the phase cost is
   $\exp(O(\Lambda\log N))(1+F_d(N^\gamma))$, and §2.7 sums it. ∎

**Corollary.** **[CONDITIONAL]** Graph isomorphism for maximum degree $d$ runs in
$n^{O(\log d+\log\log n)}$. This uses the polynomial-time Turing reduction to string isomorphism
for $\mathrm{cw}\le d-1$ (Neuen, *Comput. Sci. Rev.* 60 (2026), Lemma 4.5).

**Novelty check.** GNS (FOCS 2018, SICOMP 2023), Neuen (ICALP 2020) and Neuen's February 2026
survey (Theorems 4.6 and 4.9) give $n^{\mathrm{polylog}(d)}$ with unspecified constant $c$. GNS use
test sets of size $t>\max(8,2+\log_2d)$, hence $d^{O(t^c\log^c d)}$-type costs. We found no
$n^{O(\log d)}$-type bound, and HJ do not state one. So the corollary is new relative to the
literature we checked, conditional on HJ.

* The $\log\log N$ term comes only from top groups in $S_r$, $r\le\log_2N$. It should be removable
  with a Babai–Cameron–Pálfy-type bound $|\mathrm{top}|\le d^{O(r)}$ for $\hat\Gamma_d$ subgroups of
  $S_r$. **Not checked.**
* For $d<\log n$ the bound can be worse than GNS's $n^{(\log d)^c}$; take the minimum.

**Where it breaks for general graph isomorphism.** **[PROVEN]** At the root,
$\mathrm{cw}(\mathrm{Sym}(n))=n=\sqrt N$, so $\Lambda=\Theta(\log N)$. The theorem reproduces
$\log^2$ exactly. "Bounded alternating width" alone is not enough: $\mathrm{AGL}(k,2)$ has
$\mathrm{aw}=O(\log N)$ but $\mathrm{cw}\approx N$ and $\mu=\Theta(\log N)$ (Prop. 2). The correct
extra hypothesis is small *composition* width. That bundles "no large alternating sections" (the
$\log w$ channels) with "no large-rank Lie-type sections" (the $\mu$ channel).

### 4.2 Attempt B: replace quotient enumeration by recursion along a base

**Statement needed.** For a Maróti-small primitive $P$ of degree $d$ with base size $b(P)=O(\log d)$
(Liebeck; $\le\lceil\log d\rceil+1$ by Moscatiello–Roney-Dougal), replace "enumerate $P$" by
"individualize one block, recurse on the stabilizer's orbits", with cost $d^{o(\log d)}$.

**Where it breaks.** **[PROVEN for the family]** Take $P=\mathrm{AGL}(k,2)$ or $\mathrm{PGL}(k,2)$.

1. Fixing a point of $\mathrm{AGL}(k,2)$ leaves $\mathrm{GL}(k,2)$, which acts 2-transitively on
   the other $d-1$ points (as $\mathrm{PGL}(k,2)$ on $\mathrm{PG}(k-1,2)$). Fixing a point of
   $\mathrm{PGL}(k,2)$ leaves a group that is transitive on the remaining points. Its visible block
   system pairs the two other points of each line through the fixed point, so the quotient has size
   $(d-1)/2$. So the recursion is $T(d)\approx d\cdot T(d/2)$, i.e. $d^{\Theta(\log d)}$.
2. Every branch-on-images scheme without colour pruning has leaves in bijection with elements of
   $G$, and a minimal base has $k+1=\log_2d+1$ points, each with $\Omega(d)$ images.
3. Luks's divide-and-conquer needs a block system with a small quotient. The quotient
   $\mathrm{PSL}(k,2)$ has minimal degree $2^k-1\approx d$, so there is nothing to divide.
4. Babai's local certificates need an alternating quotient $\mathrm{Alt}(m)$ with $m>2+\log_2$ of the
   domain. $\mathrm{PSL}(k,2)$ is not alternating, and its smallest faithful "test" is the whole space.

With arbitrary colorings, pruning would have to come from a WL-type refinement of the affine
structure, which is the problem of §3.3. **The break point is exactly the classical-group primitive
section, where permutation-group methods have no smaller action to recurse on.**

### 4.3 Attempt C: a better phase recurrence, or polynomial shrinking inside a phase

**Statement needed.** Either (i) a sharper outer recurrence, or (ii) every charged step with
$N^{\Omega(1)}$ branching shrinks the domain polynomially ($s\to s^{1-\varepsilon}$). With (ii),
chains have length $O(\log\log N)$ and the exponent is $O(\log N\log\log N)$.

**Where it breaks.**

* (i) is pointless: the recurrence is lossless (§2.7).
* (ii) holds for geometrically affected children (Lemma J) and for the shrinking already used for
  fresh calls.
* (ii) fails for **same-domain continuations**: cap contraction (§2.4), unaffected tests (§2.3) and
  product refinement. It fails as well for constant-fraction rectangles and algebraically affected
  children.

Making cap contraction polynomial would need a "polynomial-shrinking Split-or-Johnson": $O(1)$
individualizations reducing every giant from $q$ to $q^{1-\varepsilon}$. That would improve
conference graphs, Latin-square graphs and Steiner triple systems beyond their 1978–80 bounds
(§3.2). **[CONDITIONAL]** With such a procedure, the giant channels cost
$\exp(O(\log N\log\log N))$ and the exponent becomes $O(\log N(\log\log N+\mu))$.

### 4.4 Attempt D: port Sun-type ideas to the enumeration bottleneck

**Statement needed.** At an affine enumeration node $P=V\rtimes H$, $V=\mathbb F_p^k$,
$H\ge\mathrm{SL}(V)$, decide the relative multi-coset problem in $p^{O(k^{2-\varepsilon})}$.

**Where it breaks** (see §3.4).

1. The data at the node is not bilinear. The kernel-orbit sub-instances are arbitrary, so neither
   matrix-space individualization nor Ivanyos–Qiao applies.
2. Specialize to trivial kernels. The problem becomes string isomorphism under $\mathrm{AGL}(k,p)$
   of arbitrary colorings. That contains truth tables of quartic forms and 4-tensors, for which the
   known reductions to 3-tensors make IMQSZ worse than brute force.

**[CONDITIONAL]** Suppose string isomorphism under classical groups in natural action, in the
relative (multi-coset) form, is solvable in $d^{O(\log^{1-\varepsilon}d)}$. Then the $\mu$ channel
costs $\exp(O(\log^{2-\varepsilon}N))$. The full exponent is then
$O(\log N\log w+\log^{2-\varepsilon}N)$, still $\log^2$ for graph isomorphism because of $w$. This
hypothesis is at least as strong as $2^{o(k^2)}$ affine equivalence of Boolean functions.

### 4.5 Attempt E: extra hypotheses the user suggested, tested against Theorem R

| hypothesis | effect on HJ's exponent |
|---|---|
| bounded (polylog) alternating width only | **no improvement**: $\mathrm{AGL}(k,2)$ (Prop. 2) |
| no Maróti-small primitive sections of large order only ($\mu=O(\log\log N)$) | no improvement: $\mathrm{Sym}(n)$ giants keep $\log w=\Theta(\log N)$ |
| both (composition width $\le d$) | $N^{O(\log d+\log\log N)}$ (Theorem R) |

---

## 5. Verdict

**Proven here (given HJ as written).**

* The hierarchy term $\rho x$ is slack (Lemma 1).
* The outer phase recurrence is lossless.
* HJ's string-isomorphism algorithm is $N^{\Theta(\log N)}$ on $\mathrm{AGL}(k,2)$ (Prop. 2). So
  HJ's Theorem 1.2 bound is tight for HJ's algorithm.
* Bounded alternating width alone does not help.
* Graph isomorphism in $n^{o(\log n)}$ implies $n^{o(\log n)}$ for group isomorphism, quasigroup
  isomorphism, Steiner triple systems and conference graphs, and $2^{o(k^2)}$ affine equivalence of
  colorings of $\mathbb F_2^k$ (Prop. 3, §3.1–3.3).

**Sketched.**

* The true multiplicities are $q^{O(\kappa)}$, not $N^{O(1)}$ (§2.1). It follows that the exponent
  is $O(\log N(\log w+\mu+\log\log N))$ (§2.9).
* Geometrically affected children are cheap (Lemma J).
* Theorem R and its corollary for degree-$d$ graph isomorphism, conditional on HJ, (H1) and (H2).

**Speculation.**

* The $x^2$ and $\sigma x$ channels are never tight.
* HJ is $n^{\Theta(\log n)}$ on conference graphs or Latin-square graphs through the cap channel.
* No permutation-group-only method beats $\log^2$ for string isomorphism under classical groups.

**The honest answer.** Within the HJ framework, the $\log^2$ is the product of two independent
$\Theta(\log N)$ factors, and each factor matches a classical open problem.

1. *Giant breaking* (Babai's core) costs $\log N\cdot\log w$. Breaking a degree-$\sqrt N$ giant
   with $o(\log N)$ rounds of polynomial branching would beat the $n^{O(\log n)}$ bounds for
   conference graphs, Latin squares and Steiner triple systems, which date from 1978–80.
2. *Enumeration of classical primitive sections* costs $\log N\cdot\mu$ and is provably paid by HJ.
   Avoiding it requires non-permutation-group (linear-algebraic) methods on arbitrary colorings.
   That is at least as hard as $2^{o(k^2)}$ affine equivalence, and it is where Le Gall–Rosenbaum
   locate the group-isomorphism obstacle ($\mathrm{PSL}$).

So "graph isomorphism faster than $n^{O(\log n)}$" is at least as hard as group isomorphism (via the
$O(m^2)$-vertex Cayley-graph reduction) and at least as hard as quasigroup isomorphism. It is also
at least as hard as $2^{o(k^2)}$ affine equivalence of truth tables (via the $O(N^3)$-vertex
affine-plane reduction). Sun and IMQSZ show the first barrier is not uniform: its best-known hard
subclass fell. Nothing comparable is known for the second and third.

---

## 6. Suggested next steps (cheap)

1. Check (H1): does GNS18 §3–4, or Babai's Johnson-scheme recognition, give deterministic
   polynomial-time constructive recognition of Cameron-large groups for all $m>q_0$? This decides
   whether Theorem R needs (M) plus extra work.
2. Check (H2) against the Lean `Script`/`Exec` call structure (`Paper/ScriptCalls.lean`). Are the
   $s$ window calls of one test recorded as disjoint-domain forests, so that $q^{2\kappa}$ (not
   $N^a$) bounds the branches?
3. Find a Babai–Cameron–Pálfy-type bound $|T|\le d^{O(r)}$ for $\hat\Gamma_d$ subgroups $T\le S_r$.
   It would remove $\log\log N$ from Theorem R.
4. `gi-practical` stress families for the worst case (not run here; CPU budget):
   * string isomorphism under $\mathrm{AGL}(k,2)$, $k=6,7$. Prop. 2 predicts
     $\approx0.29\cdot2^{k(k+1)}$ cosets, about $1.3\cdot10^{12}$ at $k=6$, so the solver should
     hit its enumeration cap;
   * Paley and conference graphs; Latin-square graphs; STS block-intersection graphs (the cap
     channel).

---

## References (verified by search on 2026-11-04 unless marked)

* Hajiaghayi, JafariRaviz, arXiv:2611.01399 (HJ); Lean: github.com/mahdi-jfri/GraphIsomorphismLog2.
* X. Sun, *Faster isomorphism for p-groups of class 2 and exponent p*, STOC 2023, arXiv:2303.15412.
  $N^{O((\log N)^{5/6})}$, $p>2$.
* G. Ivanyos, E. Mendoza, Y. Qiao, X. Sun, C. Zhang, *Faster isomorphism testing of p-groups of
  Frattini class 2*, FOCS 2024, pp. 1408–1424. $N^{\tilde O((\log N)^{1/2})}$; Thm 3.2: matrix-space
  equivalence (3-tensor isomorphism) in $q^{\tilde O(\ell^{1.5})}$.
* D. Rosenbaum, *Bidirectional collision detection and faster deterministic isomorphism testing*
  (arXiv, 2013; from memory). F. Le Gall, D. Rosenbaum, *On the group and color isomorphism problems*,
  arXiv:1609.08253 (PSL as the main obstacle).
* H. Dietrich, J. Wilson, *Group isomorphism is nearly-linear time for most orders*, FOCS 2021.
* M. Grohe, D. Neuen, P. Schweitzer, *A faster isomorphism test for graphs of small degree*, FOCS 2018
  / SICOMP 52(6) 2023, arXiv:1802.04659 (Def. 2.3, Thm 3.13).
* D. Neuen, *Hypergraph isomorphism for groups with restricted composition factors*, ICALP 2020.
* D. Neuen, *Parameterized complexity of graph isomorphism testing*, Comput. Sci. Rev. 60 (2026)
  100918 (Lemma 4.5, Thms 4.6, 4.9).
* M. Levet, *On the complexity of identifying strongly regular graphs*, Australas. J. Combin. 87(1)
  (2023) 41–67.
* M. Gill et al., *Canonical labelling of Latin squares in average-case polynomial time*, Random
  Structures Algorithms 2025, arXiv:2402.06205.
* G. Miller, *On the $n^{\log n}$ isomorphism technique*, STOC 1978; *Graph isomorphism, general
  remarks*, JCSS 1979 (from memory).
* D. Neuen, P. Schweitzer, *An exponential lower bound for individualization-refinement algorithms
  for graph isomorphism*, STOC 2018 (from memory; also summarized in HJ L236–243).
* J. Brachter, P. Schweitzer, *On the Weisfeiler–Leman dimension of finite groups*, LICS 2020;
  J. Brachter, PhD thesis, TU Darmstadt 2023.
* J. Grochow, Y. Qiao, *Isomorphism problems for tensors, groups, and cubic forms* (TI-completeness),
  SICOMP 2023; *On p-group isomorphism: search-to-decision, counting-to-decision, and nilpotency class
  reductions via tensors*, CCC 2021.
* A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002) (as used in HJ, L3069–3076;
  Lean `Cited/MarotiPrimitive.lean`).
