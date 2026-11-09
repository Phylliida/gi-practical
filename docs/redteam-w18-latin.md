# Red team: w18-latin (Theorem B1, A1, A2, A3 and the sketches)

Referee memo, branch `w26-redteam-pg`, 2026-11-08. Target: `docs/w18-latin.md` at `be65c62` and its
two simulations. HJ = arXiv:2611.01399, LaTeX `L…` line numbers. Exact replay: `docs/redteam-w18-latin-check.py`.

## 0. Verdicts

| Claim | Verdict | One-line reason |
|---|---|---|
| **B1** (HJ makes $\ge 2^{m^2/2-O_\kappa(m)}$ calls on $X_m$) | **SOUND as a statement about HJ as written, with one constant wrong** | Hand-check of Lemma 1, Lemma 2, dispatcher and count found no break. Exact replay reproduces Lemma 1 windows and the Step 4 orbit at $\kappa=5$. The enumeration cutoff is not $q_0$ (§2.4). |
| B1 count and exponent | **sound** | $\sum_{j<J}\log_2\frac12\binom{q_j}{\kappa}=m^2/2+O_\kappa(m)$; $n=(k-1)(k+4)/6$ gives $\frac18\log_2 n$. Asymptotic only: no nesting below $m=214$ at $\kappa=64$ (§2.5). |
| B4 ($\Theta$ on graphs) | **sound as an implication** | The upper half is HJ's unrefereed theorem. The lower half is B1. |
| **A1** | **sound, 4 repairs needed** | Doubling and collision are correct. The isotopy sketch has a false sentence (degenerate triples); the Latin-square-graph exponent is miscalculated ($\frac18$, not $\frac14$). Novelty "not found" stands but is routine. |
| A2 | **sound** | Lattice DP correct. |
| A3 | **sound**, 2 wording fixes | $\emptyset$ in the count; "index" is a size ratio (no Lagrange). |
| B2 (LS graphs, block graphs) | **gap, as labelled** | Root entry unverified; my small replays do not exhibit the claimed chain. |
| B3 (Paley) | **gap, as labelled** | First window goes nonfull, as said. The polynomial claim is unproved. |
| §2.9 rigid variant | **gap, as labelled** | Plausible, not checked. |

No claim is broken. **The strongest statement I would sign is §6.**

## 1. What was checked

Read directly: HJ Algorithms 1, 3, 4, 5 and 6 (L589–600, L774–811, L1033–1063, L1136–1179, L1270–1290), the
carrier policy (L1206–1218), parameters (L1739–1847), endpoint construction and call types (L2619–2721),
budget (L1932–2012, L2474–2492, L2582), large symmetry (L2868–2977), quotient selection (L3176–3216),
row normal form (L3530–3596). The Lean tree was only read, never run: `Assembly/Params.lean`,
`Algorithm/Dispatch.lean`, `Paper/LocalCertificates.lean`, and the header comments of
`Impl/AggCertRep.lean`, `Impl/AggCache.lean`, `Impl/AggCertProg.lean`, `Impl/AggSubProg.lean`. I did not
audit the `Impl/` programs beyond those headers.

**Assumed, not checked:** HJ's correctness (exact answers from every recursive call). Everything below is about the recursion the paper specifies.

## 2. Theorem B1

### 2.1 Does HJ take this path?

Every potential interception I could find, and its disposition:

| Possible interception | Where | Outcome |
|---|---|---|
| Root is intransitive | L1150, L622 | Off-diagonal orbit is largest and goes first. Fine. |
| RowStep at root ($q=n>\lambda=n^{0.8}$) | L1164–1167 | Kernel of $\mathrm{Alt}(n)$ on ordered pairs is trivial, so kernel orbits are singletons indexed by two labels: not natural. No RowStep. |
| Enumeration | L1154, L1769–1772 | Applies below a much larger cutoff than the note says (§2.4). Constant change only. |
| Product refinement | L1154 | $r=1$ for natural $\mathrm{Sym}(q_j)$. |
| Tower ambiguity at level $j$ | L1153, L3177 | The maximal block systems of $\mathrm{Sym}(\widetilde W_j)\times H_j$ are exactly rows and $D_j$-cosets, so the note's two cases are exhaustive. Inherited $D_{j-1}$-coset intervals expose $D_j$-cosets as the unique maximal system above them. |
| RowStep at level $j$ | L1279–1288, L3530 | Kernel is diagonal $H_j$, so $N=N^*=1$, $L=1$, columns are singletons, and `Continue` reaches $\mathrm{Sym}(Q_j)$. If the row record were retained instead (L1207 says only "may lose"), dispatch goes above the column floor to the same quotient. Both branches agree. |
| Early `Full` return | L789 | Cannot fire: $U\supseteq\widetilde W_{j+1}\times P_{j+1}$, so $A_{(U)}$ fixes $P_{j+1}$ pointwise, forcing $\tilde\tau=\mathrm{id}$, $\sigma=1$. The full certificate arrives only after the recursion. |
| Aggregation, large symmetry, rectangles | L1170–1176 | All run after the certificates are computed (L1168). They cannot prevent the calls being counted. |
| Pruning or memoization | L359, L705, L1168 | None in the paper. Lean: `Impl/AggSubProg.lean` lists all $\kappa$-subsets in `sbOrder q κ`; the only cache described (`AggCache.lean`) stores coset representatives, not recursive answers. |
| Phase threshold | L1149 | Root child: $\lvert\Delta\rvert\approx k^3/6\le N^{0.9}$ starts a fresh phase $N'$. Later levels have $\lvert\Omega_j\rvert\approx N'>N'^{\gamma}$, so they stay inherited. |
| $q_j$ vs $\lambda'$ | L1164 | $q_j<k<\lambda'\approx k^{1.2}/2.05$ once $k\ge 36$. No RowStep on $\Gamma=Q_j$. |

### 2.2 Lemma 1 (level step): sound

I re-derived it line by line. The points that needed care all hold:

* Full image at every stage is witnessed by a linear $g$ with $g|_{D_j}=\mathrm{id}$, which lies in $H_j$ and preserves $\widetilde W_j$.
* The $V_1$ path argument gives $\rho|_{D_{j+1}\setminus D_j}=\tilde\tau$, including on $\Sigma$ (for $|I|\ge 3$ via a block with $S=\{a_c\}$). So $V_3$ imposes nothing new.
* $\delta_c$ is genuinely free: the block through $a_c$ and $a_c+d$ has third point $d\in D_j$, excluded unless $d\in Z_j$.
* Class sizes $|W(S)|=|W(\rho S)|$ follow from the linear extension.
* $\mathcal U_{j+1}$ preserves $Z_{j+1}$.
* Parity: the note's lemma is enough for the image statements, and the family is closed under the recursion (commutators of lifts land in $[G_j,G_j]\le G$). The note should say the closure explicitly, one line.

**Proof-text gap (fixable, does not affect $\kappa\ge5$).** The $V_3$ step says the stabilizer of $w\in W^{(2)}$ is proper because $S'$ "contains some $p\in D^*$". That is not enough when $|S'|=3$: $\mathrm{Alt}(T)$ could permute the three index sets. The claim needs that $\mathrm{Alt}(\kappa)$, $\kappa\ge5$, has no proper subgroup of index $\le 3$ and fixes no proper nonempty subset of $T$. It is **false at $\kappa=3$**: for $T=\{1,2,4\}$ the block $\{3,5,6\}\subset D^*$ is preserved by all of $\mathrm{Alt}(T)$, and my $m=5$ replay finds 77 rows in $U$, not 76, with $V_3$ short by exactly one row. The $\kappa=3$ level-2 run is short by exactly 16 rows, which is the number of such lines there (I matched the counts, not the row identities). So the note's $\kappa=3$ simulations are not exact instances of Lemma 1, and the note's "Levels and windows match Lemma 1 exactly" needs this caveat.

### 2.3 Lemma 2 (root): sound

Same re-derivation. `C_∅` splitting after $V_1$, the point pairs $(p,p+d)$, $d\ne 0,\Sigma$ in $V_2$, and the selection of $\widetilde W_1\times P_1$ as largest visible orbit all hold. Block-pair orbits are invisible and are not in $V$, so they do not displace the chain child, though they are larger.

### 2.4 Error: the cutoff is not $q_0$

§2.1 and §2.5 of the note use $q_0$ as "absolute degree cutoff" and write "$q_j>q_0$, order above $\exp(a\log^2 q_j)$". That inference is wrong. HJ requires $q_0!\le\exp(a\log^2 2)$ (L1769), so $a$ is large, and the enumeration test then accepts degrees far above $q_0$. With Lean's values $a=36000$, $q_0=2064$ and the test $|\rho(G)|\le d^{\,b\lfloor\log_2 d\rfloor}$, $b=\lfloor a\ln 2\rfloor=24953$ (`Dispatch.lean:358`), the largest accepted symmetric degree is
$$q_1=486290,\qquad \log_2 q_1\approx 18.89.$$
**Fix:** define $q_1(a,\kappa)$ as the largest degree accepted by the enumeration test and take $c=\lceil\log_2 q_1\rceil+\kappa+3$ (about 86 for $\kappa=64$, not 78). Asymptotics are unchanged. Also, "for any fixed $\kappa\ge5$" must be read as a family of algorithms $\mathrm{HJ}_\kappa$ with $a,q_0,N_0$ depending on $\kappa$; the theorem needs $m\ge m_0(\kappa,a,N_0)$, which the statement omits.

### 2.5 The count, and whether it is vacuous

The product is right and $n=(k-1)(k+4)/6$, so $2^{m^2/2}=n^{\frac18\log_2 n+O(1)}$. Exact evaluation for $\kappa=64$, $c=86$:

| $m$ | $J$ | $\log_2$ bound | $(\log_2 n)^2/8$ |
|---|---|---|---|
| 150 | 1 | 9303 | 11057 |
| 214 | 2 | 22702 | 22622 |
| 300 | 3 | 44421 | 44613 |
| 1000 | 14 | 519106 | 498708 |

Reading of "vacuous": the bound is a valid asymptotic statement. **Below $m=150$ ($n\approx 2^{297}$) there are no levels, and nesting needs $m\ge 214$ ($n\approx 2^{425}$).** For every feasible $n$ the chain does not exist at $\kappa=64$, so B1 says nothing about behaviour at feasible sizes. The sign of the $O_\kappa(1)$ flips: for large $m$ the bound exceeds $n^{\frac18\log_2 n}$ by about $2^{(\kappa/2-\log_2(2\kappa!)/\kappa)m}$.

Cross-check against HJ's own budget: the chain has total marked weight $\kappa J\approx m$, against $\sigma\le C\ln s-B$ with $C\ge128$ (L2480, L2582). No contradiction, and it is far from tight in that constant.

### 2.6 What the simulations support

* **The note's two scripts:** $\kappa=3$, $m\le7$; `w18-latin-sim.py` tests one sample per *predicted* position type, so the type partition is assumed; `Alt(3)` is abelian; the root script never reached Step 4. They support the window pattern at levels 0–1 and nothing about nesting, counts, or Step 4 visibility in the simple-group regime.
* **My replay** (`redteam-w18-latin-check.py`) computes each window from the automorphism group of a gadget graph, with one representative per orbit of the current group and no position types. $A_i$ comes from the prefix-recovery identity (L2654–2664), so it tests the groups, not HJ's recursive calls. Results:

| Run | Windows found | Step 4 |
|---|---|---|
| Root model, $\mathrm{Sym}(n)$ on ordered pairs, $m=5$, $\kappa=3$ | $V_0,\dots,V_3$ | Reached in 2 s (the note's root script timed out here). Not full. Largest selected orbit $1824=76\times24$. Block-pair orbits invisible. |
| Root, $m=6$, $\kappa=4$ ($n=714$) | $V_0,\dots,V_3$ | Reached. Not full. Largest selected orbit $13440=280\times48=\widetilde W_1\times P_1$, as Lemma 2 predicts. Block-pair orbit (78120) invisible. |
| Root, $m=7$, $\kappa=5$ ($n=2794$) | $V_0$ only (27910 pairs); in the next round 12 of 13 orbit representatives were affected | Stopped by me before Step 4; each nauty call took about a minute. No evidence for or against. |
| Level 0, $m=7$, $\kappa=5$ | $V_0..V_3=13335,37210,59050,125130$, each equal to the Lemma 1 formula | Selects exactly $\Delta=1072\times96$. $\widetilde W_1\times\Sigma$ invisible. |
| Level-1 shape ($D=\langle1\rangle$, $Z=\{1\}$), $m=7$, $\kappa=5$ | $26670,67860,104100,131010$, each equal to the formula | Selects exactly $\Delta=97\times64$. |
| Level-2 shape ($\mathcal U\ne1$), $m=7$, $\kappa=3$ | Equal to the formula except $V_3=59400=61000-16\cdot100$ | Main orbit $1367\times96$, plus two orbits on 16 further rows, matching the count of artifact lines from §2.2. |
| Level-2 shape ($\mathcal U\ne1$), $m=7$, $\kappa=4$ | $42672,95904,71160,105264$, each equal to the formula | Selects exactly $\Delta=231\times64$. $\widetilde W\times\Sigma$ invisible. No artifact rows. |


Each level-state window size was compared with the Lemma 1 formula (`predict` mode): at $\kappa\ge4$ they agree exactly, and at $\kappa=3$ the difference is exactly the §2.2 artifact. The root rows compare only the Step 4 orbit and $U$, not every window. This is still small: no run nests two certificate calls, and $\kappa=64$ is out of reach. It upgrades the windows and the Step 4 selection from "checked at $\kappa=3$" to "checked at $\kappa=5$ at level 0 and on a level-1 state, and at $\kappa=3,4$ with nontrivial $\mathcal U$". No run has $\kappa\ge5$ with $\mathcal U\ne1$.

## 3. A1, A2, A3

**A1: sound.** Doubling ($xS\cap S=\emptyset$), chain length $\le\lfloor\log_2 n\rfloor+1$, canonical tables and the collision argument are correct. Repairs:

1. "Extends each to a generating tuple arbitrarily" must be **strictly increasing**, or $\varphi$ of Alice's tuple is not in Bob's list. (Rosenbaum's tree has this built in; the note's wording dropped it.)
2. Bob's greedy chain can exhaust $Q'$ before length $d$. In the branch where $Q$ is not $d$-generated this certifies "non-isomorphic", and the proof should say so. (The note's own Miller branch covers the case that $Q$ is $d$-generated. My first test omitted that branch and returned a false negative on an order-8 Latin square; with it, the test is correct.)
3. **Isotopy sketch has a false sentence.** "A closed triple $(R,C,S)$ has $|R|=|C|=|S|$" fails for degenerate triples: $(R',\emptyset,\emptyset)$ is closed for any $R'$, so a three-sorted chain can have length about $n$. Fix: start every chain with a pair $(r_1,c_1)$. Then nondegenerate closed triples are subsquares, a proper one has order at most half, and length is $\log_2 n+O(1)$.
4. **Latin-square graphs:** $k^{\frac12\log_2 k}=N^{\frac18\log_2 N}$ for $N=k^2$. The note's $N^{\frac14\log_2 N}$ is Miller's exponent, not the halved one. The stated bound is true but the speedup is not what was claimed. Net recovery remains "from memory" (Bruck/Bose, order above a constant).

Machine sanity check: Steiner quasigroup of order 15 and order-8 Latin squares, relabelled and non-isomorphic pairs, correct after repair 2.

Novelty: Rosenbaum's §§2–3 is a generic tree-of-strictly-increasing-generators framework, and its text (v2) has no mention of Latin squares, quasigroups or Steiner systems. Le Gall–Rosenbaum §2.2 is group-specific. Gill–Mammoliti–Wanless and Levet state only $n^{O(\log n)}$ for quasigroups. "Not found" stands. It is a one-paragraph application, and should be described that way.

**A2: sound.** Every step checks, including that the isomorphism on $S=\langle T,x\rangle$ is determined by its restriction to a maximal $T$ and $\varphi(x)$. The direct-product example remains conditional, as labelled.

**A3: sound.** Fixes: count or exclude $\emptyset$ ($M\ge2^r$ versus $2^r-1$); "index" means the size ratio, since subquasigroup orders need not divide $n$.

## 4. The sketches

* **B2.** The root entry is the weak point. T "generic" needs $2\kappa\le m$, so $n\ge 4096$ at $\kappa=3$; I could not replay that. At $m=4$ with three cells (not generic) the certificate went **Full at iteration 3 with no Step 4**; the block graph at $m=5$, $\kappa=3$ (pencil tests) reached Step 4 but with 15 tiny visible orbits. Neither exhibits the claimed chain, and neither refutes it. Keep [SKETCH].
* **B3.** Paley(101), $\kappa=5$: nonfull at the second iteration, as described. "Polynomial" requires the unwritten aggregation accounting. Keep [SKETCH].
* **§2.9 rigid variant.** Keep [SKETCH]. The "no sharing" count there depends on chains avoiding the switched block at every level, not just a final span.

## 5. Corrections to make in `docs/w18-latin.md`

1. Replace $q_0$ by the enumeration cutoff $q_1$ in Theorem B1 and §2.5; add $m\ge m_0(\kappa,a,N_0)$.
2. Lemma 1, $V_3$: state the $\kappa\ge5$ argument; note the $\kappa=3$ failure and its effect on §2.6.
3. Parity lemma: add the closure sentence.
4. §2.5: "Step-4 children clear them" should say "may clear; both cases agree".
5. A1: the four repairs in §3.
6. A3: the two wording fixes.
7. §0: state that B1 has no content below $m\approx150$ ($\kappa=64$), and that B4's upper half is conditional on HJ.

## 6. The strongest statement I would sign

> Let $\mathrm{HJ}$ be the algorithm of arXiv:2611.01399 as written: every $\kappa$-subset of the giant label set is tested, with no pruning or memoization of recursive calls. Assume its recursive calls return exact answers. Let $q_1$ be the largest degree of a symmetric group accepted by its enumeration test, and $X_m$ the point–line incidence graph of $\mathrm{PG}(m-1,2)$, $n=(2^m-1)(2^m+4)/6$. Then for $m\ge m_0(\kappa,a,N_0)$ and $J=\lfloor(m-c)/\kappa\rfloor$, $c=\lceil\log_2q_1\rceil+\kappa+3$, the recursion tree of $\mathrm{HJ}$ on $X_m$ has at least $\prod_{j<J}\frac12\binom{2^{m-j\kappa}-1}{\kappa}$ nodes, which is $2^{m^2/2-O_\kappa(m)}=n^{\frac18\log_2 n-O_\kappa(1)}$. The cost lies in the visible-orbit certificate branch, not in Maróti enumeration. An automorphism-pruning or memoizing variant is not covered. At the Lean parameters ($\kappa=64$, $q_1=486290$) the bound has no nested level below $m=214$, so it is an asymptotic statement about the algorithm's recursion and says nothing about feasible inputs or about the complexity of graph isomorphism.

> Quasigroup isomorphism, Latin-square isotopy and paratopy, and STS isomorphism are decidable in deterministic time and space $n^{\frac12\log_2 n+O(1)}$ (with $n$ the order, or the number of points), and Latin-square graphs on $N$ vertices of large order in $N^{\frac18\log_2 N+O(1)}$, assuming recovery of the net. This is a routine application of Rosenbaum's bidirectional collision framework; I found no earlier statement of it.

I certify the hand-check of Lemmas 1 and 2, the dispatcher path and the count. I do not certify HJ's correctness, the `Impl/` programs, B2, B3, or the rigid variant.

## 7. Reproduction

```sh
PY=/home/bepis/math/gi-practical-wt/r2-hybrid/.venv/bin/python
cd docs
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[]" "[1,2,4,8,16]"          # level 0, kappa 5 (~20 min)
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[[1]]" "[2,4,8,16,32]"      # level 1 shape, kappa 5
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[[1],[2]]" "[4,8,16]"       # nontrivial U, kappa 3
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[[1],[2]]" "[4,8,16,32]"    # nontrivial U, kappa 4
nice -n 19 $PY redteam-w18-latin-check.py root 5 "[1,2,4]"                     # root, kappa 3 (seconds)
nice -n 19 $PY redteam-w18-latin-check.py root 6 "[1,2,4,8]"                   # root, kappa 4 (~4 min)
nice -n 19 $PY redteam-w18-latin-check.py paley 101 "[1,2,5,11,23]"
nice -n 19 $PY redteam-w18-latin-check.py a1
nice -n 19 $PY redteam-w18-latin-check.py count
```
