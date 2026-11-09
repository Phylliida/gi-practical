# Referee report: w32-conference

Branch `w52-redteam-conference`, 2026-11-09. Adversarial referee of `docs/w32-conference.md` (target commit `306a469`). Code in `docs/redteam-w32-code/`, written from the memo's statements with no import of `docs/w32-code/`: its own finite-field construction, exact 1-WL (no hashing), own Spence parser and two-graph descendant code, exact $T$ arithmetic; nauty/dreadnaut for automorphism groups. Outputs in `docs/redteam-w32-code/results/`. Lean was not run; `~/math/GraphIsomorphismLog2` was not touched.

**Bottom line.** Every claim labelled [PROVEN] survives my hand re-derivation: Lemmas 2.1–2.4, Prop 2.5, Thm 3.2, Lemma 4.1, Thm 4.2. The constant $0.049$ is correct. Nothing in the memo's outcome (no $n^{o(\log n)}$; Question 6.5 open) is threatened. Real errors are in the data statements and in what is inferred from the theorems: the headline "$p$ reaches $0.28$ at $n=6561$" is a sampling artefact (exact maximum $0.1867$, and no pair at all reaches $0.2$); the "only $P(25),P(49)$" sentence is false for Spence's list; "all available" Spence coverage is a sample ($30$ of $412$ at $n=49$); and the sentence "the structure side must include tensor products" does not follow from Thm 4.2 as written (it follows from a short product statement that I prove in §3.3). The second case of Prop 2.5, presented as new, is already in Brouwer–van Eijl. Details below.

## 0. Verdicts

| # | Claim | Verdict | Severity |
|---|---|---|---|
| S1 | State of the art; Levet Q6.5 | **sound with fix**: the Q6.5 quote is exact; the constant $2$ in $n^{2\log_2n+O(1)}$ is not Levet's | low |
| S2 | Lemmas 2.1, 2.2 ($L^2$, $T\bmod 8$, $T\equiv2\bmod4$) | **sound**, exact on every Spence graph; novelty note | none / low |
| — | Lemma 2.3, Lemma 2.4, Weil corollary | **sound** | none |
| S3 | Prop 2.5 (2-rank) | **sound; attribution error**: both cases are in Brouwer–van Eijl §4, not only the first | low |
| — | "Prop 2.5 forbids [rows closed under product] globally" (§2.4, §4.4) | **gap** (no argument given) | low |
| S4 | Thm 3.2 (bad-pair reduction) | **sound**, quantifiers right; $p$ ignores sign-separation, so $B_c$ is larger than necessary | low |
| S5 | Lemma 4.1, Thm 4.2, $c\ge0.049$, Lemma X false | **sound** (exact checks §3) | none |
| S5 | "(at $n=6561$, $p$ reaches $0.28$)"; §4.2 "$0.24$ at $n=625$"; §6 "33057 pairs $p\ge0.2$" | **broken** (statement): sampling artefacts; exact $0.1867$, $0.1597$, and $0$ pairs | medium |
| S5 | "collision probability" and "$p$" used interchangeably; "for all $n$" | **sound with fix** | low |
| §4.3 | "Turyn shows the structured side must include tensor products" | **gap** (inference): Thm 4.2 gives only cliques of $B_c$ of bounded size; repaired in §3.3 | medium |
| §2.3, §4.4 | $\max\lvert T\rvert\ge n^{0.72}$; "no $\lvert T\rvert\ge n^{1-o(1)}$ seen" | **sound but understated**: Spence graphs have $\lvert T\rvert=n-3$ at $n=25,41,49$; Lemma 4.1 gives $n^{0.983}$ | low |
| §3.3 | "So base size $\le\log_2\lvert\mathrm{Aut}\rvert+O(1)$" | **non sequitur** (true for every permutation group; motion not needed) | trivial |
| §4.2 | $\lvert\mathrm{Aut}(W(V,V))\rvert=2\lvert\mathrm{Aut}V\rvert^2$ **[DATA]** | **sound; can be promoted** to a proved lower bound (§3.4) | none |
| S6 | Thm 5.1 | **unverifiable** as a sketch; label correct; the §4.1 sentence "true for … Paley (§5)" overstates it | low |
| S7 | "exact minimum depth 2 or 3" | **sound on what was actually run**, and I confirm it on the whole of Spence's list; "all available" overclaims coverage; "only $P(25),P(49)$: 3" false | medium |
| §1 | Spielman, BCSTW, Babai degree bound, Ponomarenko, Mathon | **sound** as checked against the sources available | none |
| w34 etc. | Consistency with w34, redteam-w35-w34 | **consistent**; one numeric mismatch explained in §6 | none |

## 1. Hand re-derivations

**Lemma 2.1.** $g=C_a\circ C_b$ has zeros at $a,b$, so $\|g\|^2=n-2$; $\mathbf1^Tg=(C^2)_{ab}=-1$; $T(a,b,\cdot)=Cg$, so $\|Cg\|^2=g^T(nI-J)g=n(n-2)-1$. Correct, and the sum includes the degenerate $v\in\{a,b\}$ as stated. Parameter conditions: $C^2=nI-J$ and $C\mathbf1=0$ hold exactly for $C=J-I-2A$ of a conference graph (from spectrum $0$ on $\mathbf1$ and $\mp\sqrt n$ elsewhere).

**Lemma 2.2.** Expanding $(1+C_a)(1+C_b)(1+C_v)$ on $U=V\setminus\{a,b,v\}$: $|U|=n-3$; the linear terms sum to $-2(s+t+u)$; the quadratic terms to $-3-(st+su+tu)$; $T$ unaffected by the restriction. So $T=8N-n+6+2(s+t+u)+(st+su+tu)$, exactly as stated. The mod-4 corollary needs $n\equiv1\bmod4$, and only there. $T(a,a,a)=0$ (degenerate), but the lemma is stated for distinct triples, so this is no counterexample.
*Novelty remark.* $N$ is the triple intersection number (Cameron–Goethals–Seidel), so the lemma says $T$ is an affine function of it; "likely folklore" is the right label. The $L^2$ identity is the corresponding row-norm statement for the idempotents. I found no statement of the mod-8 form; I did not search harder than web tools allow.

**Lemma 2.3 and its gloss.** $\sum_{x\in Q}C_v(x)=|Q|-2c_Q(v)-[v\in Q]$ is correct. The Fourier gloss ($1_Q=2^{-k}\sum_I\varepsilon_Ig_I$ on $V\setminus S$; $D_{vw}(a_i)=0$ because $v,w$ share a cell) is also correct, for $v,w\notin S$. One sloppy phrase: $|I|\le1$ is not "automatic up to bounded error"; $\langle D_{vw},g_I\rangle=0$ exactly for $|I|\le1$ when $a_i\notin\{v,w\}$. Harmless.

**Lemma 2.4 and Weil.** $\mathrm{tr}(D_v(nI-J)D_w(nI-J))=(n^2-2n)\langle C_v,C_w\rangle$; $\|M_v-M_w\|_F^2=2n^2(n-2)$. Correct. $\rho\ge(n-2)/(2B^2)$ with $B=2\sqrt q$ gives $\rho\ge\frac18(1-2/q)$; degenerate $(a,b)$ cost $(5q-6)/q^2$; so $p\le7/8+O(1/q)$. Correct. (Sign slip: for $C=J-I-2A$ on Paley, $T=+a_q(E)$, not $-a_q$; §5 follows the $B$-convention. Irrelevant, since only equalities of $T$ matter.)

**Prop 2.5.** $A^2+A=t(I+J)$ with $t=(n-1)/4$; $n$ odd, so $\mathbb Z_2^n=\mathbb Z_2\mathbf1\oplus\mathbf1^\perp$. $t$ odd: $A$, $A+I$ are units on $\mathbf1^\perp$, and $A\mathbf1=2t\mathbf1\equiv0$, so $\mathrm{rank}_2(A)=n-1$, $\mathrm{rank}_2(A+I)=n$. $t$ even: the 2-adic splitting (roots $r$ unit, $s$ non-unit, $r-s=\sqrt n$ unit) gives an integral eigenspace splitting of $\mathbf1^\perp$ with both eigenspaces of rank $(n-1)/2$. Correct.

**The remark on Prop 2.5.** "Prop 2.5 forbids [rows closed under pointwise product]" (§2.4, §4.4) has no argument. With zero diagonals the exact identity $C_a\circ C_b=\pm C_v$ fails trivially because the supports differ; off the diagonal, closure up to a three-point error is an affine statement, and the 2-rank does not obstruct error terms in that many coordinates. Say the 2-rank rules out an exact $\mathbb F_2$-subspace structure of the rows, or give the argument. Unlabelled and not load-bearing.

**Thm 3.2.** Quantifiers: for fixed $c$, there exists $S$ such that for every pair not in $B_c$, some test pair inside $S$ separates it within two rounds. The union bound over $\binom n2$ pairs is right ($m=\lceil2/c\rceil$ would already do; $3/c$ is harmless). A testing pair among individualized vertices separates $v,w$ after two rounds by Lemma 2.3 ($v,w$ individualized or in different round-1 cells are separated trivially). The consequence ($n^{O(1/c)}\tau(L,n)$) needs $S$ to be found by exhaustive search over $2m$-sets, which is what the statement allows.
Three remarks, none fatal. (i) $p$ counts degenerate $(a,b)$ as non-tests, so $p\ge(5n-6)/n^2$ and $B_c$ is the complete graph for $c\ge1$; the theorem is only informative for $c<1$. (ii) $p$ ignores sign-separation: $(a,b)$ with $C_a(v)\ne C_a(w)$ separates $v,w$ in round 1, yet counts as a non-test if $T$ coincides. The right quantity is $P$ (§4.2) or $p_2$ of w34. $B_c$ with $p$ is a superset; Thm 3.2 only gets weaker. (iii) Lemma X and its refutation are unaffected, since Thm 4.2 bounds $P$, and $p\ge P$.

**§3.3.** $I\ge\mathrm{base}\ge\log_n|\mathrm{Aut}|$; motion $\ge(n+3)/2$ (fixed points lie in the agree-set of size $(n-3)/2$); non-prime Paley pair stabilizers nontrivial via $x\mapsto g^{1-p}x^p$. All correct. The sentence "So base size $\le\log_2|\mathrm{Aut}|+O(1)$" does not need the motion bound; every permutation group has a base of size at most $\log_2|G|$.

## 2. Bad-pair reduction: use in the memo

Thm 3.2 is used for what it says: Lemma X would imply small depth (§4.1), Thm 5.1 reduces to $p\le q^{-\delta}$, and w34 Thm 4.1 cites the separation criterion. No quantifier error. Recommend restating $p$ as the true non-separation probability and adding "(for $c<1$)".

## 3. Lemma 4.1 and Theorem 4.2

### 3.1 Lemma 4.1
Recomputed by hand: of the 27 terms from $W_a=f_ag_a+\delta_a-\varepsilon_a$, those with two $\delta$ or two $\varepsilon$ vanish (14 terms); one main term $T_1T_2$; $3$ terms $-(st+su+tu)$ from $\delta$ on one index; $3$ terms $+(s't'+s'u'+t'u')$ from $\varepsilon$; $6$ cross terms $-(st'+ts'+su'+us'+tu'+ut')$. Exactly the stated $R$. It uses $\langle V_{i,a},V_{i,b}\rangle=-1$, so $V_1,V_2$ must be conference-type with $V\mathbf 1=0$. Exhaustive check on all generic triples, including factors of different isomorphism type: $P(5)$ ($3600$ triples), $P(9)$ ($254016$), $P(13)$ ($2.9\cdot10^6$), plus $200000$ random triples with two inequivalent order-25 Spence factors. **0 mismatches** (`results/check_turyn.out`). Sign convention: $W(V,V)=W(-V,-V)$, and $T\to-T$ globally under $C\leftrightarrow-C$; both as the memo says.

The Turyn iterates are conference matrices at every level: $W^2=(v^2I-J)$ and $W\mathbf 1=0$ by direct expansion (using $V\mathbf 1=0$ and equal orders); same-sign $V\otimes V$ makes $W$ symmetric. Symmetric and skew base matrices of the same order cannot be mixed in any case, because symmetric needs $v\equiv1\bmod4$ and skew needs $v\equiv3\bmod4$.

### 3.2 Theorem 4.2 and the constant
Recomputed by hand: collision in $W_L$ on the second coordinate plus any $a_1,b_1,x_1$ distinct gives a collision in $W_{L+1}$; the signs $V_1(a_1,x_1)V_2(a_2,x_2)$ agree since $x_1=y_1$ and the second factors agree; $R_x=R_y$; the count of $(a_1,b_1)$ gives $(1-1/v_L)(1-2/v_L)$. The product runs over $v_i=v^{2^i}$, $i\ge0$. Correct. **$0.049$ is right**: exact $P_{P(9)}$ maximum is $6/81$ (at pair $(0,1)$), the product is $0.665658$, $c=0.049308$. The inequality was checked exactly on all $324$ lifted pairs $(x_1,x_2),(x_1,y_2)$ and their $324$ mirrors at level $0\to1$ (minimum $P_W/P_V=1.905$, against the bound $0.691$): the bound is loose by about $\times2.75$.

Exact values, by direct computation of $T$ through the matrix identity $W=V\otimes V+I\otimes J-J\otimes I$ (one matvec per $a$, never using Lemma 4.1; validated by brute force at $n=81$):

| Graph | $n$ | exact max $p$ (§3.1 def.) | exact max of the code's statistic $\Pr[T\text{ equal}\mid a\neq b,\ a,b\notin\{x,y\}]$ | exact max $P$ (collision) | memo |
|---|---|---|---|---|---|
| $W_1(P9)$ | 81 | $1869/6561=0.2849$ | $0.2386$ | $926/6561=0.1411$ | "0.28" |
| $W_2(P5)$ | 625 | $62365/390625=0.1597$ | $0.1529$ | $40622/390625=0.1040$ | "0.24" |
| $W_2(P9)=W_3(\text{skew }3)$ | 6561 | $8036153/43046721=0.18668$ | $0.1861$ | $6379162/43046721=0.14819$ | "**0.28**" |

**Break.** The memo's S5 and §4.2 say $p$ reaches $0.28$ at $n=6561$, and §6 says $33057$ pairs have $p\ge0.2$. The exact maximum is $0.1867$; **no pair reaches $0.2$**. The memo's figure comes from `triples` with $S=300$ samples per pair: the maximum of $2.15\cdot10^7$ noisy estimates (standard deviation $\approx0.022$) is biased upward. Same mechanism at $n=625$ (memo $0.24$, exact $0.160$). The count $33057$ is what that noise predicts: $32\cdot6561/2=104976$ pairs have true $p=0.187$, and at $S=300$ about $27\%$ of them have an estimate $\ge0.2$ by chance, i.e. about $28000$ pairs. At $n=81$ the agreement with $0.28$ is a coincidence between the sampling artefact and the §3.1 convention. (How the maximum was bounded at $n=6561$: exact $p$ for the $200$ pairs $(0,y)$ with largest $S=12000$ estimates, hitting $32$ pairs at $0.18668$; the other $6360$ pairs have estimates $\le0.058$ with standard deviation $\approx0.002$. Vertex-transitivity from $\mathrm{Aut}(W)\supseteq\mathrm{Aut}(V)\times\mathrm{Aut}(V)$ reduces all pairs to pairs through $0$, and the two $n=6561$ chains are the same graph: $W_1(\text{skew }3)\cong P(9)$ and $W_2(\text{skew }3)\cong W(P9,P9)$ by nauty canonical form.)

This is a data error, not a proof error: Thm 4.2's content, $P\ge0.049$, stands, and $P$ at $n=6561$ is in fact $0.148$.

**Definitions.** Three different quantities travel under similar names: $p$ (T-only, includes degenerate $(a,b)$; §3.1), the code's statistic ($p$ conditioned on non-degeneracy), and $P$ (collision, with signs; §4.2). The S5 row says "collision probability $\ge0.049$" and then "$p$ reaches $0.28$"; the second figure is not a collision probability (and $P<1/4$ always, by the agree-set bound of w34 Prop 1.1, whereas $p$ can exceed $1/4$). State which is which.

"For all $n$" in S5 means: for all $L$ in the sparse family $n=9^{2^L}$. Also state that $P$ does not converge downward toward the bound: the bound is $0.049$ and the truth is $\ge0.135$ for all $L$ (exact $P_{W_1}=0.1411$ times $\prod_{i\ge1}$).

### 3.3 The inference to "structure side must include tensor products"

Thm 4.2 produces pairs differing in one coordinate of one level, i.e. pairs inside a single "line" of the product. Such pairs form cliques of $B_c$ of size at most the base size $v$ (bounded), so as written Thm 4.2 does not touch Attempt 2 (a clique of size $L(n)\to\infty$). The claim in §4.3 needs large cliques.

**Prop R1 (mine).** Let $V$ be symmetric conference-type of order $v$, $\pi=P_V(x_0,y_0)>0$, $C_0=\prod_{i\ge0}(1-v_i^{-1})(1-2v_i^{-1})$, $v_i=v^{2^i}$. On $W_L$ (coordinates in $[v]^m$, $m=2^L$), for any $x,y$ differing exactly on $J\subseteq[m]$ with $\{x_j,y_j\}=\{x_0,y_0\}$ for each $j\in J$,
$$P_{W_L}(x,y)\ge(\pi C_0)^{|J|}.$$
*Proof.* Induction on $L$ along the binary tree of the product. If both halves differ, Lemma 4.1 makes a collision of each half a collision of the product (the $T_1T_2$ terms agree, signs and hence $R$ agree, all triples distinct), so $P\ge P_1P_2$. If only one half differs, Thm 4.2's step multiplies by $(1-1/v_i)(1-2/v_i)$. Unary nodes at level $i$ are at most $|J|$ in number. $\square$

**Consequence.** For the subcube $Q=\{x_0,y_0\}^r\times\{\text{fixed}\}^{m-r}$: if $r\le cm\ln v/\ln(1/(\pi C_0))$, then every pair in $Q$ has $P\ge n^{-c}$, so $Q$ is a clique of $B_c$ of size $2^r=n^{c\ln2/\ln(1/(\pi C_0))}$. For $P(9)$: $n^{0.23\,c}$. Polynomially large cliques, for every $c>0$. Exact sanity check at $n=6561$: $Q=\{0,1\}^4$ (16 vertices, base-9 digits); all $120$ pairs computed exactly, $\min P=0.0197$ at weight $4$, so $Q$ is a clique of $B_c$ for $c\ge0.447$ (this is the regime $c<1/2$ the memo calls the difficult one). (`results/subcube.out`.)

With R1 the sentence is justified in the sense "any large-clique-implies-structure theorem must count Turyn iterates as structured". Whether "tensor" is the right structural class remains a choice: note $W(\text{skew }7,\text{skew }7)\cong P^*(49)$ (exact, nauty), a Turyn product that is also a Peisert graph, so the same graph can carry a non-product description. Suggest adding R1, or weakening §4.3 to "Turyn iterates have large $B_c$-cliques".

**"Not an individualization lower bound" (§4.2).** Correct as stated: all $n\le6561$ tested have depth 3.

### 3.4 Automorphism lower bound: a theorem, not [DATA]
$\mathrm{Aut}(W(V,V'))\supseteq\mathrm{Aut}(V)\times\mathrm{Aut}(V')$ is immediate from the entrywise formula. If $V$ has an anti-automorphism $\pi$ ($\pi V\pi^T=-V$; Paley: multiply by a nonsquare; skew Paley: $x\mapsto-x$), then $(\pi,\pi)\in\mathrm{Aut}(W(V,V))\setminus(\mathrm{Aut}V)^2$, and $(\pi,1)\circ\mathrm{swap}$ is an anti-automorphism of $W(V,V)$, so the property propagates. Hence $|\mathrm{Aut}\,W_{L+1}|\ge2|\mathrm{Aut}\,W_L|^2$ for every $L\ge0$. With $|\mathrm{Aut}\,W_1(P9)|=10368>81^2$ this gives **$I(W_L)\ge3$ for every $L\ge1$ of the $P(9)$ chain**, as a theorem. The memo records this at each tested level as [DATA]. The formula matches nauty at $n=81,625$ ($|\mathrm{Aut}\,W_2(P5)|=720000$, computed) and the memo's $214990848$ at $n=6561$ ($=2\cdot10368^2$).

## 4. Experiments

### 4.1 What was certified, independently

Exact refinement, no hashing, every pair enumerated (or, for vertex-transitive families, every pair through vertex $0$, justified by explicit translations/orbits).

| Family | Result | Certification |
|---|---|---|
| Spence $n=25$ (15), $29$ (41) | MIN 2, except one graph at $n=25$ ($P(25)$): 3 | exhaustive pairs/triples |
| Spence $n=37$ list, **all 6760** | MIN 2, all | exhaustive pairs |
| **All two-graph descendants**: $n=25$ (104 labellings), $29$ (180), $37$ (7258), $41$ (672), $45$ (2300), $49$ (1500) | MIN 2 or 3; depth 3 only $P(25)$ (all 26 labellings), $P(49)$ (all 50), and **one further graph at $n=49$** | exhaustive |
| Paley, all 103 prime powers $q\equiv1\bmod4$, $q\le1097$ | 2 for prime, 3 for non-prime | exact $k=2$ on the two pair orbits, $k=1$ impossible by §3.3, $k=2$ impossible for non-prime by §3.3, witness triple for non-prime |
| Peisert 9, 49, 81, 121, 361; a sample of random line unions, $q\le13$ | as in memo's table | exhaustive pairs through 0, witness triples |
| Turyn: skew-3 chain to 6561, $P(5)$ chain to 625, $P(9)$ to 6561, $P(13)$, skew 7, skew 11 | depth 3, except $P(13)$ and skew 11 at depth 2; $W(P25,P25)$ depth 3 | $n\le625$: exhaustive $k=2$ through 0; $n=6561$: $k=2$ excluded by $|\mathrm{Aut}|>n^2$ (§3.4), witness triple by exact refinement ($4$ of $60$ random triples discrete) |
| New products at $n=6561$: $W(P81,P81)$, $W(P^*81,P^*81)$, $W(P81,P^*81)$, $W(\text{lines}9,\text{lines}9)$, $W(W(P9,P9),P^*81)$ | all have depth $\le3$ (exact witnesses) | sampled triples |

So the memo's exact-minimum claim is correct: the largest cases are certified as $k\le3$ by an exact witness and $k\ne2$ by the automorphism count, which is a valid lower bound. Hash-based WL is only an upper bound on depth, as the memo says, but I confirm no case where hashing mattered.

### 4.2 What the memo overstates

* **Coverage.** S7 says "over all available conference graphs (Spence's lists; …)". Spence's list has descendant counts $106$ ($n=41$), $1022$ ($n=45$), $412$ ($n=49$) on his own table; the memo tests $16$, $50$, $30$ one-per-two-graph representatives, and $400$ of $6760$ at $n=37$. The table's "(30)" at $n=49$ reads as complete; it is $30$ of $412$ iso classes. At $n=49$ the memo tested one representative per two-graph, not all graphs. Fix: state coverage in S7, or adopt the complete run above.
* **"Only $P(25)$, $P(49)$: 3."** False for Spence's list: the descendant at two-graph #6 (point 3) of `conf2graph.50` is $P^*(49)$ (nauty canonical form; $|\mathrm{Aut}|=3528$, isomorphic to $W(\text{skew }7,\text{skew }7)$), with MIN $3$ (all $1176$ pairs have nontrivial stabilizer; its $\lvert\mathrm{Aut}\rvert=3528$). The sentence is true only for the memo's sample of $30$. The memo's own Peisert row lists $P^*(49)$ with depth $3$, so the two rows disagree with each other.
* Everything else in §6 that I re-ran matches: all $n=25,29$ depths, Peisert and line-union rows, Paley rows, Turyn rows. The S7 claim "depth 3 only where every 2-point stabilizer is nontrivial" holds on the depth-3 graphs where I computed stabilizers ($P(49)$, $P^*(49)$, $P(121)$, $P(125)$, $P(169)$, $W(P9,P9)$, the $W_2(P5)$ sample) and, by the Frobenius argument, on all non-prime Paley; "1-WL partition equals orbit partition" holds on all pairs at $n=49$ for the depth-3 graphs, and on pairs through $0$ for $P(121),P(125),P(169)$, $P^*(121)$, $P^*(361)$ (sample of $52$), $W(P9,P9)$, $W(P13,P13)$, $W(\text{skew }11,\text{skew }11)$, $W_2(P5)$ (sample of $90$): **0 mismatches**.

### 4.3 What computation cannot reach

The uniform cyclotomic row was not re-run (Peisert and line unions were, on a sample). Mathon $pq^2$ graphs were not constructed. $k=2$ exhaustion at $n=6561$ is replaced by the automorphism count; $k=3$ exhaustion is not done (only witnesses) at $n=625,6561$ and the new products. Nothing beyond $n=6561$ was run; Spence's list is only what Spence lists (at $n\ge37$, known to be non-exhaustive). The memo's own caveat ("cannot separate $O(1)$ from slow growth", all large examples algebraic or products) is right and should stay.

## 5. Prior art

* **Levet.** Q6.5 quoted accurately (the $O(1)$ question and "even $o(\log n)$ would be a major advance"). Levet states $n^{O(\log n)}$ and "no further improvements", not the constant $2$; the $2\log_2n$ is the memo's (correct) union-bound derivation, and the "almost all such subsets" quote refers to Levet's unspecified $O(\log n)$. Cosmetic.
* **Brouwer–van Eijl 1992 §4 ("the half case")**, read directly (open-access EMIS mirror). Items (i)–(iii) of that section give **all** of Prop 2.5: for $p=2$, (iii) gives the $n\equiv1\bmod8$ case; (ii) with $c=0$ gives $\mathrm{rank}_2(A)=n-1$ and (i) with $c=1$ gives $\mathrm{rank}_2(A+I)=n$ when $\mu$ is odd, i.e. $n\equiv5\bmod8$. The memo's "first case is Brouwer–van Eijl" should read "both cases".
* **Fijavž–Mohar, "Rigidity and separation indices of Paley graphs", Discrete Math. 289 (2004)**, read directly. Prop 2: rig$(P_p)=2$ for prime $p$ (citing Muzychuk); Thm 3: $\lfloor\log_2p\rfloor\le\mathrm{sep}(P_p)\le\lfloor2\log_2p\rfloor$. The memo's "prime $q$: 2" is known, and the one-round separation bounds are exactly this; worth citing alongside Babai.
* **Metric dimension / resolving sets** of SRGs (Bailey and Cameron; arXiv:1312.4973, seen in search results only, not read) are the natural literature for distinguishing sets; I found nothing there conflicting with the memo.
* **Babai 1980, Spielman, BCSTW, Babai–Wilmes, Chen–Sun–Teng.** Checked against Levet's survey paragraphs and Ponomarenko's statements; I did not obtain Babai's 1980 paper, nor BCSTW FOCS 2013 (the memo couldn't either). No new conflicting claim found. Ponomarenko 2006.13592 Thm 1.3 (exceptions $3^4,3^6,3^8,3^{10},5^4,5^6$) and 2511.18304 Thm 1.2 (WL-dim $\le5$), Cai et al. 2312.00460 Thm 1.1, Mathon Thm 1.3/eq. (1.10), Wang 1908.07055: quoted correctly.
* **Anti-concentration.** I did not find a statement that $T(a,b,\cdot)$ anti-concentrates uniformly for Paley graphs (Thm 5.1 remains a sketch); Sato–Tate in families is standard and the memo cites it as such. "Not found" means only that.

## 6. Consistency with later documents

w34 uses the collision version ($p_2<1/4$ by Prop 1.1), correctly different from w32's $p$; its $r=1$ statistic ($0.147$–$0.149$) matches my exact $P=0.1482$ at $n=6561$, while w32's "0.28" matches nothing exact. w34's reliance on w32 (Lemma 2.3, Lemma 4.1, Thm 4.2, Thm 5.1 as sketch) is within what those results say. redteam-w35-w34 re-checked Lemma 4.1 numerically and used w34's statements; nothing there depends on the broken numbers. Recommend w34's §8 and any later text cite $0.187$, not $0.28$.

## 7. Fixes, in order of priority

1. **S5, §4.2, §6:** replace $0.28$/$0.24$/"33057 pairs" by the exact table in §3.2, state that the maxima were estimated from $S=300$ samples.
2. **S7, §6 table:** state coverage ($30$ of $412$ at $n=49$, etc.) or use the complete run; delete "only $P(25),P(49)$" or add $P^*(49)$.
3. **§4.3:** add Prop R1, or weaken to the statement Thm 4.2 actually supports.
4. **Prop 2.5:** cite Brouwer–van Eijl §4 for both cases.
5. **§2.3/§4.4:** replace $n^{0.72}$ by $n^{0.98}$ (Spence $n=49$ triple with $T=n-3$, then Lemma 4.1); the §4.4 "not seen" is obsolete.
6. **§3.1:** add "$c<1$"; prefer $P$ (or say $B_c$ is deliberately coarse). **S5:** "for all $n$" → "for all $L$"; disambiguate $p$, $P$.
7. **§3.3:** remove the motion argument from the base-size bound.
8. **§4.2:** promote the $|\mathrm{Aut}|$ recursion to a statement with proof; add $I(W_L)\ge3$ for all $L$ on the $P(9)$ chain.
9. **§5 (Thm 5.1) & §4.1:** do not write "true for Paley".

## 8. What I would sign

Lemmas 2.1–2.4, Prop 2.5 (citing BvE), Thm 3.2, Lemma 4.1, Thm 4.2 with $c=0.0493$, Lemma X is false, Spence (complete, as above) and algebraic depth data. Not signed: Thm 5.1 (sketch), the numbers named in §3.2, and §4.3's claim without R1.

## 9. Not done

Thm 5.1 not verified beyond its plausibility; Babai 1980 not read; Mathon family and uniform cyclotomic row not re-run; $k=3$ exhaustion at $n\ge625$; novelty of the identities is limited to web-tool search. Sources: Brouwer–van Eijl, J. Algebraic Combin. 1 (1992) §4 (EMIS mirror); Fijavž–Mohar, Discrete Math. 289 (2004); Bailey, arXiv:1312.4973.
