# w28-sigma: can HJ avoid paying for the σx channel?

Moonshot memo, branch `w28-sigma`, 2026-11-08. HJ = Hajiaghayi–JafariRaviz, arXiv:2611.01399 (LaTeX `L…` line numbers). B1, Lemma 1, Lemma 2 = `docs/w18-latin.md`, read with the corrections of `docs/redteam-w18-latin.md`. Everything about "HJ" assumes HJ correct (unrefereed). The Lean was not consulted; no claim here is machine-checked.

Labels: **[PROVEN]** (full argument here, given cited results and HJ as written), **[SKETCH]** (argument with named gaps), **[CONDITIONAL: …]**, **[SPECULATION]**. Experiments: `docs/w28-sigma-check.py` (§13).

## 0. Summary

**Answer.** The channel *can* be removed on the B1 family, by a small change to HJ (lazy Step 4, §5), with correctness and Lemma 7.1 surviving. But the cost does not disappear: on the same family it reappears in the cap/anchor channel $Q$ unless automorphism pruning is added. In the worst case Step 4 survives on a "uniform" residue I cannot eliminate. **The per-phase exponent does not change**: $O(\log N(\log w+\mu+\log\log N))$, because $\sigma x$ was only one of three terms paying $\log N\log w$. No barrier is contradicted, because nothing beats $n^{\Theta(\log n)}$ here.

| # | Statement | Status |
|---|---|---|
| M1 | Exact memoization by kernel state saves only $n^{O_\kappa(1)}$ on $X_m$: states = flags, and the tree/flag ratio is $\le 2^{\kappa^2}$ per level | **[PROVEN]** §3 |
| M2 | Any memo key determining $D_j$ still has $2^{m^2/4-O_\kappa(m)}$ values: at best $n^{(1/8)\log n}\to n^{(1/16)\log n}$ | **[PROVEN]** §3 |
| P1 | Pruning tests and aggregation branches by *certified* automorphisms preserves every aggregation input | **[PROVEN]** §4 |
| P2 | That pruning collapses $X_m$ to $n^{O_\kappa(1)}$ | **[SKETCH]** §4 |
| P3 | Pruning by equality of prefix comparisons is unsound | **[PROVEN]** §4 |
| C1 | Any $\mathrm{Aut}$-invariant test rule on $X_m$ is all-or-none on independent $T$ at each level | **[PROVEN]** §5 |
| L1 | Lazy HJ (LHJ) is correct; its children are a subset of HJ's types with the same charges, so Lemma 7.1 holds | **[PROVEN, given HJ]** §5 |
| L2 | On $X_m$, at the root and every chain state, LHJ has no twin class of size $\ge2$, so never escalates; the B1 chain is gone | **[PROVEN]** §5 (whole-tree: [SKETCH]) |
| Q1 | Unpruned LHJ on $X_m$ still pays $2^{\Omega(m^2)}$, through anchors ($Q$ channel) | **[SKETCH]** §6 |
| U | Uniform first window on $C\subseteq\Gamma$ forces rows $\ge\binom{|C|}{\lfloor\kappa/2\rfloor}$, or the window is $\mathrm{Sym}(C)$-symmetric (Ray-Chaudhuri–Wilson for variable blocks) | **[PROVEN]** §7 (product states only) |
| R1 | Corrected rigid variant $X_{m,R}$ ($|R|=O(m)$ deleted lines): HJ makes $n^{(1/8)\log_2n-O(\log\log n)}$ calls | **[PROVEN, given HJ]** level steps; root entry and "P1 pruning removes nothing" [SKETCH] §8 |
| R2 | The rigid variant is **not** a barrier: 1-WL makes the deletion variant discrete in $\le5$ rounds in every rigid instance tested ($m\le9$); Pasch-switched variants with enough switches fall to one bounded-WL invariant. The w18 §2.9 "single switched block kills Aut" is false | correction **[PROVEN]**; WL is experiment only §8 |
| L | Prefix-determined Step-4 rules on $X_m$: recursive branch pays B1, lazy branch pays Q1. On $X_{m,R}$ only the recursive branch is bounded | recursive **[PROVEN]**, lazy **[SKETCH]** §9 |

**Sharpest open statement.** Uniform Prefix Conjecture (§7.3): a state whose tests are uniformly Pending on a large $C$ has domain $\ge|C|^{\Omega(\kappa)}$, cumulatively along chains. It would make Step 4 polynomial in total. It is not proved. Even if true, it would not change the exponent, since $Q$ remains.

---

## 1. The channel, exactly

Step 4 of `LocalCertificate` (L774–811, L2660–2670) applies when no position is affected and $K=(A_i)_{(U_i)}$ has image $\ne\mathrm{Alt}(T)$. It takes the union of $A_i$-orbits $\Delta\subseteq U_i$ with $\phi_T((A_i)_{(\Delta)})=1$, and recurses on the kernel $N_i$ on $\Delta$: same domain, $\sigma\mapsto\sigma-\kappa$ (L2717–2733). The multiplicity is every $\kappa$-subset (and ordered comparison pairs): $C_\kappa q^{2\kappa}$ on a giant of degree $q$. On the B1 chain the calls satisfy

$$F(s,\sigma)\ \ge\ \tfrac12\tbinom{q}{\kappa}\,F(s,\sigma-\kappa)\qquad(\text{same }s),$$

and in general HJ bounds this term by $N^a F(s,\sigma-\kappa)$, with depth $\sigma/\kappa\le C\log s/\kappa$ (Thm A.9), so the channel costs up to $\sum_j\kappa\log q_j$. The charge $\kappa x$ per step is only a bound; B1 shows that a chain with $\sum_j\kappa\log q_j=m^2/2$ really occurs. **Consequently no better potential can help HJ as written**: the calls exist. A fix must change the algorithm.

What exists at a level. $G_j=\mathrm{Sym}(\widetilde W_j)\times H_j$, label set $Q_j$, $q_j=2^{r_j}-1$, $r_j=m-j\kappa$. An independent $T$ produces a child at the level-$(j+1)$ state determined by $(D_{j+1},Z_{j+1},U_{j+1})$ (Lemma 1).

## 2. What any modification must preserve

Read from L2660–2800, Helfgott §6.2 (`BDHv8.tex` L1913–1960), L1643–1714:

* **(I1)** $F\le\mathrm{Aut}_G(x)$, assigned equivariantly. (Cases 1, 2a, 2b.)
* **(I2)** Tuple colors are an equivalence relation on (string, ordered tuple), computed by exact cosets, equivariant. (Prefix recovery, L2665–2700.)
* **(I3)** No twin class of the tuple coloring on $\Gamma\setminus S$ above the Design Lemma's threshold ($\alpha=3/4$, L2841–2853).
* **(I4)** Every recursive answer is a complete coset.
* **(I5)** Lemma 7.1: every child class has multiplicity $\mathcal M$ and potential drop $\Delta\Phi$ with $\mathcal M e^{-\Delta\Phi}\le 1/(8J)$.

HJ gets (I3) from "$T\subseteq\Gamma\setminus S$ is not Full, so its orderings are not all one color" (Helfgott L1949). That is the only place where a *resolved* status for every $T$ is used, and it is what §5 exploits.

## 3. Attempt: sharing work by memoizing the kernel state

**Theorem M1. [PROVEN]** On $X_m$, the group $G_j$ of a level-$j$ state determines the flag $D_1<\dots<D_j$. Hence the number of distinct exact kernel states at level $j$ is at least $\prod_{i<j}\binom{r_i}{\kappa}_2$, and exact-state memoization saves a factor of at most $\prod_{i<j}\big(\tfrac12\binom{q_i}{\kappa}\big/\binom{r_i}{\kappa}_2\big)\le2^{\kappa^2J}\le2^{\kappa m}$, i.e. $n^{O_\kappa(1)}$.

*Proof.* $P_j=V\setminus D_j$ gives $D_j$. For $\rho\in H_j$, $\tau_\rho(d)=\rho(v+d)+\rho(v)$ recovers $U_j$. Now $U_j\supseteq\{1+f: f\in\mathrm{Hom}(D_j/D_{j-1},D_{j-1})\}$ and every $\tau\in U_j$ is trivial on $D_j/D_{j-1}$, so $\sum_{\tau\in U_j}\mathrm{im}(\tau-1)=D_{j-1}$; restriction to $D_{j-1}$ is onto $U_{j-1}$; induct. (Parity normalization changes only the $\mathrm{Sym}$ factors, not $U_j$.) For the count, $\binom{q}{\kappa}\le2^{\kappa r}/\kappa!$ and $\binom{r}{\kappa}_2\ge2^{\kappa(r-\kappa)}$. ∎

Numbers (`count`): $\kappa=8$, $m=200$: tree $2^{20233}$, flags $2^{19177}$; ratio $2^{5.3m}$.

**Theorem M2. [PROVEN]** Any key that determines $D_j$ has at least $\binom{m}{j\kappa}_2$ values at level $j$; at $j\kappa\approx m/2$ this is $2^{m^2/4-O_\kappa(m)}=n^{(1/16)\log_2n-O_\kappa(1)}$. So a key coarsened to the subspace can at best halve the constant, from $1/8$ to $1/16$.

**Where it breaks.** The coarsened key is not a sound memo in general: it requires answering at the maximal group over all $U_j$ and restricting, and restricting a coset to a subgroup is a string-isomorphism call. Going below $D_j$ means conjugating by $\mathrm{Aut}$, which is §4. Memoization of *deep* subproblems fares no better: a child's string on $\Delta$ is the same $x$, but its group is keyed by the flag.

## 4. Attempt: merging tests into orbits

**Theorem P1. [PROVEN]** Let $F\le\mathrm{Aut}_G(x)$ be known. If $T'=T^f$, $f\in F$, then the entire certificate of $T'$ (windows, groups, status, comparisons) is the $f$-image of that of $T$. The same holds for a target anchor tuple moved by certified automorphisms of $y$. So skipping all but one representative per $F$-orbit preserves (I1)–(I4) exactly, and only removes children, so (I5) holds.

*Proof.* HJ's certificate is equivariant under $G$-isomorphisms (L749–753); apply it to $f:x\to x$. ∎

This is standard automorphism pruning, as in nauty or Traces and in Luks's framework; I claim nothing new except the check that it transports the aggregation inputs.

**Theorem P2. [SKETCH]** On $X_m$, with pruning at both tests and aggregation branches, the tree has $n^{O_\kappa(1)}$ nodes.

*Argument.* At level $j$ the first independent $T_0$ recurses, returns Full, and $K(T_0)=\mathrm{Aut}_{P_{T_0}}(x)$ (windows exhaust $\Omega_j$). Its image is the even stabilizer of $T_0$ in $\mathrm{GL}(V/D_j)$. The number of its orbits on $\kappa$-sets is the number of relative positions of $(T_0,T)$, at most $2^{O(\kappa^2)}$, independent of $r_j$. So $F_j\le2^{O(\kappa^2)}F_{j+1}$, giving $2^{O(\kappa^2 J)}$. *Gaps.* This also requires pruning HJ's Case 2b branches (target images of $d-1$ anchors and of an orbital, L2775–2795): without that, $q^{O(1)}$ continuation branches remain per cap contraction and the tree is again $2^{\Omega(m^2)}$. So w18's remark "pruning collapses the chain" is correct about the chain only. I did not trace every aggregation branch or the cost of affected children.

**Proposition P3. [PROVEN]** Skipping $T'$ because its prefix comparison with a processed $T$ is nonempty is unsound.

*Proof.* Fix an independent $T$ and the linear maps $g_\sigma$ permuting $T$ evenly and fixing a complement. Let $R$ be the union of $g_\sigma$-orbits of $O(m)$ lines chosen off $\langle T\rangle$ and off $\langle T'\rangle$, for a generic independent $T'$ (orbits have size at most $\kappa!/2$, so $|R|=O_\kappa(m)$), such that $\mathrm{Stab}_{\mathrm{GL}}(R)$ does not induce $\mathrm{Alt}(T')$. Delete $R$. The windows of $T,T'$ avoid the points of $R$, so a linear $g$ with $T\to T'$ carries the windows of Lemma 1 onto each other (§8 patch) and the prefix comparison is nonempty. But $\mathrm{Aut}$ induces $\mathrm{Alt}(T)$ and not $\mathrm{Alt}(T')$ (Lemma R0), so $T$ ends Full and $T'$ ends Nonfull. ∎

**Where it breaks.** Pruning needs real automorphisms; on rigid inputs there are none. P3 shows no local equivalence can replace them.

## 5. Attempt: canonical and adaptive test choice

**Theorem C1. [PROVEN]** At a level-$j$ state, $\mathrm{Aut}_{G_j}(x)$ acts on $Q_j$ through all of $\mathrm{GL}(V/D_j)$, transitive on ordered independent $\kappa$-tuples. So an $\mathrm{Aut}$-invariant rule selects all independent $T$ or none.

*Proof.* Lift $\bar g$ to $g$ with $g|_{D_j}=\mathrm{id}$; then $g\in H_j$ ($\tau=\mathrm{id}$), and $g$ preserves $Z_j$ and $\widetilde W_j$. ∎

A sparse canonical family therefore does not exist on this input. The "none" option is viable, though, because of the following observation: (I3) needs twin-freeness, not a resolved status for every $T$.

### 5.1 Lazy Step 4 (LHJ)

Modify the certificate phase of `GiantStep`:

1. **Phase 0.** For every ordered $\kappa$-tuple run Algorithm 3 and its lockstep comparisons, but stop at the first point where Step 4 would run. Status: Nonfull, Full, or **Pending** (with prefix window and group). Colors: comparison classes on the prefix; differing stop points give different colors.
2. Let $F_0=\langle K(T):T\text{ Full}\rangle$, $S_0=\mathrm{supp}\,\pi(F_0)$. If $|S_0|\ge q/2$, run Cases 1, 2a, 2b with $F_0$.
3. Else color $(\Gamma\setminus S_0)^\kappa$ by Phase-0 classes. If every twin class has size $\le\frac34|\Gamma\setminus S_0|$, run Case 3 (Design Lemma) with this coloring. **No Step-4 child is ever made.**
4. Else (**escalation**) let $C$ be the twin class above $\frac34$. Every $\kappa$-subset of $C$ is Pending (a Nonfull $T\subseteq C$ would have all orderings one color, a contradiction by the HJ argument, L2720–2726). Run Step 4 and finish the certificates only for $T\subseteq C$ ($C$ is canonical, being a class above $\frac12$). Recompute $F$, $S$ and the coloring, with colors recording the stage reached, and repeat from step 2. Each pass resolves more tuples; in the worst case all are resolved and this is HJ.

**Theorem L1. [PROVEN, given HJ]** LHJ returns the exact coset, and its running time obeys HJ's bound.

*Proof.* (I1): $F_0$ is generated equivariantly and lies in $\mathrm{Aut}_G(x)$. (I2): the prefix-recovery argument applies verbatim to each prefix; Phase-0 decisions are functions of equivariant data. (I3): checked explicitly in step 3; in step 4 a surviving large twin class has all $T$ resolved, hence Full and absorbed into $S$, or the HJ contradiction. Cases 1, 2a, 2b use only (I1) and the case hypotheses. Differing case outcomes for $x$ and $y$ certify non-isomorphism, as in HJ, because every decision is a function of canonical data. (I5): every child is an HJ-type child with the same drop, multiplicities are not larger, aggregation branches are charged as before. ∎

Note the converse direction of the design: the Phase-0 coloring is coarser than HJ's, but it is canonical, and if it is twin-free it is all the Design Lemma needs.

**Theorem L2. [PROVEN]** At the root of $X_m$ and at every level-$j$ state, Phase 0 has only singleton twin classes. So LHJ does not escalate there, and the B1 chain is not created.

*Proof.* If $T\subseteq Q_j$ contains a line of $\mathrm{PG}(r_j-1,2)$, the first window contains blocks meeting exactly those three cosets, so the image of $A_1$ preserves the set of collinear triples of $T$, a proper invariant for $|T|\ge5$: Nonfull at iteration 1. For $x\ne y\in Q_j$ take $T\ni x$, $T\not\ni y$, containing a line through $x$ and otherwise generic; $T^{(x\,y)}$ contains no line, so the colors differ. At the root, $T$ may mix points and blocks; a block with its three points gives the same separation for blocks, and a transporter between tuples with different adjacency patterns is empty. ∎

Replay (root model, `phase0`): $m=6$, $\kappa=5$: $T$ with a line is Nonfull at iteration 1 (image 6 of 60); $T=\{1,2,4,7,8\}$ with a 4-term dependency is Nonfull at iteration 2 (12 of 60). $m=5$, $\kappa=4$: $\{1,2,4,8\}$ and the totally dependent $\{1,2,4,7\}$ are both Pending (no affected positions, Step 3 evaluated and fails, $\phi(K)$ trivial), *with different prefix windows* (34034 vs 26746 positions), so they get different colors. ($\kappa=4$ is below the simple-group range, so this checks window behaviour only. At $m=5$, $\kappa=5$ a full basis is Full: the windows exhaust $\Omega$, as there is nothing outside the span.) (A single total-sum dependency is $\mathrm{Alt}(T)$-invariant, so "dependent implies Nonfull" is false as stated; the proof only uses lines.) That is what makes the coloring informative while Step 4 is skipped.

Whole-tree claim that LHJ never creates a Step-4 child on $X_m$: [SKETCH]; I checked the root and chain states, not every state the aggregator reaches.

## 6. It moves the cost: the $Q$ channel on $X_m$

**Theorem Q1. [SKETCH]** Unpruned LHJ on $X_m$ makes $2^{\Omega(m^2)}$ calls.

*Argument.* $\mathrm{GL}$ is transitive on points, so with no individualization every canonical structure on the point set is point-uniform; the Design Lemma must individualize $d\ge1$ labels. Each individualization lowers the projective rank by at most one, since the stabilizer of $d$ points still acts transitively outside their span with the same structure. So reaching low rank needs anchors spanning the space, $\sum_id_i\ge r-O(1)$; a round at rank $r'$ with $d_i$ anchors has at least $(2^{r'}-2^{d_i})^{d_i}$-order *successful* target tuples, because $\mathrm{GL}$-images of the anchor tuple all succeed. Unless automorphisms are used, every one is explored, and the product over rounds is $2^{\Omega(r^2)}$. *Gaps.* I did not trace every Design/Split-or-Johnson outcome on $X_m$; the rank-loss bound is the heart and is rigorous for the anchored stabilizer, but a path could in principle end by another dispatcher step (balanced partition plus kernel recursion, or enumeration at low rank) before the anchors span, and excluding that needs the case analysis.

This is exactly Miller's generator enumeration inside HJ's cap budget. So on $X_m$, LHJ converts the cost from $\sigma x$ to $Q$. That is the warning sign the assignment asked about, and it fires: **the cost moved rather than vanished**. Only automorphism pruning (§4) removes it on $X_m$.

## 7. Attempt: charging $\sigma$ differently

**The potential cannot do it.** B1 is a lower bound on calls: $\sum_j\kappa\log q_j=m^2/2$ against a budget of $\sum_j\kappa x\approx3m^2$ on the chain (both in bits). Replacing $\kappa x$ by the sharper $\kappa\log q_j$ is tight on it. So depth × branching on that chain is $\Theta(\log^2)$ and no analysis of HJ as written can be below it. For LHJ the question becomes what happens at escalation.

### 7.1 The design bound

*Product state:* $G\le\mathrm{Sym}(B)\times G_\Gamma$ acting on $\Omega\supseteq B\times\Gamma$, with $G_\Gamma\to\mathrm{Alt}(\Gamma)$ onto; string $x$ on $B\times\Gamma$, two colors. (With more colors the proof below gives (a) if some color class has $k_*\ge\lfloor\kappa/2\rfloor$, and otherwise the trace statement of (b) per color; the joint lift in (b) is proved only for two colors.) The first window of $T$ is $B\times T$.

**Lemma R (Ray-Chaudhuri–Wilson, variable blocks). [PROVEN]** Let $R_1,\dots,R_N\subseteq[v]$ with $\#\{i:J\subseteq R_i\}$ depending only on $|J|$ for $|J|\le2s$. Let $k_*=\max_i\min(|R_i|,v-|R_i|)$. Then $N\ge\binom{v}{\min(s,k_*)}$.

*Proof.* Put $s'=\min(s,k_*)$, $W$ the inclusion matrix of $s'$-subsets against $R_i$. $M=WW^{\mathsf T}$ has entries depending only on $|J\cap J'|$, so it lies in the Bose–Mesner algebra of $J(v,s')$ and acts by a scalar $\theta_r$ on each $V_r$. Pick $R$ attaining $k_*$; then $s'\le|R|\le v-s'$. For $r\le s'$ pick disjoint $a_1,\dots,a_r\in R$, $b_1,\dots,b_r\notin R$ and $h(J)=\prod_i(1_{a_i\in J}-1_{b_i\in J})\in V_r$. Then $\langle h,w_R\rangle=\binom{|R|-r}{s'-r}>0$, so $\theta_r>0$. Hence $\mathrm{rank}\,W\ge\sum_{r\le s'}\dim V_r=\binom{v}{s'}$. ∎

The constant-block case is the 1975 theorem; I did not find this variable-block form stated but it is routine.

**Theorem U. [PROVEN, product states]** Suppose all ordered $\kappa$-tuples from $C\subseteq\Gamma$, $|C|=v$, have the same color at the first window. Then either
(a) $|B|\ge\binom{v}{\lfloor\kappa/2\rfloor}$, or
(b) $x|_{B\times C}$ is $\mathrm{Sym}(C)$-symmetric: each $k$-subset of $C$ occurs equally often as a trace, for each $k$, so every $\sigma\in\mathrm{Sym}(C)$ lifts to $B\times C$.

*Proof.* A transporter $g=(\rho_B,\rho_\Gamma)$ preserves row counts, so for ordered $t$ and word $w$, $n_t(w)=\#\{b:x(b,t_i)=w_i\}$ depends only on $w$; reordering $t$ makes it depend only on the weight. So $\lambda_j$ is constant on $j$-subsets, $j\le\kappa$; apply Lemma R with $s=\lfloor\kappa/2\rfloor$. If $k_*<s$ then blocks are small or co-small, with weights on $T$ in disjoint ranges since $\kappa\ge2s>2k_*$; so small blocks and complements of co-small blocks are separately uniform, and Möbius inversion over supersets of size $\le k_*$ gives equal trace counts. ∎

**Corollary (GI root). [PROVEN]** At $G=\mathrm{Sym}(n)$ on pairs, if the first window is uniform on $C$ with $|C|\ge3n/8$ and $n$ is large, then $C$ is a clique or coclique and every vertex outside $C$ has $\le1$ or $\ge|C|-1$ neighbors in $C$, equally for all vertices of $C$. (All tuples have one color, so the induced graph on $C$ is uniform; rows inside $C$ then contribute only constant patterns, which subtract out. Rows outside $C$ number $\le5n/8<\binom{3n/8}{2}$, so Lemma R gives $k_*\le1$. The bound $3n/8$ is $\frac34\cdot\frac n2$, from $|S_0|<q/2$.)

So at the root, escalation forces the first window to be trivial. Non-product states (level-$j$, with translation kernels) need the array entries replaced by kernel-orbit patterns; that version is [SKETCH].

### 7.2 What this buys

If an escalation at a product state falls in case (a), then $q\le O_\kappa(s^{2/\kappa})$, so the multiplicity $C_\kappa q^{2\kappa}$ is $O_\kappa(s^4)$, and a $\sigma$-step charged $\kappa x$ needs only $O(x)$. The coefficient of $\sigma x$ improves by a factor $\Theta(\kappa)$ on such steps. **[PROVEN conditional on case (a)]** The depth remains $C\log s/\kappa$, so the contribution is still $\Theta(\log^2 s)$ for fixed $\kappa$. Letting $\kappa\to\infty$ does not help: Design-Lemma anchors cost $q^{O(\kappa)}$ against a $Q$ drop of $\log q$, so the $Q$ coefficient grows by $\kappa$.

Case (b) is not excluded and is where the residual Step 4 lives: e.g. a cap in $\mathrm{PG}$ has trace-complete rows with $k_*=2$. On $X_m$ this is harmless because a cap has size $\le q/2<\frac34q$.

### 7.3 The sharpest open statement

**Uniform Prefix Conjecture. [SPECULATION]** If every $\kappa$-subset of $C\subseteq\Gamma$ is uniformly Pending through its *full* prefix, then $s\ge|C|^{\Omega(\kappa)}$, and cumulatively, along a chain of $J$ such steps, $\log s\ge\Omega(J\kappa\log|C|)$. That would give $\prod_jq_j^\kappa\le s^{O(1)}$: Step 4 polynomial in total under LHJ.

Evidence: in the linear model it is the Hamming bound. If every $J\kappa$-subset of $C\subset\mathbb F_2^d$ is independent, then $2^d\ge\binom{|C|}{\lfloor J\kappa/2\rfloor}$, so the chain's tree is at most $n^{1+o(1)}$ for $|C|\ge\log^2n$ **[PROVEN arithmetic]**, and BCH codes attain this shape. What is missing: for general strings, level-wise uniformity does not obviously give cumulative strength, because the child keeps only rows constant on $T$. Theorem U handles only the first window, and rows with small traces are in case (b). I could not get past this.

## 8. The rigid variant

**Correction to w18 §2.9. [PROVEN]** Deleting or switching one block does not kill $\mathrm{Aut}$: $\mathrm{Stab}_{\mathrm{GL}(m,2)}(\ell)$ has index the number of lines, so order $2^{m^2-O(m)}$. Replay: $m=7$, 3 random lines: $|\mathrm{Aut}|=82944$.

**Construction.** $X_{m,R}$: delete a set $R$ of lines.

**Lemma R0. [PROVEN]** For $|R|\ll2^m$, $\mathrm{Aut}(X_{m,R})=\mathrm{Stab}_{\mathrm{GL}(m,2)}(R)$.

*Proof.* Vertex degrees separate points from blocks. An automorphism $f$ of points preserves real lines, so for $x,y$ pick $z$ with the lines through $(z,x)$, $(z+x,y)$, $(z,x+y)$ real (possible when $|R|$ is small): $f(z+x+y)=f(z)+f(x)+f(y)$ and $=f(z)+f(x+y)$, so $f$ is additive; and it preserves $R$. ∎

A random $R$ of $O(m)$ lines is rigid **[SKETCH: union bound over $\mathrm{GL}$]**; observed trivial at $m=7$, $r=8$ and $r=16$, $40$, and at $m=6$, $r=60$.

**Theorem R1. [PROVEN, given HJ; root entry SKETCH]** Let $P_R$ be the points of $R$. For $J'=\lfloor(m-\log_2|R|-\kappa-c)/\kappa\rfloor$ and $T$ at each level with $(T+D_j)\cup D_{j+1}$ disjoint from $P_R$, Lemma 1 holds on $X_{m,R}$. So HJ makes at least $\prod_{j<J'}\frac14\binom{q_j}{\kappa}=n^{(1/8)\log_2n-O(\log\log n)}$ calls.

*Patch to Lemma 1.* Each witness $(\rho_W,g)$ must lie in $G_j$, so $\rho_W$ cannot send a real block to a deleted line. Take $\rho_W=g$ on blocks touching $T+D_j$ or $D^*$: $g$ preserves those two sets and no deleted line meets them, so the image of such a block is a line meeting them, hence real. On the remaining blocks $\rho_W$ is any bijection of the same trace class; they carry only zeros on the windows. All full-image and unaffected claims go through unchanged. Counting: a fraction at most $2^{\kappa+1}\cdot3|R|/q_j$ of the $T$ are spoiled, $<\frac12$ for $q_j\gg2^\kappa|R|$, and $D_{j+1}\cap P_R=\emptyset$ is maintained. The root is the same patch to Lemma 2; I did not write it out line by line. ∎

*The pruning clause is weaker.* Pruning at a level-$j$ state may use automorphisms of the *state*, which sees fewer blocks than the graph, so global rigidity is not enough by itself. The additivity argument of R0, run on $P_j$ with the $\tau$ of $H_j$ acting on $D_j$, should show that state automorphisms are linear maps preserving $R$, hence trivial on $Q_j$. **[SKETCH]**

**Observation R2: it is not a barrier.** A discrete isomorphism-invariant coloring implies $\mathrm{Aut}=1$, so the discrete rows below are rigid even where nauty was not run. Observed (`rigid`, `pasch`):

| Instance | $\mathrm{Aut}$ | 1-WL |
|---|---|---|
| $m=7$, 3 lines deleted | 82944 | 4 point colors, not discrete |
| $m=7$, 8 / 16 / 40 lines deleted | 1 | discrete in 5 / 5 / 4 rounds; joint refinement with a relabeled copy matches each point to the unique image |
| $m=6$, 60 lines deleted | 1 | discrete in 4 rounds; same joint match |
| $m=9$, 30 lines deleted | 1 (implied) | discrete in 5 rounds; same joint match |
| Pasch-switched STS, $m=6$ ($k=6$), $m=7$ ($k=8$) | 1 (implied) | plain 1-WL uniform; from the bounded invariant "non-Fano triangles through $p$", discrete in 4 rounds |
| Pasch, $m=6$, $k=2$ | not computed | 5 colors, not discrete (expected: still large symmetry) |

So every instance tested that is rigid is trivial for bounded WL (small $m$, random defects, so this is evidence only): *rigidity came with canonical anchors*. For STS variants the existence of anchors is structural: classically (Veblen–Young, cited from memory) an STS in which every triangle closes to a Fano plane is $\mathrm{PG}(d,2)$, so any non-PG STS has a constant-size defect, visible to $O(1)$-WL as a count of a constant-size pattern. Having anchors does not by itself make an instance easy; that step is only observed. The only variants that hide from bounded WL are the symmetric ones, and those fall to P1. This is a real dichotomy on this family, not a general theorem: **any "fail-fast" statement extending this to all of STS or Latin squares would beat the $n^{O(\log n)}$ barrier of §3.2 of `moonshot-theory.md`, which is a reason to doubt it holds.**

## 9. A limitation that does hold

**Theorem L.** Consider modifications of HJ where the decision to run Step 4's child for $T$ depends only on the isomorphism type of $(G,\Omega,\Gamma,\pi,T,x|_{\text{prefix windows of }T})$, no other inspection of $x$ is made, and nothing else in the certificate step changes.

(i) **[PROVEN]** On $X_m$, all independent $T$ at a level have the same prefix type (C1), so the rule fires on all or none. If it fires at all chain levels, B1 applies verbatim: $n^{(1/8)\log_2n-O_\kappa(1)}$.

(ii) **[PROVEN, given HJ; root entry SKETCH]** On $X_{m,R}$, far independent $T$ have the same prefix type (a linear $g$ fixing $D_j$ carries the windows, §8). The same dichotomy holds, and if the rule fires at all levels the count of R1 applies. That this survives certified-automorphism pruning is the [SKETCH] clause of R1.

(iii) **[SKETCH]** If the rule does not fire at level $j^*$ on $X_m$, the chain contributes $\prod_{i<j^*}\frac12\binom{q_i}{\kappa}$ and the state at $j^*$ pays Q1 on rank $r_{j^*}$; the product is $2^{\Omega(m^2)}$ for every $j^*$, unless automorphisms are used.

What I could **not** prove is the lazy branch on $X_{m,R}$: Q1's successful-branch count needs automorphisms, which $X_{m,R}$ lacks. Wrong anchors there seem to die fast. So the class limitation on the rigid variant is one-sided, and the intended theorem ("any algorithm in the class pays on the rigid variant") is **false for classes containing bounded WL** (R2) and **open for the pure lazy branch**.

## 10. New exponent, and barrier check

Per-phase exponent with $\sigma x$ deleted outright: **unchanged**, $O(\log N(\log w+\mu+\log\log N))$. The $\log N\log w$ is also paid by $x^2$ (giant-degree multiplicity) and by $Q$ (cap contraction), `moonshot-theory.md` §2.9.

| Barrier | Contradicted? |
|---|---|
| Group isomorphism below $n^{\Theta(\log n)}$ | No. Nothing here improves the exponent. $X_m$ is the elementary-abelian instance, which was never hard. |
| Latin squares, STS, conference graphs | No. R2 is instance-specific; a general fail-fast theorem would beat these and is not claimed. |
| Affine equivalence $2^{o(k^2)}$ (Prop 3) | No; not addressed. |

Beating $n^{\log n}$ would require improving $Q$ and $x^2$ as well as settling the conjecture, i.e. the Babai core.

## 11. Attempts and where each broke

| Attempt | Exact statement needed | Break |
|---|---|---|
| Exact memo | Few distinct kernel states | $\ge$ number of flags (M1) |
| Coarse memo | Key $D_j$, answer restricted to $U_j$ | Unsound in general; still $2^{m^2/4}$ (M2) |
| Orbit merging | $F\le\mathrm{Aut}$ known | Works on $X_m$ (P1, P2 sketch); empty on rigid (R1); local equivalence unsound (P3) |
| Canonical test family | Thin $\mathrm{Aut}$-invariant family | All-or-none (C1) |
| Lazy Step 4 | Twin-free Phase-0 coloring suffices for (I3) | Correct (L1) and kills the chain (L2), but cost moves to $Q$ (Q1); residual uniform case open |
| Sharper charge | Multiplicity bounded by domain | Case (a) of U only; constant factor; not below $\log^2$ |
| Rigid lower bound | Rigid and locally PG-like | Rigid variants have WL-visible anchors (R2) |

## 12. Leads

1. Prove or refute the Uniform Prefix Conjecture, first at second window on product states, i.e. a level-2 analogue of Theorem U.
2. Case (b) of U: when rows are trace-complete on $C$, can Step 4 be replaced by a single call? This is where the true residual sits.
3. Turn Q1 into a theorem, tracing Design/Split-or-Johnson on $\mathrm{PG}$.
4. A family that defeats LHJ + P1 + bounded WL must be rigid, without bounded-WL anchors, and locally symmetric. By Veblen–Young it is not an STS. Candidates would have to be non-design incidence structures; random class-2 $p$-group Cayley tables look locally free but are the Sun/IMQSZ regime. **[SPECULATION]**

## 13. Reproduction

```sh
PY=/home/bepis/math/gi-practical-wt/r2-hybrid/.venv/bin/python
cd docs; export PYTHONUNBUFFERED=1
nice -n 19 $PY w28-sigma-check.py count
nice -n 19 $PY w28-sigma-check.py twins 6
nice -n 19 $PY w28-sigma-check.py phase0 5 "[1,2,4,8]"   # also "[1,2,3,4]", "[1,2,4,7]", "[1,2,4,8,16]"
nice -n 19 $PY w28-sigma-check.py phase0 6 "[1,2,3,4,8]" # also "[1,2,4,7,8]"
nice -n 19 $PY w28-sigma-check.py rigid 7 8              # also r = 3, 16, 40; rigid 9 30
nice -n 19 $PY w28-sigma-check.py pasch 6 6              # also pasch 6 2; pasch 7 8
```

Size: everything is small ($m\le9$; nesting is not exercised). The experiments check statuses, windows at the root, and refinement. They do not check any asymptotic claim. The independent-$T$ runs at $\kappa=5$, $m=6$ were not repeated here (`docs/redteam-w18-latin.md` covers those windows).

## 14. Novelty search (2026-11-08)

Searches: local-certificate pruning/memoization; Ray-Chaudhuri–Wilson in GI; follow-ups to HJ. Nothing found on lazy or pruned certificates; automorphism pruning itself is standard in practical solvers. Ray-Chaudhuri–Wilson is used for design isomorphism complexity (arXiv:1006.5892) but I found no use in local certificates. The HJ paper did not surface in search; it is read from the local LaTeX. Absence of evidence only; I would call LHJ "not found", and Lemma R and Theorem U "routine".
