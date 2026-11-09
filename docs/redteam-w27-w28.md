# Red team: w27-tree and w28-sigma

Referee memo, branch `w31-redteam-w27w28`, 2026-11-09. Targets: `docs/w27-tree.md` (code `docs/w27-code/`) and
`docs/w28-sigma.md` (`docs/w28-sigma-check.py`). HJ = arXiv:2611.01399, read from the local LaTeX. **Everything
said about HJ assumes HJ is correct**; it is unrefereed and I did not audit it. Lean was not run.
Independent checks: `docs/redteam-w27-w28-check.py` (§10).

## 0. Verdicts

**No claim is broken.** I found no counterexample and no invalid step in a main theorem. I did find one
overlabelled proposition (P3), one citation that does not give the stated bound (Theorem C), one misuse of "FPT"
(Theorem G), a scope problem in how Cor N.1 is presented, and some small fixes.

| # | Claim | Verdict | One-line reason |
|---|---|---|---|
| 1a | Prop N, Lemmas 1–2, tower depth | **sound** | Re-derived. Tower depth is section-monotone by transitivity of "section"; the real content is subadditivity along a normal series. |
| 1b | Cor N.1 | **sound as stated, narrower than advertised** | Uses reflection only at identity tanglegrams, which are polynomial and could be special-cased. The sharp statement is pointwise (§1). |
| 1c | "Every campaign reduction is Aut-reflecting" | **true of T2 Thm A and W8 Prop H; the §0 wording "every" is unsupported** | Checked item by item. "Aut" of a pair-input or CI instance needs defining. |
| 2a | Theorem G | **sound; cost correct; "FPT" only for bounded $\rho$** | $(b^m)^\rho=N^{\Theta(\rho)}$. Exhaustive equivalence test including twins and $\rho=2$, which E1 did not cover. |
| 2b | Theorem G+ | **sound** | Same test, 0 disagreements. Untested in w27. |
| 2c | Theorem C | **sound with two fixes** | Luks 1982 alone gives $m_P^{O(b)}$, i.e. XP; the absolute exponent needs Pálfy–Wolf. $R$ must be given or searched. |
| 3 | Lemma MD | **sound** | Every step re-derived, including the $W_h$, $G_2$ applications. Not found stated; very likely folklore. |
| 4 | Lemma 3.1, Prop 3.2 | **sound, one small gap** | Checked on genuinely binary tanglegrams. Needs every data pair to straddle (zero columns and weight-1 rows break that); a one-line pad fixes it. |
| 5 | LHJ correct (L1); L2 | **sound given HJ** | One boundary slip ($\le\frac34$ must be $<\frac34$). L2 replayed at level 0 and level 1. "Chain never starts" is a statement about the root. |
| 6 | Lemma R, Theorem U, GI-root corollary | **sound** | Re-derived. Lemma R in fact bounds *distinct* blocks. |
| 7a | M1, M2 | **sound** | Flag recovery re-derived. Best stated as a lower bound on the memo table (§6). |
| 7b | P3 | **gap: labelled [PROVEN], one existence step not proved** | Existence of $R$ was left to the sketched union bound. §6 gives an explicit $R$, independent of $m$, which closes it. |
| 7c | C1, Theorem L(i)(ii) | **sound** | L is conditional ("if it fires at all levels"), as stated. |
| 8 | §2.9 correction, R0, R1 | **sound as labelled** | Level steps re-derived with deletions. Root entry and the pruning clause remain sketches, as w28 says. |

---

## 1. Prop N and Cor N.1

**Checked by hand, every step.** $Y_c$ is the iterated wreath power with kernels $B_j$.

* *Section-monotone.* Define $\mathrm{td}(G)=\max\{c:Y_c\text{ is a section of }G\}$. A section of a section is a section, so td is monotone under subgroups and quotients.
* *Fact (normal subgroups are the chain $B_j$).* $C_{Y_c}(B_{c-1})=1$, $B_{c-1}$ is minimal normal by top transitivity, induct. Correct.
* *Lemma 1.* At the step where $\varphi(H_j)\ge B_{c-1}$ but $\varphi(H_{j+1})\not\ge B_{c-1}$, the chain property forces $\varphi(H_{j+1})=1$, so $\varphi$ factors through $H_j/H_{j+1}\le S_b$ and $60^{5^{c-1}}\le b!$. Correct. ($D(b)<1$ for $b<5$ is the right reading: $A_5$ is not a section of $S_4$. At $b=1$ read $D(1)=0$.)
* *Lemma 2.* $B_j/B_{j'}\cong Y_{j'-j}^{\,5^j}$, and projecting to one factor applies Lemma 1. Correct. This subadditivity is the theorem.
* *Prop N.* $N_i/N_{i+1}$ is a direct product of copies of $G_k$, because all predecessors of a rank-$(i+1)$ element have rank $\le i$ and $N_i$ acts trivially on them. $\ell$ counts elements of a chain; for $(A_m{<}k)\sqcup(A_m{<}k)$, $\ell=2$.
* *The tower in $W_h(b_0)$.* $Y_h\le W_h(b_0)$ for $b_0\ge5$, via $g=(\sigma;g_1,\dots,g_{b_0})$ with $\sigma\in A_5$ on the first five children, $g_i\in Y_{h-1}$ for $i\le5$, $g_i=\mathrm{id}$ otherwise. w27 asserts this; it is true.

**The actual reductions** (read in `docs/w4-t2.md`, `docs/w8-poset.md`, and `docs/w2-coset.md` Prop 6.1):

| Reduction | Direction | Aut relation | Note |
|---|---|---|---|
| T2 A(i) | $T^2\to$ tanglegram | equal | the key lemma of (i) |
| T2 A(ii) | tanglegram $\to T^2$ | equal | |
| T2 A(iii) | tanglegram $\leftrightarrow$ FullCI | tanglegram $\mathrm{Aut}=A\cap A'$ | a CI instance has no "Aut" until one declares it to be the group of the answer coset |
| T2 A(iv) | $T\square T\leftrightarrow T^2$ | equal | W2 Prop 6.1 |
| T2 A(v) | HS$(b,r)\to T^2$ | restricts onto | sorts under a root; product sort for $r>2$ |
| T2 A(vi),(vii) | HCGI, Def-CI | restricts onto | |
| W8 H.2 | R1$_c\to$ SI$(C_h\sqcup C_h)$ | equal | via A(ii) |
| W8 H.3 | SI$(S_b^{(P)})\to$ R1$_c$ | restricts onto, kernel on dummy padding | direction irrelevant to Cor N.1 |
| W8 H.4 | induced subposets | one-fibre restriction onto | correct: isomorphisms fix the coordinates outside $P'$ |

So the body's claim ("all reductions of T2 Theorem A and W8 Prop H") is **true**, with the CI caveat. The §0 table says "every reduction in the campaign". That is unsupported: I checked only these two theorems, and the campaign contains reductions that are not many-one at all (Luks's GI$_{\deg}\to$SI recursion, W6 Prop D, W6 Prop S). Say "every reduction **from R1$_c$** in T2 and W8".

**Gaps, all in the framing.**

1. *Pair-input reductions.* The definition speaks of $\mathrm{Aut}(x)$ and $\mathrm{Aut}(\varphi(x))$, with $\varphi$ acting on single objects, while a many-one reduction takes a pair $(x,y)$. Fix: state the definition object-wise, or on the pair.
2. *The corollary uses reflection at one family only.* The proof reads $\mathrm{Aut}$ only at the identity tanglegram, which is a tree and solved by AHU. A reduction could detect those instances in polynomial time and output a rigid instance. That does not violate Cor N.1, but it shows the corollary is about the definition at easy instances. Prop N gives the **sharp form**: if $\varphi$ reflects at $x$, then $\mathrm{td}(\mathrm{Aut}(x))\le\ell D(f(b_0))$. That is pointwise, needs no quantification over reductions, and covers subgroups of $S_b^{(P)}$ and $\ell=\ell(b_0)$.
3. *Non-reflecting reductions cannot be excluded this way.* If R1$_c$ is FPT, it reduces to anything with trivial target groups. So "Hardness in the only sense the campaign has ever used is impossible, so the question reduces to the FPT side" should read: "a hardness proof for height-2 posets cannot be of the gadget kind used so far". It reduces nothing to the FPT side, and "W8's alternative hypothesis survives" is not established by this.

**Verdict: Prop N sound. Cor N.1 sound as a statement about reductions that reflect at identity tanglegrams.**

---

## 2. Theorems G, G+, C

**Theorem G.** Re-derived the equivalence: on a branch (ordered images of the rows of $B$), $(g_1,t)$ extends to an isomorphism iff $\tilde x\to\tilde y$. The converse is the only non-trivial step: equal multisets at each row give equal $\phi$-class sizes, and within a $\phi$-class all columns are twins in both instances, so any bijection between classes works for every row at once. Tags force the row order. Rejecting a branch when $y$ fails the pinning condition is correct.

*Cost.* W8 Theorem 1 on $(A_m{<}k)\sqcup A_m$: with the order "$A_m$, then $k$, then $A'_m$" every $R_t$ contains only elements with no unprocessed predecessors, so $\mu=0$ and the cost is $b!\,2^{O(b)}N^{O(1)}$. W8's use of ADKT Theorem 5 (read in `r4-sources/w1fpt-adkt/`: coset intersection in $2^{O(b)}n^{O(1)}$ for groups stabilising each class of a partition into classes of size $\le b$) is right. Branches: $\le(b!\,b^m)^\rho$. **The stated cost is correct.** A pinning set is found additively by brute force over the $\le(b^m)^\rho$ candidates. To output a coset, also run $(x,x)$.

*Label.* w27 §0 says "FPT on three sub-classes". But $b^{m\rho}=N^{\rho/2-o(1)}$, so Theorem G is **XP in $\rho$**: FPT in $b$ for constant $\rho$ (the $\rho=1$ corollary is what w27 actually uses), not FPT in $(b,\rho)$. The same holds for G+ in $\rho$; G+ is FPT in $r$.

**Theorem G+.** Correct by the same argument. Fixing the permutations on $I$ makes the rows with $a|_I=u$ map to those with $a|_I=\sigma(u)$, so histograms are transported; the rest is Theorem G with $G_1$ replaced by a coset.

**Exhaustive check** (`pin`, `pinplus`). Random instances with twin classes and $\rho\in\{1,2\}$, with $y$ a random image or a perturbation. For every branch and every $(g_1,t)$ with the prescribed rows, compare $P$ = "some $\gamma$ works" with $Q$ = "$\tilde x\to\tilde y$". Theorem G: $(b,m)\in\{(2,1),(2,2),(3,1)\}$, about 130k tests per seed, seeds 1 and 2: **0 disagreements**. G+: $|I|\in\{1,2\}$, $\rho\in\{0,1\}$, $(b,m)$ up to $(3,1)$ and $(2,3)$, about 150k tests, seed 1: **0 disagreements**. A control with a non-pinning block gives $P\ne Q$ in 40/40 cases, so the test has power. E1 (seed 1 replayed, 36/36) only uses $\rho=1$ with no twins, so this closes that hole.

**Theorem C.** The structure is right. Invariance of $\tau$ confines the top part to a coset of $C$. In Luks's recursion each orbit meeting several $K$-orbits has the partition into $K$-orbits as a block system, even for subgroups $H\not\ge K$ arising later, and the primitive quotient is a section of the top image, hence soluble. Each terminal window has image in $S_b\times S_b$. Two fixes.

1. *Citation.* Luks's bound for $\Gamma_d$ gives primitive order $m^{O(d)}$ (BCP); with $d=b$ that is $N^{O(b)}$, not FPT. The absolute exponent comes from the Pálfy–Wolf bound for soluble primitive groups, $|P|\le 24^{-1/3}m_P^{3.25}$ (cited from memory). Name it; it is what the proof uses.
2. *$R$.* The algorithm must know $R$. Searching costs up to $(2m+1)^r$, which is not inside $(b!)^{r+2}N^{O(1)}$ for small $b$ and large $m$ (take $b=5$, $r=\Theta(m)$), but is $\le r^{O(r)}+N^{o(1)}$ since $m\le\log_2N$. So: $(b!)^{r+2}N^{O(1)}$ given $R$; FPT in $(b,r)$ with an extra $r^{O(r)}$ otherwise.

I did not implement Theorem C. **Verdict: sound with those two fixes.**

---

## 3. Lemma MD

Re-derived every step: $C_W(M)=1$, so every non-trivial normal subgroup contains $M$; a faithful action has an orbit on which $M$ is non-trivial, and that orbit is faithful; $|W:H|\ge ef'$; both index cases including $f'>r$; Scott's lemma; $\sqrt{|\mathrm{Alt}(b)|}\ge b$ for $b\ge5$; proper subgroups of $\mathrm{Alt}(b)$ have index $\ge b$. The $W_h$ and $G_2$ applications are right, since $W_{h-1}$ and $S_b^m$ are transitive. **Sound.**

Wording only. §4 item 2 says an algorithm "pays $2^{\Omega(b^{m+1})}$". Lemma MD bounds the orbit size available, so the $2^{O(\text{orbit})}$ *upper bound* becomes useless; it does not say any algorithm must spend that. "No small faithful domain in any DP order" is true (at the first step of every linear extension one whole side, including its $k'$, lies in $R_t$, and minimal degree is monotone under subgroups), but w27 omits that sentence.

---

## 4. Lemma 3.1, Prop 3.2

**Counting.** Correct: at least $2^{s^2/4}$ codes at $k=s/2$; the number of $(I,\iota)$ is $2^{O(\ell\log\ell)}(4\ell)^{2s}$ (unary nodes suppressed, colours renamed); $\rho_2$ full forces the output to determine $C$, so $\ell=\Omega(s^2/\log s)$. This refutes W6 lead 2 as stated. Since $u_1$ itself defines $\rho_1$ on $O(s^2)$ leaves, the bound is tight up to the $\log$; w27 should say so.

**Lemma 3.1, on actual binary tanglegrams.** E3 omits the comb spines and has out-degree above 2 at the pair nodes. `lem31` builds two trees of out-degree exactly $\le2$ with all combs, computes $S(u)$ and bottom$(S(u))$ from the definition, and takes groups from nauty: $|\mathrm{Aut}|=2^{s-\mathrm{rk}H}$, flip patterns in and spanning the code, $\rho_2=F_2^s$, $\rho_1=C$. For $s\le16$: **34/35**. The one failure is this real gap.

*Gap.* The lemma says "for every code". If $H$ has a zero column or a weight-1 row, some side $q_j^i$ has no leaf in $L_1$, so it does not straddle and $F$ has fewer than $2s$ nodes (seen at $s=4$, $|L_1|=13$: 7 bottom nodes). *Fix:* give each $q_j^i$ one dedicated $L_1$ leaf under a rigid pad in $T_{u_1}$, or restrict the count to $H$ with no zero column and no weight-1 row (still $2^{\Omega(s^2)}$ codes). Also put the data variables first in the comb of $T'$, so that $|S(u)|=O(s)$; the test does this.

E3 replayed 100/100. **Verdict: sound.** The hedge "mod T2 Thm B" is still appropriate: I did not re-prove the encoding beyond the argument that the flip patterns are forced to be translations, and the machine check is at small $s$.

---

## 5. Lazy Step 4 (L1) and L2

**L1.** Read HJ L2619–2800, L2841–2853, the phase induction (L1640–1720), and Helfgott §6.2 (`BDHv8.tex`). Checked:

* Phase 0 stops exactly where HJ's loop reaches step 4; statuses and prefix cosets are HJ's. HJ's prefix-recovery argument is stated for every finite prefix, so prefix classes form an equivalence relation, and differing stop stages give empty comparisons.
* Twin-freeness suffices for the Design Lemma: "$T$ is not full" is used only in the no-large-twin argument (HJ L2720–2726; Helfgott: "$T$, being contained in $\Gamma\setminus S$, is not full"). Nothing else in Case 3 uses that $T$ is resolved.
* Cases 1, 2a, 2b use only $F\le\mathrm{Aut}$, equivariance and the case hypotheses, as Helfgott's text confirms. $F_0$ is canonical and in $\mathrm{Aut}$.
* Escalation is canonical (a class above $\frac12$ is unique). All $T\subseteq C$ are Pending, by the HJ argument and $T\not\subseteq S_0$. Finishing them either adds to $S$ or breaks the class, so the loop stops, with no extra recursive multiplicity.
* Every child is an HJ child; multiplicities are no larger; aggregation branches are HJ's. LHJ reaching Case 3 at a node where HJ would not is not a new charge type. **Lemma 7.1's class bounds are preserved**, since they are per class of child type.

**One slip.** §5.1 step 3 says "$\le\frac34|\Gamma\setminus S_0|$". HJ's hypothesis is "fewer than $\alpha$ times" with $\alpha=3/4$. Escalate on $\ge\frac34$.

**L2.** Re-derived. If $T$ contains a line, $\phi_T(A_1)$ preserves the collinear triples of $T$, because blocks with points in three of the cosets exist exactly for lines. For $x\ne y$ the swap changes the collinear-triple pattern of a suitable ordered $T$, so the first-window colours differ. The root cases (point/block, block/block) go through. "Otherwise generic" needs $r_j\ge\kappa+O(1)$, which chain levels satisfy.

*Replays.* `phase0`: the results quoted in w28 §5 reproduced, including windows 34034 and 26746 at $m=5$ and $\{1,2,4,7,8\}$ Nonfull at iteration 2 with image 12 of 60. New: at level 0, and at level 1 with $D=\langle1\rangle$, a $T$ containing a line is Nonfull at iteration 1 with image 6 of 60. These are small and check windows, not asymptotics.

*Scope.* "The B1 chain never starts" is a statement about the root. Under LHJ chain states are not reached by the chain, so the "every chain state" half only matters if such a state arises by another route. w28 labels the whole-tree claim [SKETCH]; correct.

**Verdict: sound given HJ.**

---

## 6. Memoization, P3, C1, Theorem L

**M1, M2.** Flag recovery is correct: $\sum_{\tau\in U_j}\mathrm{im}(\tau-1)=D_{j-1}$ uses only the $\mathrm{Hom}(D_j/D_{j-1},D_{j-1})$ part of $U_j$ and triviality on $D_j/D_{j-1}$; restriction to $D_{j-1}$ is onto $U_{j-1}$. The count $\binom q\kappa/\binom r\kappa_2\le2^{\kappa^2}$ is correct and `count` reproduces the numbers.

*Precision.* (a) "Saves only $n^{O_\kappa(1)}$" compares to B1's lower-bound product, while HJ's true tree also has ordered comparisons. The clean statement: the table of distinct exact states has at least $\prod_{i<j}\binom{r_i}\kappa_2$ entries at level $j$, so memoized HJ still makes $2^{m^2/2-O_\kappa(m)}$ calls on $X_m$. (b) M1's parenthesis on parity is fine for HJ's actual normalization, which cuts only the sign on $\pi$. It would not follow for an arbitrary group between $[G_j,G_j]$ and $G_j$ (w18's "any $G$"), since $U_j$ is a 2-group and not perfect.

**P3: gap, closed here.** The argument is right if $R$ exists: $T$ ends Full (never Nonfull, since $\mathrm{Aut}$ induces $\mathrm{Alt}(T)$, and the loop terminates), and $T'$ cannot be Full. But "such that $\mathrm{Stab}_{\mathrm{GL}}(R)$ does not induce $\mathrm{Alt}(T')$" is asserted, resting on the same union bound w28 labels [SKETCH]. **Explicit $R$** ($m\ge3\kappa$, $|R|=O(\kappa^2)$ independent of $m$): let $T=\{e_1,\dots,e_\kappa\}$, let $f_1,\dots,f_{2\kappa}$ be further basis vectors, and $T'=\{f_i+f_{i+\kappa}\}$. Take an asymmetric graph $\Gamma$ on $[2\kappa]$ with minimum degree $\ge2$ and no edge $\{i,i+\kappa\}$, and put $R=\{\{f_i,f_j,f_i+f_j\}:ij\in E(\Gamma)\}$.

* Off $\langle T\rangle$, since $R$ lies in $C=\langle f_i\rangle$. Off $\langle T'\rangle$, whose vectors have $f$-support a union of pairs $\{i,i+\kappa\}$.
* The maps $g_\sigma$ fix $C$ pointwise, so $R$ is invariant and $\mathrm{Aut}$ induces $\mathrm{Alt}(T)$.
* Any $g\in\mathrm{Stab}_{\mathrm{GL}}(R)$ is an automorphism of the configuration on $P_R$. The $f_i$ have degree $\ge2$ and the points $f_i+f_j$ have degree 1, so $g$ induces an automorphism of $\Gamma$, hence fixes each $f_i$, hence fixes $T'$ pointwise.

With R0, P3 follows. Checked at $\kappa=3$, $m=9$ (`p3x`: every point of $T'$ fixed, $T$ one orbit); random $R$ on PG(7,2) at $\kappa=5$ also behaves as required (`p3`).

**C1.** Correct. **Theorem L.** (i), (ii) are correct: all level-$j$ states from independent sequences are GL-conjugate, so an isomorphism-invariant rule is all-or-none per level, and prefix types agree for far $T$ (linear $g$ fixing $D_j$, §8 patch). The conclusions are conditional on the rule firing at all levels, as stated.

---

## 7. Lemma R, Theorem U, GI root

Lemma R is correct: $M=WW^{\mathsf T}$ lies in the Bose–Mesner algebra, $s'\le v/2$, the test vector lies in $V_r$, and $\langle h,w_R\rangle=\binom{|R|-r}{s'-r}>0$, so every $\theta_r>0$. It bounds distinct blocks, by rank. Theorem U: row-count transport is correct; in case (b), $v\ge\kappa>2k_*$ makes the small and co-small ranges disjoint and Möbius inversion gives equal trace counts. The GI-root corollary is correct (needs $\kappa\ge4$, $n\ge12$). Two small points: "product state" should say that the first window being $B\times T$ is part of the hypothesis; and §7.2's $s^{2/\kappa}$ is exact for even $\kappa$, while odd $\kappa$ gives $s^{2/(\kappa-1)}$.

---

## 8. §2.9 correction, R0, R1

$|\mathrm{GL}(m,2)|/\#\text{lines}=2^{m^2-2m+O(1)}$, and a switched block leaves index $2^{O(m)}$ more generally. R0 is correct. `rigid 7 3` gives 82944, matching $6\cdot|\mathrm{GL}(2,2)|^3\cdot2^6$. I re-derived Lemma 1 on $X_{m,R}$ line by line: $(\star)$ uses only real lines through $T+D_j$; every window row is either a real line through $T+D_j$ or $D^*$, or carries only zeros, so the $\rho_W$ patch is valid; the spoiled-$T$ count and $J'$ are right. The error "$O(\log\log n)$" is loose, $O_\kappa(1)$ suffices. All `rigid` and `pasch` rows reproduced.

R1 stays **[PROVEN, given HJ]** for level steps and **[SKETCH]** for the root entry and pruning, as w28 labels it. I traced the root cases and found no obstruction, but did not write them out. R2 is experiment only, as labelled.

---

## 9. Strongest statements I would sign, and novelty

> **(A)** Let $\mathrm{td}(G)$ be the largest $c$ such that the depth-$c$ iterated wreath power of $A_5$ is a section of $G$. If $G$ has a normal series of length $\ell$ whose factors embed in direct products of $S_b$, then $\mathrm{td}(G)\le\ell(1+\log_5\log_{60}b!)$. This covers every subgroup of $S_b^{(P)}$ with $P$ of height $\ell$. Any reduction from R1$_c(b_0)$ to such a family which reflects $\mathrm{Aut}$ at an instance $x$ forces $\mathrm{td}(\mathrm{Aut}(x))\le\ell D(f(b_0))$. The reductions of T2 Theorem A and W8 Prop H reflect $\mathrm{Aut}$ at every instance, so a hardness proof for bounded-height posets cannot take that form.

> **(B)** For HT2, mod ADKT Theorem 5: SI is computable in $(b!\,b^m)^\rho\,b!\,2^{O(b)}N^{O(1)}$ when $\rho$ row blocks pin the columns modulo twins (FPT in $b$ for constant $\rho$); the histogram variant adds $(b!)^r$. With a surviving top having soluble pointwise stabiliser of a *given* $r$-coordinate set: $(b!)^{r+2}N^{O(1)}$, mod Luks's recursion and Pálfy–Wolf.

> **(C)** $\mathrm{Sym}(b)\wr R$, $R$ transitive on $r$ points, $b\ge5$, has minimal faithful degree exactly $rb$, attained on a faithful orbit.

> **(D)** A definable one-call combine on the code instances of Lemma 3.1 (with the pad fix) needs $\ell=\Omega(s^2/\log s)$ leaves while $n-n_{\max}=2s$, so W6 lead 2 fails; tight up to $\log$.

> **(E)** Given HJ, Lazy Step 4 is correct and within HJ's bound and Lemma 7.1's class bounds (after the $<\frac34$ fix). On $X_m$, at the root and at every chain state, Phase 0 is twin-free, so no Step-4 child is made at the root.

> **(F)** Lemma R and Theorem U as stated (product states, two colours); P3 with the explicit $R$; M1 in the form of §6; C1; the correction to w18 §2.9; R0; R1's level steps given HJ.

I do not certify: HJ; R1's root entry and pruning clause; Q1, P2, the Uniform Prefix Conjecture; or any asymptotic statement beyond the hand proofs. My machine checks are small ($s\le16$; $b\le3$; $m\le9$; $\kappa\le5$). Theorem C was checked by hand only.

**Novelty.** Searches on 2026-11-09 (minimal degrees of wreath products; Ray-Chaudhuri–Wilson for variable blocks) are thin, and absence means little.

* *Lemma MD:* not found stated for $\mathrm{Sym}(b)\wr R$. The closest are the Easdown–Praeger and Alotaibi–Easdown papers ([preprint](https://talus.maths.usyd.edu.au/u/pubs/publist/preprints/2023/alotaibi-10.pdf), which treats other wreath products) and a reported cyclic-base case $C_p\wr\mathrm{Sym}(q)$ of degree $pq$ (Easdown–Saunders, seen only in a search summary). Treat it as folklore.
* *Lemma R:* the uniform case is Ray-Chaudhuri–Wilson 1975. I did not find the variable-block form stated; it is routine, and an expert may place it in the $t$-wise balanced design literature. I could not confirm that.
* *Prop N, tower depth, the reflecting framing:* not found; elementary.
* *Theorems G, G+, C:* elementary combinations of ADKT and Luks.
* *Prop 3.2:* the classical comparison of counting subgroups against counting small structures; the content is its application to W6's lead.
* *LHJ:* not found, and it is a small modification. P1 is standard automorphism pruning, as w28 says.

---

## 10. Reproduction

```sh
PY=/home/bepis/math/gi-practical-wt/r2-hybrid/.venv/bin/python; cd docs
nice -n 19 $PY redteam-w27-w28-check.py pin 1        # also 2; Theorem G, twins, rho<=2, with control
nice -n 19 $PY redteam-w27-w28-check.py pinplus 1    # Theorem G+
nice -n 19 $PY redteam-w27-w28-check.py lem31 1      # Lemma 3.1 on binary tanglegrams, s<=16
nice -n 19 $PY redteam-w27-w28-check.py p3 8         # random R; m=9 did not finish and was stopped
nice -n 19 $PY redteam-w27-w28-check.py p3x 9 3      # explicit R of section 6, kappa=3
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[]" "[1,2,3,4,8]"         # T with a line, level 0
nice -n 19 $PY redteam-w18-latin-check.py state 7 "[[1]]" "[2,4,6,8,16]"     # T with a line in Q_1, level 1
```

Replayed: `w28-sigma-check.py` (count, twins 6, rigid, pasch, phase0, matching the memo), `e3_code_gadget.py` (100/100, seeds 1–4), `e1_pin.py` seed 1 (36/36). E1 seed 2 and E2 were not rerun.
