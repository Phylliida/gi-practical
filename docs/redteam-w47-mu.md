# Red team: w47-mu (Theorem A, A′, L, B, C, D, E)

Adversarial referee report, branch `w48-redteam-mu`, 2026-11-09. Target: `docs/w47-mu.md` at commit `a4b18d3`. HJ = arXiv:2611.01399, line numbers `L…` of the local LaTeX. Helfgott = arXiv:1710.04574 (`BDHv8.tex`). The Lean tree (`~/math/GraphIsomorphismLog2`) was read only, never run. Code: `docs/redteam-w47-code/`, written independently of `docs/w47-code/`.

**Bottom line.** Theorem A survives. I could not break the trace, the count, Lemma L or Lemma B. One theorem (C) is false as stated, because its list of group-producing operations omits the wreath-product outcomes of HJ's Case 1; its conclusion survives after a repair. The other findings are statement errors or scope overclaims. Nothing here upgrades or refutes the claim about GI, and the memo is careful about that.

## 0. Verdicts

| # | Claim | Verdict | Severity |
|---|---|---|---|
| A | Trace reaches a `Continue` node enumerating $\mathrm{GL}(m-2,2)$, $\lvert P\rvert$ children | **sound**, given (H0) and HJ as written | none |
| A (wording) | "on the 2-subspaces", degree $d\approx n/16$, for every tower | **statement error**: true only when the top partition is a coordinate partition | low |
| A (wording) | $N=n(n-1)$ | **statement slip**: HJ sets $N=\lvert\Omega\rvert=n^2$ (L1145, L596). No effect on any exponent | trivial |
| A′ | $J_2(m,2)$, same count | **sound with fix**: test set never given; "index $\le2$" is really $L=\mathrm{GL}(V)_\ell$ | low |
| L | $\mathrm{Aut}(W,R;\text{meet})\cong\mathrm{GL}(V)_\ell$, $m\ge5$ | **sound** | none |
| B | unique block system on $W$, quotient $\mathrm{GL}(m-2,2)$ on $G_2$ | **sound** | none |
| Remark §3.4 | unordered-pair tower | **sound**, and sharper: at $k=5$ the action is on hyperplanes, degree 31, not 155 | low |
| C | answer-free nodes are Young; primitive quotients are natural/2-subset giants or bounded | **broken as stated**; conclusion on enumeration survives with repair (§5) | **medium** |
| C Corollary | "not a giant of degree $\le q_1$ ⇒ answer ancestor" | **false as worded** (bounded-order non-giants occur answer-free; also conflicts with C's own "or bounded degree") | low |
| D | pruning removes this enumeration | **sound at the node**; §5.1 and §6 overreach | low |
| E | no $\exp(o(\log^2N))$ theorem for enumerated quotients | **sound** given A | none |
| §6 | "$\mu$ exceeds the σ chain" | **sound** as a comparison of two lower bounds, same unit; say "proved lower bound" | low |
| §6/§7 | separation HJ vs GI; prior art | **sound**, hedges accurate; add context, restrict "Babai-type" | low |

No break found in: Step 1 (fullness of independent tests), $F$ normal and simple, Case 2b, the rank-3 refinement, the choice of $W,R$, the rectangle answer, the orbit-chain order, the Small test, the child count, or $n\ge2^{125}$.

## 1. Method

Exact computation with my own harness. Three tools were already in the store (no download): nauty 2.9.1 (`dreadnaut`), GAP 4.15.1, Python.

| Script | Purpose | Result |
|---|---|---|
| `check_L.py 5 6 7 8` | Every nauty generator of $\mathrm{Aut}(B)$ is reconstructed as a linear map fixing $\ell$, verified additive on all pairs and matching on $W$ and $R$ | pass for all generators; so $\mathrm{Aut}(B)=\mathrm{GL}(V)_\ell$ **as a group**, not just in order |
| `emit_group.py`, `lemma_b.g` (GAP) | $\mathrm{GL}(V)_\ell$ on $W$, $m=5,6,7$: order, suborbits, block systems over **all** suborbit reps, quotient | $\{16,\lvert W\rvert\}$ only; $P$ primitive of orders 168, 20160, 9999360 |
| `lemma_b_unordered.g` | Overgroup lattice of $\mathrm{Stab}_{\mathrm{GL}(5,2)}(\{S_1,S_2\})$ | $T<X<Y<G$, $Y$ = hyperplane stabilizer, index 31 |
| `j2_sign.g` | Parity for $J_2$ | sign product $\mathrm{sgn}_W\mathrm{sgn}_R\equiv1$; $L'=\mathrm{GL}(V)_\ell$ |
| `wreath_example.g` | Case-1 wreath outcome | $\mathrm{Sym}(4)\wr C_2$ on 16 cross pairs is primitive, not natural/2-subset |
| `check_numbers.py` | All numeric claims, by exact arithmetic | see §3, §7 |

Reproduce from `docs/redteam-w47-code/`, with `GAP` and `dreadnaut` the store binaries named in the scripts: `python3 check_L.py 5 6 7 8` (m=8 takes several minutes); `python3 check_numbers.py`; for $m=5,6,7$, `python3 emit_group.py $m > group_$m.g; cat group_$m.g lemma_b.g | $GAP -q` (and the same with `j2_sign.g`, $m=5,6$); `$GAP -q lemma_b_unordered.g`; `$GAP -q wreath_example.g`.

## 2. Does HJ really take this path?

I walked Algorithms 1, 4, 5 and the aggregation (L2789–2830, L1168–1176, Helfgott §6.2, §5.2) step by step, and compared the Lean `Run` constructors (`Procedure.lean`), `Expose.lean`, `Dispatch.lean`, `FreshState.lean`, `AuxRectangle.lean`, `OutOrbital.lean`.

| Step | Interception tried | Result |
|---|---|---|
| Root intransitive | L1150, L622 | $\Omega_1$ is the largest orbit, first. Fine. |
| Root enumeration/product | L1154 | $\mathrm{Sym}(n)$ with $n\ge2^{125}$ fails Small (for $a$ up to about $n/\ln n$; $m_0$ absorbs $a$); $r=1$. |
| `RowStep` | L1164–1167, Cor. physical-support | kernel of $\mathrm{Alt}(n)$ on $\Omega_1$ is trivial, two-label map. No RowStep. |
| Other aggregation case | Helfgott Cases 1, 2a, 3 | $F=\mathrm{GL}(V)$ has orbit $\mathcal L$ with $\lvert\mathcal L\rvert>n/2$ ($m\ge4$), not a giant: exactly Case 2b. |
| Fullness | L781–794, L2629–2673 | $\mathrm{GL}(V)_T$ induces $\mathrm{Sym}(T)$, $\mathrm{GL}(V)\le\mathrm{Alt}(n)$, so $\mathrm{Aut}_{P_T}(x)$ maps onto $\mathrm{Alt}(T)$ at every window; only `Full` can end the loop, $K(T)\ne1$. |
| $F$ normal, nontrivial | L2858–2861, L732–734, L2742–2754 | equivariance gives $K(T^g)=K(T)^g$; $F\trianglelefteq\mathrm{Aut}_{G_0}(x)=\mathrm{GL}(V)$ simple. Correct. Setup is the pair state $\mathrm{Alt}(n)$ on $\Omega_1$, ideal map the identity on $\Gamma=[n]$, so $F$ lives on the right set. |
| Case 2b, $d$ | L2798–2813 | rank 3, $d=1$, no anchors; both orbital choices give the same SRG scheme. |
| Imprimitive / balanced | L4513–4517 | scheme primitive; dominant class skew; $\lvert W\rvert>\tfrac34\lvert C\rvert$ iff $m\ge6$. |
| Choice of $R$ | Helfgott Thm 5.3, L4520 | $c(x,y),c(z,y)\ne$ aqua forces beige = cyan = meet ($y=x$ is excluded by $c(z,x)=$ aqua). $R$ is forced. |
| Rectangle / parity | L4407, L4480 | $Y=P\cup\{\ell\}$, full $\mathrm{Sym}(W)\times\mathrm{Sym}(R)$. |
| `LiftAndContinue` | L1077–1083 | $H$ intransitive; suborbit lengths computed exactly: $m=7$: $6,9,168,504,1792$, $\lvert\Gamma\setminus W\rvert=314$. $O_{\mathrm{gen}}$ is the unique largest orbit for $m\ge6$. |
| Stop conditions | L1149, `Run` | $\lvert O_{\mathrm{gen}}\rvert/N\to1$ (0.57 at $m=7$, 0.76 at $m=8$); no early exit in `Run`; `orbitStop` fires only after its first child has returned, so the first-orbit node is created regardless. |
| Tower | L638–640, L3176; `FreshState`, `Expose` | Lean starts from a single interval and `exists_maxCand` maximizes related pairs, which at $\Omega_1$ picks a coordinate partition. The paper leaves the hierarchy free, so the three cases are needed, as the memo says. |
| Small test | L1766, `Dispatch.lean` | $\ln\lvert P\rvert\le a\ln^2d$ for all $a\ge1$; Lean requires $a\ge128$; integer `SmallZ` also passes, so `normalize` is unavailable and enumeration fires. |

The memo correctly says "contains a node". Every choice point (tower, orbital, source vertex, target) gives the conclusion, up to the wording issue below. This is universal over executions on the true branch, and existential only in that a tree has many other branches.

**Statement error (low).** §3.1 says the node enumerates $P$ "on the 2-subspaces", degree $d\approx n/16$, with no tower hypothesis. The unordered-pair tower gives a different action. At $k=5$ (`lemma_b_unordered.g`) the overgroup lattice of $T=\mathrm{Stab}(\{S_1,S_2\})$ is $T<X<Y<\mathrm{GL}(5,2)$ with $Y$ the hyperplane stabilizer, so the exposed quotient is $\mathrm{GL}(5,2)$ on 31 hyperplanes, not on 155 lines. For $k\ge6$ I expect $G_4(U)$; I did not prove uniqueness of the maximal overgroup. Then $d$ and $\mu$ change: if the action is on $G_4(U)$, $\mu=(\tfrac1{16}+o(1))\log_2N$ (`check_numbers.py`). The child count is unchanged. The memo's Step 7 and Remark know this, so the error is only in the theorem statement and the §0 table.

**Corrected statement.** For $m\ge\max(\kappa,7,m_0)$, $Y\cong X_m$, the tree contains a `Continue` node with group $\mathrm{GL}(V)_\ell$ on $O_{\mathrm{gen}}$ whose exposed primitive quotient is $P\cong\mathrm{GL}(m-2,2)$, with $\lvert P\rvert$ children. If the inherited top partition is a coordinate partition (the Lean case), $P$ acts on 2-subspaces, $d\approx n/16$, $\mu=(\tfrac18+o(1))\log_2N$; in the unordered-pair tower $P$ acts primitively in another action (hyperplanes at $m=7$).

## 3. The count

* Children are one per coset of $\ker\rho$ (`Reduction.ofEnumeration`, `Run.dispatch` runs all $j$). $\rho(L)=\mathrm{GL}(U)$ in full, so the count is $\lvert\mathrm{GL}(k,2)\rvert$, not divided by anything. `LiftAndContinue` takes the image of $L$; no stabilizer intervenes.
* $\lvert\mathrm{GL}(k,2)\rvert\ge0.288\cdot2^{k^2}$ holds exactly for all tested $k$ (it is $\prod(1-2^{-i})$). $\log_2\lvert P\rvert-k^2=-1.792$ for large $m$.
* $\lvert P\rvert=n^{(1/4)\log_2n-0.71+o(1)}$, $N^{(1/16)\log_2N-O(1)}$, $\mu/\log_2N=0.1262$ at $m=64$, $\to1/8$. $d/n\to1/16$. All confirmed.
* **$\mu$ versus the σ chain.** B1 counts `Continue` calls, and A counts `Continue` children, so the units agree, and both are lower bounds on tree size. But B1's $2^{m^2/2-O_\kappa(m)}$ is only a proved lower bound on that chain, so "exceeds the σ chain" should read "exceeds the proved lower bound of B1". Asymptotic only (with the $O(m)$ term ignored, $(m-2)^2>m^2/2$ from $m=7$; B1 itself has no levels below $m\approx150$ at $\kappa=64$).
* The "$\Theta$" in §6 item 2 keeps HJ's unrefereed upper bound as its other half, as `redteam-w18-latin` already required.

## 4. Lemma L, Lemma B

Hand re-derivation of §3.3 and §3.4 found no error. Points I specifically tested: the $\lambda$ values including $u\ne u'$ with $r\cap r'\neq\emptyset$ (still 4); the triangle/star distinction in $K_4$ (4 stars, 4 triangles); $f$ constant needs at least three fibres ($m\ge5$); the additivity case split including $x\in V\setminus\ell$, $y\in\ell$; the module argument, including the case $M=\mathrm{Hom}(U/S,\ell)$, $TQ=A$, which uses irreducibility of $Q$ and $k\ge3$; $T\supseteq Q$ in the Remark.

Machine checks are stronger than the author's: generators are shown to be induced by linear maps, so the group is identified and not only its order; blocks are enumerated over all suborbit representatives.

*Note on $m=8$:* `check_L.py 8` completed (31 generators, all induced by linear maps fixing $\ell$), so the group identification holds at $m=8$ too. This is stronger than the memo's $m=8$ check, an order comparison in floating point. Lemma B's block computation was run for $m\le7$ only.

## 5. Theorem C: broken as stated

The list O1–O7 omits HJ's **colored-partition overcosets**, so "the group at $v$ is Young" is false.

* HJ L2985–2993, Case 1: color by orbit length, partition each color class into the $\pi(F_x)$-orbits; "Its full allowed group is a subgroup of $\mathrm{Sym}(\ell)\wr\mathrm{Sym}(r)$." L3002–3018 and L4513 (imprimitive configuration, equal-block partition) give the same shape. Lean: `AggregationPlan.lean` L85, `AuxPartitions.lean` `impPart`, "the overcoset of the colored orbit partition."
* O5 in the memo says "a product of symmetric groups on label classes"; that is wrong for these outcomes, which are stabilizers of a partition into blocks.

**Counterexample path, answer-free in the memo's sense.** Let $X=K_a\sqcup K_a$, $n=2a$. Root as usual. Full tests inside a clique generate $F$ with two orbits of size $a$, so Case 1, $r=2$, $\ell=a$. `LiftAndContinue` runs under $(\mathrm{Sym}(a)\wr C_2)\cap\mathrm{Alt}(n)$. The largest orbit on $\Omega_1$ is the $2a^2$ cross pairs. With the unordered-pair tower the exposed primitive quotient is $\mathrm{Sym}(a)\wr C_2$ in product action of degree $a^2$, primitive, neither natural nor 2-subset (`wreath_example.g`: $a=4$ degree 16, order 1152; and the actual group $(\mathrm{Sym}(5)\wr C_2)\cap\mathrm{Alt}(10)$ on 25 cross pairs is primitive, order 14400). Under a coordinate tower the top quotient is $C_2$ instead, so the failure is tower-dependent. The path uses O1 and a partition overcoset only; $F$ enters through label classes, exactly as for O5.

**Repair.** Replace O5 by: preimage of a product of wreath products $\prod_i\mathrm{Sym}(\ell_i)\wr\mathrm{Sym}(r_i)$ on label classes (this is the shape of Case 1 and of imprimitive-configuration and Design partitions). Redefine Young accordingly. Then primitive quotients on orbits of label pairs are natural or 2-subset giants on block sets or labels, $\mathrm{Sym}(\ell)\wr C_2$ in product action on cross pairs of two blocks when $r=2$, or bounded degree. The enumeration conclusion survives: $2(\ell!)^2\le\exp(a\log^2\ell^2)$ forces $\ell$ bounded, and giants are as before. I checked this reasoning by hand; a complete proof needs the block-system classification for the wreath groups on pair orbits, which the memo does not have and neither do I.

**Corollary, wording.** "A primitive quotient that is not a giant of degree $\le q_1$ can be enumerated only at a descendant of an answer operation" is false as worded: bounded-order non-giants occur (e.g. $\mathrm{Sym}(3)\wr C_2$ on 9 points), and C itself allows "bounded degree". Replace by "a primitive quotient of superconstant order".

Small-degree exceptions of the Young block-system claim (e.g. $\mathrm{Sym}(4)$ on ordered pairs has the extra matching system) are covered by "or bounded degree", so that part is fine.

## 6. Prop D, Theorem A′

**Prop D (sound at the node).** HJ has no automorphism pruning (L1594's "pruned" refers to empty orbit-chain branches). $F_\ell\le H$, and since $\rho(F_\ell)=P$, one coset child suffices: $\mathrm{Iso}$ on $\ker\rho\cdot g$ is a translate. But the proposition's title and §5.1/§6 say the enumeration or channel is removed "on $X_m$". The argument covers only the one node, whose group contains $F_\ell$. At a node where the group is smaller, for example a later orbit under a second-coordinate tower after a label $c\in\Gamma\setminus W$ is fixed, the image of $(F_\ell)_c$ in $P$ is proper (a parabolic when $c$ is a point outside $\ell$). No post-pruning bound for the whole tree on $X_m$ is proved. §5.1's "same status as B1" also overstates: w28's P2 for B1 is [SKETCH], with the Case 2b branches unresolved. **Fix:** state D for this node; call the global collapse conjectural.

**Theorem A′ (sound with fix).**
1. The test set is never stated; §3.2 uses points, which $J_2$ does not have. Fix: $T=\{\langle e_i,\mathbf 1\rangle\}_{i\le\kappa}$ in a $\kappa$-dimensional subspace $\mathbb F_2^\kappa\subseteq V$ (with $\mathbf 1$ the all-ones vector of that subspace); coordinate permutations induce $\mathrm{Sym}(T)$, so $m\ge\kappa$ suffices.
2. "$L$ has index $\le2$" is weaker than the truth: $\mathcal L=W\sqcup R\sqcup\{\ell\}$ and $\mathrm{GL}(V)$ is perfect, so $\mathrm{sgn}_W\mathrm{sgn}_R\equiv1$ on $\mathrm{GL}(V)_\ell$, hence $L=\mathrm{GL}(V)_\ell$ exactly (`j2_sign.g`, $m=5,6$). This also makes the memo's unchecked reuse of Lemma B for an index-2 subgroup unnecessary.
3. $\mathrm{Aut}(J_2(m,2))=\mathrm{GL}(V)$ ($m\ne4$) is Chow's theorem; correctly cited.

## 7. Parameters

* $n$ at $m=64$: $\log_2n=125.415$, so $n\ge2^{125}$ holds.
* $m_0$ is not defined in the memo, only asserted. It is finite. It must absorb: $N=n^2\ge N_0$; $n>q_0$; $n\ge$ the thresholds of Cor. physical-support; $\mathrm{Sym}(n)$ failing Small in natural and 2-subset action (at Lean's $a=36000$: natural from $n=512239$, 2-subset from $n=2148258$; computed by binary search); $\lvert W\rvert>\eta\lvert C\rvert$ (for $\eta=\tfrac34$, $m\ge6$; general $\eta<1$ needs more); $\lvert O_{\mathrm{gen}}\rvert>N^\gamma$. Since $N_0$ is an unspecified "absolute base size" (L1829), "$m\ge64$" is a necessary lower bound, not the theorem's actual range. The sentence "With $\kappa=64$ this means $m\ge64$" should say "at least".

## 8. Consequences and prior art

The memo separates HJ statements from GI statements correctly (§0, §6). Nothing claims a GI lower bound.

Prior art: my searches (two web, plus local sources) found no statement of this result, which matches the memo's "not found". Two suggested additions. (i) Tightness context: $\mathrm{GL}(d,2)$ on points is the classic near-extremal case for Maróti's $n^{1+\log_2n}$ bound, and Miller's $n^{\log_2n}$ for STS is at its worst on $\mathrm{PG}(m-1,2)$; a large Lie-type quotient appearing on this family is therefore expected once a rectangle group retains the geometry. (ii) "Babai-type algorithms" in §7 is broader than what is shown. In Babai and Helfgott, Split-or-Johnson continues past the first bipartite graph with $O(\log n)$ individualizations; the exact-rectangle-then-lift step is HJ's. The result is about HJ.

## 9. What could not be checked

* Everything at actual parameters: $m\ge64$. All group computations are at $m\le8$ (Lemma L) or $m\le7$ (Lemma B), plus arithmetic at any $m$. The path needs $\kappa\le m$, so no actual HJ run on it is possible at $\kappa=64$.
* (H0): HJ's correctness itself, including the exactness of the rectangle query.
* $G_4(U)$ for $k\ge6$ in the unordered-pair tower, and the full wreath-group block-system classification in the repair of Theorem C.
* The paper leaves the initial hierarchy free; the Lean fixes one. I treated all three top partitions.

## 10. Fix list for the author

1. §3.1/§0: state the tower dependence of the action, $d$, $\mu$ (§2 above).
2. §2: fix O5, redefine Young, redo Theorem C and its Corollary (§5 above).
3. §5.1/§6: restrict Prop D to the node; mark the global statement and "same status as B1" as conjectural.
4. §3.6: give a test set for $J_2$; replace "index $\le2$" by $L=\mathrm{GL}(V)_\ell$.
5. §3.1: list what $m_0$ absorbs; "at least $m\ge64$"; $N=n^2$.
6. §6: "proved lower bound of B1"; note Maróti/Miller context; drop "Babai-type".

Sources: arXiv:2611.01399 (local LaTeX) · [Helfgott, arXiv:1710.04574](https://arxiv.org/abs/1710.04574) (local) · [Babai, arXiv:1512.03547](https://arxiv.org/abs/1512.03547v2) · `docs/w18-latin.md`, `docs/redteam-w18-latin.md`, `docs/w28-sigma.md`.
