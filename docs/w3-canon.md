# w3-canon: a canonical HJ, and memoized canonical forms in an FPT hybrid

Branch `w3-canon`, 2026-11-05. Wave 3 of the overnight campaign (`overnight-log.md`).

**Task.**
1. Extract from Babai's canonical-form paper what it took to turn his isomorphism test into a
   canonization. Say which of HJ's new components hit the same obstacles.
2. Design a canonical HJ ("HJ-canon"). Decide whether the Λ-potential of Theorem R\* survives.
3. Assuming HJ-canon, combine memoized canonical forms (Theorem E, Theorem L, prefix DP) with HJ's
   recursion into a hybrid. State the strongest theorem and the residual hard case.
4. Check novelty.

**Labels.**
* **[PROVEN]**: a complete argument is given here. It uses only cited published results and the
  standard polynomial-time permutation-group toolkit.
* **[PROVEN mod X]**: complete, except that X is used without re-proof.
* **[SKETCH]**: an argument is given; the gaps are named.
* **[CONDITIONAL: H]**: holds under hypothesis H.
* **[SPECULATION]**: opinion or conjecture.

(H0) is the standing assumption "HJ (arXiv:2611.01399v1) is correct as written".

**Abbreviations.**
* "HJ L…" is a line of `scratchpad/paper/graph_isomorphism.tex`.
* **BC** is Babai, *Canonical form for graphs in quasipolynomial time: preliminary report*, STOC 2019,
  pp. 1237–1246. "BC §n" is a section of it.
* VR = `verify-theorem-R.md`, RT = `redteam-theorem-R.md`, FPT = `w1-fpt.md`,
  RT-FPT = `redteam-w1-fpt.md`, STR = `w1-structure.md`, RT-STR = `redteam-w1-structure.md`,
  W2 = `w2-coset.md` (on master, commit faf0999).
* **S-W** is Schweitzer–Wiebking, arXiv:1806.07466 (STOC 2019).
* **Wie20** is Wiebking, *Graph isomorphism in quasipolynomial time parameterized by treewidth*,
  arXiv:1911.11257 (ICALP 2020).
* **BL83** is Babai–Luks, *Canonical labeling of graphs*, STOC 1983. It was not read; it is used
  only as BC describes it.

**Sources.** All are untrusted data, read only, each in its own new directory.
* BC: NSF public-access copy, `r4-sources/w3c-babai-canon/`. Read in full.
* Wie20: arXiv source, `r4-sources/w3c-wiebking-1911.11257/`. Read: introduction, open questions,
  Problem `CL:Obj`, Corollaries `canObj0` and `canObj`, Theorem `canSet`.
* S-W, already present: introduction, `canGenSets.tex` (Cor. `gammaD`), open questions.
* Neuen's 2026 survey and Grohe–Neuen 2011.01366, already present: searched for "canon".
* HJ LaTeX: L103–545, L545–1260, L1260–1300, L1350–1404, L2593–3300, L3530–3560, L4660–4700.
* Web searches (2026-11-05) for canonization of bounded-degree graphs in $n^{\mathrm{polylog}\,d}$.

**Executed.** One PDF-to-text conversion with the existing `r4-tools/pdf2txt.py`, run with
`python3 -I`. Nothing else: no Lean or lake, no solver, no benchmark.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | What did Babai's canonization need? | The Babai–Luks framework of canonical placement cosets (chain rule, descent by lexicographic leader, strongly canonical assignments) handles everything **except one step**. His local-certificate step built a relational structure on the ideal domain from *comparisons between $x$ and $y$*, so it was only "pairwise canonical". BC replaces it by a $2t$-ary relation built from each test set's non-fullness group $M(T,x)$. That relation is trivial on "asymmetric" test sets, so BC also needs a canonical choice of a point in each such set (BC §§11–16). **That repair uses the logarithmic certificate size $t\ge\max\{9,2\log_2n\}$ twice**: through Jordan–Liebeck (BC Cor. 13.3, Lemma 15.1) and in BC Prop. 14.2. | lit. (§1) |
| 2 | Which HJ components hit those obstacles? | In the $\hat\Gamma_d$ regime ($d\le N^\alpha$), **only HJ's ordered comparisons**, whose classes become tuple colours "with the same palette for both inputs" (HJ L2768–2773). That is exactly Babai's pairwise construction. Babai's repair does **not** transfer, because HJ's certificate size $\kappa$ is constant. The extra-orbit/σ rule, the inherited hierarchy and caps, LiftAndContinue overcosets, aggregation and the exact configuration step all have direct canonical versions. The genuinely hard components are the **first-rectangle row carrier, the row normal form and the row terminal**. They make choices that are neither invariant nor determined by the input, and **none of them runs when $d\le N^\alpha$**. | **[SKETCH]** (§1.3) |
| 3 | HJ-canon | Replace every comparison by a **canonical endpoint colour**: the canonical form of the marked window $x^{W(x,T)}$ under the pointwise stabiliser of a fixed reference tuple, reached by right descent. The colour classes are exactly HJ's comparison classes, the no-large-twin argument survives, and the cost drops from $q^{2\kappa}$ comparisons to $q^\kappa$ canonical chains. Every other component in the regime has a canonical version that keeps the same right subgroups, domains and branch counts. | key lemmas **[PROVEN]**; assembly **[SKETCH]** (§2) |
| 4 | Conditional bound | **Theorem C.** Canonical forms (and canonical placement cosets) for strings under $\hat\Gamma_d$-groups in $\exp(O(\log N\log d))\cdot Q(d^{O(1)})$, i.e. $\exp(O(\log N\log d+\log^cd))$, where $Q$ is Babai's quasipolynomial canonizer. It is used only at leaves where R\* itself switches to HJ verbatim. **The Λ-potential survives verbatim**: canonization adds no multiplicative factor inside the regime. For graphs of maximum degree $d$ this gives canonical forms in $n^{O(\log d)}\exp(\mathrm{polylog}\,d)$. | **[CONDITIONAL: (H0), BC, BL83; SKETCH]** (§2.4) |
| 5 | Does the premise hold? | **Only partly.** Prop. 4.1, Theorem E, the ADKT prefix DP and W2's Theorem P are *isomorphism-native*. They combine with isomorphism-only HJ in a frontier hybrid with no canonization at all, at the price of block *pairs*. Canonization is needed for canonical output, for one memo per block instead of per pair, and for combines that feed sub-results as labelling-coset atoms into an S-W/Wiebking canonizer (Theorem L with a frontier, Theorem P-canon). **The obstruction to finer integration inside HJ's giant step is alignment, not isomorphism versus canonization.** | **[PROVEN]** given R\* (§3.1, §3.7) |
| 6 | New canonical tools | **Lemma N:** canonical forms descend from $R$ to any normal (or subnormal) $M\trianglelefteq R$ in polynomial time. It is the canonical analogue of "intersection with a normal subgroup". **Theorem E-canon:** canonical forms in $\sum_B\lvert P_B\rvert\,\delta_B\cdot\mathrm{poly}(N)$ with $\delta_B\le\varepsilon_B$, which is the same as Theorem E. Abelian entanglement is free. **Theorem P-canon:** canonical forms for *any* $G\le\mathrm{Sym}(\Delta)\wr S_k$ in product action in $2^{\mathrm{polylog}\,b}N^{1.59+o(1)}$, mod Wiebking's canonizer for objects on a small ground set. | E-canon, N **[PROVEN mod Babai–Luks framework]**; P-canon **[SKETCH mod Wie20]** (§3.2–3.4) |
| 7 | Hybrid theorem | **Theorem H.** Time $\mathrm{poly}(N)\cdot\min_{\mathcal F}\bigl[\sum_{B\in\mathcal F}\mathrm{HJC}(\lvert B\rvert)+\sum_{B\text{ above }\mathcal F}\kappa(B)\bigr]$. The minimum runs over invariant frontiers of the block tree; $\kappa(B)$ is the cheapest local combine (E-canon, wreath/P-canon, Theorem L). **Corollary H′:** $f(d)\cdot\mathrm{poly}(N)\cdot\exp(O(\log s_{\rm bad}\log d))$, where $s_{\rm bad}$ is the largest block with no cheap combine. This covers iterated wreath products, bounded-entanglement and abelian-entanglement towers, product actions with any top group (including HJ's own barrier family), synchronised towers, and mixtures. It is never worse than R\*. | **[CONDITIONAL: Thm C]**; isomorphism version **[CONDITIONAL: (H0)]** (§3.6) |
| 8 | Residual hard case | Blocks with **unbounded non-abelian entanglement (unbounded coupling depth)** that are not level-synchronised. In isomorphism mode this is **exactly W2's core TreeCI$(b)$**: its complete instance, PCI with a full diagonal over two deep children, is the prototypical bad node. In canonical mode the residual is the canonical version TreeCan$(b)$, which contains TreeCI. Whether the two are fpt-equivalent is open. | **[PROVEN]** / open (§3.8) |
| 9 | Novelty | $n^{\mathrm{polylog}\,d}$ canonization of degree-$d$ graphs is **stated as open** by S-W (2019: GNS canonization "remains as future work") and by Wie20 (2020: "no adequate canonization version is known"). I found no later result. Theorem C (conditional) is new. HJ-canon is trivially unpublished, since HJ is four days old. Lemma N and E-canon are elementary and were not found stated. P-canon was not found. | lit. (§4) |

**Verdict.**
* *HJ-canon in the $\hat\Gamma_d$ regime.* Making HJ canonical is easier than it was for Babai.
  HJ's constant-size tests make right descent to an ordered test tuple cost only $q^\kappa$. That
  turns the pairwise comparison classes into canonical colours directly, so Babai's
  asymmetric-test-set machinery, which needs $t=\Theta(\log n)$, is not needed. The potential
  argument is untouched. What resists canonization is HJ's row machinery for wide natural giants
  ($q>N^\alpha$), which never runs for $\hat\Gamma_d$ with $d\le N^\alpha$.
* *The hybrid.* It achieves additive per-block costs and an $f(d)\,\mathrm{poly}(N)$ bound on every
  family the campaign knows to be FPT, inside one algorithm, with R\* as fallback.
* *What is left.* Exactly the coupled tree core, in canonical form. Canonization does not make the
  core easier, and the isomorphism-to-canonization gap reappears precisely there.

---

## 1. What Babai needed, and what it means for HJ

### 1.1 The framework (BC §5, §8, §9.2): what works without change

BC follows BL83.

* **Canonical placement.** $\mathrm{CP}^W_C(x)\subseteq C$ is defined for a subcoset $C=\sigma H$ and
  an $H$-invariant window $W$. Def. 5.1 imposes two rules:
  * (i) $\mathrm{CP}^W_{\sigma C}(x)=\sigma\,\mathrm{CP}^W_C(x^\sigma)$;
  * (ii) $\mathrm{CP}^W_C(x)=\tau\,\mathrm{Aut}_H(x^\tau)$ for every $\tau$ in it.

  The canonical form is $F(x)=x^{\mathrm{CP}}$ (Prop. 5.3).
* **Chain Rule** (§5.2, Rem. 5.5). Process an ordered partition into subwindows. Each subwindow
  need only be invariant under the *current* right subgroup. The window order is fixed by size,
  ties broken lexicographically (§5.3).
* **Descent** (§5.4, Prop. 5.7). Split $C$ into cosets of a subgroup, canonize each, keep the
  lexicographic leader, and take the subcoset generated by the minimizing branches.
* **Strongly canonical assignments** (§8, Obs. 8.4). Canonizing $(x,\mathfrak X(x))$ for an
  equivariant $\mathfrak X$ canonizes $x$.
* **Individualization and canonical refinement** "work for CP without change" (§9.2). So the Design
  Lemma, the aggregation of certificates and Split-or-Johnson carry over (§9.1–9.2).
* **Right descent** (end of §16). $G=\bigsqcup_\sigma G_T\sigma$, with recursive calls
  $\mathrm{CP}_{(G_T)^\sigma}(x^\sigma)$. Unlike left descent, it keeps
  $\mathrm{Aut}_{(G_T)^\sigma}(x^\sigma)=\mathrm{Aut}_{G_T}(x)^\sigma$.

**Principle P (what may be chosen freely).** By rule (i), the coset case reduces to the group case
via $\mathrm{CP}_{\sigma H}(x)=\sigma\,\mathrm{CP}_H(x^\sigma)$. This is well defined iff
$\mathrm{CP}_H(z^h)=h^{-1}\mathrm{CP}_H(z)$ for all $h\in H$. An algorithm satisfies this if every
choice it makes is of one of two kinds:
* (P1) a function of the right subgroup $H$ and of $H$-invariant inherited data; or
* (P2) a function of the input that is $H$-equivariant ("strongly canonical").

A choice of a third kind breaks canonicity unless it is enumerated by descent:
* (P3) an auxiliary object that depends on neither, is not invariant under $H$, and is picked
  "arbitrarily" (a carrier subgroup, a coordinate system, a selected subset).

Isomorphism algorithms may make (P3) choices freely, because their output, a set of isomorphisms,
does not depend on them. **[standard (BL83, BC §5); used here as the checklist]**

### 1.2 The one obstacle Babai actually had to solve (BC §§9–16)

1. **Pairwise canonicity.** [Ba15+] turned local certificates into a $t$-ary relational structure on
   the ideal domain $\Gamma$. It did so by comparing certificates of $x$ with those of $y$ and naming
   the classes jointly (BC §1, §2, §9.1). That suffices for isomorphism but not for canonical forms.
2. **BC Theorem 12.1.** BC uses $R(x)\subseteq\Gamma^{2t}$, the tuples
   $(x_1..x_t,x_1^\tau..x_t^\tau)$ with $\tau\in M(T,x)$, where $M(T,x)$ is the non-fullness group.
   It is strongly canonical (Lemma 10.1). But $\mathrm{Aut}(T,R(x)_T)=N_{\mathrm{Sym}(T)}(M(T,x))$
   (Prop. 12.2), so $R(x)$ is trivial on the asymmetric test sets, those with $M(T,x)=1$
   (Cor. 12.3).
3. **Claim 12.4.** BC selects a point $u(T)\in T$ canonically, by canonizing
   $x(T,u)=x^{W(T,x)}*\chi_{\Delta(T)}*\chi_{\Omega(T,u)}$. This needs:
   * Prop. 14.2: the affected set $\Delta(T)$ determines $T$. It needs $G$ transitive,
     $t\ge\max\{9,2\log_2n\}$, $m>2t$ and $\Delta(T)\ne\Omega$.
   * The **large-window reduction** of §11: individualize $T$ when $\lvert W(T,x)\rvert\ge n/10$, at
     cost $\binom mt$.
   * Lemma 15.1: Jordan–Liebeck sets $S(x)$ on the penultimate window. These come from Cor. 13.3,
     which needs $t\ge\max\{9,2\log_2n\}$.
   * §16: a CP version of the local-certificates loop (descent to the kernel $K_i$, then the Chain
     Rule, which is efficient by the Affected Orbit Lemma), followed by right descent $G\to G_T$.
4. **Cost.** The extra factors are $\binom mt\le n^{O(\log n)}$ (large window, right descent). They
   fit the quasipolynomial budget. BC states no explicit exponent.

### 1.3 Which HJ components hit these obstacles

Column "regime": does the component run for $\hat\Gamma_d$ with $d\le N^\alpha$ (VR §8 step 1)?

| # | HJ component | regime | obstacle | canonical status |
|---|---|---|---|---|
| 1 | joint colour compression (L572–578) | yes | joint naming | rank $x$'s own colour records; invert at the end. Trivial. |
| 2 | orbit chain, largest orbit first (L604–627) | yes | window order | BC §5.3 recipe (size, then lexicographic); (P1) |
| 3 | inherited hierarchy, caps, origin labels, $h$ (L629–663, L1109–1135) | yes | none | the hierarchy is $G$-invariant and chosen as a function of the group (P1); caps are analysis-only |
| 4 | enumeration, product refinement, normalization (L1153–1158, L3060–3087) | yes | none | descent. Product coordinates come from the socle. VR §2.2's Johnson identification is built from orbitals, so it is invariant (P1). |
| 5 | constant-size endpoint with the extra-orbit/σ rule (L774–803, L2619–2721) | yes | BC Lemma 10.1 | HJ's prefix-recovery identity (L2653–2668, L2756–2762) makes $(T,W(x,T),A_{\rm fin})$ strongly canonical (P2). Window increments are equivariant unions of orbits. **No obstacle.** |
| 6 | **ordered comparisons → tuple colours** (L806–811, L2723–2788; "Use the same palette for both inputs", L2772–2773) | yes | **exactly BC §1.2 item 1** | BC's repair is **unavailable**: Cor. 13.3/Lemma 15.1 and Prop. 14.2 need $t\ge2\log_2n$, and HJ has $\kappa=64$. New repair in §2.2. |
| 7 | aggregation Case 2b: source tuple, target images, orbital (L2795–2815) | yes | pairwise branching | descent over the equivariant family of tuples and orbitals of $x$ alone, with the same count $q^{d-1}\cdot q^2$ (Lemma 2.5) |
| 8 | Case 2a large symmetry: alignment of dominant orbits (L2885–2895) | yes | pairwise alignment | canonical target $\Phi_0$ (P1) plus a parity rule. All $K$-cosets give one canonical form (Lemma 2.6). |
| 9 | Case 1 and balanced partitions: "align the two coloured partitions" (L2984–3027) | yes | pairwise alignment | canonical subcoset of a strongly canonical structure (Lemma 2.4) |
| 10 | Design Lemma, canonical coherent refinement (L2772–2788, L2817–2853) | yes | none | BC §9.2 |
| 11 | AuxiliaryReduction for $q\le\lambda$: fresh call on $C^2$ under $\mathrm{Sym}(C)$ (L1043–1047, L3103–3175) | yes | needs a canonizer for the fresh call | the call has class $\lvert C\rvert>N'^\alpha$, i.e. HJ's verbatim regime, so use BC (§2.4) |
| 12 | LiftAndContinue overcosets with extra relabelings (L1077–1082, L3194–3215) | yes | none | canonical subcoset step (Lemma 2.4). The extra relabelings are harmless. |
| 13 | CombineExact (L1085–1090) | yes | none | lexicographic leader over an equivariant branch family (Lemma 2.5) |
| 14 | first rectangle (L857–918, L1048–1062) | **no** ($q>\lambda$) | partly | Source individualization is descent; the pair-representation orbit $\Delta$ is invariant. **But the row carrier** "couples … with the same permutations of $q$ selected rows" (L1001; Lemma diagonal-carrier, L4672): a (P3) choice. |
| 15 | row normal form, RowStep, column floors (L1260–1300, L3530–3560) | **no** | yes | the clean row coordinates are a (P3) choice; enumerating them is far too expensive |
| 16 | row terminal (Thm transitive-gat-terminal, L4025–4180) | **no** | yes | "one common residual choice across the rows, … parity" (L1293–1296) is assembled from isomorphism tables. A canonical version needs a canonical multicoset assembly. Wie20's `canSet` would give only quasipolynomial time. |

**[SKETCH]** for the table as a whole. Rows 6, 14, 15 and 16 are the substantive ones.

**Observation.** HJ's row normal form theorem (L3530–3545) is itself an entanglement theorem. The
kernel $K\le H^m$ has abelian entanglement $M/M^*=\{\sum a_i=0\}$ and diagonal coupling
$K/M\cong H/N$. So the row terminal is HJ's *solved* instance of diagonal coupling under a giant.
It works because the radical-free part of $H/N$ has bounded order (L3911–3999). This links to the
residual of §3.8 (lead 5).

---

## 2. HJ-canon

### 2.1 Scope

Fix a phase with $d\le N^\alpha$. By VR §8 step 1, $q\le d\le\lambda$, so `GiantStep` never takes
the $q>\lambda$ branch. Hence RowStep, row terminals, column floors and in-domain rectangles never
occur, and AuxiliaryReduction always makes the small-configuration call. The components are rows
1–13 of §1.3. Phases with $d>N^\alpha$ have $N<d^{1/\alpha}$; there VR runs HJ verbatim, and HJ-canon
calls a general canonizer instead (§2.4).

### 2.2 The one real change: canonical endpoint colours

**Setting.** $G_0$ is the frozen transitive parent, and $\varphi:G_0\twoheadrightarrow\mathrm{Alt}(\Gamma)$
with $q=\lvert\Gamma\rvert>q_0\ge4\kappa+2$. For an injective $\kappa$-tuple $\vec t$ with
underlying set $T$, HJ's endpoint gives the window $W(x,T)$ and
$A_{\rm fin}=\mathrm{Aut}_{P_T}(x^{W(x,T)})$ (endpoint identity, L2756–2762). Fix the reference
tuple $\vec t_0$ = the first $\kappa$ labels of $\Gamma$ in the fixed order, and put
$J_0=(G_0)_{(\vec t_0)}$. Both depend only on the group (P1).

**Lemma 2.1 (tuple right descent).** **[PROVEN]**
$G_0$ is transitive on injective $\kappa$-tuples. For a string $z$ and an injective tuple $\vec t$,
choose $\sigma\in G_0$ with $\vec t^{\,\sigma}=\vec t_0$, and put $c(z,\vec t):=\mathrm{CF}_{J_0}(z^\sigma)$.
Then:
* (a) $c$ is well defined;
* (b) $c(z^g,\vec t^{\,g})=c(z,\vec t)$ for $g\in G_0$;
* (c) $c(z,\vec t)=c(z',\vec t')$ iff some $g\in G_0$ has $z^g=z'$ and $\vec t^{\,g}=\vec t'$.

*Proof.*
* Transitivity holds because $\mathrm{Alt}(q)$ is $(q-2)$-transitive and $q\ge\kappa+2$.
* (a) If $\vec t^{\,\sigma}=\vec t^{\,\sigma'}=\vec t_0$, then $\sigma^{-1}\sigma'\in J_0$. So
  $z^{\sigma'}=(z^\sigma)^{j}$ with $j\in J_0$, which has the same $J_0$-canonical form.
* (b) $g^{-1}\sigma$ sends $\vec t^{\,g}$ to $\vec t_0$, and $(z^g)^{g^{-1}\sigma}=z^\sigma$.
* (c) "If" follows from (b). "Only if": equal forms give $z^{\sigma j}=z'^{\sigma'}$ for some
  $j\in J_0$. Put $g=\sigma j\sigma'^{-1}$. Then $z^g=z'$ and
  $\vec t^{\,g}=\vec t_0^{\,j\sigma'^{-1}}=\vec t'$. ∎

**Definition.** Give the complement of the window a fresh marker, as in HJ. Then
$$c_x(\vec t):=\bigl(\text{verdict},\ c(x^{W(x,T)},\vec t)\bigr),$$
and every non-injective tuple gets its equality-pattern colour, as in HJ L2769–2772.

**Lemma 2.2 (exactness).** **[PROVEN, given HJ's endpoint equivariance and endpoint identity]**
1. $x\mapsto c_x$ is strongly canonical: $c_{x^g}(\vec t^{\,g})=c_x(\vec t)$.
2. On $\Gamma^\kappa(x)\sqcup\Gamma^\kappa(y)$, the partition by $c$-values *equals* the partition
   into HJ's comparison classes, eq. (comparison) (L2729–2735).
3. No large twins: if all orderings of a nonfull $T$ have the same colour, then
   $\varphi_T(A_{\rm fin})\ge\mathrm{Alt}(T)$, a contradiction. So every twin class has fewer than
   $\kappa$ points. This is HJ's argument at L2777–2781, verbatim.

*Proof.*
1. $W(x^g,T^g)=W(x,T)^g$ (HJ's equivariance), then Lemma 2.1(b).
2. HJ's comparison is nonempty iff some $g\in G_0$ with $\vec t^{\,g}=\vec t'$ maps
   $x^{W(x,T)}$ to $y^{W(y,T')}$ (the full ordered-tuple transporter, L2733). This is Lemma 2.1(c).
3. By Lemma 2.1(c), equal colours for $\vec t$ and $\vec t^{\,\pi}$ give $g\in(G_0)_T$ preserving
   $x^{W(x,T)}$ and inducing $\pi$. For even $\pi$, $g\in P_T$, so
   $g\in\mathrm{Aut}_{P_T}(x^{W(x,T)})=A_{\rm fin}$. ∎

So the Design Lemma receives the *same* tuple structure as in HJ, now with canonical colour names.
Canonical coherent refinement keeps the names canonical (rename by sorting). Everything downstream
inherits canonicity.

**Computing $c_x(\vec t)$.** **[SKETCH; the template is BC §16]**
* Run HJ's endpoint for $(x^\sigma,T_0)$.
* In lockstep, run the chain-rule canonical placement under $J_0$ over its window increments $V_i$.
  By the endpoint identity, the right subgroup after window $W_i$ is
  $\mathrm{Aut}_{J_0}((x^\sigma)^{W_i})=A_i\cap J_0=N_i$, exactly HJ's comparison group (L2737–2741).
* The Chain Rule on the $N_i$-orbits of $V_i$ makes exactly HJ's two call types:
  * affected orbits, whose $N_i$-orbits have size $\le\lvert\Delta\rvert/\kappa$ (L2683–2690);
  * extra orbits, on which $N_i$ is transitive and σ drops by $\kappa$ (L2694–2708).
* The windows of one chain are disjoint. So the calls form (H2)-families indexed by
  (tuple, type): at most $2q^\kappa$ families, against HJ's $4q^{2\kappa}$ comparison families.

*Gap:* I did not re-derive BC's left/right conventions for chain-rule windows that are invariant
only under the current right subgroup (BC Rem. 5.5). §16 of BC uses the same construction for
local-certificate windows.

**Remark 2.3 (Babai's own setting).** **[SKETCH]**
* Lemma 2.1 with $t$-tuples, combined with BC §16's CP computation of window strings under
  $G_{(T)}$, gives in BC's setting a strongly canonical coloured $t$-ary structure whose
  symmetricity is $\le t-1$, by the argument of Lemma 2.2(3). The cost is
  $m^t\cdot t!=n^{O(\log n)}$ right descents.
* This seems to make BC's asymmetric-test-set route (Claim 12.4, Prop. 14.2, Lemma 15.1, §11)
  unnecessary.
* I checked only the preliminary report. BC remarks that the conceptual issues "may be obscured by
  the simplicity of the solution", so treat this as unverified.

### 2.3 The other components

**Lemma 2.4 (canonical subcoset; LiftAndContinue).** **[PROVEN mod BC's framework]**
* *Setting.* Let $\mathfrak S$ be a strongly canonical structure on $\Gamma$, i.e.
  $\mathfrak S(x^g)=\mathfrak S(x)^{\varphi(g)}$. It may be a labelling coset, such as a projected
  rectangle answer. Let $\mathfrak S\mapsto\mathfrak S_{\rm can}$ be a canonical form for such
  structures under $\mathrm{Alt}(\Gamma)$.
* *Parity rule.* Take the $\mathrm{Sym}(\Gamma)$-canonical form $\mathfrak S_0$. If $\mathfrak S$
  lies in the $\mathrm{Alt}$-orbit of $\mathfrak S_0$, put $\mathfrak S_{\rm can}=\mathfrak S_0$;
  otherwise $\mathfrak S_{\rm can}=\mathfrak S_0^{(1\,2)}$. This is a function of the
  $\mathrm{Alt}$-orbit.
* *Claim.* Put $E_C(x)=\{g\in C:\mathfrak S(x)^{\varphi(g)}=\mathfrak S_{\rm can}\}$ and
  $\mathrm{CP}_C(x):=\mathrm{CP}_{E_C(x)}(x)$. Then $\mathrm{CP}_C$ satisfies Def. 5.1. The right
  subgroup of $E_C(x)$ is the preimage of $\mathrm{Aut}(\mathfrak S_{\rm can})\cap\mathrm{Alt}(\Gamma)$,
  i.e. HJ's overcoset group.

*Proof.*
* *Rule (i).* $E_{\sigma C}(x)=\sigma E_C(x^\sigma)$, so
  $\mathrm{CP}_{\sigma C}(x)=\mathrm{CP}_{\sigma E_C(x^\sigma)}(x)=\sigma\,\mathrm{CP}_{E_C(x^\sigma)}(x^\sigma)$.
* *Rule (ii).* An $h\in\mathrm{Aut}_H(x^\tau)$ with $\tau\in E_C(x)$ fixes
  $\mathfrak S(x^\tau)=\mathfrak S_{\rm can}$, so it lies in the right subgroup of $E_C(x)$.
* *Same group as HJ.* The overcoset group equals HJ's, so the cap bound $\beta q$ and the continuation
  domain are HJ's. Lifting through $\varphi$ uses the same operations as HJ (kernel plus lifts of
  generators, L3123–3130). ∎

**Lemma 2.5 (combining branches).** **[PROVEN]**
* *Setting.* $\mathcal B(x)$ is an equivariant branch family: $\mathcal B(x^g)=\mathcal B(x)^g$.
  $F(x,b)$ is a canonical form of the pair $(x,b)$.
* *Claim.* $F(x):=\min_{b\in\mathcal B(x)}F(x,b)$ is a canonical form, and
  $\mathrm{CP}(x)=\bigcup_{b\text{ minimizing}}\mathrm{CP}(x,b)$, a coset.

*Proof.*
* Invariance: the multiset of values is invariant.
* Union: let $g\in\mathrm{Iso}(x,x')$, where $F(x)=(x',b')$. Then $b'\in\mathcal B(x')$, so
  $b'':=b'^{\,g^{-1}}\in\mathcal B(x)$ and $(x,b'')^g=(x',b')$. Hence $b''$ minimizes. ∎

This covers CombineExact, Case 2b's anchors and orbitals, and the Design Lemma's
individualizations. The counts are HJ's.

**Lemma 2.6 (large symmetry, Case 2a).** **[SKETCH]**
* After canonical alignment of $\Phi$ (Lemma 2.4), $\mathrm{Aut}_{H_0}(x')$ maps onto $H_0/K$
  (L2916–2945).
* Hence the $K$-cosets of $\tau H_0$ all yield the same $K$-canonical form. For $r,r'\in H_0$ pick
  $a\in\mathrm{Aut}_{H_0}(x')\cap rr'^{-1}K$; then $(x'^{r})^{r^{-1}ar'}=x'^{r'}$ with
  $r^{-1}ar'\in K$.
* So one CP under $K$ suffices: an orbit chain on half-size domains, plus the at most two parity
  twists and the lifts $a_1,a_2$. This is HJ's cost.

**The rest** (rows 1–4 and 10 of §1.3) follow from (P1)/(P2) and BC §5, §9.2.

### 2.4 Theorem C and the potential

**Theorem C (HJ-canon for $\hat\Gamma_d$).**
**[CONDITIONAL: (H0); BC's quasipolynomial canonization; BL83 for the graph corollary. SKETCH: the
component-wise canonization of §2.2–2.3]**

Let $G\le\mathrm{Sym}(\Omega)$ with $G\in\hat\Gamma_d$ and $\lvert\Omega\rvert=N$, given by generators,
and let $C\subseteq G$ be a subcoset. HJ-canon with dispatcher (M′) computes $\mathrm{CP}_C(x)$,
hence a $G$-canonical form of strings together with $\mathrm{Aut}_G(x)$, in time
$$\exp\bigl(O(\log(N+2)\log(d+2))\bigr)\cdot Q\bigl(d^{O(1)}\bigr)\cdot\mathrm{poly}(\text{input}).$$
Here $Q(n)$ is the time of a general canonical-placement algorithm on $n$ positions. With BC,
$Q(n)=\exp(O(\log^cn))$, which gives $\exp(O(\log N\log d+\log^cd))$.

**Corollary C′.** **[same conditions]** Graphs of maximum degree $d$ have canonical forms computable
in $n^{O(\log(d+2))}\cdot\exp(O(\log^c(d+2)))$. Luks's reduction to $\hat\Gamma_{d-1}$-string
problems has a canonical version (BL83, as described in BC §5.6), and CP handles cosets.

*Proof sketch.*

**Correctness.** Every step is a chain-rule step, a descent, or one of Lemmas 2.1–2.6, or it obeys
(P1)/(P2). Induct over the recursion as in BC Props. 5.6–5.7.

**Running time. The Λ-potential survives verbatim.**
* The recursion tree of HJ-canon has the same nodes as HJ+(M′), with the same right subgroups,
  domains and inherited states $(s,\rho,\sigma,Q_d,h)$. Only the comparison chains change, and they
  are fewer.
* Every class has at most HJ's branch count:
  * endpoint and canonical-chain families: $\le q^{O(\kappa)}$;
  * product refinement: $2^k\tilde d^{\,k-1}$;
  * enumeration: $\lvert P\rvert$;
  * continuations: $\le2q^{\kappa+1}$.

  Each family is disjoint in the sense of `branch_disjoint`. So VR §4 and RT §1.3's table, with
  $\Phi_\Lambda$ and $\Lambda=\log(8\tilde d)$, apply unchanged.
* The only new tolls are canonical fresh calls:
  * configurations on $\le d^2$ positions;
  * phases with $d>N^{\alpha}$, i.e. $N<d^{1/\alpha}$.

  These sit inside $K_N$:
  $$F(N)\le e^{C\Lambda\log N}\bigl(1+F(N^\gamma)+Q(d^2)\bigr)\quad(N^\alpha\ge d),\qquad F(N)\le Q(d^{1/\alpha})\quad(N^\alpha<d).$$
  Unrolling gives $F(N)\le\exp(O(\Lambda\log N))\cdot Q(d^{1/\alpha})\cdot O(\log\log N)$. ∎

**Does canonization cost an extra multiplicative factor here?** Inside the regime it does not. In BC,
the extra factors were $\binom mt$ (large window and right descent), which is $n^{\Theta(\log n)}$ but
within budget. Here the analogue is right descent to an ordered $\kappa$-tuple, costing $q^\kappa$. HJ
already pays $q^{O(\kappa)}$ for its endpoints. The only real extra is the factor $Q(d^{O(1)})$ at the
leaves where R\* itself drops to HJ verbatim. It is a function of $d$ alone, so it is harmless for
any FPT-type statement, and it is $\le\exp(O(\log N\log d))$ whenever
$\log^{c-1}d\le\log N$.

**What is not obtained.** If the row machinery (rows 14–16 of §1.3) were canonized at HJ's cost,
one would get $Q(n)=\exp(O(\log^2n))$, hence exactly $\exp(O(\log N\log d))$, and canonical forms for
all graphs in $n^{O(\log n)}$. Rows 14–15 are (P3) choices. Enumerating carriers costs
$\binom mq q!$ with $m,q>N^\alpha$, and I see no invariant replacement. **[SPECULATION]**: a canonical
row terminal via Wie20's `canSet` gives only quasipolynomial time.

---

## 3. Plugging in the FPT methods

### 3.1 Which methods actually need canonical forms

| method | native output | integrates with isomorphism-only HJ? |
|---|---|---|
| block-pair DP (FPT Prop. 4.1) | isomorphism sets of block pairs | yes |
| Theorem E (FPT §4.3), sharpened in RT-FPT §3.2–3.4 | PCI by bounded-index steps | yes |
| prefix DP + ADKT (FPT Prop. 3.3) | isomorphism | yes |
| Theorem P, Theorem E′ (W2 §3) | isomorphism, CI on the small domain $V$ | yes |
| Theorem L (STR §4.6, RT-STR §4) | S-W canonization of one global orbit-object over a small $U$ | yes, if run to the leaves: pairwise-canonical leaf colours decide $x\cong y$. **No**, with a frontier below which the synchronised part $S$ still acts: the leaf data must then be $S$-equivariant objects, i.e. canonical labelling cosets. |
| S-W / Wie20 combines with labelling-coset atoms (P-canon, §3.4) | canonical labellings | no: they need canonical sub-results |

**Proposition 3.1 (isomorphism frontier hybrid).** **[PROVEN, given R\*, i.e. given (H0)]**
* *Setting.* $\mathcal T$ is any $G$-invariant nested block hierarchy with $G_C\le G_B$ for every
  child $C$ of $B$. $\mathcal F$ is a $G$-invariant set of disjoint blocks covering $\Omega$.
* *Claim.* $\mathrm{Iso}_G(x,y)$ is computable with:
  * $O(N^2)$ calls of HJ+(M′) on frontier blocks $C$ under $H_C=G_C|_C\in\hat\Gamma_d$;
  * Theorem E's combine at every block above $\mathcal F$;
  * polynomial bookkeeping.

*Proof.*
* Prop. 4.1's DP needs only the tables $\mathrm{Iso}(C,C')$ for frontier blocks, plus the $x\to x$
  tables of RT-FPT §2.2.
* $\mathrm{Iso}(C,C')=\mathrm{Iso}_{H_C}(x|_C,(y|_{C'})^{g_0^{-1}})\,g_0|_C$ for any transporter
  $g_0\in G$ with $C^{g_0}=C'$. That is one R\* call each.
* Above $\mathcal F$, use Theorem E as stated (RT-FPT §8 item 3). ∎

**What canonization adds:**
* (a) canonical output;
* (b) one memo entry per block ($\le2N$) instead of per pair ($O(N^2)$);
* (c) combines in which sub-results enter an S-W/Wie20 canonizer as labelling-coset atoms;
* (d) **nothing** for the alignment problem of §3.7.

### 3.2 Lemma N: canonical forms descend to normal subgroups

**Lemma N.** **[PROVEN mod BC's framework (Def. 5.1)]**
* *Setting.* $M\trianglelefteq R\le\mathrm{Sym}(\Delta)$. For a string $z$ we are given:
  * $F=\mathrm{CF}_R(z)$;
  * generators of $A=\mathrm{Aut}_R(F)$;
  * one $\tau\in\mathrm{CP}_R(z)$, so $z^\tau=F$.

  Put $r=\tau^{-1}$, and let $\ell$ be the lexicographically least element of the coset
  $(AM)r$.
* *Claim.*
  * $\mathrm{CF}_M(z):=F^{\ell}$ is an $M$-canonical form on the $R$-orbit of $z$.
  * $\mathrm{CP}_M(z)=(M\cap A^{r})\,m_0$, where $\ell r^{-1}=a_0m'$ with $a_0\in A$, $m'\in M$,
    and $m_0=r^{-1}m'r$.
  * Both are computable in polynomial time.
  * $\mathrm{CP}_{\sigma M}(z):=\sigma\,\mathrm{CP}_M(z^\sigma)$ for $\sigma\in R$ is consistent with
    Def. 5.1.

*Proof.*
* *Well defined.* $r$ is determined up to $A r$, so the coset $AMr$ is determined by $z$. Since
  $M\trianglelefteq R$, $AM$ is a group.
* *In the $M$-orbit.* Write $\ell=amr$. Then $F^\ell=F^{mr}=z^{r^{-1}mr}$, and $r^{-1}mr\in M$.
* *Invariant on $M$-orbits.* If $z'=z^{m}$, then $z'=F^{rm}$, so $r'\in A\,rm$. Since $M$ is
  normal, $AMr'=AMrm=AMr$. Also $\mathrm{CF}_R(z')=F$, and $\ell$ depends only on the set $AMr$.
* *The coset.* $\{g\in M:F^{rg}=F^\ell\}=M\cap r^{-1}A\ell$. Writing $\ell=a_0rm_0$ gives
  $r^{-1}A\ell=A^rm_0$.
* *Polynomial time.* $M\cap A^r$ is an intersection with a normal subgroup of $R$ (standard toolkit;
  RT-FPT §3.2). The factorization $\ell r^{-1}=a_0m'$ is constructive membership in $AM$. The least
  element of a coset is found by the standard point-by-point minimization along a stabilizer chain
  with base $1,2,\dots$.
* *Consistency.* For $m\in M$, $\mathrm{CP}_M(w^m)=m^{-1}\mathrm{CP}_M(w)$, so $\sigma M=\sigma mM$
  gives the same value. ∎

*Note.* Lexicographically least *elements of cosets* are easy. Lexicographically least *images of
strings* are not. The lemma uses only the former, and $F$ itself is canonical.

**Corollary N′ (subnormal chains).** If $M=M_s\trianglelefteq\cdots\trianglelefteq M_0=R$, apply
Lemma N $s$ times. At each step $\mathrm{Aut}_{M_{j+1}}(F_{j+1})=M_{j+1}\cap\mathrm{Aut}_{M_j}(F_j)^{\ell_j}$
is again an intersection with a normal subgroup. **[PROVEN]**

### 3.3 Theorem E-canon

**Block data**, as in FPT §4.1. For each block $B$ of $\mathcal T$, with children $C_1,\dots,C_r$ in
a fixed order (a function of $K_B$, so (P1) applies):
* $H_B$, $P_B$, $K_B$;
* $R_i=\pi_i(K_B)$, which is normal in $H_{C_i}$;
* $M_i=\pi_i(K_{B,\ge i})$, which is normal in $R_i$.

Put
$$\delta_B:=1+\sum_{i:\ R_i/M_i\text{ non-abelian}}\bigl(\lvert R_i:M_i\rvert-1\bigr)\ \le\ \prod_i\lvert R_i:M_i\rvert=\varepsilon_B.$$

**Theorem E-canon.** **[PROVEN mod BC's framework]** Canonical forms and CP cosets for strings under
$G$ are computable in time $\mathrm{poly}(N)\cdot\sum_B\lvert P_B\rvert\,\delta_B$. In particular:
* $\pi_0\,\varepsilon\,\mathrm{poly}(N)$, which is the same bound as Theorem E;
* $\pi_0\,\mathrm{poly}(N)$ when every $R_i/M_i$ is abelian.

*Proof.*
1. *Memo.* Bottom-up, store for each block $C$ the triple $(F_C,\mathrm{Aut},\tau_C)$ of
   $\mathrm{CP}_{H_C}(x|_C)$, in fixed reference coordinates for $C$'s $G$-orbit. Transport is well
   defined up to $H_C$, as in the canonical block-type argument.
2. *At $B$: descent* from $H_B$ to its $\lvert P_B\rvert$ cosets $hK_B$, with lexicographic leader
   (BC Prop. 5.7). By rule (i) each branch is $\mathrm{CP}_{K_B}(z_h)$ with $z_h=(x|_B)^h$.
3. *Chain over children* (BC Prop. 5.6). At step $i$ the current coset restricts to $C_i$ as
   $X_i\zeta_i$, with $M_i\le X_i\le R_i$, because $K_{B,\ge i}$ lies in the group part.
   * If $R_i/M_i$ is abelian, then $X_i\trianglelefteq R_i$. So
     $\mathrm{CP}_{\zeta_iX_i}(w)=\zeta_i\,\mathrm{CP}_{X_i}(w^{\zeta_i})$, and Corollary N′
     along $X_i\trianglelefteq R_i\trianglelefteq H_{C_i}$ reads it off the memo.
   * Otherwise, descend over the $\le\lvert X_i:M_i\rvert$ cosets $\zeta'M_i$. Each branch is
     $\zeta'\,\mathrm{CP}_{M_i}(w^{\zeta'})$, read off the memo by Corollary N′
     ($w^{\zeta'}$ lies in the $H_{C_i}$-orbit of the memoized child).
   * Keep the lexicographic leader and lift to the preimage in the current coset (restriction plus
     constructive membership, as in Theorem E step 3).
4. *Cost.* The cost at $B$ is $\lvert P_B\rvert\cdot\bigl(r+\sum_i(\lvert X_i:M_i\rvert-1)\bigr)\cdot\mathrm{poly}\le\lvert P_B\rvert\,\delta_B\,\mathrm{poly}$.
   There are $\le2N$ blocks. ∎

**Relation to FPT §4.5.** FPT noted that "canonize the children, then sort" fails for diagonal
kernels. E-canon locates the price exactly. For $K=\{(h,h)\}$ one has $M_1=R_1$ and $M_2=1$, so
step 3 descends over $\lvert X_2\rvert=\lvert\mathrm{Aut}(x_1)\rvert$ cosets. That is the
TreeCI-complete node of W2 Thm 2.1(c).

### 3.4 Theorem P-canon: product actions with any top group

**Setting.** As in W2 §3.1: $V=[k]\times\Delta$ with $\lvert\Delta\rvert=b$;
$G\le\mathrm{Sym}(\Delta)\wr S_k$ acts faithfully on $V$, and in product action on
$\Omega=\Delta^k$ with $N=b^k$.

**Theorem P-canon.** **[SKETCH: complete modulo Wie20 Cor. `canObj0` and S-W's object/labelling-coset
conventions, which I did not re-derive]** Canonical forms for strings under $G$ are computable in
time
$$(b+1)^k\cdot2^{\mathrm{polylog}(bk)}\ \le\ 2^{O(\log^cb)}\cdot N^{\log_2 3+o(1)}.$$

*Construction.*
* For $J\subseteq[k]$ and $u\in\Delta^J$, viewed as a point set in $V$, define the coset-labelled
  object
  $$\mathcal X_{J,u}=\Bigl(G\rho,\ u,\ \bigl\{\bigl((j,a),\ \mathrm{rk}(F_{J+j,u+(j,a)}),\ \Lambda_{J+j,u+(j,a)}\bigr):j\notin J,\ a\in\Delta\bigr\}\Bigr).$$
  Here $\Lambda$ is the child's canonical labelling coset of $V$ and $F$ its canonical form.
  $\mathrm{rk}$ is the rank among all canonical forms at that level; it is canonical because the set
  of forms at a level is an isomorphism invariant.
* The base case $J=[k]$ is $(G\rho,u,x(u))$.
* Process levels $\lvert J\rvert=k,k-1,\dots,0$. Canonize each object by Wie20 Cor. `canObj0`:
  time $2^{\mathrm{polylog}(\lvert V\rvert+t_{\max})}n^{O(1)}$, with $\lvert V\rvert=bk$,
  $t_{\max}\le bk$ and object size $n=\mathrm{poly}(bk)$.
* The atom $G\rho$ restricts isomorphisms to $G$.

*Correctness.* For $g\in G$:
$$g:\mathcal X_{J,u}(x)\to\mathcal X_{J',u'}(y)\iff u^g=u'\ \text{and}\ g\ \text{maps the link}\ x_{J,u}\ \text{to}\ y_{J',u'}.$$
* "$\Leftarrow$": $g$ maps child links to child links. By (CL1), equal forms and
  $\Lambda_y=g^{-1}\Lambda_x$ follow.
* "$\Rightarrow$": equal forms and $\Lambda_y=g^{-1}\Lambda_x$ mean that $g$ maps each child link of
  $x$ to the matching child link of $y$. Every $z\in\Delta^{[k]\setminus J}$ is covered by the child
  at $(j,z_j)$ for any $j\notin J$.
* At the root this gives a canonical labelling of $x$.

*Remarks.*
* The table has $\sum_J b^{\lvert J\rvert}=(1+b)^k$ entries.
* There is no branching over $\pi\in\mathrm{Sym}(\Delta)$ or over the top group. The canonizer on the
  small set $V$ absorbs both.
* It is the canonical twin of W2's Theorem P ($b!\cdot N^{3.17+o(1)}$ mod Babai's CI): Wie20's
  canonization of coset-labelled objects on $V$ replaces Babai's CI on $V$. The table is over single
  partial assignments rather than pairs, which is why the exponent halves.
* At a **full-wreath** node of the block tree ($H_B=H_C\wr P_B$) with coordinate-type $P_B$, use
  children's ranks as the colours $x(u)$. Twisted nodes ($H_C/R_C\ne1$) are not covered.

### 3.5 Theorem L with a canonical frontier

**[SKETCH]** Theorem L (RT-STR §4) builds $R$-invariant, $S$-equivariant orbit-objects bottom-up and
canonizes once under $S$ on $U$.
* If the tower is level-synchronised only above a frontier, replace the leaves $\ulcorner x(p)\urcorner$
  by $(\mathrm{rk}\,F_p,\Lambda_p)$. Here $\Lambda_p$ is the canonical labelling coset of the frontier
  block $p$, taken with respect to a domain on which $S$'s action below the frontier is faithful.
* Step 3 of Theorem L (equivariance) then holds by (CL1).
* *Gap:* making "$S$ below the frontier" act on a *small* ground set jointly with the frontier
  labelling cosets. If $S$ acts trivially below the frontier, leaf colours suffice and no
  canonization is needed.

### 3.6 Theorem H: the hybrid

**Definitions.**
* $\mathcal T$: the inherited hierarchy at the fresh call (maximal chains per orbit), or any
  $G$-invariant block tree with $G_C\le G_B$.
* $\mathcal F$: a $G$-invariant set of disjoint blocks covering $\Omega$. Singletons are allowed.
  "Above $\mathcal F$" means strictly containing a member.
* $\mathrm{HJC}(s)=\exp(O(\log(s+2)\log(d+2)))\cdot Q(d^{O(1)})$ (Theorem C).
* The local combine cost $\kappa(B)$ is the minimum of the applicable options:
  * **(E)** $\lvert P_B\rvert\,\delta_B$ (Theorem E-canon); always applicable;
  * **(W)** at a full-wreath node, $\mathrm{Can}_{P_B}(d_B)$: string canonization under $P_B$ on the
    $d_B$ children, coloured by child ranks. This is $\le d_B^{O(\log d)}Q(d^{O(1)})$ by Theorem C,
    or $2^{\mathrm{polylog}\,b}d_B^{1.59+o(1)}$ by P-canon when $P_B$ is of coordinate type with
    base $b$;
  * **(L)** for a maximal level-synchronised segment, Theorem L's cost (§3.5, **[SKETCH]**).

**Theorem H.** **[CONDITIONAL: Theorem C; options (W) with P-canon and (L) as labelled]** Canonical
forms, $\mathrm{Aut}_G(x)$ and $\mathrm{Iso}_G(x,y)$ are computable in time
$$\mathrm{poly}(N)\cdot\min_{\mathcal F}\Bigl[\ \sum_{B\in\mathcal F}\mathrm{HJC}(\lvert B\rvert)\ +\ \sum_{B\text{ above }\mathcal F}\kappa(B)\ \Bigr].$$
The algorithm chooses $\mathcal F$ itself, by a bottom-up DP over $\mathcal T$ on the explicit,
computable cost bounds:
* $\lvert P_B\rvert$ by Schreier–Sims;
* $\lvert R_i:M_i\rvert$ from group orders;
* the abelian test $[R_i,R_i]\le M_i$.

The **isomorphism version** needs no Theorem C and is **[CONDITIONAL: (H0)]** only. It is the same
bound with HJ+(M′) at frontier block *pairs* (Proposition 3.1), Theorem E in place of E-canon, and
W2's Theorem P/E′ for option (W).

*Proof.*
* Bottom-up: frontier blocks by HJ-canon on $(B,H_B)$, valid since $H_B\in\hat\Gamma_d$. Blocks
  above the frontier by their chosen combine, which reads only children's memo entries.
* Correctness follows from Theorem C and §§3.3–3.5.
* There are $\le2N$ blocks, each with polynomial bookkeeping. ∎

**Node by node.** Taking $\mathcal F=\{\Omega\text{'s orbits}\}$ gives R\* (canonical: Theorem C).
Taking $\mathcal F=$ singletons gives $\sum_B\kappa(B)$. The DP takes, at every block, the better of
"solve this subtree by HJ" and "combine the memoized children". **Costs at different blocks add.**

**Corollary H′.** **[same conditions]** Fix any $f$ and call $B$ *good* if $\kappa(B)\le f(d)$. Let
$s_{\rm bad}$ be the largest size of a block that is not good (0 if none). Then the time is
$$\mathrm{poly}(N)\cdot\Bigl(f(d)+\exp\bigl(O(\log(s_{\rm bad}+2)\log(d+2))\bigr)Q(d^{O(1)})\Bigr).$$
*Proof.* Take $\mathcal F$ = the maximal non-good blocks, plus singletons elsewhere. ∎

**Families solved in $f(d)\cdot\mathrm{poly}(N)$ by the one algorithm** (those with $s_{\rm bad}\le g(d)$):
1. towers with $\lvert P_B\rvert\le f(d)$ and $\varepsilon_B=1$. This includes iterated wreath
   products of primitive groups of degree $\le f(d)$, giants of degree $q\le d$ at aligned nodes
   ($\le d!$), and FPT's $\mathcal W_L$. **[PROVEN mod framework]**
2. towers with $\lvert P_B\rvert\le f(d)$ and bounded non-abelian entanglement, or arbitrary
   abelian entanglement. **[PROVEN mod framework]**
3. tree groups of degree $b$ with bounded coupling depth (W2 Cor. 2.3, $\varepsilon\le(b!)^{b^{s+1}}$).
   **[PROVEN mod framework]**
4. product-action primitive groups with **any** top group, as a root node via (W): HJ's barrier
   family $G_{d,m}$ (FPT Prop. 3.1) and $\mathrm{AGL}(r,2)^L$ in product action (STR Prop. 4.2), on
   which HJ+(M′) pays $N^{\Omega(\log d)}$. **[SKETCH mod Wie20]**; isomorphism version
   **[PROVEN mod Babai CI]** via W2's Theorem P.
5. level-synchronised towers such as $G_{r,L}$, given the tower data: Theorem L as one segment.
   **[PROVEN mod S-W]** when run to the leaves; with a frontier, **[SKETCH]**.
6. any tree-shaped mixture of 1–5 in which the "unstructured" parts are blocks of size $\le g(d)$,
   paid by HJ-canon at cost $\exp(O(\log g(d)\log d))$.

### 3.7 Inside HJ's recursion: memoization is limited by alignment, not by canonicity

**[SKETCH / analysis]**
* *What works.* At a node where HJ exposes a primitive quotient on blocks of $\mathcal T$, use
  chain-rule windows equal to whole child blocks rather than kernel orbits; BC Rem. 5.5 allows any
  invariant subwindows. Then:
  * the first child call of every descent branch is a memo hit ($R_i\trianglelefteq H_{C_i}$,
    Lemma N);
  * later calls cost $\lvert X_i:M_i\rvert$.

  This is exactly E-canon. At such nodes a giant of degree $q\le d$ can simply be enumerated ($\le d!$)
  instead of running `GiantStep`. So **memo-aware HJ-canon at aligned nodes is Theorem H.**
* *What does not work.*
  * Inside `GiantStep`, recursive calls go to $N_i$-orbits inside window increments $V_i$ (L2677–2690).
    $N_i\le J_T$ still permutes the children outside $T$, so these orbits merge or cut blocks of
    $\mathcal T$.
  * After orbit restrictions the active domain $\Omega'$ meets blocks in $C\cap\Omega'$.
  * A memo entry for a whole block under $H_C$ answers neither query: window restriction loses
    information, and the groups are not normal in $H_C$.
* *The point.* Exactly the same holds for the isomorphism pair-memo: intersecting with a non-normal
  subgroup is CI. So a node-by-node minimum *finer than the block tree*, inside HJ's giant machinery,
  is blocked by **alignment**. Canonization does not help with that. The "additive rather than
  multiplicative" branching is achieved precisely at aligned nodes, which is what Theorem H uses.

### 3.8 The residual hard case

* **Bad nodes.** In tree groups $\lvert P_B\rvert\le b!$. So $B$ is bad iff its non-abelian descent
  number $\delta_B$ is superpolynomial and no synchronised segment covers it. By W2 Cor. 2.3, bounded
  coupling depth makes every node good.
* **The prototype bad node.** PCI with kernel the full diagonal of two deep children, which W2
  Thm 2.1(c) shows is TreeCI$(b)$-complete. **[PROVEN, from W2]**
* **Isomorphism hybrid.** The residual is exactly W2's core TreeCI$(b)$, together with W2's §3.5
  residual (a coordinate-type node over an entangled kernel). **It coincides with the coupled tree
  core.**
* **Canonical hybrid.** The combine at a bad node is CanPCI.
  * Theorem E-canon gives TreeCan $\le\sum$ CanPCI.
  * A CanPCI instance is TreeCan on $\mathcal T_B$ under $K_B$.
  * So the canonical residual is TreeCan$(b)$, with TreeCI $\le$ TreeSI $\le$ TreeCan.
  * Whether TreeCan $\le_{\rm fpt}$ TreeCI is open; it is a special case of Can versus GI.
  * So an FPT algorithm for W2's core would plug into the isomorphism hybrid immediately, but not
    automatically into the canonical one.
* **What R\* contributes.** R\* is the fallback exactly on bad subtrees, at cost
  $s_{\rm bad}^{O(\log d)}$. Nothing better is known there.

---

## 4. Novelty

| source | what it says about canonization for degree $d$ / $\hat\Gamma_d$ | checked |
|---|---|---|
| BC (Babai, STOC 2019) | quasipolynomial canonization of all graphs; no degree parameter; no explicit exponent | full text |
| S-W (arXiv:1806.07466, STOC 2019) | intro: "For results building on [Babai's] algorithm [GNS], there are still no known canonization versions." Open questions: GNS "should then be amenable to canonization. However, this remains as future work." Cor. `gammaD`: $k^{O(\mathrm{cw})}n^{O(1)}$, i.e. $n^{O(d)}$ | source |
| Wie20 (arXiv:1911.11257, ICALP 2020) | intro: GNS, "for which no adequate canonization version is known"; open questions: "whether the bounded-degree isomorphism algorithm of [GNS] extends to canonization". Cor. `canObj`: $n^{\mathrm{polylog}\lvert V\rvert}$ for objects | source |
| Wiebking's dissertation (RWTH 2021) | unified canonization framework; abstract mentions no degree or polylog result | abstract (web) |
| Neuen 2026 survey §1 | generic: canonization "is possible for many of the algorithms discussed"; no degree-$d$ canonization stated | full text |
| Grohe–Neuen–Wiebking (minors, arXiv:2004.07671) | no canonization in abstract | abstract |
| Grohe–Neuen–Schweitzer–Wiebking (ICALP 2018, treewidth) | canonization in $2^{O(k^2\log k)}\mathrm{poly}(n)$ | search snippet |
| BL83 | canonical forms for bounded valence, $n^{O(d)}$ (as described in BC §5.6) | via BC |
| HJ | "Canonization is a separate task" (L189–191, L254–257); none provided | full |
| web searches (standard and extended, 2026-11-05) | no $n^{\mathrm{polylog}\,d}$ canonization of degree-$d$ graphs found | — |

**Status.**
* *Theorem C / C′.* Conditional on HJ. They would also settle, conditionally and with a better
  exponent, the canonization question that S-W and Wie20 leave open. The best unconditional
  canonization for degree $d$ I found is $\min\{n^{O(d)},\exp(\mathrm{polylog}\,n)\}$ (BL83, BC).
* *HJ-canon* is trivially unpublished, since HJ is four days old. Its one non-routine ingredient,
  Lemmas 2.1–2.2, is simple. Remark 2.3, that it may also simplify BC, is unverified.
* *Lemma N, Theorem E-canon.* Elementary and not found stated. Lemma N may be folklore among
  Babai–Luks users.
* *Theorem P-canon.* Not found. It is a direct use of Wie20, of the kind experts would expect.
* *Proposition 3.1 / Theorem H.* Routine compositions. Their value is the clean min-over-frontiers
  form and the alignment diagnosis.

---

## 5. Leads (ranked)

1. **Unconditional $n^{\mathrm{polylog}\,d}$ canonization**, the question S-W and Wie20 leave open.
   * GNS use Babai-type certificates of size $t=O(\log d)$ on almost $d$-ary sequences, after
     normalization.
   * Lemma 2.1–2.2's canonical endpoint colours need no relation between $t$ and $n$. Combined with
     BC's framework, they should canonize GNS's certificate step.
   * Still to check: GNS's other pairwise steps (aggregation, normalization, the domain blow-up of
     their Thm 4.6) against Principle P.
   * This looks like the most valuable concrete next step, and it is unconditional.
2. **TreeCan versus TreeCI.** If W2's core gets an FPT algorithm, does it canonize? Lemma N handles
   normal pieces; the diagonal node needs a canonical analogue of a CI algorithm.
3. **Prototype E-canon in `gi-practical`.** Use one memo per block with Lemma N, and measure
   $\delta_B$ (non-abelian part only) on Luks towers. This refines FPT lead 3. It is cheap, but was
   not run here because of the CPU rule.
4. **Theorem L with frontier (§3.5).** Find a small ground set on which the below-frontier $S$-action
   and the frontier labelling cosets coexist.
5. **HJ's row terminal as solved diagonal coupling.** It handles $K/M\cong$ diagonal $H/N$ using a
   bounded radical-free part (L3911–3999). Coupled sections of tree groups (iterated wreath products
   of $S_b$, $b\ge5$) have trivial radical, so this does not transfer to TreeCI. It might for
   "solvable-coupled" towers, beyond the abelian case of Lemma N. **[SPECULATION]**
6. **Canonical row machinery** (rows 14–16 of §1.3), for canonical forms of all graphs in
   $n^{O(\log n)}$. I see no invariant replacement for the row carrier. Low priority.

---

## 6. Ledger

| item | status |
|---|---|
| BC's obstacles; the logarithmic threshold in BC Cor. 13.3, Lemma 15.1 and Prop. 14.2 | read in BC (§1.2) |
| Principle P | standard (§1.1) |
| component table, §1.3 | **[SKETCH]** |
| Lemma 2.1 (tuple right descent), Lemma 2.2 (exactness, twins) | **[PROVEN]** (2.2 given HJ's endpoint identity) |
| canonical chain computation | **[SKETCH]** (BC §16 template) |
| Lemma 2.4 (canonical subcoset), Lemma 2.5 (branches) | **[PROVEN mod BC framework]** / **[PROVEN]** |
| Lemma 2.6 (large symmetry) | **[SKETCH]** |
| Theorem C, Corollary C′; potential survives | **[CONDITIONAL: (H0), BC, BL83; SKETCH]** |
| Remark 2.3 (simplifies BC?) | **[SKETCH]**, unverified |
| Proposition 3.1 (isomorphism frontier hybrid) | **[PROVEN given (H0)]** |
| Lemma N, Corollary N′ | **[PROVEN mod BC Def. 5.1]** |
| Theorem E-canon | **[PROVEN mod BC framework]** |
| Theorem P-canon | **[SKETCH mod Wie20 Cor. canObj0]** |
| Theorem L with frontier | **[SKETCH]** |
| Theorem H, Corollary H′ | **[CONDITIONAL: Thm C]**; isomorphism version **[CONDITIONAL: (H0)]** |
| alignment diagnosis, §3.7 | **[SKETCH]** |
| residual = TreeCI (isomorphism) / TreeCan (canonical) | **[PROVEN]** from W2; TreeCan vs TreeCI open |
| canonical row machinery | not obtained; **[SPECULATION]** |
| novelty | literature table, §4 |
| no Lean, no solver, no benchmark run | — |
