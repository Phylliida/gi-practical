# w6-tanglegram: coloured tanglegram isomorphism (R1), parameterized by out-degree

Branch `w6-tanglegram`, 2026-11-05. Wave 6 of the overnight campaign (`overnight-log.md`). Input:
`w4-t2.md` (T2 below), `w2-coset.md` (W2), `w1-fpt.md` (FPT), `w3-canon.md` (CANON).

**Problem (R1).** Given rooted trees $T,T'$ of out-degree $\le b$ on a common coloured leaf set $L$
($\lvert L\rvert=n$), compute $G=\mathrm{Aut}(T)\cap\mathrm{Aut}(T')$, and isomorphism cosets between
two such tanglegrams. Is this FPT in $b$? By T2 Theorem A it is equivalent to full-group $T^{\,2}$,
HCGI, Def-CI and FullCI. It is necessary for degree-$d$ GI to be FPT.

**Labels.** As in T2: **[PROVEN]**, **[PROVEN mod X]**, **[SKETCH]**, **[CONDITIONAL: H]**,
**[SPECULATION]**.

**Work done.** A literature search (a sub-agent plus my own checks of the key statements); the
analysis below; one experiment (`scratchpad/w6tg/e1_coord.py`, pynauty in the r2-hybrid venv,
`nice`, under a minute). Lean was not run. The session was cut short by a rate limit, so §5 lists
what is unfinished.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Is tanglegram isomorphism studied? | **No complexity result exists** that I or the search agent could find, under any parameterization. The phylogenetics papers use double cosets only for counting, and settle isomorphism with GAP, Sage or nauty. The closest results are: Luks 1993's double-coset theorem (one group in $\Gamma_d$ suffices), and the GI-completeness of tree-sibling phylogenetic networks at unbounded in-degree, with in-degree 2 in P. | §1 |
| 2 | Best algorithm | **Prop L.** Tanglegram isomorphism is **polynomial when one of the two trees has out-degree $\le4$, with no bound at all on the other tree**. It takes $n^{O(d/\log d)}$ when one tree has out-degree $\le d$. It is FPT in $(b,\nu)$, where $\nu$ is the *non-solvable depth* of either tree: the largest number of nodes, on one root–leaf path, that have $\ge5$ isomorphic children. | P case and $n^{O(d/\log d)}$: **[PROVEN mod Luks 1993 Cor. 6.3/6.4]**. $\nu$ refinement: **[SKETCH]** |
| 3 | Structure | (a) **Prime decomposition**: canonization reduces to *prime* tanglegrams, which share no non-trivial cluster (Prop D). (b) **Straddling decomposition**: at a node $u$ of $T$, $G^{\rm loc}(u)$ is a fibre product of the children's groups over their actions on the straddling subtree $S(u)$ of $T'$. This subtree has at most $\lvert L(u)\rvert-\max_i\lvert L(u_i)\rvert$ leaves, and the total over all $u$ is $\le n\log_2n$ (Prop S). (c) **Coordinate tanglegrams**: the groups of $(T_{\rm id},T_\rho)$ on $[b]^h$ are exactly the **generalized wreath products** (Bailey–Praeger–Rowley–Speed) of $S_b$ over the 2-dimensional poset $\mathrm{id}\cap\rho$ (Prop C). These range from product action (digit reversal) to the full tree group. | **[PROVEN]**; (c) verified in E1 |
| 4 | FPT for the general problem? | **Not found.** Each route stops at a named point (§2.5). Peeling $\mathrm{Sym}(b)$ costs the whole iterated-$\mathrm{Alt}$ normal subgroup, not $f(b)$. The straddling recursion multiplies a recursive call by $b!$, which gives $n^{O(b\log b)}$. Recursing on the smaller side would need projections of tanglegram groups to be definable *on the straddling subtree*. | — |
| 5 | Lower bound / hardness | **No reduction.** The ETH barrier of W2 §5.1 applies unchanged. New *necessary conditions* for hard instances, from Props L, D, S and T2's Prop T: prime; non-solvable depth unbounded in **both** trees; large twisting $\tau$; not product-type. Consequence: **non-abelian CFI over a fixed group with a rigid binary top is in P or FPT** (by Prop L), even though it defeats WL. The only lower bound proved is the trivial one for Luks without memoization ($\ge(b!)^h$ on digit reversal). | **[PROVEN]** (conditions); lower bound for a general coset-splitting model: open |
| 6 | Experiment | E1: on 21 coordinate tanglegrams, nauty's $\lvert\mathrm{Aut}\rvert$ equals the generalized-wreath-product order. It matches exactly on 18; on the 3 instances with $\lvert\mathrm{Aut}\rvert>10^{28}$ it matches to the 15 digits nauty reports in floating point. A single leaf transposition usually shrinks the group a lot, by factors up to about 1150 ($b=4$, $h=3$; $2^9$ at $b=2$, $h=6$), and splits the single leaf orbit into up to 24 orbits. Random bijections have tiny groups. | §4 |

**Verdict.** R1 remains open. This round adds a clean **one-sided tractability** theorem:
solvability of *either* tree's automorphism group suffices, and the other tree may be arbitrary.
Together with Prop T, Prop D and Theorem P, it pins the hard core to **prime tanglegrams with deep
$\mathrm{Sym}(\ge5)$ towers on both sides, coupled in a non-product, twisted way**. Coordinate
tanglegrams (generalized wreath products over 2-dimensional posets) are the natural structured
family inside that core, and they are the best next target (§5, lead 1).

---

## 1. Literature status

Search scope (2026-11-05). Queries: tanglegram isomorphism complexity; tanglegram automorphism and
double coset algorithm; two dendrograms / two ultrametrics / bi-ultrametric; two hierarchical
clusterings; bi-hierarchical; union of two laminar families; 2-laminar; laminar or cross-free
hypergraph isomorphism; clustered-graph isomorphism; display-graph isomorphism; double cosets of
iterated wreath products; FPT coset intersection; FPT by the number of non-abelian composition
factors; isomorphism of level-$k$, galled and tree-child networks. Sources were downloaded to
`r4-sources/w6lit-*/`.

**Tanglegram papers.** None of these has any algorithm or complexity content. Each was verified from
its source.
* Matsen–Billey–Kas–Konvalinka, arXiv:1507.04784 (IEEE/ACM TCBB 2018).
  * Prop. 14: tanglegrams on fixed trees are the double cosets $\mathrm{Aut}(S)\,w\,\mathrm{Aut}(T)$.
  * Prop. 18–19: the automorphism group is $\mathrm{Aut}(T)\cap\varphi^{-1}\mathrm{Aut}(\cdot)\varphi$, up to
    index 2 when the trees can be swapped.
  * Computation: counts were validated "by checking for graph isomorphisms between exemplars for
    $n\le6$", and GAP/Sage were used for double cosets and symmetry groups.
* Konvalinka–Wagner, arXiv:1512.01168. Thm. 8: with high probability, all automorphisms of a random
  (binary) tanglegram come from matched cherries, whose number is asymptotically Poisson(1/4).
* Billey–Konvalinka–Matsen, arXiv:1507.04976 (JCTA 2017): Burnside counting over double cosets.
* Gessel, arXiv:1509.03867; Clifton et al., arXiv:2501.13670: counting only.
* Diaconis et al., arXiv:2504.01149 (2025): double cosets of Sylow 2-subgroups of $S_{2^k}$. These are
  exactly tanglegrams of two complete binary trees, although the paper does not say so. Structural
  results only.

**Double cosets (directly relevant).** Luks, "Permutation groups and polynomial-time computation",
DIMACS 11 (1993), verified in `w6lit-luks-dimacs/`.
* Prop. 4.4: DC-EQ ($Gx_1H=Gx_2H$?) is polynomial-time equivalent to set transporter.
* Thm. 5.1: the lexicographic leader of a double coset is NP-complete.
* **Cor. 6.3(ii)/6.4(ii): for fixed $d$ and $G\in\Gamma_d$, DC-EQ and $G\cap H$ are polynomial for
  *arbitrary* $H$.** The time is $O(\lvert\Omega\rvert^{cd})$, improved to
  $O(\lvert\Omega\rvert^{cd/\log d})$ in the remarks; solvable groups are included. Only **one**
  group needs restricted composition factors. This is the source of Prop L.
* GI $\le$ DC-EQ (Hoffmann 1982; restated in Verbitsky arXiv:0801.4911). In that reduction one group
  is a Young subgroup, i.e. the automorphism group of a depth-2 tree. This matches T2 Prop A″.

**Phylogenetic networks.** Cardona–Llabrés–Rosselló–Valiente, arXiv:0902.4640 (read through a fetch
summary of the PMC full text, not first-hand):
* isomorphism of tree-sibling time-consistent networks is GI-complete, via hybrid nodes of unbounded
  in-degree;
* it is in P for in-degree 2;
* the authors *conjecture* it is in P for any bounded in-degree.

That is the same shape of question as R1, unresolved there too. Display graphs ($T\cup_LT'$) can
have linear treewidth (Kelk–Stamoulis–Wu, arXiv:1703.10840; abstract only).

**General GI parameterizations** (Neuen's survey, Comput. Sci. Rev. 2026).
* There are FPT results for treewidth, tree-depth, feedback vertex number, genus and eigenvalue
  multiplicity. None applies to tanglegrams in general (degree $b+1$, possibly linear treewidth,
  cycle rank $n-1$).
* FPT by maximum degree is open (GNS arXiv:1802.04659, last paragraph).
* ADKT (FSTTCS 2010 / ECCC TR09-093): $2^{O(b)}N^{O(1)}$ for bounded *orbits*; Schweitzer–Wiebking
  canonize in the same bound.
* Nothing parameterizes by bounded composition factors, or by the number of non-abelian factors.
  Neuen arXiv:2002.06997 gives hypergraph isomorphism for $\hat\Gamma_d$ in
  $(n+m)^{O((\log d)^c)}$, which applies to tanglegrams (hyperedges = clusters of $T'$) and gives
  XP only.

**Status.** As far as both searches found, R1 is **not stated anywhere**. The ingredients of Prop L
are classical; that corollary is probably folklore among permutation-group experts, but I found no
statement of it.

---

## 2. Results

Notation: $A=\mathrm{Aut}(T)$, $A'=\mathrm{Aut}(T')$, $G=A\cap A'$. Trees are coloured and unary
nodes are suppressed. $T$ is encoded on $L\times L$ by the pair colouring
$(x,y)\mapsto(\text{depth of }\mathrm{lca}_T(x,y),\ \text{colour of the lca})$. The automorphism
group of this pair colouring is exactly $A$: the clusters are the classes of "lca depth $\ge j$",
over all $j$.

### 2.1 Prop L: one solvable side suffices

**Prop L.** Let $T'$ have out-degree $\le d$. Coloured tanglegram isomorphism, and the computation
of $G$, takes time:
1. **polynomial** if every node of $T'$ has at most 4 children in each isomorphism class (in
   particular, if $d\le4$), whatever $T$ is (any out-degree); **[PROVEN mod Luks 1993 Cor. 6.3/6.4]**
2. $n^{O(d/\log d)}$ in general, again whatever $T$ is; **[PROVEN mod Luks 1993]**
3. $(b'!)^{O(\nu(T'))}\cdot n^{O(1)}$, where $\nu(T')$ is the largest number of nodes, on one
   root–leaf path, with $\ge5$ pairwise isomorphic children, and $b'$ bounds their number.
   **[SKETCH]**

*Proof of 1–2.*
* $A'$ is an iterated product of direct and wreath products of the groups
  $\mathrm{Sym}(m_{v,\theta})$, where $m_{v,\theta}$ is the number of children of $v$ of isomorphism
  type $\theta$. So $A'\in\Gamma_d$, and $A'$ is **solvable** when every $m_{v,\theta}\le4$.
* Compute $a,c$ with $T^a=T_1'$ and $T'^c=T_2'$ (AHU), or stop if either does not exist.
* The isomorphisms are $Aa\cap A'c$. Deciding non-emptiness is DC-EQ, and computing the coset is
  $G\cap H$ in coset form. Luks 1993 Cor. 6.3(ii) and 6.4(ii) do both in polynomial time when one
  group is solvable, and in $O(n^{cd/\log d})$ when it lies in $\Gamma_d$. The other group is
  arbitrary; here $A$ is given by generators, which AHU computes. ∎

*Sketch of 3.*
* Run Luks's string-isomorphism recursion for $A'c$ on $L\times L$, with $T$'s pair colouring as
  the string. Use **tree-aligned** block systems, and minimal ones only where it helps: on an orbit of
  pairs with lca $w$, split first by the path to $w$, then by the ordered child pair at $w$, then by
  the pairs of children $(u_i,v_j)$.
* Within an orbit, blocks have equal size. A step whose quotient $P$ is solvable acts on
  $m\ge2$ blocks with $\lvert P\rvert\le24^2\le m^{10}$. With cost $C(s)=s^{11}M$, Luks's recurrence
  $C\le\sum_{\rm orbits}\lvert P\rvert\,m\,C(\lvert O\rvert/m)$ then telescopes, because
  $\sum_O\lvert O\rvert^{11}\le(\sum_O\lvert O\rvert)^{11}$.
* A step with a non-solvable quotient multiplies $M$ by $\le(24\,b'!)^2$.
* Each pair lies on two root–leaf paths, so $M\le(24\,b'!)^{4\nu}$.
* *Gap:* I did not write out the bookkeeping for the path above $w$ and for orbits finer than
  sub-blocks; both look routine.

*Consequences.*
1. **[PROVEN]** Prop A″ of T2 (degree-$d$ GI = depth-2 tanglegrams with unbounded roots) needs
   **both** roots unbounded. If one side is solvable, unbounded out-degree on the other side is
   harmless.
2. **[PROVEN]** A hard family for R1 must have non-solvable depth $\nu\to\infty$ in **both** trees.
   Every node on such a path has $\ge5$ isomorphic children, so $\nu\le\log_5n$, and the hard
   structure is a pair of deep $\mathrm{Sym}(\ge5)$ towers.
3. **[PROVEN]** The parameter can be shrunk for free: replace $T'$ by $T'$ coloured with any
   isomorphism-invariant node colouring, e.g. 2-WL colours of the tanglegram, which T2's E5 found to
   equal the orbits on plain tanglegrams. Then $\nu$ counts only nodes with $\ge5$ children that
   2-WL cannot separate.
4. **[PROVEN]** Non-abelian CFI constructions over a fixed group $\Gamma$ (for instance with
   $\mathrm{Sym}(5)$ torsors), placed under a rigid binary top as in T2 §5.1, have $\nu=O(1)$ on the
   row side. They therefore defeat WL but are polynomial.
5. **Digit reversal** has $\nu=h$ on both sides. It is the canonical instance that Prop L does
   *not* cover, and Theorem P does.

**Novelty.** Items 1–2 are immediate from Luks 1993. I found the tanglegram reading nowhere. The
observation "one side solvable, the other arbitrary" is the new content for the campaign. It
strengthens T2's "$b=2$ is in P" to "$\min(b_1,b_2)\le4$ is in P".

### 2.2 Prop D: prime decomposition **[PROVEN]**

* Let $\mathcal C=\mathcal C(T)\cap\mathcal C(T')$ be the common clusters. It is laminar and forms a
  tree $T_c$ (unbounded out-degree).
* For each node $X$ of $T_c$ with $T_c$-children $Y_1,\dots,Y_m$: contract each $Y_i$ to a leaf in
  $T_X$ and $T'_X$ (each $Y_i$ is a cluster of both). This gives a **prime** tanglegram $P_X$ on
  $\{Y_i\}$, whose two trees have out-degree $\le b$ and share no non-trivial cluster.
* *Canonization.* Bottom-up along $T_c$: $\mathrm{can}(X)$ is the canonical form of $P_X$ with each
  leaf $Y_i$ coloured by $\mathrm{can}(Y_i)$. The automorphism group is the usual wreath-type
  composition.

So R1 (canonical version) is fpt-equivalent to R1 restricted to prime tanglegrams. Two consequences:
* it is FPT in the largest prime size, by brute force;
* it is FPT in the Robinson–Foulds distance, which bounds every prime size.

Digit reversal, CFI-in-tanglegram and coordinate tanglegrams are prime. This is the analogue of
modular decomposition, and I expect it is folklore.

### 2.3 Prop S: the straddling decomposition **[PROVEN]**

Fix a node $u$ of $T$ with children $u_1,\dots,u_k$, and write $L_i=L(u_i)$.
* Let $T'_u=T'|_{L(u)}$ (restriction, unary nodes suppressed).
* Let $S(u)$ be its *straddling* nodes: those meeting $\ge2$ of the $L_i$. $S(u)$ is upward closed.
* Let $G^{\rm loc}(u)=\mathrm{Aut}(T_u)\cap\mathrm{Aut}(T'_u,\text{marks})$, where the marks record
  the straddling structure.

1. *Fibre product.* The kernel of $G^{\rm loc}(u)$ on the children of $u$ is
   $\{(g_i)\in\prod_iG^{\rm loc}(u_i):\ \rho_i(g_i)\text{ agree on }S(u)\}$, where $\rho_i$ is the
   action on $S_i=S(u)\cap T'_{u_i}$. All $S_i$ contain the root of $T'_u$, and every node of $S(u)$
   lies in $\ge2$ of them. *(Gluing: maps that preserve $T'|_{L_i}$ and agree on the straddling
   nodes preserve $T'_u$. Monochrome hanging subtrees belong to one $i$ each.)*
2. *Small domain.* $\mathrm{Aut}(S(u))$ acts faithfully on the leaves of $S(u)$, i.e. its bottom
   nodes. Each bottom node meets $\ge2$ classes and the bottom nodes are disjoint, so
   $\lvert\mathrm{bottom}(S(u))\rvert\le\lvert L(u)\rvert-\max_i\lvert L_i\rvert$.
3. *Total size.* $\sum_u(\lvert L(u)\rvert-\max_i\lvert L_i\rvert)\le n\log_2n$, by the smaller-half
   argument: a leaf lies in a non-maximal child at most $\log_2n$ times.
4. *Reduction.* Hence coloured tanglegram isomorphism reduces, in $b!\cdot\mathrm{poly}(n)$ time, to
   $k$-fold ($k\le b$) coset intersections of tree groups of out-degree $\le b$, given by generators
   (the $\rho_i(G^{\rm loc}(u_i))$), on domains of total size $\le n\log_2n$. With iso-pairs instead
   of canonical forms, the count is $O(n^2)$ instances.

**Where it stops.**
* The combine is TreeCI, the harder group core, though on small domains.
* Keeping it inside R1 needs the projections $\rho_i(G^{\rm loc}(u_i))$ to be definable *on
  $S(u)$*. Their natural defining structures have size $\lvert L_i\rvert$, which gives no shrinkage.
* Even with exact small definability, the recurrence
  $C(n)\le\sum_iC(n_i)+b!\cdot C(n-n_{\max})$ solves to $n^{\Theta(\log b!)}$.
* The smaller-half recurrence $C(n)\le\sum_iC(n_i)+O(1)\cdot C(n-n_{\max})$ is polynomial
  ($n^{\log_23}$ at $k=2$). So FPT would follow from a combine that calls the problem once, on
  $\le n-n_{\max}$ leaves, *without* the $b!$ factor. **[CONDITIONAL: such a combine]**
* *FPT in the straddling width* $\max_u\lvert\mathrm{bottom}(S(u))\rvert$, by brute force on the
  combine. **[PROVEN]** This parameter is probably dominated by treewidth, so it adds nothing new.

### 2.4 Prop C: coordinate tanglegrams are generalized wreath products **[PROVEN]**; E1

**Setting.**
* $L=[b]^h$, and $T_\sigma$ is the complete tree that splits coordinates in the order
  $\sigma(1),\sigma(2),\dots$.
* For orders $\sigma,\rho$, let $P=P_{\sigma,\rho}$ be the poset on $[h]$ with $j\prec i$ iff $j$
  precedes $i$ in both orders. Every poset of order dimension $\le2$ arises this way.

**Prop C.** $\mathrm{Aut}(T_\sigma)\cap\mathrm{Aut}(T_\rho)$ is the **generalized wreath product**
of $S_b$ over $P$ (Bailey–Praeger–Rowley–Speed, Proc. LMS 1983): the maps $g$ with
$g(x)_i=\pi_i(x_{\prec i})(x_i)$, for arbitrary $\pi_i:[b]^{\{j\prec i\}}\to S_b$. Its order is
$\prod_i(b!)^{b^{\lvert\{j\prec i\}\rvert}}$.

*Proof.*
* An automorphism of $T_\sigma$ acts on coordinate $i$ by a permutation that depends only on the
  coordinates before $i$ in $\sigma$; likewise for $T_\rho$.
* For $g$ in the intersection, the function $x\mapsto g(x)_i$ on the product $[b]^h$ therefore
  depends only on $\{j:j<_\sigma i\}\cup\{i\}$, and also only on $\{j:j<_\rho i\}\cup\{i\}$. Hence it
  depends only on the intersection of these sets, $\{j\prec i\}\cup\{i\}$.
* Bijectivity forces each $\pi_i(\cdot)$ to be a permutation.
* Conversely, every such map preserves both trees. ∎

**Reading.**
* An antichain (digit reversal) gives $S_b^h$ in product action (Theorem P).
* A chain gives the full tree group (AHU).
* Every 2-dimensional poset in between is a tanglegram group. Its non-abelian factors $\mathrm{Alt}(b)$
  sit at every coordinate and are **diagonally shared** across all leaves with the same values on
  the down-set $\{j\prec i\}$. So the coupling is non-uniform, and neither Theorem P nor Prop T
  covers it.
* With leaf colours added, coordinate tanglegrams are SI under generalized wreath products with
  strings on all of $[b]^h$.

### 2.5 Ideas from the brief that did not reach FPT

| idea | outcome | stops at |
|---|---|---|
| peel off $\mathrm{Sym}(b)$, Luks on the solvable rest | $A\trianglerighteq E=\mathrm{Alt}$-iterated wreath product, and $A/E$ is a 2-group. Luks handles $A/E$ | $E$ is not $f(b)$-sized: $G\cap E$ can contain $\mathrm{Alt}(b)^h$ (digit reversal). Peeling only works one-sidedly, which is Prop L |
| recursion on the meet $E_i\wedge E'_j$, or the join chain $E_j\vee E'_j$ | the join chain is a $G$-invariant hierarchy, but its out-degree is unbounded | digit reversal: the incidence graph of depth-$j$ nodes is complete bipartite for $j\le h/2$, so nothing decouples |
| straddling recursion | Prop S | $b!$ times a recursive call; projections are not small-definable |
| abelian twisting (T2 lead 1) | for tanglegrams the Prop T quotients $Q(u,v)$ are automorphism groups of sub-tanglegrams on $L(u)\cap L(v)$ | the combine is a sub-tanglegram again (T2 Prop D.3). "Abelian $Q$" needs that sub-tanglegram to have an abelian group, which is a property of the answer, not of the input |
| non-abelian CFI (bounded $\Gamma$) as a hard family | defeats WL | Prop L (rigid binary top), and group-CSP / bounded-orbit methods |

---

## 3. Lower bounds and hardness

* **No reduction** from a problem believed not to be FPT. W2 §5.1's ETH barrier applies verbatim:
  the problem is in $n^{\mathrm{polylog}\,b}$ (GNS; Neuen 2002.06997), so W[1]-hardness would need
  $b\ge2^{k^{\Omega(1)}}$. Luks's NP-completeness of the lexicographic double-coset leader
  (Thm. 5.1) concerns a different question, not isomorphism.
* **Necessary conditions for hard families** **[PROVEN]**, combining Props L, D, S with T2's Prop T
  and Theorem P:
  1. prime;
  2. $\nu\to\infty$ in both trees, even after 2-WL colouring;
  3. twisting $\tau$ unbounded;
  4. straddling width and treewidth unbounded;
  5. not of product type.

  Coordinate tanglegrams with twisted leaf colourings satisfy 1–5 as far as I can see
  **[SPECULATION]**, which makes them the natural candidate lower-bound family.
* **Model lower bounds.** Luks's recursion without memoization explores all $\lvert P\rvert$ cosets
  at each block step. On digit reversal with tree-aligned blocks, the child-1 calls under the $b!$
  root branches are again digit-reversal instances of depth $h-1$, so it costs
  $\ge(b!)^h=n^{\log b!/\log b}$. **[PROVEN, trivial]** A lower bound for a model *with*
  memoization of sub-tanglegrams, or with arbitrary subgroup splitting, is **open**. FPT §3.4's
  prover–delayer formulation is still the right shape.
* WL, IR and rank logic fail already at $b=2$ (T2 Theorem B), and Prop L shows that failure is
  unrelated to hardness: those families are polynomial.

---

## 4. Experiment E1 (`scratchpad/w6tg/e1_coord.py`, seed 1)

Coordinate tanglegrams $(T_{\rm id},T_\rho)$ for random $\rho$, with
$(b,h)\in\{(2,4),(3,3),(3,4),(4,3),(5,2),(5,3),(2,6)\}$ and 3 values of $\rho$ each. nauty computes
$\lvert\mathrm{Aut}\rvert$ and the leaf orbits of the tanglegram graph.

* **Prop C prediction.**
  * Exact on 18/21.
  * The other 3 are $\rho=\mathrm{id}$ with $\lvert\mathrm{Aut}\rvert\approx10^{29}$ and $10^{64}$.
    There the prediction agrees with nauty's floating-point value to about 15 significant digits.
  * Examples: $b=3,h=4,\rho=(0,2,3,1)$ gives $2.82\cdot10^{12}$; digit-reversal-type orders give
    $(b!)^h$; $b=2,h=6$ gives $4096$ to $6.7\cdot10^7$, depending on the poset.
* **Fragility.** Swapping one pair of leaves usually shrinks the group a lot:
  * $b=2,h=6$: from $4096$ to $8$ ($2^9$), and from $6.7\cdot10^7$ to $5.2\cdot10^5$ ($2^7$);
  * $b=3,h=4$: from $2.18\cdot10^9$ to $2.24\cdot10^6$;
  * $b=4,h=3$: from $1.91\cdot10^8$ to $1.66\cdot10^5$;
  * one leaf orbit splits into up to 24.

  Twisted variants therefore have large but irregular groups. This is the regime §3 points to.
* **Random leaf bijections** give $\lvert\mathrm{Aut}\rvert\in\{1,2,4,32,64,512\}$ with almost all
  leaves in singleton orbits. This matches Konvalinka–Wagner Thm. 8 (cherry-type symmetry only), and
  confirms again that random instances say nothing about hardness.

---

## 5. Leads (ranked)

1. **SI under generalized wreath products over posets.**
   * Generalize Theorem P's DP from antichains to arbitrary posets. The state would be a down-set
     $J$ of $P$ plus an assignment on $J$; there are $\le2^h\le N$ down-sets, so enumerating them
     costs only $\mathrm{poly}(N)$.
   * Branch on the whole of coordinate $i$ at once, but only for minimal elements of the complement.
     The difficulty is that $\pi_i$ depends on the assignment of $\{j\prec i\}$, so the $b$
     sub-conditions are not independent unless $\{j\prec i\}\subseteq J$, which holds for minimal
     $i$.
   * **[SPECULATION]** This looks FPT. It would cover the whole coordinate-tanglegram family and
     strictly contain Theorem P and AHU. Then test it against twisted coordinate tanglegrams (§3).
2. **A one-call combine for Prop S.**
   * Show that $\rho_i(G^{\rm loc}(u_i))$ is defined by a tanglegram on
     $\mathrm{bottom}(S(u))$ plus $O(\lvert S(u)\rvert)$ auxiliary leaves, without the $b!$ factor
     (for example via canonical child orderings).
   * The smaller-half recurrence then gives polynomial time.
   * Binary $T$ ($k=2$) is the first test. There the factor is 2 and harmless, so only definability
     is needed. And by Prop L, $T$ binary is already in P, so the real test is $T$ with $k\ge5$.
3. **Prop L with memoization.** Combine Luks on the solvable levels of $T'$ with CANON's memoized
   canonical forms on non-solvable nodes whose children are untwisted (E-canon). The parameter would
   become the number of *twisted* non-solvable nodes per path.
4. **A prover–delayer lower bound on twisted coordinate tanglegrams**, for coset splitting with
   memoization of sub-tanglegrams.
5. **Phylogenetics link.** The Cardona et al. conjecture (tree-sibling networks of bounded in-degree
   are in P) is the same kind of question. A network-to-tanglegram reduction in either direction
   would connect R1 to an existing open problem.

---

## 6. Ledger

| item | status |
|---|---|
| R1 not studied in the literature (tanglegram, double-coset, laminar, phylogenetics searches) | searched; nothing found |
| Prop L.1–2: one tree solvable ⇒ P; one tree in $\Gamma_d$ ⇒ $n^{O(d/\log d)}$; other tree arbitrary | **[PROVEN mod Luks 1993 Cor. 6.3/6.4]** |
| Prop L.3: FPT in $(b',\nu)$ | **[SKETCH]** |
| Prop L consequences (both sides need deep $\mathrm{Sym}(\ge5)$; fixed-group non-abelian CFI with rigid top is easy) | **[PROVEN]** |
| Prop D: reduction to prime tanglegrams; FPT in prime size / RF distance | **[PROVEN]** |
| Prop S: fibre product, frontier bound, $n\log_2n$ total, reduction to small-domain TreeCI | **[PROVEN]**; FPT from it **[CONDITIONAL: one-call combine]** |
| Prop C: coordinate tanglegrams = generalized wreath products over 2-dimensional posets | **[PROVEN]**; E1 21/21 |
| FPT algorithm for R1 | **not achieved** |
| hardness / model lower bound | **not achieved**, beyond the trivial no-memo Luks bound |

---
**Note added 2026-11-08 (see docs/w21-eth.md).** The "ETH barrier" above should be read as conditional on
CLIQUE-LB, the hypothesis that k-Clique has no f(k)·n^{o(k)} algorithm. ETH implies CLIQUE-LB but not conversely,
so the barrier survives even if ETH fails, as an unrefereed October 2026 preprint claims.
