# The core problem: TreeCI and tanglegrams

What remains when the group-theoretic machinery is stripped away. This is where the question "is degree-d GI FPT?" now lives.

[Home](Home.md) · Sources: [w1-fpt](../docs/w1-fpt.md), [w1-structure](../docs/w1-structure.md), [w2-coset](../docs/w2-coset.md), [w4-t2](../docs/w4-t2.md), [w6-tanglegram](../docs/w6-tanglegram.md), [w8-poset](../docs/w8-poset.md), [w27-tree](../docs/w27-tree.md), [redteam-w27-w28](../docs/redteam-w27-w28.md) · Ledger: [section 6](Results-Ledger.md#6-the-core-problem-treeci-tanglegrams-posets) · Open: [Open problems](Open-Problems.md#core-questions)

No FPT algorithm and no hardness result was found for any of these problems. All are in XP by Luks or GNS.

**w27** attacked R1_c (complete-tree tanglegram isomorphism) and height-2 posets with large μ; [below](#height-2-posets-and-r1_c-w27). Neither is settled.

## Definitions

* **Tree group of degree b**: a subgroup G ≤ W(T) = Aut(T) of a rooted tree T with node degree ≤ b, acting on the leaves.
* **TreeCI(b)**: coset intersection G₁a ∩ G₂c of tree groups on one tree, parameter b.
* **TreeSI(b)**: string isomorphism under tree groups.
* **PCI**: product-coset intersection, the combine step of the block DP: K ∩ ∏_i A_i z_i with K ≤ ∏ R_i.
* **T²(b)**: string isomorphism under G₁ × G₂ on Λ₁ × Λ₂ (matrices with tree-structured rows and columns).
* **Tanglegram**: two rooted trees on one leaf set. **(R1)** is the problem of coloured tanglegram isomorphism, FPT in out-degree b? **R1_c** is the restriction to complete b-ary trees.
* **Entanglement index** ε_B = |∏_i π_i(K_B) : K_B| at a block B.
* **Coupling depth** δ_B: how deep the coupled sections reach.

## The chain of reductions

1. **Block-pair DP** (w1-fpt Prop 4.1). String isomorphism memoized over O(N²) block pairs reduces to at most 4N²·max|P_B| PCI instances. Giants of degree q ≤ d then cost q! additively, not multiplicatively. So the difficulty is not the number of subproblem types; it is entirely in PCI.
2. **Theorem E** (w1-fpt §4.3). PCI is solvable in r·ε·poly(N), so total cost π₀·ε·poly(N). Entanglement of index ε is what is hard, and abelian entanglement is free ([red-team](../docs/redteam-w1-fpt.md) §3.4).
3. **TreeSI ≡ TreeCI** for tree groups (w1-fpt Prop 4.2, after repairs). The core can be taken to be coset intersection.
4. **Equivalences** (w2-coset Thm 2.1): TreeSI ≡ TreeCI ≡ PCI ≡ PCI_diag ≡ T². GNS's almost d-ary class is tree groups of degree d!/2 (Lemma 2.4).
5. **Bounded coupling depth is FPT** (Cor 2.3). What matters is depth, not the coupling pattern: a diagonal on a full-depth direct factor is already complete.
6. **Graph side** (w4-t2 Theorem A). Full-group T² ≡ coloured tanglegram isomorphism ≡ FullCI ≡ HCGI (arbitrary graphs carrying a b-ary hierarchical clustering) ≡ Def-CI.
   * TreeCI = CI(arbitrary G, full Aut(T,x), same tree). T²_full = CI(full, full, different trees). The gap between them is exactly **(R2): are all tree groups fpt-definable?**
   * Degree-d GI ≡ depth-2 tanglegrams with unbounded root (Prop A″). **R1 is necessary for FPT degree-d GI** (T²_full ≤ coloured GI of degree b+1).
7. **Posets** (w8-poset). Theorem 1 solves SI under generalized wreath products over posets in b!·2^{O(b^{μ+1})}·N^{O(1)}, but Prop H shows C_h ⊔ C_h (width 2) is already R1_c. So width and dimension cannot help.

## Height-2 posets and R1_c (w27)

Source: [w27-tree](../docs/w27-tree.md) (`b11f2d3`), AI red-teamed by [redteam-w27-w28](../docs/redteam-w27-w28.md), which found no claim broken and narrowed three. See [Corrections](Corrections.md#height-2-posets-and-r1_c-w27-w31); the memo was not edited afterwards. **HT2** is string isomorphism under G₁ × G₂, G_i = K_i ⋊ T_i, with T_i = S_b^m on V and K_i = S_b^V: the poset (A_m < k) ⊔ (A_m < k).

* **Not settled.** FPT for height-2 is open and FPT for R1_c was not found.
* **Barrier** (Prop N, Cor N.1, proven): a section Y_c of the A₅ wreath tower in a group with a normal series of length ℓ whose factors embed in products of S_b has c ≤ ℓ·D(b). So no parameterized reduction from R1_c(b₀) to a bounded-height family can reflect Aut at the identity tanglegrams. This narrows but does not decide height 2: it only rules out hardness proofs of the gadget kind used so far.
* **No small faithful domain** (Lemma MD, proven, likely folklore): Sym(b) ≀ R has minimal faithful degree exactly rb for b ≥ 5, so a domain-based coset-intersection bound is useless for the shared group of HT2.
* **Sub-classes.** Reduction 0 (T₂ fixed or enumerable: FPT, modulo ADKT). Theorem G (pinning set of ρ blocks): (b!·b^m)^ρ · b!·2^{O(b)}·N^{O(1)}, which is **XP in ρ and not FPT in (b, ρ)**. Theorem G+ adds r top coordinates, FPT in r. Theorem C (soluble surviving top after a given r-coordinate set): (b!)^{r+2}·N^{O(1)}, modulo Luks's recursion and Pálfy–Wolf.
* **Open residue.** A hard height-2 instance needs a non-soluble surviving top on many coordinates and no small pinning set. The cleanest case is a bipartite gain graph with labels in S_b, up to switching: non-abelian with curvature over a large non-soluble top. Flat components are a sketch; low-support generation of π₁ is speculation.
* **The gain-graph conjecture is false as sharpened (w50, w53).** [w50-gain](../docs/w50-gain.md) states w27's lead 1 precisely and refutes it. A non-bipartite base graph of odd girth g, with patterns from a code, gives a parity map from π₁ onto the code, so every normal generating set needs walks with many values on many coordinates (Theorem B; folded cubes and odd graphs). If every coordinate group is 2-transitive, 3 values per coordinate suffice, and 3 is optimal (Theorem A, constant improved by the red-team). The [red-team](../docs/redteam-w50-gain.md) found no break in a main theorem and judged the sharpening fair. It corrected the framing: on this family |C| = N^{Θ(log log b)}, so every gain problem on it, non-abelian included, takes f(b)·N^{O(log log b)}, and what is open is only removing that log log b exponent. Prior art: Matsushita (2017) already has the parity map modulo short cycles and the odd-graph case. Forms that survive: c ≳ log log b, κ ≤ M extra walks, k = Θ(log b), or w50's W\*. Nothing follows for TreeCI or GI.
* **R1_c.** Prop 3.2: a definable one-call combine at node u needs Ω(s²/log s) leaves where n − n_max = 2s, so W6's lead 2 is false as stated. A limit on that route; a combine that leaves R1 is TreeCI on the frontier.

## What makes instances hard (w6-tanglegram, w4-t2)

* **Prop L**: polynomial if *either* tree has out-degree ≤ 4 (or at most 4 isomorphic children at each node), with no bound on the other tree; n^{O(d/log d)} generally. The other tree may be arbitrary. So hard instances need deep Sym(≥5) towers in **both** trees.
* **Prop D**: prime decomposition via common clusters. Hard instances are prime.
* **Prop S** (w6): at a node u, the group is a fibre product over the *straddling* subtree of T′, of total size ≤ n log₂ n over all u.
* **Prop T** (w4-t2): FPT in (b, τ), τ the largest Goursat quotient of the instance's own row strips. Tanglegrams are the purest twisted instances.
* **Theorem B** (w4-t2): CFI over cubic expanders embeds in coloured binary tanglegrams, so WL dimension is Ω(|V|) at b = 2. Any FPT algorithm must be group-theoretic. Prop L shows that defeating WL is unrelated to hardness: those families are polynomial.
* **Random instances are easy.** Colour refinement separates random T² instances; random leaf bijections have tiny groups; 2-WL computed the orbits on all 21 plain tanglegrams tested.

Necessary conditions for a hard family: prime; non-solvable depth unbounded in both trees; twisting τ unbounded; straddling width and treewidth unbounded; not product type; and, for coordinate instances, μ unbounded (Theorem 1 of w8-poset).

## Other structural results

* **Enumeration channel** (w1-structure). Primitive quotients with large order split into alternating/top-group types (μ reaches Θ(log d) only at d′ ≥ 2^{d^Ω(1)}) and Lie-rank types (AGL(r,2), PGL(r,2) with μ ≈ log₂(d+1)+1 at d′ ≈ d). The Lie part is the real independent source of n^{log d}. Sketch.
* **Theorem L** (w1-structure): level-synchronised towers G = R·S are FPT given their tower data; G_{r,L} shows "entangled, no small faithful domain" does not imply hard.
* **Theorem P** (w2-coset, known prior work; see [Corrections](Corrections.md#theorem-p-is-babaicodenottiqiao-2012)): product actions with any top group are FPT.
* **Example X** (Cayley-coupled): collapses for r ≥ 3 at levels ≥ 3; level 2 may stay coupled, bounded in d (FPT still).
* **Theorem E′**: for Γ̂_d, only entanglement matters; primitive components may be unbounded. Sketch.
* **Hardness**: none. The Clique-lower-bound barrier forces parameter blow-up 2^{k^Ω(1)} for any W[1]-hardness; see [Barriers](Math-Barriers.md#the-clique-lower-bound-barrier).

## Practical note

Coloured or plain tanglegrams of complete trees defeat colour refinement and are a cheap stress family for individualization-refinement solvers (w4-t2 §6). They are not in the benchmark tiers.
