# The core problem: TreeCI and tanglegrams

What remains when the group-theoretic machinery is stripped away. This is where the question "is degree-d GI FPT?" now lives.

[Home](Home.md) · Sources: [w1-fpt](../docs/w1-fpt.md), [w1-structure](../docs/w1-structure.md), [w2-coset](../docs/w2-coset.md), [w4-t2](../docs/w4-t2.md), [w6-tanglegram](../docs/w6-tanglegram.md), [w8-poset](../docs/w8-poset.md) · Ledger: [section 6](Results-Ledger.md#6-the-core-problem-treeci-tanglegrams-posets) · Open: [Open problems](Open-Problems.md#core-questions)

No FPT algorithm and no hardness result was found for any of these problems. All are in XP by Luks or GNS.

**In progress as of `1368fb6`:** `w27-tree` attacks R1_c (complete-tree tanglegram isomorphism) and height-2 posets with large μ. Nothing from it is on this page yet.

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
