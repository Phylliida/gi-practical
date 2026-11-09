# Barriers

Why n^{O(log n)} for GI and n^{O(log d)} for degree-d GI are hard to beat. Nothing here is a general lower bound for GI.

[Home](Home.md) · Sources: [moonshot-theory](../docs/moonshot-theory.md), [w1-fpt](../docs/w1-fpt.md), [w1-structure](../docs/w1-structure.md), [w21-eth](../docs/w21-eth.md), [w18-latin](../docs/w18-latin.md), [redteam-w18-latin](../docs/redteam-w18-latin.md), [w28-sigma](../docs/w28-sigma.md), [redteam-w27-w28](../docs/redteam-w27-w28.md), [w30-sts](../docs/w30-sts.md), [redteam-w30-sts](../docs/redteam-w30-sts.md), [w34-vc](../docs/w34-vc.md), [redteam-w35-w34](../docs/redteam-w35-w34.md) · Ledger: [section 3](Results-Ledger.md#3-lower-bounds-for-specific-algorithms-and-barriers)

## HJ is tight on string isomorphism

* **AGL(k,2)** (moonshot Prop 2): HJ's `Solve` enumerates this group at the root, creating ≥ |G| ≥ 0.288·N^{1+log₂N} branches for every pair of strings, so HJ's Theorem 1.2 bound is tight *for HJ's algorithm*.
* **(F₂^{D−1} ⋊ S_D) ≀ C_m** (w1-fpt Prop 3.1): primitive and in Γ̂_D for odd D; HJ and HJ+(M′) create ≥ N^{log₂D − 0.443} children, at every fixed D. So R\*'s exponent O(log d) is tight for that algorithm, and GNS Thm 3.13's exponent cannot be o(log d).
* **G_{r,L}** (w1-structure Prop 4.2): ≥ N^{r+1−1.8/r−o(1)} branches, though FPT by another method given its tower data.

These are proofs about what the algorithm does (read from HJ's pseudocode and Lean dispatcher); they do not assume HJ correct. They **hold for string isomorphism only**, and have not been transferred to graphs. w20 adds: Prop 2 is about the dispatcher, not the problem, since Theorems A, B of [w17](../docs/w17-affine.md) beat it by a constant in the exponent.

## HJ is tight on graphs too (w18)

**Theorem B1** ([w18-latin](../docs/w18-latin.md), given HJ as written; AI red-teamed by [w26](../docs/redteam-w18-latin.md)): on the point–line incidence graph X_m of PG(m−1,2), with n ≈ 2^{2m}/6, HJ as written (every κ-subset tested, no pruning or memoization) creates at least n^{(1/8)log₂ n − O_κ(1)} recursive calls for every fixed certificate size κ ≥ 5, by a chain of nested certificate calls through the visible unaffected orbit (σx) term, not the Maróti enumeration channel.

The red-team found it **sound as a statement about HJ as written**, with one constant wrong. Its caveats matter:

* **Asymptotic only.** The theorem needs m ≥ m₀(κ, a, N₀). With κ = 64 and Lean's parameters, the enumeration cutoff is q₁ = 486290 (not q₀), there are no levels below m = 150 (n ≈ 2^297), and nesting needs m ≥ 214 (n ≈ 2^425). It says nothing about feasible inputs.
* **It bounds HJ, not GI.** X_m is a fixed geometry, easily solved by other means. It is **not a lower bound for GI**, and it assumes every recursive call of HJ answers exactly.
* **What was checked.** Hand-check of Lemmas 1 and 2, the dispatcher path and the count; exact replay of windows at κ = 3, 4, 5 with m ≤ 7. No run nests two certificate calls. The memo's own κ = 3 simulations are not exact instances of Lemma 1, and support the window shape only.

So the n^{Θ(log n)} behaviour of HJ is not confined to string isomorphism (the upper half being HJ's unrefereed theorem). It implies that a better potential cannot improve HJ; any improvement must change the certificate recursion (or prune tests).

## HJ's enumeration channel on graphs (w47, w48)

**Theorem A** ([w47-mu](../docs/w47-mu.md), given HJ as written and exact recursive answers; AI red-teamed by [w48](../docs/redteam-w47-mu.md)): on X_m, HJ reaches a `Continue` node with group GL(V)_ℓ and |GL(m−2,2)| = n^{(1/4)log₂ n − O(1)} children. Under a coordinate top partition, which is what the Lean selects, P acts on 2-subspaces, with μ = (1/8+o(1)) log₂ N and N = n². Other towers give another primitive action. This is above the n^{(1/8)log₂ n} of Theorem B1.

Its caveats matter:

* **Asymptotic only.** At κ = 64 it needs n ≥ 2^125. No run at m ≥ 64 is possible, and exact recursive answers are an assumption.
* **It bounds HJ, not GI.** X_m is easy. At this node the automorphisms F_ℓ cover all of P, so pruning collapses the children. That is a statement about one node only.
* **What was checked.** The red-team identified the group exactly for m = 5..8, checked block systems exhaustively for m = 5..7, and traced the path against the paper and the Lean.
* **Theorem C is broken as stated.** See [Corrections](Corrections.md#hjs-enumeration-channel-w47-w48).

So "enumerated quotients on graphs are small" is false for HJ as written, and this route gives no evidence that GI is easier than string isomorphism. The open question is whether any graph forces superpolynomial enumeration after pruning.

**Does it survive pruning? (w49, w51)** [w49-pruned](../docs/w49-pruned.md) builds a Cayley graph on F₂^d⊗F₂^e whose first rectangle has symmetry GL(V)×GL(U) while the whole graph has only symplectic symmetry. HJ then enumerates GL(d,2) at a node, for any resolution whose Case 2b orbital is R₁ (in the Lean, a worst-case labelling), with n ≥ 2^33280 at κ = 64. Pruning by automorphisms on one side leaves at least [GL:Sp] children.

The [red-team](../docs/redteam-w49-pruned.md) broke the claim that this holds for any pruning. Certified automorphisms act on both source and target, so one child per double coset Sp\\GL/Sp suffices, about N^{(1+o(1))/(4e)}, which is polynomial in N (exact counts 1, 3, 6, 14 for d = 2, 4, 6, 8; the classification is cited from memory). So w47's conjecture is false as literally worded, but its two-sided form stands. Even complete removal of enumeration would leave the x² and Q channels paying log N·log w ([w28](../docs/w28-sigma.md)), so this line cannot lower HJ's exponent.

## Can HJ avoid the σx channel? (w28)

[w28-sigma](../docs/w28-sigma.md) attacks the σx channel that B1 exploits. AI red-teamed by [w31](../docs/redteam-w27-w28.md), which found no claim broken and certifies neither P2, Q1 nor the conjecture below; everything assumes HJ correct, and nothing is machine-checked.

* **Lazy Step 4 (LHJ)** removes the channel on the B1 family: correctness and Lemma 7.1 survive (L1, sound given HJ after the boundary fix: escalate at ≥ ¾), and on X_m no chain is created (L2 at the root and chain states; the whole tree is a sketch; "never starts" is a statement about the root).
* **The cost moves rather than vanishes.** Unpruned LHJ on X_m still pays 2^{Ω(m²)} through anchors in the Q channel (Q1, a sketch), which is Miller's generator enumeration. Only automorphism pruning removes it on X_m (P1 proven, P2 a sketch).
* **The per-phase exponent does not change:** O(log N(log w + μ + log log N)), because x² and Q also pay log N·log w. No barrier is contradicted.
* **Memoization and canonical tests fail on X_m** (M1, M2, C1). Local equivalence of prefixes is unsound as a pruning rule (P3, after the red-team's explicit R). A prefix-determined rule either pays B1 or, on the lazy branch, Q1 (Theorem L; the lazy half is a sketch).
* **The rigid variant is not a barrier.** A single switched block does not kill Aut (correcting w18 §2.9). The corrected variant X_{m,R} still forces n^{(1/8)log₂ n − O(log log n)} calls on HJ (R1, root entry a sketch), but its rigid instances tested fell to bounded WL (m ≤ 9; experiment only).
* **Sharpest open statement:** the Uniform Prefix Conjecture (§7.3, speculation). It would make Step 4 polynomial in total under LHJ, and would still not change the exponent.

## Steiner triple systems and GL(d,2) (w30)

**T2** ([w30-sts](../docs/w30-sts.md), AI red-teamed by [w33](../docs/redteam-w30-sts.md)): linear equivalence of Boolean functions on F₂^d many-one reduces to STS isomorphism on n = 2^{d+3} − 1 points. So an n^{o(log n)} algorithm for STS (or quasigroup) isomorphism would give 2^{o(d²)} string isomorphism under GL(d,2), which ties the STS barrier to the affine barrier below. **This is an implication, not a lower bound.** No hardness of the 2^{o(d²)} question is known, and nothing shows the T2 instances are the hardest STS. On those instances the problem is decided in n^{(1/4+o(1))log₂ n} given w17 Theorem B, better than the general n^{(1/2)log₂ n} of A1.

## Classical barriers for n^{o(log n)}

An n^{o(log n)} GI algorithm would give n^{o(log n)} algorithms for all of these (moonshot §3):

* **group isomorphism**, by the O(m²)-vertex Cayley encoding (Miller 1979). Best general bound n^{c log n}, where only c has improved; Sun (2023) and IMQSZ (2024) cover p-groups of class 2 and 3-tensor isomorphism, not general groups.
* **quasigroup / Latin-square isomorphism, Steiner triple systems, conference graphs.** Best bounds still n^{O(log n)} since 1978–80 (Miller; Babai 1980).
* **affine equivalence of arbitrary colourings of F₂^k** in 2^{o(k²)} via a Θ(N³)-vertex affine-plane encoding (Prop 3). See [Moonshots](Moonshots.md#affine-equivalence-w17-w20).

The exponent factors into giant breaking (log N·log w) and enumeration of classical sections (log N·μ), each matching one of these open problems.

## Other algorithm-specific barriers

* **WL**: dimension Ω(n) on degree 3 graphs (CFI), and Ω(|V|) on binary tanglegrams.
* **Individualization-refinement**: 2^{Ω(n)} search trees for refinement within fixed-dimension WL (Neuen–Schweitzer 2018). This rules out pure IR, including this repo's front end, as a route even to quasipolynomial time.
* **Gadget-style hardness for bounded-height posets** (w27, Cor N.1): no parameterized reduction from R1_c to SI under S_b^{(P)} with P of height ≤ ℓ can reflect Aut at the identity tanglegrams. As the red-team stresses, this rules out only hardness proofs of the kind used so far; it reduces nothing to the FPT side, and does not constrain reductions that do not reflect Aut.
* **VC / ε-net proofs for conference graphs** (w34, red-teamed): separation systems have VC dimension Θ(log n), on every conference graph in one round and on iterated Turyn products for every fixed number of rounds. This obstructs that proof technique, not small hitting sets: those graphs have depth 3 at every level tested.
* **Individualization on Latin squares** (w34 §7): Latin squares of Z₂^k need individualization depth Ω(log n) by base size. It concerns individualization, not isomorphism (for which see w18 A1).
* **No lower bound is known for any class containing Luks-type coset recursion.** The only bounds are the algorithm-specific ones above. A lower bound for a coset-splitting model with or without memoization is open.

## The Clique-lower-bound barrier

W[1]-hardness of GI by degree, of TreeCI, or of tanglegrams would need a parameter blow-up g(k) ≥ 2^{k^Ω(1)}, or else GNS's n^{polylog g(k)} would solve k-Clique in f(k)n^{o(k)}. Conditional on HJ's R\*, g(k) ≥ 2^{Ω(k)}. **The hypothesis is CLIQUE-LB** (k-Clique has no f(k)n^{o(k)} algorithm), not ETH; see [Corrections](Corrections.md#the-eth-barrier).

## Attempts that stopped at these barriers

See [What we tried](Tried-and-Failed.md) and [moonshot-theory](../docs/moonshot-theory.md) §4–5: a polynomial-shrinking Split-or-Johnson would beat the 1978–80 bounds; a non-enumerative treatment of classical sections would give 2^{o(k²)} affine equivalence.
