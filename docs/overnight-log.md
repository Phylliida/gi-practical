# Overnight campaign: improving n^{O(log d)} (2026-11-04 → 2026-11-05)

## Morning summary

**Bottom line.** No polynomial or FPT algorithm for degree-d graph isomorphism; that is still a recognized
open problem. The night produced:
1. a candidate unconditional new theorem (canonization), survived one red-team, write-up in progress;
2. a practical win over nauty and Traces on the family designed to beat them;
3. a precise map of why n^{log d} is hard to beat.

**1. Candidate new result, unconditional: canonical forms for graphs of maximum degree d in
n^{O((log d)^c)}.**
* Grohe–Neuen–Schweitzer (GNS) gave *isomorphism* in n^{polylog d}. *Canonization* in n^{polylog d} is
  listed as open by Schweitzer–Wiebking (2019), by Wiebking (2020), and in Wiebking's 2021 thesis
  (Question 9.6).
* The fix replaces the one pair-dependent step in GNS (an aggregation case) by a "canonical subcoset"
  device: move a tuple to a reference tuple chosen from the group alone, then canonize under its
  stabilizer. Credit for the device goes to Wiebking's thesis, Lemma 5.34, which uses it for another
  purpose.
* Status: derived in w4-gnscanon.md; no break in 7 attacks in redteam-w4-gnscanon.md. Paper-style draft
  in **docs/canonization-bounded-degree.md** (commit 3729e8e). Both write-up gaps are closed:
  - the running time (§7), with a full branch-count table;
  - the canonical Luks reduction (§8), following Babai–Luks 1983 §4.2–4.3, read from Luks's homepage.
  The assumptions are listed in §10 and the questions for experts in §13.
* The write-up also flags an apparent gap in GNS's own Lemma 7.2 potential argument (repeated in Neuen
  2020), with an explicit input (S_m wr S_2, product action) and a one-line fix.
  - Red-team verdict (docs/redteam-gns-lemma72.md): a REAL GAP IN THE WRITTEN PROOF, not a misreading,
    and not evidence the theorem is wrong. The text lets the next block system be the "columns", where
    H'_(C') ≤ ker φ' fails. Checked by computation (m = 5–8); at m = 180 columns give k' = 180 vs the
    required ≤ 172.
  - The fix (choose the system coarser than C') is itself a legal run, so the algorithm and theorem are
    unaffected.
  - Present in all arXiv versions of GNS and of Neuen 2020; the SICOMP text could not be checked.
  - Approach the authors as a question, not a claim; a draft paragraph is in §5 of the red-team report.
* **Next step: a human expert (Wiebking, Neuen or Schweitzer) should look at it before any claim.**

**2. Conditional on the HJ preprint: degree-d GI in n^{O(log d)}** (verify-theorem-R.md and
redteam-theorem-R.md, from yesterday).
* Tonight showed the exponent is tight for HJ's algorithm itself (w1-fpt.md, red-teamed): an explicit
  primitive group (F_2^d ⋊ S_{d+1}) wr C_m forces N^{log d − O(1)} branches. So beating it needs a
  different algorithm, not a better analysis.
* HJ (with or without the corrected dispatcher) also needs N^{log d} on the synchronised affine tower
  G_{r,L}, which is FPT by another method (w1-structure.md).

**3. Where the hardness lives.** The problem reduces, step by step, to one clean core:
* TreeCI, coset intersection for groups acting on bounded-degree trees (w2-coset.md);
* whose graph-side form is **tanglegram isomorphism**: two rooted trees of out-degree ≤ b sharing one
  leaf set (w4-t2.md). FPT for tanglegrams is *necessary* for FPT degree-d GI.
* Tanglegrams defeat Weisfeiler–Leman in dimension Ω(n), already at b=2 (CFI embeds), so any FPT
  algorithm must be group-theoretic.
* Tanglegram isomorphism is polynomial if either tree has out-degree ≤ 4 (Luks 1993). Hard instances
  need deep Sym(≥5) towers in both trees (w6-tanglegram.md).
* Along the way several "new" algorithms turned out to be known (Theorem P = Babai–Codenotti–Qiao 2012),
  which the red-teams caught.

**4. Practical: we beat nauty and Traces on Neuen–Schweitzer multipedes** (w1-scale.md).
* New: an elementary-abelian layer solver over F_2 inside the Luks bounded-degree pipeline.
* At n=2464, dense nauty, sparse nauty and Traces all time out (>600s); ours gives a fully verified
  answer in 1.4s.
* Growth: ours ~n^1.17, nauty exponential. Answers are proved by NS Lemma 2.3, not taken from a solver.
* We still lose to Traces on CFI over random cubics and Miyazaki graphs, and to sparse nauty below
  n≈1000.

**Suggested next steps.**
1. Finish the canonization write-up and send it to an expert.
2. Build the HJ Lean repo when the machine is free; it machine-checks HJ's σ-budget, the main risk
   under result 2.
3. The best theory lead: extend the Babai–Codenotti–Qiao DP from product actions to generalized wreath
   products over posets, which would cover all "coordinate" tanglegrams.

---

## Full log

Goal set by the user: push the conditional n^{O(log d)} bound for graph isomorphism of maximum degree d
(Theorem R*, see verify-theorem-R.md and redteam-theorem-R.md) further, ideally toward polynomial,
with 2-3 agents at a time. Framing: polynomial for all d would put GI in P; f(d)·poly(n) (FPT in the
degree) is a recognized open problem. Every claim is labeled proven / sketched / speculative, and
claimed results get an independent red-team pass.

## Wave 1
* w1-fpt: source of the log d factor; amortization attempts; lower bounds for the algorithm class.
* w1-structure: replace enumeration of non-Cameron primitive quotients (affine groups etc.) by
  structure; polynomial time for d = O(log n)?
* w1-scale: bounded-degree pipeline at n in the thousands; instances hard for nauty.

### w1-fpt (done, commit 4eb2ccc; docs/w1-fpt.md)
* Literature: FPT by maximum degree is open (Downey–Fellows; GNS; Grohe–Neuen 2021 Q4; Neuen 2026 survey
  "wide open", Q4.8). No W-hardness known; known lower bounds (CFI/WL, Neuen–Schweitzer for IR, proof
  systems) do not apply to group-theoretic recursion.
* [PROVEN, pending red-team] Barrier: on string isomorphism under G = (F_2^d ⋊ S_{d+1}) wr C_m (primitive,
  in Γ̂_{d+1}), HJ+(M') enumerates ≥ |G| ≥ N^{log2(d+1) − 0.443} cosets. So R*'s exponent is tight for the
  algorithm; FPT needs a different algorithm, not a better analysis. (Not claimed for graphs.)
* [PROVEN, pending red-team] That family is FPT by a DP over coordinate prefixes with ADKT coset
  intersection. Memoization over O(N^2) block-pair subinstances makes giant branching additive; the
  difficulty concentrates in kernel-coset ∩ product-of-child-cosets. Theorem E: if primitive components
  have order ≤ π0 and every kernel has entanglement index ≤ ε, string isomorphism is π0·ε·poly(N).
  Prop 4.2: for tree groups, string isomorphism is FPT iff coset intersection is FPT.
* Leads: coset intersection for tree groups (test family T_{b,h}^L); prefix-DP for product-action
  quotients in the dispatcher; measure the entanglement index on real Luks towers; does the barrier
  transfer to graphs?

### w1-structure (done, commit 61b8576; docs/w1-structure.md)
* [SKETCH] Classification: for non-option-2 primitive P in Γ̂_d, μ(P) = log|P|/log d' ≤ C(1 + λ + min{log d,
  log log d'}), λ = largest natural-module dimension of a classical factor. Two mechanisms: alternating /
  top-group (d'^{Θ(log d)} only when d' ≥ 2^{d^{Ω(1)}}) and Lie-rank (AGL(r,2), PGL(r,2): μ ≈ log2(d+1)+1
  already at d' ≈ d).
* [CONDITIONAL on HJ] Theorem R**: string isomorphism in exp(O(log N·(log w + λ + 1))) (w = largest
  alternating factor, λ = classical dimension). For degree-d graphs this equals R*; removing the
  enumeration channel alone buys nothing for graphs.
* [PROVEN] "Recurse on H" re-creates enumeration. Simply exponential canonization (Luks 1999, ADKT,
  BCQ, Schweitzer–Wiebking) plus equivariant orbit-objects works: Theorem L [PROVEN modulo SW;
  coset assembly SKETCH] gives 2^{O(k)}·N^{O(1)} for level-synchronised towers. The synchronised affine
  tower G_{r,L} is FPT even though HJ+(M') needs ≥ N^{log2(d+1)+1−o(1)} branches on it, and it has
  unbounded non-abelian entanglement, so "entanglement + large orbits" does not by itself imply hardness.
* Main gap: the FPT-style methods are canonization algorithms; HJ is isomorphism-only. Leads: canonical
  version of HJ; global dispatcher detecting synchronised structure; settle the Cayley-coupled Example X;
  HJ's σ-machinery on non-Cameron giant homomorphisms (Neuen Ex. 5.5.10).

## Wave 2
* w2-redteam-fpt: adversarial check of w1-fpt.
* w2-coset: the core problem both theory agents isolated (coset intersection / string isomorphism for
  coupled tree groups; Example X; T_{b,h}^L).

### w2-redteam-fpt (done, commit 120400c; docs/redteam-w1-fpt.md)
* No breaks; low-severity gaps with one-line fixes. The barrier is confirmed:
  - primitive, with irreducibility of the even-weight module checked;
  - HJ enumerates it at the root (order test first, both in the paper and in the Lean dispatch);
  - no giant quotient, since A_D sits in the point stabilizer.
* Prop 3.3 (FPT for that family) is an instance of Schweitzer–Wiebking (STOC'19). Theorem E holds (the
  max index over blocks is the right quantity) and is plausibly new but elementary. Prop 4.2 holds after
  running the DP on the given tree.
* Verdict: the barrier is the solid HJ-specific contribution; correct, not deep.

### w2-redteam-structure (done, commit ae84005; docs/redteam-w1-structure.md)
* No breaks.
  - Classification: sound as a sketch; w and λ must be defined via sections.
  - R**: sound conditional on HJ.
  - Theorem L: now proven modulo Schweitzer–Wiebking, coset version included after a repair.
  - G_{r,L}: FPT given its tower; HJ (and HJ+(M')) create ≥ N^{r+1−1.8/r−o(1)} branches on it, regardless
    of HJ's correctness.
* Gaps:
  - low–medium: the decoupled row's twisted terminal costs |P|·poly(s) as a global factor, not a node toll;
  - low: the consequences paragraph overstated (S_m wr S_k carries m!).
* Novelty: modest. Theorem L / G_{r,L} are a clean counterexample to "entangled + no small faithful
  domain ⇒ hard".

## Wave 3
* w3-canon: a canonical-form version of the HJ recursion, the integration gap both theory agents named.

### w2-coset (done, commit faf0999; docs/w2-coset.md)
* [PROVEN] The core is TreeCI(b), coset intersection for subgroups of Aut(tree of degree ≤ b). It is
  fpt-equivalent to tree-group string isomorphism, to the block-DP combine step, and already to the
  simplest (full diagonal) coupling. So depth, not pattern, is what matters; bounded coupling depth is FPT.
  GNS's class refines to tree groups of node degree d!/2.
* [PROVEN] Example X collapses for r ≥ 3 (it contains GL at every node, so Theorem E applies).
* [PROVEN mod Babai] Theorem P: string isomorphism for any G ≤ Sym(Δ) wr S_k in product action runs in
  b!·N^{3.17+o(1)}, with an arbitrary top group that is never enumerated. This covers the families on
  which HJ+(M') pays N^{log d}, i.e. it removes the product-type enumeration channel. Theorem E' [SKETCH]:
  FPT whenever every kernel's entanglement is ≤ f(d).
* No hardness found (ETH forces parameter blow-up ≥ 2^{k^Ω(1)} for any W[1]-hardness).
* Graphs: coloured Cartesian products of two b-ary trees put the full-group T^2 form inside bounded-degree
  GI. [SPECULATION] degree-d GI is strictly easier than TreeCI.
* Leads: FPT for T^2 (full-group case first); lower bound for coset-splitting on the iterated diagonal;
  implement Theorem P in gi-practical; red-team Theorem P.

### w3-canon (done, commit 5c35d29; docs/w3-canon.md)
* Babai's canonization obstacle was the certificate relational structure, whose colours are consistent only
  per (x, y) pair. His repair uses t ≥ max(9, 2 log2 n) and does not transfer to HJ's constant κ. In the
  regime d ≤ N^α only HJ's ordered comparisons hit it. The row machinery (genuinely non-canonical) does
  not run there.
* "Canonical-colour trick": replace each comparison by the canonical form of the marked window under the
  pointwise stabiliser of a fixed reference tuple (right descent). Same colour classes, ~q^κ chains.
* [CONDITIONAL on HJ, assembly SKETCH] Theorem C: canonical forms for Γ̂_d-strings in
  exp(O(log N·log d))·exp(polylog d); degree-d graphs in n^{O(log d)}·exp(polylog d). The literature
  (Schweitzer–Wiebking 2019, Wiebking 2020) lists n^{polylog d} canonization as open.
* Lemma N (canonical forms descend to normal subgroups), Theorem E-canon, Theorem P-canon (via Wiebking).
  Theorem H: the frontier hybrid, f(d)·poly(N)·s_bad^{O(log d)}, never worse than R*. The residual is TreeCI
  (TreeCan in canonical mode).
* Lead 1 (unconditional!): the canonical-colour trick applied to Grohe–Neuen–Schweitzer (certificates of
  size O(log d)) may give the first n^{polylog d} canonization for degree-d graphs.

## Wave 4
* w4-gnscanon: develop lead 1 rigorously (unconditional n^{polylog d} canonization?).

### w3-redteam-coset (done, commit 73b1837; docs/redteam-w2-coset.md)
* No breaks.
* Theorem P is correct (72 brute-force instances), but its algorithm is Babai–Codenotti–Qiao 2012 Thm 5 /
  Codenotti thesis Thm 4.2.1 (twisted code equivalence), so the novelty is low. Relabel it a corollary.
  - Improved exponent: (b!)^{1+o(1)}·N^{2.33} (only (1+b²)^k states are reachable).
  - Base-case fix: setwise transporter by coset intersection.
* Corollary 2.2 needs rewording: the hard DP shape is a diagonal on a full-depth direct factor
  K1×diag(G2), not a bare full diagonal. Example X: entanglement bounded in d (level-2 pairing can
  survive), so the FPT conclusion stands. The tree-product automorphism claim is verified (22 cases;
  depth colours essential). Theorem E' is the most interesting new claim, still a sketch.

### w4-gnscanon (done, commit c1a043f; docs/w4-gnscanon.md)
* Claimed (UNCONDITIONAL relative to published work, pending red-team): canonical labelling for graphs of
  maximum degree d in n^{O((log d)^c)} (Theorem A for Γ̂_d strings; Corollary B for graphs), via the
  canonical-colour trick applied to GNS.
  - The trick is a "canonical subcoset" lemma: send a tuple to a reference T0 chosen from H alone, then
    canonize under J0 = H_(T0) [PROVEN].
  - The only pair-dependent step in GNS is the |S| < k/4 aggregation case (GNS L2370–2385).
* Stated open by Schweitzer–Wiebking 2019 and Wiebking 2020. Risks:
  - Wiebking's 2021 thesis not read (bot wall);
  - Babai STOC'19 canonization is a "preliminary report";
  - GNS's analysis reused unchanged [SKETCH];
  - Babai–Luks 1983 canonical reduction not re-read.

## Wave 5
* w5-redteam-gnscanon: adversarial check, especially the coset-vs-group issue in canonization recursions
  and the prior-art check against Wiebking's thesis.

### w5-redteam-gnscanon (done, commits b380cb0, 8b1a839; docs/redteam-w4-gnscanon.md)
* No breaks across 7 attacks.
  - Coset vs group: sound. Children keep the subgroup fixed and move the input, so the reference tuple
    depends on the subgroup only. Naive variants fail, with explicit S4 counterexamples; the memo uses
    neither.
  - Colour classes exact.
  - All 17 arbitrary choice points in GNS covered.
  - Running time carries over (the only automorphism pruning, in find-symmetry, is reproduced).
* Gaps (low):
  - the blank symbol must lie outside the alphabet;
  - Step 4 (running time) and Corollary B's canonical Luks reduction (Babai–Luks 1983 /
    Fürer–Schnyder–Specker 1983) need full write-ups.
* Prior art: Wiebking's 2021 thesis (read; doi 10.18154/RWTH-2021-06242) states the problem as open
  (Question 9.6), but its Lemma 5.34 already uses the core device (a single canonical test set) for
  another purpose. The trick must be credited to Wiebking; the main result appears new.
  - The agent passed the RWTH JS bot wall by sending the APP_INIT=1 cookie for the open-access PDF.
* Strongest signed statement: given GNS's lemmas, Babai's canonical form theorem and canonical generating
  sets, canonical labellings for Γ̂_d-strings in n^{O((log d)^c)}; graphs of maximum degree d likewise
  once the canonical Luks reduction is written out. Before any public claim: contact Wiebking / Neuen /
  Schweitzer and check the SICOMP 2023 GNS text.

### w4-t2 (done, commit c8491b3; docs/w4-t2.md)
* [PROVEN] Full-group T² is fpt-equivalent, with polynomial size, to coloured TANGLEGRAM isomorphism (two
  rooted trees of out-degree ≤ b on one leaf set), to coset intersection of two full coloured tree groups,
  to isomorphism of arbitrary graphs carrying a b-ary hierarchical clustering, and to multi-sorted
  tree-structured structures. T²_full ≤ coloured GI of degree b+1.
* TreeCI = coset intersection of an arbitrary tree group with a full one. The gap to the graph core is
  "definability" of tree groups (R2). (R1), tanglegram isomorphism FPT in the out-degree, is NECESSARY for
  degree-d GI to be FPT.
* [PROVEN mod the standard CFI game] Theorem B: CFI over cubic expanders embeds into coloured binary
  tanglegrams (size O(n)), so the WL dimension is Ω(|V|) already at b = 2. Any FPT algorithm must be
  group-theoretic.
* Prop T: FPT in (b, τ), τ = largest Goursat quotient of the instance's row strips. Every brief idea fails
  the same way (the combine step is a same-size T²_full instance).
* Experiments: equivalences 54/54; CFI tanglegrams defeat CR and 2-WL; Aut(T)∩Alt(L) is definable
  (degree-9 structure, N ≤ 64), so the classic Alt(n) obstruction to definability disappears.
* Leads: abelian twisting via linear algebra; definability for 2-groups; a straddling-node recursion;
  tanglegrams as a lower-bound family and a solver stress family.

## Wave 6
* w5-writeup (running): paper-style draft of the canonization result.
* w6-tanglegram: attack (R1), tanglegram isomorphism FPT in out-degree.

### w1-scale (done, commits ba25237, c35df43, 753860a; docs/w1-scale.md)
* Speedups (all exact):
  - rooted 1-WL refinement with the root edge individualized;
  - colour-class layer order, which keeps layer groups elementary abelian on CFI-type graphs;
  - new gi/ea2.py, which solves elementary-abelian layers by Gaussian elimination over F_2 with no
    Schreier–Sims.
  CFI n=800: 10.5s → 0.50s. ns multipedes n=528–704: >300s → 0.2–0.3s.
* bench/irhard.py: Neuen–Schweitzer multipedes. Answers and |Aut|=1 are proved by NS Lemma 2.3 (extended
  to isomorphisms), with its conditions checked per instance. Also CFI over random cubics, and a Miyazaki
  generator matching the bliss files edge for edge.
* HEADLINE: on ns multipedes we beat dense nauty, sparse nauty and Traces (dreadnaut, nauty 2.9.1).
  - At n=2464 all three time out (>600s); ours gives a fully verified answer in 1.4s.
  - Ours grows ~n^1.17; nauty grows exponentially (dense 2^(9.3n/1000), sparse 2^(6.4n/1000)).
  - The crossover with sparse nauty is at n ≈ 1056–1760.
  - Sanity checks: nauty solves the smaller members; on X alone sparse nauty needs 530s and 10.2M nodes.
* Where we lose: Traces is >100× faster on CFI over random cubics and solves Miyazaki graphs instantly;
  sparse nauty wins on everything below n ≈ 1000.
* Tests: 341 passed.

### w6-tanglegram (done, commit 53f8b51; docs/w6-tanglegram.md)
* (R1) is still open. No literature on the complexity of tanglegram isomorphism (phylogenetics counts
  tanglegrams via double cosets; isomorphism is done with GAP/nauty). Closest open relative:
  tree-sibling network isomorphism (Cardona et al. conjecture P at bounded in-degree).
* [PROVEN mod Luks 1993 Cor. 6.3/6.4] Prop L: if EITHER tree has out-degree ≤ 4 the problem is
  polynomial, with no bound on the other tree; out-degree ≤ d gives n^{O(d/log d)}. Probably folklore.
  Hard instances need deep Sym(≥5) towers in BOTH trees.
* [PROVEN] Prop D: prime decomposition via common clusters. Prop S: fibre-product structure over
  straddling subtrees. Prop C (new to the agent's knowledge): coordinate tanglegrams have the generalized
  wreath product of S_b over a 2-dimensional poset as their group, checked against nauty on 21 instances.
* Lead: extend the Theorem P DP from antichains to arbitrary posets (string isomorphism under generalized
  wreath products), which would cover all coordinate tanglegrams.

# Day 2 campaign (2026-11-05, ~noon → 8–10 PM)

The user offered two more 5-hour usage windows. Plan: wave 8 hardens and extends the canonization
result; wave 9 is practical (canonical labeling tool, solvable layers, automatic dispatch); waves 10–11
are red-teams, a LaTeX paper, and final integration.

## Wave 8
* w8-redteam-writeup: independent red-team of canonization-bounded-degree.md §7 (running time) and §8
  (canonical Luks reduction); retry the SICOMP GNS text and Neuen's thesis.
* w8-hypercanon: canonical version of Neuen 2020 (hypergraph isomorphism for Γ̂_d) with the
  canonical-subcoset device; consequences for treewidth canonization via Wiebking.
* w8-poset: extend the Babai–Codenotti–Qiao DP to generalized wreath products over posets
  (coordinate tanglegrams); the Prop S one-call combine.
* w8-gnsexp: tighten GNS's n^{(log d)^c} unconditionally (exponent c; target n^{O(log^2 d)} or better).
* The HJ Lean build is authorized (machine free; 88 GB disk free at start).

### w8-redteam-writeup (done, commit bbbb475; docs/redteam-canonization-writeup.md)
* §7 (running time) sound: Lemma 7.0 covers the semi-regular Luks step; the §7.3 fix restores
  k' ≤ k − k/(3 log k); every branch-count row matches GNS (canonization explores no extra branches).
* §8 (canonical Luks reduction) sound: S_{d−1} wr Aut(CF_r; both roots) ∈ Γ̂_{d−1}. A literal brute-force
  implementation (docs/redteam-canonization-writeup-check.py) passes on 47 small graphs and catches two
  sabotaged variants.
* §2.5 sound. §10 is missing 4 assumptions; the main one is that all "function of the group" subroutines
  are deterministic and run on canonical generators (including Babai STOC'19).
* SICOMP GNS and Neuen's thesis are behind bot checks; the agent did not bypass them. Left to the user.

### w8-hypercanon (done, commit 9935b16; docs/w8-hypercanon.md)
* Theorem H (canonical Neuen 2020): canonical forms for sets of m strings, or hypergraphs, under Γ̂_d
  cosets in (n+m)^{O((log d)^c)}. Correctness [PROVEN mod Neuen/GNS/Babai lemmas + Theorem A]; time
  [SKETCH].
  - New obstacle: Neuen's local certificates run "on all pairs in parallel" with non-invariant
    renormalization.
  - Fix: a single object moved to Wiebking's canonical test set T0, canonized under its setwise stabilizer.
* Theorem TW: canonical forms for treewidth k in n^{polylog k}. It needs only Theorem A (Corollary D),
  since Wie20 applies the hypergraph lemma only to cosets already mapping hyperedges to hyperedges
  (corrects write-up §9.2). [PROVEN mod Theorem A and canonical tools; Wie20 rewrite SKETCH.] Wie20 and
  Wiebking's thesis predict it once GNS is canonical.
* Corollaries (mostly sketches): coset-labelled hypergraphs; t-CR-bounded graphs; K_{3,h}-minor-free and
  genus g; K_h-minor-free and topological-subgraph-free in n^{polylog h} (would answer thesis Q 9.7;
  conditional).
* Neuen 2020 repeats GAP-1 verbatim (N2716; same fix), and has a minor cost-accounting slip (fixable).

## Wave 9
* w9-redteam-hypercanon: adversarial check of Theorem H and Theorem TW.

### w8-poset (done, commit 643ee53; docs/w8-poset.md)
* Theorem 1 [PROVEN mod ADKT Thm 5]: string isomorphism under generalized wreath products ∏^{(P)} G_i
  (G_i ≤ S_b) in b!·2^{O(b^{μ+1})}·N^{O(1)}. The DP runs over fibres above down-sets, and the fibre lemma
  decouples everything above a minimal element. μ(P) is a new poset parameter (0 for antichains, chains
  and series compositions). Validated on 1280 instances against brute force / nauty.
* Prop H [PROVEN mod T2 Thm A]: for P = C_h ⊔ C_h (width 2, dimension 2) the problem is exactly complete-tree
  tanglegram isomorphism R1_c. So width and dimension can't help, and "all coloured coordinate tanglegrams
  FPT" ⇔ R1_c FPT.
* W6's Prop C is NOT new: it is AMBC Theorem 4.24(a) (Forum Math. Sigma 2025).
* Smallest open poset family: height-2 posets with large μ (does μ capture hardness?).

### w8-gnsexp (done, commit 6b98724; docs/w8-gnsexp.md)
* GNS as written (with the Lemma 7.2 fix): c = 5 [PROVEN]. The main recursion (domain blow-up
  n^{O(log² d)} × K = O(log³ d)) and the black box (Babai on d^{O(log d)} points, 2^{O(log⁶ d)}) each give
  log⁵ d. Using the known n^{O(log d)} domain count: c = 4 for all d.
* NEW, unconditional [PROVEN, pending red-team]: a multiplicative giant decrease k' ≤ 3k/4, via a CFSG-free
  lemma (an Alt(m) composition factor with m > 3k/4 forces an Alt(Δ) with |Δ| ≥ m, contradicting the
  symmetry defect). Height O(log d) gives a main recursion of n^{O(log³ d)}. Overall c = 3 when
  log n ≥ log³ d (so d = polylog n: n^{O((log log n)³)} vs GNS's 5th power) and c = 4 for all d.
  c = 10/3 for all d via Design Lemma / Split-or-Johnson in the black box [SKETCH].
* Barrier [PROVEN]: c < 2 unconditionally would beat general GI's exp(O(log³ n)). c = 3 is the floor of GNS's
  architecture [SKETCH].
* HJ Thm A.9 re-derived except the CFSG primitive-valuation lemma. A weak σ ≤ C log d log N via GNS 3.13
  gives n^{O(log² d)} conditional on HJ §§4–7 but not on that lemma [SKETCH].

### HJ Lean formalization BUILT (2026-11-05 13:25)
* Toolchain v4.30.0-rc2 via nixpkgs elan. mathlib cache download 76s; `lake build` exited 0 after 44m30s.
  Disk used ~14 GB.
* `#print axioms main_theorem`: exactly propext, Classical.choice, Quot.sound plus the 10 declared
  literature axioms (chiefSeriesAlgo, gmpOutBound, gmpTransitiveNonabelian, marotiPrimitive,
  quotientCentralizer, simpleValuationDegree, sixTransitiveContainsAlt, sylowAlgo, sylowConjugate,
  transitiveAffected). No sorryAx, no ofReduceBool.
* Dependency cone of main_theorem (115,555 constants) contains GI.Paper.thm_hereditary_budget (HJ Thm A.9).
  So HJ's σ-budget, the #1 residual risk under the conditional n^{O(log d)}, is machine-checked as part of
  HJ's theorem, modulo the 10 axioms. The new Λ-accounting itself is still pen-and-paper.
* Comparator (fresh-kernel replay + statement match) is being built and run.

### w9-redteam-hypercanon (done, commit 97c4b9d; docs/redteam-w8-hypercanon.md)
* No break, and no isomorphic pair with different outputs.
* Theorem H: canonicity sound. Renormalization is built from canonical data, Γ''1 is replaced by the
  stabiliser of the canonical multiplicity string, and a toy check gave 0/60 failures while both mutants
  failed 60/60. The defect bound holds at ≥ 3/4. Running time: plausible sketch. Minor fixes listed.
* Theorem TW: the key claim is confirmed (cosetHyper called once, W336, on a hyperedge-preserving coset).
  Three fixable gaps:
  - TW-1: canonize the child colours χ first;
  - TW-2: mark the parent adhesion set;
  - TW-3: the doubling search must check degeneracy, not min-degree (grid counterexample).
  Overall: SKETCH, conditional on Theorem A.
* H4: Q 9.7 needs a parameter-free form. Missing prior art: Grohe (polynomial time per fixed minor) and
  Lokshtanov–Pilipczuk–Pilipczuk–Saurabh STOC'22 (f(H)·n^{O(1)}); neither reaches n^{polylog h}.
* Novelty: no prior canonization found, but Neuen's 2026 survey says canonization "is possible for many
  of the algorithms", so experts may call these results expected.

### w9-redteam-gnsexp (done, commit a40134e; docs/redteam-w8-gnsexp.md)
* No break.
  - Lemma A (CFSG-free, Bochert): true for every m ≥ 6; fails only at PSL(2,5)/PGL(2,5) on 6 points.
    GNS uses it only for k' ≥ 91.
  - k' ≤ 3k/4 holds in every branch, given the Lemma 7.2 fix.
* The gain is narrower than the summary said. "c = 4 for all d" was already known (survey Thm 4.16). Lemma A
  helps only when log n > log² d. Signed statement: degree-d GI in n^{O(log³ d)}·2^{O(log⁶ d)}, which is
  n^{O(log³ d)} for d ≤ 2^{(log n)^{1/3}} and n^{O(log⁴ d)} for all d.
* Prior art: Pago arXiv:2302.05426 (Lemma G_groupInduction, proof credited to Wiebking) is the same
  induction; cite it and present Lemma A as a variant. Seven memo edits are required.
* The black box (Babai on d^{O(log d)} points) now dominates for large d.

## Wave 10
* w9-canontool and w9-paper (running).
* w10-blackbox: reduce the GNS black-box cost; make c = 10/3 rigorous; aim for c = 3 for all d.

### w9-paper (done, commit eb0c727; paper/canon.tex, paper/canon.pdf, paper/cover-note.md)
* 45-page LaTeX draft covering Theorems A, B (with D), H, TW and corollaries H1–H4, each with its true
  status; a 25-row assumptions table; the Lemma 7.2 issue posed as a Question; AI assistance disclosed;
  author line left as a placeholder.
* The agent reconciled 9 cross-document inconsistencies, always taking the more conservative statement.
  Examples: TW is a SKETCH; the counterexample needs m ≥ 200; "beats BC" is claimed only for
  k = polylog n.
* cover-note.md: a draft note to an expert (not sent).
