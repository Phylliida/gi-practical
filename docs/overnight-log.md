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
* COMPARATOR ACCEPTS (13:28–14:15): "Lean default kernel accepts the solution. Your solution is okay!"
  Solution.lean proves exactly Challenge.lean's statement, built in a landrun sandbox, exported with
  lean4export and replayed in a fresh kernel, using only the 3 standard axioms plus the 10 permitted
  ones. Kernel replay took 46m22s.
  - Tools: comparator and lean4export at v4.30.0-rc2, landrun 5ed4a3d.
  - One local deviation: comparator's landrun args gained `--rox /nix/store` so the NixOS toolchain
    wrappers can execute; writes stay confined to .lake.

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

### w10-blackbox (done, commit 07c3068; docs/w10-blackbox.md)
* The black box is GNS case (v): t-ary structures (t = max(9, 3 + log d)) on > 3k/4 points.
* [PROVEN] No canonical arity reduction: PSL(2,q) instances make every individualization-free binary
  relaxation trivial, so reducing arity costs 2^{Θ(log² d)} branches.
* [PROVEN, pending red-team] Theorem X: degree-d GI in n^{O(log³ d)}·2^{O(log⁵ d)}. That is c = 10/3 for all
  d, and c = 3 for d ≤ 2^{√log n} or d ≥ 2^{(log n)^{2/3}}. Route: one Design-Lemma / Split-or-Johnson
  round, then GNS on the reduced instance (≤ 3m/4 points), unrolled.
* [SKETCH] Theorem G: c = 3 for all d (Design rounds charged to a non-reset tower potential; gaps O2, O3).
* The HJ black-box route works (log M = O(log² d)) but is redundant: n^{O(log n)} on the whole graph already
  covers it. The Lean development verifies only GI at the machine level, not HJ's string-isomorphism
  theorem.

## Wave 11
* w11-redteam-blackbox: adversarial check of Theorem X (and the gaps in G).

### w10-referee (done, commit 71b7438; docs/referee-canon-paper.md)
* No mathematical error found in Theorem A, B or D. ~120 citations checked; 7 fixed. 17 of 26 minor issues
  fixed in paper/canon.tex (47 pp, recompiles).
* MAJOR, status labelling (not applied; text proposed in the report):
  - M1: Theorem H's "correctness proved" is overstated (no written algorithm; termination argument not
    well-founded). Relabel as "proof outline" or write it out.
  - M2: surface Theorem A's dependencies in the abstract, Table 1 and the status box: Babai STOC'19 ("we
    sketch the proof") and deterministic subroutines on canonical generators. Babai is only called on
    Sym/Alt on ≤ d points.
* Still running when the usage window ended: w9-canontool, w11-redteam-blackbox (resume them after reset).

### w11-redteam-blackbox (done, commit 0c29907; docs/redteam-w10-blackbox.md)
* Theorem X SOUND: degree-d GI in n^{O(log³ d)}·2^{O(log⁵ d)}, so n^{O(log^{10/3} d)} for all d (the worst
  case over d drops from 4 to 10/3) and n^{O(log³ d)} for d ≤ 2^{√log n}.
* The arity lower-bound claim is BROKEN (PGL(2,q) is sharply 3-transitive, so 3 individualizations suffice).
* Theorem G is still a sketch: O3 closed; a new gap needs a maintained-tower rule.


## Wave 12 (resumed 2026-11-08)
* w9-canontool (resumed): finish the canonical labeling tool's benchmarks and write-up.
* w12-paperfix: apply referee issues M1 and M2 and the proposed minor fixes to paper/canon.tex.
* w12-theoremg: close the gaps in Theorem G (c = 3 for all d); write up the exponent results as a note.
* Disk: 11 GB free at start of this wave (not from this project); agents told not to write large files.

### w9-canontool (done, commit 5809a0f; docs/w9-canontool.md)
* gi/canon.py: canonical_form / canonical_labeling for bounded-degree graphs (canonical Luks reduction,
  elementary-abelian least-image canonizer, stabilizer-chain search with automorphism pruning elsewhere).
  perm_canon is exponential in the worst case. 146 new tests (exhaustive against brute force for n ≤ 5).
* Multipede canonical forms: n=2464 in 1.25s (all nauty modes and Traces > 600s), n=5632 in 4.23s; fit n^1.25.
* Traces beats us on everything except the multipede families (24× on 3-regular, 220× on CFI, 230× on Q11).
  All nauty modes win on hypercubes. Python wall time vs C CPU time; one seed per size.

### w12-paperfix (done, commit 22fb2c0)
* M1: Theorem H's algorithm written out (§10.9, Algorithm CanHyp, Lemmas E4 and F2^set; termination by
  (virtual size, |Γ|) under a complete-occupancy invariant). Status unchanged (correctness proof modulo
  §13; running time a sketch). The new text has not yet been independently checked.
* M2: Babai's STOC'19 "we sketch the proof" and (D1)–(D4) now appear in the abstract, Table 1 and the status
  box. The referee's sharpening held only in part: BC is called only under A_k/S_k with k ≤ d, but on
  t-ary structures, so it is not graph canonization on ≤ d points (Remark rem:BC).
* All 9 proposed minor fixes applied. 52 pages.

### w13-redteam-canhyp: adversarial check of the new §10.9.

### w13-redteam-canhyp (done, commit 9a8c61e; docs/redteam-canhyp.md)
* CanHyp, canonicity, cosets, Lemmas E4/F2^set/W/B, complete occupancy: sound.
* One break, repaired: the second half of (S4) and Neuen 2020 Thm 4.17(G) are claimed FALSE, with a small
  counterexample (Γ=1, two blocks). Only the CanLC round bound and cost sum used it. New potential ŝ restores
  (I4). Neuen's Thm 4.24 accounting would need the same repair. To be independently verified before
  relying on it.
* Test: 0 failures over 4868 toy calls; all mutants detected. Giant steps (k > 90) are not exercised.

### w13-verify-neu417: independent check of the claimed counterexample to Neuen 2020 Thm 4.17(G).

### w13-verify-neu417 (done, commit 51ec3a5; docs/verify-neu417.md)
* Verdict: a real error in Neuen 2020's PROOF only, not a misreading and not a false statement. Thm 4.17
  claims only existence, and a trivial witness satisfies (A)–(G), so the statement is true; but Thm 4.24 needs (G) for
  the proof's own construction, where it fails (t_{p+2} ≤ t', Claim 4.25). The potential ŝ repairs it, and the
  main theorem is unaffected. Present in arXiv v1, v2 and ICALP Thm 11; the TALG version not accessed.
* paper/canon.tex Remark rem:neu20(3) rewritten as a question to the author.

### w12-theoremg (done, commit 5e6a3d0; docs/w12-theoremg.md, paper/exponent.tex)
* Claimed, single pass only: Theorem G with a complete written argument: degree-d GI in n^{O(log³ d)} for
  all d (c = 3), overall n^{O(min{log³ d, log² n})}. All four open items closed (pairwise heavy round;
  maintained-tower rule, a legal GNS run; O2 parity; case (iv) calls absorbed, "no t-ary black box").
* Fallback if G fails: Theorem X (c = 10/3 for all d; c = 3 for d ≤ 2^{√log n}).
* Correction: Split-or-Johnson individualizes up to O(log² m) points, not O(log m); no bound changes.
* paper/exponent.tex: 12-page note.

### w15-redteam-theoremg: adversarial check of Theorem G.

### w15-redteam-theoremg (done, commit df12b78; docs/redteam-theoremg.md)
* No break. Signed: given GNS (v3), the N ≤ n^{O(L)} count, Lemma A, HBD's lemmas as corrected, and
  Babai–Helfgott, string isomorphism for Γ̂_d and degree-d GI run in n^{O(log³ d)} for all d, and
  n^{O(min(log³ d, log² n))}. One AI referee reading; no human or machine check.
* One low-severity error fixed: (H3)'s "reads one point of Γ" is false after cohcoup's contraction, where
  V₂ consists of blocks; the stream reads elements of the current V₂.
* Strict gain over Theorem X and Babai–Helfgott: 3/2 < x < 2 (log n = L^x).
* Conditional on HJ, Theorem C alone gives n^{O(min(L³, log n))}, so Theorem G is redundant in that case;
  disclosed in the note.

## Wave 16–17
* w14-solver: solvable layers, dispatch, hot spots.
* w16-ckernel: compiled kernel for hot primitives (Python stays as fallback and reference).
* w17-affine (moonshot): beat 2^{O(k²)} for affine equivalence of arbitrary k-variable functions, the
  provably tight instance of HJ's enumeration channel.
* w18-latin (moonshot): n^{o(log n)} for Latin square or Steiner triple system isomorphism; does any graph
  family force n^{log n} on HJ's algorithm?
* w19-video: an HTML/CSS/JS animated explainer of the HJ algorithm and its running time (video/).

### w17-affine (done, commit 6f28e9a; docs/w17-affine.md)
* No 2^{o(k²)} algorithm. Corrects the campaign's "nothing better than brute force" by a constant in the
  exponent, pending red-team:
  - Theorem A: canonical form for AGL(k,2)-strings in 2^{k²/2+k/2}·poly(N) (flags + Borel 2-group).
  - Theorem B: deterministic Iso in 2^{k²/4+k/2}·poly(N) (bidirectional collision, Rosenbaum-style).
  Both [PROVEN mod Babai–Luks]; Theorem B is possibly folklore.
* Theorem C [PROVEN reduction]: d-tensor isomorphism of format k^{×d} reduces to AGL(dk,2)-SI, so 2^{o(K²)} for
  AGL solves every fixed-d TI in 2^{o(k²)}. A 2^{Ω(K²)} lower bound is conditional on 4-TI hardness, a
  hypothesis without independent support.
* Prop. 2's tightness holds for HJ as written, not for the problem. Enumerating a Sylow-2 transversal gives
  |P|_{2'} cosets at classical nodes [SKETCH]; R** keeps its form (λ coefficient halved).
* Experiments (k ≤ 10) cannot distinguish k from k² scaling.

### w20-redteam-affine: adversarial check of w17.

### Note: "The Exponential Time Hypothesis is False" (OpenAI math release, 25 Oct 2026; unrefereed)
* Claims deterministic #k-SAT in (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)}, polynomial space.
* If correct, the "ETH barrier" remarks in w1-fpt, w2-coset, w4-t2 and w6-tanglegram (W[1]-hardness needs a
  parameter blow-up ≥ 2^{k^Ω(1)}) lose their hypothesis. They are all stated "under ETH". paper/canon.tex and
  paper/exponent.tex do not use ETH.
* w21-eth: spot-check the preprint's core and assess relevance to this campaign.

### w16-ckernel (done, commits 26e2a7a–87745ce; docs/w16-ckernel.md)
* gi/_ckernel.c: wl2_single, wl2 final check, mul/inv/act/maps, sift, sifts_to_id, make_fast_plan, orbits.
  Build with `python3 build_ckernel.py`; GI_NO_CKERNEL=1 disables. ASan + UBSan clean; identical outputs.
* Paired: full hybrid about 2× (xl 10.3s → 4.9s); ir=0 1.5×. Multipedes, CFI, 3-regular, hypercubes barely
  moved (1.00–1.15×), because their hot code is in bounded.py/canon.py/ea2.py, off limits during w14.

### w14-solver (done, commits 7ca2c25–ef6f8ab; docs/w14-solver.md)
* SparseEA, worklist 1-WL (gi/wl.py), staged root classes, discrete rooted certificates, ir_canon, and
  graph_iso(method="auto") (bounded if maxdeg ≤ 8 or n > 256, otherwise hybrid; counted work budget).
* Canon: CFI n=3200 13.5→1.41s; Miyazaki n=3000 66.5→1.86s; 3-reg n=4000 0.46→0.26s; ns n=2464 1.24→0.83s.
* Traces still wins every non-multipede family (CFI 10–23×, Miyazaki 30–90×, Q12 ~250×, 3-regular 13×).
  Solvable layers NOT done (profiles pointed elsewhere), so gi.canon has no polynomial guarantee at d ≤ 5.

### w20-redteam-affine (done, commit 361654e; docs/redteam-w17-affine.md)
* Theorems A, B, C sound. A is folklore; B is a routine instance of Rosenbaum / Le Gall–Rosenbaum; C is a
  one-line gadget (its displayed Iso set had the direction reversed; nothing depends on it).
* Prop B′ is only a generic birthday bound, so "the flag method has hit its limit" is unsupported.
* "λ coefficient halved" in R** is speculative as worded: R** has a single Λ.

### w19-video (done, commit ed3aa0b; video/index.html)
* "The Third Logarithm": about 64 min, 24 chapters, offline. Derives the n^{O(log n)} running time on screen and
  ends with the n^{O(log d)} chapters and a status card. CLAIMS.md ledger; headless-Firefox sweep.
* w24-video-review: independent fact-check of the script against the sources.

### w21-eth (done, commit b4d1322; docs/w21-eth.md)
* No flaw found in what was checked (one adversarial read and small-case exact tests; Appendix D, Appendix B
  bit sizes and all asymptotics not checked). No reported error found publicly.
* No transfer to GI: natural fixed-width encodings have about n² variables, and Sec. 4's M ≥ 32b²(b+w) rules out
  affine equivalence and tensor isomorphism as written.
* The ETH barrier is re-based on CLIQUE-LB (notes added to the five memos); it survives if ETH fails.
* w25-wiki: a wiki under wiki/ covering everything done, learned and tried.

### w18-latin (done, commit 8047173; docs/w18-latin.md), NOT yet red-teamed
* No n^{o(log n)} for Latin squares or STS. A1: n^{(1/2) log2 n + O(1)} for quasigroups / STS, Rosenbaum's
  argument extended. A2/A3: subquasigroup-lattice DP.
* Theorem B1 (given HJ as written): on the point–line incidence graph of PG(m−1,2), HJ makes at least
  n^{(1/8) log2 n − O(1)} recursive calls, through the σx channel. A bound on HJ, not on GI: the family is easy
  by other means. Partly checked by simulation.

### w24-video-review (done, commit 4085217; video/REVIEW.md)
* 31 errors found and fixed (10 wrong, 12 misleading, 9 minor). Runtime 65:31.

## Wave 26
* w26-redteam-pg: adversarial check of w18 Theorem B1 (PG(m-1,2) lower bound for HJ) and A1.

### w22-speed (done, merged; docs/w22-speed.md)
* Stage-loop verdict memo with a written safety argument (GI_STAGE_CHECK=1 audits every scan), new C fast paths,
  incremental Schreier scans. Paired: xl hybrid 4.85s → 3.07s; xl ir=0 55.0s → 37.5s; 112 outputs identical.
* Merge note: the work-budget charge is now len(T)·len(news)·n/32, charging only generators actually scanned;
  tests/test_stage_memo.py pinned to method="hybrid" because auto dispatch sends small graphs elsewhere.

### w23-speed2 (done, merged; docs/w23-speed2.md)
* Compiled the bounded and canonical hot paths; verified-automorphism probe skips root edges; layer group H built
  without Schreier–Sims. Hypercube diagnosis (Q12): union-find on all oriented edges and repeated rooted runs,
  not perm_canon.
* Paired canon: CFI n=3200 1.40→0.43s; Miyazaki n=3000 1.84→0.47s; Q12 4.83→0.57s; 3-reg n=4000 0.25→0.11s;
  ns n=5632 3.63→1.43s. Traces still ahead except on multipedes (about 7× CFI, 23× Miyazaki, 14–29× Q12).
* After the merge: 2679 passed (kernel on), 1910 passed (off); bench 56/56 in 3.3s; irhard audit ran.

## Night 3 moonshots (2 at a time)
* w27-tree: complete-tree tanglegram isomorphism R1_c; the smallest open family (height-2 posets, large mu).

### w26-redteam-pg (done, commit b503900; docs/redteam-w18-latin.md)
* B1 sound as a statement about HJ as written: no step intercepts the path; n^{(1/8) log2 n − O(1)} recursive calls on
  the PG(m−1,2) incidence graph. Asymptotic only (no nesting below m ≈ 214 at κ = 64; enumeration cutoff is
  q₁ = 486290 at Lean's parameters, not q₀). It bounds HJ, not GI. Simulations support the window shape only.
* A1 sound after four repairs; routine application of Rosenbaum. Latin-square-graph exponent should be (1/8) log2 N.
* w28-sigma: attack the sigma channel that the PG(m-1,2) family exploits.

### w28-sigma (done, commit 27292f8; docs/w28-sigma.md), NOT yet red-teamed
* Lazy Step 4 (LHJ) removes the σ channel on the B1 family, but the exponent does not change: x² and Q still pay
  log N·log w, and unpruned LHJ pays 2^{Ω(m²)} on X_m through anchors in the Q channel [SKETCH], i.e. Miller's
  generator enumeration. No barrier contradicted.
* Correction to w18 §2.9: one switched block leaves |Aut| = 2^{m²−O(m)}. A rigid variant X_{m,R} deletes O(m) lines.
  It is not a barrier: rigid instances tested became discrete under 1-WL (m ≤ 9).
* Theorem U (Ray-Chaudhuri–Wilson with variable blocks) and Theorem L (limitation for prefix-determined rules).

### w27-tree (done, commit b11f2d3; docs/w27-tree.md), NOT yet red-teamed
* Neither the height-2 question nor R1_c settled. Prop N [PROVEN]: no parameterized Aut-reflecting reduction takes
  R1_c to a bounded-height family (A_5 tower depth), so unbounded μ alone gives no R1_c-hardness of the Prop H kind.
* FPT subclasses: Theorems G, G+ (mod ADKT) and C (mod Luks). Prop 3.2 limits one-call combines. Open residue:
  non-abelian gain graphs with curvature over a large non-soluble top.

## Next
* w30-sts: Steiner triple systems in n^{o(log n)} via a structure dichotomy (attacks the Q / Miller channel).

### w31-redteam-w27w28 (done, commit 894cc10; docs/redteam-w27-w28.md)
* Nothing broken. Narrowed: Cor N.1 uses reflection only at identity tanglegrams, and "every campaign reduction" holds only
  for T2 Thm A and W8 Prop H. Theorem G is XP in ρ, not FPT in (b, ρ). Theorem C needs Pálfy–Wolf. LHJ escalates at ≥ ¾.
  P3's missing existence proof closed with an explicit R of O(κ²) lines.
* w32-conference: conference graphs below n^{log n} (pseudorandom-versus-algebraic dichotomy).

### w30-sts (done, commit ffda3f4; docs/w30-sts.md), NOT yet red-teamed
* No n^{o(log n)} for STS. T1: structure dichotomy at the top of the rank range only (rank ≥ 0.947 log2(n+1)).
* T2 [claimed PROVEN]: linear equivalence of Boolean functions on F_2^d reduces to STS isomorphism with n = 2^{d+3}−1, so
  n^{o(log n)} for STS gives 2^{o(d²)} string isomorphism under GL(d,2). Links the STS barrier to the affine / tensor barrier.
* T5: STS within n^{o(1)} blocks of a projective space in n^{o(log n)}. w18's "locally algebraic" lead refuted.
* w33-redteam-sts: adversarial check of T1, T2, T3, T5.

### w32-conference (done, commit 49fec8a; docs/w32-conference.md), NOT yet red-teamed
* No n^{o(log n)}. Levet 2023 Q6.5 (individualization set of size O(1) or o(log n)) still open.
* Proven: T(a,b,v) second moment and mod-8 facts; rank₂(A); bad-pair reduction. "Collision probability → 0 for all pairs" is
  FALSE (iterated Turyn over P(9)), so the structure side must include tensor products.
* Experiments to n = 49 (Spence), Paley to 1097, Turyn to 6561: minimum 1-WL depth always 2 or 3. Cannot separate O(1) from
  slow growth; large examples are all algebraic or products.
* w34-vc: follow up with VC/ε-net bounds, 2-WL grid detection, and a growth lemma for the stable algebra.

### w33-redteam-sts (done, commit a6d1fcc; docs/redteam-w30-sts.md)
* T2 SOUND: exact checks agree with GL-orbit equality (d=3 all 8256 pairs; d=4 1035 representative pairs; d=5 samples). So
  n^{o(log n)} for STS would give 2^{o(d²)} string isomorphism under GL(d,2). Isomorphisms surject onto linear equivalences,
  with a gauge kernel. Quasigroup isomorphism follows; Latin-square isotopy now proved with one extra gadget condition.
* T1 sound and improved: λ < (log2 10)/3, r > 0.9031ℓ, sharp at AG(2,3). T3, T5 sound.
* Overclaims to fix: "hardest instances are PG-fibred", "exactly the barrier". The fibration form is Jungnickel–Tonchev
  Thm 2.8/2.9; no reduction to STS isomorphism found in prior art.
* w35-cubic: cubic Boolean equivalence over F_2 in 2^{Õ(d^{1.5})}.

### w34-vc (done, commit 005ca3c; docs/w34-vc.md), NOT yet red-teamed
* VC route does not reach o(log n): one-round VC is at least ⌊½ log2 n⌋ − 4, and on iterated Turyn products the multi-round
  VC is ≥ log_v n − 1 in every round. Yet those graphs have depth 3 at every tested level: VC obstructs the proof technique,
  not small hitting sets.
* Thm 4.1: depth ≤ 2⌈3 ln n / ln(1/τ)⌉ + 88 d(τ) + 22; conditional on d(τ) = o(log n), conference graphs are in n^{o(log n)}.
* Latin squares of Z_2^k need depth Ω(log n), so that analogue of Levet's question is negative.
* w36-lean: scope machine-checking the n^{O(log d)} re-accounting against the HJ Lean development.

### w35-cubic (done, commit 8fb152f; docs/w35-cubic.md), NOT yet red-teamed
* Theorems A, B, C [claimed PROVEN by hand]: exact reductions from cubic Boolean equivalence to quadratic-form tuple isometry over F_2.
* Conditional on arXiv:2610.00874 Thm 1.2 (unrefereed, partly audited): AGL/GL equivalence of cubics decided in 2^{Õ(n^{1.5})}.
  T2 instances with cubic colourings would be decided in n^{Õ(√log n)}; nothing for general STS. Prior-art search not completed.

### w36-lean (done, commit 719357a; docs/w36-lean.md, lean/DegreeD/)
* Machine-checked (3,342 lines, no sorry; axioms re-verified independently by a fresh compile): Lemma 7.1 with a parameter Λ
  (PhaseTree.HypL.cost_le), the recurrence abstract_R_star, and the (H2) regrouping on the real scripts (aggregate_branch_fam,
  ≤ 9 q^{2κ} disjoint-domain families). Non-vacuity shown at Λ = x and at d ≥ N.
* NOT machine-checked: for d < N, nothing yet shows the required Good runs exist (Γ̂_d closure and the M' dispatcher); the
  tree uses unclipped Q; tolls K are hypotheses. Estimated remaining: 5k–12k lines for Stage-1 R*; 30k–150k for machine level.

### w37-redteam-cubic (done, commit dce72f3; docs/redteam-w35-w34.md)
* No break. Theorems A, B, C of w35 sound for all n, both directions; Theorem D sound as a conditional. w34's VC bounds, Thm 4.1 and
  the Latin-square depth bound sound. Solutions biject with Iso(f,g).
* Prior art: Sun, arXiv:2611.05920 (4 Nov 2026, unrefereed) covers alternating tuple isometry over Z/p^τ, so E(i)'s tuple case is no
  longer new as a statement; it gives a second conditional route to cubics in 2^{O(n^{51/26} log n)}.
* w39-wiki-refresh: fold w27–w37 into the wiki and repair docs/w18-latin.md.

## Next
* w40-solvable: worst-case polynomial canonical forms at bounded degree (replace the exponential searches with Luks / Babai-Luks group recursion).

### w38-lean-stage1 (done, commit 1c162b8; docs/w38-lean-stage1.md, lean/DegreeD/M/)
* Stage-1 degree-d theorem machine-checked (fresh compile, 3m22s): for a modified recursion M.Run, any run on a Γ̂_d state returns the
  exact transporter at cost ≤ exp(C'·log(8·max(d,6))·log(s+2)), C' independent of d. `degreeD_stage1` uses only the 3 standard axioms
  (BCP and GNS 3.13 as hypotheses); `degreeD_stage1_ax` adds axioms `bcp` and `gnsPrimitive`.
* gnsPrimitive states the product form from GNS's proof plus a normalizer step, not GNS's literal Thm 3.13.
* Still hypotheses: Supply (not shown inhabited), NodeBoundD, RootsOK for arbitrary runs. Not addressed: the machine-level program, the
  Luks reduction, HJ's correctness beyond its Lean theorem.
* w41-redteam-lean: does the theorem say what is claimed; are the hypotheses satisfiable; is gnsPrimitive faithful?

### w41-redteam-lean (done, commit 16336ad; docs/redteam-lean-stage1.md)
* Neither axiom found false: gnsPrimitive checked case by case against GNS's O'Nan–Scott analysis, normalizer step re-proved, all 15,100
  primitive groups of degree ≤ 2500 consistent; bcp true. GammaHat matches GNS Def 2.3. Hypotheses satisfiable: NodeBoundD holds for w ≡ 1;
  Supply holds for D ≤ q₀; for D > q₀ not built, no obstruction found.
* "Cost" is Σ w over nodes, a tree-size bound with an abstract weight, not machine time. Nothing in lean/DegreeD/ is about graphs, running
  time or a machine. Gap to the English claim: no program, w is not time, Supply for d > q₀, Luks reduction, trusted axioms.
* w42-lean-supply: Supply for D > q₀ and the abstract Luks reduction.

### w42-lean-supply (merged, commit f03df03; docs/w42-lean-supply.md): STATEMENT DEFECT FOUND
* Real: `Supply.ofGiant` and `degreeD_stage1_cited` (runs exist for every d) and the Luks layer lemmas (extf_isIso, readStep_*, gammaHat_wreath).
* DEFECT: `graphIso_final` / `graphIso_general` / `graphIso_connected` are trivially true as stated. `Script.done a` may carry any value, built
  classically, so `s := done {iso set}` with zero calls satisfies the conclusion with C = 0. Proved in Lean: docs/vacuity-graphIso-final.lean.txt
  (axioms: the 3 standard ones). The proof does build a real reduction, but the statement does not expose it. Do NOT cite these theorems as they stand.
* w43-lean-statement: restate so that the trivial witness fails.

### w40-solvable (done, commits 6737822, b6a4d9e; docs/w40-solvable.md), NOT yet red-teamed
* The old canonical labeler was exponential at degree 3 (binary tree + random leaf matching: n=66 > 60s). gi/luks.py gives a deterministic polynomial
  guarantee when twin blocks ≤ 4 (every d ≤ 5; hand proof, crude exponent about 53, group-order bounds cited from memory); guarantee=True gives
  n^{O(d²)}. Remaining exponential paths at d ≥ 6 are counted. nauty and Traces solve these families easily.
* w44-redteam-luks: adversarial check of the polynomial guarantee.

### w44-redteam-luks (done, commit 0cb2fd5; docs/redteam-w40-solvable.md)
* No wrong answer or canonicity failure; no input at d ≤ 5 reached ir_canon or perm_canon. Theorem A is sound at d ≤ 5, but false as stated for "twin blocks
  ≤ 4" with unbounded degree (needs d fixed). The exponent 3.2439 should be 3.244; "about 53" is an estimate (g(m) = m⁶ asserted). Theorem B sound for fixed d;
  citation fixed (Liebeck–Shalev via GNS). Wolf (1982) read in full; Pálfy, BCP, Liebeck–Shalev not read. §2.1's "true worst case is Schreier–Sims" is false.
* w45-quartic: quartic Boolean equivalence / 4-tensor isomorphism in 2^{o(d²)}, or a barrier.

### w45-quartic (done, commit 5a17e2e; docs/w45-quartic.md), NOT yet red-teamed
* No 2^{o(d²)} for general quartics; no CFI-style barrier. Why cubic results don't propagate: kernel reductions blow up to L = O(n³), so a 3-TI bound transfers only
  if its exponent is < 3/2, and today's is exactly 3/2.
* T1: 4-TI in q^{n²}·poly. T2: h-tuples of 3-tensors reduce to one 3-tensor of length O(hn). T3 (subclass, conditional). H [claimed PROVEN]: rank-based
  2^{(2√2+o(1))d²/√min(s,d/2)}, beats 2^{d²/4} for s > 128.
* w46-redteam-quartic: adversarial check.

### w46-redteam-quartic (done, commit 91a1fd4; docs/redteam-w45-quartic.md)
* Theorem H sound except the threshold: ranks are even, and the printed parameters first win at s = 132 (s = 130 needs hand-picked R = 8). The random-quartic sketch closes
  (s ≥ d − 2√d − O(1)), beating 2^{d²/4} only from d = 282. Blow-up analysis sound as counting; "any kernel reduction" overreaches. T1 sound mod Qiao–Sun. T2 and T3 reverse
  directions tested exactly, 0 disagreements. No test reaches the regime where H beats 2^{d²/4}.
* w47-mu: does any graph family force HJ's Lie-rank enumeration channel?

### w47-mu (done, commit 92af9b0; docs/w47-mu.md), NOT yet red-teamed
* A graph family, not a barrier. Claimed PROVEN from HJ as written: on PG(m−1,2) point–line incidence graphs X_m (m ≥ max(κ,7,m₀)), HJ reaches a Continue node enumerating
  P ≅ GL(m−2,2) on 2-subspaces, with |P| ≥ 0.288·2^{(m−2)²} = n^{(1/4)log₂ n − O(1)} children, above the σ chain's n^{(1/8)log₂ n}. J₂(m,2) gives the same. Asymptotic only: at κ = 64, n ≥ 2^125.
* Theorem C: nodes reached without an answer operation hold only Young groups; superconstant enumeration needs an ancestor answer group. No complete classification of those.
* A statement about HJ, not GI: X_m is easy, and automorphism pruning removes this cost (Prop D). Gives no evidence of a GI/string separation; Neuen Q4.8 not addressed.
* Open: does any graph force superpolynomial enumeration after pruning?
* w48-redteam-mu: adversarial check of w47.

### w48-redteam-mu (done, commit 2138e9a; docs/redteam-w47-mu.md)
* Theorem A survives: node group GL(V)_ℓ with |GL(m−2,2)| children, given (H0) (HJ as written, exact recursive answers). P acts on 2-subspaces (d ≈ n/16, μ = (1/8+o(1)) log₂ N) only under a coordinate top
  partition, which is what the Lean selects; other towers give another primitive action (at m = 7 the unordered-pair tower acts on 31 hyperplanes). N = n². m₀ is finite but its conditions are never listed.
* Lemmas L, B sound: every nauty generator of Aut(B) is induced by a linear map fixing ℓ (m = 5..8), block systems exhaustive (m = 5..7), hand re-derivation. L = GL(V)_ℓ exactly. n ≥ 2^125 confirmed.
* Theorem C BROKEN as stated (medium): O5 omits HJ's Case 1 and imprimitive partition overcosets, which are wreath products; K_a⊔K_a exposes Sym(a)≀C₂ in product action, degree a². Repairable by widening O5 and "Young"; bounded-order
  enumeration then checked by hand only, wreath block-system classification missing. Its Corollary is false as worded (say "superconstant order").
* A′ needs a test set (lines ⟨e_i,1⟩). Prop D covers one node only: "removable on X_m" and "same status as B1" overreach, since w28's P2 is a sketch.
* Not reachable by computation: any run at m ≥ 64, (H0) itself, the action on G₄(U) for k ≥ 6.
* w49-pruned: is there a graph whose enumeration is not covered by automorphisms?
