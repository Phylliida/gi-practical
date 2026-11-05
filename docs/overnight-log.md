# Overnight campaign: improving n^{O(log d)} (started 2026-11-04)

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
