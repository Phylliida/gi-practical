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
