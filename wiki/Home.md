# gi-practical: project wiki

This wiki records what the project did, what it claimed, how sure anyone is, what failed, and how to
reproduce it. It is a reference: look things up by topic rather than reading in order. The running
log is [docs/overnight-log.md](../docs/overnight-log.md); this wiki reorganizes it and the memos, and where a later
correction contradicts an earlier claim, the wiki states the later one and says so.

**The project in one paragraph.** Starting from the preprint of Hajiaghayi and JafariRaviz
(arXiv:2611.01399, "HJ"), which claims a deterministic n^{O(log n)} algorithm for graph isomorphism and
ships with a Lean formalization, the project (1) audited and built that formalization, (2) wrote an exact
Python implementation and pushed it toward practicality, (3) ran a research campaign on graph isomorphism
of graphs of maximum degree d, and (4) produced two draft papers and an animated explainer.

## Read this first

* **Nothing here has been checked by a human expert.** The work was done by AI agents. "Red-team" means an
  independent AI agent tried to break a claim. See [Disclosures](Disclosures.md).
* **Only one result is machine-checked:** HJ's main theorem, modulo 10 cited literature axioms
  ([Lean audit](Lean-Audit.md)). None of the project's own theorems is machine-checked. Some have
  brute-force checks on small cases, which test instances, not proofs.
* **No polynomial or FPT algorithm for degree-d graph isomorphism was found.** That is still open.
* Claims have been corrected many times. Before citing anything, read
  [Corrections and withdrawals](Corrections.md).

## What was claimed, in brief

| Topic | Strongest statement | Status | Page |
|---|---|---|---|
| HJ's theorem | GI in exp(C·log(n+2)²) on a log-cost RAM, with isomorphism and Aut generators | Lean kernel accepts it, modulo 10 axioms; paper unrefereed | [Lean audit](Lean-Audit.md) |
| Degree d, using HJ | GI of maximum degree d in n^{O(log(d+2))} (Corollary R\*) | conditional on HJ's analysis; one AI verifier and one AI red-team; the new accounting is not machine-checked | [Degree-d bound](Math-Degree-d.md) |
| Canonization | canonical forms for maximum degree d in n^{O((log d)^c)} (Theorem A, Corollary B) | proof modulo listed literature, depends on Babai's preliminary STOC 2019 report; three AI reviews; no expert | [Canonization](Math-Canonization.md) |
| Hypergraphs, treewidth | Theorem H (time only sketched), Theorem TW (sketch) | see ledger | [Canonization](Math-Canonization.md) |
| Exponent c, no HJ | c ≤ 10/3 for all d (Theorem X); c = 3 for all d (Theorem G) | X: AI red-teamed. G: one AI red-team pass, provisional | [Exponent](Math-Exponent.md) |
| Where hardness lives | reduction to TreeCI and tanglegram isomorphism (R1); R1 remains open | reductions proven; no algorithm, no hardness | [Core problem](Math-Core-Problem.md) |
| Limits of HJ's method | HJ needs ≥ N^{log₂ D − 0.45} branches on an explicit string-isomorphism family; separately, n^{(1/8)log₂ n − O_κ(1)} calls on the PG(m−1,2) incidence graphs (w18, Theorem B1) | proven from HJ as written; both AI red-teamed. B1 is asymptotic only: at κ = 64 it has no nested level below m ≈ 214 (n ≈ 2^425). A bound on HJ, not on GI | [Barriers](Math-Barriers.md) |
| Avoiding HJ's σ channel | a lazy Step 4 removes the B1 chain, but the cost reappears in the Q channel; the per-phase exponent does not change (w28) | **not yet red-teamed**; several parts are sketches | [Barriers](Math-Barriers.md) |
| Practice | on Neuen–Schweitzer multipedes we beat nauty and Traces from n ≈ 1100 (n = 2464: 0.34 s; nauty and Traces exceed 120 s in the latest run and exceeded 600 s in the earlier w1 run) | measured; answers proved by a lemma checked per instance; Traces wins on every other family, about 3–29× | [Benchmarks](Benchmarks.md) |

## Pages

**Results and status**
* [Results ledger](Results-Ledger.md): every theorem, bound and claim, with status, assumptions and who checked it.
* [Corrections and withdrawals](Corrections.md): everything later fixed, refuted, or found to be known.
* [Disclosures and method](Disclosures.md): how the work was done, status tags, what was not accessible.

**Mathematics**
* [The HJ algorithm and its running time](Math-HJ-Algorithm.md)
* [The Lean audit](Lean-Audit.md)
* [The n^{O(log d)} bound](Math-Degree-d.md)
* [Canonization](Math-Canonization.md)
* [The exponent c](Math-Exponent.md)
* [The core problem: TreeCI and tanglegrams](Math-Core-Problem.md)
* [Barriers](Math-Barriers.md)
* [Moonshots: affine equivalence, ETH, Latin squares, the σ channel](Moonshots.md)
* [What we tried that did not work](Tried-and-Failed.md)

**Software**
* [Software: architecture, pipelines, kernel, correctness checks](Software.md)
* [Benchmarks: tables, caveats, wins and losses](Benchmarks.md)
* [How to reproduce](Reproduce.md)

**Reference**
* [Open problems and next steps](Open-Problems.md)
* [Glossary of notation](Glossary.md), including symbols and theorem names that mean different things in different places
* [Project timeline](Timeline.md): every round, wave and worktree
* [Bibliography](Bibliography.md): what was read and what was only cited
* [Maintaining this wiki](Maintaining.md): how to update it and how to run the link check

## Work still in progress

This wiki is current to master `1368fb6`. `w18-latin`, `w22-speed`, `w23-speed2`, `w24-video-review`, `w26-redteam-pg` and `w28-sigma` are on master and folded in; `w28-sigma` is on master but has **not been red-teamed**. The branch below is the only unfinished one. Pages that depend on it say so in place. See [Maintaining](Maintaining.md) for how to fold it in.

| Branch | Commit | State | Area |
|---|---|---|---|
| `w27-tree` | `63372b5` | tanglegram moonshot (complete-tree tanglegram isomorphism R1_c, in progress). No commits of its own yet: the tip is a master commit, and its work is uncommitted in its worktree | [Core problem](Math-Core-Problem.md), [Open problems](Open-Problems.md) |
