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
| Limits of HJ's method | HJ needs ≥ N^{log₂ D − 0.45} branches on an explicit string-isomorphism family; separately, n^{(1/8)log₂ n − O(1)} calls on the PG(m−1,2) incidence graphs (w18, **not yet red-teamed**) | proven from HJ as written; the string bound AI red-teamed. A bound on HJ, not on GI | [Barriers](Math-Barriers.md) |
| Practice | on Neuen–Schweitzer multipedes we beat nauty and Traces (n = 2464: under 1.5 s vs > 600 s) | measured; answers proved by a lemma checked per instance; Traces wins on most other families | [Benchmarks](Benchmarks.md) |

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
* [Moonshots: affine equivalence, ETH, Latin squares](Moonshots.md)
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

This wiki was cut from master at `b1a2d03`. Master has since gained `w18-latin` (`860e782`, log `603bd7b`), whose results are on the relevant pages. The branches below were unfinished at that point. Pages that depend on
them say so in place. See [Maintaining](Maintaining.md) for how to fold them in.

| Branch | Commit | State | Area |
|---|---|---|---|
| `w22-speed` | `624be06` | one commit ahead of master's history (stage-loop speed); not merged | [Software](Software.md), [Benchmarks](Benchmarks.md) |
| `w23-speed2` | `4742c66` | one commit (C versions of the bounded and canonical hot paths, per its message); not merged | [Software](Software.md) |
| `w24-video-review` | `08fd28a` | no commits of its own yet (fact-check of the video); no `video/REVIEW.md` on master | [Reproduce](Reproduce.md#the-video) |
