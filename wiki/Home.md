# gi-practical: project wiki

This wiki records what the project did, what it claimed, how sure anyone is, what failed, and how to
reproduce it. It is a reference: look things up by topic rather than reading in order. The running
log is [docs/overnight-log.md](../docs/overnight-log.md); this wiki reorganizes it and the memos, and where a later
correction contradicts an earlier claim, the wiki states the later one and says so.

**The project in one paragraph.** Starting from the preprint of Hajiaghayi and JafariRaviz
(arXiv:2611.01399, "HJ"), which claims a deterministic n^{O(log n)} algorithm for graph isomorphism and
ships with a Lean formalization, the project (1) audited and built that formalization, (2) wrote an exact
Python implementation and pushed it toward practicality, (3) ran a research campaign on graph isomorphism
of graphs of maximum degree d, (4) produced two draft papers and an animated explainer, and (5) began formalizing its own degree-d accounting in Lean.

## Read this first

* **Nothing here has been checked by a human expert.** The work was done by AI agents. "Red-team" means an
  independent AI agent tried to break a claim. See [Disclosures](Disclosures.md).
* **What is machine-checked is narrow.** HJ's main theorem, modulo 10 cited literature axioms
  ([Lean audit](Lean-Audit.md)). Separately, parts of the project's degree-d accounting compile in
  `lean/DegreeD` with only the three standard Lean axioms: the abstract Λ bound and recurrence, the (H2)
  regrouping on the real scripts, and the real-run bound under explicit hypotheses. **For d < N nothing yet shows
  the required `Good` runs exist, so the full n^{O(log d)} theorem is still conditional and hand-argued there**
  ([details](Lean-Audit.md#the-degree-d-accounting-in-lean-w36)). No other theorem of the project is machine-checked;
  some have brute-force checks on small cases, which test instances, not proofs.
* **No polynomial or FPT algorithm for degree-d graph isomorphism was found.** That is still open.
* Claims have been corrected many times. Before citing anything, read
  [Corrections and withdrawals](Corrections.md).

## What was claimed, in brief

| Topic | Strongest statement | Status | Page |
|---|---|---|---|
| HJ's theorem | GI in exp(C·log(n+2)²) on a log-cost RAM, with isomorphism and Aut generators | Lean kernel accepts it, modulo 10 axioms; paper unrefereed | [Lean audit](Lean-Audit.md) |
| Degree d, using HJ | GI of maximum degree d in n^{O(log(d+2))} (Corollary R\*) | conditional on HJ's analysis; one AI verifier and one AI red-team. Parts of the accounting are machine-checked, the whole theorem is not: for d < N it is still hand-argued | [Degree-d bound](Math-Degree-d.md), [Lean audit](Lean-Audit.md#the-degree-d-accounting-in-lean-w36) |
| Canonization | canonical forms for maximum degree d in n^{O((log d)^c)} (Theorem A, Corollary B) | proof modulo listed literature, depends on Babai's preliminary STOC 2019 report; three AI reviews; no expert | [Canonization](Math-Canonization.md) |
| Hypergraphs, treewidth | Theorem H (time only sketched), Theorem TW (sketch) | see ledger | [Canonization](Math-Canonization.md) |
| Exponent c, no HJ | c ≤ 10/3 for all d (Theorem X); c = 3 for all d (Theorem G) | X: AI red-teamed. G: one AI red-team pass, provisional | [Exponent](Math-Exponent.md) |
| Where hardness lives | reduction to TreeCI and tanglegram isomorphism (R1); R1 remains open. Height-2 posets: not settled; FPT sub-classes and a barrier to gadget-style hardness (w27) | reductions proven; no algorithm, no hardness; w27 AI red-teamed, with Theorem G narrowed to XP in ρ | [Core problem](Math-Core-Problem.md) |
| Limits of HJ's method | HJ needs ≥ N^{log₂ D − 0.45} branches on an explicit string-isomorphism family; separately, n^{(1/8)log₂ n − O_κ(1)} calls on the PG(m−1,2) incidence graphs (w18, Theorem B1) | proven from HJ as written; both AI red-teamed. B1 is asymptotic only: at κ = 64 it has no nested level below m ≈ 214 (n ≈ 2^425). A bound on HJ, not on GI | [Barriers](Math-Barriers.md) |
| Avoiding HJ's σ channel | a lazy Step 4 removes the B1 chain, but the cost reappears in the Q channel; the per-phase exponent does not change (w28) | AI red-teamed by w31 (nothing broken; one boundary fix, one repaired existence step); several parts remain sketches | [Barriers](Math-Barriers.md) |
| Steiner triple systems | no n^{o(log n)} algorithm. An n^{o(log n)} algorithm for STS isomorphism would give 2^{o(d²)} string isomorphism under GL(d,2) (T2, w30); rank above 0.9031·log₂(n+1) forces a projective quotient (T1, improved by the red-team) | proven by hand; AI red-teamed; T2 confirmed by exact checks to d = 4. An implication, not a lower bound | [Moonshots](Moonshots.md#steiner-triple-systems-and-the-gl-barrier-w30-w33) |
| Conference graphs | no n^{o(log n)} algorithm; the VC route cannot give o(log n) depth (w34); depth 2 or 3 in every tested graph, to n = 6561 (w32) | w34 AI red-teamed; **w32 not red-teamed**; the depth figures are data only | [Moonshots](Moonshots.md#conference-graphs-w32-w34) |
| Cubic Boolean equivalence | decided in 2^{Õ(n^{1.5})} (w35), or 2^{O(n^{51/26} log n)} by a second route | **conditional** on an unrefereed preprint (arXiv:2610.00874; second route arXiv:2611.05920); the reductions are proven by hand and AI red-teamed | [Moonshots](Moonshots.md#cubic-boolean-equivalence-w35-w37) |
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
* [Moonshots: affine equivalence, ETH, Latin squares, STS, conference graphs, cubics, the σ channel](Moonshots.md)
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

This wiki is current to master `b819c8d`. Every branch through `w37-redteam-cubic` is on master and folded in. `w32-conference` is on master but has **not been red-teamed** (`w37` re-ran one of its lemmas numerically and leaned on two others; that is not a review of the memo). The branch below is the only unfinished one. Nothing in this wiki depends on it. See [Maintaining](Maintaining.md) for how to fold it in.

| Branch | Commit | State | Area |
|---|---|---|---|
| `w38-lean-stage1` | `5fb87e4` | in progress as of `5fb87e4`: continues `lean/DegreeD` toward Theorem R\*. Its commit message reports a Γ̂_d class with closure, the (M′) dispatcher and a generated run type; its worktree also has uncommitted files, so this is not its final state. Not reviewed or folded in here | [Lean audit](Lean-Audit.md), [Degree-d bound](Math-Degree-d.md) |
