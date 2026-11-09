# Project timeline

All dates are 2026. Branches are in `git branch -a`; worktrees are at `~/math/gi-practical-wt/<branch>`. Commit is the branch tip. "Rounds" are the Python implementation work (r1–r4), "waves" the campaign (w1–w24). Wave numbers follow the branch names; [overnight-log.md](../docs/overnight-log.md) groups a few of them differently.

[Home](Home.md)

## Before the repository

* **3 Nov.** Read-only audit of the Lean formalization `~/math/GraphIsomorphismLog2` of HJ. Trusted base and axioms read; build deferred because the user was benchmarking. See [Lean audit](Lean-Audit.md).

## 4 November: implementation rounds

Baseline `44c90a3`: a minimal Python implementation of HJ's recursion. Baseline solves 14/29 with the mislabeled `3reg12-pair` counted correct; `9180532` fixes it.

| Round | Branch | Commit | What | Result |
|---|---|---|---|---|
| 1 | r1-engine | `e23cfb3` | faster exact Schreier–Sims and homomorphisms | merged |
| 1 | r1-branch | `2a82183` | branching economy (Sym giants, pruning, memo) | certificates never helped |
| 1 | r1-refine | `d4da12b` | joint 2-WL front end, staged orbit chain, bounded individualization | 29/29 in 4.4 s after merge |
| 2 | r2-dispatch | `768e074` | verified Johnson/product recognition, abstract giants, Johnson/Hamming step | |
| 2 | r2-aggregate | `ba2d9ea` | Young-label step | |
| 2 | r2-hybrid | `fb24582` | budgeted levels, chunked stages, VF2/pynauty reference | 56/56 in 16 s, about 1000× behind nauty |
| 3 | r3-practical | `1475f21` | explicit chains, work budget | [README](../README.md) tables |
| 3 | r3-theory | `dcd2519` | [moonshot-theory](../docs/moonshot-theory.md): dissection of n^{O(log n)}; Theorem R | no route below n^{log n} |
| 3 | r3-hardness | `0e0f9d2` | [hardness](../docs/hardness.md) | planes blow up by one heuristic |
| 4 | r4-implement | `4ed21c3` | [bounded](../docs/bounded-degree.md) pipeline | Luks layer step in code |
| 4 | r4-verify | `b2f03ee` | [verify-theorem-R](../docs/verify-theorem-R.md) | Theorem R\* |
| 4 | r4-redteam | `e93c7de` | [redteam-theorem-R](../docs/redteam-theorem-R.md) | no hole outside (H0) |

## Overnight campaign (4–5 Nov): pushing n^{O(log d)}

| Wave | Branch | Commit | What | Memo |
|---|---|---|---|---|
| 1 | w1-fpt | `4eb2ccc` | FPT status; HJ tightness; Theorem E | [w1-fpt](../docs/w1-fpt.md) |
| 1 | w1-structure | `61b8576` | enumeration channel; Theorem L | [w1-structure](../docs/w1-structure.md) |
| 1 | w1-scale | `753860a` | ea2, multipedes against nauty and Traces | [w1-scale](../docs/w1-scale.md) |
| 2 | w2-redteam-fpt | `120400c` | red-team | [report](../docs/redteam-w1-fpt.md) |
| 2 | w2-redteam-structure | `ae84005` | red-team | [report](../docs/redteam-w1-structure.md) |
| 2 | w2-coset | `faf0999` | TreeCI core, Theorem P | [w2-coset](../docs/w2-coset.md) |
| 3 | w3-redteam-coset | `73b1837` | Theorem P = BCQ | [report](../docs/redteam-w2-coset.md) |
| 3 | w3-canon | `5c35d29` | canonical HJ, Theorem H (hybrid) | [w3-canon](../docs/w3-canon.md) |
| 4 | w4-gnscanon | `c1a043f` | Lemma T, Theorem A | [w4-gnscanon](../docs/w4-gnscanon.md) |
| 4 | w4-t2 | `c8491b3` | tanglegrams, T² | [w4-t2](../docs/w4-t2.md) |
| 5 | w5-redteam-gnscanon | `8b1a839` | red-team; RWTH thesis read | [report](../docs/redteam-w4-gnscanon.md) |
| 5 | w5-writeup | `3729e8e` | paper-style draft | [write-up](../docs/canonization-bounded-degree.md) |
| 6 | w6-tanglegram | `53f8b51` | R1, Prop L, Prop C | [w6-tanglegram](../docs/w6-tanglegram.md) |
| 7 | w7-redteam-gns72 | `3e83459` | GAP-1 | [report](../docs/redteam-gns-lemma72.md) |

## Day 2 (5 Nov)

| Wave | Branch | Commit | What | Memo |
|---|---|---|---|---|
| 8 | w8-redteam-writeup | `bbbb475` | §7, §8 of the write-up | [report](../docs/redteam-canonization-writeup.md) |
| 8 | w8-hypercanon | `9935b16` | Theorem H, TW | [w8-hypercanon](../docs/w8-hypercanon.md) |
| 8 | w8-poset | `643ee53` | generalized wreath products | [w8-poset](../docs/w8-poset.md) |
| 8 | w8-gnsexp | `6b98724` | exponent c | [w8-gnsexp](../docs/w8-gnsexp.md) |
| — | (no branch) | `3763308`, `f1b93c1` | HJ Lean built and accepted by comparator | [Lean audit](Lean-Audit.md) |
| 9 | w9-redteam-hypercanon | `97c4b9d` | red-team | [report](../docs/redteam-w8-hypercanon.md) |
| 9 | w9-redteam-gnsexp | `a40134e` | red-team | [report](../docs/redteam-w8-gnsexp.md) |
| 9 | w9-paper | `eb0c727` | [canon.tex](../paper/canon.tex) draft | |
| 9 | w9-canontool | `5809a0f` | canonical labeling tool (finished on 8 Nov) | [w9-canontool](../docs/w9-canontool.md) |
| 10 | w10-blackbox | `07c3068` | Theorem X | [w10-blackbox](../docs/w10-blackbox.md) |
| 10 | w10-referee | `71b7438` | whole-paper review | [report](../docs/referee-canon-paper.md) |
| 11 | w11-redteam-blackbox | `0c29907` | red-team; arity claim refuted | [report](../docs/redteam-w10-blackbox.md) |

The usage window ended during wave 11; work resumed on 8 Nov.

## 8 November

| Wave | Branch | Commit | What | Memo |
|---|---|---|---|---|
| 12 | w12-paperfix | `22fb2c0` | M1, M2, minor fixes | [canon.tex](../paper/canon.tex) |
| 12 | w12-theoremg | `5e6a3d0` | Theorem G | [w12-theoremg](../docs/w12-theoremg.md), [exponent.tex](../paper/exponent.tex) |
| 13 | w13-redteam-canhyp | `9a8c61e` | CanHyp red-team | [report](../docs/redteam-canhyp.md) |
| 13 | w13-verify-neu417 | `51ec3a5` | Neuen 4.17(G) | [report](../docs/verify-neu417.md) |
| 14 | w14-solver | `ef6f8ab` | dispatch, sparse EA, worklist WL | [w14-solver](../docs/w14-solver.md) |
| 15 | w15-redteam-theoremg | `df12b78` | red-team | [report](../docs/redteam-theoremg.md) |
| 16 | w16-ckernel | `87745ce` | C kernel | [w16-ckernel](../docs/w16-ckernel.md) |
| 17 | w17-affine | `6f28e9a` | affine moonshot | [w17-affine](../docs/w17-affine.md) |
| 18 | w18-latin | `8047173` | Latin-square moonshot; Theorem B1 (merged `860e782`; not yet red-teamed) | [Moonshots](Moonshots.md) |
| 19 | w19-video | `ed3aa0b` | video | [CLAIMS](../video/CLAIMS.md) |
| 20 | w20-redteam-affine | `361654e` | red-team | [report](../docs/redteam-w17-affine.md) |
| 21 | w21-eth | `b4d1322` | ETH preprint review | [w21-eth](../docs/w21-eth.md) |
| 22 | w22-speed | `624be06` | stage-loop speed (**in progress**, unmerged) | [Software](Software.md) |
| 23 | w23-speed2 | `4742c66` | bounded-path compilation (**in progress**, unmerged) | [Software](Software.md) |
| 24 | w24-video-review | `08fd28a` | video fact-check (**in progress**) | [Reproduce](Reproduce.md#the-video) |
| 25 | w25-wiki | this branch | this wiki | |

This wiki was cut from master at `b1a2d03`; master later reached `603bd7b` with the w18 merge.
