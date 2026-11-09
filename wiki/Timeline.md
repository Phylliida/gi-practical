# Project timeline

All dates are 2026. Branches are in `git branch -a`; worktrees are at `~/math/gi-practical-wt/<branch>`. Commit is the branch tip. "Rounds" are the Python implementation work (r1–r4), "waves" the campaign (w1–w39). Wave numbers follow the branch names; [overnight-log.md](../docs/overnight-log.md) groups a few of them differently.

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
| 18 | w18-latin | `8047173` | Latin-square moonshot; Theorem B1 (merged `860e782`; red-teamed by w26) | [w18-latin](../docs/w18-latin.md), [Moonshots](Moonshots.md) |
| 19 | w19-video | `ed3aa0b` | video | [CLAIMS](../video/CLAIMS.md) |
| 20 | w20-redteam-affine | `361654e` | red-team | [report](../docs/redteam-w17-affine.md) |
| 21 | w21-eth | `b4d1322` | ETH preprint review | [w21-eth](../docs/w21-eth.md) |
| 22 | w22-speed | `2f79977` | stage-loop speed and cheaper Schreier–Sims (merged `66f11ee`) | [w22-speed](../docs/w22-speed.md) |
| 23 | w23-speed2 | `e89e417` | bounded and canonical hot paths compiled (merged `04fb3ea`) | [w23-speed2](../docs/w23-speed2.md) |
| 24 | w24-video-review | `4085217` | video fact-check, 31 errors fixed (merged `6dad6a2`) | [REVIEW](../video/REVIEW.md), [Reproduce](Reproduce.md#the-video) |
| 25 | w25-wiki | `df455f8` | this wiki (merged `1645773`) | |
| 26 | w26-redteam-pg | `b503900` | red-team of w18 (B1, A1–A3, sketches); merged `ad9c9ef` | [report](../docs/redteam-w18-latin.md) |
| 27 | w27-tree | `b11f2d3` | height-2 posets and R1_c moonshot; neither settled (merged `15b522a`; commit at 00:07 on 9 Nov; red-teamed by w31) | [w27-tree](../docs/w27-tree.md), [Core problem](Math-Core-Problem.md) |
| 28 | w28-sigma | `27292f8` | attempts to remove HJ's σ channel; on master (commit at 00:03 on 9 Nov; red-teamed by w31) | [w28-sigma](../docs/w28-sigma.md) |

## 9 November

| Wave | Branch | Commit | What | Memo |
|---|---|---|---|---|
| 29 | w29-wiki-refresh | `43f3843` | refresh of the wiki to `1368fb6` (merged `c8cb697`) | |
| 30 | w30-sts | `ffda3f4` | Steiner triple systems; T1, T2 (merged `142aa6f`; red-teamed by w33) | [w30-sts](../docs/w30-sts.md) |
| 31 | w31-redteam-w27w28 | `894cc10` | red-team of w27 and w28; on master | [report](../docs/redteam-w27-w28.md) |
| 32 | w32-conference | `49fec8a` | conference graphs (merged `2b54de7`); **not red-teamed** | [w32-conference](../docs/w32-conference.md) |
| 33 | w33-redteam-sts | `a6d1fcc` | red-team of w30 (merged `20b2451`) | [report](../docs/redteam-w30-sts.md) |
| 34 | w34-vc | `005ca3c` | VC bounds for conference graphs (merged `12ab032`; red-teamed by w37) | [w34-vc](../docs/w34-vc.md) |
| 35 | w35-cubic | `8fb152f` | exact reduction of cubic Boolean equivalence to quadratic-form spaces (merged `0ed8fd3`; red-teamed by w37) | [w35-cubic](../docs/w35-cubic.md) |
| 36 | w36-lean | `719357a` | `lean/DegreeD`: machine-checked parts of the n^{O(log d)} accounting (merged `4bbd0ab`) | [w36-lean](../docs/w36-lean.md), [Lean audit](Lean-Audit.md#the-degree-d-accounting-in-lean-w36) |
| 37 | w37-redteam-cubic | `dce72f3` | red-team of w35 and w34 (merged `79aa9c1`) | [report](../docs/redteam-w35-w34.md) |
| 38 | w38-lean-stage1 | `5fb87e4` | **in progress** as of `5fb87e4`: continues `lean/DegreeD` toward Theorem R\*; not folded in | [Home](Home.md#work-still-in-progress) |
| 39 | w39-wiki-refresh | this branch | this refresh of the wiki; two value corrections in `docs/w18-latin.md` | |

The wiki was first cut from master at `b1a2d03` (w25); w29 refreshed it to `1368fb6`, and this refresh (w39) is current to master `b819c8d`.
