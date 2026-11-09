# Corrections and withdrawals

Everything claimed and later fixed, refuted, narrowed, or found to be already known. Later corrections win:
where this page and an older memo differ, this page is right about what the project now claims. Status of the
current statements is on the [Results ledger](Results-Ledger.md).

[Home](Home.md)

## Withdrawn or refuted

### Arity lower bound for the GNS black box

* **Claim** ([w10-blackbox](../docs/w10-blackbox.md) §0 row 1′): reducing the arity of the case-(v) structures canonically
  costs k^{<t} = 2^{Θ(L²)} branches, because PSL(2,q) makes every isomorphism-invariant binary relaxation trivial.
* **Refuted** by [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2. On the memo's own instance, PGL(2,q) is
  sharply 3-transitive, so 3 individualized points make the colouring discrete: the cost there is k³. The
  poly(k)-family remark is false as stated.
* **What remains.** At most k^{<t} by the Design Lemma; at least one individualization on some instances; whether O(1)
  always suffices is open. Prop 1.3 stands as an elementary statement about Aut(𝔄)-invariant binary relaxations.

### "Neuen 2020 Theorem 4.17(G) is false as stated"

* **Claim** ([redteam-canhyp](../docs/redteam-canhyp.md) §2.1): a counterexample shows the statement false.
* **Narrowed** by [verify-neu417](../docs/verify-neu417.md). Theorem 4.17 is an existence statement and a trivial witness
  satisfies (A)–(G), so the *statement* is not refuted. The objects built in the *proof* can violate (G), so
  this is a real error in the proof, at N2141 and propagated to Claim 4.25. The main theorem is unaffected; the potential ŝ repairs
  the accounting. `redteam-canhyp.md` keeps its original wording; `verify-neu417.md` corrects it. The paper's
  Remark `rem:neu20`(3) is now a question to the author. The TALG version was not accessed.

### "λ coefficient halved" in Theorem R\*\*

* **Claim** ([w17-affine](../docs/w17-affine.md) Prop. G, §7): the Sylow trick halves the coefficient of λ in R\*\*.
* **Withdrawn** by [redteam-w17-affine](../docs/redteam-w17-affine.md) §5: R\*\* has one Λ and no tracked coefficient to halve.
  The per-node count |P|_{2′} is right, the composite row is plausible and unproven (actual row cost
  μ_{2′} + 2), and no statement about R\*\*'s constants is supported.

### "Flag method has hit its limit"

* **Claim** ([w17-affine](../docs/w17-affine.md)): Prop. B′ shows the bidirectional flag method is at its limit.
* **Withdrawn** by [redteam-w17-affine](../docs/redteam-w17-affine.md) §3: B′ is a generic birthday bound for
  equality-only access to opaque labels, and says nothing about algorithms that read the labels.

### Draft claims retracted inside memos

* "No faithful tree representation of degree < m" for product-type components: false, retracted in
  [w2-coset](../docs/w2-coset.md) §2.4 (A₅ ≀ C_m is a tree group of degree 5 in its imprimitive action).
* "Every family in §4.5–4.6 costs 2^{O(d)}N^{O(1)}" and "all decoupled families are polynomial"
  ([w1-structure](../docs/w1-structure.md)): false or unproved as worded. The correct list is in
  [redteam-w1-structure](../docs/redteam-w1-structure.md) §7.
* The bound "2^{O(k₀)} poly(d′)" for the twisted instance when Q ≠ 1: unsupported, same report §6.
* w1-structure Prop 4.4's "paid with Λ = O(1)" as a whole: the terminal instance contributes a global factor
  max|P| (same report §6).
* w10's "no black box at all": case (iv) still calls B–H on binary structures, so "no t-ary black box"
  ([redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §4.5, [w12-theoremg](../docs/w12-theoremg.md) §0).

## Found to be known

### Theorem P is Babai–Codenotti–Qiao 2012

[w2-coset](../docs/w2-coset.md) presented Theorem P (string isomorphism for any G ≤ Sym(Δ) ≀ S_k in product action) as a
new FPT ingredient. [redteam-w2-coset](../docs/redteam-w2-coset.md) §2 identifies its recurrence with
Babai–Codenotti–Qiao ICALP 2012 Thm 5 / Codenotti's thesis Thm 4.2.1 (twisted code equivalence), and the
arbitrary top group with one extra coset intersection on V. The memo w1-structure had already sketched this. What remains is the
arithmetic that the CI cost on b·log N points is f(b)N^{o(1)}. Relabel as a corollary. The same report also repairs
the base case (setwise transporters need one CI each) and improves the exponent from 3.17 to 2.33
(states are (1 + b²)^k, so N^{log_b(1+b²)}).

### The coordinate-tanglegram group is AMBC 2025

[w6-tanglegram](../docs/w6-tanglegram.md) Prop C, described as new to the agent's knowledge, is a special case of
Anagnostopoulou-Merkouri–Bailey–Cameron Theorem 4.24(a) (Forum Math. Sigma 2025), found in
[w8-poset](../docs/w8-poset.md) §0, §7.

### "c = 4 for all d" was already known

[w8-gnsexp](../docs/w8-gnsexp.md) counted c = 4 for all d as part of its gain. [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §4.3: this needs
no new lemma. It follows from the known n^{O(log d)} domain count (Grohe–Neuen survey Thm 4.16) and B–H.
Likewise "c = 3 for log n ≤ log^{1.5} d" is B–H alone. Lemma A lowers the exponent only when log n > log² d.
The honest headline: for d ≤ 2^{(log n)^{1/3}} the exponent drops from 4 to 3; the worst case over d stayed 4 until
Theorem X.

### Affine equivalence: "nothing better than brute force"

[moonshot-theory](../docs/moonshot-theory.md) §3.3 and later memos said no algorithm beats brute force for AGL(k,2) string isomorphism.
[w17-affine](../docs/w17-affine.md) §1: false as a statement about available techniques. The generic methods give 2^{k²/2+O(k)}
(Theorem A) and 2^{k²/4+O(k)} (Theorem B). No 2^{o(k²)} algorithm is known; the exponent changed only by a constant
factor. [redteam-w17-affine](../docs/redteam-w17-affine.md): Theorem A is folklore and B is a routine instance of Rosenbaum /
Le Gall–Rosenbaum; the "+k/2" carries no content because 2^{k/2} = N^{1/2} is absorbed by poly(N).

### Other novelty corrections

| Item | Correction | Source |
|---|---|---|
| Lemma T "to my knowledge new" | device credited to Wiebking's thesis Lemma 5.34 and BC's right descent; what may be new is its use at test-set size Θ(log d) | [redteam-w4-gnscanon](../docs/redteam-w4-gnscanon.md) §6 |
| Lemma A | a non-asymptotic variant of Pago arXiv:2302.05426 (Lemma `G_groupInduction`, primitive case credited to Wiebking) | [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §7 |
| Prop 3.3 of w1-fpt | an instance of Schweitzer–Wiebking and ADKT; ADKT Thms 5–6 give the small-faithful-degree remark too | [redteam-w1-fpt](../docs/redteam-w1-fpt.md) §2.4 |
| Prop L of w6 | probably folklore among permutation-group experts | [w6-tanglegram](../docs/w6-tanglegram.md) §2.1 |
| Theorem B of w17 | "possibly folklore", then routine (see above) | [overnight log](../docs/overnight-log.md) |
| Prop 1.3 of w10 | elementary; a 2-transitive group has two orbitals | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2 |
| GN21 L1253 | w10 over-read it as naming the Design-Lemma option | same §6 |

## Gaps found in published work (questions to authors, not error claims)

### GNS Lemma 7.2

* The written proof asserts H′_(𝒞′) ≤ ker φ′ (v3, l. 2126) without justification. The algorithm lets the next round
  pick any minimal block system above 𝔅₁. For (S_m ≀ S₂) × C_q and x(a,b,c) = [a ∈ U], |U| ≈ 0.3m, the column system
  gives k′ = k, so the displayed k′ ≤ k − k/(3 log k) fails.
* Fix: take the next block system above 𝒞′. This is itself a legal run, so **the algorithm and the theorem are
  unaffected**; the running time is not shown to break.
* Status: confirmed by [redteam-gns-lemma72](../docs/redteam-gns-lemma72.md) and computed for m = 5–8. Numeric hypotheses: the red-team
  says m ≥ 180 with unrounded t; the paper uses t = max{9, 3 + ⌈log d⌉}, hence m ≥ 200. Both are consistent; the
  paper's rounding is the conservative one.
* The write-up's phrase "GNS's remark suggests this was intended" and "verbatim in Neuen" were over-readings
  (red-team §5). The "fewest blocks" reading of l. 2087 would avoid this example, but the text states no such rule.
* Present in all arXiv versions of GNS and Neuen 2020. **The SICOMP 2023 text was not accessible**; check it first.
  The paper poses this as a question, and the [cover note](../paper/cover-note.md) drafts it.

### Neuen 2020

See above for Thm 4.17(G). Also the giant-test order in the local certificates routine: the test must come
after BalanceOrbits; this affects only the cost proof ([w8-hypercanon](../docs/w8-hypercanon.md) §2.8).

### Minor slips in published text

* GNS L2324: |D_{i,j}| ≥ 3k/4 should be ≥ 3k/4 − 4; harmless.
* Babai arXiv v2 Thm 3.2.1 prints 2^{1+log₂ n} for n^{1+log₂ n}; a typo.
* HBD's "H is a pointwise stabilizer" (L1437, L1504) is imprecise at the contraction step; see
  [redteam-theoremg](../docs/redteam-theoremg.md) §1.3.

## Corrections to the project's own statements

### The ETH barrier

The statement "W[1]-hardness would need parameter blow-up ≥ 2^{k^Ω(1)}" was written "under ETH" in
w1-fpt, w2-coset, w4-t2 and w6-tanglegram. An unrefereed October 2026 preprint claims ETH is false. [w21-eth](../docs/w21-eth.md)
§B.3: the argument only ever used that k-Clique has no f(k)n^{o(k)} algorithm (CLIQUE-LB). ETH implies CLIQUE-LB, not
conversely, so the barrier survives if ETH fails. Notes were added to the five memos.
One unedited residue: the `w2-coset` entry in [overnight-log.md](../docs/overnight-log.md) still says "ETH forces".

### "SAT encoding of GI has at least n log n variables"

Said in discussion before w21. [w21-eth](../docs/w21-eth.md) §B.1: that is a statement about encodings whose assignments include every
bijection, not a lower bound on reductions. Natural fixed-width encodings have about n² variables, for which
2^{n²/√log n} is worse than n!. The theorem helps only if N ≲ log² n·√(log log n)/log log log n.

### Theorem R, and its verification

| Item | Correction | Source |
|---|---|---|
| Dispatcher (M) | ambiguous and wrong read with HJ's order test; replaced by the structural rule (M′) | [verify-theorem-R](../docs/verify-theorem-R.md) §4.0, [redteam](../docs/redteam-theorem-R.md) §9(b) |
| (H1) | not a hypothesis: holds, after replacing "Cameron-large" by GNS option 2 | [verify-theorem-R](../docs/verify-theorem-R.md) §2 |
| log log N term | removable via BCP/Maróti, giving R\* | same §4.4 |
| "m ≥ 300" for the overlap of HJ's exceptional range with option 2 | wrong; first overlap at m = 509 (t = 22), or m = 557 for t = ⌈√m⌉ | [redteam-theorem-R](../docs/redteam-theorem-R.md) §9(a) |
| Λ = log(4d̃) | use log(8d̃) to cover both readings of BCP | same §9(c) |
| "n^{O(log d)}" | should read n^{O(log(d+2))} | same §9(d) |
| Literature note on c | w1-fpt "c ≥ 4", red-team "c ≥ 3": replaced by the bookkeeping c = 5 of w8 (upper bound from the written proof) | [w8-gnsexp](../docs/w8-gnsexp.md) §1.3 |

### Speculation that HJ's σx channel is never tight

[moonshot-theory](../docs/moonshot-theory.md) §5 listed as speculation that the x² and σx channels are never tight, and §2.3 knew no instance. Theorem B1 of w18 (given HJ as written, not yet red-teamed) attains the σx channel on the PG(m−1,2) incidence graphs: "visible unaffected steps with polynomial-degree giants" occur there. See `docs/w18-latin.md`.

### Status of the Lean formalization

The memo [moonshot-theory](../docs/moonshot-theory.md) (Nov 4) describes the Lean as a "stage 1" formalization with subroutines as
hypotheses, and `RunningTime.lean` L9 says Sections 4–6 are not formalized. These were superseded: the final
`main_theorem` takes no such hypotheses, and building and comparator confirm it (see [Lean audit](Lean-Audit.md)). Separately, the string
theorem 1.2 really is only at "stage 1"; only GI is verified at machine level ([w10-blackbox](../docs/w10-blackbox.md) §2.1).
Also: the "main residual risk" named in round 4 was HJ's σ-budget; it is now machine-checked modulo the axioms.

### Canonization write-ups

| Item | Correction | Source |
|---|---|---|
| Blank symbol in windowed strings | must be fresh (β ∉ Σ); handled by explicit tags in the write-up | [redteam-w4-gnscanon](../docs/redteam-w4-gnscanon.md) §2.3 |
| Lemma F1 / Lemma 5.1 "right subgroup" | stated wrongly; fixed | [redteam-canonization-writeup](../docs/redteam-canonization-writeup.md) §6 |
| §10 assumptions | four missing, chiefly determinism and canonical generators for every subroutine feeding a (P1) choice, including BC | same §4 |
| Write-up §9.2: treewidth needs canonical Neuen | wrong; treewidth needs only Theorem A (`cosetHyper` is applied once, to a hyperedge-respecting coset) | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md) §0, [w8-hypercanon](../docs/w8-hypercanon.md) §3.3 |
| Theorem TW | labelled proven mod; relabelled **sketch**; fixes TW-1 (χ step), TW-2 (mark S), TW-3 (degeneracy check) | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md) §3 |
| Theorem H "correctness proved" | overstated (no written algorithm); §10.9 CanHyp was added and red-teamed; status unchanged: correctness proof modulo §13, time a sketch | [referee](../docs/referee-canon-paper.md) M1, [redteam-canhyp](../docs/redteam-canhyp.md) |
| Babai's STOC 2019 dependency | hidden at headline level; surfaced in abstract and Table 1. The referee's "only graph canonization on ≤ d points" held only in part: BC is called on t-ary structures under A_k/S_k, k ≤ d | [referee](../docs/referee-canon-paper.md) M2, [overnight log](../docs/overnight-log.md) wave 12 |
| Citations | 7 of about 120 fixed | [referee](../docs/referee-canon-paper.md) §5 |

### Exponent memos

| Item | Correction | Source |
|---|---|---|
| Lemma A | hypothesis m ≥ 16; exact threshold m ≥ 6; fails at m = 5, k = 6 (PSL(2,5), PGL(2,5)); "CFSG-free" refers to the lemma only | [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §2 |
| Corollary F | "not on the CFSG lemma" must add "still CFSG-dependent via GNS 3.13" | same §6 |
| Theorem X framing | c = 3 for d ≥ 2^{(log n)^{2/3}} is B–H alone; gain confined to 5/3 < x < 3 | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §1.5 |
| Split-or-Johnson individualization count | "O(log m) points" wrong; at most O(log² m) (w12), in fact O(log^{3/2} m) (w15) | [w12-theoremg](../docs/w12-theoremg.md) §9, [redteam-theoremg](../docs/redteam-theoremg.md) §1.2 |
| Reading of HBD Split-or-Johnson | "reads one point of Γ" false at contraction: streams read elements of the current V₂ (possibly blocks) | [redteam-theoremg](../docs/redteam-theoremg.md) §1.3 |
| "Legal run of GNS" (Theorem G) | slightly too strong: G2 tests the inserted top | same §3 |
| Theorem G regimes | improvement exactly on 3/2 < x < 2 (x = 3/2 not new); "min(log³ d, log² n)" needs B–H | same §5 |
| Check script cost | memo said about 2 s; took over 2 minutes at nice 19 | same header |

### Core-problem memos

| Item | Correction | Source |
|---|---|---|
| w1-fpt Prop 4.1 | Aut(B) := Iso(B,B) is not a group; needs an x→x table | [redteam-w1-fpt](../docs/redteam-w1-fpt.md) §3.1 |
| w1-fpt Prop 4.2 | virtual root fails for intransitive tree groups; run the DP on the given tree | same §4.1 |
| w1-fpt "every size N" | only suitable m; "c ≥ 4" wording | same §1.6, §5 |
| w1-structure Lemma 4.3 | "≥ N/(dL)" false; correct bound N/((d+1)L) | [redteam-w1-structure](../docs/redteam-w1-structure.md) §5.3 |
| w1-structure "closed under sections" | false for the composition-factor class; use aw and section-closed λ | same §1.4, §2.2 |
| w1-structure Theorem L coset version | missed Aut_R(x); repaired, now proven modulo S-W | same §4.3 |
| w2 Cor 2.2 | full-diagonal PCI in DPs is SI on one child; the hard shape is a diagonal on a full-depth direct factor | [redteam-w2-coset](../docs/redteam-w2-coset.md) §3.3 |
| w2 Example X "ε = 1" | overstated: level 2 can stay coupled, ε_root ≤ \|GL(r,2)\|^{2^{r−1}}; FPT conclusion stands | same §5 |
| w2 Theorem P's exponent and base case | see above | same §1 |

### Moonshot and affine memos

| Item | Correction | Source |
|---|---|---|
| Theorem C (w17) displayed Iso set | wrong direction: it is Iso(c_T′, c_T) | [redteam-w17-affine](../docs/redteam-w17-affine.md) §4 |
| Prop B′ bound | true bound Ω(2^{k²/4+k/4}) | same §3 |
| Theorem B parabolic | a 3- or 4-block parabolic reaches 2^{k²/4+k/4} at a cost in space; harmless | same §2.4 |

### Benchmarks and software

| Item | Correction | Source |
|---|---|---|
| `3reg12-pair` mislabeled | random cubic graphs from seeds 5 and 6 are isomorphic; the solver's answer was right and the benchmark's WRONG was wrong. Fixed (seeds 5 and 7); non-isomorphism labels now verified by networkx or a cited theorem | commit `9180532`, [bench/families.py](../bench/families.py) |
| Baseline "14/29" | counts the mislabeled pair as correct; the raw JSON shows 13 ok, 1 WRONG, 15 timeouts | [bench/results/baseline-nocert.json](../bench/results/baseline-nocert.json) |
| Timed individualization budget | changed output on 7 of 56 instances under simulated preemption; replaced by a counted budget | [README](../README.md), commit `4d47f55` |
| Hypercube regression in `class_plan` | class layers made Q8 > 200 s; plan now falls back to BFS on a twin block ≥ 3 | [w1-scale](../docs/w1-scale.md) §1.6 |
| `gi.canon` | no polynomial guarantee at d ≤ 5; solvable layers not done | [w14-solver](../docs/w14-solver.md) |
| w14 profiles and slowdowns | corrected against measurements in `ef6f8ab` | [w14-solver](../docs/w14-solver.md) |
| README table of canonical times | README's "CFI n = 3200 … 13 s" is w9; w14 reached 1.41 s for canonical forms. Later numbers in [Benchmarks](Benchmarks.md) win | [README](../README.md) |

### The video

Fact-checked by `w24-video-review` (`4085217`), which fixed wrong and overclaimed statements in the narration, cards and code; `video/REVIEW.md` on master lists them with sources. Differences between planning documents and data, as of `b1a2d03`:
[STORYBOARD.md](../video/STORYBOARD.md) still says CFI over K₄ has 28 vertices and the window run uses Alt(5); [CLAIMS.md](../video/CLAIMS.md), generated from the code, says 40 vertices (16 middle, 24 edge-end) and Alt(7) on 21 pairs. CLAIMS.md is the later, computed record.

### Cross-document inconsistencies resolved when the paper was assembled

The agent writing [canon.tex](../paper/canon.tex) reconciled 9 such items, always keeping the more conservative statement, for
example: TW is a sketch; the counterexample needs m ≥ 200; "beats BC" is claimed only for k = polylog n
([overnight log](../docs/overnight-log.md), w9-paper).
