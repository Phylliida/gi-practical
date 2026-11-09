# Results ledger

Every theorem, bound and claim of the project, with its status, what it assumes, and what checked it.
Corrections are summarized here and explained on [Corrections and withdrawals](Corrections.md).

[Home](Home.md)

## How to read the status columns

**Status** is one of:

* **proven**: a complete written argument, using only published results and the standard polynomial-time
  permutation-group toolkit.
* **proven modulo X**: complete, except that X is used without re-proof.
* **sketch**: an argument with gaps; the gaps are named in the source.
* **conditional on H**: holds under hypothesis H, which may be an unrefereed result.
* **withdrawn**: claimed earlier and now retracted or refuted.
* **known prior work**: true, but the claim of novelty does not stand.

"Proven" means an AI agent wrote a complete argument. It does not mean a human has verified it.

**Checked by** is one of:

| Tag | Meaning |
|---|---|
| Lean | accepted by the Lean kernel (only HJ's main theorem, modulo 10 axioms) |
| AI red-team | an independent AI agent tried to break it and reports what it checked |
| AI verify | an AI agent checked it against the sources (a pass aimed at confirmation) |
| brute force | checked on small instances by computation (tests instances, not proofs) |
| author only | one AI author pass, with no separate check |
| nobody | not checked beyond being written |

No statement has been checked by a human expert. This covers every row below.

Abbreviations: GNS = Grohe–Neuen–Schweitzer; BC = Babai STOC 2019; B–H = Babai with Helfgott's analysis,
exp(O(log³ n)); CFSG = classification of finite simple groups. Notation is in the [Glossary](Glossary.md).
Many memos reuse theorem names, so each row names its memo.

---

## 1. HJ and its Lean formalization (external result audited here)

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| HJ main theorem (`main_theorem`) | one program and one real C with: for all n and graphs G, H on Fin n, the run on the adjacency-matrix memory halts with the correct yes/no (on yes, an isomorphism and generators of Aut(G)) at cost ≤ exp(C·log(n+2)²) on a log-cost RAM | proven modulo 10 axioms | 10 CFSG-era literature axioms; 3 standard Lean axioms | **Lean** (build, `#print axioms`, comparator); trusted base read by an AI agent | [Lean audit](Lean-Audit.md) |
| HJ Thm A.9 (hereditary budget σ ≤ C log n − B) | as stated in the paper | proven modulo the axioms | as above | **Lean** (`GI.Paper.thm_hereditary_budget` is in the 115,555-constant dependency cone of `main_theorem`); AI re-derivation of all but the primitive-valuation lemma | [overnight log](../docs/overnight-log.md), [w8-gnsexp](../docs/w8-gnsexp.md) §3.2 |
| HJ Thm 1.2 (string isomorphism in exp(O(log² N))) | as stated in the paper | paper claim; not machine-checked as a string theorem | HJ | **not** Lean: `GI.Paper.thm_main_string_stage1` covers the abstract recursion and carries hypotheses; the machine-level statement is GI only | [w10-blackbox](../docs/w10-blackbox.md) §2.1 |
| HJ constant C | non-explicit; explicit parts force C ≳ 4·10¹⁴, realistically ≳ 10¹⁶ | traced by reading only | — | nobody beyond the reading | [Lean audit](Lean-Audit.md#the-constant-c) |
| Canonical forms for HJ | none claimed by HJ ("Canonization is a separate task") | — | — | — | [w3-canon](../docs/w3-canon.md) §4 |

## 2. The n^{O(log d)} bound and analysis of HJ (conditional)

Everything in this section assumes (H0), that HJ's algorithm and analysis (Sections 4–7 and Appendix A)
are correct, unless the row says otherwise.

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Theorem R (first form) | Γ̂_d string isomorphism in exp(O(log N(log d + log log N))), under (H1), (H2) | superseded by R\* | (H0), (H1), (H2) | superseded | [moonshot-theory](../docs/moonshot-theory.md) §4.1 |
| **Theorem R\*** | HJ with dispatcher (M′) solves Γ̂_d string isomorphism on N points in exp(O(log(N+2)·log(d+2)))·poly(input) | conditional on (H0) | (H0); GNS Thm 3.13, Lemma 4.4; BCP Lemma 2.2 (or Maróti Cor. 1.5); Luks/Babai–Luks reduction | AI verify, AI red-team (no hole outside (H0)); the Λ accounting is **not** machine-checked | [verify-theorem-R](../docs/verify-theorem-R.md), [redteam-theorem-R](../docs/redteam-theorem-R.md) |
| **Corollary R\*** | GI of maximum degree d in n^{O(log(d+2))} | conditional on (H0) | as above | as above | same |
| (H1) recognition of option-2 constituents | holds; a theorem from the literature, not a hypothesis | proven modulo GNS 3.13 + Lemma 4.4 (or the self-contained §2.2 variant for m ≥ 3t) | BLS87, Kantor–Luks | AI verify, AI red-team | [verify-theorem-R](../docs/verify-theorem-R.md) §2 |
| (H2) call grouping | at most about 10 q^{2κ} disjoint-domain families; fits `PhaseTree.Hyp` in the Lean | proven (verified against HJ and Lean scripts) | (H0) | AI verify, AI red-team | same §3 |
| Theorem R\*\* | exp(O(log(N+2)(log w + λ + 1))), w = alternating width, λ = largest classical section dimension | conditional on (H0) and Prop 2.1 (sketch) | (H0), [w1-structure](../docs/w1-structure.md) Prop 2.1 | AI red-team (needs section-closed parameters) | [w1-structure](../docs/w1-structure.md) §3, [redteam](../docs/redteam-w1-structure.md) §2 |
| Per-phase exponent of HJ | O(log N·(log w + μ + log log N)) | sketch | (H0) | author only | [moonshot-theory](../docs/moonshot-theory.md) §2.9 |
| Lemma 1 (ρx is slack) | ρ·O(log log N) suffices in HJ's analysis | proven given HJ's step structure | (H0) | author only | same §2.2 |
| Outer phase recurrence is lossless | no gain possible from N → N^γ recurrence | proven | (H0) | author only | same §2.7 |
| Theorem C (w3, HJ-canon) | canonical forms for Γ̂_d strings in exp(O(log N log d + log^c d)); degree-d graphs in n^{O(log d)}·exp(polylog d) | conditional on (H0), BC, BL83; assembly sketched | (H0), BC, BL83 | author only | [w3-canon](../docs/w3-canon.md) §2.4 |
| Theorem H (w3, frontier hybrid) | poly(N)·min over invariant frontiers of Σ HJC + Σ combine costs; never worse than R\* | conditional on w3 Theorem C (canonical); on (H0) for the isomorphism version | see left | author only | [w3-canon](../docs/w3-canon.md) §3.6 |
| Lemma N (canonical forms descend to normal subgroups); Theorem E-canon | polynomial descent; canonical forms in Σ_B \|P_B\| δ_B poly(N), δ_B ≤ ε_B | proven modulo BC framework | BC §5 | author only | [w3-canon](../docs/w3-canon.md) §3.2–3.3 |
| Theorem P-canon | canonical forms for any G ≤ Sym(Δ) ≀ S_k in product action in 2^{polylog b}·N^{1.59+o(1)} | sketch modulo Wiebking's canonizer | Wie20 Cor. canObj0 | author only | [w3-canon](../docs/w3-canon.md) §3.4 |
| Corollary F (w8) | degree-d GI in n^{O(log² d)} without HJ's primitive-valuation lemma | conditional on HJ §§4–7; weak budget (Theorem E of w8) is a sketch; still uses CFSG through GNS 3.13 | HJ §§4–7 | AI red-team at proof-sketch level | [w8-gnsexp](../docs/w8-gnsexp.md) §3.3, [redteam](../docs/redteam-w8-gnsexp.md) §6 |

## 3. Lower bounds for specific algorithms, and barriers

These are about what particular algorithms do, or about implications; none is a general lower bound for
GI, and none has been transferred to graphs.

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Prop 2 (moonshot) | HJ on AGL(k,2), N = 2^k, makes ≥ 0.288·N^{1+log₂N} coset branches for all strings | proven, given HJ's dispatcher as written | — | author only; dispatcher traced in Lean by later red-teams; w17/w20 show the bound is about HJ's dispatcher, not the problem | [moonshot-theory](../docs/moonshot-theory.md) §2.5 |
| Prop 3.1, Cor 3.2 (w1-fpt) | for odd D ≥ 3, G = (F₂^{D−1} ⋊ S_D) ≀ C_m (m = 2^j) is primitive, affine, in Γ̂_D; HJ and HJ+(M′) create ≥ \|G\| ≥ N^{log₂D − 0.443} children on every instance; GNS 3.13's exponent is sharp at fixed d | proven | HJ pseudocode only (not (H0)) | AI red-team | [w1-fpt](../docs/w1-fpt.md) §3.1, [redteam](../docs/redteam-w1-fpt.md) §1 |
| Prop 4.2 (w1-structure) | on G_{r,L} and AGL(r,2)^L, HJ+(M′) makes ≥ N^{r+1−1.8/r−o(1)} branches | proven from pseudocode; independent of (H0) | — | AI red-team | [w1-structure](../docs/w1-structure.md) §4.6, [redteam](../docs/redteam-w1-structure.md) §5 |
| Group-iso and combinatorial barriers | n^{o(log n)} GI would give n^{o(log n)} for group, quasigroup, Steiner triple, conference-graph isomorphism, and 2^{o(k²)} for AGL(k,2) string isomorphism | proven reductions | — | author only | [moonshot-theory](../docs/moonshot-theory.md) §3 |
| Prop 3 (moonshot) | AGL(k,2) string isomorphism reduces to GI on Θ(N³) vertices | proven | — | author only | same §3.3 |
| c < 2 barrier | an unconditional n^{O(log^c d)} with c < 2 for all d would beat exp(O(log³ n)) for general GI | proven (state-of-the-art statement, not a lower bound) | — | AI red-team | [w8-gnsexp](../docs/w8-gnsexp.md) §2.7, [redteam](../docs/redteam-w8-gnsexp.md) §5 |
| c = 3 floor of GNS's architecture | K·log N accounting cannot go below L³ | sketch; a heuristic about the accounting | — | AI red-team (heuristic) | same |
| Clique-lower-bound barrier | W[1]-hardness of degree-d GI, TreeCI or tanglegrams would need parameter blow-up 2^{k^Ω(1)} | conditional on CLIQUE-LB (implied by ETH), modulo GNS. Originally stated under ETH | CLIQUE-LB | AI red-team of the ETH form; re-based in w21 | [w21-eth](../docs/w21-eth.md) §B.3 |
| Theorem B (w4-t2) | CFI over cubic expanders embeds in coloured binary tanglegrams, so WL dimension Ω(\|V\|) at b = 2; Ω(\|V\|^{1/2}) on binary T□T | proven modulo the standard CFI game | CFI game | brute force E2 (nauty, 2-WL), author only | [w4-t2](../docs/w4-t2.md) §5.1 |
| IR and rank-logic lower bounds at b = 2 | NS multipede and Lichter constructions carry over | sketch | — | author only | [w4-t2](../docs/w4-t2.md) §5.2 |
| Heart-module tightness | E ⋊ A_k (k odd, E even-weight code) shows Babai's threshold k > 2 + log₂ n tight to an additive 1; such levels must be made semi-regular in GNS | proven | — | AI red-team | [w8-gnsexp](../docs/w8-gnsexp.md) §2.6 |
| Bounded alternating width alone does not help | AGL(k,2) has polylog alternating width and N^{Θ(log N)} HJ branches | proven | — | author only | [moonshot-theory](../docs/moonshot-theory.md) §2.5, §4.5 |

## 4. Canonization (does not depend on HJ)

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Lemma S (canonical subcoset), Lemma T (reference tuple colours), F1–F4, R, K | canonizer framework; T gives colours from a group-chosen reference tuple | proven | standard toolkit | AI red-team (three passes across reviews), AI referee; device credited to Wiebking's thesis Lemma 5.34 | [w4-gnscanon](../docs/w4-gnscanon.md), [canon.tex](../paper/canon.tex) |
| Lemma T′ (exactness, symmetry defect ≥ 1/4), T″ (cost ≤ k^t·n) | colours match GNS comparison classes; no t-vs-n relation | proven (T″ modulo GNS Thm 5.9) | GNS local-certificate facts | AI red-team | same |
| **Theorem A** | for G ∈ Γ̂_d by generators, a coset and a string, a canonical form and placement coset in n^{O((log d)^c)} | proven modulo §10 of the paper | GNS Thms 3.13, 4.3/4.6, 5.8, 5.9, Lemmas 6.2, 7.1, Cor 6.5; BC Thm 2.2 (a preliminary report that sketches its proof) on instances of size d^{O(log d)}; canonical generating sets; deterministic subroutines on canonical generators (D1–D4) | AI red-teams ([1](../docs/redteam-w4-gnscanon.md), [2](../docs/redteam-canonization-writeup.md)), AI [referee](../docs/referee-canon-paper.md) (no error); running time written out and checked | [canon.tex](../paper/canon.tex), [write-up](../docs/canonization-bounded-degree.md) |
| **Corollary B** | canonical forms for graphs of maximum degree d in n^{O((log d)^c)} | proven modulo Theorem A | canonical Luks reduction written out (BL83 read) | AI red-team; brute force on 47 graphs with two caught mutants | same, [check script](../docs/redteam-canonization-writeup-check.py) |
| Corollary D | canonical labelling relative to a labelling coset of a Γ̂_d group in \|V\|^{O((log d)^c)} | proven modulo Theorem A | as Theorem A | AI red-team | [canon.tex](../paper/canon.tex) |
| Corollary C (w4) | relational structures in n^{O(t·(log n)^c)} (weaker than Wiebking in general) | as Theorem A | as Theorem A | listed for completeness | [w4-gnscanon](../docs/w4-gnscanon.md) §4.1 |
| **Theorem H** (canonical Neuen 2020) | canonical form and coset for a set of m 𝔓-strings under Γ̂_d cosets in (n+m)^{O((log d)^{c′})} | correctness proof modulo §13 of the paper (Neu20 constructions, Theorem A, Neuen's dissertation lemma 6.1.17, unseen); **running time a sketch** | as listed | AI red-team; CanHyp §10.9 red-teamed separately; toy code 0 failures over 4868 calls, mutants caught; giant steps (k > 90) not exercised | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md), [redteam-canhyp](../docs/redteam-canhyp.md) |
| Lemma CH | coset-labelled hyperedges under a hyperedge-respecting coset | proven modulo Corollary D and GNSW18 Lemma 23 | | AI red-team | [canon.tex](../paper/canon.tex) §11 |
| **Theorem TW** | canonical forms for treewidth k in n^{O((log k)^{c″})}; needs only Theorem A | **sketch**, conditional on Theorem A, with fixes TW-1–TW-3 | Theorem A, Wiebking's tools | AI red-team | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md) §3 |
| H1 (coset-labelled hypergraphs) | (n+m)^{polylog d} | proven modulo Theorem H, Corollary D (time as good as H's sketch) | | AI red-team | [w8-hypercanon](../docs/w8-hypercanon.md) §4 |
| H2 (t-CR-bounded), H3 (K_{3,h}-minor-free, genus) | n^{polylog t}, n^{polylog h}, n^{polylog g} | sketch | Theorem H | AI red-team (hypotheses right) | same |
| H4 (K_h-minor-free, topological-subgraph-free) | n^{polylog h} | conditional on H, H1, H2; DP sketched; would answer Wiebking's Q 9.7 only in a parameter-free form | | AI red-team | same |
| Remark 5.2 (BC simplification) | BC §§11–15 seem avoidable by the same device | sketch; keep out of any public claim | | AI red-team: unverified | [w4-gnscanon](../docs/w4-gnscanon.md) §5, [redteam](../docs/redteam-w4-gnscanon.md) §8 |
| GAP-1 (GNS Lemma 7.2 written proof) | H′_(𝒞′) ≤ ker φ′ can fail for the algorithm as written; fix: next block system above 𝒞′, a legal run; theorem not in doubt | proven gap and fix; **question to the authors** | SICOMP text unread | AI red-team, computation for m = 5–8 | [redteam-gns-lemma72](../docs/redteam-gns-lemma72.md) |
| GAP-2 | GNS Lemma 2.8 does not literally cover the semi-regular step; covered by a recursion lemma | proven | | AI red-team | [redteam-canonization-writeup](../docs/redteam-canonization-writeup.md) §1.1 |
| Neuen 2020 Thm 4.17(G) | proof error (not a false statement); potential ŝ repairs the accounting; main theorem unaffected; **question to the author** | proven error in the proof; earlier "false as stated" withdrawn | TALG version unread | AI red-team, AI verify, computation | [verify-neu417](../docs/verify-neu417.md) |
| Neuen 2020 giant-test order | test must follow BalanceOrbits; correctness unaffected | proven fix | | AI red-team | [w8-hypercanon](../docs/w8-hypercanon.md) §2.8 |

## 5. The exponent c in n^{O(log^c d)} (does not depend on HJ unless stated)

L = log₂(d+2); write log n = L^x. See [Math: exponent](Math-Exponent.md).

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Theorem 1 (w8) | GNS as written, with the 7.2 fix: c = 5 (bookkeeping of the written proof; upper bound on what the proof gives) | proven | GNS; §7.3 fix | AI red-team | [w8-gnsexp](../docs/w8-gnsexp.md) §1.3 |
| Prop 2, Cor 3 (w8) | domain N ≤ n^{O(L)}; with the B–H switch, c = 4 for all d | **known prior work** (survey Thm 4.16 count; one line of bookkeeping) | | AI red-team | same, [redteam](../docs/redteam-w8-gnsexp.md) §1 |
| Lemma A | L₀ ≤ S_k with an A_m composition factor, m > 3k/4 and m ≥ 16 (true exactly for m ≥ 6) contains Alt(Δ), \|Δ\| ≥ m, fixing the rest | proven; CFSG-free as a lemma; a non-asymptotic variant of Pago's lemma, credited to Pago and Wiebking | Bochert or Praeger–Saxl | AI red-team, computation | [w8-gnsexp](../docs/w8-gnsexp.md) §2.1, [exponent.tex](../paper/exponent.tex) |
| Prop B (w8) | k′ ≤ 3k/4 between consecutive aggregation nodes | proven, with the §7.3 fix | GNS | AI red-team | same §2.2, [redteam](../docs/redteam-w8-gnsexp.md) §3 |
| Theorem C (w8) | GNS with the fix runs in n^{O(L³)}·(1 + X(d)), X(d) = cost of one black-box call | proven | GNS, GN21 Thm 4.16 | AI red-team | same §2.3 |
| Signed w9 statement | n^{O(log³ d)}·2^{O(log⁶ d)}; n^{O(log³ d)} for d ≤ 2^{(log n)^{1/3}}; n^{O(log⁴ d)} for all d (the last needs no new lemma) | proven modulo GNS, B–H | | AI red-team | [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §8 |
| **Theorem X** | black box in 2^{O(t log³ m + log⁵ m)}; degree-d GI in n^{O(log³ d)}·2^{O(log⁵ d)}; c = 10/3 for all d; c = 3 for d ≤ 2^{√log n} | proven modulo GNS, HBD Design Lemma / Split-or-Johnson, B–H | see source | AI red-team (sound), with framing corrections | [w10-blackbox](../docs/w10-blackbox.md) §3, [redteam](../docs/redteam-w10-blackbox.md) |
| **Theorem G** | degree-d GI in n^{O(log³ d)} for all d (c = 3); with B–H, n^{O(min(log³ d, log² n))} | proven modulo GNS and HBD's lemmas as read; **provisional**: one author pass and one AI red-team | GNS (v3), N ≤ n^{O(L)}, Lemma A, HBD lemmas read as streams over V₂, B–H | AI red-team (no break, one low-severity error fixed) | [w12-theoremg](../docs/w12-theoremg.md), [redteam-theoremg](../docs/redteam-theoremg.md), [exponent.tex](../paper/exponent.tex) |
| HJ as black box / whole-input switch | conditional on HJ, n^{O(min(L³, log n))}; subsumes X and G for GI | conditional on HJ Lean `main_theorem` | HJ | AI red-team | [w10-blackbox](../docs/w10-blackbox.md) §2, [redteam-theoremg](../docs/redteam-theoremg.md) §5 |
| Prop 1.3 (w10) | binary relaxations of some case-(v) instances are trivial; at least one individualization needed | proven (elementary); the stated cost lower bound is **withdrawn** | | AI red-team | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2 |
| Theorem E (w8, weak budget) | σ ≤ C(c₁L + c₂) log n for transitive Γ̂_d | sketch | GNS 3.13 | AI red-team, sketch level | [w8-gnsexp](../docs/w8-gnsexp.md) §3.3 |
| β-variant (c = 10/3, w8 route) | black box 2^{O(L⁵)} by the Design Lemma | sketch; superseded by Theorem X | | AI red-team | [w8-gnsexp](../docs/w8-gnsexp.md) §2.4 |

## 6. The core problem: TreeCI, tanglegrams, posets

See [Math: core problem](Math-Core-Problem.md). None of these gives FPT for degree-d GI.

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Prop 3.3 (w1-fpt) | SI(P ≀ K) product action on Δ^m in \|K\|\|P\|2^{O(b)}N²poly(bm); G_{d,m} in 2^{2^{O(D)}}N^{2+o(1)} | proven modulo ADKT Thm 5; **known prior work** (instance of SW19, ADKT) | ADKT | AI red-team | [w1-fpt](../docs/w1-fpt.md) §3.2, [redteam](../docs/redteam-w1-fpt.md) §2.4 |
| Prop 4.1 (block-pair DP) | SI reduces to O(N²)·max\|P_B\| PCI instances | proven | | AI red-team (after a group-part fix) | [w1-fpt](../docs/w1-fpt.md) §4.1 |
| **Theorem E** (w1-fpt) | π₀·ε·poly(N); tree groups of node degree ≤ b: b!·ε·poly(N) (run on the given tree) | proven; plausibly new, elementary | standard toolkit | AI red-team | same §4.3, [redteam](../docs/redteam-w1-fpt.md) §3 |
| Abelian entanglement | R_i/M_i abelian ⇒ ε replaced by 1 | proven (red-team's argument, checked once) | | AI red-team | [redteam-w1-fpt](../docs/redteam-w1-fpt.md) §3.4 |
| Prop 4.2 (w1-fpt) | SI for tree groups is FPT iff coset intersection is | proven after two low-severity repairs | | AI red-team | same §4 |
| Theorem L (w1-structure) | level-synchronised towers G = R·S: 2^{O(k)}·poly(Σ\|U_j\| + N·max\|R_j\|) given the tower data | proven modulo S-W Theorem obj (coset version repaired by red-team) | Schweitzer–Wiebking | AI red-team | [w1-structure](../docs/w1-structure.md) §4.6, [redteam](../docs/redteam-w1-structure.md) §4 |
| G_{r,L} facts | FPT given tower data; no faithful action with orbits ≤ N/((d+1)L); unbounded non-abelian entanglement | proven | | AI red-team | same §5 |
| Prop 2.1 (μ bound), Prop 2.2 (coordinate type) | μ(P) ≤ C(1+λ+min(log w, log log d′)) | sketch | LS14 etc. | AI red-team (no counterexample) | [w1-structure](../docs/w1-structure.md) §2 |
| Theorem 2.1 (w2) | TreeSI ≡ TreeCI ≡ PCI ≡ PCI_diag ≡ T² under fpt-reductions | proven (abstract problems) | | AI red-team | [w2-coset](../docs/w2-coset.md) §2.1, [redteam](../docs/redteam-w2-coset.md) §3 |
| Cor 2.2, Cor 2.3 (w2) | coupling pattern irrelevant (reworded: diagonal on a full-depth direct factor); bounded coupling depth is FPT | proven after rewording | | AI red-team | same |
| Lemma 2.4 (w2) | GNS's almost d-ary class = tree groups of degree d!/2 | proven | | AI red-team | same §4 |
| **Theorem P** (w2) | SI for any G ≤ Sym(Δ) ≀ S_k in product action in (b!)^{1+o(1)}·N^{2.33} | proven modulo Babai CI; **known prior work**: Babai–Codenotti–Qiao 2012 Thm 5 / Codenotti Thm 4.2.1 plus one coset intersection; exponent 2.33 after red-team fix | Babai CI | AI red-team; brute force on 72 instances | [redteam-w2-coset](../docs/redteam-w2-coset.md) §1–2 |
| Theorem E′, Cor 3.1 (w2) | bounded entanglement suffices with unbounded primitive components; primitive Γ̂_d FPT | sketch (needs Prop 2.2 of w1-structure and bookkeeping) | | AI red-team: plausible | [w2-coset](../docs/w2-coset.md) §3.3–3.4 |
| Prop 6.1 (w2) | Aut of coloured T□T is {(α,β) ∈ W×W}; diagonal if marked | proven | | AI red-team; VF2 22/22 | [w2-coset](../docs/w2-coset.md) §6 |
| Theorem A (w4-t2) | T²_full ≡ GI(coloured T□T) ≡ tanglegram isomorphism ≡ FullCI ≡ HCGI ≡ HS(b,r)-GI ≡ Def-CI | proven | | brute force E1 54/54; author only | [w4-t2](../docs/w4-t2.md) §2 |
| Prop A′, A″ (w4-t2) | TreeCI ≡ CI(arbitrary, full, same tree); degree-d GI ≡ depth-2 tanglegrams with unbounded root | proven | | author only | same §2.3–2.4 |
| Cor A.2 (w4-t2) | degree-d GI FPT ⇔ tanglegram FPT | conditional on (R2) and the W2 §3.5 gap; "⇒" direction unconditional | | author only | same |
| Prop D (w4-t2), Prop T | diagonal shape adds nothing; FPT in (b, τ) | proven | | author only | same §3–4 |
| Prop S (w4-t2) | W(T) ∩ Alt(L) definable by a degree-9 structure on O(N) points | proven | | E4 to N = 64; author only | same §4.3 |
| Prop L (w6) | tanglegram isomorphism polynomial if either tree has out-degree ≤ 4; n^{O(d/log d)} in general; FPT in (b, ν) (the last is a sketch) | L.1–2 proven modulo Luks 1993; probably folklore | Luks 1993 Cor. 6.3/6.4 | author only | [w6-tanglegram](../docs/w6-tanglegram.md) §2.1 |
| Prop D, Prop S (w6) | prime decomposition; straddling fibre product with total size ≤ n log₂ n | proven | | author only | same §2.2–2.3 |
| Prop C (w6) | coordinate tanglegrams' groups are generalized wreath products over 2-dim posets | proven; **known prior work**: AMBC 2025 Thm 4.24(a) | | nauty 21/21 | same §2.4, [w8-poset](../docs/w8-poset.md) §0 |
| Theorem 1 (w8-poset) | SI under ∏^{(P)} G_i in b!·2^{O(b^{μ+1})}·N^{O(1)} | proven modulo ADKT Thm 5 | ADKT | brute force / nauty on 1280 instances | [w8-poset](../docs/w8-poset.md) §2 |
| Prop H (w8-poset) | SI over all posets ≡ R1_c ≡ C_h ⊔ C_h ≡ coloured coordinate tanglegrams | proven modulo w4-t2 Theorem A | | E3 32/32 | same §3 |
| Prop B (w8-poset) | a complete-tree tanglegram is coordinate iff its partition lattice is a poset block structure | proven modulo BPRS/AMBC | | E6 | same §5.1 |

## 7. Moonshots: affine equivalence and ETH

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Theorem A (w17) | canonical form/Iso under AGL(k,2) in 2^{k²/2+k/2}·poly(N) | proven modulo Babai–Luks; **known prior work** (folklore) | | AI red-team | [w17-affine](../docs/w17-affine.md), [redteam](../docs/redteam-w17-affine.md) §1 |
| Theorem B (w17) | deterministic Iso in 2^{k²/4+k/2}·poly(N) | proven modulo Babai–Luks; **known prior work** in shape (routine instance of Rosenbaum) | | AI red-team; brute force k ≤ 4 | same §2 |
| Prop B′ (w17) | Ω(2^{k²/4}) flag-canon queries in an oracle model | proven; a generic birthday bound; does **not** show the flag method has hit its limit | | AI red-team | same §3 |
| Theorem C (w17) | d-tensor isomorphism reduces to AGL(dk,2)-SI; hardness conditional on 4-TI | proven reduction; hardness conditional on 4-TI hypothesis | | AI red-team (displayed Iso direction corrected) | same §4 |
| Prop D (w17) | T(f,g) ≤ 2^{(sep(g)+1)k}poly(N); random g: 2^{k log k+O(k)} | proven | | AI red-team | same §6 |
| Prop E (w17) | vectorial quadratic colourings in 2^{O((m+k)^{1.5})} (decision) | proven modulo arXiv:2610.00874 (unrefereed) | GIQS Thm 1.3 | AI red-team (citation) | same §6 |
| Prop G (w17) | Sylow enumeration at classical nodes costs \|P\|_{2′}; "λ coefficient halved" | Sylow count sketch; **"λ coefficient halved" withdrawn as unsupported** | | AI red-team | same §5 |
| ETH preprint review | no flaw found in the core checked; no transfer to GI | review only; not a verification | | one AI review, exact small-case tests | [w21-eth](../docs/w21-eth.md) |
| Prop (feasibility bound, w21) | Lemma 4.7's hypotheses force M ≥ 32 b²(b+w), excluding AGL and TI as written | proven | | author only; `check_transfer.py` | [w21-eth](../docs/w21-eth.md) §B.2 |

## 8. Practical claims

See [Benchmarks](Benchmarks.md) for tables and caveats. All timings are one machine.

| Claim | Status | Checked by | Source |
|---|---|---|---|
| Every benchmark answer of `bench/run.py`, `irhard.py`, `canon.py`, `bounded.py`, `hardness.py` verified (decision, σ, generators, \|Aut\|) | as implemented | run-time verification; no wrong answer recorded | [Software](Software.md#correctness-checks) |
| On `ns` multipedes (n = 2464), dense nauty, sparse nauty and Traces exceed 600 s; ours under 1.5 s | measured; answers from NS Lemma 2.3 re-proved and checked per instance; seed 0 for headline, seeds 1–2 for robustness | audit script | [w1-scale](../docs/w1-scale.md) §3 |
| Canonical forms on `ns` to n = 5632 in about 4 s; nauty modes > 600 s from n = 2464 | measured, seed 0 | as above | [w9-canontool](../docs/w9-canontool.md) §3.1 |
| Traces wins every non-multipede family | measured | | [w14-solver](../docs/w14-solver.md) §3 |
| `gi.canon` polynomial guarantee at d ≤ 5 | **not achieved**: `perm_canon`/`ir_canon` exponential in the worst case | | [w14-solver](../docs/w14-solver.md) §1 |
| Compiled kernel: default hybrid 2.0–2.4×, `ir=0` 1.5×, bounded and canonical 1.00–1.15× | measured, paired | identical output digests; ASan/UBSan clean | [w16-ckernel](../docs/w16-ckernel.md) |
| HJ's local certificates never reduced branching in practice (cost about 10–60×) | measured in round 1 | | [Tried and failed](Tried-and-Failed.md) |

## 9. Not achieved (explicitly)

* An FPT or polynomial algorithm for degree-d graph isomorphism.
* An FPT algorithm for TreeCI, or for tanglegram isomorphism (R1).
* A hardness reduction for TreeCI or R1.
* A lower bound for a general coset-splitting model.
* A 2^{o(k²)} algorithm for AGL(k,2) string isomorphism.
* Any transfer of the HJ string lower bounds to graphs.
