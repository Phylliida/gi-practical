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
| Lean | accepted by the Lean kernel: HJ's main theorem, modulo 10 axioms ([section 1](#1-hj-and-its-lean-formalization-external-result-audited-here)), and the `lean/DegreeD` statements of [section 2](#machine-checked-parts-of-this-section-w36), which report only the three standard axioms and carry the hypotheses their rows state |
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
| **Theorem R\*** | HJ with dispatcher (M′) solves Γ̂_d string isomorphism on N points in exp(O(log(N+2)·log(d+2)))·poly(input) | conditional on (H0) | (H0); GNS Thm 3.13, Lemma 4.4; BCP Lemma 2.2 (or Maróti Cor. 1.5); Luks/Babai–Luks reduction | AI verify, AI red-team (no hole outside (H0)). **Not machine-checked as a theorem**: parts are (see [below](#machine-checked-parts-of-this-section-w36)), but for d < N nothing yet shows the required `Good` runs exist, so it remains conditional and hand-argued there | [verify-theorem-R](../docs/verify-theorem-R.md), [redteam-theorem-R](../docs/redteam-theorem-R.md) |
| **Corollary R\*** | GI of maximum degree d in n^{O(log(d+2))} | conditional on (H0) | as above | as above | same |
| (H1) recognition of option-2 constituents | holds; a theorem from the literature, not a hypothesis | proven modulo GNS 3.13 + Lemma 4.4 (or the self-contained §2.2 variant for m ≥ 3t) | BLS87, Kantor–Luks | AI verify, AI red-team | [verify-theorem-R](../docs/verify-theorem-R.md) §2 |
| (H2) call grouping | at most about 10 q^{2κ} disjoint-domain families; fits `PhaseTree.Hyp` in the Lean | proven (verified against HJ and Lean scripts) | (H0) | AI verify, AI red-team; the regrouping on the real Lean scripts is now machine-checked, with ≤ 9 q^{2κ} families (`aggregate_branch_fam`, [below](#machine-checked-parts-of-this-section-w36)) | same §3 |
| Theorem R\*\* | exp(O(log(N+2)(log w + λ + 1))), w = alternating width, λ = largest classical section dimension | conditional on (H0) and Prop 2.1 (sketch) | (H0), [w1-structure](../docs/w1-structure.md) Prop 2.1 | AI red-team (needs section-closed parameters) | [w1-structure](../docs/w1-structure.md) §3, [redteam](../docs/redteam-w1-structure.md) §2 |
| Per-phase exponent of HJ | O(log N·(log w + μ + log log N)) | sketch | (H0) | author only | [moonshot-theory](../docs/moonshot-theory.md) §2.9 |
| Lemma 1 (ρx is slack) | ρ·O(log log N) suffices in HJ's analysis | proven given HJ's step structure | (H0) | author only | same §2.2 |
| Outer phase recurrence is lossless | no gain possible from N → N^γ recurrence | proven | (H0) | author only | same §2.7 |
| Theorem C (w3, HJ-canon) | canonical forms for Γ̂_d strings in exp(O(log N log d + log^c d)); degree-d graphs in n^{O(log d)}·exp(polylog d) | conditional on (H0), BC, BL83; assembly sketched | (H0), BC, BL83 | author only | [w3-canon](../docs/w3-canon.md) §2.4 |
| Theorem H (w3, frontier hybrid) | poly(N)·min over invariant frontiers of Σ HJC + Σ combine costs; never worse than R\* | conditional on w3 Theorem C (canonical); on (H0) for the isomorphism version | see left | author only | [w3-canon](../docs/w3-canon.md) §3.6 |
| Lemma N (canonical forms descend to normal subgroups); Theorem E-canon | polynomial descent; canonical forms in Σ_B \|P_B\| δ_B poly(N), δ_B ≤ ε_B | proven modulo BC framework | BC §5 | author only | [w3-canon](../docs/w3-canon.md) §3.2–3.3 |
| Theorem P-canon | canonical forms for any G ≤ Sym(Δ) ≀ S_k in product action in 2^{polylog b}·N^{1.59+o(1)} | sketch modulo Wiebking's canonizer | Wie20 Cor. canObj0 | author only | [w3-canon](../docs/w3-canon.md) §3.4 |
| Corollary F (w8) | degree-d GI in n^{O(log² d)} without HJ's primitive-valuation lemma | conditional on HJ §§4–7; weak budget (Theorem E of w8) is a sketch; still uses CFSG through GNS 3.13 | HJ §§4–7 | AI red-team at proof-sketch level | [w8-gnsexp](../docs/w8-gnsexp.md) §3.3, [redteam](../docs/redteam-w8-gnsexp.md) §6 |

### Machine-checked parts of this section (w36)

`lean/DegreeD/`, 3,342 lines, no `sorry`, compiled against the HJ build. For the five theorems named `GI.…` below, `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`, re-verified independently by a fresh compile ([overnight log](../docs/overnight-log.md)). These are implications about the Lean model: the rows state what each one assumes. **They do not prove Theorem R\*:** for d < N nothing yet shows the required `Good` runs exist (Γ̂_d closure and the (M′) dispatcher are not formalized), so the full n^{O(log d)} theorem is still conditional and hand-argued there. Details and gaps: [Lean audit](Lean-Audit.md#the-degree-d-accounting-in-lean-w36).

| Lean name | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| `GI.Paper.PhaseTree.HypL.cost_le` | Lemma 7.1 with a parameter Λ: a phase tree meeting `HypL` terminates, and each node costs ≤ K(s+2)^D exp(Φ_Λ); HJ's constants, no N in the multiplicity column | conditional on `HypL` | `HypL`; a valid weight Λ | Lean | [w36-lean](../docs/w36-lean.md) §2 |
| `GI.DegreeD.abstract_R_star` | abstract recurrence: absolute `base` and C′ with F(N) ≤ exp(C′·Λ·log(N+2)) for every F ≥ 0 bounded below `base` whose phases are provided by `PhaseStep`, Λ ≥ log 48 | conditional on `PhaseStep` at every N ≥ `base` | `PhaseStep` | Lean | same |
| `GI.Algorithm.aggregate_branch_fam` | (H2) on the real scripts: the branch sums of the `Continue` calls of an aggregation round fall into ≤ 9 q^{2κ} families of total size ≤ s | proven | an actual aggregation round of the Lean scripts | Lean | same |
| `GI.Algorithm.phaseTreeOn_hypL`, `GI.Algorithm.real_runs_cost_le` | the real phase tree restricted to a child-closed `Good` meets `HypL` at Λ = `lam d`, so every `Good` vertex costs ≤ K(s+2)^D exp(Φ_Λ) | conditional; **for d < N no `Good` set with these properties is shown to exist** | `Good` child-closed; `Run.VertexBound` on `Good` (q ≤ max(d,6) at giant steps, dispatcher cosets ≤ `multL`); cost hypotheses `leaf_cost`, `toll` | Lean | same |
| `good_le_N_conditions`, `real_runs_hypL_x`, `example_hypL` | non-vacuity: the hypotheses hold on real runs at d ≥ N (`Good` := s ≤ N), and at Λ = x; an explicit tree meets `HypL` with Λ fixed. None covers d < N for real runs | compiled, no `sorry`; not in the re-verified axiom list | | author only (compile) | same §2 |

## 3. Lower bounds for specific algorithms, and barriers

These are about what particular algorithms do, or about implications; none is a general lower bound for
GI. The string-isomorphism bounds of w1 have not been transferred to graphs; the graph bound of w18 (Theorem B1) is a separate one, through a different channel.

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Prop 2 (moonshot) | HJ on AGL(k,2), N = 2^k, makes ≥ 0.288·N^{1+log₂N} coset branches for all strings | proven, given HJ's dispatcher as written | — | author only; dispatcher traced in Lean by later red-teams; w17/w20 show the bound is about HJ's dispatcher, not the problem | [moonshot-theory](../docs/moonshot-theory.md) §2.5 |
| Prop 3.1, Cor 3.2 (w1-fpt) | for odd D ≥ 3, G = (F₂^{D−1} ⋊ S_D) ≀ C_m (m = 2^j) is primitive, affine, in Γ̂_D; HJ and HJ+(M′) create ≥ \|G\| ≥ N^{log₂D − 0.443} children on every instance; GNS 3.13's exponent is sharp at fixed d | proven | HJ pseudocode only (not (H0)) | AI red-team | [w1-fpt](../docs/w1-fpt.md) §3.1, [redteam](../docs/redteam-w1-fpt.md) §1 |
| Prop 4.2 (w1-structure) | on G_{r,L} and AGL(r,2)^L, HJ+(M′) makes ≥ N^{r+1−1.8/r−o(1)} branches | proven from pseudocode; independent of (H0) | — | AI red-team | [w1-structure](../docs/w1-structure.md) §4.6, [redteam](../docs/redteam-w1-structure.md) §5 |
| Group-iso and combinatorial barriers | n^{o(log n)} GI would give n^{o(log n)} for group, quasigroup, Steiner triple, conference-graph isomorphism, and 2^{o(k²)} for AGL(k,2) string isomorphism | proven reductions | — | author only | [moonshot-theory](../docs/moonshot-theory.md) §3 |
| Theorem B1 (w18) | on the point–line incidence graph of PG(m−1,2), HJ as written (every κ-subset tested, no pruning or memoization) has a recursion tree of at least 2^{m²/2−O_κ(m)} = n^{(1/8)log₂ n − O_κ(1)} nodes, for every fixed κ ≥ 5 and m ≥ m₀(κ, a, N₀); through the σx channel, not enumeration. **Asymptotic only:** at κ = 64 and Lean's parameters (enumeration cutoff q₁ = 486290, not q₀) there are no levels below m = 150 and no nesting below m = 214 (n ≈ 2^425), so it says nothing about feasible inputs or about GI. A pruning or memoizing variant is not covered | proven, given HJ as written; sound as a statement about HJ as written, after correcting that constant | HJ as written; exact answers from recursive calls | AI red-team (hand-check of Lemmas 1, 2, the dispatcher and the count; exact replay of windows at κ = 3, 4, 5, m ≤ 7; no run nests two certificate calls). Simulations support the window shape only | [w18-latin](../docs/w18-latin.md) §2, [redteam](../docs/redteam-w18-latin.md) §2, §6 |
| B4 (w18) | HJ is n^{Θ(log n)} on graphs | sound as an implication: the lower half is B1, the upper half is HJ's unrefereed theorem | (H0) for the upper half | AI red-team | same §0 |
| M1, M2 (w28) | on X_m the table of distinct exact kernel states has at least ∏_{i<j} binom(r_i, κ)₂ entries at level j, so memoized HJ still makes 2^{m²/2−O_κ(m)} calls; any memo key determining D_j still has 2^{m²/4−O_κ(m)} values, so at best n^{(1/8)log n} → n^{(1/16)log n} | proven | HJ as written | AI red-team (flag recovery re-derived, sound; M1 in the form stated here) | [w28-sigma](../docs/w28-sigma.md) §3, [redteam](../docs/redteam-w27-w28.md) §6 |
| P1 (w28) | pruning tests and aggregation branches by *certified* automorphisms preserves every aggregation input | proven; standard automorphism pruning; the red-team gave no separate verdict | HJ as written | author only | [w28-sigma](../docs/w28-sigma.md) §4 |
| P3 (w28) | pruning by equality of prefix comparisons is unsound | labelled proven in w28 with a gap: the existence of R rested on a sketched union bound. Closed by the red-team's explicit R, \|R\| = O(κ²), independent of m | HJ as written; m ≥ 3κ | AI red-team (explicit R checked at κ = 3, m = 9) | same §4, [redteam](../docs/redteam-w27-w28.md) §6 |
| P2 (w28) | that pruning collapses X_m to n^{O_κ(1)} nodes (needs pruning of Case 2b branches too) | sketch; explicitly not certified by the red-team | | author only | [w28-sigma](../docs/w28-sigma.md) §4 |
| C1 (w28) | any Aut-invariant test rule on X_m is all-or-none on independent T at each level | proven | | AI red-team (correct) | same §5, [redteam](../docs/redteam-w27-w28.md) §6 |
| L1 (w28), lazy HJ (LHJ) | stopping certificates before Step 4 and escalating only on a uniform class of at least ¾ is correct (w28's step 3 had the boundary as ≤ ¾; escalation is at ≥ ¾); its children are a subset of HJ's types, so Lemma 7.1's class bounds hold | proven, given HJ, after that fix | (H0) | AI red-team (sound given HJ; HJ L2619–2800, L2841–2853, the phase induction and Helfgott §6.2 read) | same §5, [redteam](../docs/redteam-w27-w28.md) §5 |
| L2 (w28) | on X_m, at the root and every chain state, LHJ has no twin class of size ≥ 2, so the B1 chain is not created. "Never starts" is a statement about the root | proven at the root and chain states; whole tree a sketch | | AI red-team (sound given HJ; replays at level 0 and level 1); root-model replay at m = 5, 6 | same §5, [redteam](../docs/redteam-w27-w28.md) §5 |
| Q1 (w28) | unpruned LHJ on X_m still pays 2^{Ω(m²)}, through anchors in the Q channel (Miller's generator enumeration) | sketch; explicitly not certified by the red-team | | author only | [w28-sigma](../docs/w28-sigma.md) §6 |
| Lemma R, Theorem U (w28) | variable-block Ray-Chaudhuri–Wilson; a uniform first window on C forces \|B\| ≥ binom(\|C\|, ⌊κ/2⌋) or a Sym(C)-symmetric window | proven, product states only (the first window being B × T is part of the hypothesis); routine; the uniform case is Ray-Chaudhuri–Wilson 1975, the variable-block form not found stated | | AI red-team (sound) | same §7, [redteam](../docs/redteam-w27-w28.md) §7, §9 |
| R1 (w28; not the tanglegram R1) | corrected rigid variant X_{m,R} (O(m) deleted lines): HJ makes n^{(1/8)log₂ n − O(log log n)} calls | proven given HJ for the level steps; root entry and "P1 pruning removes nothing" remain sketches. The red-team notes the O(log log n) error can be O_κ(1) | (H0) | AI red-team (level steps re-derived; sound as labelled; root entry traced, not written out) | same §8, [redteam](../docs/redteam-w27-w28.md) §8 |
| R2 (w28; not the tanglegram R2) | the rigid variant is not a barrier: 1-WL makes deletion variants discrete in ≤ 5 rounds in every rigid instance tested (m ≤ 9); Pasch-switched variants fall to one bounded-WL invariant | experiment only; the correction of w18 §2.9 is proven | | small random instances; `rigid` and `pasch` rows reproduced by the red-team, which found the correction sound | same §8, [redteam](../docs/redteam-w27-w28.md) §8 |
| Theorem L (w28; not w1-structure's) | prefix-determined Step-4 rules on X_m: the recursive branch pays B1, the lazy branch pays Q1; on X_{m,R} only the recursive branch is bounded | recursive proven, lazy a sketch; conditional on the rule firing at all levels, as stated | | AI red-team (L(i), (ii) correct) | same §9, [redteam](../docs/redteam-w27-w28.md) §6 |
| Per-phase exponent without σx (w28) | removing σx leaves O(log N(log w + μ + log log N)), because x² and Q also pay log N·log w | as the per-phase exponent above (sketch); the red-team gave no separate verdict | (H0) | author only | same §10 |
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
| Prop N, Lemmas 1–2 (w27) | if Y_c (depth-c iterated wreath power of A₅) is a section of G and G has a normal series of length ℓ with factors in direct products of S_b, then c ≤ ℓ·D(b), D(b) = 1 + log₅ log₆₀ b!. Covers every subgroup of S_b^{(P)}, P of height ℓ | proven | | AI red-team (every step re-derived, sound) | [w27-tree](../docs/w27-tree.md) §2.1, [redteam](../docs/redteam-w27-w28.md) §1 |
| Cor N.1 (w27) | for b₀ ≥ 5, no parameterized reduction from R1_c(b₀) to SI under S_b^{(P)}, P of height ≤ ℓ, can reflect Aut at the identity tanglegrams. Sound as stated; **narrower than advertised**. Sharp form: if φ reflects at x, td(Aut(x)) ≤ ℓ·D(f(b₀)). A hardness proof for height-2 posets cannot be of the gadget kind used so far; this reduces nothing to the FPT side | proven (narrowed by the red-team) | | AI red-team | same, [redteam](../docs/redteam-w27-w28.md) §1, §9 |
| Lemma MD (w27) | for b ≥ 5 and R transitive on r points, Sym(b) ≀ R has minimal faithful degree exactly rb | proven; very likely folklore | Scott's lemma | AI red-team (sound) | [w27-tree](../docs/w27-tree.md) §2.2, [redteam](../docs/redteam-w27-w28.md) §3, §9 |
| Reduction 0 (w27) | HT2 with T₂ fixed or enumerable is FPT | proven modulo ADKT | ADKT | author only | [w27-tree](../docs/w27-tree.md) §1 |
| Theorem G (w27; not w12's) | if x has a pinning set of ρ row (or column) blocks: (b!·b^m)^ρ · b!·2^{O(b)}·N^{O(1)}. **XP in ρ, not FPT in (b, ρ)**, since (b^m)^ρ = N^{Θ(ρ)}; FPT in b for constant ρ | proven modulo ADKT Thm 5 | ADKT Thm 5 | AI red-team (sound; cost correct; exhaustive equivalence test, 0 disagreements, with twins and ρ ≤ 2, control has power); E1 90/90 against nauty | [w27-tree](../docs/w27-tree.md) §2.3, [redteam](../docs/redteam-w27-w28.md) §2 |
| Theorem G+ (w27) | r top coordinates plus ρ row blocks: (b!)^r (b!·b^m)^ρ · b!·2^{O(b)}·N^{O(1)}. FPT in r; XP in ρ | proven modulo ADKT | ADKT | AI red-team (sound; about 150k tests, 0 disagreements) | same |
| Theorem C (w27; not w3's, w8's or w17's) | if the surviving top C has a soluble pointwise stabilizer of a *given* r-coordinate set R: (b!)^{r+2}·N^{O(1)}; FPT in (b, r) with an extra r^{O(r)} if R must be found | proven modulo Luks's recursion and Pálfy–Wolf. w27 cited Luks 1982 alone, which gives only XP | Luks 1982; Pálfy–Wolf (from memory) | AI red-team (by hand, two fixes; not implemented) | same §2.4, [redteam](../docs/redteam-w27-w28.md) §2 |
| Lemma 3.1, Prop 3.2 (w27) | on the code instances (one pad leaf per side added), a definable one-call combine needs ℓ = Ω(s²/log s) leaves while n − n_max = 2s, at b = 2. W6 lead 2 is false as stated; tight up to log. A limit on that route, not hardness (b = 2 is polynomial) | proven modulo T2 Thm B's encoding, after a small repair: as written it needs every data pair to straddle | T2 Thm B encoding | AI red-team (sound, one small gap; 34/35 at s ≤ 16 on binary tanglegrams, the failure being the gap); E3 100/100 | [w27-tree](../docs/w27-tree.md) §3.1, [redteam](../docs/redteam-w27-w28.md) §4 |
| Flat components via S-W objects (w27 §2.5) | isomorphism for gain graphs with trivial holonomy, via T-equivariant objects | sketch | Schweitzer–Wiebking | author only | [w27-tree](../docs/w27-tree.md) §2.5 |
| Low-support generation of π₁ (w27 §2.5) | with large point stabilizers in C, π₁(Γ) normally generated by closed walks using O(1) values per coordinate | speculation; E2 (limited: orbitals of full products, N ≤ 243) | | not checked | same |
| Height-2 FPT; FPT for R1_c (w27) | **not settled**; R1_c open, no new upper bound | open | | | same §0 |

## 7. Moonshots: affine equivalence, ETH, Latin squares, Steiner systems, conference graphs, cubics

| Result | Statement | Status | Assumes | Checked by | Source |
|---|---|---|---|---|---|
| Theorem A (w17) | canonical form/Iso under AGL(k,2) in 2^{k²/2+k/2}·poly(N) | proven modulo Babai–Luks; **known prior work** (folklore) | | AI red-team | [w17-affine](../docs/w17-affine.md), [redteam](../docs/redteam-w17-affine.md) §1 |
| Theorem B (w17) | deterministic Iso in 2^{k²/4+k/2}·poly(N) | proven modulo Babai–Luks; **known prior work** in shape (routine instance of Rosenbaum) | | AI red-team; brute force k ≤ 4 | same §2 |
| Prop B′ (w17) | Ω(2^{k²/4}) flag-canon queries in an oracle model | proven; a generic birthday bound; does **not** show the flag method has hit its limit | | AI red-team | same §3 |
| Theorem C (w17) | d-tensor isomorphism reduces to AGL(dk,2)-SI; hardness conditional on 4-TI | proven reduction; hardness conditional on 4-TI hypothesis | | AI red-team (displayed Iso direction corrected) | same §4 |
| Prop D (w17) | T(f,g) ≤ 2^{(sep(g)+1)k}poly(N); random g: 2^{k log k+O(k)} | proven | | AI red-team | same §6 |
| Prop E (w17) | vectorial quadratic colourings in 2^{O((m+k)^{1.5})} (decision) | proven modulo arXiv:2610.00874 (unrefereed) | GIQS Thm 1.3 | AI red-team (citation) | same §6 |
| Prop G (w17) | Sylow enumeration at classical nodes costs \|P\|_{2′}; "λ coefficient halved" | Sylow count sketch; **"λ coefficient halved" withdrawn as unsupported** | | AI red-team | same §5 |
| Theorem A1 (w18) | quasigroup, Latin-square isotopy, paratopy and STS isomorphism in n^{(1/2)log₂ n + O(1)} time and space; Latin-square graphs on N vertices of large order in N^{(1/8)log₂ N + O(1)}, assuming recovery of the net (the memo originally said 1/4) | proven; sound after four repairs; a routine application of Rosenbaum's bidirectional collision, not found stated for quasigroups | net recovery from memory (Bruck/Bose) | AI red-team; small machine sanity check | [w18-latin](../docs/w18-latin.md) §3.1, [redteam](../docs/redteam-w18-latin.md) §3, §6 |
| Theorem A2, Lemma A3 (w18) | quasigroup isomorphism in poly(n, M, A) (M subquasigroups, A their automorphism groups); structural lemmas | proven; A2 sound, A3 sound after two wording fixes; not found in the literature | | AI red-team | same §3 |
| Latin-square graphs of Z₂^m; STS block graphs (w18, B2) | same 2^{Ω(m²)} chain | sketch; red-team found the gap as labelled (root entry unverified; small replays neither exhibit nor refute the chain) | | AI red-team; window pattern simulated | [redteam](../docs/redteam-w18-latin.md) §4 |
| Paley graphs polynomial for HJ (w18, B3) | no chain, since Aut is solvable | sketch; gap as labelled (the polynomial claim needs unwritten aggregation accounting) | | AI red-team; Paley(101) nonfull at the second iteration | same §4 |
| Rigid variant of X_m (w18 §2.9) | a single switched block kills Aut | **withdrawn**: false (w28; found sound by the w31 red-team); see Theorem R1 (w28) in section 3 for the corrected variant | | AI red-team | [w28-sigma](../docs/w28-sigma.md) §8, [redteam](../docs/redteam-w27-w28.md) §8 |
| ETH preprint review | no flaw found in the core checked; no transfer to GI | review only; not a verification | | one AI review, exact small-case tests | [w21-eth](../docs/w21-eth.md) |
| Prop (feasibility bound, w21) | Lemma 4.7's hypotheses force M ≥ 32 b²(b+w), excluding AGL and TI as written | proven | | author only; `check_transfer.py` | [w21-eth](../docs/w21-eth.md) §B.2 |
| L1 (w30), rank–closure duality | rk(X) = min_T(ρ(T) + ⌊log₂((n+1)/(\|T\|+1))⌋); every ρ-generated subsystem has size ≤ 2^{ρ+c} − 1 | proven | | AI red-team (exact lattices on 114 systems) | [w30-sts](../docs/w30-sts.md) §2, [redteam](../docs/redteam-w30-sts.md) §2 |
| T1 (w30, improved by w33) | for 1 < λ < (log₂10)/3 ≈ 1.1073, every maximizer S ≠ X of Ψ_λ has cosets forming a PG(d−1,2), with d ≥ r − c/(λ−1) and S ≠ X when r > ℓ/λ; so r > 0.9031ℓ suffices, and d ≥ r − 9.32c. The threshold is sharp at AG(2,3). The memo's own numbers (λ < (log₂9)/3, r ≥ 0.947ℓ, 17.7c) are superseded | proven; re-derived, then sharpened by the red-team | | AI red-team | [w30-sts](../docs/w30-sts.md) §3, [redteam](../docs/redteam-w30-sts.md) §2.3, §7 |
| P1 (w30; not w28's) | converse: a PG(d−1,2)-fibration has rank ≥ d | proven | | AI red-team | [w30-sts](../docs/w30-sts.md) §3 |
| T2 (w30) | for non-constant χ, χ′: X_χ ≅ X_χ′ iff χ′∘A = χ for some A in GL(d,2). Linear equivalence of Boolean functions on F₂^d many-one reduces to STS isomorphism on n = 2^{d+3} − 1 points, with r ≥ ℓ − 3. So n^{o(log n)} for STS (or quasigroup) isomorphism implies 2^{o(d²)} string isomorphism under GL(d,2). **An implication, not a lower bound**, and nothing shows these are the hardest STS. Isomorphisms surject onto linear equivalences with gauge kernel K | **machine-checked in Lean** ([w54](../docs/w54-lean-t2.md), 3 standard axioms); hand proof; exact checks to d = 4 | gadget properties (a), (b) | AI red-team (hand proof re-derived; exact checks on all 8256 colouring pairs at d = 3 and all 1035 pairs of the 46 orbits at d = 4; samples at d = 5). No prior reduction to STS isomorphism found, not "new" | [w30-sts](../docs/w30-sts.md) §6, [redteam](../docs/redteam-w30-sts.md) §1, §5, §7 |
| T2 family, upper bound (w33) | on the X_χ family, STS isomorphism is polynomially equivalent to linear equivalence, so it is decided in 2^{d²/4+O(d)}·poly(n) = n^{(1/4+o(1))log₂ n} | proven given w17 Theorem B | w17 Theorem B | AI red-team (its own statement) | [redteam](../docs/redteam-w30-sts.md) §1.5, §7 |
| Prop A (w33) | Latin-square isotopy of the Steiner loop squares of order 2^{d+3} iff GL-equivalent, for gadgets with (a), (b) and (c) (M₁ not isotopic to the Cayley table of F₂³; includes w30's table). Replaces w30's sketch | proven by the red-team | | AI red-team only; nauty at d ≤ 3 | [redteam](../docs/redteam-w30-sts.md) §1.6 |
| T3 (w30) | under an index-gap hypothesis, a linear space with lines of size q+1 and planes projective planes of order q; a PG(d−1,q) only for d ≥ 4 (q a prime power) | proven | index gap | AI red-team (sound; small fixes) | [w30-sts](../docs/w30-sts.md) §4, [redteam](../docs/redteam-w30-sts.md) §3 |
| T5 (w30) | an STS within D < (n−2)/24 blocks of a PG is decided in (6D)^{min(m,6D)}·poly(n), so n^{o(log n)} for D = n^{o(1)}; must reject X′ that does not decode | proven, after adding the rejection step | | AI red-team | same §7, §3.2 |
| C4 / Prop 2 (w30) | refutes w18's "locally algebraic" lead, as a statement about the Steiner loop L_g (not the Steiner quasigroup, where PG already fails w18's definition) | proven for the Steiner loop | Albert, Bruck (from memory) | AI red-team | same §5, §4.1 |
| No bilinear or trilinear core at p = 2 (w30 §6) | alternating bilinear cochains are coboundaries; no nonzero alternating trilinear associator exists | proven | | AI red-team (checked on all cochains) | same §6, §4.1 |
| Near-top bound (w30 §6) | n^{(1/4+o(1)) log n} for c = O(1) | **sketch**, named gaps; not signed by the red-team (only the T2 family is) | | AI red-team | [redteam](../docs/redteam-w30-sts.md) §4.2 |
| Rank dichotomy for rk ≥ ε log n (w30 §9) | open; the conjecture is speculation | open | | | [w30-sts](../docs/w30-sts.md) §9 |
| Fibration form of T1, T2 | PG-fibred form of low-2-rank STS | **known prior work**: Jungnickel–Tonchev Thms 2.5, 2.7–2.9; the cocycle description (Grishkov et al.) also not new | | AI red-team | [redteam](../docs/redteam-w30-sts.md) §5 |
| T-identities, Lemmas 2.1–2.4, Prop 2.5 (w32) | Σ_v T(a,b,v)² = n² − 2n − 1; T ≡ 2 (mod 4); round-2 criterion; 2-rank of A | proven; likely folklore; first 2-rank case Brouwer–van Eijl | | author only (numerics on 24 graphs); **w32 not red-teamed** | [w32-conference](../docs/w32-conference.md) §2 |
| Thm 3.2 (w32; not w34's), bad-pair reduction | 2⌈3/c⌉ vertices leave only cliques of B_c after two 1-WL rounds | proven; trivial | | AI red-team | same §3, [redteam-w32-conference](../docs/redteam-w32-conference.md) |
| Lemma 4.1, Thm 4.2 (w32) | Turyn lift: on iterated Turyn products of P(9), pairs have collision probability ≥ 0.049 for all n, so uniform anti-concentration is false. Not an individualization lower bound | proven; sound on AI red-team (c = 0.0493) | | author only; numerics; w37 re-ran Lemma 4.1 on 1200 triples (0 mismatches) | same §4, [redteam](../docs/redteam-w35-w34.md) §8 |
| Thm 5.1 (w32), Paley, O(1) individualizations | 1-WL discrete in two rounds after O(1) vertices, via Deligne–Katz | sketch; constants not written; unverifiable as a sketch | | AI red-team | same §5, [redteam-w32-conference](../docs/redteam-w32-conference.md) |
| Minimum individualization depth (w32) | exact minimum 1-WL depth 2 or 3 in every tested graph, up to n = 6561 | **data**; cannot separate O(1) from slow growth; large examples are all algebraic or products | | experiment | same §6 |
| Thm 2.1 (w34) | for every conference graph, ⌊½ log₂ n⌋ − 4 ≤ VC(E¹) < 2 log₂ n | proven | | AI red-team (sound; all lines checked; run on P(65537)) | [w34-vc](../docs/w34-vc.md) §2, [redteam](../docs/redteam-w35-w34.md) §7 |
| Prop 3.1, Thm 3.2 (w34) | on iterated Turyn products, VC of the separation system of k-tuples after r ≥ 1 rounds is ≥ log_v n − 1 (k ≤ v − 2). Obstructs VC as a proof technique, not small hitting sets | proven (at r = 0 no separation occurs, so the statement is empty) | | AI red-team (sound; exact 1-WL at n = 625, 648/648) | same §3, §7 |
| Thm 4.1 (w34) | depth ≤ 2⌈3 ln n/ln(1/τ)⌉ + 88 d(τ) + 22 | proven (easy) | ε-net theorem | AI red-team (sound; constants checked) | same §4, §7 |
| Prop 4.2 (w34) | on Turyn iterates d(τ) grows, so Thm 4.1 cannot beat Θ(√log n) there | proven, with two notational fixes ("equivalently" holds only for τ in range) | | AI red-team | same §4, §7 |
| E1, E2 (w34) | if d(τ) = o(log n) for some τ → 0, uniformly over conference graphs, then depth o(log n) and isomorphism in n^{o(log n)}. Hypothesis open; proved for no non-trivial family | conditional on that hypothesis; E2 reads O(√(A log n) + 1) | d(τ) bound | AI red-team (implication only) | same §4, §7 |
| Prop 5.2, §6 energy identity (w34) | row-pair formula for T on Turyn products; equitable-partition identity. No growth lemma follows | proven; outside the red-team's scope | | author only; numerics (7846 triples; Paley and Spence) | [w34-vc](../docs/w34-vc.md) §5–6 |
| Latin squares of Z₂^k (w34 §7) | individualization depth Ω(log n) by base size, so the analogue of Levet's question is negative for Latin squares; none known for conference graphs | proven, elementary | | AI red-team | same §7 |
| Theorem A (w35), squares gadget | alternating matrix tuple/space isometry on (n, m) reduces to quadratic-form tuple/space isometry on (n+m, m) | proven by hand; treat as folklore-adjacent | | AI red-team (sound for all n; exact tests) | [w35-cubic](../docs/w35-cubic.md) §2.2, [redteam](../docs/redteam-w35-w34.md) §1, §6 |
| Theorem B (w35), exact cubic reduction | if Rad τ_f = Rad τ_g = 0: f∘L = g for some L in GL(n,2) iff the (n+1)-dimensional spaces of forms Φ(f), Φ(g) on F₂^{2n} are isometric. Sharper (w37): solutions S biject with Iso(f,g) | proven by hand. Appears new as far as a limited search could determine | | AI red-team (both directions by hand, all n; exhaustive at n = 3, samples at n = 5, 6) | same §2.3, [redteam](../docs/redteam-w35-w34.md) §2, §6 |
| Theorem C (w35), radical elimination; composite | f⁺ has Rad τ = 0, and f ~ g iff f⁺ ~ g⁺; so f ~ g iff Φ(f⁺), Φ(g⁺) are isometric (2n+2 forms on F₂^{4n+2}) | proven by hand | n ≥ 2 | AI red-team (sound) | same §2.4–2.5, [redteam](../docs/redteam-w35-w34.md) §3 |
| Theorem D (w35), cubic equivalence | decide AGL(n,2)- or GL(n,2)-equivalence of cubics in 2^{Õ(n^{1.5})}, worst case, all cubics. Decision only; not a canonical form. A second route (w37) via Thm F gives GL-equivalence in 2^{O(n^{51/26} log n)} | **conditional on GIQS Thm 1.2** (arXiv:2610.00874, unrefereed, repairable defect in Thm 4.9 Step 3, proofs partly audited); second route conditional instead on Sun, arXiv:2611.05920 Thm 1.1 (unrefereed) | GIQS Thm 1.2, or Sun Thm 1.1 | AI red-team (parameter accounting checked; the preprints' proofs not verified) | same §3, [redteam](../docs/redteam-w35-w34.md) §4 |
| Consequences E(i)–(iii) (w35) | alternating tuple and space isometry, 3-tensor isomorphism, ATF equivalence over F₂, in 2^{Õ(L^{1.5})} | conditional on GIQS Thm 1.2; (ii), (iii) also on GQ IV Thm 2.1 / Cor. 5.4 (FGS19 not re-verified). E(i)'s tuple case is **known prior work** as a statement: Sun, arXiv:2611.05920 Thm 2.1/A.1 (bounds incomparable) | as listed | AI red-team | same §3.2, [redteam](../docs/redteam-w35-w34.md) §4, §6 |
| Theorem F (w35) | exact GL-equivalence of cubics reduces, in time polynomial in \|G\| = 2^{O(n)}, to Cayley-table isomorphism of 2-groups of Frattini class 2 (order 2^{6n+4}) | proven modulo Higman's criterion as cited in GIQS | Higman | author only; the red-team uses it for the second route without a separate verdict | same §3.3, [redteam](../docs/redteam-w35-w34.md) §4 |
| G (w35), STS with cubic colourings | T2 instances with cubic χ are decided in n^{Õ(√log n)}; nothing for general STS. Hard T2 instances, if any, need degree ≥ 4 | conditional on GIQS Thm 1.2 | GIQS Thm 1.2 | AI red-team | same §5, §4 |
| Char-2 obstacle (w35 §1) | located at the *-symmetric decomposition X\*X = E; explicit instance on F₂⁶. The instance is valid but not char-2-specific; w37 gives one that is | proven (the instance) | | AI red-team | same §1.2, [redteam](../docs/redteam-w35-w34.md) §5 |

### Waves 38–46

| Claim | Statement | Status | Checked by | Source |
|---|---|---|---|---|
| `degreeD_stage1` (w38) | any `M.Run` on a Γ̂_d state returns the exact transporter at tree cost ≤ exp(C′·log(8·max(d,6))·log(s+2)) | machine-checked; 3 standard axioms, BCP and GNS 3.13 as hypotheses. Cost is an abstract weight | fresh compile; AI red-team w41 | [w38](../docs/w38-lean-stage1.md), [w41](../docs/redteam-lean-stage1.md) |
| `graphIso_final` and variants (w42) | as stated, trivially true | **do not cite**; renamed `*_weak` | Lean proof of the trivial witness | [w42](../docs/w42-lean-supply.md) |
| `graphIso_reduction` (w43) | the named script `luksScript` computes the explicit read-off on every oracle, asks only layer instances, is exact, and has a run with ≤ exp(C log(d+2) log(n+2)) nodes | machine-checked; 3 standard axioms, `bcp`, `gnsPrimitive`, six cited hypotheses. Node count, not machine time; "explicit" is a reader's check | independent fresh compile and axiom check; no red-team of the definitions | [w43](../docs/w43-lean-statement.md) |
| Theorem A (w47) | HJ reaches a node with group GL(V)_ℓ and \|GL(m−2,2)\| children on X_m; P acts on 2-subspaces under a coordinate top partition, μ = (1/8+o(1)) log₂ N | proven from HJ as written with exact recursive answers; asymptotic only (n ≥ 2^125 at κ = 64) | AI red-team w48; group identified exactly for m = 5..8 | [w47](../docs/w47-mu.md), [w48](../docs/redteam-w47-mu.md) |
| Theorem C (w47) | which HJ nodes can enumerate | **broken as stated**, repair hand-checked only | AI red-team w48 | same |
| Theorem T (w49) | on a Cayley graph on F₂^d⊗F₂^e, HJ enumerates GL(d,2) at a node, for a resolution whose Case 2b orbital is R₁ | proven given H0; n ≥ 2^33280 at κ = 64 | AI red-team w51 | [w49](../docs/w49-pruned.md), [w51](../docs/redteam-w49-pruned.md) |
| Theorem P (w49) | left-only pruning leaves ≥ [GL:Sp] children; two-sided pruning leaves \|Cl(GL(d/2,2))\|, polynomial in N | "any pruning" **broken**; corrected form rests on a classification cited from memory | AI red-team w51 | same |
| Polynomial canonization (w40) | deterministic polynomial canonical forms at fixed d ≤ 5; n^{O(d²)} with `guarantee=True` | hand proof; needs d fixed; exponent about 53 is an estimate | AI red-team w44 | [w40](../docs/w40-solvable.md), [w44](../docs/redteam-w40-solvable.md) |
| T1 (w45) | 4-tensor isomorphism in q^{n²} poly | proven modulo Qiao–Sun Thm 1.1 | AI red-team w46 | [w45](../docs/w45-quartic.md), [w46](../docs/redteam-w45-quartic.md) |
| T2 (w45) | h-tuples of 3-tensors reduce to one 3-tensor of length O(hn) | proven | AI red-team w46; exact tests | same |
| T3, T3′ (w45) | a quartic subclass; T3′ needs f_i(0) = 0 | conditional | AI red-team w46 | same |
| Theorem H (w45) | quartic equivalence in 2^{(2√2+o(1))d²/√min(s,d/2)} poly(d); beats 2^{d²/4} from s = 132 as printed | proven, threshold repaired | AI red-team w46 | same §1 |

### Gain-graph core (w50, w53)

| Claim | Statement | Status | Checked by | Source |
|---|---|---|---|---|
| Theorem B (w50) | parity map π₁ → 𝒟 onto; normal generating sets need ≥ dim 𝒟 walks with ≥ g values on ≥ d(𝒟) coordinates; refutes W for absolute k, c | proven; parity map on π₁ is in Matsushita 2017, the code coupling appears new | AI red-team w53 | [w50](../docs/w50-gain.md), [w53](../docs/redteam-w50-gain.md) |
| Theorem A (w50) | coordinate groups 2-transitive: 3 values per coordinate suffice (4 in the memo), optimal | proven | AI red-team w53, exhaustive for b ≤ 5, M ≤ 3 | same |
| Prop E, Cor E.1 (w50) | abelian gains on folded-cube family FPT | proven, Cor E.1 modulo Schweitzer–Wiebking; not proved for odd graphs | AI red-team w53 | same |

## 8. Practical claims

See [Benchmarks](Benchmarks.md) for tables and caveats. All timings are one machine.

| Claim | Status | Checked by | Source |
|---|---|---|---|
| Every benchmark answer of `bench/run.py`, `irhard.py`, `canon.py`, `bounded.py`, `hardness.py` verified (decision, σ, generators, \|Aut\|) | as implemented | run-time verification; no wrong answer recorded | [Software](Software.md#correctness-checks) |
| On `ns` multipedes (n = 2464), dense nauty, sparse nauty and Traces exceed 600 s (w1); ours 0.34 s (w23, biso; 1.41 s at w1) | measured; answers from NS Lemma 2.3 re-proved and checked per instance; seed 0 for headline, seeds 1–2 for robustness | audit script | [w1-scale](../docs/w1-scale.md) §3, [w23-speed2](../docs/w23-speed2.md) §3 |
| Canonical forms on `ns` to n = 5632 in 1.43 s (w23); nauty modes > 600 s from n = 2464 (w9, not rerun for that long since) | measured, seed 0 | as above | [w23-speed2](../docs/w23-speed2.md) §3, [w9-canontool](../docs/w9-canontool.md) §3.1 |
| Traces wins every family except multipedes (about 7× CFI, 23× Miyazaki, 14–29× Q12, 3–6× 3-regular) | measured | | [w23-speed2](../docs/w23-speed2.md) §3, §6 |
| `gi.canon` polynomial guarantee at d ≤ 5 | **not achieved**: `perm_canon`/`ir_canon` exponential in the worst case | | [w14-solver](../docs/w14-solver.md) §1 |
| Compiled kernel at w16: default hybrid 2.0–2.4×, `ir=0` 1.5×, bounded and canonical 1.00–1.15× (the last superseded by w23) | measured, paired | identical output digests; ASan/UBSan clean | [w16-ckernel](../docs/w16-ckernel.md) |
| Stage loop and cheaper Schreier–Sims (w22): xl hybrid 4.85 → 3.07 s, xl `ir=0` 55.0 → 37.5 s | measured, paired; 112 outputs identical | identical digests; audit mode; mutation checks | [w22-speed](../docs/w22-speed.md) |
| Bounded and canonical paths compiled (w23): canon 1.7–8.4× faster, biso 1.1–2.5×, no slowdown with the kernel on | measured, paired | forms and labellings identical on all paired rows; ASan/UBSan; `bench/run.py` 56/56 | [w23-speed2](../docs/w23-speed2.md) |
| Test suite and benchmark on master after the w22 and w23 merges: 2679 passed (kernel on), 1910 passed (off); `bench/run.py` 56/56 in 3.3 s | measured | | [overnight log](../docs/overnight-log.md) |
| HJ's local certificates never reduced branching in practice (cost about 10–60×) | measured in round 1 | | [Tried and failed](Tried-and-Failed.md) |

## 9. Not achieved (explicitly)

* An FPT or polynomial algorithm for degree-d graph isomorphism.
* An FPT algorithm for TreeCI, or for tanglegram isomorphism (R1).
* A hardness reduction for TreeCI or R1.
* A lower bound for a general coset-splitting model.
* A 2^{o(k²)} algorithm for AGL(k,2) string isomorphism.
* Transfer of the w1 HJ string lower bounds to graphs (Theorem B1 of w18 is a separate graph-level bound).
* An n^{o(log n)} algorithm for general Latin squares, Steiner triple systems or conference graphs.
* An unconditional 2^{o(n²)} algorithm for cubic Boolean equivalence (Theorem D of w35 is conditional).
* A machine-level Theorem R\*. `graphIso_reduction` (w43) gives a reduction with a recursion-node bound, but there is no program, and node count is not machine time ([Lean audit](Lean-Audit.md#stage-1-in-lean-and-a-vacuous-statement-w38-w41-w42)).
* A 2^{o(d²)} algorithm for general quartic Boolean equivalence (w45).
