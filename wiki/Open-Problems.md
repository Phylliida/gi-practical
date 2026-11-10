# Open problems and next steps

[Home](Home.md) · Related: [Results ledger](Results-Ledger.md), [Tried and failed](Tried-and-Failed.md)

## Next steps, in order

1. **Get a human expert to look at the canonization paper** before any public claim. A draft cover note is at [paper/cover-note.md](../paper/cover-note.md), not sent. Natural readers: Wiebking, Neuen, Schweitzer, Grohe.
2. **Before writing to them, read the unread sources**: the SICOMP 2023 text of GNS, especially Lemma 7.2, and Neuen's dissertation (the unseen Lemma 6.1.17). Accessing them was blocked; see [Disclosures](Disclosures.md#literature-that-was-not-read).
3. **Ask as questions, not error claims,** about GNS Lemma 7.2 and Neuen 2020 Thm 4.17(G).
4. Decide about publishing [exponent.tex](../paper/exponent.tex). Theorem G should be regarded as provisional until a human checks it; Theorem X is the fallback.
5. Machine-check the self-contained theorems, starting with T2 and Theorem H ([Maintaining](Maintaining.md)).
6. Apply the fixes the red-teams list to the memos they reviewed, none of which was edited afterwards: [w27-tree](../docs/w27-tree.md), [w28-sigma](../docs/w28-sigma.md), [w30-sts](../docs/w30-sts.md), [w34-vc](../docs/w34-vc.md), [w35-cubic](../docs/w35-cubic.md); and the remaining items of [redteam-w18-latin](../docs/redteam-w18-latin.md) §5 in [w18-latin](../docs/w18-latin.md) (its q₁ and exponent fixes are done).

## Asymptotic todos: toward a better algorithm

Added 2026-11-09, as of master `2dbaade`. Three directions aimed at the exponent of the running time, not at wall-clock time (for that, see [Engineering](#engineering)). **This section is a plan and contains no result.** It was written by one AI session and has had no red-team pass; every forward-looking statement in it is [SPECULATION]. Numbers are quoted from the linked pages, and computations made only here are marked "arithmetic here". The labels AS1–AS3 are used only in this section.

HJ's per-phase exponent is O(log N·(log w + μ + log log N)), a sketch ([where the two logarithms live](Math-HJ-Algorithm.md#4-where-the-two-logarithms-live)): giant breaking pays log N·log w, and enumeration of small primitive quotients pays log N·μ. AS1 changes only the constant. AS2 and AS3 attack the two terms, one each. Both are long shots, and each contains a problem that is open in its own right ([classical barriers](Math-Barriers.md#classical-barriers-for-nolog-n)).

### AS1. An explicit constant c_GI

**Target.** A variant of HJ and a stated constant c_GI such that the variant decides GI in n^{(c_GI + o(1))·log₂ n}, proved by hand and conditional on HJ being correct. Behind it, a ledger: for each row of HJ's [charging table](Math-HJ-Algorithm.md#3-the-running-time-analysis), the true number of branches, the true potential drop, and the constant the row forces. The main output is the name of the row that binds.

**Known.**

* No explicit constant exists. Lean's C is non-explicit, and its explicit parts force C ≳ 4·10¹⁴ ([Lean audit](Lean-Audit.md#the-constant-c)). The paper's own potential needs a root exponent of at least 2.5×10⁶·log² N ([CLAIMS.md](../video/CLAIMS.md)). Both figures measure what the proofs need, not the running time.
* HJ as written cannot have c_GI below 1/4: on the PG(m−1,2) incidence graphs it reaches a node with n^{(1/4)log₂ n − O(1)} children (w47, Theorem A), and a separate chain makes n^{(1/8)log₂ n − O_κ(1)} calls (w18, Theorem B1). See Barriers on [the enumeration channel](Math-Barriers.md#hjs-enumeration-channel-on-graphs-w47-w48) and on [the σx chain](Math-Barriers.md#hj-is-tight-on-graphs-too-w18). Both bounds are asymptotic, and both bind only HJ as written.

**Ingredients, with their status.**

* *True multiplicities.* The windows of one test are pairwise disjoint (H2), so the window calls of an aggregation round fall into at most 9·q^{2κ} disjoint-domain families, where HJ charge N^a. This is machine-checked on the real scripts (`GI.Algorithm.aggregate_branch_fam`, [Lean audit](Lean-Audit.md#the-degree-d-accounting-in-lean-w36)). With it the degree-d table closes with one absolute A ≈ 2κ/c_θ ≈ 10³ ([derivation](Math-Degree-d.md#derivation)). That table assumes that no wide giant occurs.
* *Lazy Step 4 (LHJ).* [w28-sigma](../docs/w28-sigma.md) §5.1: Step-4 children are made only on escalation. LHJ returns the exact coset within HJ's bound, given HJ (L1, with the boundary fix of the [red-team](../docs/redteam-w27-w28.md) §5). It does not create the B1 chain at the root and chain states of X_m (L2); for the whole tree this is a sketch. On X_m the cost reappears in Q unless automorphisms are pruned (§6, a sketch).
* *Automorphism pruning.* Pruning tests and aggregation branches by certified automorphisms is sound (P1, w28 §4). It needs real automorphisms: on the rigid variant X_{m,R} the chain survives (R1, w28 §8; that pruning removes nothing there is a sketch). At enumeration nodes one child per double coset is enough ([redteam-w49-pruned](../docs/redteam-w49-pruned.md) §4–5), which covers w47's node (Prop D) and leaves polynomially many children on w49's family. There is no whole-tree statement ([w49-pruned](../docs/w49-pruned.md) §6).
* *Sylow transversals.* At a classical enumeration node the count |P| becomes its odd part ([w17-affine](../docs/w17-affine.md) §7, a sketch; the per-node count is right). The composite row is unwritten, and the claim that this halves the λ coefficient of R\*\* is [withdrawn](Corrections.md#λ-coefficient-halved-in-theorem-r).
* *Bidirectional collision.* w17's Theorem B and w18's A1 ([w18-latin](../docs/w18-latin.md) §3.1) halve an exponent by meeting in the middle. Inside HJ this needs canonical forms of sub-instances, hence a canonical HJ, whose row machinery is open ([Canonization](#canonization)).

**First steps.**

1. **The ledger for HJ as written, on general graphs.** The degree-d table covers only phases without wide giants (q ≤ N^α). General graphs start with one: at the root q = n > N^α, and the certificates run there because the kernel orbits carry two labels (w18 §2.4, checked in [redteam-w18-latin](../docs/redteam-w18-latin.md) §2.1). Below the root, RowStep, the row terminal E_N = exp(c_T·log² N), column floors and in-domain rectangles occur on one-label wide giants (w18 §2.5; [moonshot-theory](../docs/moonshot-theory.md) §2.6). These rows have to be traced in the paper and in the Lean scripts and added to the table.
2. **Separate the constants that the paper merges.** One constant a serves the multiplicities N^a, the tolls and the enumeration threshold exp(a·log² d). The requirement q₀! ≤ exp(a·(log 2)²) alone forces a ≥ 2453 at q₀ = 258, and then A ≥ 19,152 through the enumeration row (HJ L1767–1791; CLAIMS.md). The constant C of σ ≤ C·log s is at least 128 and is chosen after an unnamed "primitive valuation constant" A₀ (HJ L2581–2586), so an explicit c_GI needs an explicit A₀.
3. **Fixed factors (arithmetic here).** A per-phase bound exp(K·ln² N) on N = n² positions gives c_GI = 4·ln 2·K/(1 − γ²) ≈ 14.6·K at γ = 9/10: the 4 comes from N = n², the ln 2 from the base of the logarithm, and 1/(1 − γ²) ≈ 5.3 from the phase recurrence. Read off the potential, K is about A·C, since σx may reach C·log² s with C ≥ 128, while x², ρx and Q together stay below 4.9·log² s. With A ≈ 10³, a first ledger at κ = 64 should be expected to give c_GI of order 10⁶ (a guess; the wide-giant rows may force a larger A). So the constant of HJ as written is known only to lie between 1/4 and roughly 10⁶ to 10⁷, and the σx term is the first candidate for the binding one.
4. **The least κ.** A ≈ 2κ/c_θ grows with κ, and letting κ → ∞ does not help, because the Q coefficient grows with κ (w28 §7.2). HJ say only that their hereditary-budget arithmetic "is satisfied by" κ ≥ 64 and C_⋆ = 128 (L2582). The least admissible κ, and the trade-off with θ, β, α and γ, are not traced anywhere in this wiki.
5. **Add LHJ and two-sided pruning as rows**, with whole-tree statements. Then look for the family that defeats both: by w28 §12 it must be rigid, without bounded-WL anchors, and locally symmetric.
6. **Collision last**, and only after a canonical HJ.

**Milestones for c_GI** (arithmetic here, from n^{c·log₂ n} = 2^{c·log₂² n}). They calibrate the scale at which an explicit constant would say something new; by step 3 they are six or more orders of magnitude below what a first ledger gives, and no step above is expected to reach them.

* c_GI < 2 would beat n^{2 log₂ n + O(1)} for conference graphs (Babai 1980; [w32-conference](../docs/w32-conference.md) §1).
* c_GI < 1/4 would beat generator enumeration, m^{log₂ m + O(1)}, for 2-groups of order m, through Miller's graph on O(m²) vertices: n^{c·log₂ n} = m^{4c·log₂ m + O(1)}.
* c_GI < 1/8 would beat m^{(1/2)log₂ m + O(1)}: Rosenbaum's bound for groups (arXiv:1304.3935, Theorem 1.1), and w18's A1 for quasigroups, Latin squares and Steiner triple systems.
* c_GI < 1/16 would beat m^{(1/4)log₂ m + O(1)}, the best known bound for general groups (Le Gall–Rosenbaum, arXiv:1609.08253, §2.2, deterministic), on 2-groups.
* c_GI < 1/36 would beat 2^{k²/4 + O(k)} for string isomorphism under AGL(k,2) (w17, Theorem B), through Prop 3 of moonshot-theory §3.3: n = Θ(N³) and N = 2^k give n^{c·log₂ n} = 2^{9c·k² + O(k)}.

**Stop when** the ledger exists and the binding row is named. This line cannot give n^{o(log n)}: with σx deleted outright, x² and Q still pay log N·log w (w28 §10). If the binding row is a giant-breaking row, the remaining gain is AS2.

### AS2. A dichotomy for giant breaking

**Target [SPECULATION].** A statement of the following shape, and a proof of it on one natural class. After O(1) individualizations, at polynomial cost, either (i) every giant of degree q is reduced to degree at most q^{1−ε}, or (ii) a classical geometry is exposed canonically, a PG- or AG-type section of dimension Ω(log q), and what remains is a string problem under a classical group, which goes to the enumeration channel and so to AS3. Finding the right statement is part of the todo.

**Why.** Two conditional statements of [moonshot-theory](../docs/moonshot-theory.md) §4.3–4.4, neither proven: with polynomial shrinking, the giant channels cost exp(O(log N·log log N)); and with relative (multi-coset) string isomorphism under classical groups in d^{O(log^{1−ε} d)}, the μ channel costs exp(O(log^{2−ε} N)). In the other direction, string isomorphism under AGL(k,2) reduces to GI on Θ(N³) vertices (Prop 3, §3.3 of that memo; proven, checked by its author only). So GI would sit between the plain form of the classical-group problem, which is necessary, and its relative canonical form, which would suffice by these sketches. This is not an equivalence.

**The one proved instance** is Steiner triple systems near the top of the rank range: rank above 0.9031·log₂(n+1) forces a PG(d−1,2) quotient above a maximizer (T1 of w30 as improved by its red-team; sharp at AG(2,3); [Moonshots](Moonshots.md#steiner-triple-systems-and-the-gl-barrier-w30-w33)). Below that rank it is the conjecture of [w30-sts](../docs/w30-sts.md) §9. By T2, which is machine-checked ([Lean audit](Lean-Audit.md#self-contained-results-machine-checked)), the geometric side on that family is at least as hard as linear equivalence of Boolean functions on F₂^d, so on STS the dichotomy alone gives no algorithm.

**Sub-problems.**

* **(2a) The structure theorem.** For STS, extend T1 past (log₂10)/3 to a statement that allows AG(2,3)-type planes (already listed under [Moonshots](#moonshots)). For Latin squares and conference graphs no analogue is known, and the caveats are on record: "hard cases are group-like" is not established ([w18-latin](../docs/w18-latin.md) §3.4); "locally algebraic" is refuted for Steiner loops ([redteam-w30-sts](../docs/redteam-w30-sts.md) §4.1); conference graphs have no F₂-quotient structure, and every tested one has depth 2 or 3 ([Moonshots](Moonshots.md#conference-graphs-w32-w34)), so there horn (i) alone may hold.
* **(2b) Relative versus plain.** The data at an enumeration node is a multi-coset structure, not a string (moonshot-theory §3.4). The canonical forms of the children determine the parent's only for ε = 1, and fail to for diagonal kernels ([w1-fpt](../docs/w1-fpt.md) §4.5). So horn (ii) has to hand over a problem that the enumeration channel can solve relatively and canonically ([w17-affine](../docs/w17-affine.md) §7, item 3).

**First steps.** (1) The cheap probe: on graph encodings of rigid structured colourings (the T2 family, the graphs of Prop 3), find which channel pays, that is, whether any graph forces superpolynomial enumeration after two-sided pruning. [w49-pruned](../docs/w49-pruned.md) §7 tried "T2 with intermediate χ" and did not complete it ("I could not build a rigid example"); the lead it keeps is a smaller transitive group with an Alt(κ) section, such as SL(κ, 2^{d/κ}). (2) Then (2a) on STS.

**Refuted if** some family has giants of polynomial degree that survive Θ(log N) rounds with no geometry exposed. **Caveat:** AS2 together with AS3 at every fixed degree still would not give n^{o(log n)}, because colourings of F₂^k have degree up to k (random ones are easy: w17, Proposition D).

### AS3. A format-sensitive tensor bound, for the Lie channel past cubics

**Target.** Quartic Boolean equivalence, or 4-tensor isomorphism, in 2^{o(d²)}. Cubics are done only conditionally, in 2^{Õ(n^{1.5})} ([Moonshots](Moonshots.md#cubic-boolean-equivalence-w35-w37)). For quartics there is Theorem H, which wins from s = 132, and no general 2^{o(d²)} ([Moonshots](Moonshots.md#quartic-equivalence-and-4-tensors-w45-w46)).

**The opening.** Kernel reductions from 4-tensors to 3-tensors need total length L ≳ n^{4/3}, the published ones give L = O(n³), and the exponent 3/2 of the best 3-tensor bound is exactly the threshold at which even an optimal reduction gains nothing ([w45-quartic](../docs/w45-quartic.md) §1.1). The red-team narrowed this to bounds stated in the total length alone ([redteam-w45-quartic](../docs/redteam-w45-quartic.md) §2): the format (3, n², n²) has at least q^{n⁴} orbits, so counting does not exclude a kernel reduction from 4-tensor isomorphism into it, and every instance of that format is solved in q⁹·poly(n) by enumerating GL₃. No such reduction is known.

**Sub-problems.**

* **(3a)** A kernel reduction from quartics or 4-tensors into a 3-tensor format with one short side a. Enumerating the short side costs q^{a²}·poly, as in the red-team's example, so a = o(n) with the other sides polynomial would give the target by itself (an inference made here, not in the memos). At a = O(1) it would put 4-tensor isomorphism, and with it GI, in polynomial time for fixed q, which nobody should expect; the open range is a between a constant and n.
* **(3b)** Where no side is that short: a 3-tensor bound whose exponent depends on the format, and which beats both short-side enumeration and the length-only q^{Õ(L^{1.5})} on unbalanced formats.
* **(3c)** The canonical regularity lemma for 4-forms (w45 §4.1, speculation), the missing second half of Theorem H's dichotomy. It and the memo's other leads are already listed under [Moonshots](#moonshots).

**First step.** Tabulate formats, not only lengths: what the published route produces (GQ Theorem B gives an algebra of dimension O(n³), whose structure tensor is balanced; GQ IV Theorem 1.10 then changes the action at linear length), and how the IMQSZ and GIQS bounds depend on the format when it is unbalanced.

**Stop when** an argument shows that every kernel reduction from 4-tensors is too balanced for format-sensitivity to help, or when (3a) and (3b) meet. Over F₂ the 3-tensor bound itself rests on the unrefereed arXiv:2610.00874, so anything obtained for Boolean functions inherits that condition.

### Relation to group isomorphism

By Miller's encoding, GI in n^{o(log n)} would give group isomorphism in m^{o(log m)}, where the best general bounds have improved only the constant (moonshot-theory §3.1). Group isomorphism is the special case of AS2 and AS3 with the most machinery: w35's Theorem F ties cubic equivalence to 2-groups of Frattini class 2 ([w35-cubic](../docs/w35-cubic.md) §3.3), and the class-2 algorithms of Sun and IMQSZ are 3-tensor algorithms. The milestones c_GI < 1/4, 1/8 and 1/16 mark where a GI algorithm would start to beat the group-specific bounds; against a first-ledger constant of order 10⁶ they are out of reach, so an attempt on group isomorphism has to be direct. No memo proves anything about group isomorphism, as of `2dbaade`; [groupiso-scoping](../docs/groupiso-scoping.md) holds a literature scan and unverified first ideas.

## Core questions

* **Is GI FPT by maximum degree?** Downey–Fellows; GNS; Grohe–Neuen 2021 Q4; Neuen 2026 survey ("wide open", Q4.8).
* **(R1)** Coloured tanglegram isomorphism, FPT in out-degree b? Necessary for FPT degree-d GI. **R1_c** is the complete-tree version.
* **(R2)** Are all tree groups fpt-definable? If yes, TreeCI ≡ R1. If no, degree-d GI may be strictly easier than TreeCI.
* **Is TreeCI FPT?** **TreeCan versus TreeCI**: would an FPT TreeCI algorithm canonize? Open.
* **(W2 §3.5)** Entangled kernels under product-type nodes: is coordinate-tree CI reducible to TreeCI?
* **Neuen Q4.8**: is there an fpt-reduction from SI by composition width to GI by degree?
* **Height-2 posets with large μ** ([w8-poset](../docs/w8-poset.md) §5.3): the smallest open poset family, whether μ captures hardness. [w27-tree](../docs/w27-tree.md) excludes gadget-style hardness (Cor N.1, narrowed) and does not settle FPT.
* **The gain-graph core** ([w27-tree](../docs/w27-tree.md) §2.5, §7): prove or refute that π₁(Γ) is normally generated by closed walks with O(1) values per coordinate, except where C is enumerable. A proof would very likely decide HT2 for permutation-type blocks; a counterexample is a new candidate hard family at height 2.
* **Posets with one deep tower**, such as C_m ⊔ (A_m < k), and a **C_s ⊔ C_s-sensitive barrier** that would sharpen Prop N (w27 §7).
* **R1 versus R1_c**: reduce general trees to complete ones, or explain why unbalanced trees are easier.
* **Lower bounds**: an adversary argument that every coset-splitting strategy needs N^{Ω(log b)} on iterated PCI_diag or twisted coordinate tanglegrams would be the first lower bound for a group-theoretic model.
* **Hardness**: no source problem believed not FPT encodes into tree groups.

## Exponent and analysis

* **X(d) ≤ 2^{O(log⁴ d)}** for isomorphism of (log d)-ary structures on d points, directly or by a finer B–H analysis. Would settle c = 3 without Theorem G ([w8-gnsexp](../docs/w8-gnsexp.md) §6).
* **c below 3** within GNS's architecture needs a stabilizer theorem tolerating small primitive levels, or constant-size tests, i.e. HJ's route.
* **Arity reduction**: do O(1) individualizations always suffice for a binary black box? Open after the [refutation](Corrections.md#arity-lower-bound-for-the-gns-black-box).
* **HJ's σ-machinery on heart-type non-Cameron giants** ([w1-structure](../docs/w1-structure.md) §4.9).
* **Theorem G (w12)** human check: the functorial reading of Split-or-Johnson; Lemma 3.1 of w12.
* **Machine-check Theorem R\*** at d < N: the Γ̂_d closure, the (M′) dispatcher, clipped caps Q_d, and tolls ([w36-lean](../docs/w36-lean.md) §3; `w38-lean-stage1` is running).
* **Turn w18's sketches into proofs:** the Latin-square-graph and block-graph chains (B2) and Paley graphs (B3). Theorem B1 itself has been AI red-teamed ([report](../docs/redteam-w18-latin.md)).
* **Leads from [w28-sigma](../docs/w28-sigma.md)** (red-teamed by [w31](../docs/redteam-w27-w28.md)): prove or refute the Uniform Prefix Conjecture (§7.3, speculation); case (b) of Theorem U; turn Q1 into a theorem; find a family that defeats LHJ + P1 + bounded WL (§12).
* **Transferring HJ's string lower bounds to graphs:** does a graph family force the N^{log d} of w1 at fixed degree? Open (w18's B1 is a different channel at unbounded degree).
* **Canonically chosen test sets** in HJ's certificate step (a w18 lead). w28's C1 (red-teamed) shows any Aut-invariant rule is all-or-none on X_m, so a thin canonical family does not exist there; see [Barriers](Math-Barriers.md#can-hj-avoid-the-σx-channel-w28).
* **BC simplification** (Remark 5.2 of w4): check against a full version of BC if one exists.

## Canonization

* Write out Theorem H's running time and TW, H2–H4 ([paper §15](../paper/canon.tex)).
* Canonical row machinery of HJ, for canonical forms of all graphs in n^{O(log n)} (no invariant replacement known).
* FPT 2^{k polylog k} treewidth canonization (speculation).

## Moonshots

* Cubic Boolean equivalence: 2^{Õ(n^{1.5})} is now conditional on unrefereed preprints ([w35-cubic](../docs/w35-cubic.md)); an unconditional proof, or a check of arXiv:2610.00874, remains. Colourings of degree ≥ 4 are where hard T2 instances, if any, must live. Also 4-TI below 2^{o(k²)}, a degree-preserving reduction from 4-TI to quartics, low-rank quartics beyond Theorem H ([w45-quartic](../docs/w45-quartic.md)), and an "affine CFI" ([w17-affine](../docs/w17-affine.md) §8).
* STS: extend T1 past (log₂10)/3 to a structure theorem allowing AG(2,3)-type planes ([redteam-w30-sts](../docs/redteam-w30-sts.md) §2.3); the rank dichotomy for rk ≥ ε log n ([w30-sts](../docs/w30-sts.md) §9); the near-top bound written out.
* Conference graphs: Levet's Question 6.5 (an individualization set of size O(1) or o(log n)); an upper bound on d(τ), on Turyn iterates or in general ([w34-vc](../docs/w34-vc.md) §9); grid detection as the structured side of a dichotomy ([w32-conference](../docs/w32-conference.md) §7).
* Ask whether the "ETH is False" preprint survives review; then update [Moonshots](Moonshots.md).
* Latin squares: rank-Ω(log n) quasigroups. The "locally algebraic" lead of [w18-latin](../docs/w18-latin.md) §6 is refuted for Steiner loops ([w30-sts](../docs/w30-sts.md) §5, as worded by the [red-team](../docs/redteam-w30-sts.md) §4.1); the right form for STS is a projective quotient.

## Engineering

* Solvable-layer extension of `ea2`, or a polynomial `perm_canon` replacement (Theorem A or BL83 canonical Luks).
* A principled individualization rule (trial refinement per class) instead of `young_pick`.
* Cut the remaining Python per layer: `RootedCanon.step` (40–60% on CFI and Miyazaki), `_Rooted` construction and the root class ([w23-speed2](../docs/w23-speed2.md) §6). w23 compiled `absorb` and most other hot primitives; the "up to 1.9×–4×" estimate in [w16-ckernel](../docs/w16-ckernel.md) §6 predates it.
* A sparse representation of non-elementary-abelian groups on long graphs, the next algorithmic step ([w23-speed2](../docs/w23-speed2.md) §6).
* Fewer groups, rather than cheaper ones, for Q7 at `ir=0` ([w22-speed](../docs/w22-speed.md) §6).
* Faster Young-subgroup bookkeeping for `ir=0` (Θ(n⁴) per node).
* Measure entanglement on real Luks towers (CFI, multipedes) to see if Theorem E is practical.
* Implement Theorem P or Theorem 1 of w8-poset as dispatcher cases.
* Add tanglegrams as a stress family.

## Paper loose ends

* [canon.tex](../paper/canon.tex): author lines and disclosure are placeholders. Update the "not independently checked" note for §10.9 after any external check; a red-team has since looked at it ([redteam-canhyp](../docs/redteam-canhyp.md)).
* Several red-team reports list recommended edits to memos that were not applied (for example the Theorem G memo, [redteam-theoremg](../docs/redteam-theoremg.md) §6).
