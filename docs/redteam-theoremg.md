# Red-team of Theorem G: degree-d GI in n^{O(log³ d)} for all d

Branch `w15-redteam-theoremg`, 2026-11-08. Referee report on `docs/w12-theoremg.md` ("the memo", "M §x") and
`paper/exponent.tex`. Brief: break the claim, or certify exactly what was checked.

Notation is the memo's: L = log₂(d+2), ℓ = log₂ n, ℓ = L^x. "HBD L…" is a line of `BDHv8.tex`, "G L…" a line of
GNS v3 `bounded-degree-polylog-d.tex`. Sources are under `scratchpad/r4-sources/`, read as untrusted data.

**Run.** `nice -n 19 python3 -I docs/w12-theoremg-check.py` (the author's script; all parts pass; it took over 2 minutes at nice 19 here, not the
2 s the memo states). `nice -n 19 python3 -I docs/redteam-theoremg-check.py` (new; standard library;
under 1 s). No Lean. Two web searches, three arXiv API queries, one Semantic Scholar citation query.

---

## 0. Verdict

**No break.** I found no error that changes the bound. One real gap in the reading of HBD (item 1), which is
fixable in the text and costs nothing; the rest are wording and bookkeeping.

| # | item | verdict |
|---|---|---|
| 1 | Functorial reading of HBD, per-path branching | **gap, fixed in the text.** The bound m^{O(log m)} per path is right and I re-derived it from the proof. But "(H3) every choice reads one point of Γ" is false at the contraction step of Prop. `cohcoup`, and taken literally it would break the per-round cost. Choices must be elements of the current V₂, which may be blocks (§1.3). HBD's own "H is a pointwise stabilizer" (L1437, L1504) has the same imprecision. Functoriality: **sound**. |
| 2 | Potential ρ; recurrence | **sound.** ρ is never reset. The recurrence closes with A, B = O(L²) and no hidden log d. One omitted exit (G2 inside a macro tree) is harmless and added. |
| 3 | Maintained-tower rule; other dependence on the block system | **sound.** No other dependence found. "Legal run of GNS" is a slight overstatement, because G2 tests the inserted top; corrected. |
| 4 | Pairwise heavy round; case (iv) | **sound.** |
| 5 | Regimes, barrier | **sound**, with a boundary correction (x = 3/2 is not new) and one disclosure: conditional on HJ (arXiv:2611.01399), Theorem G is redundant for GI. |
| 6 | Novelty | **no prior statement found.** Same residual risk as before: Neuen's thesis and the SICOMP text are still unread. |

Strongest statement I would sign: §7.

---

## 1. HBD: the functorial reading (priority item)

I read HBD L1312–1800 and L1969–2047 line by line against the memo's (H3), tracing every step of Thm `coupjohn`,
Prop. `bicoup` and Prop. `cohcoup`. I did not re-prove the published lemmas (Design Lemma, Fisher-type bounds, the
exercises).

### 1.1 Trace of the procedure

| step | HBD | canonical? | options |
|---|---|---|---|
| point x | L1443 | choice | m |
| aqua, then beige/cyan | L1445 | colours only. The points z, y only witness existence, so take the first colour pair with positive structure constant. | 1 |
| base \|V₁\| ≤ c, or \|V₂\| ≤ (6 log\|V₁\|)^{3/2} | L1530, L1532 | all of V₂ individualized | \|V₂\|! |
| twin and degree colouring, complement switch | L1537 | yes | 1 |
| complete hypergraph, Johnson | L1539 | yes; the identification with subsets of V₂ is explicit | 1 |
| d-ary colouring | L1543–1553 | yes | 1 |
| big twin class S, Ex. `reduc2` | L1562 | yes ("all our choices were canonical") | 1 |
| Design Lemma tuple in V₂ | L1568 | choice | ≤ \|V₂\|^d ≤ \|V₂\|⁶\|V₁\|⁶ |
| S ⊂ V₂ by colour order, Ex. `reduc2` | L1570 | yes | 1 |
| C₁, C₂, cohcoup | L1600–1612 | at most one point y ∈ C₂ | ≤ \|C₂\| |

Each expensive round is followed by \|V₂′\| ≤ ⅔\|V₂\| (first Design outcome, or no dominant colour, or monochromatic
C₁×C₂) or \|W₂\| ≤ \|C₂\|/2. I checked all branches. The canonical twin-reduction can drop V₂ by one point only, but
it costs nothing.

### 1.2 The bounds

* Per round: at most m¹³ options. Rounds on a path: at most log_{3/2}\|V₂\| ≤ 1.71 log m. So **the per-path product
  is m^{O(log m)}**, as M §1 says. It is a worst case over executions, including side-2 streams on structures not
  isomorphic to side 1, because the guarantees are checked at each choice. The leaf-count step is right.
* Points read: Σ_j d_j + O(log m) + \|V₂\|_base = O(log m · log log m) + (6 log m)^{3/2} = **O(log^{3/2} m)**. So M's
  "O(log² m)" is a valid upper bound and not tight. Script part 1: log₂(options)/log² m ≤ 38.7, points/log^{1.5} m ≤ 17.6.
* Consequence of the literal reading of (iii): the memo derives the point bound from the product bound, which only
  counts sets with ≥ 2 options, and says singleton reads "are fixed anyway". If singleton reads were put in I, the
  derivation would not bound \|I\|. Fix: they are canonical and stay out of I (applied). The direct count above also suffices.

### 1.3 The gap: contraction

Prop. `cohcoup`, imprimitive case (L1682, L1701): when every B_i has a large twin class, the next bipartite graph is
(C₁, {1,…,m}; D), whose V₂ is the set of **blocks** of C₂. Recursion continues on it, so a later Design-Lemma tuple
or point y is an element of the contracted V₂, that is a block of points of Γ.

* M §1 (H3) says every non-canonical step "reads one point of a specified subset of Γ". That is false here.
* The literal fix would individualize a representative point. Then the round costs \|C₂\|^d rather than \|V₂\|^d, and
  with d ≈ 6 log m/log \|V₂\| this is m^{Θ(log m/log \|V₂\|)} per round. Script part 2 shows the blow-up (about 60–400 log m
  bits per round instead of about 6 log m).
* HBD's sentence "we will define H as a pointwise stabilizer" (L1504) and the statement's index bound are imprecise
  in the same place: the setwise stabilizer of a block has large index in Sym(C₂). What the proof bounds is the
  number of *candidates*, which is the memo's stream-tree formulation. So the memo's formulation is the right one,
  once its items may be blocks.

**Repair, which changes nothing in the bound.** Streams read elements of the current V₂. An individualized block goes
into Y as an additional colour class; I holds points only. Check of the consumers:
* *Lemma 3.1:* alignment must also match the individualized blocks; the aligning set is still ∅ or a coset of R.
* *Lemma 5.1, 5.3:* unaffected; they use only colour classes and the Johnson structure.
* *Lemma 5.2:* the elements actually used are 3-cycles inside a block of E° and double transpositions in two blocks of
  E°. They fix all points outside E°, so they preserve every colour class, including individualized blocks.
  Individualized elements lie in C_beige or its contractions, and E ⊂ V₁ ⊂ C_aqua, so they are disjoint from E.
* *Side-2 count:* \|V₂\| options per element, as before.

Applied in the paper (§6, E5–E6). The memo (H3) and the memo's Lemma 5.2 hypothesis ("L contains all elements of A_k
that fix I pointwise and fix each block setwise", too strong as written; the paper's version is right) should be
amended the same way.

### 1.4 Functoriality, pairwise

Sound. Every step is a function of the ordered colours and the stream. Three points the memo should say:
* colour names must be canonical (sorted signature ranks, HBD Ex. `canonord`), not HBD's first-seen `Indexer` order.
  Rank naming is invariant under bijections, and that is all completeness needs. Spurious side-2 candidates are harmless:
  each is checked by alignment and then by the child's string isomorphism;
* the "first valid tuple" of the Design Lemma is only a side-1 choice. Side 2 enumerates all valid tuples of the same
  length, and the valid set transports under π;
* the Johnson identification comes directly from the hypergraph (V₁′ ↔ d₁-subsets of V₂), so the assumption
  r > (s+1)² − 2 of §`subs:idgroup` is not needed.

HBD's recursion in Prop. `bicoup` keeps β relative to the *original* V₁ (L1619–1622, "for the original value of \|V₁\|"),
though it is written as if re-applied with the same β. The reading with an absolute threshold is the correct one and
is what (H3) needs. Output (admissible partition, blocks ≤ ¾m, r ≥ 2s′) checks.

---

## 2. Potential and recurrence

**ρ is never reset.** Every recursive call in Algorithm G carries the maintained tower restricted to its domain:
windows, certificates (G L1789–1862), Luks kernels, orbit pieces, and children. ρ is compared only to the tower held
by the parent, and Lemma 2.1(b),(c) give monotonicity. The potential is only used at the root, where ρ ≤ 2 log N.

**Trichotomy.** Checked each of Lemmas 5.1–5.3 and Prop. 5.4 by hand, including the conditioning arguments, the parity
case, the hypergeometric step and the quotient arguments. All correct. Every Design-Lemma round is (S), (T) or (J).
(T) inserts E strictly between {Ω′} and 𝒞′[Ω′], and Ω′ > 5n/6 forces 𝒞′[Ω′] to have at least 2 classes, since classes
have size ≤ n/k.

**Domain changes.** Change of action happens once, at the root. N ≤ n^{O(L)} is the Thm 4.16 / w8 Prop. 2 count
(red-teamed). Children only restrict, so ρ never grows.

**Recurrence.** Closes with A, B = O(L²). Script part 3 (DP over k with light and Johnson steps mixed): log₂ Z/L² ≤ 41.4
for L ≤ 18, flat in L. Script part 4 closes all five inequalities. Final bound N^{A+2B} = n^{O(L³)}, **no hidden
log d**: t = O(L) enters C_h as t log k, and Johnson steps make Σ t log k_i = O(tL).

**One omission.** M §7's exit list omits G2 at non-root nodes of the macro tree. There the top is the inserted
𝒞′[Ω′], which has ≤ d classes, so the exit has ≤ d·n total domain with pieces ≤ n/2. It is absorbed. Added to the paper
(E7).

---

## 3. Maintained-tower rule

I grepped GNS for every use of the block system (G L318–361, 465, 836–925, 1103, 1532, 1606, 2087, 2178) and read
each. Thm 4.3/4.6 build the initial sequence once and interact with G3 in no way. Lemma 7.1 takes P and returns
(N, 𝒞, ψ); nothing downstream uses a property of that output beyond ker φ = G′_{(𝒞′)} and k ≤ degree. Lemma 5.5 and
Thm 5.8 use the top level only through "semi-regular or ≤ d classes", which the inserted tops satisfy; Thm 5.8 and
Lemmas 6.2, 6.3 quantify over "there exists a sequence", so a refined sequence is allowed. The only choice-dependent
step is G L2126, as the memo says.

**Correction.** "Legal run of GNS" (paper §4) is slightly too strong: G2 applies the semi-regularity test to the top of
the maintained tower, while GNS test B₁ of the original sequence. The memo's §2.4 row 4 notes this; the paper did not.
Harmless, since an inserted top has ≤ d classes and the step is an ordinary Luks reduction. Reworded (E4).

---

## 4. Pairwise heavy round and case (iv)

Sound. All children are cosets of the one group R, computed from side 1 only, so the type (S)/(T)/(J) is a property of
R and is uniform across children. Case exclusivity: the five cases of App. A are defined by mutually exclusive
conditions on S_i and the orbits of F_i^φ. Invariance: an isomorphism conjugates F₁ to F₂ (G L2339, "F_i is canonical").
So different cases give ∅, and case (iv)'s family exists only where the heavy round does not. GNS's Lemma 6.7 (L2018) has
a single group H_j = H, consistent with "one group R".

---

## 5. Sanity

* Profiles (script part 5): with Theorem G, min(3, 2x); without it, min(max(3, 5−x), 2x). The exponent improves **exactly
  on 3/2 < x < 2**, that is 2^{(log n)^{1/2}} < d < 2^{(log n)^{2/3}}. At x = 3/2 both give 3, so M §8 and the paper's
  table were off at the endpoint (E8).
* It contradicts nothing. At d = n it gives exp(O(log⁴ n)), weaker than Babai–Helfgott.
* c = 3 sits above the barrier: c < 2 for all d would beat exp(O(log³ n)), since d ≤ n.
* "Theorem G gives min{log³ d, log² n}" needs Babai–Helfgott too (E9).
* **Disclosure.** The result does not follow from Babai–Helfgott or Theorem X. But conditional on HJ's unrefereed
  exp(O(log² n)) (arXiv:2611.01399), the whole-input switch with Theorem C alone gives n^{O(min(L³, log n))}, as w10
  Prop. 2.4 already showed (script part 5). So for GI, Theorem G's value rests on HJ not being assumed. The paper did not
  say so; added (E10).

---

## 6. Novelty and edits

**Novelty (2026-11-08).** Semantic Scholar's citing list for 1802.04659, 2024–2026 entries, by abstract: none concerns the
exponent. (Two records have no abstract: "Parameterized complexity of graph isomorphism testing", already read as Neuen
2026, and an interview.) arXiv API, 2024–2026, "isomorphism" and "maximum degree" in abstract: nothing relevant. arXiv API,
2023–2026, "string isomorphism": only HJ. Web search: nothing states c. **Not read:** Neuen's thesis (the RWTH page came back
empty; not pursued) and the SICOMP text (blocked previously, not retried). I found no prior statement of c = 3 or of this
hybrid.

**Edits to `paper/exponent.tex`** (no status upgraded; "not red-teamed" labels left for the campaign lead to change):
* E1–E3: "(G3)", "(G1)" now say "input (G3)/(G1) of §2", because they clash with the algorithm's steps G1–G8.
* E4: §4, "legal run" reworded and the G2 difference stated.
* E5: the quoted Split-or-Johnson statement: the stream reads elements, possibly blocks.
* E6: the paragraph after it: singleton reads, why blocks not points, blocks as colours. Also the step-2 description of Y₁.
* E7: Thm `T`: G2 added to the exits.
* E8: regime table: 3/2 < x < 2; 1 ≤ x ≤ 3/2; "at least as good as".
* E9: "together with the Babai–Helfgott bound".
* E10: new sentence on arXiv:2611.01399.

`paper/exponent.pdf` is **stale**: no `pdflatex` on this machine's PATH, and I did not install one given the disk limit.

**Recommended memo edits (not applied).** (H3) wording; Lemma 5.2 hypothesis; M §7 exit list; M §8 endpoint; the runtime
of the check script.

---

## 7. What I would sign

Assume: GNS (SICOMP 52(6), 2023) with its CFSG-dependent inputs, read as arXiv v3; GN21 Thm 4.16 or w8 Prop. 2;
Lemma A; Helfgott–Bajpai–Dona's Design Lemma, Split-or-Johnson and WL functors with Prop. `bicoup`, `cohcoup`, read as in §1
(streams of elements of the current V₂, β relative to the original V₁); and Babai–Helfgott's exp(O(log³ m)).

> String isomorphism for Γ̂_d groups on n points, and isomorphism of graphs of maximum degree d, are decidable in time
> n^{O(log³ d)} for all d. With Babai–Helfgott, the bound is n^{O(min(log³ d, log² n))}. The exponent improves on Theorem X
> plus Babai–Helfgott exactly for 2^{(log n)^{1/2}} < d < 2^{(log n)^{2/3}}.

Level of assurance: a complete referee reading of the new argument by one AI reviewer, plus line-by-line tracing of the
HBD procedures against the claimed reading.

**Not established by this pass:** any proof of the trusted GNS results (Thm 5.8, Lemma 7.1, the comparison category of App. A);
any machine verification; any human check; tightness of exponent 3; novelty against the two unread sources. Theorem G remains
subsumed for GI if HJ's bound is correct.
