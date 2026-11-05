# Referee report on `paper/canon.tex` ("Canonical labelings for graphs of maximum degree d in time n^polylog(d)")

Branch `w10-referee`, 2026-11-05. This is a program-committee-style review of the whole assembled draft,
read front to back. Line numbers ("l.") are those of `paper/canon.tex` **after** the edits listed in
§6; page numbers ("p.") are those of the recompiled `paper/canon.pdf` (47 pages).

**Sources used** (read only): `scratchpad/r4-sources/` — GNS arXiv:1802.04659v3 source; Neu20
arXiv:2002.06997v2 source; Wie20 arXiv:1911.11257 source; SW19 arXiv:1806.07466 source; GNSW
arXiv:1803.06858v1 source; Pago arXiv:2302.05426 source; GNW arXiv:2004.07671 source; Babai STOC'19
(text); Babai–Luks STOC'83 (text); Wiebking's dissertation (PDF, re-extracted page by page with
`pdftotext` into `scratchpad/w10ref-build/thesis/`, so printed page = PDF page − 8); Neuen's 2026
survey (text). Theorem numbers were recomputed from the LaTeX sources with a counter script
(`scratchpad/w10ref-scripts/thmnum.py`) and checked against `\label`s. New download: arXiv API queries
into the new directory `r4-sources/w10ref-arxivapi/` (nothing relevant found). Neuen's dissertation is
behind a bot challenge and the SICOMP version of GNS is paywalled; neither was obtained, and no attempt
was made to get around either.

---

## 1. Summary verdict

**Theorem A, Corollary B and Corollary D: the argument appears correct as written, modulo the stated
assumptions.** I checked every lemma of §§2–9 against its uses. That covers:
- the canonizer and coset conventions, with right actions and left cosets;
- the quantifiers in Lemmas S and T, and the right-subgroup conjugations everywhere;
- the windowed and layered tags, and Lemma T, Lemma 5.4 and Lemma 5.6;
- the case analysis against GNS App. A;
- the recursion lemma, the potential lemma and the macro-step accounting;
- the canonical Luks reduction, claim by claim.

I found no mathematical error in these. The GNS Lemma 7.2 example (Remark 7.3) is correct; I re-derived
the block systems and the numbers. Lemma 7.5 then proves the inequality under the Step 6 choice.

**Theorem H: the new ingredients are proved, but the assembly is only outlined.** E1–E3, T^set, LC
and AGG are proved; W, B and SIMP only nearly. The abstract and Table 1 nevertheless call its
correctness "proved" (Major M1). **Theorem TW** is correctly labelled a sketch, and fixes TW-1–TW-3 are
sound at sketch level.

**Status labelling is mostly honest.** But the single most important external dependency of Theorem A
is not visible at the headline level. That dependency is Babai's STOC'19 canonical form, which its own
text says it only sketches. The determinism requirements (D1)–(D4) are also hidden there (Major M2).

**Citations are accurate.** I verified about 120 theorem, page and line pointers. Seven small citation
problems were fixed (§5).

**Counts.** Major issues: **2** (both about status and completeness; no mathematical error). Minor
issues: 26 (17 fixed in the text, 9 proposed). Citation problems: 7, all fixed. In total 28 edits
were applied to `canon.tex` and `refs.bib` (§7).

---

## 2. Major issues

### M1. Theorem H: "correctness proved" overstates what the body contains

**Where.**
- Abstract l. 99 ("correctness proved, running time only sketched").
- Table 1, row Theorem H (l. 232, p. 5).
- Proof of Theorem H (correctness), l. 1749–1760, p. 32.
- §15.1, rows "Lemmas W, B, SIMP, LC, AGG" and "Theorem H" (l. 2197–2198).

**Problem.**
- For Theorem A the paper writes out an algorithm (CanAD, §6.2) with an instance format, a step list and a
  correctness proposition (Prop. 6.1) with a termination measure. For Theorem H there is no counterpart.
  The "proof" of correctness is one paragraph listing which lemma replaces which step of Neuen's Lemma 4.36
  and Thm. 4.37.
- Lemma B has no proof. Lemma SIMP has inline justifications only. Lemma W's proof is four lines.
- The proof also says "induction on the virtual size, and then on the k-potential". The k-potential is
  not a well-founded measure for same-domain calls. Those calls terminate because they are on proper
  subgroups, as in Prop. 6.1.
- The new ingredients (E1–E3, T^set, LC, AGG) are proved, and I found no error in them. The red-team's
  verdict ("sound") is about canonicity of the single-object loop, not about a written assembly.
- The three Neu20 points and the unseen structure-graph lemma [Neu19, 6.1.17] add further dependencies.

**Proposed fix.** Choose one of the following.
- (a) Add a §10.9 "Algorithm CanHyp" in the format of §6.2:
  - instances (Ω, Γ, 𝔓, B⃗, 𝔛);
  - the intransitive step: chain rule plus Lemma W;
  - the semi-regular top: Lemma B, descent, chain rule;
  - the primitive step: Neu20 Lemma 4.35 (P1), then descent to Γ′;
  - Agg via CanLC/AGG, then Option 1 (Lemma S with BC, then F4) or Option 2 (Lemma 5.8);
  - Step 6 (𝒞′ on top).

  Add a Proposition "CanHyp returns a Γ-canonizer", proved by induction on (virtual size, |Γ|)
  lexicographically. Add short proofs of Lemmas B and SIMP.
- (b) Relabel. Proposed abstract text: "We also give a canonical version of Neuen's hypergraph
  isomorphism test for such groups (Theorem H; the new ingredients are proved, while the assembly into
  Neuen's algorithm and the running time are sketched)". In Table 1 and §15.1: "correctness: proof outline;
  Lemmas E1–E3, T^set, LC, AGG proved modulo Neu20; running time: proof sketch".

*Not applied* (status change; for the authors to decide). I only added "running time only a proof
sketch" to the Theorem H heading in §1.4, which matches the existing Table 1 status.

### M2. The main external dependencies of Theorem A are not visible at the headline level

**Where.**
- Abstract l. 106–108 ("conditional on the published results listed in Section 13").
- Table 1, row Theorem A (l. 229).
- Status box after the proof of Theorem A (l. 1052).
- The dependency itself: Prop. 5.7 (l. 879), (D4) (l. 421), §13 row 13, Question 15.3 (l. 2250), Known
  limitations.

**Problem.**
- (a) **BC is a sketch by its own account.** Theorem A calls Babai's canonical form [Bab19, Thm. 2.2] at
  every Option-1 node. Babai's paper is a "preliminary report", and in §2 it says: "In this note we sketch
  the proof of the following main result. Theorem 2.2." So "proof modulo §13" for Theorem A is a proof
  modulo a result whose only published proof is a sketch. The paper is candid about this, but only in
  §15. A reader of the abstract, Table 1 or the Theorem A status box would not learn it.
- (b) **(D1)–(D4) are not published results.** They are assumptions that published algorithms can be run
  deterministically on canonical generators: the GNS toolkit, Babai's Thm. 3.2.1, the constructions inside
  GNS Thms. 4.3 and 4.6 (Question 15.2), and BC. The abstract calls everything "published results".

**Proposed text.**
- Abstract, replacing the sentence at l. 106–108: "Every result is conditional on the published results
  listed in Section 13, among them Babai's canonical form for strings (STOC 2019), whose published account
  is a preliminary report that sketches the proof, and on the requirement (Section 2.4) that the
  group-theoretic subroutines we use be run deterministically on canonical generating sets."
- Theorem A status box: "Proof modulo the results listed in Section 13, in particular Babai's canonical
  form [Bab19, Thm. 2.2] (a preliminary report), the internal constructions of [GNS, Thms. 4.3, 4.6], and
  requirements (D1)–(D4); see Questions 15.2, 15.3."

**A simplification worth adding (my observation; please check).**
- In Prop. 5.7, BC is only ever called on φ(H) ∈ {A_k, S_k}, with k ≤ d, acting on structures on [k].
- An A_k-canonizer follows from an S_k-canonizer by a parity argument:
  - keep F_{S_k}(x) if Aut_{S_k}(x) contains an odd permutation;
  - otherwise use F_{S_k}(x) or F_{S_k}(x)^{(1 2)}, according to the (well-defined) parity of λ ∈ Λ_{S_k}(x).
- So Theorem A needs exactly "Babai's quasipolynomial canonical form for graphs [Bab19, Cor. 2.3],
  applied to relational structures of arity O(log d) on at most d points". That is a sharper and more
  familiar dependency.
- (D4)'s precaution makes BC's output a function of the group in any case. The second half of Question
  15.3 ("is its output known to depend on the group only?") is therefore unnecessary.

*Not applied* (status wording); proposed for the authors.

---

## 3. Minor issues (mathematics and clarity)

"Applied" means fixed in `canon.tex` (§6). None of the applied edits changes a claim. The two that touch
statements, m1 and m3, only make quantifiers explicit.

| # | location | issue | fix |
|---|---|---|---|
| m1 | Lemma S, l. 648–656, p. 12 | **Quantifiers.** S_can := S^{Λ′(S)} and R are written as if fixed, but both depend on (the orbit of) x. The domain of the R-canonizer must be R-invariant, which it is but is not said. The right subgroup should also be noted to equal Aut_H(F). | **Applied:** S_can(x) := F′(S(x)) and R(x), constant on H-orbits; "for each value of S_can an R-canonizer on the R-invariant set …"; right subgroup Aut_R(F) = Aut_H(F). |
| m2 | Def. 3.1, l. 584 | "first A_i-orbit in Ω∖U_i" mixes frames: U_i is on the input side, A_i in the canonical frame. | **Applied:** "among the positions where F_i carries the tag (0,*) (i.e. Ω∖U_i^τ)". |
| m3 | Lemma R, l. 630–632 | "Given a G\*-canonizer for ι(G) on {x\*}" is garbled. | **Applied:** "a G\*-canonizer (F_{G\*}, Λ_{G\*}), G\* := ι(G), on the G\*-invariant set {x\*}". |
| m4 | §5 intro, l. 715 | "k > 10t (so k ≥ 100)" is wrong: t = 9 is possible, so only k ≥ 91 follows. Also t is defined with ⌈log d⌉ here but without the ceiling in §2.6 (as in GNS). | **Applied:** "so k ≥ 91", plus a note on the rounding. Nothing used k ≥ 100; Cor. 6.5 needs k ≥ 24 and Lemma 7.5 needs k ≥ 13. |
| m5 | Lemma 5.6 proof, stage i (l. 868–871); Lemma 5.1 proof (l. 732) | "Alternatively, if \|V′\| ≤ n/2, make one call on V′" reads as a free choice. Two procedures give different canonical forms, so F_{J_0} would not be a single function. Also, the chain rule on a windowed string should first restrict to the window. | **Applied:** the rule must be a fixed function of \|V′\| (a J_0-invariant), and the restriction is done via Lemma F1. Same restriction added in Lemma 5.1. |
| m6 | l. 989, 1543, 1751, 2131, 2182 | "Lemma K" is cited five times, but Lemma 5.8 never carries that name. | **Applied:** Lemma 5.8 is now titled "canonical find-symmetry"; all mentions use `\ref{lem:K}`. |
| m7 | after Step 6, l. 976–981 | "So Step 6 selects one of the runs that the GNS algorithm permits" is not literally true. At the child, CanAD tests semi-regularity on 𝒞′[Ω′], whereas GNS tests it on 𝔅_1[Ω′]. (Remark 7.3's claim, which is about runs of GNS itself, is correct.) | **Applied:** reworded. Whenever Step 4 applies at the child, the block system is one that GNS also permits. CanAD is a variant analysed directly in §7. |
| m8 | Table 2, l. 1033 ff., p. 19 | The text claims the table lists *every* place where GNS compare two inputs. It omitted the pairwise steps of GNS Lemma 6.7 (pairing 𝔄_{1,1} with each 𝔄_{2,j}, and the Babai16 isomorphism test; src 2017–2019) and Lemma 6.9 (g mapping Δ_1 to Δ_2, transposition τ; src 2049–2051). | **Applied:** rows 19 and 20 added, and the float fixed so that the table stays on p. 19. |
| m9 | Lemma W, l. 1565 | "one call of Theorem A on at most 2m points" is inaccurate: the linking graph has ≤ 2m vertices, so its string has ≤ (2m)² points. | **Applied.** |
| m10 | Claim 2 (B2), l. 1333 | The statement refers to itself ("Claim 2 applies to …"). | **Applied:** "in particular the first statement applies to …". |
| m11 | §1.5 "Why BC's repair does not transplant", l. 284–288 | "When d < 20 log n, test sets of size 2 log n do not even fit into the ideal domain" is false as stated: they fit whenever k ≥ 2 log n. What fails is GNS's constraint t < k/10. | **Applied:** both statements made precise. |
| m12 | Caveats, l. 315–321 | "They found no error in the main argument", yet the second review found the F1 "right subgroup" slip. Also, the list of computer checks omits the numerical check of Lemma 7.5. | **Applied.** |
| m13 | Abstract l. 100 | "using Theorem A alone (Theorem TW)" overstates: TW also uses Wiebking's canonizers [Wie20, Thm. 9, Cor. 27], [GNSW, Lemma 23] and [Wie21, Thm. 6.11]. The intended contrast is "not Theorem H". | **Applied:** "which needs Theorem A but not Theorem H". |
| m14 | §1.4 headings, l. 211, 218 | Theorem H and Theorem TW are stated as theorems without their status. A reader who skims §1.4 sees "Theorem TW" as a claim. | **Applied** (flagged here; no status changed): "running time only a proof sketch" and "proof sketch" added to the headings, matching Table 1. |
| m15 | Def. 10.1 | "Right group" is used from Lemma E1 on but never defined. | **Applied.** |
| m16 | §2.6, l. 474 | Aff(B^h, φ^h) uses φ^h without defining it. | **Applied:** φ^h(c) := φ(hch⁻¹), with a remark covering φ\|_{B^h} and ψ_{T^{φ(h)}}, as used in (L4). |
| m17 | l. 658, 1027, 1254, 1749 | "the coset rule" is used but never named where it is defined. | **Applied:** named in §2.2, and Theorem A points to it. |
| m18 | throughout | **Notation collisions:** F (fullness group vs canonical forms); S (support vs structure map vs separator); K (certificate, subgroup in F3, exponent in Lemma 7.1, K(x) in case (iii), K_0); R (coset representatives in F3, child group, orbitals, rows); C (coset map, 𝒞′-classes, orbit C); t (test-set size vs tree node in §11). | *Proposed:* rename the fullness group (e.g. Φ(x)), the support (supp_x) and the F3 transversal. |
| m19 | §7 | The paper's own Lemma 7.1, Remark 7.2 and Lemma 7.5 sit next to constant references to GNS Lemmas 7.1 and 7.2. | *Proposed:* number the named lemmas, or call the recursion lemma "Lemma REC". |
| m20 | Lemma 5.8 proof, l. 915 | "τ any element inducing an odd permutation on Δ_0 (omit … if there is none)": it is cleaner to say "omit if K(z)L = H_{Δ_0}". Harmless as written, since a τ ∈ K(z)L just repeats a branch value. | *Proposed.* |
| m21 | Lemma 7.1, l. 1060 | τ is a function of n, but the application is over instances. | *Proposed:* "apply to τ(n) := max over instances of size n", or state the lemma for recursion trees. |
| m22 | Proof of Theorem H, l. 1759 | The termination measure "virtual size, then k-potential" (see M1). | *Proposed:* (virtual size, \|Γ\|) lexicographically. |
| m23 | Theorem H and TW statements, Corollary B | The same letter c is used for possibly different absolute constants. | *Proposed:* c′, c″. |
| m24 | Lemma CH, l. 1871 ff. | The lemma mixes Δρ (group on the V side, SW style) with τ_SΘ_S (group on the label side, GNSW style). Both are correct and consistent with the sources. | *Proposed:* one sentence noting the two conventions. |
| m25 | Question 15.3, second half | Moot given (D4); see M2. | *Proposed:* delete. |
| m26 | numbering | Named lemmas do not use the theorem counter. So Remark 10.2 sits at the very end of §10, after Lemma AGG, and the unused `\label`s on named lemmas would resolve to section numbers. | *Proposed:* number them ("Lemma 3.1 (F1)") or remove the labels. |

Items checked and found correct, with no fix needed:
- Lemma 2.2(1)–(3).
- The coset rule's independence of the representative.
- Remark 2.3 against SW's (CL1)/(CL2): CL(x^φ, φ⁻¹Δρ) = φ⁻¹CL(x, Δρ), and CL = Aut_Δ(x)π.
- F1–F4, including the right-group generators in F3.
- Lemma T (a)–(c), and the S_4 counterexample of Remark 4.1.
- Proposition 5.2: all five defect bounds, and r ≤ k⁶ = k⁴·k·k as in GNS App. A.
- Lemma 5.4(3).
- Lemma 5.6: B = G_i(T, x)^{στ_i} and A_i = ker(ψ_{T_0}\|_B); this is the conjugation issue the red-teams raised, and it is now right everywhere.
- Lemma 5.8, including the case φ(H) = A_k.
- Prop. 6.1 termination.
- Lemma 7.1 (both bullets of (A)).
- Lemma 7.5: steps 1–4, and 0.415k − 1 ≥ k/3 for k ≥ 13.
- The height h, the macro-step counts, and the exponent bookkeeping (c = max(3, c_1) + 2 with c_1 = 2c_BC − 1).
- Claims 1–5 of §8.
- Corollary D.
- E1–E3, T^set (a)–(d), and LC (LC1)–(LC3), including independence of π for Δ(Z).
- AGG's defect bound: 1 − max(1/4, 1/10 + 1/k) ≥ 3/4 for k ≥ 7.
- TW-1 (χ must be preserved for GNSW Lemma 23).
- TW-2: a clique lies in α(v) for its first-peeled vertex v.
- TW-3: the degeneracy check holds for k ≥ tw(G) by [Wie20, Lemma 29(3), Thm. 30(3)]; sep(G^k) ≤ k by Lemma 29(2).

---

## 4. Status honesty and the Lemma 7.2 question

- **Theorem A, Corollaries B and D.** The labels are right, except for the prominence of BC and of
  (D1)–(D4) (M2).
- **Theorem H.** Overstated at the level of "correctness proved" (M1). The running-time status is right.
- **Theorem TW, H2–H4.** Labelled sketch or conditional, correctly. The headings now say so too (m14).
  "H1: proof modulo Theorem H" is fine, because Table 1 says its running time is only as good as the
  sketch.
- **GNS Lemma 7.2 (Remark 7.3, Question 7.4, §1.6).** **Fairly phrased.**
  - I re-checked the example:
    - P = S_m ≀ S_2 is primitive.
    - Every valid output of Lemma 7.1 has N ≤ S_m × S_m, k = m, and 𝒞 the rows or the columns.
    - Full test sets are exactly those inside U or inside U^c, giving case (ii).
    - The large orbit has size 0.7n.
    - H′ = Sym(U^c) × S_m has exactly two maximal block systems.
    - The column choice gives k′ = m.
  - The numbers check: at m = 200, 200 − 200/(3 log 200) ≈ 191.3, t = 19 and 10t = 190 < 200.
  - The proposed choice is a legal run of GNS's algorithm, and Lemma 7.5 proves the inequality under it.
  - The text says explicitly that it has not shown the GNS running time fails under other choices.
  - Two small suggestions:
    - (i) **Applied:** the abstract now adds "the GNS theorem itself is not affected", which the body
      already says.
    - (ii) *Proposed:* "could not justify" in the abstract slightly understates what is shown, since the
      asserted inequality is false for one permitted run. Consider "a step … which does not hold for every
      run the text permits (Remark 7.3)".
  - Remark 10.2 (Neu20) is also fair. I confirmed the typo at Neu20 l. 2687: "ker ψ = N_(𝔅)" should be
    N_(𝒞). The test order at l. 2222/2224 and the pre-balancing kernel at l. 2442 are also as stated.

---

## 5. Citations

### Verified correct (numbers recomputed from sources)

| source | items verified |
|---|---|
| **GNS** (arXiv:1802.04659v3) | Thm 2.1; Def 2.3; Lemma 2.4; Lemmas 2.6, 2.8 (the semi-regular remark 7.2 is right: Thm 7.3's proof appeals to Lemma 2.8, whose case 1 needs Σn_i ≤ 2^k n); Thm 3.13; Def 4.1; Obs 4.2; Thm 4.3; Lemmas 4.4 (BLS87), 4.5; Thm 4.6 (\|Ω\*\| ≤ n^{(c_1 log d + c_2 + 1) log d}); Def 5.6; Thms 5.8, 5.9 (= Babai Thm 6(b)); Def 6.1; Algs 1–4; Lemmas 6.2, 6.3; Thm 6.4 / Cor 6.5; Lemmas 6.6, 6.7, 6.9; Lemma 7.1 (= Bab15 Thm 3.2.1); Lemma 7.2 (t = max{9, 3 + log d}); Thm 7.3; Thms 8.1, 8.3; Cor 8.4; Thm A.2; Lemma A.3 (= Bab15 Cor 2.4.13). About 30 `src` line pointers spot-checked (1103, 1120, 1207, 1802, 1810, 1902, 1908, 1917, 1931–1934, 2087, 2092, 2097, 2101, 2120–2126, 2270, 2324, 2357, 2368, 2383, 459–470, …): all match. |
| **Neu20** (arXiv:2002.06997v2) | Lemmas 2.6, 3.9 (= Neu19 Lemma 6.1.17), 4.3; Thm 4.6 (= GNS 5.8); Lemma 4.7; Thms 4.8, 4.9; Obs 4.12, 4.13; Lemmas 4.14, 4.15, 4.16; Thm 4.17; Thm 4.24; Cor 4.28; Lemma 4.29; Thm 4.31; Lemmas 4.32–4.36; Thm 4.37; Def 5.1; Thm 5.3; Cor 5.4; Thm 6.1 (Ringel, K_{3,4g+3}); Cor 6.3 (any three vertices). `src` lines 270–275, 1648, 1669, 1930, 1974, 1987, 2048, 2053, 2201–2258, 2222, 2224, 2442, 2589, 2683, 2687, 2710, 2716: all match. |
| **Wie20** (arXiv:1911.11257) | Thm 9 (canHyper); Cor 27 (canObj); Lemma 29 (parts 2, 3); Thm 30 (part 3); Thm 31 (GNS form, \|V\|^{polylog cw Δ}); Lemmas 32, 33, 34; Thm 35. The intro quote ("no adequate canonization version") and the Outlook quote: verbatim. |
| **Wie21** (dissertation) | Printed pp. 7, 9–10, 179, 180, 181, 242. Questions 9.6 and 9.7: wording verbatim. Lemma 5.34 (p. 101; quote p. 102); T^can := {1, …, m} (p. 103; note that m = max{8, 3 + ⌊log \|V\|⌋}, i.e. log \|V\|, consistent with the novelty claim "test-set size Θ(log d)"). Thm 5.2; Thm 5.4(1); §6.1.3 (p. 144); Thm 6.11 (p. 145); Thm 6.13 (p. 152); Thm 6.29 (Hadwiger number); Cor 6.30. |
| **SW19** (arXiv:1806.07466) | Outlook quote verbatim. Lemma 15 = `lem:canGen` (cites AGMMM Lemma 6.2 and GNSW Lemma 21). (CL1)/(CL2) as used in Remark 2.3. |
| **GNSW** (arXiv:1803.06858v1) | Lemma 21 (canonical generating sets); Lemma 23 (second case: "Δ preserves 𝒮 and χ"); canonization in 2^{O(k² log k)} poly(n), so "also GNSW" in the §11 table is right. |
| **Babai STOC'19** | Thms 2.1, 2.2; Def 5.1(i); §§5, 8, 16 ("right descent"); Thm 12.1; Cor 12.3; Claim 12.4; Remark 12.5; Cor 13.3 and Prop 14.2 (both need t ≥ max{9, 2 log₂ n}). |
| **Babai–Luks 1983** | §2.1: CF(X, σG) := CF(X^σ, G), and properties (I), (II) = the paper's coset rule and right subgroup. §4.2: the fourth trick, "due to Babai". §4.3: Thm 4.2. Lemma 4.3 (proved by Luks). Lemma 4.4 (outvalence ≤ d − 1). |
| **GNW** | Cites [Neu19, Thm 6.6.7], as the paper says. |
| **Neuen 2026 survey** | "the same is possible for many of the algorithms discussed in this survey": the quote is accurate. |

### Citation problems found (all fixed in the text)

1. **Wie20 Lemma 34 / "GNSW Lemma 9"** (l. 1862). Wiebking cites `cosetHyper` as "Lemma 9" of the
   *ICALP* version of GNSW. In arXiv v1, the version the bibliography says is used, item 9 is Theorem 9
   (label decomposition). The text now says so.
2. **Wie21 p. 103** for both quotes in §10.3 (l. 1507). "Stabilize[s] the test set T^can setwise" is on
   p. 102. Changed to pp. 102–103.
3. **"the paragraph after [Bab19, Remark 12.5]"** (l. 273). The quote is the second paragraph *of*
   Remark 12.5. Changed to "in [Bab19, Remark 12.5]".
4. **§13 row 4.** "[GNS, Lemmas 4.4, 4.5] ([BLS87])" credits BLS87 with both lemmas, but only Lemma 4.4
   is from BLS87.
5. **Wie21 page range** for Thm 6.11: "pp. 144–152" (row 24) vs "pp. 145–152" (§11 table). Harmonised to
   pp. 145–152; Thm 6.11 is on p. 145.
6. **Neu26** bibliography entry: DOI 10.1016/j.cosrev.2026.100918 added (article 100918).
7. **History** (§1.2): BL83 also remark, after Thm 4.2, that the canonical bound improves to
   n^{O(d/log d)}. Added.

**Pago (arXiv:2302.05426)** is not cited, and nothing in the current text needs it. His Lemmas
`G_fixingTheRestPointwise` and `G_groupInduction` (credited to Wiebking) concern the composition-factor
induction used in the separate exponent analysis (`docs/w8-gnsexp.md`, red-team `redteam-w8-gnsexp.md`).
**If that analysis is merged** (Remark "The exponent", l. 1260, says it is in progress), Pago must be cited
there, with the credit to Wiebking.

**Could not be verified:**
- Neu19, Lemma 6.1.17 and Thm 6.6.7: thesis behind a bot challenge.
- GNS SICOMP 52(6): paywalled.
- FSS83: the bibliography already says "not consulted".
- AGMMM18 Lemma 6.2: checked only via SW19's citation.

**Prior art.** The arXiv API queries of 2026-11-05 (in `r4-sources/w10ref-arxivapi/`) found no
n^{polylog d} canonization for maximum degree d, no canonical Neu20, and no n^{polylog k} treewidth
canonization. This agrees with the paper's §14. Besides the BL83 remark and the conditional Pago
citation, I see no missing prior art. Before submission, the authors should still consult the SICOMP
version of GNS (it may treat the Lemma 7.2 point) and Neuen's dissertation (for 6.1.17).

---

## 6. Presentation: what would most confuse an expert, and suggested edits

1. **No proof map.** The decisive new step (Lemma T → Def. 5.3 → Lemmas 5.4 and 5.6) is buried in §5.3.
   *Suggest* a half-page roadmap at the start of §3: a table listing each CanAD step, the lemma it uses,
   and the GNS result it replaces. Also state Lemma T directly for its one application (layered
   certificate strings), with the abstract version as a remark.
2. **Named vs numbered lemmas** (m6, m19, m26). Number everything ("Lemma 3.1 (F1)"). This also fixes
   "Remark 10.2" appearing at the end of §10.
3. **Notation collisions** (m18). The three most confusing are F (fullness group vs canonical form), S
   (support vs structure map) and K (certificate vs subgroup vs exponent).
4. **Too many `src` line pointers in the main text.** Move them to footnotes, or to one appendix table
   keyed by claim; keep result numbers in the text.
5. **Two status tables** (Table 1 and §15.1) that must be kept in sync. Keep one and cross-reference it.
6. **Theorem H section.** It is dense, and its hypotheses read "in the setting of [Neu20, …]". Restate
   the key hypotheses of Lemmas W, SIMP and LC inline, and add the algorithm (M1).
7. **BC dependency.** State it as in M2, including the reduction to graph canonization on ≤ d points.
8. **Abstract.** At about 260 words in two paragraphs it is long. The provenance sentences ("The use of a
   canonical test set … is due to Wiebking") could move to §1.5.

---

## 7. Edits applied to `paper/canon.tex` and `paper/refs.bib`

Typo, clarity and citation fixes only. No proof was rewritten, and no claim's status was changed. The
only status-adjacent edits are the §1.4 headings (m14) and the abstract clause on GNS, both flagged above.

1. Abstract: "using Theorem A alone" → "which needs Theorem A but not Theorem H" (m13).
2. Abstract: added "the GNS theorem itself is not affected" (§4).
3. §1.2: BL83's n^{O(d/log d)} remark (citation 7).
4. Theorem A statement: points to the coset rule; new label `sec:canonizers` (m17).
5. Theorem H heading: "running time only a proof sketch" (m14).
6. Theorem TW heading: "proof sketch" (m14).
7. §1.5 Credit: "in [Bab19, Remark 12.5]" (citation 3).
8. §1.5 "Why BC's repair does not transplant": made precise (m11).
9. Caveats: wording about the reviews, and the list of computer checks (m12).
10. §2.2: "coset rule" named (m17).
11. §2.6: φ^h defined; equivariance of Aff for φ\|_{B^h} and ψ_T (m16).
12. Def. 3.1: canonical-frame complement (m2).
13. Lemma R statement (m3).
14. Lemma S statement: quantifiers (m1).
15. §5 intro: k ≥ 91, and the rounding of t (m4).
16. Lemma 5.1 proof: chain rule on W\* via F1 (m5).
17. Lemma 5.6 proof: fixed rule, restriction via F1 (m5).
18. Lemma 5.8 titled "canonical find-symmetry"; five "Lemma K" references → `\ref{lem:K}` (m6).
19. Remark after Step 6: reworded (m7).
20. Table 2: rows 19–20 added; float `[!htbp]` (m8).
21. Claim 2: self-reference removed (m10).
22. Def. 10.1: "right group" defined (m15).
23. Lemma W cost: (2m)² points (m9).
24. §10.3: Wie21 pp. 102–103 (citation 2).
25. §11.3: the GNSW "Lemma 9" numbering explained (citation 1).
26. §13 row 4: BLS87 attribution (citation 4).
27. §13 row 24: pp. 145–152 (citation 5).
28. `refs.bib`, Neu26: article number and DOI (citation 6).

The paper was recompiled with `pdflatex` / `bibtex` / `pdflatex` ×2 (TeX Live scheme-medium): 47 pages,
no undefined references, and four pre-existing overfull boxes of at most 6 pt.
