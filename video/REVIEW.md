# Fact-check and copy-edit of "The Third Logarithm"

Reviewed against the paper's LaTeX (`graph_isomorphism.tex`, cited as L…), Helfgott–Bajpai–Dona
(`BDHv8.tex`, H-L…), Babai's WL50 slides, `docs/{verify,redteam}-theorem-R.md`,
`docs/{w1-fpt,redteam-w1-fpt}.md`, `docs/moonshot-theory.md`, and the Lean `README.md`, `AXIOMS.md`
and source files (read only, never run). Every narration line and every on-screen string in
`video/js/` was read. Screenshots are in the scratchpad.

Total running time went from about 64:00 to 65:31; beat timing is still computed from word counts, so
sync is automatic. `tools/ui_test.py` passes, and a sweep of all 53 scenes at three points per beat
found no KaTeX or console errors.

## Errors found and fixed

Severity: **A** wrong statement, **B** misleading or overclaimed, **C** minor or copy.

| # | Sev | Where | What was wrong | Fix | Source |
|---|---|---|---|---|---|
| 1 | A | ch16 weighted induction | "K_N … one fresh call …, times a small factor". E_N = exp(c_T log²(N+2)) is quasi-polynomial, not small. | Says the factor E_N is not small, paid once per phase, opened in ch19. | L1630–1636 |
| 2 | A | ch10 giants, narration and card | "A giant has no marked steps at all": false. Only while the action stays a natural giant; a chain can leave by an ordinary restriction and then mark. | Narration and card restated. | L2552–2563 |
| 3 | A | ch10 primitive card | Heading "primitive, not a giant: v_ℓ(\|G\|)=O(log n)" is false for Johnson and product actions (v₃(\|S_m\|) ~ m/2, degree only polynomial in m). | Heading now "affine, almost simple, diagonal". | L2357–2366, L2522–2548 |
| 4 | A | ch10 property 2 | σ(N) ≤ σ(G)−k stated without k ≥ κ (weight only counts for k ≥ κ). | k ≥ κ added on screen and in narration. | L1951–1958, L1982–1997 |
| 5 | A | ch8, bill for log³ | "r is at most 2 log₂ n rounds". The recursion depth is r plus halvings of n; r alone undercounts it. | "Each round lowers r by one or halves n… at most about 3 log₂ n rounds"; screen shows r + log₂ n ≤ 3 log₂ n. | H-L2034–2046, eq. urg1/urg2 |
| 6 | A | ch6 positions/labels | "Ten positions move" under the 3-cycle (1 2 3). {4,5} is fixed; nine move. | "Nine of the ten positions move and one stays put." | direct |
| 7 | A | ch19 geometric series slider | Default γ̂ = 0.90 equals γ, but the paper needs γ̂ > γ; range went down to 0.5, below the γ̂ > 2/3 the constraints force; square labels used γ while the sum used γ̂. | Default 0.91 (shows 5.82), range 0.67–0.99, labels use γ̂, ellipsis marks truncated squares. | L1724–1732, L1097–1100 |
| 8 | A | ch18 charging table, "predict row five" | Row five's potential drop was already drawn at the prediction beat, under the "?" (bad reveal index). | Drop hidden until the answer beat. | code bug; L1540–1551 |
| 9 | A | ch21 giant bound | "Alt(q) is a section of the group, so it is a composition factor": false in general (Alt(5) is a section of Alt(6)). | "Alt q is a quotient, so one of the composition factors"; the on-screen section implication stays (it is true via closure). | GNS Def. 2.3, verify §4.1 |
| 10 | A | ch7, local certificates | "the affected orbits are at most a 1/k fraction": the kernel orbits inside an affected orbit are. | Narration corrected. | L741–743, L2683–2690 |
| 11 | B | ch7 Confirm | "preserved by most of the giant" and card "nearly all of Alt(Γ) preserves x"; and "in polynomial time". The real statement: Aut_G(x) maps onto Alt(Γ) or a giant on ≥ 0.9\|Γ\|, then an efficient Luks reduction. | Narration and cards restated. | Babai slides p. 58 |
| 12 | B | ch20, AGL(k,2) tightness | Presented without saying it is not in the paper. | Said in narration; "not in the HJ paper" chip. | moonshot §2.5 |
| 13 | B | ch23 barrier | No status at the moment of the claim. | "not in the HJ paper · AI-checked only" chip; conditional chip on the first scene from its start. | w1-fpt §3.1 |
| 14 | B | ch1 chart | "2015" attached to exp(log³): Babai's 2015 exponent was larger; 3 is Helfgott's. "e^{(log n)²}" stated without O and as equal to n^{O(log n)}. | Label 2015–17, O(·) added, "Nov 2026 preprint". | H-L1961, L124–131 |
| 15 | B | ch1 narration | "proves" for a preprint. | "gives a proof of". | status |
| 16 | B | ch21 opening | "The same machinery can do better" before the status. | "If the analysis below is right". | redteam §10 |
| 17 | B | ch24 coda | "on the kinds of instances the paper is really about, this structure is reachable in pure Python": unsupported. | Restated as what the repo supports. | `README.md` |
| 18 | B | ch3 end | "no such symmetry" read as if CFI graphs were asymmetric. | "yet no symmetry carries one onto the other". | L231–233 |
| 19 | B | ch13 | "the classification pins down the action": the kernel-orbit statement is a lemma in the paper, not the CFSG classification itself. | "a lemma in the paper". | L4212–4222, L4303–4330 |
| 20 | B | ch22 enumeration | "pays for it, exactly" (only up to the constant A). | "up to the constant A". | redteam §1.3 |
| 21 | B | ch8, ch20, ch6, ch7 | Simplifications not marked though the ledger says each is: the three-log bill is my framing, T(s) ≤ \|P\|dT(s/d) drops constants, the Alt(k) grid is a cartoon. | Chips or on-screen labels added. | ledger |
| 22 | B | ch20 third log | "solved exactly on existing positions" (only for q > λ). | "on existing positions when there are many labels". | L424–433 |
| 23 | C | ch23 | Wreath product with C_m needs m a power of 2 for the class claim. | Narration and formula say m = 2^j. | w1-fpt §3.1 |
| 24 | C | ch19 | "costs nothing" contradicted the factor 4. | "costs only a constant". | L584–585 |
| 25 | C | ch18, ch16 | "J is at most 8", "the paper J equals 8": J is a chosen upper bound, 8 is an example. | "takes J equal to 8"; screen J=8. | L1774–1775 |
| 26 | C | ch18 last row | "the weight drops by B": the potential does. | Fixed. | L1547 |
| 27 | C | ch17 | "the potential falls by about c_θ x" after an area of 2cx; the paper records ≥ c_θ x. | Reworded. | L1487 |
| 28 | C | ch24 | "Six are structural facts about finite simple groups": several are about primitive and permutation groups. | "structural facts about groups". | `AXIOMS.md` |
| 29 | C | ch14 | "Depth times depth" (screen says cost M₁·M₂). | "Cost times cost." | — |
| 30 | C | ch10, ch22 | Copy: "There are absolute constants"; "Palfy"; ch7 "coloring"; ch7 "fixing the test" logic for unaffected. | Fixed. | — |
| 31 | C | ch17 | r ≤ log s where r ≤ log₂ s is meant; c_β undefined in narration. | Fixed. | L1510, L1527 |

Totals: 10 A (one a timeline-visible bug), 12 B, 9 C (31 entries).

### Visual glitch

Literal `_` and `^` in canvas text: **Γ̂_d** (ch21 heading and one caption, ch22 theorem line), v_ℓ (ch10),
c_θ and c_β (ch18 explanations), N^a (ch22 heading), q^a (ch17), d^(r−1) (ch22), N^(1+log₂ N) (ch20 table
header). Fixed by adding `_{..}`, `^{..}` and `\hat{..}` to `c.text` in `js/engine.js`; the Lean identifiers
`lem_main_phase_bound` and `branch_disjoint` keep their real underscores. Checked in screenshots, dark and light,
at 53:55, 54:59, 58:09 and the other changed frames.

## Teaching issues fixed

* ch6: alternating group and "giant" now defined when first used.
* ch5: Sym(3) glossed.
* ch13: N and "phase" introduced with a forward reference.
* ch20: socle, elementary abelian, dispatcher, size test defined.
* ch21: "column floors" replaced by terms the video has used.
* ch22: Johnson group glossed.
* ch8: "first term / second term" relabelled to match the three-term formula on screen.
* ch18: row five reveal.
* ch19: square labels, slider, ellipsis.

## Could not verify

* Everything under H0: the HJ proof itself, including the σ budget (Thm A.9) and the Design Lemma step. I checked the
  video against the paper's statements, not the paper's proofs.
* Lean development: I read `README.md`, `AXIOMS.md` and identifiers (`lem_main_phase_bound`, `branch_disjoint`) but
  never ran it. "Comparator accepts" is the README's claim.
* Degree-d material: checked against the two AI memos and their cross-references. GNS Thm 3.13, BCP (the original is
  paywalled) and the Babai–Luks reduction were not independently read.
* GEN numbers: rechecked by hand or by derivation where feasible (hexagon, Hoffman–Singleton counts, AGL table, D=9
  barrier exponent, q₀, a, A). The 40-vertex CFI WL results and the 35 window runs were read from `data.js`, not re-run.
* Babai's remarks attributed to talks ("Plato", "Rubik's cube", "the job", the "Pólya move" is my reading): confirmed
  from the WL50 slide text except Pólya, which is a general heuristic with no source in the notes.

## Teaching issues left unfixed

* W means the window (ch9), the dominant class (ch12) and the weight (ch16); r means Helfgott's depth and the product
  exponent; D means a constant and later an odd integer. Each use is locally clear. Renaming would touch many formulas.
* The ↠ symbol is never glossed.
* `STORYBOARD.md` still has stale details (28-vertex CFI, Alt(5) window run, about 64 minutes); it is a production note
  and was left alone.
