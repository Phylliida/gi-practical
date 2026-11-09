# Storyboard: "The Third Logarithm"

## Audience

Smart, comfortable with proofs and big-O. No permutation-group background: we build it (orbit,
block, primitive, alternating group, coset) as needed, on small pictures, before use.

## The through-line question

> The best proven bound for graph isomorphism used to be exp(log³ n). A November 2026 preprint
> proves exp(log² n). **Where did the third logarithm go, and who pays for the two that are left?**

Recurring visual: **the bill**, three tiles `log n · log n · log n`. Each part of the video works on
one tile. Chapter 20 removes the middle tile for good. The promise in chapter 1: "by the end you will
be able to read `Φ = A(x² + ρx + σx + Q) + Bh` and say what every term pays for".

Second recurring device: **the wallet**. Every recursive branch must be paid for from a finite wallet;
the cost of the algorithm is exp(size of the wallet). Terms have fixed colours everywhere: x² blue,
ρx orange, σx aqua, Q yellow, Bh magenta. Positions Ω are blue and labels Γ are yellow, everywhere.

## Running examples, carried through

| Object | Where | Why |
|---|---|---|
| Petersen graph, drawn with vertices named by 2-subsets of {1..5} | ch. 1,2,4,5,7 | same small object is both a hard-looking regular graph and the model giant: labels Γ={1..5}, positions = 2-subsets |
| Pentagonal prism | ch. 1,2 | same degree sequence as Petersen, not isomorphic |
| Hexagon with its 12 symmetries | ch. 5, 6 | blocks, orbits, primitive quotient, a Luks run |
| CFI over K₄ (28 vertices) | ch. 3 | the parity bit; real refinement output |
| Real window run: Alt(5) acting on Petersen, a real 2-colouring, κ=3 for the picture | ch. 7, 9 | an actual Algorithm 2 trace |
| Hoffman–Singleton graph: real 42×7 rectangle | ch. 12 | a homogeneous configuration with a dominant class; twins are real |
| AGL(3,2): 1344 elements; AGL(k,2) table | ch. 20 | tightness |

All are computed in `video/tools/gen_data.py` (using this repo's `gi` package and plain Python) and
stored in `video/js/data.js`. Numbers shown are the computed numbers.

## Chapters

Timing is automatic from the narration (about 64 minutes in total at 1x, at 2.9 words per second). Every chapter has several scenes; every scene is a list of
beats (sentences), and each animation is keyed to a beat. "S" is what is said, "V" what is shown.

**Part I: the problem**

1. **The question.** V: two graphs, 10 dots, 15 lines, every dot degree 3. S: same graph? Viewer gets
   a beat to guess, then the 4-cycles reveal the answer. V: timeline of bounds: n! → exp(√(n log n))
   (BKL 1983) → exp(log³ n) (Babai/Helfgott) → exp(log² n) (HJ, 2026). V: the three-tile bill. S: the
   promise, including what is *not* promised (status: preprint, Lean-checked modulo 10 cited axioms).
2. **Colour refinement.** Worked example: recolour by neighbour multisets on a real asymmetric graph;
   colours split until each vertex is unique. Then Petersen vs prism: one colour forever.
   Wrong-intuition beat: "look closer", k-tuples.
3. **The parity trap.** CFI over K₄ built step by step: gadget = even subsets. Real refinement
   histograms equal. Twist moves but cannot vanish (interactive: drag the twist). Babai's framing:
   symmetry versus regularity. Combinatorics alone cannot finish.

**Part II: the language of symmetry**

4. **Strings and allowed relabelings.** Adjacency grid of Petersen: a vertex swap moves rows and
   columns together. Ω = n² ordered pairs, three colours. Definition of Iso_G(x,y), Pólya's "related
   problem", n² worry raised (and left hanging until ch. 19). Output is a coset: 120 automorphisms
   from 2 generators. Real orbit counts on Petersen pairs: 10, 30, 60.
5. **Orbits, blocks, primitive.** Hexagon: 12 symmetries. Orbits. Block systems: antipodal pairs,
   triangles; a non-example broken by rotation. Quotient on blocks, kernel. Primitive = no blocks;
   Petersen is. Interactive: click two vertices and watch the smallest block containing them.
6. **Luks's recursion and the wall.** Three moves on a real run: split orbits (chain rule), quotient
   and enumerate cosets, recurse on kernel orbits. Recurrence shown growing. V: the same tree with a
   giant Sym(d) quotient, explodes. The Cameron–Maróti dichotomy: primitive means small, or a giant
   in disguise. V: Petersen again, labels vs positions, "the Luks barrier".

**Part III: Babai**

7. **Local certificates.** Dichotomy: confirm or break. Test set T ⊂ Γ, window growing on a real
   string. Full vs nonfull. Why k ≈ log n: the unaffected-stabilizer theorem, and the small-group
   counterexample (Alt(κ) × Alt(κ) on itself). Viewer asked what could go wrong with small tests.
8. **The bill for log³.** Helfgott's recurrence on screen, three places cost exp(log² n) (test
   sets, Design tuple, Split-or-Johnson), rounds r ≤ 2 log₂ n. The tile count: log · log · log.

**Part IV: Hajiaghayi–JafariRaviz**

9. **Constant-size tests.** κ = 64. Replay the window procedure, new endpoint: fix the unchecked
   region; if the test still acts, full certificate; else a visible orbit, restrict, the domain does
   not shrink. "Then what paid?" Hanging question.
10. **The hereditary budget σ.** Definition via chains, why nonincreasing (chain lifting), why
    κ-decrease, why O(log s) (blocks add logs; primitive case valuation; natural giants have no marks;
    CFSG honesty). Tight example Alt(κ)^r on itself.
11. **Hierarchy and caps.** Bars of width log dᵢ and height log cᵢ. Q = area inside the log s
    square. Restriction lowers a height. Inheritance rule: min with new ratio. Alternating width.
12. **The first rectangle.** Real 42×7 Hoffman–Singleton rectangle: individualize, dominant class W,
    R, semiregular, twins of size 6. Cap argument: kernel on R permutes only twins, quotient acts on
    R. max{w/2, r, q−w}. Babai continues recursing here, HJ stop.
13. **Where the rectangle lives.** q ≤ λ fresh small call on ≤ q² positions. q > λ: kernel orbits are
    labels, ordered pairs or unordered pairs. Pair case: pull colours back, Δ ≤ θs. Single label:
    rows, normal form, row terminal or columns, diagonal coupling of rows and columns, ≤ s/4,
    one enlargement only.
14. **Complete cosets.** Sequential orbit chain needs all answers. Auxiliary work adds to, not
    multiplies, the continuation. CombineExact. Overcoset then re-check.
15. **Phases.** Number line in log N: fresh threshold γ, small configs 2α, rows 1−α, λ at α; α=2/5,
    γ=9/10. "Fresh" means the wallet is refilled.

**Part V: the bill**

16. **A wallet called Φ.** Why T(s)≤s^a T(s/2) is already s^{log s}. W = (s+2)^D e^Φ. Induction:
    every child costs e^(−drop) of the parent's weight. The node toll.
17. **Φ term by term.** x² (a full square-drop derivation, the worked example), then ρx (floor
    identity), σx, Q, Bh. Each: what it counts, how it falls, what it pays.
18. **The charging table.** All six rows, multiplicity vs. drop, side by side; fade: predict the last
    rows. Constants: A's inequalities, J=8.
19. **From one phase to n^{O(log n)}.** Root bound; K_N; F(N) ≤ exp(C log²N)(1+F(N^γ)) as a sum of
    shrinking squares; slider for γ; N = n², log²N = 4 log²n pays off the worry from ch. 4.
20. **Where the third log went, and what is tight.** Babai versus HJ, tile by tile. Tightness:
    N^{log₂N} on AGL(k,2) in the string setting.

**Part VI: degree d**

21. **Degree d: a smaller class of groups.** Luks's reduction on a picture (edge-rooted layers,
    each step a permutation of ≤ d−1 children). Γ̂_d. Closure. q ≤ d. With d ≤ N^α, the wide-giant
    branch, RowStep, row terminal disappear (V: rows of the flow chart go grey).
22. **The Λ-accounting.** Φ_Λ. Each charging row, multiplicity now d^{O(1)}, not N^{Ω(1)}. Regrouping:
    disjoint window families, q^{O(κ)} of them. GNS Thm 3.13 and the dispatcher rule. BCP removes
    log log.
23. **n^{O(log(d+2))}, limits, status.** exp(O(log N · log(d+2))). d=O(1) gives Luks; d=n gives HJ.
    Barrier family, N^{log₂ d − O(1)} on this algorithm. Plain status card (full text on screen).
24. **What is and is not proved; the code.** HJ status. Lean, 10 axioms, comparator. Non-explicit
    constant. Not practical. Brief separate note: this repo's Python solver and what it found.

## Simplifications that must be said on screen

Marked with a chip reading **"simplified"** at the moment they are shown:

* κ = 3 on 5 labels in the window run (the real proof needs κ ≥ 64, where Alt(κ) is simple).
* The Design Lemma and aggregation are named, not derived.
* Row normal form: pictured for a clean grid.
* Luks's bounded-degree reduction: drawn as layers, the actual reduction is a recursion over layers.
* "Rounds" as a single count: the actual recursion is the potential argument.

`video/CLAIMS.md` lists every claim and its source.
