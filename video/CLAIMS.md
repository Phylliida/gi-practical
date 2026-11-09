# Claims ledger

Every mathematical claim and number in the video, and where it comes from.

* **L…** = line of the paper's LaTeX, `graph_isomorphism.tex` (arXiv:2611.01399, 4953 lines).
* **H-L…** = line of Helfgott–Bajpai–Dona, arXiv:1710.04574, `BDHv8.tex`.
* **Lean** paths are under `~/math/GraphIsomorphismLog2/Workspace` (read only, never run).
* **docs/…** are this repository's memos.
* **GEN** = computed by `video/tools/gen_data.py` (output in `video/js/data.js`); re-run to reproduce.
* **SIMPL** = my own simplification; each is marked on screen with a "simplified" chip at the moment it
  appears (or, for pictures, a chip naming what is cartoon about them).

## Status claims (chapters 1, 24)

| Claim | Source |
|---|---|
| Paper proves deterministic exp(O((log(n+2))²)) GI, returning an isomorphism and Aut generators | L160–167 (Thm 1.1); L139–142 |
| Same bound for string isomorphism on N positions | L179–186 (Thm 1.2) |
| Prior explicit bound exp(O(log³ n)) (Helfgott's analysis of corrected Babai). Chart date reads 2015–17: Babai announced quasi-polynomial in 2015, c = 3 is Helfgott's ("smaller than the original one") | L124–131; H-L1961, H-L1987–2046 |
| exp(O(√(n log n))) (Babai–Kantor–Luks 1983) | L224–225; H-L ("Luks … exp(O(√(n log n)))") |
| Preprint, Nov 2026, not refereed | arXiv id in L71 title; paper has no venue. Task statement. |
| Lean: whole algorithm as one program, correct and time-bounded, accepted by comparator | `README.md` ("The Lean proof covers the whole algorithm", "comparator accepts the solution"); `Statement/Main.lean`. |
| Exactly 10 cited axioms; 6 structural, 4 algorithmic; all rely on CFSG | `AXIOMS.md` |
| Constant in exponent is non-explicit | L1743–1791 (fixed but unspecified); C from Thm A.9 unspecified L2583–2586 |
| κ ≥ 64, q₀ ≥ 4κ+2 = 258 | L1749, L2582, L2603 |
| a ≥ ln(258!)/ln²2 ≈ 2453 | from L1769–1771 (`q₀! ≤ exp(a (log 2)²)`); GEN |
| A ≥ 3(a + a_*/log 2) ≈ 19,152 | from L1787–1790 (main-constant-enum); GEN (uses a_* = a/γ, γ = 9/10) |
| Root exponent ≈ A·C·log²N ≥ 2.5×10⁶ log²N, with C ≥ 128 | product of the above; C_⋆ = 128 L2582. SIMPL: a lower bound on the constants the proof needs, not the true running time |
| Algorithm not practical as stated | consequence of the above |
| Repo solver is simplified, κ = 3, exact; multipede and random-regular comparison with nauty/Traces | `README.md` (interface `Solver(kappa=3,…)`, canonical-labeling section, bench notes). Separate coda, marked as a separate note. |

## Graphs, refinement, CFI (chapters 1–3)

| Claim | Source |
|---|---|
| Petersen: 10 vertices, 15 edges, cubic; zero 4-cycles; Aut order 120; 3 generators from solver | GEN |
| Pentagonal prism: 10 vertices, 15 edges, cubic; five 4-cycles; Aut order 20; not isomorphic to Petersen (solver) | GEN |
| 10! = 3 628 800 | arithmetic |
| Colour refinement rule, stops when classes stop splitting; runs on the real 8-vertex example: 1,3,6,8 classes | GEN; algorithm standard, L115–118 |
| Colour refinement finishes "on almost every graph" in near-linear time | Standard (Babai–Erdős–Selkow, CR complexity); not in paper; said as background |
| CFI: non-isomorphic pairs needing linear WL dimension, degree 3 (coloured) | L231–233 (CFI92) |
| k-dim WL cost n^{k+O(1)} | standard |
| CFI gadget: edge-end pairs, middle vertices = even subsets | GEN builder, standard CFI construction (`bench/families.py`) |
| K₄ CFI pair has 40 vertices (16 middle, 24 edge-end) | GEN |
| Colour refinement gives one colour on both K₄ CFI graphs; 2-dim WL identical; graphs not isomorphic | GEN (uses `gi.refine.wl2`, `gi.graph_iso`) |
| Twisting two edges at a common vertex is isomorphic to untwisted (twist can slide); parity survives | GEN checks `{0,1}` twist ≅ untwisted; parity invariance standard CFI |
| Babai's framing "symmetry vs regularity" | WL50 tutorial slides, Babai 2018 |

## Strings, groups (chapters 4–6)

| Claim | Source |
|---|---|
| Graph on n vertices as colouring of n² ordered pairs; G = Sym(n) acting diagonally; n² positions | L174–177, L581–600 (Alg. graph wrapper) |
| String isomorphism definition Iso_G(x,y) | L169–173; H-L100–115 |
| Rubik's cube analogy | Babai WL50 slides |
| Answer is a coset of Aut_G(x); return one isomorphism and generators | L153–158, L605–621, H-L100–114 |
| Hexagon: 12 symmetries, stabilizer of 0 has orbits {0},{3},{1,5},{2,4}; block systems antipodal pairs and two triangles; quotient on pairs = Sym(3) (order 6), kernel order 2 | GEN |
| Petersen under Aut has 3 orbits on ordered pairs of sizes 10, 30, 60 | GEN |
| Petersen primitive: every pair generates all 10 points as a block | GEN (`gi.group.minimal_block`) |
| Hierarchy of block systems with ratios d₁…d_t, product s | L334–339, L629–637 |
| Luks 1982: orbit chain rule, quotient enumeration, kernel orbit recursion | L606–621, H-L263ff; Babai slides |
| Bounded degree in polynomial time (Luks) | L214–217 |
| T(s) ≤ |P|·d·T(s/d) recurrence | standard reading of Luks' move, SIMPL (statement of the recursion; constants dropped) |
| Real hexagon string example: x = RRBRBB, y = BRRBRB, 6 block permutations, one survives, a rotation by one | GEN, plus JS branch test |
| Cameron–Maróti: primitive of degree ≥ 25 has order < n^{1+⌊log₂n⌋} or is a Cameron/Johnson product | `AXIOMS.md` (marotiPrimitive), L3072–3079 |
| "Luks barrier": either efficient Luks reduction or a large giant epimorphism | Babai WL50 slides; H-L intro |
| Petersen's vertices = 2-subsets of 5 labels; edge iff disjoint; label permutations act | GEN (Johnson graph J(5,2)) |
| Labels = "ideal domain", Babai's "Plato" | Babai WL50 slides |

## Babai and the log³ bill (chapters 7–8)

| Claim | Source |
|---|---|
| Confirm / break dichotomy; confirm means Aut_G(x) maps onto Alt(Γ), or a giant on a subset of at least 0.9·\|Γ\| labels, then an efficient Luks reduction | Babai WL50 slides p. 58 ("Goal (i), (ii)", "\|Γ′\| ≥ 0.9\|Γ\|", "efficient Luks reduction"); H-L125–155 |
| Real window run: Alt(7) on 21 pairs, κ = 3, real colouring; T={1,2,4} Full, T={1,2,3} Nonfull; group sizes 36 → 9 or 12 | GEN (SIMPL: κ = 3, chip on screen) |
| Kernel orbits inside an affected orbit have at most 1/k of its points (narration corrected) | L746–748, L2683–2690 |
| Unaffected Stabilizer Theorem threshold k > max{8, 2 + log₂ n} | Babai slides; L1094-ish `AXIOMS.md` transitiveAffected; H-L1104, H-L1160 |
| Alt(k) × Alt(k) acting on itself: no affected points, stuck | standard; also moonshot §2.3 tight example; SIMPL (cartoon grid) |
| Threshold is tight | Babai WL50 slides ("∃ infinitely many examples … with no affected points") |
| Certificate aggregation → k-ary structure → Design Lemma → Split-or-Johnson | L813–847, H-L ("Design Lemma", "Split-or-Johnson") (named, not derived; chip on screen) |
| Helfgott recurrence F(n,r) ≤ n^{O(k)} + O(k n^{2k+2}F(n/k,r)) + m^{O(log n)}(1+F(n₁,r−1)+ΣF(n_i,r)) | H-L2034–2038 (eq. urg1) |
| k ≈ 2 log n; r ≤ 2 log₂ n; each recursive step lowers r or halves n, so depth at most r + log₂ n ≤ 3 log₂ n; exp(O(log³ n)) | H-L1992, H-L2010, H-L2034–2046 (F(n₁,r−1) + ΣF(n_i,r), n_i ≤ n/2) |
| Three contributors to exp(log²n) per round: tests n^{2k}, Design tuple m^k, Split-or-Johnson m^{O(log m)} | H-L2020–2030; H-L1438–1442 (SoJ index m^{O(log m)}) |
| Three logs as rounds × labels named × bits per label | my framing of the above recurrence (SIMPL for exposition; chip on screen in ch. 8 and ch. 20) |

## HJ: tests, budget, caps (chapters 9–11)

| Claim | Source |
|---|---|
| Test sets of size κ = 64 (example constant; needs κ above threshold) | L1749, L1820–1823, L2582 |
| Local-test interface: polynomially many calls of two types | L719–735 |
| New endpoint procedure, Alg. L774–795; visible-orbit rule; simplicity argument | L2629–2651, L745–751 |
| Recursive calls (s,σ) → (s/κ,σ), (s,σ) → (s,σ−κ) | L728–730 |
| Definition of σ via marked chains | L1964–1970, L1951–1958 |
| σ nonincreasing; marked decrease for G/N ≅ Alt(k) with k ≥ κ | L1982–2012 (Lem. budget-inheritance) |
| σ(G,Ω) ≤ C log n − B | L2474–2492 (Thm hereditary-budget) |
| Block additivity σ(G) ≤ σ(blocks) + σ(block) | L2064–2076 |
| σ ≤ 6 v_ℓ(\|G\|), ℓ∈{3,5} | L2023–2026 |
| Primitive cases: valuation bound for affine, almost-simple non-alternating, diagonal, and non-Johnson alternating; Johnson and product get separate arguments (v_ℓ = O(log n) does not hold for Johnson actions, so the on-screen heading names only the valuation cases) | L2357–2470 (Lem. budget-primitive-valuation), L2522–2548 |
| Natural giant Alt(n), Sym(n): no mark while the active action stays a natural giant; a chain must leave the giant first | L2552–2563 |
| Alt(κ)^r two-sided: σ ≥ rκ, log n = r log(κ!/2) | `docs/moonshot-theory.md` §2.3 |
| Hierarchy: ratios d_i, caps c_i, initially c_i = d_i | L334–339, L642–652 |
| Q = Σ(log d_i) log max{c_i,2} ≤ (log s)² | L1431–1432, L519 |
| Refinement and restriction do not increase Q; cap inherited c′ = min{c,d′} | L1436–1439, L650–652 |
| Alternating width definition; closed under subgroups and quotients | L653–656, L3090–3099 |

## Rectangle, rows, columns, cosets, phases (chapters 12–15)

| Claim | Source |
|---|---|
| Aggregation yields a homogeneous coherent configuration on C, \|C\| ≥ δq | L831–840 |
| First-rectangle interface: W, R, \|W\| > η\|C\|, \|R\| ≤ \|C\|−\|W\|, twin classes ≤ w/2, width bound | L869–884, L896–918, L4493–4535 |
| Width of left action ≤ max{w/2, r}; extended ≤ max{w/2, r, q−w} ≤ max{1/2, 1−ηδ}q | L905–913; L4552–4560 |
| Real Hoffman–Singleton: SRG(50,7,0,1); W = 42 non-neighbours, R = 7 neighbours; each row one entry, each column six; twin classes of size 6; width 21 = max{21,7,8} | GEN |
| "Babai recurses here, HJ stop" | L318–320, L852–855 (HJ); Babai's Split-or-Johnson continuation H-L1414 |
| q ≤ λ = N^α: fresh on q² ≤ N^{2α} positions | L424–426, L1065–1067 |
| q > λ: kernel orbits indexed by labels, ordered, or unordered pairs | L428–433, L1238–1242, L4302–4318 |
| \|Δ\|/s ≤ 2\|W\|\|R\|/(q(q−1)) ≤ θ < 1 | L438–441, L928–935 |
| Row normal form, row terminal, exp(O(log²N)) additive | L448–459, L990–995, L1292–1299 |
| Diagonal rectangle: \|W\|\|R\|/(mq) ≤ q/(4m) ≤ 1/4; diagonal subgroup not enumerated | L472–474, L1005–1015, L4671–4699 |
| Row action enlarged at most once, N/(mq) < N^{1−2α} < λ | L478–485, L1304–1339, L1326 |
| Counter h ∈ {0,1,2}: paid events | L1115–1116, L1442–1444 |
| Complete cosets, auxiliary work additive not multiplicative; CombineExact; overcoset then re-check | L493–513, L606–621, L1026–1031, L1085–1090 |
| Phases, α = 2/5, γ = 9/10; 1/3 < α < 1/2; 2α < γ < 1; fresh calls at N^γ, N^{2α}, N^{1−α} | L1095–1107, L1097–1100, L1618–1626, L1820–1825 |

## The running time (chapters 16–19)

| Claim | Source |
|---|---|
| T(s) ≤ s^a T(s/2) is s^{O(log s)} | elementary; on-screen derivation |
| Φ = A(x²+ρx+σx+Q)+Bh, x = log(s+2) | L1447, L1427; Lean `Paper/RunningTime.lean` L38–56 |
| W = (s+2)^D e^Φ | L1452 |
| T ≤ K_N W(S) | L1646–1647 (Lem. 7.1) |
| Branch count vs drop: M e^{−ΔΦ} ≤ 1/(8J), with J a fixed bound on child classes, J = 8 for example | L1668–1684, L1774–1775 |
| Disjoint-domain prefactors add: Σ(s_i+2)^D ≤ (s+2)^D | L1583–1589, L1670–1671 |
| Node toll paid by prefactor; W ≥ 2N^a | L1685–1691 |
| x − log(θs+2) ≥ c_θ = ½log(1/θ) for s ≥ 6; x² − log²(θs+2) ≥ c_θ x | L1482–1487 |
| N^a ≤ e^{a_* x}, a_* = a/γ, using s > N^γ | L1469–1470 |
| Domain drop by d: x² − log²(s/d+2) ≥ ⅓ x log d | L1497–1500 |
| ρ = Σ(2⌊log₂d_i⌋−1) ≤ 2log₂s; refinement drops ρ ≥ r−1 | L1429–1430, L1435–1436, L3060–3061 |
| Floor identity ⌊log₂a⌋+⌊log₂b⌋ ≤ ⌊log₂ab⌋ (strict decrease) | L3354–3355; elementary derivation on screen |
| log(2^r r!) ≤ r log 2r ≤ 4(r−1)x | L1510 |
| σx pays via κx | L1490–1492 |
| Q falls ≥ (log d) log(1/β) ≥ c_β log q; only q^a branches here | L1524–1526, L1473–1475 |
| Bh row events | L1441–1444, L1458–1459, L1549 |
| Six-row charging table verbatim | L1540–1551 |
| Constant conditions for A | L1782–1790, L1794–1812; Lean `Paper/RunningTimeParameters.lean` |
| Root potential O(log²N) | L1708–1710 |
| K_N = E_N(1+F(⌈N^γ⌉)), E_N = exp(c_T log²(N+2)) (not a small factor; ch. 16 narration corrected) | L1630–1636 |
| F(N) ≤ exp(C log²(N+2))(1+F(⌈N^γ⌉)) | L1719–1722; Lean `Paper/RunningTime.lean` L1101 (`main_recurrence_solution`, per docs/moonshot) |
| Geometric series Σ γ̂^{2j} = 1/(1−γ̂²). Slider default 0.91, range 0.67 to 0.99: γ̂ must exceed γ, and 2α < γ < γ̂ with α > 1/3 forces γ̂ > 2/3 | L1724–1732, L1097–1100 |
| N = n²: log²N = 4 log²n, a constant factor 4 in the exponent; exp(O(log²n)) = n^{O(log n)} | arithmetic; L584–585, L1735–1737 |

## Tightness (chapter 20). **Not in the HJ paper**; this project's analysis, marked on screen.

| Claim | Source |
|---|---|
| Three logs compared; two changes removing the middle tile | L356–421 (HJ), L1540–1551; H-L2030 |
| \|AGL(k,2)\| = 2^k Π(2^k−2^i); k=3 gives 1344; ratio to N^{1+log₂N} tends to ~0.2888 | GEN, `docs/moonshot-theory.md` Prop. 2 |
| Enumerated: elementary abelian socle, not Cameron/giant; passes the dispatcher's size test exp(a log²d) | moonshot §2.5 proof; L1766–1772 |
| Forces ≈ N^{log₂ N} coset branches for every pair of strings | moonshot Prop. 2 |
| String-setting scope only; not a graph lower bound | moonshot §2.5 |
| Narration says the socle is elementary abelian, not "no alternating quotient" (GL(4,2) ≅ Alt(8) makes the latter false at k = 4) | a check made while writing; the socle statement is moonshot §2.5 |

## Degree d (chapters 21–23). **Not in the HJ paper.**

All of this is conditional on HJ's analysis (H0), has passed one AI verification and one AI red-team
(`docs/verify-theorem-R.md`, `docs/redteam-theorem-R.md`), has not been checked by a human, and the
Λ-accounting is not machine-checked. This is stated on screen.

| Claim | Source |
|---|---|
| Γ̂_d: every composition factor embeds in S_d; closed under subgroups, quotients | GNS Def. 2.3, Lem. 2.4; docs/verify §1.1; redteam §5 |
| Luks / Babai–Luks reduction, poly time independent of d, to Γ̂_{d−1} or Γ̂_d | GNS Thm 8.1; survey Lem. 4.5; verify §1.2, §6. Layer picture SIMPL (chip) |
| Every giant has q ≤ d (Alt(q) is a quotient, hence a composition factor; minimal degree of Alt(q) is q for q ≥ 5) | verify §4.1, GNS Def. 2.3 |
| d ≤ N^α ⇒ q ≤ λ ⇒ RowStep, row terminal, column floors, in-domain rectangles never run; E_N poly | verify §8 step 1, L1164 |
| Φ_Λ = A(Λx + ρℓ + Λσ + Q_d) + Bh, then ρℓ → Λρ | moonshot §4.1 (ℓ form); verify §4.2 and redteam §1.3 (Λρ form, used for the final Φ_Λ on screen) |
| **Λ = log(8·max(d,6))** | redteam §1.3 and §9(c) (corrected from log(4d̃)) |
| Q_d, caps c_i = min(d_i, d) | verify §4.2 |
| Multiplicities polynomial in d, q^{O(κ)}; affected ≤ 32q^{2κ}, unaffected ≤ 12q^{2κ} | redteam §1.3 |
| Domain row, Λ x drop ≥ Λ c_θ; Λσ drop ≥ κΛ; Q_d cap payment unchanged | redteam §1.3 table |
| Regrouping: window calls of one test on disjoint domains; 2·C(q,κ)·κ!/2·2 endpoint families plus 4q^{2κ} comparison families | verify §3.2; redteam §2; Lean `PhaseTree.Hyp.branch_disjoint`, `Algorithm/Certificates.lean` |
| Lean branch hypothesis asks only child sizes sum ≤ parent | redteam §2 (`Paper/RunningTime.lean` L228–230) |
| GNS Thm 3.13: \|P\| ≤ d′^{c₁ log d + c₂} or socle (A_m^{(t)})^k in product action with m > 4 log₂ C(m,t) | verify §1.1 (G864–928); redteam §4 |
| Corrected dispatcher: recognize, product-refine and GiantStep iff socle (A_m^{(t)})^k in product action, m > 4 log₂ C(m,t), m > q₀; else enumerate | redteam §9(b) (structural test) |
| BCP: top group in Γ̂_d has order ≤ d^{r−1} for d ≥ 6; removes log log N | verify §1.1, §4.4; redteam §6 (Maróti Cor. 1.5, Burness–Shalev restatement) |
| log index ≤ (r−1)Λ, ρ drop r−1 pays | redteam §1.3 product row |
| Result exp(O(log(N+2) log(d+2))); n^{O(log(d+2))} | redteam §10 (statement R*), verify |
| Sanity: d=O(1) Luks; d≈n HJ; d polylog: n^{O(log log n)} | redteam §8, verify §6 |
| Published best n^{polylog d} (GNS) | verify §1.1, survey Thm 4.6, Cor 4.7 |
| Barrier G_{d,m} = P_d ≀ C_m, m = 2^j, P_d = F₂^d ⋊ S_{d+1}, D=d+1 odd, N=2^{dm}, in Γ̂_D, \|G\| ≥ N^{log₂D−0.443}, forced ≥ N^{log₂D−0.45} coset branches on every string pair. Project analysis, not in HJ; AI-checked only, marked on screen | `docs/w1-fpt.md` §3.1 (Prop 3.1, Cor 3.2); `docs/redteam-w1-fpt.md` §1 |
| Exponents log_N\|G\| at m = 256 for D=3,5,9,33 | GEN |
| Scope: string isomorphism, not graphs; family FPT by memoization | w1-fpt §3.1 Cor 3.2(3), §3.2 Prop 3.3 |
| Status card wording | coordinator's scope addition; redteam §9(e) and §10 |
| Dispatcher, as used in ch. 20: at a primitive quotient, enumerate when order ≤ exp(a log²d), else giant route | L1766–1772, L1150–1156 |

## Teaching decisions

See `TEACHING-NOTES.md`. Sources for the running examples: `gen_data.py` header and each block.

## Review log

A w24 fact-check changed the items above and others; `video/REVIEW.md` lists every change with its source line.
