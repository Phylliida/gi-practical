# What we tried that did not work

So nobody repeats it. Each item says where the attempt stopped. Sources are in the linked memos.

[Home](Home.md) · Related: [Barriers](Math-Barriers.md), [Open problems](Open-Problems.md)

## FPT for degree d

| Idea | Where it stopped | Source |
|---|---|---|
| Potential amortization: an FPT potential C log N + g(d) | every charged step with q^{Ω(1)} branching would need polynomial-in-q shrink; σ, cap, algebraically affected, large symmetry and ρ rows do not have it | [w1-fpt](../docs/w1-fpt.md) §4.5 |
| Canonical forms of children composing into a parent | true for ε = 1; false for diagonal kernels | [w1-fpt](../docs/w1-fpt.md) §4.5 |
| Memoizing types | gives O(N²) block pairs; combining is PCI, so nothing gained without a PCI algorithm | same |
| Diagonal kernels via product alphabets | with a giant on top, each child bijection gives a different tuple string: set-of-strings isomorphism on the child, with no fpt reduction to SI | same |
| "Recurse on H" instead of enumerating V ⋊ H | Johnson layers with t = Θ(m) enumerated at m!; for AGL, PSL on points again gives d′^{Θ(log d′)} | [w1-structure](../docs/w1-structure.md) §4.2 |
| Paying the individualization in Φ_Λ | children shrink by √m; drop O(log d log m) against m needed | same §4.3 |
| Routing large-t Johnson levels to HJ giants | budget Θ(log m!), no better than enumerating | same §4.4 |
| Relative Schweitzer–Wiebking on (α) quotients | leaf `canInt` is coset intersection on Ω | same §4.8 |
| Example X as a hard family | collapses under equivariance (r ≥ 3) | [w2-coset](../docs/w2-coset.md) §4.2 |
| Goursat decomposition of the coupling | pieces are quotients of deep tree groups; bounded exactly in Theorem E's regime | same §4.1 |
| Aligned-position DP | child cosets are arbitrary tree groups; only reproduces known regimes | same §4.4 |
| Every method against T² | Theorem E, L, P, ADKT/S-W, Goursat, aligned DP, block DP, HJ/GNS all fail for named reasons | same §4.6 |
| Peel off Sym(b) (tanglegrams) | E contains Alt(b)^h on digit reversal; works only one-sidedly (Prop L) | [w6-tanglegram](../docs/w6-tanglegram.md) §2.5 |
| Meet/join chains of the two trees | digit reversal decouples nothing | same |
| Straddling recursion | multiplies a recursive call by b!, n^{Θ(log b!)} | same §2.3 |
| Abelian twisting in tanglegrams | "abelian Q" is a property of the answer, not the input | same §2.5 |
| WL dimension f(b) on T□T | would give only XP; and dimension is unbounded at b = 2 | [w4-t2](../docs/w4-t2.md) §1, §5 |

## Beating n^{O(log n)} or the exponent

| Idea | Where it stopped | Source |
|---|---|---|
| Replace quotient enumeration by recursion along a base | AGL/PGL: no smaller action to recurse on; Babai's certificates need an alternating quotient | [moonshot-theory](../docs/moonshot-theory.md) §4.2 |
| Polynomial shrinking inside a phase | fails for same-domain continuations; would beat the 1978–80 barriers | same §4.3 |
| Sun-type linear algebra at affine enumeration nodes | data at the node is not bilinear | same §4.4 |
| Charging GNS per level instead of per halving (c = 2) | window exits need not lie inside blocks | [w8-gnsexp](../docs/w8-gnsexp.md) §5 |
| Self-reducing the black box | genuine regress below k^t ≤ N/2 | same |
| Canonical arity reduction of the black box | bound refuted as a lower bound (see [Corrections](Corrections.md#arity-lower-bound-for-the-gns-black-box)); still open whether O(1) individualizations suffice | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2 |
| Affine equivalence: hyperplane/flag recursion, degree parameters, moment forms, Sun-style individualization beyond bilinear, IR on the affine structure | stopped at named points; only constants improved | [w17-affine](../docs/w17-affine.md) §4–5 |
| Transferring ETH-refutation techniques to GI, TI, AGL, TreeCI | witness and occurrence counts break the construction | [w21-eth](../docs/w21-eth.md) §B |
| Making HJ's row machinery canonical | carrier and normal form are arbitrary choices; no invariant replacement found | [w3-canon](../docs/w3-canon.md) §2.4 |

## Latin squares and Steiner systems (w18)

| Idea | Where it stopped | Source |
|---|---|---|
| Generator enumeration with a coset representation of Aut(T) | extension test is a string-isomorphism condition under Aut(T), as hard as the original | [w18-latin](../docs/w18-latin.md) §3.4 |
| Top-down chain enumeration | gives exactly Miller's bound; only the bidirectional split (Theorem A1) halves it | same |
| HJ-style constant-size certificates on natural labels | refuted for HJ's form by Theorem B1 | same |
| Sun's individualize-then-average | no linear structure exists in a general quasigroup | same |
| "Hard cases are group-like" | not established; index-2 towers carry non-associative data | same |

## Avoiding HJ's σ channel (w28, not yet red-teamed)

| Idea | Where it stopped | Source |
|---|---|---|
| Exact memoization by kernel state | distinct states are at least the number of flags; saves only n^{O_κ(1)} on X_m (M1) | [w28-sigma](../docs/w28-sigma.md) §3 |
| Coarse memo keyed by D_j | unsound in general; still 2^{m²/4} values, so it can at best halve the constant (M2) | same §3 |
| Merging tests into orbits | works on X_m with certified automorphisms (P1, and P2 as a sketch); has nothing to use on rigid inputs (R1); local equivalence is unsound (P3) | same §4, §8 |
| A thin canonical test family | any Aut-invariant rule is all-or-none on independent T (C1) | same §5 |
| Lazy Step 4 (LHJ) | correct (L1) and removes the chain on X_m (L2), but the cost moves to the Q channel (Q1, a sketch); the residual uniform case is open | same §5–6 |
| A sharper charge for σ | improves only case (a) of Theorem U, by a constant factor; does not go below log² | same §7 |
| A rigid lower bound | rigid variants tested have WL-visible anchors (R2, experiment only) | same §8 |

## Practical experiments

| Idea | Result | Source |
|---|---|---|
| HJ's local certificates | cost about 10–60× and never reduced branching in measured runs. Certificates remain available (`certificates=True`); benchmarks use `certificates=False` | round 1 results [r1-branch-cert](../bench/results/r1-branch-cert.json); project notes |
| Paper's two normalization cosets (Sym→Alt) | doubled every giant step; replaced by working on Sym(q) directly | [README](../README.md) |
| Down-edge wreath product in `bounded.py` | exact but gave each vertex a Sym factor; much slower than the twin-class form (Q7 18.8 s vs 0.11 s) | [bounded-degree](../docs/bounded-degree.md) |
| Wall-clock individualization budget | non-deterministic output; replaced by counted work | [README](../README.md) |
| Dispatcher (M) on natural families | changed nothing measurable (natural families reach no small non-natural giant action) | [bounded-degree](../docs/bounded-degree.md) §3 |
| `young_pick="small"` (default) on projective planes | label depth grows linearly in q. `young_pick="large"` keeps depth 3–5 but is not the default; rigid random structures get worse (attempts double on random Latin squares) | [hardness](../docs/hardness.md) |
| Largest-class prototype on Hall(9) | no help: cost is graph-level pruning, not depth | same |
| AVX2 clones in the C kernel | about 0.4% end to end; removed | [w16-ckernel](../docs/w16-ckernel.md) §2 |
| Compiling `_schreier`, `_orbit`, `PermGroup.__init__` | not worthwhile by measurement | same §1 |
| k-XOR multipedes (`multipede4`) | 2-WL splits gadgets; behaves like `multipede` | [hardness](../docs/hardness.md) |
| Finding hardness in small instances | fits on n ∈ [30, 300] cannot separate polynomial from n^{c log n}; use the trend of the local exponent instead | same |
| Solvable-layer extension of `ea2` | not done; profiles did not point to it, so `gi.canon` has no polynomial guarantee at d ≤ 5 | [w14-solver](../docs/w14-solver.md) |
| Compiling the F₂ solver first (`ea_canon`) | worth only 3–8% on Miyazaki and multipedes; the multipede cost was `SparseEA.restrict` | [w23-speed2](../docs/w23-speed2.md) §2 |

## Literature access attempts

See [Disclosures](Disclosures.md#literature-that-was-not-read).
