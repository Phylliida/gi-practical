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

## Height-2 posets and R1_c (w27)

| Idea | Where it stopped | Source |
|---|---|---|
| CI directly in G₂ = K₂ ⋊ T₂ for arbitrary subgroups | gives a double-coset condition on t in C; computing its zero set is a point stabilizer on a set of size 2^{Ω(b^m)} | [w27-tree](../docs/w27-tree.md) §2.5 |
| Row-first DP with definable cores | the choice of each row block's order compounds to (b!)^{b^s} at level s | same |
| Canonical gauge-fixing from a lexicographic order of V | the orders are moved by T, (b!)^m of them: XP | same |
| Balanced left/right recursion on HT2 | T(m) ≤ (b!)²T(m−1) + poly: XP, the same multiplicative form as Prop S | same |
| Reduction to a bounded-μ poset by re-coordinatising gauges | μ is intrinsic to the fibre order | same |
| HT2 as a template for R1_c | W_h = W_{h/2} ≀ W_{h/2} is formally right, but pinning costs \|W_{h/2}\|; Theorems G, G+, C do not lift | same §3.2 |
| Theorem L objects (w1-structure) on tanglegrams | Lemma MD: no faithful domain below N for the shared W_h | same |
| Peeling Sym(b) with a one-call combine | the definable version is impossible (Prop 3.2); a non-definable one is TreeCI on the frontier | same |
| Memoised state over block pairs | reproduces Prop 4.1; no compression below the coset itself | same |
| Goursat potential along root-leaf paths | a property of the answer, not the input; no potential found | same |
| Split-or-Johnson for tree pairs | no usable relational structure on children obtained | same |

## Latin squares and Steiner systems (w18)

| Idea | Where it stopped | Source |
|---|---|---|
| Generator enumeration with a coset representation of Aut(T) | extension test is a string-isomorphism condition under Aut(T), as hard as the original | [w18-latin](../docs/w18-latin.md) §3.4 |
| Top-down chain enumeration | gives exactly Miller's bound; only the bidirectional split (Theorem A1) halves it | same |
| HJ-style constant-size certificates on natural labels | refuted for HJ's form by Theorem B1 | same |
| Sun's individualize-then-average | no linear structure exists in a general quasigroup | same |
| "Hard cases are group-like" | not established; index-2 towers carry non-associative data | same |

## Avoiding HJ's σ channel (w28)

| Idea | Where it stopped | Source |
|---|---|---|
| Exact memoization by kernel state | distinct states are at least the number of flags; saves only n^{O_κ(1)} on X_m (M1) | [w28-sigma](../docs/w28-sigma.md) §3 |
| Coarse memo keyed by D_j | unsound in general; still 2^{m²/4} values, so it can at best halve the constant (M2) | same §3 |
| Merging tests into orbits | works on X_m with certified automorphisms (P1, and P2 as a sketch); has nothing to use on rigid inputs (R1); local equivalence is unsound (P3) | same §4, §8 |
| A thin canonical test family | any Aut-invariant rule is all-or-none on independent T (C1) | same §5 |
| Lazy Step 4 (LHJ) | correct (L1) and removes the chain on X_m (L2), but the cost moves to the Q channel (Q1, a sketch); the residual uniform case is open | same §5–6 |
| A sharper charge for σ | improves only case (a) of Theorem U, by a constant factor; does not go below log² | same §7 |
| A rigid lower bound | rigid variants tested have WL-visible anchors (R2, experiment only) | same §8 |

## Steiner triple systems below n^{log n} (w30)

| Idea | Where it stopped | Source |
|---|---|---|
| Closure-size expansion: o(log n) points generate everything unless structured | the dichotomy is proved only near the top of the rank range (T1, now r > 0.9031ℓ); below it, mixing of extension indices is not controlled and T3 needs an index gap | [w30-sts](../docs/w30-sts.md) §9, [redteam](../docs/redteam-w30-sts.md) §2.3 |
| Low-depth generation | depth does not bound Miller's branching | same |
| WL dimension of STS | only the trivial O(log n); all STS look alike to pair refinement at depth ≤ 1 (observed); no lower bound beyond small examples | same |
| HJ-style constant-size local certificates on points | refuted for HJ's algorithm by B1; any such certificate would, via T2, give 2^{o(d²)} linear equivalence | same |
| Group techniques on the residue (Sun/IMQSZ) | no bilinear or trilinear core at p = 2 | same §6, §9 |
| Luks-type splitting on the GL base | gives only the constant in the exponent, 1/4 against 1/2 (w17 Theorem B) | same §9 |
| Counting random STS for rank 3 | the needed count was not found or proved | same |

## Conference graphs below n^{log n} (w32, w34)

| Idea | Where it stopped | Source |
|---|---|---|
| Uniform anti-concentration: p(v,w) ≤ exp(−ω(n)) for all pairs | **false**: iterated Turyn products keep collision probability ≥ 0.049 for all n (Thm 4.2; w32 is not red-teamed) | [w32-conference](../docs/w32-conference.md) §4 |
| Structure of large cliques in B_c | no inverse theorem at hypothesis p ≥ n^{−c}; Turyn shows the structured side must include tensor products | same §4.3 |
| Approximate F₂-linearity of rows | a Hamming-noise 1%-regime problem; polynomial Freiman–Ruzsa could not be made to apply | same §4.4 |
| Moment methods on T | L² gives Lemma 2.1; L⁴/Hausdorff–Young is extremal for characters | same §7 |
| VC dimension o(log n) | false: Θ(log n) for one round on every conference graph, and on iterated Turyn products for every fixed number of rounds. It obstructs the proof technique, not small hitting sets (those graphs have depth 3 at every tested level) | [w34-vc](../docs/w34-vc.md) §2–3 |
| Stronger hypothesis Σ p₂(y, y′) ≤ \|Q\|^{1−δ} | false on Turyn iterates | same §4 |
| Growth lemma for the stable algebra | none; each round's identity is consistent with no growth | same §6, [w32](../docs/w32-conference.md) §4.5 |
| Inverse theorem from B_c-cliques to Delsarte/grid structure | no route found; only exact formulas on Turyn products | [w34-vc](../docs/w34-vc.md) §5 |

## Cubic Boolean equivalence (w35)

| Idea | Where it stopped | Source |
|---|---|---|
| Contract to alternating bilinear forms, treat the lower-order part as a separate Dickson-type step | the fibre of f ↦ τ_f is acted on by the uncontrolled Aut(τ), and GIQS is decision-only, so no generators to run Dickson under; the lower-order part carries GIQS-level difficulty. Replaced by folding the kernel into one instance | [w35-cubic](../docs/w35-cubic.md) §2.6 |
| The Sun/IMQSZ tuple step over F₂ | the *-symmetric decomposition X\*X = E relies on IQ19's lifting, which divides by 2 and has no procedure over F₂; w35 goes through GIQS and Theorem A instead | same §1.1, [redteam](../docs/redteam-w35-w34.md) §5 |
| Degree ≥ 4 by the same gadget | the absorption is Frobenius additivity of squaring, with no analogue for cubic lifts (speculation on whether a substitute exists) | [w35-cubic](../docs/w35-cubic.md) §5 |

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
