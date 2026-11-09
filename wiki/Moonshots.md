# Moonshots

Long-shot attempts: an honest try at each, done knowing success was unlikely.

[Home](Home.md) · Related: [Barriers](Math-Barriers.md), [Tried and failed](Tried-and-Failed.md)

## Beating n^{O(log n)} for general GI (r3-theory)

[moonshot-theory](../docs/moonshot-theory.md) dissects every term of HJ's potential and tries five routes. Outcome: no route below n^{log n}. Within the HJ framework the log² is a product of two independent Θ(log N) factors (giant breaking; enumeration of classical sections), each matching a classical open problem. The one positive outcome is the conditional degree-d bound, [Theorem R](Math-Degree-d.md).

## Affine equivalence (w17, w20)

**Target.** A 2^{o(k²)} = N^{o(log N)} algorithm for string isomorphism under AGL(k,2), the provably tight instance of HJ's enumeration channel. Sources: [w17-affine](../docs/w17-affine.md), [redteam-w17-affine](../docs/redteam-w17-affine.md), code in [docs/w17-affine-code](../docs/w17-affine-code/).

* **Result: no such algorithm.** But "nothing better than brute force" was wrong by a constant in the exponent.
* Theorem A (flags + Borel 2-group): canonical form in 2^{k²/2+k/2}·poly(N). Folklore.
* Theorem B (bidirectional collision): deterministic Iso in 2^{k²/4+k/2}·poly(N). A routine instance of Rosenbaum's framework.
* Theorem C: d-tensor isomorphism reduces to AGL(dk,2) string isomorphism. So a 2^{o(K²)} algorithm would solve every fixed-d tensor isomorphism in 2^{o(k²)}. A 2^{Ω(K²)} lower bound would be conditional on a 4-TI hypothesis without independent support.
* Literature: for cubic Boolean functions (char 2), a 2^{o(k²)} algorithm is not established by any source found; vectorial quadratics are done in 2^{O((m+k)^{1.5})} modulo arXiv:2610.00874, an unrefereed preprint.
* Experiments (k ≤ 10) could not distinguish k from k² scaling; the refinement was exact on all but a factor-2 exception. Too small to say anything about scaling.
* Effect on the campaign: Prop 2 is specific to HJ's dispatcher; only constants change. The Sylow trick and "λ halved" are discussed on [Corrections](Corrections.md#λ-coefficient-halved-in-theorem-r).

## The "ETH is False" preprint (w21)

"The Exponential Time Hypothesis is False" (OpenAI math release, unrefereed; dated 17 Oct, revised 25 Oct 2026) claims deterministic #k-SAT in (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)}. Source: [w21-eth](../docs/w21-eth.md), code in [docs/w21-eth-code](../docs/w21-eth-code/).

* **One adversarial AI read plus exact small-case tests found no flaw** in Secs. 2–4 and the Sec. 5 lift. Not a verification. Appendix D's sharper exponent, Appendix B bit sizes, and asymptotics were not checked. The cited Lean formalizations were not run or read. The reviewer is a Claude model and notes it is not independent of Anthropic's parallel claim.
* **No transfer to GI.** A polynomial reduction with N variables helps only if N ≲ log² n·√(log log n)/log log log n. Natural fixed-width encodings have about n² variables, and Sec. 4's M ≥ 32 b²(b+w) rules out affine equivalence and tensor isomorphism as written.
* **Effect on the campaign:** only the barrier statement, re-based on [CLIQUE-LB](Math-Barriers.md#the-clique-lower-bound-barrier).

## Latin squares and Steiner systems (w18)

Source: [w18-latin](../docs/w18-latin.md) (`8047173`), red-teamed by [redteam-w18-latin](../docs/redteam-w18-latin.md) (`b503900`), which found no claim broken. The memo's text was not edited afterwards; read it with the red-team's §5, or use [Corrections](Corrections.md#latin-squares-and-hj-on-graphs-w18-w26-w28). The brief: n^{o(log n)} for Latin square or Steiner triple system isomorphism, and whether any graph family forces n^{log n} on HJ's algorithm.

* **No n^{o(log n)} algorithm** for general Latin squares, Steiner triple systems or conference graphs.
* **Theorem A1:** quasigroup, Latin-square isotopy and paratopy, and STS isomorphism in n^{(1/2)log₂ n + O(1)} time and space. Sound after four repairs; a routine one-paragraph application of Rosenbaum's bidirectional collision, not found stated for quasigroups. Latin-square graphs on N vertices of large order: N^{(1/8)log₂ N + O(1)}, assuming recovery of the net (the memo's (1/4) is wrong).
* **Theorem A2, Lemma A3:** a DP over the subquasigroup lattice runs in poly(n, M, A); structural lemmas about generation chains. Sound (A3 with two wording fixes).
* **Theorem B1:** HJ as written creates ≥ n^{(1/8)log₂ n − O_κ(1)} recursive calls on the PG(m−1,2) incidence graphs, through the σx channel. AI red-teamed: sound as a statement about HJ as written, asymptotic only (no nesting below m ≈ 214 at κ = 64; the cutoff is q₁ = 486290 at Lean's parameters). Answers the earlier question of whether any graph family forces n^{log n} on HJ. A bound on HJ, not on GI. See [Barriers](Math-Barriers.md#hj-is-tight-on-graphs-too-w18).
* Latin-square graphs of Z₂^m and STS block graphs: same chain, sketch; the red-team could not exhibit or refute it at small sizes. Paley graphs: no chain (Aut solvable), sketch. The single-switched-block rigid variant in w18 §2.9 is false; see w28 below.

w18's simulations ran at κ = 3, m ≤ 7, and check the window structure only. The red-team's replay reached κ = 5 at level 0 and on a level-1 state, and κ = 3, 4 with nontrivial 𝒰; no run nests two certificate calls.

The empirical background is [hardness.md](../docs/hardness.md): no family at n ≤ 300 made branch counts grow superpolynomially except projective planes through one heuristic ([details](Tried-and-Failed.md#practical-experiments)).

## Removing HJ's σx channel (w28)

Source: [w28-sigma](../docs/w28-sigma.md) (`27292f8`), **not yet red-teamed**. Everything assumes HJ correct; the Lean was not consulted; no claim is machine-checked. The brief: can HJ avoid paying for the σx channel that the PG(m−1,2) family exploits?

* **The channel can be removed on the B1 family** by a small change, lazy Step 4 (LHJ), but the cost moves to the Q channel unless automorphism pruning is added. In the worst case Step 4 survives on a "uniform" residue that could not be eliminated.
* **The per-phase exponent does not change.** No barrier is contradicted. Details and statuses: [Barriers](Math-Barriers.md#can-hj-avoid-the-σx-channel-w28-not-yet-red-teamed), [ledger](Results-Ledger.md#3-lower-bounds-for-specific-algorithms-and-barriers).
* **Correction to w18 §2.9:** one switched block leaves |Aut| = 2^{m²−O(m)}. A rigid variant X_{m,R} deletes O(m) lines; it is not a barrier (rigid instances tested became discrete under bounded WL, m ≤ 9).
* **Theorem U** (Ray-Chaudhuri–Wilson with variable blocks) and **Theorem L** (limitation for prefix-determined rules). The Uniform Prefix Conjecture is speculation.

Experiments are small (m ≤ 9, no nesting) and check statuses, root windows and refinement only.

## Complete-tree tanglegrams (w27)

**In progress as of `1368fb6`:** `w27-tree` targets R1_c, the smallest open family. Nothing is folded in yet; see [Core problem](Math-Core-Problem.md).

## Practical moonshots

See [hardness.md](../docs/hardness.md) and the [benchmarks](Benchmarks.md). The headline practical result, beating nauty and Traces on multipedes, came from linear algebra over F₂ in the Luks layers, not from the HJ recursion.
