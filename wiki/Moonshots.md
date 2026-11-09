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

Source: `docs/w18-latin.md` (on master from `860e782`; this wiki branch was cut at `b1a2d03`, so the file is not linked here). The memo is at commit `8047173`, **not yet red-teamed**. The brief: n^{o(log n)} for Latin square or Steiner triple system isomorphism, and whether any graph family forces n^{log n} on HJ's algorithm.

* **No n^{o(log n)} algorithm** for general Latin squares, Steiner triple systems or conference graphs.
* **Theorem A1:** quasigroup, Latin-square isotopy and STS isomorphism in n^{(1/2)log₂ n + O(1)} time and space, an immediate extension of Rosenbaum's bidirectional collision. Proven; not found stated for quasigroups.
* **Theorem A2, Lemma A3:** a DP over the subquasigroup lattice runs in poly(n, M, A); structural lemmas about generation chains.
* **Theorem B1:** HJ creates ≥ n^{(1/8)log₂ n − O_κ(1)} recursive calls on the PG(m−1,2) incidence graphs, through the σx channel. Answers the earlier question of whether any graph family forces n^{log n} on HJ. A bound on HJ, not on GI. See [Barriers](Math-Barriers.md#hj-is-tight-on-graphs-too-w18).
* Latin-square graphs of Z₂^m and STS block graphs: same chain, sketch. Paley graphs: no chain (Aut solvable), sketch. A rigid variant of X_m: sketch.

Simulations ran at κ = 3, m ≤ 7, and check the window structure only.

The empirical background is [hardness.md](../docs/hardness.md): no family at n ≤ 300 made branch counts grow superpolynomially except projective planes through one heuristic ([details](Tried-and-Failed.md#practical-experiments)).

## Practical moonshots

See [hardness.md](../docs/hardness.md) and the [benchmarks](Benchmarks.md). The headline practical result, beating nauty and Traces on multipedes, came from linear algebra over F₂ in the Luks layers, not from the HJ recursion.
