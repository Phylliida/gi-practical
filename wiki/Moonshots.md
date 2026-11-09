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

## Latin squares and Steiner systems (in progress)

**As of commit `4137ae7` on branch `w18-latin`, in progress.** The branch has no commits of its own. Its brief: n^{o(log n)} for Latin square or Steiner triple system isomorphism, and whether any graph family forces n^{log n} on HJ's algorithm. Update this section when it lands; see [Maintaining](Maintaining.md).

The empirical background is [hardness.md](../docs/hardness.md): no family at n ≤ 300 made branch counts grow superpolynomially except projective planes through one heuristic ([details](Tried-and-Failed.md#practical-experiments)).

## Practical moonshots

See [hardness.md](../docs/hardness.md) and the [benchmarks](Benchmarks.md). The headline practical result, beating nauty and Traces on multipedes, came from linear algebra over F₂ in the Luks layers, not from the HJ recursion.
