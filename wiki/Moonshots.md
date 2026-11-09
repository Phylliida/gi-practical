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
* Literature at w17: for cubic Boolean functions (char 2), a 2^{o(k²)} algorithm was not established by any source found; vectorial quadratics are done in 2^{O((m+k)^{1.5})} modulo arXiv:2610.00874, an unrefereed preprint. **Later:** see [Cubic Boolean equivalence](#cubic-boolean-equivalence-w35-w37), conditional on that same preprint.
* Experiments (k ≤ 10) could not distinguish k from k² scaling; the refinement was exact on all but a factor-2 exception. Too small to say anything about scaling.
* Effect on the campaign: Prop 2 is specific to HJ's dispatcher; only constants change. The Sylow trick and "λ halved" are discussed on [Corrections](Corrections.md#λ-coefficient-halved-in-theorem-r).

## The "ETH is False" preprint (w21)

"The Exponential Time Hypothesis is False" (OpenAI math release, unrefereed; dated 17 Oct, revised 25 Oct 2026) claims deterministic #k-SAT in (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)}. Source: [w21-eth](../docs/w21-eth.md), code in [docs/w21-eth-code](../docs/w21-eth-code/).

* **One adversarial AI read plus exact small-case tests found no flaw** in Secs. 2–4 and the Sec. 5 lift. Not a verification. Appendix D's sharper exponent, Appendix B bit sizes, and asymptotics were not checked. The cited Lean formalizations were not run or read. The reviewer is a Claude model and notes it is not independent of Anthropic's parallel claim.
* **No transfer to GI.** A polynomial reduction with N variables helps only if N ≲ log² n·√(log log n)/log log log n. Natural fixed-width encodings have about n² variables, and Sec. 4's M ≥ 32 b²(b+w) rules out affine equivalence and tensor isomorphism as written.
* **Effect on the campaign:** only the barrier statement, re-based on [CLIQUE-LB](Math-Barriers.md#the-clique-lower-bound-barrier).

## Latin squares and Steiner systems (w18)

Source: [w18-latin](../docs/w18-latin.md) (`8047173`), red-teamed by [redteam-w18-latin](../docs/redteam-w18-latin.md) (`b503900`), which found no claim broken. The memo's q₁ cutoff and (1/8) exponent were corrected in `w39`; the rest of the report's §5 was not applied, so read it with the red-team's §5, or use [Corrections](Corrections.md#latin-squares-and-hj-on-graphs-w18-w26-w28). The brief: n^{o(log n)} for Latin square or Steiner triple system isomorphism, and whether any graph family forces n^{log n} on HJ's algorithm.

* **No n^{o(log n)} algorithm** for general Latin squares, Steiner triple systems or conference graphs.
* **Theorem A1:** quasigroup, Latin-square isotopy and paratopy, and STS isomorphism in n^{(1/2)log₂ n + O(1)} time and space. Sound after four repairs; a routine one-paragraph application of Rosenbaum's bidirectional collision, not found stated for quasigroups. Latin-square graphs on N vertices of large order: N^{(1/8)log₂ N + O(1)}, assuming recovery of the net (the memo originally said (1/4)).
* **Theorem A2, Lemma A3:** a DP over the subquasigroup lattice runs in poly(n, M, A); structural lemmas about generation chains. Sound (A3 with two wording fixes).
* **Theorem B1:** HJ as written creates ≥ n^{(1/8)log₂ n − O_κ(1)} recursive calls on the PG(m−1,2) incidence graphs, through the σx channel. AI red-teamed: sound as a statement about HJ as written, asymptotic only (no nesting below m ≈ 214 at κ = 64; the cutoff is q₁ = 486290 at Lean's parameters). Answers the earlier question of whether any graph family forces n^{log n} on HJ. A bound on HJ, not on GI. See [Barriers](Math-Barriers.md#hj-is-tight-on-graphs-too-w18).
* Latin-square graphs of Z₂^m and STS block graphs: same chain, sketch; the red-team could not exhibit or refute it at small sizes. Paley graphs: no chain (Aut solvable), sketch. The single-switched-block rigid variant in w18 §2.9 is false; see w28 below.

w18's simulations ran at κ = 3, m ≤ 7, and check the window structure only. The red-team's replay reached κ = 5 at level 0 and on a level-1 state, and κ = 3, 4 with nontrivial 𝒰; no run nests two certificate calls.

The empirical background is [hardness.md](../docs/hardness.md): no family at n ≤ 300 made branch counts grow superpolynomially except projective planes through one heuristic ([details](Tried-and-Failed.md#practical-experiments)).

## Removing HJ's σx channel (w28)

Source: [w28-sigma](../docs/w28-sigma.md) (`27292f8`), AI red-teamed by [redteam-w27-w28](../docs/redteam-w27-w28.md) (`894cc10`), which found no claim broken (one boundary fix, one repaired existence step, and no certification of P2, Q1 or the Uniform Prefix Conjecture). Everything assumes HJ correct; the Lean was not consulted; no claim is machine-checked. The brief: can HJ avoid paying for the σx channel that the PG(m−1,2) family exploits?

* **The channel can be removed on the B1 family** by a small change, lazy Step 4 (LHJ), but the cost moves to the Q channel unless automorphism pruning is added. In the worst case Step 4 survives on a "uniform" residue that could not be eliminated.
* **The per-phase exponent does not change.** No barrier is contradicted. Details and statuses: [Barriers](Math-Barriers.md#can-hj-avoid-the-σx-channel-w28), [ledger](Results-Ledger.md#3-lower-bounds-for-specific-algorithms-and-barriers).
* **Correction to w18 §2.9:** one switched block leaves |Aut| = 2^{m²−O(m)}. A rigid variant X_{m,R} deletes O(m) lines; it is not a barrier (rigid instances tested became discrete under bounded WL, m ≤ 9).
* **Theorem U** (Ray-Chaudhuri–Wilson with variable blocks) and **Theorem L** (limitation for prefix-determined rules). The Uniform Prefix Conjecture is speculation.

Experiments are small (m ≤ 9, no nesting) and check statuses, root windows and refinement only.

## Height-2 posets and complete-tree tanglegrams (w27)

Source: [w27-tree](../docs/w27-tree.md) (`b11f2d3`), AI red-teamed by [redteam-w27-w28](../docs/redteam-w27-w28.md) (`894cc10`), which found no claim broken and narrowed three. The brief: decide the smallest open poset family, attack R1_c by new routes, prove a restricted lower bound. **Neither was settled.** Details: [Core problem](Math-Core-Problem.md#height-2-posets-and-r1_c-w27); corrections: [Corrections](Corrections.md#height-2-posets-and-r1_c-w27-w31).

* **Prop N and Cor N.1** (proven). The depth of the A₅ wreath tower bounds what a bounded-height poset can absorb, so gadget-style hardness for height-2 posets from R1_c is excluded. Corollary narrowed: it does not reduce the question to the FPT side.
* **Theorems G, G+, C** give sub-classes: pinning sets (XP in ρ, not FPT in (b, ρ)), and a soluble surviving top, modulo ADKT and Luks with Pálfy–Wolf.
* **Open residue:** non-abelian gain graphs with curvature over a large non-soluble top (§2.5).

## Steiner triple systems and the GL barrier (w30, w33)

Source: [w30-sts](../docs/w30-sts.md) (`ffda3f4`), AI red-teamed by [redteam-w30-sts](../docs/redteam-w30-sts.md) (`a6d1fcc`), which found no break. The memo's text was not edited afterwards; see [Corrections](Corrections.md#steiner-triple-systems-w30-w33). The brief: n^{o(log n)} for Steiner triple systems via a structure dichotomy.

* **No n^{o(log n)} algorithm.** The dichotomy holds only at the top of the rank range.
* **T1**, improved by the red-team: rank above 0.9031·log₂(n+1) forces a PG(d−1,2) quotient above a maximizer, for 1 < λ < (log₂10)/3, and this threshold is sharp at AG(2,3).
* **T2** (hand proof, confirmed by exact checks to d = 4): linear equivalence of Boolean functions on F₂^d reduces to STS isomorphism on 2^{d+3} − 1 points, so n^{o(log n)} for STS would give 2^{o(d²)} string isomorphism under GL(d,2). **An implication, not a lower bound**; nothing shows these are the hardest STS, and the w30 phrases "hardest instances" and "exactly the barrier" are not supported. On the T2 family the problem is decided in n^{(1/4+o(1))log₂ n}.
* **T3, T5, C4:** the analogue over F_q under an index gap; an STS within n^{o(1)} blocks of a PG in n^{o(log n)}; w18's "locally algebraic" lead refuted (about Steiner loops).
* **Prior art:** the fibration form is Jungnickel–Tonchev Thm 2.8/2.9, and no reduction to STS isomorphism was found ([Corrections](Corrections.md#the-pg-fibration-form-of-w30-is-jungnickeltonchev)). The near-top bound n^{(1/4+o(1))log n} for all c = O(1) stays a sketch.

Experiments are small (at most a few hundred points) and do not bear on scaling.

## Conference graphs (w32, w34)

Sources: [w32-conference](../docs/w32-conference.md) (`49fec8a`), **not red-teamed**; [w34-vc](../docs/w34-vc.md) (`005ca3c`), AI red-teamed by [redteam-w35-w34](../docs/redteam-w35-w34.md) (`dce72f3`), which found no break. The brief: conference graphs below n^{log n}, against the best bound n^{2 log₂ n + O(1)} (Babai 1980); Levet's Question 6.5 (an individualization set of size O(1) or o(log n)) remains open.

* **No n^{o(log n)} algorithm**, for the class or for the Cayley subclass.
* **w32 (not red-teamed):** exact identities for the triple correlation T(a,b,v); a bad-pair reduction; the natural lemma "collision probability → 0 for all pairs" is false, on iterated Turyn products of P(9). Paley O(1) by Deligne–Katz is a sketch. Data: minimum 1-WL depth 2 or 3 in every tested graph (Spence to 49, Paley to 1097, Turyn to 6561), which cannot separate O(1) from slow growth.
* **w34 (red-teamed):** the VC route cannot reach o(log n): one-round VC is at least ⌊½ log₂ n⌋ − 4, and on Turyn products multi-round VC is at least log_v n − 1. Thm 4.1 replaces it by depth ≤ 2⌈3 ln n/ln(1/τ)⌉ + 88 d(τ) + 22; n^{o(log n)} follows only conditionally, if d(τ) = o(log n), proved for no non-trivial family. Latin squares of Z₂^k need depth Ω(log n), so that analogue of Levet's question is negative.

## Cubic Boolean equivalence (w35, w37)

Source: [w35-cubic](../docs/w35-cubic.md) (`8fb152f`), AI red-teamed by [redteam-w35-w34](../docs/redteam-w35-w34.md) (`dce72f3`), which found no break. The memo's text was not edited afterwards.

* **Theorems A, B, C (proven by hand, for all n):** exact reductions from cubic Boolean equivalence to isometry of spaces of quadratic forms over F₂, via a squares gadget, a pairing, and radical elimination. Solutions correspond one-to-one with Iso(f,g) (a sharpening by the red-team).
* **Theorem D, conditional:** AGL/GL equivalence of cubics decided in 2^{Õ(n^{1.5})}, **conditional on arXiv:2610.00874 Thm 1.2** (unrefereed, partly audited, one repairable running-time defect). A second route via Sun, arXiv:2611.05920 Thm 1.1 and Thm F gives GL-equivalence in 2^{O(n^{51/26} log n)}, also unrefereed. So the headline 2^{o(n²)} no longer depends on one preprint, but it depends on an unrefereed one either way.
* **Consequences, conditional:** alternating tuple and space isometry, 3-tensor isomorphism and ATF equivalence over F₂, and T2 instances with cubic colourings in n^{Õ(√log n)}. **Nothing for general STS**; hard T2 instances, if any, need degree ≥ 4.
* Decision only, not a canonical form. Novelty: Theorem B and the composite appear new as far as a limited search could determine; E(i)'s tuple case is not ([Corrections](Corrections.md#alternating-tuple-isometry-in-characteristic-2-w35-ei-is-sun-2026)).

## Practical moonshots

See [hardness.md](../docs/hardness.md) and the [benchmarks](Benchmarks.md). The headline practical result, beating nauty and Traces on multipedes, came from linear algebra over F₂ in the Luks layers, not from the HJ recursion.
