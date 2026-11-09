# Barriers

Why n^{O(log n)} for GI and n^{O(log d)} for degree-d GI are hard to beat. Nothing here is a general lower bound for GI.

[Home](Home.md) · Sources: [moonshot-theory](../docs/moonshot-theory.md), [w1-fpt](../docs/w1-fpt.md), [w1-structure](../docs/w1-structure.md), [w21-eth](../docs/w21-eth.md) · Ledger: [section 3](Results-Ledger.md#3-lower-bounds-for-specific-algorithms-and-barriers)

## HJ is tight on string isomorphism

* **AGL(k,2)** (moonshot Prop 2): HJ's `Solve` enumerates this group at the root, creating ≥ |G| ≥ 0.288·N^{1+log₂N} branches for every pair of strings, so HJ's Theorem 1.2 bound is tight *for HJ's algorithm*.
* **(F₂^{D−1} ⋊ S_D) ≀ C_m** (w1-fpt Prop 3.1): primitive and in Γ̂_D for odd D; HJ and HJ+(M′) create ≥ N^{log₂D − 0.443} children, at every fixed D. So R\*'s exponent O(log d) is tight for that algorithm, and GNS Thm 3.13's exponent cannot be o(log d).
* **G_{r,L}** (w1-structure Prop 4.2): ≥ N^{r+1−1.8/r−o(1)} branches, though FPT by another method given its tower data.

These are proofs about what the algorithm does (read from HJ's pseudocode and Lean dispatcher); they do not assume HJ correct. They **hold for string isomorphism only**, and have not been transferred to graphs. w20 adds: Prop 2 is about the dispatcher, not the problem, since Theorems A, B of [w17](../docs/w17-affine.md) beat it by a constant in the exponent.

## HJ is tight on graphs too (w18)

**Theorem B1** (w18, given HJ as written; **not yet red-teamed**): on the point–line incidence graph X_m of PG(m−1,2), with n ≈ 2^{2m}/6, HJ creates at least n^{(1/8)log₂ n − O_κ(1)} recursive calls for every fixed certificate size κ, by a chain of nested certificate calls through the visible unaffected orbit (σx) term, not the Maróti enumeration channel. Source: `docs/w18-latin.md` (on master from `860e782`; this wiki branch was cut at `b1a2d03`, so the file is not linked here).

So the n^{Θ(log n)} behaviour of HJ is not confined to string isomorphism. It is **not a lower bound for GI**: X_m is a fixed geometry, easily solved by other means. It implies that a better potential cannot improve HJ; any improvement must change the certificate recursion (or prune tests). The chain was simulated exactly at κ = 3 and m ≤ 7 for its window structure only.

## Classical barriers for n^{o(log n)}

An n^{o(log n)} GI algorithm would give n^{o(log n)} algorithms for all of these (moonshot §3):

* **group isomorphism**, by the O(m²)-vertex Cayley encoding (Miller 1979). Best general bound n^{c log n}, where only c has improved; Sun (2023) and IMQSZ (2024) cover p-groups of class 2 and 3-tensor isomorphism, not general groups.
* **quasigroup / Latin-square isomorphism, Steiner triple systems, conference graphs.** Best bounds still n^{O(log n)} since 1978–80 (Miller; Babai 1980).
* **affine equivalence of arbitrary colourings of F₂^k** in 2^{o(k²)} via a Θ(N³)-vertex affine-plane encoding (Prop 3). See [Moonshots](Moonshots.md#affine-equivalence-w17-w20).

The exponent factors into giant breaking (log N·log w) and enumeration of classical sections (log N·μ), each matching one of these open problems.

## Other algorithm-specific barriers

* **WL**: dimension Ω(n) on degree 3 graphs (CFI), and Ω(|V|) on binary tanglegrams.
* **Individualization-refinement**: 2^{Ω(n)} search trees for refinement within fixed-dimension WL (Neuen–Schweitzer 2018). This rules out pure IR, including this repo's front end, as a route even to quasipolynomial time.
* **No lower bound is known for any class containing Luks-type coset recursion.** The only bounds are the algorithm-specific ones above. A lower bound for a coset-splitting model with or without memoization is open.

## The Clique-lower-bound barrier

W[1]-hardness of GI by degree, of TreeCI, or of tanglegrams would need a parameter blow-up g(k) ≥ 2^{k^Ω(1)}, or else GNS's n^{polylog g(k)} would solve k-Clique in f(k)n^{o(k)}. Conditional on HJ's R\*, g(k) ≥ 2^{Ω(k)}. **The hypothesis is CLIQUE-LB** (k-Clique has no f(k)n^{o(k)} algorithm), not ETH; see [Corrections](Corrections.md#the-eth-barrier).

## Attempts that stopped at these barriers

See [What we tried](Tried-and-Failed.md) and [moonshot-theory](../docs/moonshot-theory.md) §4–5: a polynomial-shrinking Split-or-Johnson would beat the 1978–80 bounds; a non-enumerative treatment of classical sections would give 2^{o(k²)} affine equivalence.
