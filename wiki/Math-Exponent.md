# The exponent c in n^{O(log^c d)}

GNS prove isomorphism for maximum degree d in n^{O((log d)^c)} without specifying c. This work bounds c without using HJ.

[Home](Home.md) · Sources: [w8-gnsexp](../docs/w8-gnsexp.md), [w10-blackbox](../docs/w10-blackbox.md), [w12-theoremg](../docs/w12-theoremg.md), reports [w9](../docs/redteam-w8-gnsexp.md), [w11](../docs/redteam-w10-blackbox.md), [w15](../docs/redteam-theoremg.md) · Paper: [exponent.tex](../paper/exponent.tex), [exponent.pdf](../paper/exponent.pdf) · Ledger: [section 5](Results-Ledger.md#5-the-exponent-c-in-nologc-d-does-not-depend-on-hj-unless-stated)

Notation: L = log₂(d+2), log n = L^x, "exponent c" means n^{O(L^c)}. B–H is Babai's algorithm with Helfgott's analysis, exp(O(log³ N)).

## The ladder

| Version | Black box cost | Worst exponent over d | Exponent 3 when | Status |
|---|---|---|---|---|
| GNS as written, with the 7.2 fix | 2^{O(L⁶)} (B–H) | 5 | | proven (bookkeeping, an upper bound from the written proof) |
| + known domain count + B–H switch | 2^{O(L⁶)} | 4 | x ≤ 1.5 | **known prior work** (Grohe–Neuen survey Thm 4.16) |
| + Lemma A / Prop B | 2^{O(L⁶)} | 4 | x ≤ 1.5 or x ≥ 3 | proven, AI red-teamed |
| + Theorem X | 2^{O(L⁵)} | **10/3** | x ≤ 1.5 or x ≥ 2 | proven modulo, AI red-teamed |
| Theorem G | no t-ary black box | **3** | all x | proven modulo; **provisional**, one AI red-team |
| HJ as black box or whole-input switch | 2^{O(L⁴)} | 3 | all x (and x itself for x < 3) | conditional on HJ |

For GI, conditional on HJ, n^{O(min(L³, log n))} ([w10](../docs/w10-blackbox.md) §2.4) subsumes X and G.

## The steps

* **Multiplicative giant decrease.** GNS have k′ ≤ k − k/(3 log k). [Lemma A](../docs/w8-gnsexp.md): a subgroup of S_k with an A_m composition factor, m > 3k/4, contains Alt(Δ), |Δ| ≥ m, fixing the rest. Combined with the symmetry defect, Prop B gives k′ ≤ 3k/4, so the macro step's tree height drops from O(L²) to O(L). Lemma A is CFSG-free, the algorithm is not.
* **Theorem C (w8).** GNS with the fix runs in n^{O(L³)}·(1 + X(d)), X(d) the cost of one black-box call.
* **The black box.** Only GNS's case (v) is expensive: two t-ary structures on m > 3k/4 points, with every injective t-tuple coloured by its comparison class (the call to Babai's test in GNS Lemma 6.7).
* **Theorem X.** One Design-Lemma/Split-or-Johnson round on the structure, then GNS's own algorithm on the reduced instance (an almost m-ary instance on m^t points), whose black boxes are on at most 3m/4 points. So X(m, t) ≤ 2^{O(t log³ m)}·X(3m/4, ·), which unrolls to 2^{O(t log³ m + log⁵ m)}. Hence n^{O(log³ d)}·2^{O(log⁵ d)}.
* **Theorem G.** Use the Design Lemma and Split-or-Johnson inside GNS's macro step and charge their branching to a hereditary tower potential (HBD's ρ ≤ 2 log N), never reset. Each round (S) shrinks the domain by 5/6, (T) inserts a tower level (ρ drops), or (J) is a Johnson step (k → O(√k)). With the maintained-tower rule (next block system above the top of the tower) the recurrence closes at N^{O(L²)} = n^{O(L³)}.
  The least-audited input is the functorial reading of Split-or-Johnson; the red-team corrected it (streams read elements of the current V₂, which may be blocks) and found no break. If Theorem G fails, Theorem X is unaffected.

## Regimes

| Range of x | Bound | Source |
|---|---|---|
| x ≥ 2 | n^{O(L³)} | Theorem C with Theorem X |
| 3/2 < x < 2 | n^{O(L³)} | Theorem G only; without it, exponent min(5−x, 2x), worst case 10/3 at x = 5/3 |
| 1 ≤ x ≤ 3/2 | exp(O(log³ n)) = n^{O(L^{2x})} | B–H alone |

Theorem G with B–H gives n^{O(min(log³ d, log² n))}. Theorem X improves on the previously signed statement only for 5/3 < x < 3; the worst case over d drops from 4 to 10/3. Theorem G improves on X only for 3/2 < x < 2.

## Limits

* c < 2 for all d would beat exp(O(log³ n)) for general GI (put d = n−1). This is a state-of-the-art statement, not a lower bound; c = 2 would merely match B–H at d = n.
* c = 3 is a limit of this accounting: log N = Θ(L log n) times K = Θ(L²) per macro step. A heuristic, not a theorem.
* The black box is self-similar: GNS-type methods applied to it need the same black box again.

## HJ Theorem A.9 independently

[w8-gnsexp](../docs/w8-gnsexp.md) §3 re-derived HJ's proof skeleton of the hereditary budget, except the CFSG primitive-valuation lemma, with one harmless slip in a constant. A weak form via GNS 3.13 gives σ ≤ C log d·log N for transitive Γ̂_d, and n^{O(log² d)} conditional on HJ §§4–7 but independent of the valuation lemma. Still CFSG-dependent.
