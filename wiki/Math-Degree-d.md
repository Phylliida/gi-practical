# The n^{O(log d)} bound for maximum degree d

**Claim.** Graph isomorphism for graphs of maximum degree d is decidable in n^{O(log(d+2))}, *conditional on HJ's analysis being correct*.
This is the project's Theorem R\* and Corollary R\*.

[Home](Home.md) · Sources: [moonshot-theory](../docs/moonshot-theory.md) §4.1, [verify-theorem-R](../docs/verify-theorem-R.md), [redteam-theorem-R](../docs/redteam-theorem-R.md) · Ledger: [section 2](Results-Ledger.md#2-the-nolog-d-bound-and-analysis-of-hj-conditional)

## Status

Conditional on (H0): HJ's algorithm and analysis, Sections 4–7 and Appendix A, are correct as written. The derivation had one AI verification and one AI red-team, which found
no hole outside (H0). HJ's own bound is machine-checked modulo axioms, but **the Λ-potential, the dispatcher (M′) and the regrouping below are not machine-checked**. The
Luks/Babai–Luks reduction and the GNS inputs are trusted, not re-proved. No human has checked it. At d = O(1) it matches Luks, at d ≥ n^ε it matches HJ, and at d = polylog n it gives n^{O(log log n)}.

## Setting

Γ̂_d is the class of groups whose composition factors all embed in S_d. It is closed under subgroups, quotients and extensions. Isomorphism of graphs of maximum degree d reduces by
Luks / Babai–Luks in polynomial time, independent of d, to string isomorphism under Γ̂_{d−1} (or Γ̂_d) groups on domains of polynomial size.

## Derivation

Theorem R\*: HJ with dispatcher (M′) solves Γ̂_d string isomorphism on N points in exp(O(log(N+2)·log(d+2)))·poly(input). The argument:

1. **No wide giants.** In phases with d ≤ N^α, every giant has q ≤ d ≤ λ = N^α, so GiantStep never takes the q > λ branch: no RowStep, no row terminals, no column floors, no in-domain rectangles. E_N becomes N^{O(1)}. In phases with d > N^α run HJ verbatim; its bound exp(C log² N) is then ≤ exp((C/α) log N log d).
2. **Closure.** Every group the algorithm acts on stays in Γ̂_d, including overcoset lifts (always taken inside the frozen parent), so every giant has q ≤ d.
3. **The dispatcher (M′)**, replacing "enumerate by order". Recognize, and run product refinement and GiantStep, exactly when Soc(P) ≅ (A_m^{(t)})^k in product action with m > 4 log₂ C(m,t) and m > q₀; otherwise enumerate P. This is needed because HJ's order test and its exceptional recognition range would enumerate some groups outside budget.
4. **The potential** is Φ_Λ = A(Λx + Λρ + Λσ + Q_d) + Bh, with Λ = log(8d̃), d̃ = max(d, 6), and caps initialized at min(d_i, d).
5. **Counting branches.** The families below are the true branch counts, replacing HJ's N^a. Each row satisfies log(branches) + H\* ≤ drop + 2B for one absolute A ≈ 2κ/c_θ ≈ 10³:

| Class | Branches | Drop | Reason |
|---|---|---|---|
| affected: certificate and comparison families, large-symmetry | ≤ 32 q^{2κ} | ≥ AΛc_θ − 2B | s′ ≤ θs |
| unaffected: extra-type families | ≤ 12 q^{2κ} | ≥ AΛκ − 2B | σ′ ≤ σ − κ |
| product refinement, k ≥ 2 | ≤ 2^k(d̃+1)^{k−1} | ≥ A(k−1)Λ − 2B | ρ′ ≤ ρ − (k−1) |
| enumeration, option 1 | ≤ d′^{c₁ log d + c₂} | ≥ (A/3)Λ log d′ − 2B | GNS Thm 3.13 |
| enumeration, option 2, m ≤ q₀ | ≤ (q₀!)^k(d̃+1)^{k−1}, d′ ≥ 17^k | same | |
| continuation | ≤ 2q^{κ+1} | ≥ c_β log q | unchanged cap payment |
| row events | do not occur | | q ≤ d ≤ λ |

6. **Root.** At a phase root Φ_Λ = O(log(N+2)·log d̃), giving exp(O(log(N+2)·log(d+2))) after the geometric recurrence.

**(H2), the key regrouping.** HJ charge a local test with multiplicity N^a. In fact the windows of one test are pairwise disjoint, so window calls group into at most about 10 q^{2κ} disjoint-domain families (string × test × coset × type). A disjoint-domain family fits `PhaseTree.Hyp.branch_disjoint`, which only requires the child sizes to sum to at most the parent's.

## Hypotheses that turned out not to be hypotheses

Theorem R (the first form) assumed (H1), (H2) and had a log log N term. In [verify-theorem-R](../docs/verify-theorem-R.md):

* (H1), recognition of Cameron constituents, is a literature theorem once restated for GNS option 2 (GNS 3.13 and Lemma 4.4 / BLS87; a self-contained variant for m ≥ 3t is in §2.2).
* (H2) was verified against HJ L774–800, L2655–2760 and the Lean scripts.
* The log log N term vanishes by BCP Lemma 2.2 or Maróti Cor. 1.5.

## Refinements

* **Theorem R\*\*** ([w1-structure](../docs/w1-structure.md) §3): with w the alternating width and λ the classical section dimension, exp(O(log(N+2)(log w + λ + 1))). The parameters must be defined via sections ([red-team](../docs/redteam-w1-structure.md) §2.2). Conditional on (H0) and the sketch Prop 2.1. For degree-d GI this equals R\*.
* **Channels.** Per unit of log N the exponent is log w (giants) + min(log w, log log N) (top groups, alternating enumeration) + λ (Lie enumeration). Only the Lie part is an independent source of log d.
* **The exponent is tight for HJ's own algorithm.** See [Barriers](Math-Barriers.md#hj-is-tight-on-string-isomorphism).

## Residual risk

In the red-team's order: (1) (H0), especially Theorem A.9 and the extra-orbit rule (the Lean build has since machine-checked A.9 and HJ's GI theorem, modulo axioms, but not the Λ version); (2) recognition of all structural option-2 groups (trusted from BLS87 etc.); (3) no machine check of the Λ accounting. What the literature identifies as blocked is the Unaffected Stabilizers Theorem for Γ̂_d with t = O(log d) (Grohe–Neuen §4.4, citing Neuen's thesis Ex. 5.5.10); HJ's constant κ plus σ-budget claims to bypass exactly this.

## Novelty

No n^{O(log d)} bound was found in the literature checked, but the result is a short corollary of HJ with GNS 3.13 and BCP; HJ's authors or a referee may regard it as routine ([verify-theorem-R](../docs/verify-theorem-R.md) §7).
