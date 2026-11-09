# Canonization for maximum degree d

**Claim.** Canonical forms for graphs of maximum degree d in n^{O((log d)^c)}, with c an absolute constant (Theorem A for strings, Corollary B for graphs). Isomorphism in this time is GNS; canonization in this time
was stated open by Schweitzer–Wiebking (2019), Wiebking (2020) and as Question 9.6 of Wiebking's 2021 thesis. Unconditional in the sense that it does not use HJ.

[Home](Home.md) · Paper: [canon.tex](../paper/canon.tex), [canon.pdf](../paper/canon.pdf); [cover note](../paper/cover-note.md) · Earlier: [write-up](../docs/canonization-bounded-degree.md), [w4-gnscanon](../docs/w4-gnscanon.md) · Ledger: [section 4](Results-Ledger.md#4-canonization-does-not-depend-on-hj)

## Status

Theorem A is a proof **modulo §10 of the paper** (published GNS lemmas, canonical generating sets, deterministic subroutines (D1–D4), and Babai's STOC 2019 canonical form, whose published text is a preliminary report that sketches the proof). The running time is written out. Three internal AI reviews plus an AI referee found no mathematical error in Theorem A, B, D. **No expert has checked it**, and the next step is to send it to one. The SICOMP text of GNS and Neuen's thesis were not read.

## The idea

A canonizer for H assigns each string a form F_H(x) and the coset Λ_H(x) = {h ∈ H: x^h = F_H(x)}. In GNS exactly one step is pairwise: comparison of local certificates of x₁ and x₂, used to build a t-ary structure whose colour names are joint, so the structure built for x₁ depends on x₂.

**Lemma T (the device).** Fix a reference tuple T⃗₀ as a function of the group alone (the first t labels of the ideal domain). Let J₀ be its pointwise stabilizer. For a test tuple T⃗, choose σ ∈ H sending T⃗ to T⃗₀ and set c(y, T⃗) := F_{J₀}(y^σ). This is well defined, equivariant, and equal for two pairs iff some h moves one to the other. It is the Babai–Luks canonical-subcoset step (Lemma S) applied to a marked tuple.

* **Lemma T′** shows the colour classes equal GNS's comparison classes, the structure is strongly canonical, and the relative symmetry defect is at least the 1/4 that GNS need (in the write-up's sharper form, at least 3/4 on [k] with D as a unary colour).
* **Lemma T″** shows all colours cost at most k^t·n in recursive sizes. **No relation between t and n is needed**, so the construction works at t = Θ(log d).
* **Credit.** The device of a single canonical test set over an ordered group is in Wiebking's thesis, Lemma 5.34, used there for fullness certificates at cost |V|^{polylog|V|}. BC's right descent transports test sets the same way.
* **Why Babai's repair did not transfer.** BC's strongly canonical structure needs t ≥ 2 log₂ n (Cor. 13.3, Prop. 14.2, for Claim 12.4). GNS work at t = Θ(log d) < k/10; if d < 20 log₂ n, test sets of size 2 log₂ n do not fit.

The remaining steps of GNS canonize with the Babai–Luks toolkit: chain rule (F1, F2), descent (F3), branch families (F4), canonical change of action (R), find-symmetry (K). GNS never run the Design Lemma or Split-or-Johnson; they apply Babai's test as a black box to structures on k ≤ d points, which BC replaces.

## Corollaries and extensions

| Result | Summary | Notes |
|---|---|---|
| Corollary B | Canonical forms for maximum degree d | canonical Luks reduction written out following Babai–Luks 1983 §4.2–4.3; padded slots; machine-checked on 47 small graphs |
| Corollary D | canonical labelling relative to a Γ̂_d labelling coset | the form Wiebking imports GNS in |
| Theorem H | canonical Neuen 2020 hypergraph test, (n+m)^{O((log d)^{c′})} | correctness proof modulo; **time only a sketch**; needs a single-object loop at the setwise stabilizer of a test set, so renormalization is computed from canonical data |
| Theorem TW | treewidth k in n^{O((log k)^{c″})} | **sketch**; needs only Theorem A because `cosetHyper` is applied only to hyperedge-respecting cosets; three fixes TW-1..3 |
| H1–H4 | hypergraphs, t-CR-bounded, K_{3,h}-minor-free and genus, K_h-minor-free | H1 mod Theorem H; H2, H3 sketches; H4 conditional and sketched |

**A canonical HJ** ([w3-canon](../docs/w3-canon.md)): Theorem C gives canonical forms for Γ̂_d in exp(O(log N log d + log^c d)) *conditional on HJ, BC, BL83*, the assembly sketched. Babai's obstacle hits only HJ's ordered comparisons in the regime d ≤ N^α. HJ's row machinery (rows 14–16 of its table) has no canonical version; it does not run in this regime.

**Lemma N and Theorem E-canon** ([w3-canon](../docs/w3-canon.md) §3): canonical forms descend to normal subgroups, giving a canonical analogue of Theorem E, at the same cost.

## Gaps found along the way

* **GAP-1** (GNS Lemma 7.2): see [Corrections](Corrections.md#gns-lemma-72). It is fixed by building the next block system above 𝒞′ into the algorithm (Step 6); [§7.3](../docs/canonization-bounded-degree.md) proves the inequality.
* **GAP-2**: GNS Lemma 2.8 does not literally cover the semi-regular step. Covered by the recursion lemma REC.
* **Neuen 2020**: GAP-1 repeated verbatim; the giant-test order; Thm 4.17(G) proof error.

## Assumptions (paper §13; earlier write-up §10)

GNS Thm 2.1 (Seress toolkit), Lemma 2.4, Thm 3.13, Thms 4.3 and 4.6 including the constructions in their proofs, Obs. 4.2, Thm 5.8, Thm 5.9, Lemma 6.2, Thm 6.4 / Cor 6.5, Thm A.2, Lemma A.3, Lemma 7.1, Lemma 2.6; Babai STOC 2019 Thm 2.2 on domains of size ≤ 2k^t = d^{O(log d)} and Babai's string test; canonical generating sets; lexicographically least coset elements. See also (D1)–(D4) in the paper: all group-theoretic subroutines must be run deterministically on canonical generators, including BC.

## Practical counterpart

[gi/canon.py](../gi/canon.py) implements the canonical Luks reduction with a linear-algebra canonizer and a search for other groups. It has **no polynomial guarantee** and does not implement Theorem A. See [Software](Software.md#canonical-labeling).

## Next step

Contact an expert (Wiebking, Neuen or Schweitzer) with the [cover note](../paper/cover-note.md), after checking the SICOMP GNS text. The note is a draft and has not been sent.
