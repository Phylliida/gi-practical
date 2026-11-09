# Open problems and next steps

[Home](Home.md) · Related: [Results ledger](Results-Ledger.md), [Tried and failed](Tried-and-Failed.md)

## Next steps, in order

1. **Get a human expert to look at the canonization paper** before any public claim. A draft cover note is at [paper/cover-note.md](../paper/cover-note.md), not sent. Natural readers: Wiebking, Neuen, Schweitzer, Grohe.
2. **Before writing to them, read the unread sources**: the SICOMP 2023 text of GNS, especially Lemma 7.2, and Neuen's dissertation (the unseen Lemma 6.1.17). Accessing them was blocked; see [Disclosures](Disclosures.md#literature-that-was-not-read).
3. **Ask as questions, not error claims,** about GNS Lemma 7.2 and Neuen 2020 Thm 4.17(G).
4. Decide about publishing [exponent.tex](../paper/exponent.tex). Theorem G should be regarded as provisional until a human checks it; Theorem X is the fallback.
5. Fold in `w27-tree` when it lands, and red-team [w28-sigma](../docs/w28-sigma.md) ([Maintaining](Maintaining.md)).

## Core questions

* **Is GI FPT by maximum degree?** Downey–Fellows; GNS; Grohe–Neuen 2021 Q4; Neuen 2026 survey ("wide open", Q4.8).
* **(R1)** Coloured tanglegram isomorphism, FPT in out-degree b? Necessary for FPT degree-d GI. **R1_c** is the complete-tree version.
* **(R2)** Are all tree groups fpt-definable? If yes, TreeCI ≡ R1. If no, degree-d GI may be strictly easier than TreeCI.
* **Is TreeCI FPT?** **TreeCan versus TreeCI**: would an FPT TreeCI algorithm canonize? Open.
* **(W2 §3.5)** Entangled kernels under product-type nodes: is coordinate-tree CI reducible to TreeCI?
* **Neuen Q4.8**: is there an fpt-reduction from SI by composition width to GI by degree?
* **Height-2 posets with large μ** ([w8-poset](../docs/w8-poset.md) §5.3): the smallest open poset family, whether μ captures hardness. As of `1368fb6`, `w27-tree` is in progress on this and on R1_c.
* **R1 versus R1_c**: reduce general trees to complete ones, or explain why unbalanced trees are easier.
* **Lower bounds**: an adversary argument that every coset-splitting strategy needs N^{Ω(log b)} on iterated PCI_diag or twisted coordinate tanglegrams would be the first lower bound for a group-theoretic model.
* **Hardness**: no source problem believed not FPT encodes into tree groups.

## Exponent and analysis

* **X(d) ≤ 2^{O(log⁴ d)}** for isomorphism of (log d)-ary structures on d points, directly or by a finer B–H analysis. Would settle c = 3 without Theorem G ([w8-gnsexp](../docs/w8-gnsexp.md) §6).
* **c below 3** within GNS's architecture needs a stabilizer theorem tolerating small primitive levels, or constant-size tests, i.e. HJ's route.
* **Arity reduction**: do O(1) individualizations always suffice for a binary black box? Open after the [refutation](Corrections.md#arity-lower-bound-for-the-gns-black-box).
* **HJ's σ-machinery on heart-type non-Cameron giants** ([w1-structure](../docs/w1-structure.md) §4.9).
* **Theorem G** human check: the functorial reading of Split-or-Johnson; Lemma 3.1 of w12.
* **Turn w18's sketches into proofs:** the Latin-square-graph and block-graph chains (B2) and Paley graphs (B3). Theorem B1 itself has been AI red-teamed ([report](../docs/redteam-w18-latin.md)).
* **Red-team [w28-sigma](../docs/w28-sigma.md)**, and then the leads it lists: prove or refute the Uniform Prefix Conjecture (§7.3, speculation); case (b) of Theorem U; turn Q1 into a theorem; find a family that defeats LHJ + P1 + bounded WL (§12).
* **Transferring HJ's string lower bounds to graphs:** does a graph family force the N^{log d} of w1 at fixed degree? Open (w18's B1 is a different channel at unbounded degree).
* **Canonically chosen test sets** in HJ's certificate step (a w18 lead). w28 (not red-teamed) shows any Aut-invariant rule is all-or-none on X_m, so a thin canonical family does not exist there; see [Barriers](Math-Barriers.md#can-hj-avoid-the-σx-channel-w28-not-yet-red-teamed).
* **BC simplification** (Remark 5.2 of w4): check against a full version of BC if one exists.

## Canonization

* Write out Theorem H's running time and TW, H2–H4 ([paper §15](../paper/canon.tex)).
* Canonical row machinery of HJ, for canonical forms of all graphs in n^{O(log n)} (no invariant replacement known).
* FPT 2^{k polylog k} treewidth canonization (speculation).

## Moonshots

* Cubic Boolean equivalence in 2^{Õ(k^{1.5})}; 4-TI below 2^{o(k²)}; an "affine CFI" ([w17-affine](../docs/w17-affine.md) §8).
* Ask whether the "ETH is False" preprint survives review; then update [Moonshots](Moonshots.md).
* Latin squares and Steiner triple systems: rank-Ω(log n) quasigroups ('locally algebraic'?), [w18-latin](../docs/w18-latin.md) §6.

## Engineering

* Solvable-layer extension of `ea2`, or a polynomial `perm_canon` replacement (Theorem A or BL83 canonical Luks).
* A principled individualization rule (trial refinement per class) instead of `young_pick`.
* Cut the remaining Python per layer: `RootedCanon.step` (40–60% on CFI and Miyazaki), `_Rooted` construction and the root class ([w23-speed2](../docs/w23-speed2.md) §6). w23 compiled `absorb` and most other hot primitives; the "up to 1.9×–4×" estimate in [w16-ckernel](../docs/w16-ckernel.md) §6 predates it.
* A sparse representation of non-elementary-abelian groups on long graphs, the next algorithmic step ([w23-speed2](../docs/w23-speed2.md) §6).
* Fewer groups, rather than cheaper ones, for Q7 at `ir=0` ([w22-speed](../docs/w22-speed.md) §6).
* Faster Young-subgroup bookkeeping for `ir=0` (Θ(n⁴) per node).
* Measure entanglement on real Luks towers (CFI, multipedes) to see if Theorem E is practical.
* Implement Theorem P or Theorem 1 of w8-poset as dispatcher cases.
* Add tanglegrams as a stress family.

## Paper loose ends

* [canon.tex](../paper/canon.tex): author lines and disclosure are placeholders. Update the "not independently checked" note for §10.9 after any external check; a red-team has since looked at it ([redteam-canhyp](../docs/redteam-canhyp.md)).
* Several red-team reports list recommended edits to memos that were not applied (for example the Theorem G memo, [redteam-theoremg](../docs/redteam-theoremg.md) §6).
