# Open problems and next steps

[Home](Home.md) · Related: [Results ledger](Results-Ledger.md), [Tried and failed](Tried-and-Failed.md)

## Next steps, in order

1. **Get a human expert to look at the canonization paper** before any public claim. A draft cover note is at [paper/cover-note.md](../paper/cover-note.md), not sent. Natural readers: Wiebking, Neuen, Schweitzer, Grohe.
2. **Before writing to them, read the unread sources**: the SICOMP 2023 text of GNS, especially Lemma 7.2, and Neuen's dissertation (the unseen Lemma 6.1.17). Accessing them was blocked; see [Disclosures](Disclosures.md#literature-that-was-not-read).
3. **Ask as questions, not error claims,** about GNS Lemma 7.2 and Neuen 2020 Thm 4.17(G).
4. Decide about publishing [exponent.tex](../paper/exponent.tex). Theorem G should be regarded as provisional until a human checks it; Theorem X is the fallback.
5. Merge the running work ([Maintaining](Maintaining.md)).

## Core questions

* **Is GI FPT by maximum degree?** Downey–Fellows; GNS; Grohe–Neuen 2021 Q4; Neuen 2026 survey ("wide open", Q4.8).
* **(R1)** Coloured tanglegram isomorphism, FPT in out-degree b? Necessary for FPT degree-d GI. **R1_c** is the complete-tree version.
* **(R2)** Are all tree groups fpt-definable? If yes, TreeCI ≡ R1. If no, degree-d GI may be strictly easier than TreeCI.
* **Is TreeCI FPT?** **TreeCan versus TreeCI**: would an FPT TreeCI algorithm canonize? Open.
* **(W2 §3.5)** Entangled kernels under product-type nodes: is coordinate-tree CI reducible to TreeCI?
* **Neuen Q4.8**: is there an fpt-reduction from SI by composition width to GI by degree?
* **Height-2 posets with large μ** ([w8-poset](../docs/w8-poset.md) §5.3): the smallest open poset family, whether μ captures hardness.
* **R1 versus R1_c**: reduce general trees to complete ones, or explain why unbalanced trees are easier.
* **Lower bounds**: an adversary argument that every coset-splitting strategy needs N^{Ω(log b)} on iterated PCI_diag or twisted coordinate tanglegrams would be the first lower bound for a group-theoretic model.
* **Hardness**: no source problem believed not FPT encodes into tree groups.

## Exponent and analysis

* **X(d) ≤ 2^{O(log⁴ d)}** for isomorphism of (log d)-ary structures on d points, directly or by a finer B–H analysis. Would settle c = 3 without Theorem G ([w8-gnsexp](../docs/w8-gnsexp.md) §6).
* **c below 3** within GNS's architecture needs a stabilizer theorem tolerating small primitive levels, or constant-size tests, i.e. HJ's route.
* **Arity reduction**: do O(1) individualizations always suffice for a binary black box? Open after the [refutation](Corrections.md#arity-lower-bound-for-the-gns-black-box).
* **HJ's σ-machinery on heart-type non-Cameron giants** ([w1-structure](../docs/w1-structure.md) §4.9).
* **Theorem G** human check: the functorial reading of Split-or-Johnson; Lemma 3.1 of w12.
* **HJ tightness on graphs**: does any graph family force the N^{log d} of HJ on string isomorphism? (see in-progress [Latin squares](Moonshots.md#latin-squares-and-steiner-systems-in-progress).)
* **BC simplification** (Remark 5.2 of w4): check against a full version of BC if one exists.

## Canonization

* Write out Theorem H's running time and TW, H2–H4 ([paper §15](../paper/canon.tex)).
* Canonical row machinery of HJ, for canonical forms of all graphs in n^{O(log n)} (no invariant replacement known).
* FPT 2^{k polylog k} treewidth canonization (speculation).

## Moonshots

* Cubic Boolean equivalence in 2^{Õ(k^{1.5})}; 4-TI below 2^{o(k²)}; an "affine CFI" ([w17-affine](../docs/w17-affine.md) §8).
* Ask whether the "ETH is False" preprint survives review; then update [Moonshots](Moonshots.md).
* Latin squares and Steiner triple systems: `w18-latin` (in progress).

## Engineering

* Solvable-layer extension of `ea2`, or a polynomial `perm_canon` replacement (Theorem A or BL83 canonical Luks).
* A principled individualization rule (trial refinement per class) instead of `young_pick`.
* Compile `edge_invariants`, `canon.step` and `absorb` ([w16-ckernel](../docs/w16-ckernel.md) §6; up to 1.9×–4× estimated).
* Faster Young-subgroup bookkeeping for `ir=0` (Θ(n⁴) per node).
* Measure entanglement on real Luks towers (CFI, multipedes) to see if Theorem E is practical.
* Implement Theorem P or Theorem 1 of w8-poset as dispatcher cases.
* Add tanglegrams as a stress family.

## Paper loose ends

* [canon.tex](../paper/canon.tex): author lines and disclosure are placeholders. Update the "not independently checked" note for §10.9 after any external check; a red-team has since looked at it ([redteam-canhyp](../docs/redteam-canhyp.md)).
* Several red-team reports list recommended edits to memos that were not applied (for example the Theorem G memo, [redteam-theoremg](../docs/redteam-theoremg.md) §6).
