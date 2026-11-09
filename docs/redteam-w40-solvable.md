# Referee report: w40-solvable (Luks canonizer, polynomial guarantee at degree at most 5)

Branch `w44-redteam-luks`, 2026-11-09. Adversarial referee of `docs/w40-solvable.md` against `gi/luks.py`, `gi/canon.py`, `gi/bounded.py`, `gi/group.py`, `gi/ea2.py`, `bench/adversary.py`. Scripts: `docs/redteam-w40-code/`.

## 0. Verdict

**No wrong answer and no canonicity failure was found.** No input of degree at most 5 reached `ir_canon` or `perm_canon`, and no node count grew super-polynomially.

| # | Claim | Verdict | What is wrong, if anything |
|---|---|---|---|
| 1 | Theorem A at d <= 5 | **sound** | the exponent 3.2439 is rounded the wrong way (2.1); the per-node bound g is not derived |
| 1' | Theorem A as stated, "twin blocks <= 4" with no bound on d | **gap: false as stated** | needs d fixed; 2.2 has a family with twin blocks of 3 and a position domain of 3^k points |
| 2 | Theorem B, n^O(d^2) for fixed d, no exponential path | **sound** | the citation is wrong in form: Babai-Cameron-Palfy give n^f(d); f linear is attributed to Liebeck-Shalev |
| 3 | Isomorphism invariance | **sound** | the elementary abelian test reads the number of generators, which needs an argument the code did not state (given in 3.1) |
| 3' | A node budget breaks canonicity | **confirmed** | reproduced exactly |
| 4 | Exactly two exponential paths; counters truthful | **sound** | the k^4 limit admits large enumerations with no counter set (4.2); correct, but worth knowing |
| - | "Schreier-Sims at the position domain is the true worst case" (§2.1 of the memo) | **false** | a single listed primitive group is worse: 7.8 s at n = 31, d = 5 (2.3) |

These are instance tests plus a hand reading of the proofs; nothing here is machine-checked.

## 1. Sources for the order bounds

| Bound | Source | How I read it |
|---|---|---|
| Solvable primitive of degree m: \|G\| <= m^(a+1) / 24^(1/3), a = (3 log 48 + log 24) / (3 log 9) = 2.24399... | **T. R. Wolf, Solvable and nilpotent subgroups of GL(n, q^m), Canad. J. Math. 34 (1982) no. 5, 1097-1111**, Thm 3.1(a) (completely reducible) and **Cor 3.3** (primitive) | full text (Cambridge). The corollary is exactly the statement needed. |
| The same bound | **P. P. Palfy, A polynomial bound for the orders of primitive solvable groups, J. Algebra 77 (1982) 127-137**, Thm 1 | **not read**: the publisher page did not load. Statement taken from Halasi-Maroti, arXiv:1310.5454, and Guralnick-Maroti-Pyber, arXiv:1603.00187, which agree with Wolf. |
| Primitive in the class of composition factors <= Sym(d): \|G\| <= n^f(d) | **L. Babai, P. J. Cameron, P. P. Palfy, J. Algebra 79 (1982) 161-168** | **not read**: abstract page only. Statement taken from Grohe-Neuen-Schweitzer, arXiv:1802.04659, Thm 2.5, and Burness-Shalev, arXiv:2012.12818. |
| f can be chosen linear in d | Grohe-Neuen-Schweitzer, after Thm 2.5, "cf." **Liebeck-Shalev, Simple groups, permutation groups, and probability, JAMS 12 (1999)** | Liebeck-Shalev **not read** (the AMS site refused the fetch, and I did not try to get round it). This is second-hand. |
| Closure of that class under subgroups and quotients | Luks, as Lemma 2.4 of Grohe-Neuen-Schweitzer | read there |

Corrections: the year of Wolf's paper is **1982**, as the memo says (the brief's 1984 is wrong). The "degree-4 bound" of the code is just the solvable bound: every composition factor of a group built from Sym(<=4) is cyclic of order 2 or 3, so Palfy-Wolf applies and Babai-Cameron-Palfy is not needed for Theorem A.

Checked numerically: the bound is 432.000 at k = 9, which is |AGL(2,3)|, and it is below k^4 at every prime power tested. log_7 5040 = 4.381.

## 2. Claim 1: Theorem A, line by line

**Lemma 1 (node count).** Correct, including the arithmetic of the induction: f convex with f(0) = 0, the bound 1 + f(w-1) + f(1) at intransitive nodes, and (2w-1) k^c >= 2w+1. Against the code: a transitive node has a kernel N that is intransitive (k >= 2 blocks); `_chain` recurses on orbits of strictly smaller size; recursion depth is O(log w). The memo and `seen` only remove work.

**Primitive quotient.** `_top_block_system` stacks minimal systems until the quotient has no block system, so P is primitive with k >= 2. The orbit-representative shortcut is valid: a block containing 0 is fixed setwise by the stabilizer of 0, so B(0, b^h) = B(0, b). Checked on every transitive node of 23465 runs at d <= 5: 26422 quotients, all primitive (tested for k <= 120), none above the Palfy-Wolf bound, and P solvable in all 43186 checks (degree at most 64). The largest log_k |P| seen in that run was 2.54, at k = 16, |P| = 1152.

**(a) q <= 4.** Correct. In BFS layers a twin class has a common neighbour with a neighbour outside the class. In class layers, `class_plan` puts a class in a layer only if it is determined (distinct up-sets within the class) or its twin blocks have at most 2 vertices. Two classes in one layer may share an up-set, but they have different colours, so no colour block arises; the memo's "pairwise distinct up-sets" should say "within each class".

**(b) Solvability.** Correct. For Theorem A solvability alone suffices. The memo's wording about composition factors needs the closure lemma above for subgroups; for solvable groups this is trivial.

**(c) No fallback.** Correct, given Wolf's corollary. The giant shortcut and `big` behave as stated.

**(d) The rest.** Components, 1-WL, root class, probes, closures and F_2 elimination are polynomial. No randomness reaches this path: `random` is used only in `gi/group.py:_giant_labels` (fixed seed) and `gi/refine.py`, neither called from it.

### 2.1 Gaps that do not affect polynomiality at d <= 5

* **c = 3.2439 is too small.** The true exponent is 3.243991. At k = 9, 24^(-1/3) 9^3.2439 = 431.91 < 432, so the displayed inequality is false for AGL(2,3). Lemma 1 survives (it only needs |P| <= k^c, and the factor 0.347 absorbs the difference for any feasible k), but the text should say 3.244.
* **g(m) = m^6 is asserted, not derived.** The cost of `_chain` is up to one restriction per moving orbit, so it must be charged to the children, not to the node. A listed primitive group costs |G| w, up to about w^4.25. All of this stays within a polynomial, but "about 53" is an estimate. With c = 3.244 and g = m^6 the arithmetic gives 53.2 at d = 5 and 32.7 at d = 3, as stated.

### 2.2 The bound on m: polynomial only for fixed d

Theorem A is stated for "every twin colour block at most 4" with no restriction on d. The proof gives a bound in terms of m <= 2 n^d, which is exponential when d grows. This is a real failure of the statement, not only of the proof:

`fams.twin_triples_big_upset(k)`: a binary tree with k leaves at one depth and a tail on the root, a twin triple on each leaf, and three vertices each joined to the j-th twin of every leaf. Twin blocks have size 3; maximum degree is k. The up-set {a_1, ..., a_k} has 3^k images, so the phase-1 domain has 3^k points and P is primitive solvable in product action.

| k | n | d | phase-1 domain | largest group listed | time | nauty |
|---|---|---|---|---|---|---|
| 6 | 40 | 6 | 729 | many small listings (1297 nodes) | 0.75 s | 0.0001 s |
| 8 | 46 | 8 | 6561 | order 214,990,848 on 6561 points | > 150 s | 0.0001 s |

(k = 7 with this tree: 129 positions, 1.2 s, because the tree is not complete and the group is much smaller.) With k growing the domain is 3^Θ(n) and even the position closure is exponential. No counter fires (`canon_ir = canon_luks_fallback = 0`). Twin blocks of 2 do not reproduce it: class layers split that case (16 positions at k = 8).

**Fix:** state Theorem A for fixed d (polynomial in n with exponent depending on d, as the memo's own bound already shows). The headline claim at d <= 5 is unaffected.

### 2.3 Practical worst case

§2.1 of the memo says the true worst case is Schreier-Sims at the degree of the position domain. `fams.twin_blocks_full(4, 4)` (a complete binary tree with 4 leaves, a twin 4-set on each, 4 extra vertices; degree 5, **n = 31**) gives one Luks node that lists Sym(4) wr D_4 in product action on 256 points, |P| = 2,654,208: **7.8 s** against nauty's 0.0001 s. So at degree 5 the cost can be the listing of a single primitive quotient. Polynomial, within Theorem A, but it is not the cost the memo names.

## 3. Claim 3: invariance

**3.1 Reading the code against "the group as a set".** The decisions at a node are: order <= 256, elementary abelian, orbits by least point, `top_block_system` (a function of the group and the point order), natural giant, and the limit. I found one decision that reads a generating set: `_ea_possible` compares |G| with 2^|gens|. For `PermGroup` the generators are irredundant by construction. Kernels, however, take `S[m]` of a chain as generators, and redundancy there would make an elementary abelian group follow the recursion instead of `_ea_group`; those two forms could differ (the chain orders positions per orbit of the current stabilizer).

It is safe, for a reason not recorded in the code. Each element appended to `S[m]` during Schreier-Sims is outside <S[m]> at that moment (the levels above are complete when it is sifted), so it enlarges that group, and in an elementary abelian group enlarging means doubling. Hence |S[m]| is the rank. Checked by instrumenting every node: 585 elementary abelian nodes, none missed, and 200 kernels from random generating sets. Now stated in `gi/luks.py`, with a test.

`_gens_split` also reads generators, but both paths compute the same function, as the memo says. The case analysis of `_chain` and `_transitive` (the coset argument, the tie counting, the order passed to `PermGroup`) is correct.

**3.2 Direct tests** (0 failures in every row; forms compared under random relabellings):

| test | size |
|---|---|
| Structured low-degree fuzz (19 generators, default + `bfs` + `guarantee`, vertex colours, disconnected unions, degenerate small cases), with nauty classes compared | 1920 graphs |
| Exhaustive: graph atlas up to 7 vertices, degree <= 5, all three modes | 1097 graphs |
| Exhaustive: all 2-colourings of the atlas up to 5 vertices | 1306 |
| Larger instances (cfi3, cfit, tb2-4, nst3, mpi, new families) with \|Aut\| and twisted pairs against nauty | 57 |
| Degree >= 6 (`fuzz2.py`), default and guarantee | 941 |
| C kernel against pure Python: identical forms | 500 |
| Strings under 31 structured group families (AGL, wreath, product action, diagonals, giants): orbit, generating set, lam, Aut against listing | 3745 |

Non-isomorphic pairs differ because the form is the relabelled graph; this was also checked through the nauty classes.

**3.3 Work budget.** `bench/adversary.py handoff` reproduces the memo: budget 0 gives 1 distinct form among 8 copies, 50000 gives **2**, 10^9 gives 1. The explanation (search node counts vary over an orbit and the two canonizers differ) is correct. The `WORK` budget in `gi/group.py` is set only by `gi/graph.py`, which does not call the canonizer.

## 4. Claim 4: the remaining exponential paths

**4.1 Paths and counters.** Grep and reading: `perm_canon` is called only from `_fallback`, `ir_canon` only from `_ir_layer`, and both are counted. In the d >= 6 fuzz `canon_ir` fired in 381 runs, `canon_luks_fallback` in 1 (`hub8.3`, one call, 732 search nodes), and the fallback count always equalled `canon_perm_calls`. With `guarantee=True` all of these were zero on all 941 graphs that finished. Ten further hub instances (`hub8.2`, `hub8.3`, `hub9.2`) exceeded the 25 s per-instance alarm and were not compared. At d <= 5 they were zero on every graph tested. The condition "P non-solvable implies a twin block >= 5, hence d >= 6" is correct.

**4.2 What the limit admits.** The limit is on |P| as a function of the degree of its action, so large enumerations pass with no counter set. `hubtest.py`, a hub with 9 twin children, 2 leaves each and a random matching (n = 31, d = 9): P = Sym(9) on 36 points, |P| = 362880 <= 36^4, 90721 nodes, 52 s, in default mode with both counters at 0. This agrees with the memo's c = 4.38 statement, and it is polynomial for fixed d, but a reader who takes "counters zero" to mean "fast" would be misled. `guarantee=True` costs the same there.

## 5. Claim 2: Theorem B

The code path is as claimed: `guarantee` reaches `big` and `canon_group`, so `ir_canon` and the limit are both off. Composition factors lie in Sym(d-1) by the argument of (b), with the closure lemma cited above. The time bound is arithmetic on Lemma 1 with c = O(d). The one correction is the attribution: Babai-Cameron-Palfy gives n^f(d), and n^O(d^2) needs f linear, which is due to Liebeck-Shalev as cited by Grohe-Neuen-Schweitzer (second-hand here, see section 1). Without linear f the same proof gives only n^(d f(d)).

## 6. Growth at d <= 5

New families (`docs/redteam-w40-code/fams.py`): two trees glued on their leaves (`dt2`), a tree with one Hamiltonian cycle on its leaves (`tc`), a tree with a cubic graph on the leaves (`tq`), 4-twin leaf blocks with a matching (`hub4`), Cayley graphs of solvable groups. Luks nodes:

| family | n: nodes |
|---|---|
| dt2 | 38: 7, 70: 106, 134: 670, 262: 3614 (n = 518 over 130 s) |
| tc2 | 66: 44, 130: 100, 258: 291, 514: 705 |
| tc3 | 43: 53, 124: 318, 367: 2770 |
| hub4 | 50: 88, 98: 281, 194: 1022 |

Local exponents in n, taken from the last two sizes of each row, run from about 1.3 (tc2) to 2.5 (dt2). Time grows faster, because the groups act on domains of tens of thousands of points (tc2-8: 31 s). Nothing looks super-polynomial.

## 7. Fixes

Applied:
* `gi/luks.py`: `_ea_possible` docstring now states why it is exact on kernels (comment only).
* `tests/test_luks.py`: the Palfy-Wolf constant exactly (including that 3.2439 is too small); kernels of elementary abelian groups have a basis as generators; a product-action section at degree 5; twin blocks alone do not bound the position domain.
* Suite: 2731 passed, 19 skipped with the kernel; 1962 passed, 788 skipped with `GI_NO_CKERNEL=1`.

Proposed for `docs/w40-solvable.md`, not made (the memo is the author's):
1. Theorem A: "for fixed d" (2.2), and 3.2439 -> 3.244 in §4 (2.1).
2. Theorem B: cite Babai-Cameron-Palfy for n^f(d) and Liebeck-Shalev for f linear, and Luks for closure.
3. §2.1: the worst case can be the listing of a primitive quotient (2.3).
4. "pairwise distinct up-sets" -> "within each class" in (a).

## 8. Limits of this check

Three of the primary papers (Palfy, Babai-Cameron-Palfy, Liebeck-Shalev) were not read; only Wolf's was. The polynomial bound rests on the hand proof; the tests can only fail to find counterexamples. I searched by families and fuzz, not exhaustively beyond the atlas. The graph-level fallback was reached once.

## 9. Reproduce

```sh
P=/path/to/.venv/bin/python3    # with pynauty and networkx
cd docs/redteam-w40-code
nice $P fuzz1.py 11 180                     # low-degree fuzz
nice $P fuzz2.py 2 280                      # degree >= 6
nice $P instr.py 7 300                      # every transitive node: primitive, Palfy-Wolf, solvable
nice $P instr2.py 120                       # EA test at every node; atlas
nice python3 stress_groups.py 3 240         # strings under structured groups
nice $P big1.py 1 500                       # large instances against nauty
$P diff1.py 5 500 c.txt; GI_NO_CKERNEL=1 $P diff1.py 5 500 py.txt; diff c.txt py.txt
nice python3 sweep.py "dt2:2,3,4,5,6;tc2:3,4,5,6,7;tc3:2,3,4;hub4:2,3,4" 70
nice python3 sweep.py "ttb:4,6,8;pa44:2,3,4" 200
nice $P meas.py 150                         # the slow instances against nauty
python3 hubtest.py 90                       # degree 9: default and guarantee
python3 bench/adversary.py handoff          # from the repository root
```
