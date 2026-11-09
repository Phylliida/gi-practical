# w40-solvable: a polynomial guarantee for canonical labeling at degree at most 5

Before = commit de9606e, after = branch w40-solvable. Timings are paired: the two trees alternate in fresh processes under `nice`, one at a time, on a 64-core machine at load about 3.

**Short version.**

* The old search canonizers were breakable at degree 3 to 5. On a binary tree with a random matching on its leaves (degree 3), `perm_canon` needs 25 search nodes at n = 18 and 5445 at n = 34 (both forms of a pair), and does not finish in 60 s at n = 66. The new code takes 0.07 s there.
* `gi/luks.py` is a Luks / Babai-Luks recursion (orbits, block systems, primitive quotients enumerated). At maximum degree at most 5, and more generally when all twin blocks have size at most 4, canonical labeling is now deterministic polynomial time, with no exponential fallback (Theorem A, §4).
* For general degree, `guarantee=True` gives **n^O(d^2)** with no exponential path (Theorem B). This is weaker than Babai-Luks's n^O(d), because the code keeps its up-set position domain.
* By default, two exponential paths remain, and only with a twin block of size at least 5, hence d >= 6: `ir_canon`, and `perm_canon` above a limit on primitive sections.
* There is deliberately no work counter: a node-budget hand-off **measurably breaks canonicity** (§2.3).
* Speed on the natural families is unchanged (forms identical to the base on all 51 paired rows). Slowdowns are listed in §6; the largest is PG(2,3), 13 to 44 ms.

Nauty and Traces solve the §2 families easily (0 to 0.05 s where they were run). These inputs are hard for our old search, not for GI tools in general.

## 2. The attack

### 2.1 Growth of the old code

`bench/adversary.py` has the generators and the paired runner; `bench/canon.py` accepts the same families and checks the answers against nauty. Times are for both canonical forms of an (X, relabelled or twisted Y) pair; node counts are totals over the pair. Timeout 60 s (100 s for tb4). Twisted and "other" twins are in the JSON and behave the same.

| instance | n | deg | before (s) | perm_canon nodes | after (s) | Luks nodes |
|---|---|---|---|---|---|---|
| tb2-3 | 18 | 3 | 0.003 | 25 | 0.002 | 2 |
| tb2-4 | 34 | 3 | 0.029 | 5445 | 0.010 | 18 |
| tb2-5 | 66 | 3 | >60 | - | 0.067 | 100 |
| tb2-6 | 130 | 3 | >60 | - | 0.710 | 182 |
| tb2-7 | 258 | 3 | >60 | - | 6.260 | 810 |
| tb4-2 | 24 | 5 | 2.067 | 316801 | 0.045 | 176 |
| tb4-3 | 88 | 5 | >100 | - | 1.698 | 1532 |
| cfi3-4 | 72 | 4 | 0.016 | 90 | 0.017 | 10 |
| cfi3-6 | 108 | 4 | 0.357 | 16780 | 0.127 | 116 |
| cfi3-8 | 144 | 4 | 0.220 | 13255 | 0.123 | 91 |
| cfi3-10 | 180 | 4 | 0.702 | 31747 | 0.242 | 166 |
| cfi3-12 | 216 | 4 | 0.468 | 29881 | 0.163 | 66 |
| cfi3-16 | 288 | 4 | 1.180 | 67803 | 0.398 | 92 |
| cfi3-20 | 360 | 4 | 2.361 | 131170 | 0.516 | 108 |
| cfi3-24 | 432 | 4 | 0.927 | 47788 | 0.443 | 88 |
| cfi3-30 | 540 | 4 | 14.206 | 684658 | 1.212 | 144 |
| cfi3-40 | 720 | 4 | >60 | - | 3.187 | 184 |
| mpi4 | 254 | 9 | 0.056 | 2721 | 0.046 | 26 |
| mpi6 | 458 | 9 | 0.045 | 1266 | 0.067 | 28 |
| mpi8 | 502 | 9 | 0.098 | 3636 | 0.104 | 42 |
| mpi10 | 866 | 9 | 5.985 | 235529 | 0.612 | 64 |
| mpi12 | 910 | 9 | 0.392 | 21074 | 0.248 | 48 |
| mpi16 | 998 | 9 | 45.996 | 1483398 | 2.116 | 194 |
| nst3-8 | 180 | 9 | 0.266 | 14921 | 0.181 | 42 |
| nst3-12 | 268 | 9 | 0.264 | 11207 | 0.227 | 56 |
| nst3-16 | 356 | 9 | 2.067 | 65235 | 0.577 | 62 |
| nst3-24 | 532 | 9 | >60 | - | 3.052 | 116 |
| cfit-20 | 204 | 4 | 0.061 | 324 | 0.079 | 40 |
| cfit-40 | 404 | 4 | 0.389 | 1327 | 0.428 | 96 |
| cfit-80 | 804 | 4 | 2.374 | 4786 | 2.850 | 174 |
| cfit-160 | 1604 | 4 | 17.841 | 16085 | 21.265 | 372 |

Instance names: `tb2-k` is family `tm` (a binary tree of depth k plus a random leaf matching), `tb4-k` the 4-ary version. `nst3` and `cfit` add a hub with a twin triple to a multipede and to Z_2-CFI: the Sym(3) factor makes the group non-elementary-abelian from then on, so the linear-algebra path is lost on an otherwise easy graph.

**What breaks it.** The search branches on ties and only prunes by automorphisms. A rigid string (few automorphisms) under a large non-abelian group has many tied minimal prefixes and nothing to prune with. Trees with a matching give iterated wreath products acting on pairs of leaves. Z_3-CFI gives abelian groups that are not 2-groups, so the F_2 path does not apply. Growth is exponential where it can be seen (tb2: 25, then 5445 nodes, then over 60 s), and erratic in the base graph for cfi3 and mpi because the group that reaches `perm_canon` depends on the layering.

**`ir_canon`.** Called directly on the rigid multipede of bench/irhard.py, colored by foot pair and row (`bench/adversary.py irdirect`, on the base commit), its nodes double every few sizes: 15 nodes at k = 8, 127 at 16, 511 at 24, 1023 at 32, 2047 at 48, 4095 at 56, and at k = 64 (n = 1408) it does not finish in 90 s (over 49000 nodes). **I did not manage to produce this at graph level.** The `mpi` family was built for it, but `gi.canon` roots elsewhere and the layers split the multipede, so `mpi` attacks `perm_canon` instead.

**The new code's own growth.** Polynomial where measured: tb2 at n = 66, 130, 258 takes 0.07, 0.7 and 6.3 s, and n = 514 takes 40 s per graph (1373 nodes, phase-2 domain 32512). tb4-4 (n = 344) takes 101 s per graph (6061 nodes). The cost is Schreier-Sims at the degree of the position domain, about n^2/2 here, not the number of nodes. That is the true worst case now: a large polynomial with a Python constant, not a search.

### 2.2 Degree of the groups

`tm`, `tb4`, `cfi3` and `cfit` have degree at most 5, so Theorem A covers them. `mpi` and `nst3` have degree 9. Theorem A covers them only if their twin blocks stay at most 4, which I did not check; every run in the table used neither fallback (`canon_ir` = `canon_luks_fallback` = 0).

### 2.3 Node counts are not an orbit invariant, and a work counter is unsafe

`perm_canon`'s node count depends on the relabelling. On one Z_3-CFI graph and a relabelled copy (separate earlier runs, one graph each) it was 434796 against 68001 nodes at n = 288 and 1330091 against 102693 at n = 432. So a budget splits an orbit: some copies finish the search and others hand off. That is harmless only if the two paths compute the same function, and the least image and Luks's form differ.

`python3 bench/adversary.py handoff` runs `perm_canon` with a node budget and hands off to `luks_canon_group` on overflow, on eight relabelled copies of tb4-2 (n = 24, degree 5):

| budget | searches finished | handed off | distinct forms among 8 copies |
|---|---|---|---|
| 0 (always Luks) | 0 | 8 | 1 |
| 50000 | 4 | 4 | **2** |
| 10^9 (always search) | 8 | 0 | 1 |

So isomorphic graphs got different "canonical" forms. On cfi3-24 the two functions happen to agree, and no failure shows up there.

## 3. What replaced the search

`gi/luks.py` computes a canonical form of a string under a permutation group by Luks's recursion. It has the interface of
`perm_canon` and replaces it in `canon_group` for every layer that is not trivial, invariant or elementary abelian. For a group
G on w points and a string x, C(G, x) returns lam in G and U = Aut_G(x^lam):

1. x invariant under G: (1, G).
2. |G| <= 256: the least image, by listing G.
3. G elementary abelian: `EAAction.canon`.
4. G intransitive: the chain rule over the orbits in order of least point (C on the restriction to the first orbit, restrict the
   group to the stabilizer of the result, continue). If every generator moves only one orbit, G is the direct product of its
   restrictions, and the orbits are done independently; this is an optimization of the same computation.
5. G transitive on w >= 2 points: take the block system of `top_block_system`, whose quotient P = G/N on k blocks is primitive.
   Enumerate the cosets of N, compute C(N, x^g) for each, keep the least result, and add one automorphism per tied coset. If G itself
   is primitive this means listing it, except that Sym(w) and Alt(w) in the natural action are sorted directly.
6. If |P| > max(k^4, 5040): `perm_canon` on (G, x). This is the only way back into the old search, and solvable groups cannot get here (§4).

`ir_canon` now runs only on a phase-2 layer where H = U1 x prod Sym(blocks) with U1 fixing every position holding a block, **and** the
layer has a twin block of size at least 5. Results are memoized per (group object, string) inside one call, which only saves work.

## 4. Worst-case bounds

Notation. n = |V|, d = maximum degree, q = the largest colour block of a twin class over all layers of a rooted run, and m = the largest
position domain of a string problem in the run (counters `canon_phase1_max_degree`, `canon_phase2_max_degree`). Phase 1 positions are
A_r-images of up-sets, which have at most d labels, and phase 2 positions are pairs of labels, so m <= max(sum_{j<=d} C(n, j), C(n, 2)) <= 2 n^d for d >= 2.

**Lemma 1 (recursion size).** Suppose every primitive quotient met at a transitive node has |P| <= k^c, with c >= 1, where k is its degree. Then
a call on w points expands at most f(w) := 3 w^(c+1) - 2w nodes.

*Proof.* f is convex with f(0) = 0, so it is superadditive. Induct on w; f(1) = 1. A terminal node (cases 1-3, a listed primitive group, a giant) costs 1.
An intransitive node on w >= 3 points has moving orbits of sizes at most w - 1 with sum at most w, so it expands at most
1 + f(w - 1) + f(1) <= f(w), since f(w) - f(w - 1) >= 3(c+1)(w-1)^c - 2 >= 6(w-1) - 2 >= 2 for w >= 2. (On w = 2 points an intransitive group is trivial: case 1.)
At a transitive imprimitive node with k blocks of size b = w/k, each of the |P| <= k^c cosets expands one node for N, whose
moving orbits lie inside the blocks, so at most k f(b) below it by superadditivity. Then the total is at most
1 + k^c (1 + k f(b)) = 1 + k^c + 3 w^(c+1) - 2 k^c w, which is at most 3 w^(c+1) - 2w because (2w - 1) k^c >= 2w + 1 when k^c >= 2 and w >= 2. ∎

A node's own work is polynomial in w: invariance and orbits by the generators, `top_block_system` (Atkinson's algorithm, at most w trials per
level), one or two Schreier-Sims runs with known order (deterministic, polynomial: w^O(1), conservatively w^6), and |P| lifts and string images. Write g(w) for this bound.

**Theorem A (twin blocks at most 4; in particular d <= 5).** If every twin colour block of the rooted runs has size at most 4, then the
default `canonical_labeling` runs in deterministic polynomial time, and neither `ir_canon` nor `perm_canon` is called. With R <= 2|E| <= dn
root edges and at most n layers, the time is O(R · n · (f(m) · g(m) + poly(n, m))) with c = 3.2439.

*Proof.* (a) *q <= 4 at d <= 5.* With BFS layers a twin class has a common neighbour y in the previous layer, and y has a neighbour outside the layer
(in the layer before it, or the other root for layer 1), so the class has at most d - 1 members. With class layers, a layer is
either a union of classes with pairwise distinct up-sets (no block), or a single class with twin blocks of size at most 2 (`class_plan` returns BFS otherwise).
(b) *Solvability.* A_0 is trivial and H = rho(U1) x| prod Sym(blocks) with U1 <= A_r, and A_(r+1) <= H. By induction every A_r and H has all composition factors isomorphic to subgroups of Sym(4), so it is
solvable. Every group at a node of the recursion is a section of such a group: restrictions, kernels, stabilizers and their restrictions. So every primitive quotient P is solvable.
(c) *No fallback.* A primitive solvable group of degree k has order at most 24^(-1/3) k^3.2439 (Pálfy 1982, Wolf 1982), below k^4, so the limit is not reached, and `big` is false in `step`. Lemma 1 applies with c = 3.2439.
(d) Everything else in the run (components, 1-WL, root class, probes, closures, F_2 elimination) is polynomial. ∎

The exponent is not small. With the crude g(m) = m^6 and m <= n^5 it is about 53 at d = 5 and 33 at d = 3. It is a guarantee, not a prediction. The measured node counts are far below it (§2, §6).

**Theorem B (any d, `guarantee=True`).** The time is at most R · n · (f(m) · g(m) + poly) with c = O(d) and m <= 2n^d, which is **n^O(d^2)** for fixed d, with no exponential path.

*Proof.* With `guarantee=True`, `ir_canon` is off and there is no limit, so `perm_canon` is never called. As in (b), all groups have composition factors in Sym(d - 1), and a primitive such group of degree k has order at most k^O(d) (Babai, Cameron, Pálfy 1982). ∎

The two group-theory bounds (Pálfy-Wolf, Babai-Cameron-Pálfy) are cited from memory of the literature and not re-derived here; I checked only that the Pálfy-Wolf formula gives exactly 432 = |AGL(2,3)| at k = 9.

**This is weaker than Babai-Luks's n^O(d).** Their bound needs a position domain of size poly(n) independent of d, which the half-edge encoding of docs/canonization-bounded-degree.md §8 provides. The code keeps its up-set positions, whose domain can be as large as n^d. I did not implement the half-edge encoding: it would replace both phases of the layer step, and only for a mode that is already impractically slow.

**Default mode, any d: exactly what can still be exponential.** Two paths, and only these:

* `ir_canon`: a phase-2 layer with H = U1 x prod Sym(blocks), U1 fixing every position holding a block, and a twin block of size at least 5. This needs d >= 6.
* `perm_canon`: a transitive node with |P| > max(k^4, 5040). P is then non-solvable, so some twin block has size at least 5 and d >= 6. The natural S_8 on 8 blocks is the smallest natural example (d >= 9); other non-solvable primitive sections may exceed the limit at smaller degrees, and I do not claim they cannot.

The counters `canon_ir` and `canon_luks_fallback` say whether a run used them. When neither is used the time obeys Lemma 1 with c = 4.38: |P| <= k! for k <= 7 and |P| <= max(k^4, 5040) above, and the largest exponent is log_7 5040 = 4.38.

## 5. Why the output stays canonical, and why there is no work counter

The form must depend only on the group as a set and on the orbit of the string. Every choice in the recursion is a function of those: the order of G, its orbits in order of least point, elementary abelian or not, whether it is a natural giant, the primitive quotient and kernel of `top_block_system`. That block system is defined by the group and the order of the points: it is the stack of systems of the first b whose block B(0, b) is smallest. So different generating sets give the same form (tested).

By induction: cases 1, 2, 3 and 6 are functions of (G, orbit of x). In case 4, the first orbit's form is a function of (G^O, orbit of x|O), the elements achieving it form a left coset of its stabilizer U, so the remaining string is determined up to U, and the next step is a function of the U-orbit. In case 5, N is normal and C(N, ·) depends only on the N-orbit, so the multiset of forms over the cosets is a function of the G-orbit, and the choice of coset representative does not matter. The product shortcut of case 4 computes the same function as the chain rule, because restricting to a stabilizer in one factor leaves the other factors' restrictions unchanged.

Aut: if a is in Aut_G(F) and h_b attains F, then h_b a lies in a tied coset, so a = h_b^-1 h_t u with u in Aut_N(F). Hence Aut_G(F) is generated by Aut_N(F) and the h_b^-1 h_t, and its order is (number of tied cosets) · |Aut_N(F)|.

**The brief suggested a work counter that hands off from the fast search to the guaranteed path. That is unsafe unless the two compute the same function, and here they do not** (one is the least image, the other is defined by the recursion). A counter that stops `perm_canon` depends on where the string sits in its orbit, so two relabellings of one graph can take different branches and get different forms. §2.3 has the node counts and a run where exactly this happens. Every hand-off here is decided by a predicate of (H as a set, orbit of x) instead: |G| <= 256, elementary abelian, natural giant, |P| against the limit, and the layer's block sizes. None of them counts work, and each is on the list of §3.

## 6. Speed: paired before and after

**Natural families** (`bench/w23.py`, min of 2 rounds, kernel on; 51 rows). The canonical forms are identical to the base on all 51 rows: these families never reach a node where the two canonizers differ. Canon ratio before/after ranges from 0.94 to 1.01, total 11.99 to 12.10 s. The largest size of each family:

| instance | n | canon before | canon after | ratio |
|---|---|---|---|---|
| Q12 | 4096 | 0.598 | 0.589 | 1.01 |
| CFIx320 | 3200 | 0.439 | 0.446 | 0.99 |
| mz150 | 3000 | 0.445 | 0.456 | 0.98 |
| 3reg4000 | 4000 | 0.116 | 0.116 | 1.00 |
| 4reg4000 | 4000 | 0.135 | 0.143 | 0.94 |
| ns256 | 5632 | 1.433 | 1.441 | 0.99 |
| nsr64 | 1152 | 0.265 | 0.266 | 1.00 |
| nst64 | 768 | 1.082 | 1.086 | 1.00 |

Without the kernel (42 rows, 1 round): 0.93 to 1.07, total 22.78 to 22.93 s. Ratios within about 7% of 1 are noise at this resolution: `bounded_iso` code did not change, and its ratios span a similar or wider range.

**Canonical forms on the tiers** (`bench/families.py`, 50 instances, 25 s limit per instance, the 48 that finish in both): total 0.585 to 0.628 s, every decision correct. PG(2,5) and PG(2,7) exceed the limit in both versions (as at w23).

**`bench/run.py` tiny to xl** (graph_iso; this path did not change): 50/50 correct, 3.3 s before and 3.4 s after.

**Johnson gadgets** (the old code's largest natural `perm_canon` counts):

| instance | n | before (s) | after (s) |
|---|---|---|---|
| jgad6 | 96 | 0.349 | 0.333 |
| jgad8 | 128 | 0.545 | 0.482 |
| jgad10 | 160 | 0.728 | 0.607 |
| jgad12 | 192 | 0.989 | 0.745 |

**Slowdowns, all of them I found.**

* PG(2,3): 13 to 44 ms (3.3×), the only tier instance over 10 ms more than 7% slower.
* cfit: 1.1 to 1.3× (n = 1604: 17.8 to 21.3 s). The Luks path pays for extra chains where the old search needed few nodes; Schreier-Sims was about 95% of a profile of the new run at that size.
* mpi6: 45 to 67 ms.
* Everything else in the adversarial table is faster or within 6%.

Hypercubes keep `ir_canon` because they have twin blocks of 5 or more. Sending them through Luks instead (`guarantee=True`) costs far more: Q8 goes from 11 ms to 4.2 s, measured on an earlier version of the recursion.

## 7. Exactness and tests

* `python3 -m pytest -q tests`: **2708 passed, 19 skipped** with the kernel, **1939 passed, 788 skipped** with `GI_NO_CKERNEL=1`, both on the final code.
* New in `tests/test_luks.py` (29 tests): random groups of every kind (the form is equal on the orbit and for a different generating set of the same group, lam is in G, and Aut is checked against listing G); natural giants against listing; the strict limit; the adversarial families (forms under relabelling, non-isomorphic twins, Aut, the same decisions with `guarantee=True`); and no `ir_canon` or `perm_canon` at degree at most 5 on those families and random graphs.
* `tests/test_canon.py`: the structured-graph coverage test now includes Q6, because the `ir_canon` path needs a twin block of 5, and it also requires the Luks path to run. No assertion was removed.
* A one-off cross-check against pynauty certificates on 132 random and adversarial graphs of degree at most 5 (all pairs): no disagreement, in the old or the new code (final code).
* `bench/canon.py` on all six adversarial families (small sizes, decisions and |Aut| against sparse nauty and Traces) and on cfix, cube, mzgen, reg3 and ns: no WRONG. `bench/irhard.py audit --size 112`: lemma answers, sigma and |Aut| verified. `bench/run.py` and `bench/families.py` are unchanged.
* No C code was added, so ASan/UBSan has nothing new to check.

These tests check instances. The arguments in §4 and §5 are by hand and are not machine-checked.

## 8. What is not done

* **n^O(d) for general d** is not reached (Theorem B gives n^O(d^2)); it needs the half-edge domain.
* **No polynomial guarantee by default at d >= 6.** `ir_canon` and the `perm_canon` fallback remain there unless `guarantee=True`. The guaranteed mode is slow on graphs with large twin blocks (enumerates up to |P| cosets).
* **The polynomial is large.** The proved exponent is about 53 at d = 5, and the practical limit is Schreier-Sims on position domains of tens of thousands of points (n about 500 on trees with a matching). The next step would be working on labels with lazily computed positions, or a hypergraph-style recursion, instead of building chains at the degree of the position domain.
* Theorem A rests on the Pálfy-Wolf bound, cited and not re-derived.

## 9. Reproduce

```sh
python3 build_ckernel.py
git archive de9606e | tar -x -C /some/dir && (cd /some/dir && python3 build_ckernel.py)
nice python3 bench/adversary.py paired --base /some/dir --family tm --sizes 3,4,5,6,7 --timeout 60 --label X   # also tb4, cfi3, mpi, nst3, cfit
python3 bench/adversary.py handoff
python3 bench/adversary.py irdirect --sizes 8,16,24,32,48,56,64 --timeout 90    # run from the base tree's code to measure the old ir_canon; ir_canon itself is unchanged
nice python3 bench/w23.py run --base /some/dir --label X --rounds 2
python3 bench/canon.py run --family cfi3 --sizes 6,10,16,24 --modes canon,dns,dnt --timeout 60 --label X
python3 -m pytest -q tests && GI_NO_CKERNEL=1 python3 -m pytest -q tests
```
