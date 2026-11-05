# Where the implementation (and the paper's recursion) blow up

Branch `r3-hardness`. Measurements of `graph_iso` on parametrized families with exactly known
answers, in the full hybrid front end (`ir=3` plus budgeted levels, "full") and with
graph-level individualization switched off (`ir=0`, so the paper's recursion does the work),
against pynauty 2.8.8.1. All runs use `Solver(certificates=False)`, `nice -n 19`, one process
at a time, and a per-run limit of 120–300 s. The machine was shared and under varying load,
so treat times as accurate to about 1.5×. Branch counts are deterministic.

**Short answer.** No family we could build at n ≤ 300 makes the branch counts grow
superpolynomially, except through one heuristic: the choice of which label class the Young
step individualizes. On projective planes that choice makes the individualization depth grow
linearly in the order q. We prototyped a fix and it keeps the depth at 3–5. Everything else
grows polynomially, as n^3 to n^5.5 in our implementation and n^2 to n^4 in nauty. Where we are
slow, the cost is a polynomial overhead per branch, not the number of branches. The
n^O(log n) terms of the paper's analysis (enumerating Cameron-small primitive groups;
q^O(log q) label individualization) never dominate at this scale. The closest is Sylvester
Hadamard graphs with ir=0: the depth grows like 2 log2 m, but automorphism pruning keeps the
branch count at about 30.

## Families (`bench/hardness.py`)

`python bench/hardness.py list` shows all families. Every instance is either a random
relabeling (isomorphic by construction) or a non-isomorphic pair justified by a theorem or by
nauty. Every claim is checked against nauty before the run, and |Aut(X)| is taken from nauty.
Every answer of `graph_iso` is verified: the decision, the isomorphism (edges and vertex
colors), each generator, and |<gens>| (sympy) = |Aut|. Of 632 recorded rows, 415 are
verified solver runs, 19 timed out, and 0 answers were wrong.

| family | n | non-isomorphic pairs from |
|---|---|---|
| `cfi3`, `cfi4`, `cfik`, `cfigrid`: CFI over random 3-/4-regular graphs, K_m, 3×k grids | 40–288 | CFI theorem (twisted edge) |
| `multipede`, `multipede4`: colored 3-/4-XOR systems (Gurevich–Shelah multipedes, CFI gadgets); 3-XOR: linear hypergraph, rigid; 4-XOR: Aut = global flip | 88–264 | flips S with AS = r + r′ (rank test) |
| `latin_group`: Latin-square graphs of Cayley tables, orders 5–16 (11 groups of order 16) | 25–256 | Bruck (graph = main class, k ≥ 5) + Albert (isotopic groups are isomorphic) |
| `latin_random`: random Latin squares (cycle switching) | 36–196 | nauty |
| `bilinear`: class 2, exponent p (Sun's hard class) as alternating maps F_p^a × F_p^a → F_p^c, faithful projective encoding | 31–197 | nauty |
| `sts`: point-block graphs of random Steiner triple systems (Stinson) | 39–186 | nauty |
| `plane`: PG(2, q), q ≤ 9; Hall plane of order 9 (nearfield); Hall vs its dual, points and lines colored | 14–182 | nauty |
| `gq`: GQ W(q) vs Q(4, q) | 15–156 | Payne–Thas (W(q) is not self-dual for odd q) |
| `symplectic`, `paley`, `hadamard` (Sylvester, Paley I), `cayley2` (random Cayley graphs of Z_2^d) | 15–288 | nauty |

On the class-2 encoding: the vertices are the points and lines of PG(a−1, p), the points (and
lines) of PG(c−1, p), and a zero vertex. Each V-line ⟨u, v⟩ is joined to ⟨b(u, v)⟩. For a ≥ 3
and a trivial radical, color-preserving isomorphism of these graphs is exactly pseudo-isometry:
by the fundamental theorem of projective geometry on both sides, and because a map that is a
scalar multiple of b on every pair is globally a scalar multiple when rad b = 0. This uses
p^(2a−4) vertices instead of the p^(2(a+c)) of a Cayley table, but n ≤ 300 still only allows
a ≤ 4 for p = 3.

On the multipedes: with random (non-linear) 3-XOR systems, 2-WL makes the coloring discrete,
because two equations sharing two variables give a two-variable relation. Linear hypergraphs
stay 2-WL-stable. The k-XOR generalization (`multipede4`, 8-vertex gadgets) was meant to give
the individualization heuristics classes of size 8 to fire on. But 2-WL splits each gadget
into complementary pairs, since equations may share 2 of their 4 variables. So it behaves
like `multipede`.

Commands:

```sh
PY=../r2-hybrid/.venv/bin/python
nice $PY bench/hardness.py run --family plane --sizes 2,3,4,5,7,8,9 --timeout 300 --label X
$PY bench/hardness.py table --labels X           # markdown table
$PY bench/hardness.py fit --label X --metric time --floor 1e-4 [--filter REGEX]
nice $PY bench/hardness.py run ... --solver-args '{"young_pick": "large"}' --graph-pick large
```

Raw results: `bench/results/hardness/probe-*.json` (default solver) and `fix-*.json`
(prototype). In the tables, "br (a+b)" counts all branch attempts (graph-level
individualization branches plus label branches of the Young step and GiantStep), with
graph-level depth a and label depth b.

## Growth tables (default solver)

Selected rows. Full tables: `bench/hardness.py table --labels probe-<family>`.

**Projective planes** (the one family where branch counts grow quickly):

| instance | n | full s | full br (depth) | ir=0 s | ir=0 br (depth) | nauty s |
|---|---|---|---|---|---|---|
| PG(2,2) | 14 | 0.017 | 9 (2+0) | 0.015 | 6 (0+2) | 0.0001 |
| PG(2,3) | 26 | 0.078 | 28 (3+1) | 0.126 | 22 (0+4) | 0.0002 |
| PG(2,4) | 42 | 0.256 | 31 (4+1) | 0.718 | 33 (0+5) | 0.0004 |
| PG(2,5) | 62 | 0.436 | 26 (4+0) | 3.08 | 34 (0+6) | 0.0007 |
| PG(2,7) | 114 | 1.66 | 34 (4+1) | 114 | 657 (0+9) | 0.0017 |
| PG(2,8) | 146 | 13.5 | 238 (4+1) | >240 | ≥599 (0+≥11) | 0.0044 |
| PG(2,9) | 182 | 27.4 | 349 (4+2) | – | – | 0.0045 |
| Hall(9) | 182 | 146 | 1608 (4+2) | – | – | 1.01 |
| PG(2,9) vs Hall(9) (non-iso) | 182 | 19.7 | 326 (4+2) | >240 | (0+≥10) | 4.60 |
| Hall(9) vs dual, colored (non-iso) | 182 | >240 | ≥565 (0+≥13) | – | – | 0.83 |

The plane pairs of order 9 are the hardest instances for nauty in the whole study (1–4.6 s).
On PG(2,9) vs Hall(9) we are only about 4× slower than nauty.

**Rigid SRG-like structures** (no automorphisms to prune with):

| instance | n | full s | full br | ir=0 s | ir=0 br (depth) | nauty s |
|---|---|---|---|---|---|---|
| STS15 / pair | 50 | 1.07 / 0.06 | 44 / 70 | 4.7 / 4.9 | 611 / 617 (2–3) | 0.029 |
| STS21 / pair | 91 | 15.7 / 16.4 | 137 / 140 | 83 / 84 | 1969 / 1987 (2) | 0.30 |
| STS25 / pair | 125 | 39.9 / 49.3 | 164 / 200 | >150 | – | 0.83 |
| STS31 / pair | 186 | 97.5 / 117 | 259 / 310 | – | – | 2.42 |
| LatinRand8 / pair | 64 | 2.87 / 2.82 | 96 / 128 | 29 / 30 | 1411 / 1429 (2) | 0.03 / 0.02 |
| LatinRand10 / pair | 100 | 15.0 / 27.1 | 188 / 200 | >150 | – | 0.14 / 0.23 |
| LatinRand14 / pair | 196 | 118 / 160 | 290 / 392 | – | – | 0.55 |

In full mode, the graph-level individualization always has depth 1: one individualized vertex
plus 2-WL makes the coloring discrete. So the branch count is about 1.4n (isomorphic) to
1.7n (non-isomorphic).

**Constant branches, ir=0** (the per-node cost alone):

| Paley q | 29 | 61 | 101 | 149 | 197 | 257 |
|---|---|---|---|---|---|---|
| full s (br) | 0.022 (7) | 0.10 (8) | 0.29 (8) | 1.02 (7) | 1.21 (7) | 3.94 (7) |
| ir=0 s (br) | 0.12 (6) | 1.90 (7) | 13.5 (7) | 62.9 (6) | >123 | – |
| nauty s | 0.0003 | 0.0009 | 0.0021 | 0.0041 | 0.0075 | 0.022 |

**Group Latin squares** (full mode, all 11 groups of order 16 and their 10 adjacent pairs):
7–170 branches, depth ≤ 4+2, 5–27 s at n = 256 (nauty: 0.01–0.02 s). With ir=0: n = 64: 2.5–20 s
with up to 784 branch attempts on non-isomorphic pairs (depth 4); n = 81: 37–51 s; n = 121:
>300 s with only 6 branches.

**Polynomial and harmless at this scale**: multipedes (0 branches; the staged orbit chain
solves them group-theoretically; 0.4–8 s, nauty 0.001–0.01 s), CFI (5–85 branches; 3×k grids
0.6→31 s full and 0.7→156 s ir=0 for n = 80→260), the class-2 bilinear encodings (≤ 147 branches,
≤ 7 s), GQs, symplectic graphs (Sp(8,2), n = 255: 47 s, 199 branches), Cayley graphs of Z_2^d
(≤ 10 branches), Hadamard graphs (full: 0.14 → 73 s for n = 32 → 288, ≤ 142 branches).

## Growth fits and how much to trust them

Least squares of log y against four models: n^c, n^(c log2 n), 2^(cn), 2^(c√n). Here y is the
largest time among the instances of one kind (isomorphic or not) at each n. "LLO" is the error
factor when the largest n is predicted from the other sizes (`bench/hardness.py fit`).

| family, mode | sizes | best fit | R² (poly / quasi / exp) | LLO poly | local exponents |
|---|---|---|---|---|---|
| Paley, ir=0 (6–7 br) | 4 | **n^3.84** | 0.9999 / 0.998 / 0.95 | 1.08× | 3.75, 3.89, 3.95 |
| Paley, full | 6 | n^2.3 | 0.986 / 0.989 / 0.93 | 1.57× | 2.1, 2.0, 3.3, 0.6, 4.5 |
| STS, full, iso | 7 | n^3.6 | 0.983 / 0.969 / 0.89 | 1.9× | 3.8, 4.5, 4.4, 2.9, 2.4, 2.2 |
| STS, ir=0 | 4 | n^5.6 | 0.986 / 0.981 / 0.96 | 1.4× | 7.9, 4.8, 4.7 |
| STS, nauty | 7 | n^4.0 | 0.967 / 0.949 / 0.86 | 2.1× | 8.2, 4.0, 3.8, 3.2, 3.4, 2.3 |
| random Latin, full, iso | 5 | n^3.6 | 0.995 / 0.984 / 0.91 | 1.5× | 4.1, 3.7, 3.4, 2.7 |
| random Latin, nauty | 5 | n^3.6 | 0.946 / 0.918 / 0.79 | 3.0× | 5.7, 3.5, 2.0, 1.9 |
| group Latin, full, iso | 8 | n^2.7 | 0.981 / 0.990 / 0.93 | 1.6× | noisy, 1.6–5.8 |
| group Latin, ir=0, iso | 4 | n^4.8 | 0.998 / 0.9996 / 0.98 | 1.2× | 4.4, 5.5, 5.0 |
| CFI 3×k grid, full / ir=0 | 6 | n^3.4 / n^4.4 | 0.997 / 0.996 / 0.97 | 1.1× | 2.4–4.2 / 3.7–5.6 |
| Hadamard Paley I, full | 9 | n^3.0 | 0.996 / 0.996 / 0.93 | 1.03× | 1.9–6.7 |
| multipede, full / ir=0 | 5 | n^2.9 / n^2.9 | 0.98 / 0.98 / 0.98 | 1.1× | 1.2–4.4 |
| **PG(2,q), ir=0, time** | 5 | 2^(1.8√n) | 0.982 / 0.996 / 0.967 (√n: 0.997) | 4.4× (√n: 1.17×) | **3.4, 3.6, 3.7, 5.9** |
| **PG(2,q), ir=0, branches** | 5 | exp | 0.85 / 0.89 / 0.94 | 7.2× | 2.1, 0.9, 0.1, 4.9 |

How to read this:

* **Exponential growth (2^(cn)) is rejected** for every family except PG(2,q) at ir=0. It has
  the lowest R² and leave-one-out errors of 2–50×.
* **Polynomial vs n^(c log n) cannot be told apart from times on [30, 300].** log2 n only moves
  from 5 to 8.2 there, so n^(c log2 n) looks like n^(5c)…n^(8c), and the R² values differ by
  less than 0.02. The useful test is the trend of the local exponent d log T / d log n.
  n^(c log n) predicts that it rises linearly in log n (by a factor of about 1.6 over this
  range). For STS, random Latin squares and nauty it *falls* (4.5 → 2.2). For Paley at ir=0 it
  is flat (3.75 → 3.95), so that one is confidently polynomial: Θ(n^4) with constant branches.
  Our confidence is high that full mode is polynomial, about n^3.5, on rigid SRG-like inputs.
  For the ir=0 fits with 3–4 sizes it is moderate.
* **PG(2,q) at ir=0 is the only superpolynomial signature.** The local exponent rises
  (3.4 → 5.9), the depth grows linearly in q (2, 4, 5, 6, 9, ≥11), and the branch counts jump
  (34 → 657 from q = 5 to 7). With 5 points we cannot choose between 2^(c√n) and n^(c log n)
  (q ~ √n, so depth ~ q means n^(Θ(√n)) in the worst case if pruning fails). The mechanism is
  identified below, though, and a fix removes it.

## Where the time goes, and why

### 1. Projective planes: the Young step individualizes along a line (label depth Θ(q))

With ir=0, a plane's labels are its points and lines. 1-WL on the labels (`young_wl=1`, pair
colors from the root 2-WL) is strong here: once two lines have unique colors, their
intersection point gets a unique color, and once two points do, their joining line does. So
for prime q, four points in general position (a quadrangle) already generate the plane and
make the partition discrete. `young_step` instead individualizes "the smallest class of size
≥ young_min that is involved". After P1 and P2 are fixed, that class is the q − 1 remaining
points of the line P1P2. Individualizing a third collinear point refines nothing beyond its own
pencil: the stabilizer of a set of collinear points is still transitive off the line. The step
repeats down the line until the class has fewer than 5 points. The depth comes out as
2, 4, 5, 6, 9, ≥11 for q = 2, 3, 4, 5, 7, 8. In the paper's terms, these individualizations
make no progress: the cap does not shrink. The full front end hits the same path when points
and lines are colored apart (Hall(9) vs dual): no Sym factor is then non-uniform, so the merge
stage hands the whole problem to the recursion, which reaches depth 13 and runs out of time.

Graph-level individualization picks a target in the same "smallest first" way. On PG(2,8) and
PG(2,9) that leads to flags (a point, then a line through it), and 238–349 branches.

### 2. Rigid SRG-like inputs, full mode: n branches × one 2-WL each

STS and random Latin squares have trivial automorphism groups and no 2-WL information at the
root. One individualized vertex plus 2-WL makes the coloring discrete, so the search is a
single level with ~n targets (all of them on non-isomorphic pairs). Each branch costs one 2-WL
refinement of the whole graph, Θ(n^3) word operations in pure Python. Hence Θ(n^4), and n^3.6
measured. At n = 186–196 that is 0.3–0.4 s per branch. nauty does the same search with 1-WL
in C and shows the same exponent (n^3.4–4.0). The gap is a constant 40–300×, not a different
growth rate. This is not a weakness of the recursion.

### 3. ir=0: Θ(n^4) per recursion node, from group bookkeeping on n² positions

Paley graphs take 6–7 branches at every size, yet ir=0 time grows as n^3.84 (R² = 0.9999).
Profiles:

* Latin(Z9), n = 81, 7 branches, 77 s under the profiler: `PermGroup.__init__` (1806 calls)
  52.8 s, of which Schreier–Sims (`_schreier`, `_sifts_to_id`) 25 + 17 s; `RestrictionHom`
  (451 calls) 28 s. Once the Young labels split into classes of size < 5, `young_step` falls
  back to the orbit chain. The chain peels the O(#classes²) pair orbits one at a time, and each
  orbit builds a restriction and a group of degree up to n² = 6561.
* STS21 pair, full mode, n = 91, 140 branches, 12.1 s: 12.0 s in 2-WL (`wl2_single`, 142
  calls, 4 rounds each; the hashed 1-WL pre-pass does not make the coloring discrete). This
  confirms §2.
* Hall(9) vs dual, colored, n = 182 (16 744 positions), 150 s: Schreier–Sims for the Young
  subgroup preimages (`young_group`, 141 `_schreier` calls) 89 s, and `refine_labels` (pure
  Python 1-WL on 182 labels with q² pair colors, 104 calls, 0.54 s each) 56 s.

Building a Young-subgroup preimage costs Θ(n²·|base|·|gens|) even with the base and order
known, so every node of the label search pays roughly n^4. This is why ir=0 is 10–60× slower
than full mode on the same branch count. It is also why ir=0 cannot get past n ≈ 150 on
anything that branches. CFI(4reg) is the exception: ir=0 is faster than full mode there
(n = 256: 5.1 s vs 40.9 s), because the three forced graph-level levels cost more than the
recursion does.

### 4. Hall(9) in full mode: little pruning at depth 4

Aut(Hall(9)) has order 311 040, against 1.7·10^8 for PG(2,9). The forced and budgeted
graph-level levels take 1477–1608 branches (25 953 pruned), against 65 for PG(2,9). This is the
classic IR cost of a smaller automorphism group. Choosing the largest class at graph level
does not change it (157 s with the prototype). nauty also finds Hall(9) its hardest isomorphic
instance (1.0 s).

### 5. Sylvester Hadamard, ir=0: log-depth, as in the q^(log q) term

For the Sylvester matrices (elementary abelian structure), the label depth is 4, 6, ≥ 8 for
m = 8, 16, 32 (n = 32, 64, 128), that is 2 log2 m − 2. This is the generator-enumeration
pattern behind the paper's q^O(log q) aggregation cost. The branch count stays at 21–30
because |Aut| is huge (4·10^10 at m = 32), and the time is again the per-node overhead
(>300 s at n = 128). Group Latin squares show the same pattern more mildly: depth 3–4 at
k = 8, 9 (log2 k + 1).

## Relation to the paper's n^O(log n) analysis

The bound pays for two things:

1. enumerating d^O(log d) elements of Cameron-small primitive quotients;
2. q^O(1) branches per cap reduction, with O(log q) reductions, that is q^O(log q) label
   individualization. The Design Lemma and Split-or-Johnson (stopped at the first rectangle)
   guarantee that each round reduces the cap by a factor β.

In our measurements:

* (1) never matters. Over all runs, `enum_cosets` (quotients of order ≤ 500 or degree < 5)
  is called at most 463 times per run, and `enum_large_primitive` and
  `unrecognized_primitive` never occur. Graph inputs start from Sym(n), and the primitive groups the
  recursion meets are giants, Johnson or product actions, which are all recognized.
* (2) shows up structurally but does not dominate. The depth is about log q on
  elementary-abelian-like structures (Sylvester Hadamard, Latin(Z_2^r)), exactly the regime
  the bound is built for. But automorphism pruning cuts the q^depth tree to tens of branches
  on isomorphic pairs, and 2-WL refutes non-isomorphic group pairs at depth ≤ 4 (≤ 170
  branches at n = 256, full mode).
* The one superpolynomial behavior (planes) is a missing piece of (2). Our WL refinement with
  the smallest-class rule has no progress guarantee: individualizing a collinear point does not
  reduce any cap, so the depth becomes Θ(q) instead of O(log q). The paper's analysis would not
  allow such a round. This is the only place where the guarantee visibly matters. It is the
  q^depth term the bound pays for, with an unbounded depth where the paper has a logarithmic
  one.
* The rest of the gap to nauty consists of polynomial overheads: Θ(n^3) 2-WL per branch, and
  Θ(n^4) group bookkeeping per node on n² positions. They are invisible in the paper's
  analysis, and they dominate every wall-clock number here.

The genuinely hard group-isomorphism instances (Sun's class-2 exponent-p groups with matching
invariants) need |G| ≥ p^5 to p^6. That means n ≥ 59 049 as a Latin square graph, or a ≥ 6 in
the projective encoding (n ≥ 10^4). The instances that fit in n ≤ 300 (a ≤ 4) are easy:
pseudo-isometry of pencils of alternating forms on F_3^4 has few orbits, and random pairs are
separated by refinement at once.

## Prototype fix: individualize the largest class

The structure suggests choosing the individualization target by progress: a label whose
individualization splits the other classes, not a point on an already-determined line. The
cheapest proxy is to take the largest eligible class. `Solver(young_pick="large")` already
exists for the Young step. For the graph-level step, `--graph-pick large` (in
`bench/hardness.py`) wraps `gi.graph.individualize` so that it branches on the largest
non-uniform Sym factor. This is exact: any Sym factor of G gives an exhaustive split.
`gi/` is unchanged.

Selected rows: default solver (`probe-*`) vs the prototype (`fix-*`). Each cell gives the
time, then the branch attempts and depth (graph-level + label). The two campaigns ran under
different machine load. For example, STS full mode, with identical branch counts, was 1.7×
faster in the later run. So compare branch counts and depths first.

| instance | n | full: default | full: largest | ir=0: default | ir=0: largest |
|---|---|---|---|---|---|
| PG(2,5) | 62 | 0.44 s, 26 (4+0) | 0.52 s, 36 (3+1) | 3.08 s, 34 (0+6) | 2.54 s, 21 (0+4) |
| PG(2,7) | 114 | 1.66 s, 34 (4+1) | 1.67 s, 65 (4+1) | 114 s, 657 (0+9) | **26.3 s, 23 (0+4)** |
| PG(2,8) | 146 | 13.5 s, 238 (4+1) | **5.61 s, 59 (4+1)** | >240 s, ≥599 (0+≥11) | **76.1 s, 63 (0+5)** |
| PG(2,9) | 182 | 27.4 s, 349 (4+2) | **9.83 s, 67 (4+1)** | – | **174 s, 41 (0+5)** |
| PG(2,9) vs Hall(9) (non-iso) | 182 | 19.7 s, 326 (4+2) | 16.5 s, 60 (4+1) | >240 s (0+≥10) | 299 s, 847 (0+5) |
| Hall(9) | 182 | 146 s, 1608 (4+2) | 157 s, 1757 (3+1) | – | >300 s (0+5) |
| Hall(9) vs dual, colored (non-iso) | 182 | >240 s (0+≥13) | >300 s (0+5) | – | >300 s (0+5) |
| HadSyl16 | 64 | 0.91 s, 53 (4+1) | 0.93 s, 53 (4+1) | 12.4 s, 30 (0+6) | 3.19 s, 42 (0+5) |
| HadSyl32 | 128 | 7.43 s, 78 (5+1) | 5.09 s, 82 (6+1) | >302 s, ≥26 (0+≥8) | **49.9 s, 71 (0+6)** |
| Latin(Z2xZ4) vs (Z2^3) (non-iso) | 64 | 0.21 s, 14 (3+0) | 0.25 s, 7 (2+0) | 13.9 s, 784 (0+4) | 8.79 s, 462 (0+3) |
| Latin(Z9) vs (Z3^2) (non-iso) | 81 | 0.11 s, 12 (3+0) | 0.08 s, 7 (2+0) | 46.6 s, 409 (0+3) | 34.3 s, 343 (0+3) |
| W(3) vs Q(4,3) (non-iso) | 40 | 0.05 s, 33 (4+1) | 0.07 s, 14 (3+0) | 2.07 s, 135 (0+4) | 1.27 s, 89 (0+3) |
| CFI(K6)-twist (non-iso) | 156 | 3.84 s, 74 (4+1) | 2.58 s, 59 (3+1) | >300 s, ≥319 (0+5) | **107 s, 404 (0+4)** |
| CFI(K6) | 156 | 10.8 s, 73 (3+1) | 5.04 s, 59 (3+1) | 113 s, 45 (0+5) | 150 s, 34 (0+4) |
| STS21 pair (non-iso) | 91 | 16.4 s, 140 (1+0) | 9.57 s, 140 (1+0) | 83.5 s, 1987 (0+2) | 63.4 s, 3052 (0+2) |
| LatinRand8 pair (non-iso) | 64 | 2.82 s, 128 (1+0) | 2.83 s, 128 (1+0) | 29.6 s, 1429 (0+2) | 48.2 s, 2794 (0+2) |

Effect:

* **Projective planes: the label depth becomes constant.** With ir=0 it is 3, 4, 4, 4, 5, 5
  for q = 3, …, 9, against 4, 5, 6, 9, ≥11. Branches drop 28× at q = 7, and PG(2,8), PG(2,9)
  and PG(2,9) vs Hall(9) now finish. In full mode, PG(2,8) and PG(2,9) need 59–67 branches
  instead of 238–349, and run 2.4–2.8× faster.
* **Sylvester Hadamard**: the ir=0 depth becomes log2 m + 1 (4, 5, 6) instead of
  2 log2 m − 2, and HadSyl32 finishes in 50 s instead of >300 s.
* Group Latin squares with ir=0: depth 4 → 3, and 10–40% fewer attempts on non-isomorphic pairs.
  W(q): fewer branches in both modes. CFI(K6)-twist with ir=0 now finishes (107 s).
* **Costs**: on rigid random structures with ir=0, the largest class is the poorest
  individualization target. Attempts double on random Latin squares (1429 → 2794) and grow by
  10–55% on STS. Hall(9) is unchanged: its cost is graph-level pruning, not depth. The
  colored Hall-vs-dual pair still times out, now at depth 5, because of the per-node overhead
  of §3.
* **Standard benchmark** (`bench/run.py --tiers large`, 18 instances, all answers checked):
  18/18 in both configurations. Full mode is identical (3.9 s). With ir=0, the branch count
  falls on 11 of the 12 instances that change (Latin(Z8) vs Latin(Z2xZ4): 138 → 85;
  T8-vs-Chang1: 35 → 46). Total 49.5 → 48.1 s; the worst case is J(8,4), 5.1 → 8.6 s.
  Results: `bench/results/r3-{base,fix}-large{,-ir0}.json`.

"Largest first" is only a proxy. The principled rule, which is what the paper's progress
measure asks for, would choose the class whose individualization refines the most: one trial
refinement of x per eligible class, then take the finest result. We have not implemented
that. Doing so means changing `Solver.young_step` (the class choice) and `graph.staged_iso`
(the target factor). Both are local changes, and exactness does not depend on the choice.

What remains slow after the fix is the per-node overhead (§3), not the branching:

* building Young-subgroup preimages from a known BSGS instead of by Schreier–Sims on n²
  positions;
* using the hashed 1-WL of `refine.py` in `refine_labels`;
* in the orbit chain, solving all small-class pair orbits of a Young node in one step instead
  of one orbit at a time.

These would bring ir=0 to within a small factor of full mode. Compared with nauty, they are
the 10^2–10^4× gap. They are not an asymptotic issue.

## Reproduction and files

* `bench/hardness.py`: families, runner (`run`), tables (`table`), fits (`fit`).
* `bench/results/hardness/probe-*.json`: default solver; `fix-*.json`: prototype.
* `bench/results/r3-{base,fix}-large{,-ir0}.json`: standard large tier, default vs
  `young_pick="large"`.
