# The HJ algorithm and its running time

Hajiaghayi and JafariRaviz, *Deterministic n^{O(log n)} Graph Isomorphism Algorithm via Inherited
Decompositions* (arXiv:2611.01399, 1 Nov 2026; "HJ"). This page explains the algorithm as the project
understands it from HJ's LaTeX, its Lean development, and [moonshot-theory](../docs/moonshot-theory.md). It is a reading aid, not a
proof. Line references such as "HJ L1542" in the memos are to the LaTeX source `graph_isomorphism.tex` (arXiv v1).

[Home](Home.md) · Related: [Lean audit](Lean-Audit.md), [n^{O(log d)}](Math-Degree-d.md), [video](Reproduce.md#the-video)

Status: HJ's main theorem is [machine-checked modulo 10 axioms](Lean-Audit.md). Theorems about HJ's algorithm that this
project added (tightness, Theorem R\*) are on the [ledger](Results-Ledger.md). The paper is unrefereed.

## 1. From graphs to strings

GI of two n-vertex graphs is string isomorphism with positions the n² ordered pairs, colors the adjacency values, and
Sym(n) acting on both coordinates. So N = n². For a group G ≤ Sym(Ω) and strings x, y: Ω → Σ,
Iso_G(x, y) = {g ∈ G: x^g = y} is empty or a coset of Aut_G(x). Answers are returned as cosets (generators plus one
representative), and are combined by Luks's orbit-chain rule and coset covers.

## 2. Structure of the recursion

The state carries an *inherited hierarchy* of block systems. Each level has a ratio d_i and a cap c_i, an analysis-only bound on
the largest alternating section at that level (`Algorithm/State.lean`). Restricting to subgroups or orbits keeps the hierarchy, so
earlier progress is not lost.

Three procedures:

* **Solve** starts a *phase* on the faithful image of the group, with N = current domain size, λ = N^α and
  a threshold N^γ.
* **Continue**: at or below N^γ it calls Solve. If the group is intransitive it runs the orbit chain, largest orbit first.
  Otherwise it exposes the next primitive quotient P of degree d′ and dispatches:
  * **small quotient** (order ≤ exp(a log² d′)): enumerate cosets; children run on block-kernel orbits of size ≤ s/d′;
  * **Maróti product action** with r ≥ 2 coordinates: refine to the coordinate subgroup (index at most 2^r·r! over Alt(m)^r);
  * **single Alt(m) on k-sets**: normalize, then GiantStep. Mathieu groups are excluded by n ≥ 25 in the Maróti axiom.
* **GiantStep** handles a quotient G ↠ Alt(q).
  * **Row case** (natural labels, q > N^α): a *row normal form* with a clean complement and a zero-sum description of the kernel, finished
    by a row terminal (fresh calls on rows of size ≤ N^{1−α} plus a solvable multicoset algorithm) or a column step.
  * **Aggregation round** otherwise: for every κ-subset of labels, compute a local certificate; compare them in lockstep; aggregate
    (Babai/Helfgott cases 1/2a/2b/3, κ-ary coherent refinement, Design Lemma). Babai's Split-or-Johnson is replaced by a
    **first rectangle**: individualize one vertex, get a balanced partition or a W×R matrix realized as an inherited orbit of size ≤ θs.

### Local tests and the hereditary budget (the new idea)

Babai needs test sets of size about log n, because of the Unaffected Stabilizers Theorem (threshold k > 2 + log₂ n): an unaffected orbit
could otherwise exist. That makes n^{O(log n)} certificates per level, over O(log n) levels: exp(log³ n), Helfgott's third logarithm.

HJ use **constant-size test sets** (κ = 64). Each recursive call of a local test is either:

* on orbits of size ≤ s/κ (paid by the domain shrinking), or
* on a full orbit where the group has a visible Alt(κ) quotient with transitive kernel. The hereditary budget **σ** then drops by κ.

σ(G) is the largest total weight of a chain of such visible steps. It cannot increase under subgroup or orbit restriction, and **Theorem A.9**
bounds it: σ ≤ C·log n − B. So unaffected calls are paid once per whole path, not once per level. Only the row normal form and a
"no large giant above a transitive kernel" lemma still use a logarithmic threshold, and these are structural, not branching costs
([moonshot-theory](../docs/moonshot-theory.md) §2.8).

## 3. The running-time analysis

**Potential.** Φ = A(x² + ρx + σx + Q) + Bh, with x = log(s+2), and weight W = (s+2)^D·e^Φ.

* ρ = Σ_i (2⌊log₂ d_i⌋ − 1) ≤ 2 log₂ s (hierarchy rank).
* σ ≤ C log s (Thm A.9).
* Q = Σ_i log d_i · log max(c_i, 2) ≤ log² s (cap moment).
* h ∈ {0, 1, 2} (a row counter).

**Charging table** (each row: number of branches against potential drop):

| Step | Multiplicity | Potential drop |
|---|---|---|
| affected test / rectangle | N^a | A·c_θ·x − 2B |
| visible unaffected test | N^a | A·κ·x − 2B |
| product refinement, r ≥ 2 | N^a·2^r·r! | A(r−1)x − 2B |
| primitive enumeration, degree d | N^a·e^{a log² d} | (A/3)·x·log d − 2B |
| auxiliary-graph continuation | q^a | A·c_β·log q − 2B |
| row event | b₀ | B |

**Lemma 7.1** shows each class of children carries at most W/(8J) of the parent's weight; the node cost is at most K_N·W, where
K_N collects a quasipolynomial per-node toll and fresh calls. At a phase root Φ = O(log² N), so a phase costs exp(O(log² N)).

**Recurrence.** Fresh calls run on smaller domains (threshold N^γ, configurations on ≤ N^{2α}, rows on ≤ N^{1−α}), so
F(N) ≤ exp(C log² N)·(1 + F(⌈N^γ⌉)). Since log²(N^γ) = γ² log² N, this is a geometric series and F(N) = exp(O(log² N)), i.e. n^{O(log n)}.
The project's [dissection](../docs/moonshot-theory.md) (§2.7) shows this outer recurrence is lossless: an improvement must come from inside a phase.

**Parameters.** κ = 64, α = 2/5, γ = 9/10, θ = 3/4, β = 9/10, q₀ = 2064, a = 36000 (in the recursion; 36001 in the charging constants), J = 8,
as in `Assembly/Params.lean` of the Lean. HJ's own constraints are lower bounds (q₀ ≥ 4κ + 2 = 258, and so on), which is why other project documents quote smaller numbers;
for instance [CLAIMS.md](../video/CLAIMS.md) gives a ≥ 2453 for q₀ = 258. The constant in the exponent is non-explicit ([Lean audit](Lean-Audit.md#the-constant-c)).

## 4. Where the two logarithms live

From [moonshot-theory](../docs/moonshot-theory.md) §2. Tag in brackets is the memo's.

* **Chain length × branching.** Inside a phase each charged step pays multiplicity M with a potential drop of at least log M. The root
  potential is Θ(log² N). Rewriting HJ's crude N^a gives per-phase exponent O(log N·(log w + μ + log log N)) **[sketch]**, where w is the
  largest giant degree that can occur and μ the largest order exponent log|P|/log deg P of an enumerated section.
* **Slack:** the ρx term is slack: ρ·O(log log N) suffices **[proven given HJ]**. The bound Q ≤ log² s shrinks to log N·log w **[proven]**.
  The real multiplicity of a local test is C_κ q^{2κ}, not N^a **[sketch, later verified as (H2)]**.
* **Giant breaking** (x, σ, Q, rectangles) costs log N·log w. It would be tight only if polynomial-degree giants survive Θ(log N) rounds, the
  shape of the 1978–80 n^{O(log n)} barrier for conference graphs, Latin squares and Steiner triple systems. The memo's speculation that the σx channel is never tight was later contradicted: w18's Theorem B1 attains it on the PG(m−1,2) incidence graphs (given HJ as written, not yet red-teamed); see [Barriers](Math-Barriers.md#hj-is-tight-on-graphs-too-w18).
* **Enumeration** of Maróti-small primitive quotients is **tight for HJ**: on AGL(k,2), HJ makes ≥ 0.288·N^{1+log₂N} branches **[proven]**.
  The bound cannot be improved for HJ's *string* algorithm by analysis alone.
* **The row terminal** E_N is enumeration-type, and arises only for giants of degree above N^α.

## 5. What the implementation does differently

The Python solver follows the skeleton but simplifies: κ = 3 by default, no row/column step, no hereditary-budget bookkeeping, aggregation by WL-style
refinement of label colorings, no first rectangle. It stays exact; the running-time guarantee is not kept. See
[Software](Software.md#what-follows-the-paper-and-what-does-not).

## 6. Explainer

The video *The Third Logarithm* derives this running time on screen; its claims ledger is [video/CLAIMS.md](../video/CLAIMS.md).
