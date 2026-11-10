# Group isomorphism: scoping notes

Written 2026-11-09, as of master `2dbaade`, by one AI session. **This memo contains no result.** It records (1) a literature scan of the state of the art for group isomorphism in the Cayley-table model, and (2) unverified first ideas for a direct attack. Nothing in §3–§5 has been red-teamed, written out as a proof, or checked for novelty; all of it is [SPECULATION] unless marked otherwise. The context is the section [Asymptotic todos](../wiki/Open-Problems.md#asymptotic-todos-toward-a-better-algorithm) of the wiki.

Notation: G is a group of order N; for a p-group, N = p^ℓ, d = d(G) is the rank of G/Φ(G), and m = ℓ − d.

## 1. Literature scan

How each item was obtained is stated, because the levels differ.

**Read directly (PDF text extracted and read):**

* Le Gall–Rosenbaum, *On the Group and Color Isomorphism Problems*, arXiv:1609.08253, intro and §2.2.
  * §2.2: every group has at most N^{(1/2)log_p N + O(1)} composition series (p the smallest prime divisor); with Luks's polynomial-time composition-series isomorphism and Rosenbaum's bidirectional collision detection ("a deterministic square-root speedup") this solves group isomorphism in **N^{(1/4)log_p N + O(1)}, deterministically, for all groups**.
  * Theorem 1.2: group isomorphism is Turing reducible in N^{O(log log N)} time to CI∗, colour isomorphism with only cyclic and projective special linear composition factors. This is the same shape as HJ's enumeration channel.

**From abstracts or the first part of the arXiv HTML, through a fetch tool that summarises (statements not checked against the full papers):**

* Rosenbaum, arXiv:1304.3935: Theorem 1.1, deterministic N^{(1/2)log_p N + O(1)} for general groups; N^{(1/4)log_p N + O(log N/log log N)} for solvable groups.
* Sun, arXiv:2611.05920, *Faster Isomorphism for Groups of Class 2* (submitted 2026-11-04, unrefereed): p-groups of class 2, every prime p, in N^{O((log N)^{25/26} log log N)}; the same for nilpotent groups of class 2. Its introduction gives N^{(1/4+o(1))log N} as the best general bound. Obstacles it names for p = 2: the commutator tensor does not determine squaring (D₈ against Q₈), division by 2, power maps are not linear, the data lives over Z/2^τ.
* Sun, arXiv:2303.15412 (STOC 2023): class 2 and exponent p, odd p, N^{O((log N)^{5/6})}.
* Ivanyos–Mendoza–Qiao–Sun–Zhang (FOCS 2024): N^{Õ((log N)^{1/2})} for class 2 and exponent p, extended to Frattini class 2, odd p. A follow-up for 2-groups of Frattini class 2 in N^{O((log N)^{1/2})} is cited by search results and by Sun 2611.05920.
* Grochow–Qiao IV, arXiv:2306.16317 (STOC 2025): linear-length reductions; the Lazard correspondence realised in the Cayley-table model, which extends the class-2 bound to p-groups of **class c < p and exponent p**.
* Seen in listings only: arXiv:2605.26748 (solvable groups with abelian Sylow subgroups, polynomial time), arXiv:2602.15497, arXiv:2604.13953, arXiv:2609.07429, arXiv:2411.19555.

**Not found** by this scan (which is not proof of absence): any N^{o(log N)} bound for p-groups of class ≥ 3 outside "class < p, exponent p"; any bound for all p-groups below N^{(1/4)log_p N}.

## 2. The frontier, as read from §1

* General groups: N^{(1/4)log_p N + O(1)}. Only the constant has moved since generator enumeration.
* Class 2: claimed for every p (Sun, November 2026, unrefereed).
* Class c < p with exponent p: done, through Lazard.
* Open: class ≥ 3 when the class is at least p (for example 2-groups and 3-groups of class 3); exponent larger than p (Lie rings over Z/p^k); all p-groups in N^{o(log N)}; a constant below 1/4.

**Consequence for the wiki's AS1 milestones (arithmetic).** Through Miller's graph, n^{c·log₂ n} = m^{4c·log₂ m + O(1)}, so a GI algorithm beats the best general group bound on 2-groups only if c_GI < 1/16. A first ledger for HJ is expected to give c_GI of order 10⁶ (AS1, step 3). Group isomorphism will not be beaten through general GI constants; an attempt has to be direct. The wiki's milestone list was amended accordingly on 2026-11-09.

Two kinds of target:

* **T-class.** A new class in N^{o(log N)}: class 3 for p ≤ 3, or bounded Frattini class, or exponent above p.
* **T-const.** All p-groups in N^{c·log_p N} for some c < 1/4.

## 3. Candidate lemma L1: Frattini lifting [SPECULATION; novelty unchecked]

**Claim.** For p-groups G, H and a linear map φ̄: G/Φ(G) → H/Φ(H), whether φ̄ lifts to an isomorphism G → H can be decided in time poly(N), and a canonical form of the pair (G, ordered basis of G/Φ(G)) can be computed in time poly(N).

**Idea of the argument.** K = ker(Aut(G) → GL(d,p)) is a p-group and acts unipotently on the p-multiplicators along the lower exponent-p central series. For a p-group acting linearly, the orbit, stabilizer and canonical form of a subspace are polynomial time: induct along an invariant flag; the complements to M₁ in S + M₁ form an affine space on which the stabilizer acts affinely; an affine action on F_p^k is a linear action on F_p^{k+1}; vector orbits are handled by stabilizers of index at most p at each step.

**Consequence, if L1 holds.** p-group isomorphism in p^{d²}·poly(N) by enumerating GL(d,p), and in **p^{d²/2}·poly(N)** with bidirectional collision. This beats p^{ℓ²/4} when d < ℓ/√2, and always beats generator enumeration with collision, p^{dℓ/2}.

**Before any work on this:** it is close to known techniques (Schwingel's canonical forms; O'Brien's standard presentations; Eick–Leedham-Green–O'Brien; Luks's composition-series algorithm; Rosenbaum's thesis). It may be folklore or published. A literature check comes first.

Bidirectional collision, as reconstructed here (not checked against Rosenbaum's paper): for a search tree with T leaves and canonical labels on leaves, on the G side fix one top half and enumerate all its completions (√T); on the H side enumerate all top halves with one completion each (√T); an isomorphism maps the fixed top half to some top half on the H side. Deterministic, 2√T.

## 4. Reduction to a hard core [SPECULATION]

Compute the image Ā in GL(d,p) of the automorphism group of a quotient for which good algorithms exist: the Frattini-class-2 quotient G/P₂(G) (IMQSZ and successors), or the associated graded Lie algebra of the lower exponent-p central series. If |Ā| = p^{o(ℓ²)}, enumerate Ā and test each element with L1; that is N^{o(log N)}.

So the hard instances would be those whose class-2 quotient (or graded algebra) is highly symmetric, |Ā| ≥ p^{εℓ²}, which forces d = Θ(ℓ), together with a deformation on top. What remains is a **relative** orbit problem under a large linear group. This is the same "relative versus plain" obstacle as (2b) of AS2.

Unresolved here: computing Ā needs automorphism-group generators or coset descriptions from the class-2 algorithms, not only a yes/no answer; whether those algorithms give this was not checked.

## 5. Class 3 [SPECULATION]

A group of Frattini class 3 corresponds to a graded algebra L = V ⊕ W₂ ⊕ W₃ generated by V, plus a deformation class [λ] in Hom(K₂, W₃)/D, where K₂ is the space of weight-2 relators and D the derivations coming from Hom(V, W₂). In the Lie case the deformation can be absorbed into one filtered Lie algebra, with bracket [v, v′] = b₂(v, v′) + c(v, v′) for c extending λ (Jacobi holds in class 3), so the problem becomes one algebra-isomorphism problem.

Obstacles to a general statement:

* class ≥ p: no Lazard correspondence; in characteristic 2 there are quadratic operations;
* exponent > p: mixed characteristic, Z/p^k;
* the structure is of higher degree, which meets AS3's threshold: a bilinear model of size o(ℓ^{4/3}) would be needed.

**Bottom-fixing for large d (d > ℓ/2).** Enumerate the action on Φ(G), at most p^{m²}, then solve the top as isometry of tuples of forms (Ivanyos–Qiao, arXiv:1708.03495, odd p; cited from memory). This is fine for Frattini class 2 and unclear for higher class, where the problem is again relative.

## 6. Side remarks

* Equivalence of Boolean functions given by truth tables cannot reduce to Cayley-table group isomorphism in the obvious way: a group of order N is described by O(log³ N) bits. Group isomorphism is the low-information end of the Lie channel.
* Search results on exponent-3 groups: they are 2-Engel and of class at most 3, and no isomorphism algorithm specific to them turned up. For p = 3, "class c < p" is only class ≤ 2, so exponent-3 groups of class 3 are a small concrete case outside the known results.

## 7. Next steps (none started)

1. Literature check on L1 and on the p^{d²/2} bound.
2. Choose between T-class (suggested first case: 3-groups of class 3 and exponent 3, or 2-groups of class 3) and T-const.
3. Write L1 as a proof and red-team it before it is called a result.

## Sources

* https://arxiv.org/abs/1609.08253
* https://arxiv.org/abs/1304.3935
* https://arxiv.org/abs/2611.05920
* https://arxiv.org/abs/2303.15412
* https://arxiv.org/abs/2306.16317
* https://eprints.sztaki.hu/10827/
* https://arxiv.org/abs/1708.03495
* https://arxiv.org/abs/1907.00309
