# Red-team of w8-hypercanon: canonical Neuen 2020 (Theorem H) and treewidth canonization (Theorem TW)

Branch `w9-redteam-hypercanon`, 2026-11-05. Adversarial referee pass over `docs/w8-hypercanon.md`
("the memo", "H§…"). The base result (Theorem A, Corollary D of `docs/canonization-bounded-degree.md`) has
had two red-team passes with no break (`redteam-w4-gnscanon.md`, `redteam-canonization-writeup.md`). I
take it as given here, with its stated status.

**Sources.** All are untrusted data, read only, under `scratchpad/r4-sources/`.

| short | what | where | read |
|---|---|---|---|
| Neu20 | arXiv:2002.06997v2, "N…" = line of `hypergraph-gamma-d.tex` | `arxiv-2002.06997/x/` | N255–290, N974–1240 (problem, BalanceOrbits, normalize, renormalize statements), N1440–1560 (renormalize proof), N1570–1700 (virtual size, CombineWindows, orbit-by-orbit), N1700–2300 (Simplify, LC statement and algorithm), N2300–2460 (LC proof and cost), N2460–2670 (aggregation, find-structure, find-symmetry), N2670–2800 (main recursion), N3075–3135 (K_{3,h}) |
| Wie20 | arXiv:1911.11257, "W…" = line of `articles/treewidth.tex` | `w3c-wiebking-1911.11257/x/` | `treewidth.tex` in full; `hypergraph.tex` L420–470 (`canSetHyper`), L64–76; `multiCoset.tex` L1370–1390 (`canObj`); grep of all files for "arbitrar/choose/pick" |
| GNSW18 | arXiv:1803.06858v1, "G…" = line of `articles/bag_subproblem.tex` | `w8-gnsw18/x/` | `bag_subproblem.tex` in full; `bag_subproblem_iso.tex` L1–60 |
| Thesis | Wiebking, RWTH 2021 (pypdf text) | `w5rt-thesis/thesis.txt` | p. 9–10, 101–103 (canonical test set), 144–152 (Thm 6.11 proof), 241–242 (Q 9.3–9.7) |
| GNW | arXiv:2004.07671v2, "M…" = line of `gi-excluded-minor.tex` | `w8-2004.07671/x/` | M600–720, M760–870, M1880–1900, grep for choices |
| Survey26 | Neuen, Comput. Sci. Rev. 2026 | `regensburg-neuen-survey/survey.txt` | "canoni" passages, scope |
| new | arXiv API (15 queries) and abstracts by id | **new** `w9rt-search/` | parsed with `scratchpad/w9-scripts/atom.py` under `python3 -I` |

**Executed.** curl (arXiv API only), `python3 -I` XML parsing, web searches, and
`nice python3 -I docs/redteam-w8-hypercanon-check.py` (new, about 80 s, brute force on hypergraphs over 6
points, §1.5). No Lean, no solver.

---

## 0. Verdicts

| claim | verdict | one line |
|---|---|---|
| Theorem H, canonicity of the single-object loop (Lemmas E1–E3, T^set, W, B, SIMP, LC) | **sound** | Every auxiliary construction is a function of the canonical prefix. I read Renormalize's proof: strings enter only through 𝔛* (N1521–1525). Two counterexample attempts fail. The toy check confirms E2/E3/T^set and catches both "non-canonical renormalization" mutants. |
| "Only the symmetry defect matters" | **confirmed** | Neuen uses the comparison classes only to build 𝔄_i (N2583–2597). Find-structure uses only invariance and the defect bound (N2610–2630). |
| Lemma AGG | **sound** | The defect bound is in fact ≥ 3/4, stronger than stated. |
| Theorem H, running time | **plausible sketch** | Canonization adds no branch type that Neuen's test lacks, and the branch counts are the same or smaller. One imprecision: the descent in LC step (d) (H-a). |
| H§2.8 remarks on Neu20 | **confirmed** | GAP-1 is verbatim at N2716. The giant-test order (N2222 before N2224, kernel of the pre-balancing Λ at N2442) is a real but minor slip in the cost proof. |
| Correction of write-up §9.2: `cosetHyper` is applied only to hyperedge-respecting cosets | **confirmed** | Its only use is W336, right after `isoBasicClique` (W332). The hypothesis is stated at W258–259. |
| GNSW18 v1 Lemma 23, second case | **says what is claimed, with one more hypothesis** | It needs Δ to preserve 𝒮 **and** χ (G82–84). The memo's pipeline gets only 𝒮 (gap TW-1). |
| Theorem TW | **sound at sketch level, three fixable gaps** | TW-1: χ-refinement step missing. TW-2: the parent adhesion set is never marked. TW-3: the doubling-search checks do not certify the clique-cover bound (needs degeneracy, not min-degree). No other isomorphism-only step in Wie20 was missed. |
| H1 | **sound mod Theorem H** | Hypotheses match GNW Thm M648–656. |
| H2, H3 | **sketches; hypotheses right** | N3084 allows any three vertices. Parameter-free running time needs an invariant doubling search (§4). |
| H4 | **label right; "would answer Q 9.7" needs two additions** | (i) A parameter-free form ("either a K_h minor or a canonical form", then doubling h). (ii) The prior canonization results for excluded minors, which the memo does not cite: Grohe (LICS 2010 / book 2017), polynomial for each fixed H; Lokshtanov–Pilipczuk–Pilipczuk–Saurabh (STOC 2022, arXiv:2210.14638), f(H)·n^{O(1)}. |
| Novelty | **H, TW: confirmed none found. H4: context missing.** | No n^{polylog} canonization for Γ̂_d-hypergraphs, treewidth or minors in print through 2026-11. Survey26 says canonization "is possible for many of the algorithms discussed", so the results are expected. |

**Overall: no break.** Theorem H stands as stated: correctness proven modulo Neu20's constructions, time
a sketch. Theorem TW stands at sketch level after three small repairs (§3).

---

## 1. Theorem H: is the single-object loop canonical?

### 1.1 What I checked

* Lemmas E1–E3 (H§1.2) line by line, with right actions. E2's well-definedness, πr·C₂(Z^{πr}) =
  πr·r⁻¹C₂(Z^π), and its equivariance under h ∈ H, using π′ = h⁻¹π, are both correct. E3 is Lemma R
  with a prefix-dependent auxiliary map. Correct.
* Lemma T^set (a)–(d). (a) uses σ′ = σg with g ∈ H₀ and E1. (b) uses h⁻¹σ. (c) holds because for fixed T
  the set E(Z, T), and hence e, does not depend on the ordering, so the t! orderings of T map onto all
  orderings of T₀. Correct.
* Lemma LC. (L1)–(L3) and (I1)–(I4) were checked against Neu20 Thm N2175, Alg. N2201–2258 and its proof.
  * (L2) is a tautology of the stopping tests. By E1, ψ(Aut_{H₀}(Z^σ)) is then conjugate to a subgroup
    of ψ(R), so "routine-nonfull" coincides with Neuen's "not full". Likewise "routine-full" coincides
    with "full", by (L3).
  * (L3) uses GNS Thm V.3 on Λ_i. This needs Λ_i to be d-normalized, i.e. (I1). Subgroups inherit
    almost-d-arity, since subgroups of semi-regular groups are semi-regular. It also uses Lemma
    `extending-window-automorphisms` (N1732–1756; I re-read the proof) and (I3).
  * Independence of π holds because (Λ_i)_{(Ω_i∖W_i)} ⊴ Λ_i, as W_i is Λ_i-invariant.
* Lemma SIMP against Thm `simplify-on-window` (N1935–2112) and Thm `renormalize` (N1202–1554), §1.2.
* Lemma W against Lemma `combine-windows` (N1624–1690). The memo's disjointness assumption on W₁, W₂ holds
  in its only use (W′ = Aff ∖ W_i).
* Lemma B against Lemma N1045 (BalanceOrbits).

### 1.2 Is renormalization really computed from canonical data?

This was the main worry. Neuen says renormalization "is not isomorphism-invariant" (N1930) and
synchronizes all pairs (N270–275).

* **Renormalize (N1455–1554).** The construction uses Γ, 𝔓 and the 𝔅-sequence: structure graphs per
  block and per orbit, combination along block systems, the choice of v_P (N1497–1499), the unfolding,
  f and f′. **The strings enter only in the definition of 𝔛\*, 𝔜\* (N1521–1525).** So the memo's claim
  (H§2.4 step 4) is correct. The "not isomorphism-invariant" remark means that the construction is not
  equivariant under relabelling of the domain. That is irrelevant once all objects with a given prefix
  share the same group on the same ordered domain, which is exactly what E2 provides.
* **Copy blocks (N1974–2003).** Ω′ = ⋃_P P × {x[W ∩ P] : (P, x) ∈ 𝔛}, 𝔓′, ψ′ and the lifted sequence
  (N2031–2040) depend on 𝔛 only through the window part 𝔛[W]. In CanLC that window part is F_i, the
  canonical window part, which is constant on C_i(Z) and on the H₀-orbit. ✓
* **Simplify's representative group Γ″₁ (N2053–2061).** Neuen computes the stabilizer cosets of the
  multiplicity strings x_i for every pair and fixes Γ″ := Γ″₁. The memo replaces this by the right group
  A″ of a Theorem A canonizer of x(𝔛′) for the single transported object. A″ is the stabilizer of the
  *canonical* multiplicity string, so it is a function of the new prefix. Claim `respect-block-sizes`
  (N2069–2074) holds for any group preserving that string, which is all that the virtual-size estimate
  (proof of (F)/(G), N2115–2141) uses. ✓
* **Injectivity and equivariance of 𝔛 ↦ 𝔛′ ↦ 𝔛′\*** (needed for E3).
  * Copying: x′ determines x. ✓
  * Renormalize: (VIII) for all pairs implies that f′ is onto (completely occupied instances).
    Equivariance follows from (II), (III) and the invariance of 𝔓\*. ✓
* **Structure graphs at the first normalization** (N935: γ_{1→i}; Neu19 Lemma 6.1.17). These are
  group-only, so P1 applies, **provided** the construction runs deterministically on canonical generating
  sets. See H-c below.

### 1.3 Order of operations

* Every order in CanLC is fixed by the ordered domain:
  * orbits in Lemma B: (size, least point);
  * Λ′-orbits in step (d): P1;
  * N′-orbits: P1;
  * Lemma W joins: in the order in which the windows were processed.
* Different loops, one per t-set T, are independent. Aggregation uses only the multiset of their outputs
  through equivariant constructions (fullness group, support S, colours). No result depends on the order
  in which the loops run. ✓

### 1.4 Are the colours read off T₀ well defined?

Yes, by Lemma T^set(a). The colour (R(Z^σ), ψ(R)-orbit of T⃗^{φ(e)}) does not depend on σ ∈ {σ : T^{φ(σ)} =
T₀} or on e ∈ E(Z, T). Comparing colours needs a canonical encoding of R. The memo uses canonical
generating sets on the ordered domain Ω, which is fine. The toy check (below) also tests independence
of σ directly.

### 1.5 Counterexample attempts

I tried to make two isomorphic inputs give different outputs. The only way in is an auxiliary choice
that sees non-canonical data. I tested this on a toy model, `docs/redteam-w8-hypercanon-check.py`.

* **Setting.** Ω = [6], H = S₆, φ = id, T₀ = {0, 1}, H₀ = Stab(T₀) (48 elements). Objects are random
  hypergraphs.
* **Two-stage canonizer.**
  * Stage 1 canonizes the window part on W = T₀ under H₀.
  * Stage 2 lifts the object to a 12-point auxiliary domain (copies of the window, as in Simplify). It
    relabels that domain by a **pseudo-random permutation** seeded from data (standing in for
    Renormalize's arbitrary choices), canonizes there under the image of the stage-1 right group, and
    pulls back.
* **Results.**

| variant | seed of the arbitrary relabelling | ECM / equivariance failures (60 objects × 12 g ∈ H₀) |
|---|---|---|
| memo (prefix) | the canonical window part F | **0** (and 0 π-dependence, 0 non-cosets) |
| mutant "raw" | the untransported object Z | 60 / 60 |
| mutant "first π" | Z^π for the first π ∈ C₁(Z) | 60 / 60 |

* **Lemma T^set**, on 25 objects × 15 test sets × 2 orderings, with σ chosen two ways and h ∈ S₆ random:
  * (a) failures 0, (b) failures 0, (c) failures 0;
  * E1 failures 0;
  * 22 test sets had equal colours for both orderings, and each had ψ(R) = Sym(T₀).

The second mutant matters. Choices must be a function of the **prefix**, not of "the transported object".
The transported object Z^π still depends on π inside C(Z), because R moves the part outside the window.
The memo's Lemma SIMP uses only (A, F, 𝔅) and the canonical multiplicity string, so it is on the right
side of this line. This is a toy model, not a proof, but it exercises exactly the bookkeeping that
replaces Neuen's synchronization.

### 1.6 Comparison classes vs symmetry defect

* Neuen's case |S_i| < k/4 (N2583–2597) builds 𝔄_i from the classes of the category on D′₁ ⊔ D′₂.
* Its only downstream uses:
  * Lemma `find-structure` (N2603–2630) uses (i) the set equation {𝔄_{1,j}}^{φ(γ)} = {𝔄_{2,j}} for
    isomorphisms γ, and (ii) "the symmetry defect of Λ_j^φ is at least 1/4" (N2628), via Cor. N2483.
  * Nothing uses that equal colours mean "isomorphic local certificates".
* The memo's 𝔄(𝔛) = ([k]; D; rank of c(𝔛, T⃗)) is strongly canonical by T^set(b). Its defect argument is
  correct:
  * Alt(M) ≤ Aut(𝔄) with |M| ≥ 3 is transitive on M and preserves D, so M ⊆ D or M ∩ D = ∅.
  * If M ⊆ D and |M| ≥ t + 2, every ordering of a t-set T ⊆ M is realized inside Alt(M), so all
    orderings of T have one colour. T^set(c) then gives ψ(R) = Sym(T₀), contradicting non-fullness.
* So every symmetrical set lies in S or has ≤ t + 1 points. The relative defect is ≥ 1 −
  max(1/4, 1/10 + 1/k) = 3/4 for k ≥ 7, which is stronger than the memo's "≥ 1/4".
* **Exactness of the colour classes is not used anywhere. Confirmed.**

### 1.7 Defects found (none breaks the theorem)

* **H-a (step (d), descent group).** "Descent (F3) to N′ := ker(ψτ_i|_{Λ′})" is right for the first
  Λ′-orbit of W′. For later orbits, processed by the chain rule, the current group is a right group
  R ≤ Λ′. The descent must then be to R ∩ N′, which has index ≤ t! in R.
  * The cost argument survives. Orbits of R ∩ N′ lie inside N′-orbits, which have size ≤ |O|/t by Babai
    Thm 6(b) applied to Λ′ (giant after test (c)). The halving uses balance of 𝔛[O] for the Λ′-orbit O
    (Obs. N1589 holds for every subset of O).
  * Fix: state it this way.
* **H-b (coset input).** For a coset σΓ the partition that must be Γ-invariant is 𝔓^σ, after the coset
  rule Λ_{σΓ}(𝔛) = σΛ_Γ(𝔛^σ). This is a notational fix and irrelevant for hypergraphs, where 𝔓 is
  trivial.
* **H-c (P1 hygiene).** Correctness needs every group-only construction to be a deterministic function of
  (group, ordered domain) computed from canonical generating sets. The constructions are:
  * Neu19 Lemma 6.1.17 and the structure-graph combination (γ_{1→i}, N935);
  * v_P (N1497);
  * the minimal block system (N2683);
  * Babai 3.2.1 / Lemma N2664, including the labelling of [k];
  * the structure-graph unfolding order of Ω\*.
  This is the documentation gap that `redteam-canonization-writeup.md` §10 already found for the base
  write-up. Add the same sentence to H§2.2 row 2.
* **H-d (statement).** Lemma AGG's defect bound can be stated as ≥ 3/4 (§1.6). Harmless.

**Verdict on correctness:** sound. The label "[PROVEN mod Neu20's constructions, GNS V.3, Babai 6(b),
CFSG facts, Theorem A, BC]" is fair for the canonicity layer. The main-theorem induction (H§2.7) is short
but each case is a composition of already-checked canonizers (Lemma K, F3, F4 and S are object-agnostic,
so they apply to sets of strings verbatim).

---

## 2. Theorem H: running time

* **Extra branches?** I listed every point where the canonical algorithm branches or descends:
  * descent to G′ (≤ d cosets);
  * Luks steps (≤ k! for k ≤ 10t; semi-regular b cosets);
  * t! cosets of N′ in LC;
  * ≤ k⁶ individualizations in aggregation (F_i, R_{i,j}, one vertex);
  * ≤ k⁶ structures in Option 1;
  * 2 cosets in Option 2 (Lemma K).

  Each occurs in Neuen's isomorphism test with the same count. LC runs binom(k, t) single-object loops
  instead of 4k^{2t} pair loops, so the canonical version is cheaper there. Colours cost t! orderings per
  t-set, which is negligible. **No new branch type.**
* **Substitutions.**
  * GNS calls become Theorem A calls on domains of size ≤ s ≤ (n+m)^{O(log d)}. Theorem A's time is then
    (n+m)^{O((log d)^{c+1})}, absorbed into c.
  * Babai's test on t-ary structures over ≤ k points becomes BC, k^{O(t^c (log k)^c)} = exp(polylog d).
* **Chain rule vs. Neuen's orbit-by-orbit.** Neuen's orbit-by-orbit is sequential too (N1677–1686): each
  orbit is solved inside the previous coset, then the results are combined by CombineWindows. So the
  canonical chain has the same recursion. The potential argument N2710–2725 only needs upper bounds on
  |Λ[𝒞′]|, which subgroups preserve.
* **H§2.8(2) confirmed.**
  * In Alg. N2221–2224 the recursive call (line `recursive-call`, N2222) precedes the giant test (N2224).
  * The cost proof takes N ⊴ Λ as the kernel in the pre-balancing group (N2442). It then uses orbits of
    the partition at N2438 together with balance, which holds only for post-balancing orbits.
  * When ψ(Λ′) is not a giant, the halving is unjustified as written. The memo's reorder (test right
    after balancing) fixes it, and correctness is unaffected.
* **GAP-1** is inherited verbatim (N2716 = GNS L2126). The write-up's fix applies (𝒞′ ⪰ 𝔅 ⪰ 𝔅₁; |𝒞′| ≤ d).

**Verdict:** a plausible sketch. I would sign "(n+m)^{O((log d)^c)}, modulo a written transfer of
Lemma N2671 and Lemma `recursion-bound` (N608) to the canonical recursion", not more. This is the memo's
own label.

---

## 3. Theorem TW

### 3.1 Is `cosetHyper` applied only to hyperedge-respecting cosets? Yes.

* A grep of all Wie20 sources finds exactly one call, W336: "Compute Δφ := iso(V(G₁), H₁, J₁, α₁; …) ∩ Δφ
  using `lem:cosetHyper`".
* The Δφ there was set at W332 to iso(Y₁, H₁; Y₂, H₂) by `isoBasicClique`, which maps H₁ onto H₂.
* The lemma's hypothesis (W258–259) is "a coset that maps the hyperedges in H₁ to hyperedges in H₂".
* Its cost is polylog in cw Δ, and that bound holds only after individualizing one point (W338).
* So the correction of write-up §9.2 item 2 is right. The Neu20-type statement is not needed for
  treewidth.

### 3.2 GNSW18 v1 Lemma 23

* `theo:big` (G57–63): canonical labelling of a hypergraph with coset-labelled hyperedges relative to τΔ,
  in time (|V||𝒮|)^{O(max(cw Δ, cw 𝓕))}.
* **First case** (G71–80): if Δ does not preserve 𝒮 **and χ**, canonize the coloured hypergraph with
  Miller's n^{O(cw)} algorithm. This is the step that would need Theorem H.
* **Second case** (G82–114): Δ preserves 𝒮 and χ.
  * Build Λ̂ on V ∪ U with cw ≤ max(cw Δ, cw 𝒮) (G108–109).
  * Canonize the incidence graph Y relative to Λ̂ and restrict to V.
  * (CL1)–(CL3) are proved at G116–180. I re-derived that Λ̂ is a coset: the block of T moves to the block
    of T^g with inner permutation in Θ_T. This uses Θ_{T^g} = Θ_T, i.e. that χ is preserved.
* With Corollary D in place of GNSW18's Luks-type canonizer, the second case gives
  (|V| + Σ|S|)^{polylog max(d, d′)}. Lemma CH is correct **as stated** (it assumes Δ preserves χ).

### 3.3 Gaps in the canonical rewrite (H§3.4)

* **TW-1 (χ not preserved).**
  * In H§3.4(c), distinct case: Λ₁ := (b) on (Y, H), then Λ₂ := Lemma CH relative to Λ₁.
  * (b)'s output group preserves H (verified: identification forces φ|_{α(v)} into the canonical coset of
    H_v → H_{φ(v)}, and every hyperedge lies in some α(v)). It does **not** preserve the child colours χ.
  * Wie20 never needed χ: in the distinct case the label image ρ₁(S_{t\*}) encodes the class, because
    adhesion sets are distinct. The memo's compressed labels Θ_tτ_t lose that information, so χ is
    necessary, and Lemma CH's hypothesis fails as written.
  * **Fix:** between Λ₁ and Λ₂, canonize the string χ : H → ℕ under the induced action of Λ₁'s group on H.
    This is Theorem A through a homomorphism (H§1.1; Γ̂ is closed under quotients). Alternatively, colour
    the hyperedges inside the `canHyper` calls of (b). This is GNSW18's own first case restricted to χ.
* **TW-2 (parent adhesion set).**
  * The instance X̂ = (Ĝ, T, β, r, S) carries the parent adhesion set S, and isomorphisms must map S to S.
  * Neither Wie20's `isoTree` body (W283–358) nor H§3.4(c) uses S. In Wie20 this is harmless only because
    the children's cosets are compared by restriction.
  * For canonization, the root-bag object must contain S, otherwise CL3 fails at the parent.
  * **Fix:**
    * distinct case: add S as a hyperedge with a reserved colour (S is a clique in G^k, so the clique
      cover covers it, and by property (3) it differs from the children's sets);
    * equal case: S equals every child's adhesion set;
    * global root: no S.
* **TW-3 (doubling-search checks).**
  * H§3.4(c) accepts k when (i) equal-adhesion bags have ≤ k+1 vertices, (ii) every basic bag has
    min-degree ≤ k, and (iii) adhesion sets have ≤ k+1 vertices.
  * The time analysis also needs |α(v)| ≤ k+1 for the clique cover of `isoBasicClique` (W197–203).
    Wie20 derives this from "mindeg ≤ tw" applied to every peeled subgraph, i.e. from **degeneracy** ≤ tw.
  * It is needed twice: for `canHyper` on α(v) (W218), and for the kernel orbits of the wreath product
    (W241).
  * When k < tw(G), tw(G^k) can be far above tw(G). For example, in a large grid with k = 3, interior
    vertices joined by 4 disjoint paths become adjacent in G^k. So
    check (ii) does not imply the bound. I did not construct a bag that passes (i)–(iii) and fails it,
    and the argument does not exclude one.
  * **Fix:** replace (ii) by "every basic bag of G^k has degeneracy ≤ k". It is invariant, polynomial, and
    holds for all k ≥ tw(G), since degeneracy ≤ tw(G^k[D]) ≤ tw(G^k) = tw(G) (Lemma W53(3)).
  * sep ≤ k needs no check: sep(G^k[D]) ≤ sep(G^k) ≤ k for every k, because local connectivity is
    monotone under induced subgraphs. The accepted k is then ≤ 2·tw(G), as claimed.
* **TW-4 (nits).**
  * Lemma CH writes Λ = ρΔ with "Δ preserves 𝒮 ⊆ 2^V". In the ρΔ form Δ acts on labels, so this should be
    𝒮^ρ.
  * H§3.3 bounds cw via "individualize one vertex (W338)", H§3.4 via the branch S. Either gives n
    branches; pick one.
  * The overall label of Theorem TW should be [SKETCH, mod Theorem A], since its proof is the sketched
    rewrite.

### 3.4 The other rewrites

* **`isoBasic` (a).** I checked CL3 for the branch-S chain. Each Λ̂ orders S before the copies, so its
  group stabilizes S. Passing to the quotient S′ keeps the stabilizer of "classes meeting S". So the final
  group is Aut(G) ∩ Stab(S) = Aut(G, S), and F4 over the invariant family 𝒮 gives Aut(G). ✓
  * The S_{v,w}-size relation is directed (leftmost separators depend on the order). It is a string on
    S², which Corollary D covers.
* **`isoBasicClique` (b).** Covered by TW-1. Otherwise ✓. Composition width stays ≤ k inside the branch,
  because Λ₁'s group is a subgroup of the isoBasic group.
* **Equal adhesion sets.**
  * `canObj` (`multiCoset.tex` L1387): n^{polylog|V|} with |V| = |bag| ≤ k+1. ✓
  * The memo is right that Thesis Thm 6.11's |D|^{O(cw)} route costs 2^{O(k log k)} there.
  * The extension to the subtrees in this case (bundling identical (colour, Θτ) children, wreath with
    Sym) is not spelled out in H§3.4(c). Thesis Thm 6.11's equal-adhesion cases (p. 148–151) give it.
* **Distinct case extension.** Thesis Thm 6.11, "P is the partition into singletons" (p. 151–152). It
  accepts any canonical coset Γ on D whose group respects the labelled hyperedges. With TW-1 and TW-2
  fixed, Λ₃ is such a Γ. ✓
* **Root.** The centre of the clique-separator tree is invariant. A subdivided central edge gives a bag
  that is a clique in G^k (clique-separator-free) with two equal adhesion sets of size ≤ k+1 (check iii).
  ✓
* **Missed steps?** Grep of `treewidth.tex` for choices finds:
  * W122 (some bijection φ);
  * W293–297 (ρ₁, t\*);
  * W355 (arbitrary extension of generators);
  * W271 (Amir's approximation).

  All four are treated in the memo's table H§3.2. The arbitrary choices inside `multiCoset.tex`
  (L1144–1329) belong to Wiebking's canonical `canSet` and are justified there. **None missed.**

### 3.5 Verdict

**Theorem TW holds at sketch level, conditional on Theorem A (via Corollary D), after TW-1 to TW-3.** All
three repairs are routine. The key observation (Wie20 needs only canonical GNS) is correct and is the
memo's real contribution here.

---

## 4. Corollaries

* **H1** (GNW Thm M648–656, defined at M618–640). The labels are labelling cosets of the hyperedge itself
  (ρΘ with Θ ≤ S_{|E|}) plus a colour, and isomorphisms require equal (c, Θ). So the refinement to (c, Θ)
  is invariant and gives Θ_S = Θ_{S′} on colour classes, as Lemma CH needs. Theorem H then makes Δ
  preserve ℰ and χ, and Lemma CH applies with d′ ≤ d. **Sound mod Theorem H.**
* **H2.** A sketch. The ingredients are right: Neuen's refinement steps are GNS quotient isomorphisms
  and Neu20 set-of-strings isomorphisms. The closure output must be an equivariant Γ̂_t labelling coset
  containing Aut[D], which is a weak canonical labelling, not a canonical one. The memo says this.
* **H3.**
  * N3084 holds for **any** three vertices of a 3-connected graph in 𝒞_h, so branching over all ordered
    triples (F4) is legitimate.
  * The 2/3-connected canonical combination is standard but needs arc-coloured components. Neuen's
    corollary is stated for vertex- and arc-coloured graphs. ✓
  * For "n^{polylog g}" with g the (unknown) genus of the input, add an invariant doubling over h. The
    (h−1)-CR test is itself invariant.
* **H4.** CONDITIONAL is the right label. Two additions are needed before "would answer Q 9.7"
  (Thesis p. 242: "time n^{polylog(k)} where k is the Hadwiger number of G").
  * (i) **Parameter-free form.** GNW's Thm M1885 takes h as input and "either correctly concludes that G₁
    has a minor isomorphic to K_h or decides…". The canonical twin must have the same form, with the
    failure outcome produced from canonical data, so that it is invariant. Then a doubling over h gives
    n^{polylog(Hadwiger number)}. The memo does this for treewidth (H§3.4) but not here.
  * (ii) **Prior art** (§5). Canonization of K_h-minor-free graphs is known in polynomial time for each
    fixed h (Grohe, LICS 2010; complete proof in the 2017 book), and in f(H)·n^{O(1)} with f possibly
    non-computable (LPPS, STOC 2022, arXiv:2210.14638). Neither gives n^{polylog h}, so Q 9.7 is still
    open as stated, and H4 would be new in its dependence on h only. The memo's "No prior … canonical
    version of … GNW" should be qualified accordingly.
* **FPT speculation.** Labelled as speculation. Fine.

---

## 5. Novelty

* **Searches I ran** (new dir `w9rt-search/`):
  * arXiv API, sorted by date: (canonization ∨ canonisation ∨ "canonical labeling/labelling/form(s)")
    ∧ {treewidth/tree width, minor/Hadwiger/topological subgraph, hypergraph, bounded degree, maximum
    degree, quasipolynomial/polylog, genus, composition factors, graph isomorphism}, through 2026-11-03;
  * au:Neuen (37 papers, latest 2609.37979), au:Wiebking (7), au:Grohe ∧ isomorphism,
    au:Schweitzer ∧ isomorphism;
  * four web searches (treewidth n^{polylog k} canonization; Neuen hypergraph canonization; excluded-minor
    canonization 2024–26; bounded-degree n^{polylog d} canonization).
* **Results.**
  * **No** canonization of Neu20, of n^{polylog k} treewidth, or of GNW/Neu22t in n^{polylog h}.
  * Nearest items:
    * Levet–Rombach–Sieger (rank-width, 2306.17777);
    * Grohe–Neuen (rank-width, 1901.10330);
    * Neuen 2106.14869 (genus FPT, isomorphism only);
    * LPPS 2210.14638 (excluded minor, isomorphism **and canonization**, f(H)·n^{O(1)});
    * a 2026 talk by Neuen (Leeds; seen only as a search snippet, not fetched) lists bounded-degree
      isomorphism at n^{polylog d} and canonization only via Babai.
  * Thesis p. 242 (June 2021) names GNS and Neu20a as the only tests without canonization. Neuen's
    dissertation (2020) predates this, so it is unlikely to contain canonical Neu20. Not obtained.
* **Missing from the memo's §5.** LPPS22 and Grohe's definable canonization for excluded minors, both
  relevant to H3/H4. For treewidth the memo's comparison (LPPS17, GNSW, Thesis 6.13) is adequate.
* **Expert expectation.** Survey26 (`survey.txt` L111–128): "many algorithms for GI can be modified to compute a graph
  canonization … We stress that the same is possible for many of the algorithms discussed in this
  survey". This does not name Neu20 or treewidth, and it does not claim the results. It supports the
  memo's "experts may call the results expected".
* **Credit.** The single-test-set, setwise-stabilizer device is Wiebking's (Thesis p. 101–103: "choose
  one single (canonical) test set T^can ⊆ W^can only"; Δ^can_T stabilizes T^can setwise). The memo
  credits this. What is new is its combination with Neuen's renormalization. It is modest but genuine.

---

## 6. Overall verdict and what I would sign

**No break.** I found no isomorphic pair with different outputs, and the toy model shows why: the only
risk, renormalization choices that see non-canonical data, does not occur in the memo's construction.

Statements I would sign:

1. **Theorem H (correctness).** The algorithm of H§2 is a canonizer for sets of 𝔓-strings under Γ̂_d
   cosets. This is modulo Neu20's constructions and their listed properties, GNS Thm V.3, Babai Thm 6(b),
   the CFSG facts of the aggregation, BC, Theorem A, and the P1 hygiene of H-c.
   **(Time.)** (n+m)^{O((log d)^c)} is a plausible sketch, conditional on writing out the transfer of
   N2671–2728 with the GAP-1 fix, the giant-test reorder, and H-a.
2. **Correction to write-up §9.2.** Wie20's treewidth algorithm uses `cosetHyper` only on
   hyperedge-respecting cosets (single call W336), so its canonical version needs canonical GNS, not
   canonical Neu20. [verified]
3. **Theorem TW.** Canonical forms for graphs of treewidth k in n^{O((log k)^c)}, [SKETCH, conditional on
   Theorem A], after TW-1 (χ step by Theorem A), TW-2 (mark S) and TW-3 (degeneracy check).
4. **H1** [mod Theorem H]. **H2, H3** [SKETCH]. **H4** [CONDITIONAL + SKETCH]. "Would answer Thesis Q 9.7"
   holds only in the parameter-free form (§4), and must be stated next to the f(H)·n^{O(1)} canonization
   of LPPS22 and the fixed-H polynomial canonization of Grohe.

**Edits requested in `w8-hypercanon.md`:**
* H§2.5 step (d): descent to R ∩ N′.
* H§2.7: 𝔓^σ-invariance.
* H§2.2 row 2: canonical generators for all group-only constructions.
* H§3.4(c): χ step, S marking, degeneracy check, equal-case extension pointer.
* H§3.3: notation.
* Theorem TW label → SKETCH.
* §4 H4: parameter-free form.
* §5: add LPPS22 and Grohe 2010/2017.
