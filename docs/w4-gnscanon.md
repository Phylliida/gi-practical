# w4-gnscanon: canonical forms for graphs of maximum degree d in n^polylog(d)

Branch `w4-gnscanon`, 2026-11-05. Wave 4 of the overnight campaign (`overnight-log.md`).
Follows Lead 1 of `w3-canon.md` (W3). **Nothing here depends on HJ (arXiv:2611.01399).**

**Task.**
1. State W3's "canonical-colour trick" as an exact lemma and attack it.
2. Go through Grohe–Neuen–Schweitzer (GNS) component by component. For each step, either give a
   canonical version or show that the trick is needed.
3. State and prove the strongest correct theorem.
4. Check novelty.

**Labels.**
* **[PROVEN]**: a complete argument is given here, using only the cited results and the standard
  polynomial-time permutation-group toolkit.
* **[PROVEN mod X]**: complete, except that X is used without re-proof.
* **[SKETCH]**: an argument is given; any missing details are named.
* **[GAP]**: a named step whose proof is missing.
* **[SPECULATION]**: opinion or conjecture.

**Sources.** All are untrusted data, read only, under `scratchpad/r4-sources/`.

| short name | what it is | where | read |
|---|---|---|---|
| GNS | arXiv:1802.04659v3 (FOCS'18; SICOMP 52(6), 2023). "GNS L…" is a line of `bounded-degree-polylog-d.tex`. | `arxiv-1802.04659/` | L125–580 (intro, preliminaries), L860–1556 (structure theorem, both reduction steps), L1556–2300 (affected orbits, local certificates, comparison, aggregation, main algorithm, applications), L2288–2390 (appendix: aggregation proof) |
| BC | Babai, *Canonical form for graphs in quasipolynomial time*, STOC'19, NSF copy | `w3c-babai-canon/` | full text |
| S-W | Schweitzer–Wiebking, arXiv:1806.07466 | `w1s-arxiv-1806.07466/` | intro, open questions |
| Wie20 | Wiebking, arXiv:1911.11257 (ICALP'20) | `w3c-wiebking-1911.11257/` | intro, open questions, hypergraph section (canonical generating sets, Lemma `canGen`), Theorem `canGraph` (BC as a black box), treewidth section (Theorem `boundedDegree`) |
| Neu20 | Neuen, arXiv:2002.06997 (ICALP'20), hypergraph isomorphism for Γ̂_d | `arxiv-2002.06997/` | abstract, related work, conclusion, aggregation L2585–2600 |
| Survey26 | Neuen's 2026 survey (Comput. Sci. Rev.) | `regensburg-neuen-survey/` | the "Can" paragraph |
| arXiv API | author and title queries | new dir `w4g-arxiv-queries/` | parsed with `scratchpad/w4g-scripts/atom.py` (`python3 -I`) |

I tried to download Wiebking's 2021 dissertation into `w4g-wiebking-thesis/`. A bot wall blocked
it, so only its abstract was read (§6).

**Executed.** curl downloads and one XML parse with `python3 -I`. Nothing else: no Lean, no solver,
no benchmark. CPU use was negligible.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Is the trick genuinely canonical? | **Yes.** It is the "canonical subcoset" step applied to a marked ordered tuple: send the tuple to a fixed reference tuple, then canonize under the reference tuple's pointwise stabilizer (Lemma T). The colour of (x, T⃗) depends only on the H-orbit of the pair (windowed string, T⃗), where H is the current group. It does not depend on the pairing, the transporter σ, or the generators. The reference tuple is a function of the group alone, and changing it renames colours without changing the classes. The colour classes are **exactly** GNS's comparison classes. Every t-set inside the non-full region is non-symmetric, so the relative symmetry defect is ≥ 1/4 (Lemma T′). | **[PROVEN]** |
| 2 | What does the trick cost? | At most k^t ≤ d^{O(log d)} ordered tuples. Each costs recursive canonizer calls on disjoint subsets of the window, each of size ≤ n/2, total size ≤ n (Lemma T″). GNS pay binom(k,t)²·t! comparisons. The trick is cheaper and needs **no relation between t and n**. | **[PROVEN mod GNS Thm 5.9 (Affected Orbit Lemma)]** |
| 3 | Where does Babai's t ≥ 2 log₂ n enter, and is it still needed? | In BC it enters only through the selection of a point from each *asymmetric* test set (Claim 12.4): via Cor. 13.3 / Lemma 15.1 (Jordan–Liebeck sandwich, which needs binom(t, ⌊t/4⌋) > n) and via Prop. 14.2 together with the large-window step §11. Babai's isomorphism threshold t > 2 + log₂ n (Unaffected Stabilizers) is replaced in GNS by t > max{8, 2 + log₂ d}. The trick makes Claim 12.4 unnecessary. **No logarithmic-in-n threshold remains.** | **[PROVEN]** (§5) |
| 4 | Does the trick apply to GNS? | **Yes.** In GNS, the *only* pairwise-canonical step is the |S| < k/4 case of the aggregation (GNS L2370–2385, built from Lemma 6.3 `compare-local-certificates`). Every other step has a direct canonical version: chain rule, descent, strongly canonical assignment, canonical subcoset, equivariant change of action. GNS never run the Design Lemma or Split-or-Johnson. They apply Babai's test as a black box to structures on k ≤ d points, which BC's canonizer replaces. | **[PROVEN mod cited]** (§3) |
| 5 | Main result | **Theorem A.** For G ∈ Γ̂_d given by generators, a canonical labelling (canonical form plus canonical coset) of strings under G is computable in n^{O((log d)^c)}. **Corollary B.** Graphs of maximum degree d have canonical forms computable in n^{O((log d)^c)}, the same bound as the GNS isomorphism test. Also: canonical labellings of graphs relative to a labelling coset of composition width d (Corollary D), the canonical twin of the GNS statement that Wiebking uses. | **[PROVEN mod GNS's lemmas, BC Thm 2.2, BL83's canonical Luks reduction, canonical generating sets]**. The new canonical ingredients are **[PROVEN]**. The transfer of the GNS running-time recursion is **[SKETCH]**, with no known gap. |
| 6 | Gaps | No mathematical gap found. Dependencies used without re-proof: (i) BC (STOC'19, a "preliminary report", used by Wie20 and others as a theorem), here only on structures with ≤ d points and arity O(log d); (ii) BL83's canonical version of Luks's reduction (not re-read; §3.1 sketches it); (iii) GNS's structural lemmas and recursion analysis as published. | §4.4 |
| 7 | Novelty | Stated as open by S-W (2019: "remains as future work") and by Wie20 (2020: "no adequate canonization version is known"). Not done by Neu20, Grohe–Neuen–Wiebking (minors), Neuen (topological subgraphs) or the 2026 survey (only a generic "the same is possible for many of the algorithms"). Arxiv author and title queries for Neuen, Wiebking and Schweitzer through 2026-11 and web searches found nothing. Wiebking's 2021 thesis could not be read; its abstract mentions treewidth and minors but not degree. **To my knowledge new.** The trick itself is elementary ("send the individualized tuple to reference labels"). The new point is that it removes the obstacle that made GNS canonization open. | lit. (§6) |

**Verdict.** The lead works. Making GNS canonical needs exactly one new idea: canonical tuple colours
instead of pairwise comparisons. Everything else is Babai–Luks bookkeeping. With BC as a black box
on d-point structures, this gives **the first n^polylog(d) canonization of graphs of maximum degree d**,
an unconditional result relative to published work. Not refereed. It should be checked by someone
who knows the GNS paper in detail (§4.4, §7).

---

## 1. The trick, stated exactly

### 1.1 Conventions (used throughout)

* Ω is finite and linearly ordered. Σ is an alphabet with a blank symbol β.
* Sym(Ω) acts on strings by x^g(α) = x(α^{g⁻¹}), so (x^g)^h = x^{gh}.
* For U ⊆ Ω, x^{[U]} is the *windowed string*: equal to x on U and to β elsewhere.
* For H ≤ Sym(Ω): Aut_H(x) = {h ∈ H : x^h = x} and Iso_H(x, y) = {h ∈ H : x^h = y}.

**Canonizer.** Let H ≤ Sym(Ω) and let 𝒳 be an H-invariant set of strings. An *H-canonizer on 𝒳*
assigns to each x ∈ 𝒳 a string F_H(x) and a set Λ_H(x) ⊆ H such that:
* (C1) Λ_H(x) = {h ∈ H : x^h = F_H(x)} ≠ ∅;
* (C2) F_H(x^h) = F_H(x) for all h ∈ H.

Consequences:
* Λ_H(x^h) = h⁻¹Λ_H(x);
* Λ_H(x) = λ·Aut_H(F_H(x)) for any λ ∈ Λ_H(x);
* Aut_H(x) = Λ_H(x)Λ_H(x)⁻¹;
* Iso_H(x, y) = Λ_H(x)Λ_H(y)⁻¹ if F_H(x) = F_H(y), and ∅ otherwise.

This is BC Def. 5.1 (canonical placement CP = Λ), and also S-W's (CL1)/(CL2) with labelling
cosets.

**Cosets.** For a coset C = σH put Λ_C(x) := σΛ_H(x^σ) and F_C(x) := F_H(x^σ). By (C2) this does not
depend on the representative σ, and Λ_{gC}(x) = gΛ_C(x^g). This is BC rule (i). So everything reduces
to groups.

**Principle P1 (choices that are functions of the group).** At a node with group H, the algorithm
may make any choice that is a deterministic function of H *as a set*: block systems, giant
representations, orderings of orbits, reference tuples. This is achieved by first replacing the
generators with a *canonical generating set*, which depends only on H and is computable in
polynomial time (Wie20 Lemma `canGen` = AGMMM18 Lemma 6.2 = GNSW18 Lemma 21; S-W §"canonical
generating sets"). In what follows, "(P1)" marks such a choice.

### 1.2 The canonical-subcoset lemma and the trick

**Lemma S (canonical subcoset).** **[PROVEN]**
* *Setting.*
  * H ≤ Sym(Ω), and φ : H → Sym(Γ) is a homomorphism.
  * 𝒮 is a φ(H)-set of "structures on Γ". It comes with a φ(H)-canonizer Λ′ (so Λ′(S) ⊆ φ(H) and
    S_can := S^{Λ′(S)}).
  * x ↦ S(x) ∈ 𝒮 is H-equivariant: S(x^h) = S(x)^{φ(h)}.
  * For each S_can, a canonizer is available for R := φ⁻¹(Aut_{φ(H)}(S_can)).
* *Definition.* Put E(x) := φ⁻¹(Λ′(S(x))), a left coset σR of R, and Λ_H(x) := Λ_{E(x)}(x), i.e.
  F_H(x) := F_R(x^σ).
* *Claim.* This is an H-canonizer, and its right subgroup is Aut_R(F_H(x)).

*Proof.*
* *Equivariance of E.* From Λ′(S^π) = π⁻¹Λ′(S) we get E(x^h) = h⁻¹E(x).
* *(C2).* For x^h the representative h⁻¹σ gives F_R((x^h)^{h⁻¹σ}) = F_R(x^σ).
* *(C1), "⊆".* Every e ∈ Λ_{E(x)}(x) satisfies x^e = F := F_H(x). It also satisfies
  S(F) = S(x)^{φ(e)} = S_can, since e ∈ E(x).
* *(C1), "⊇".* Let h ∈ H with x^h = F. Then S(x)^{φ(h)} = S(F) = S_can, so φ(h) ∈ Λ′(S(x)) by (C1)
  for Λ′. Hence h ∈ E(x), and so h ∈ Λ_{E(x)}(x). ∎

**Lemma T (tuple colours: the trick).** **[PROVEN]**
* *Setting.*
  * H, φ : H → Sym(Γ) as above. T⃗₀ is a fixed injective t-tuple of Γ (P1, e.g. the first t labels
    of Γ), and φ(H) is transitive on the orbit 𝒪 := T⃗₀^{φ(H)}.
  * J₀ := {h ∈ H : T⃗₀^{φ(h)} = T⃗₀}, the pointwise stabilizer of T⃗₀.
  * 𝒴 is an H-invariant set of strings, and F_{J₀} is a J₀-canonizer on 𝒴.
* *Definition.* For y ∈ 𝒴 and T⃗ ∈ 𝒪, choose σ ∈ H with T⃗^{φ(σ)} = T⃗₀ and put
  c(y, T⃗) := F_{J₀}(y^σ).
* *Claim.*
  * (a) c is well defined, i.e. independent of σ.
  * (b) c(y^h, T⃗^{φ(h)}) = c(y, T⃗) for all h ∈ H.
  * (c) c(y, T⃗) = c(y′, T⃗′) **iff** there is h ∈ H with y^h = y′ and T⃗^{φ(h)} = T⃗′.
  * (d) Λ_H(y, T⃗) := σΛ_{J₀}(y^σ) is an H-canonizer for the pairs (y, T⃗).

*Proof.* This is Lemma S with S(y, T⃗) := T⃗. The canonizer Λ′ on 𝒪 sends T⃗ to T⃗₀; it is well
defined because φ(H) is transitive on 𝒪, and Λ′(T⃗) = {π ∈ φ(H) : T⃗^π = T⃗₀}. Then R = J₀ and
E(y, T⃗) = σJ₀. Directly:
* (a) If σ, σ′ both work, then σ⁻¹σ′ ∈ J₀, so y^{σ′} = (y^σ)^{σ⁻¹σ′} lies in the J₀-orbit of y^σ.
* (b) h⁻¹σ is a valid transporter for (y^h, T⃗^{φ(h)}).
* (c) "If" is (b). "Only if": F_{J₀}(y^σ) = F_{J₀}(y′^{σ′}) gives j ∈ J₀ with y^{σj} = y′^{σ′}. Take
  h := σjσ′⁻¹. Then y^h = y′ and T⃗^{φ(h)} = T⃗₀^{φ(jσ′⁻¹)} = T⃗′. ∎

**How it is used (the definition that replaces GNS's comparisons).** At an aggregation node of GNS
(§3.4) we have:
* the current group H, with an almost d-ary sequence;
* a giant representation φ : H → S_k with k ≤ d;
* test-set size t with max{8, 2 + log₂ d} < t < k/10;
* for every t-set T ⊆ [k], GNS's local-certificate window W(T, x), which is H-equivariant:
  W(T^{φ(h)}, x^h) = W(T, x)^h (GNS L1939; BC Lemma 10.1);
* the canonical set D(x) ⊆ [k] of points outside the support of the fullness group. Every t-set
  T ⊆ D(x) is non-full.

Then define
$$c_x(\vec T) := c\bigl(x^{[W(T,x)]},\ \vec T\bigr)\qquad(\vec T\in D(x)^{\langle t\rangle}),$$
$$\mathfrak A(x) := \bigl([k];\ \text{unary colour } D(x);\ t\text{-ary colouring } \vec T\mapsto \operatorname{rank}(c_x(\vec T))\bigr).$$
The rank is taken in the set of all values of c_x. That set is an invariant of the H-orbit of x by
(b), so ranking is canonical.

**Lemma T′ (what GNS need from the structure).** **[PROVEN, using only GNS's local-certificate
facts]**
1. *Strongly canonical.* 𝔄(x^h) = 𝔄(x)^{φ(h)} for h ∈ H.
2. *Exactness.* For two strings x₁, x₂ under the same H, the partition of
   D(x₁)^{⟨t⟩} ⊔ D(x₂)^{⟨t⟩} by c-values **equals** the partition into GNS's comparison classes
   (GNS L2370–2385).
3. *Symmetry defect.* If Alt(Δ) ≤ Aut(𝔄(x)), then Δ ⊆ [k] ∖ D(x) or |Δ| ≤ t + 1. Hence, since
   t < k/10 and |[k] ∖ D| < k/4, the relative symmetry defect of 𝔄(x) is ≥ 1/4.

*Proof.*
1. Combine equivariance of D, of W and of c (Lemma T(b)).
2. GNS's comparison (Lemma `compare-local-certificates`) runs the window loop for (T₁, x₁) and carries
   along the coset G_iσ_i of maps that respect x₁ on the window so far. By induction on i:
   * W₁ depends only on T₁, so W₁(T₁)^{σ₀} = W₁(T₂).
   * If G_iσ_i ≠ ∅, then G_i^{σ_i} = Aut_{H_{T₂}}(x₂^{[W_i(T₂,x₂)]}), so W_{i+1}(T₁, x₁)^{σ_i} = W_{i+1}(T₂, x₂).

   Hence the final coset is exactly
   {h ∈ H : T₁^{φ(h)} = T₂, (x₁^{[W(T₁,x₁)]})^h = x₂^{[W(T₂,x₂)]}}, restricted to T₁. So two ordered
   tuples are comparison-equivalent iff such an h maps one to the other. That is Lemma T(c).
3. Alt(Δ) is transitive on Δ (|Δ| ≥ 3) and preserves D, so Δ ⊆ D or Δ ∩ D = ∅. Suppose Δ ⊆ D and
   |Δ| ≥ t + 2, and pick T ⊆ Δ with |T| = t.
   * Every π ∈ Sym(T) is induced by some ρ ∈ Alt(Δ): fix the parity on Δ ∖ T, which has ≥ 2 points.
     So c_x(T⃗) = c_x(T⃗^π) for every ordering.
   * T⃗ and T⃗^π have the same window W(T, x). Lemma T(c) gives h ∈ H_T fixing x^{[W(T,x)]} with
     φ(h)|_T = π.
   * So ψ_T(Aut_{H_T}(x^{[W(T,x)]})) = Sym(T). But for non-full T, GNS's loop ends with exactly this
     group being a non-giant (GNS L1840–1844, L1930–1934). [We use the identity G_i = Aut_{H_T}(x^{[W_i]}): every
     element of the right-hand side preserves W₁, …, W_i successively, because W_j is
     G_{j−1}-invariant.] Contradiction.

   The defect bound: k − max(t + 1, k/4) ≥ k/4. ∎

**Adversarial checklist.**

| possible hidden dependence | status |
|---|---|
| on the pairing (x₁, x₂) | none: c_x uses x only |
| on the transporter σ | none: Lemma T(a) |
| on the reference tuple T⃗₀ | T⃗₀ is (P1). Another reference T⃗₁ gives c₁(y, T⃗) = F_{J₁}(y^{σσ₀₁}), a bijective renaming with the same classes, and it is the same function for every input under H |
| on generator lists | J₀ = φ⁻¹(stabilizer) is a set. The canonizer F_{J₀} is a function of (J₀, input), because every choice inside it is (P1) on canonical generating sets |
| on the labelling of the ideal domain [k] | (P1): the giant representation is computed from canonical generators of H |
| on how W(T, x) is computed | none: W is a function of (T, x), and equivariant |
| is F_{J₀} really a canonizer, given that it is computed by a special procedure rather than a general call? | yes: Lemma F2 below proves the special procedure satisfies (C1)/(C2) on the J₀-invariant set of windowed certificate strings |
| relative to which group is it canonical? | relative to the node's group H. That is what the Babai–Luks framework requires (BC rule (i), Principle P2 of W3) |

**Why Babai did not do this (diagnosis).** **[SKETCH]**
* BC §16 computes CP of certificate strings under the *setwise* stabilizer G_T. It then makes them
  G-canonical by **right descent over all t-sets**, taking a lexicographic leader.
* The result is a G-canonical form of the *string* x(T, u). It forgets T unless the string itself
  determines T. Prop. 14.2 (Δ(T) determines T) and Lemma 15.1 (Ω(T, u) determines u) exist to force
  that.
* Lemma T keeps only the **single right-coset piece** at a fixed reference tuple. That piece is the
  canonical form of the *marked pair* (string, ordered tuple). So nothing has to be encoded into the
  string.

Remark 5.2 discusses what this means for BC itself.

---

## 2. Framework lemmas (Babai–Luks, in the conventions of §1.1)

**Lemma F1 (restriction).** **[PROVEN]** Let U be H-invariant and ρ_U : H → H^U the restriction. Then
Λ_H(x^{[U]}) := ρ_U⁻¹(Λ_{H^U}(x|_U)) is an H-canonizer for windowed strings. It is computable from
Λ_{H^U} in polynomial time (preimage of a coset).

**Lemma F2 (sequential chain rule with input-dependent windows).** **[PROVEN]**
* *Setting.* U₀ = ∅. Windows V₁, V₂, … are given by functions V_{i+1}(x^{[U_i]}) ⊆ Ω ∖ U_i of the
  already-windowed string, H-equivariant: V_{i+1}(y^h) = V_{i+1}(y)^h. Put U_{i+1} := U_i ∪ V_{i+1}.
  The *layered* string x^{⟨U_r⟩} also records the layer index of each position. It is an
  H-equivariant function of x^{[U_r]}.
* *Recursion.* Given (F_i, Λ_i) for x^{⟨U_i⟩}, pick τ ∈ Λ_i and put:
  * w := x^τ;
  * A_i := Aut_H(F_i), the right subgroup of Λ_i;
  * V′ := V_{i+1}(F_i), which is A_i-invariant;
  * (F′, Λ′) := an A_i-canonizer of w^{[V′]};
  * F_{i+1} := F_i ⊕ F′ (labelled with layer i+1) and Λ_{i+1} := τΛ′.
* *Claim.* (F_{i+1}, Λ_{i+1}) is an H-canonizer for x^{⟨U_{i+1}⟩}.

*Proof.*
* *Independent of τ.* Replacing τ by τa (a ∈ A_i) replaces w by w^a. Since V′^a = V′, F′ is unchanged
  and Λ′ becomes a⁻¹Λ′.
* *(C2).* For x^h, Λ_i(x^h) = h⁻¹Λ_i(x), so we may take τ′ = h⁻¹τ and get the same w.
* *(C1), "⊆".* For τa with a ∈ Λ′: (x^{⟨U_i⟩})^{τa} = F_i^a = F_i. By equivariance,
  V_{i+1}(x^{[U_i]})^τ = V_{i+1}(F_i) = V′, so (x^{[V_{i+1}]})^{τa} = (w^{[V′]})^a = F′.
* *(C1), "⊇".* If h maps x^{⟨U_{i+1}⟩} to F_{i+1}, then the layers force (x^{⟨U_i⟩})^h = F_i. So
  h = τa with a ∈ A_i, and (w^{[V′]})^a = F′, so a ∈ Λ′. ∎

The plain windowed string determines the layering equivariantly. So canonizing the layered string
canonizes the plain one (Lemma F4 with one branch). This is BC Rem. 5.5 / §16, with the left/right
conventions fixed. It closes the convention gap flagged in W3 §2.2.

**Ordinary chain rule.** This is Lemma F2 with windows that are functions of the group only. The
standard case: the orbits of A_i inside V′, ordered by (size, least element) (P1), each processed by
Lemma F1 under the then-current right subgroup.

**Lemma F3 (descent).** **[PROVEN]**
* *Setting.* K ≤ H with H = ⊔_{ρ∈R} ρK.
* *Definition.* Put m := min_ρ F_K(x^ρ) and Λ_H(x) := ⋃_{ρ : F_K(x^ρ) = m} ρΛ_K(x^ρ).
* *Claim.* This is an H-canonizer, and Λ_H(x) = {h ∈ H : x^h = m}.

*Proof.*
* *(C2).* The multiset of branch values for x^h is a permutation of the one for x, because
  hρK runs over all left cosets and F_K(x^{ρk}) = F_K(x^ρ).
* *(C1).* If x^{ρk} = m, then the K-orbits of x^ρ and of the minimizing x^{ρ₀} coincide (both contain
  m). So F_K(x^ρ) = m. ∎

This is BC Prop. 5.7. The output depends only on the branch values. Hence **branches whose values are
known to coincide need not be evaluated separately**; this is used in Lemma K.

**Lemma F4 (equivariant branch family; strongly canonical assignment).** **[PROVEN]**
* *Setting.* x ↦ 𝔅(x) is a finite H-equivariant family of branch objects: 𝔅(x^h) = 𝔅(x)^h. There is a
  canonizer F_H(x, b) for pairs.
* *Definition.* Put F := min_{b∈𝔅(x)} F_H(x, b), with first component F^x, and
  Λ_H(x) := ⋃_{b minimizing} Λ_H(x, b).
* *Claim.* Λ_H(x) = {h ∈ H : x^h = F^x}, so this is an H-canonizer for x.

*Proof.*
* Let x^h = F^x. Then 𝔅(F^x) = 𝔅(x)^h contains the second component F^b (F is attained by some pair in
  the H-orbit of (F^x, F^b)).
* So b := (F^b)^{h⁻¹} ∈ 𝔅(x) and (x, b)^h = F.
* F_H(x, b) = F_H(F) = F, so b minimizes. ∎

With |𝔅| = 1 this is BC Obs. 8.4. It covers individualization (the branch is the individualized
object) and "canonical refinement".

---

## 3. GNS, component by component

GNS prove the result by:
* Luks's reduction from graphs to Γ̂_d strings (GNS Thm 8.1, citing Luks82 and BL83);
* the change of action to an **almost d-ary** sequence (Thms 4.3/4.6, GNS L1042–1556), giving
  |Ω*| ≤ n^{(c₁ log d + c₂ + 1) log d};
* the almost-d-ary string algorithm (Alg. `string-isomorphism-alg`, Lemma
  `partition-small-size-recursion`, L2059–2190), built on:
  * the Unaffected Stabilizers Theorem for almost-d-ary groups (Thm 5.8, L1690): test sets of size
    t > max{8, 2 + log₂ d};
  * local certificates (Lemma 6.2, L1775–1862);
  * comparison (Lemma 6.3, L1866–1940);
  * aggregation (Lemma 6.6 and Appendix A, L1966–1998, L2311–2385);
  * Lemmas 6.7 `find-structure` / 6.9 `find-symmetry` (L1999–2057).

### 3.1 Table

| GNS component (lines) | pairwise? | canonical version | tool | label |
|---|---|---|---|---|
| Luks reduction graphs → Γ̂_{d−1} strings (Thm 8.1, L2208) | — | BL83's canonical version (BC §5.6). Sketch: (1) branch over edges e (Lemma F4); (2) layer by layer, canonize the half-edge string on (L_r × [d−1])² under the lift of the current canonical coset to A_r ≀ S_{d−1}, which lies in Γ̂_{d−1}. Polynomially many calls, domains of polynomial size | BL83 | cited / **[SKETCH]** |
| orbit-by-orbit processing (Alg. 1, L441) | no | chain rule; orbits ordered by (size, least point) | F1, F2 | **[PROVEN]** |
| change of action to almost d-ary (Thms 4.3, 4.6) | no | the construction (Ω*, G*, 𝔅*_i, x ↦ x*) is a function of G only (P1: maximal block, σ_{1→i}, ρ_{i,B}, choice of orbit A*). It is equivariant: (x^g)* = (x*)^{g*}, and g ↦ g* is injective. So the canonizer pulls back (Lemma R) | Lemma R | **[PROVEN]** |
| semi-regular top level, small primitive P (≤ d^{1+log d}), k ≤ 10t: "standard Luks reduction" (L2088, L2100, L2153) | no | descent to the kernel, then chain rule on its orbits | F3, F2 | **[PROVEN]** |
| primitive quotient, Babai's giant representation (Lemma 7.1, L2065) and descent to G′ of index ≤ d | no | (P1) choice of N, 𝔅, φ; descent over ≤ d cosets | P1, F3 | **[PROVEN]** |
| local certificates (Lemma 6.2, Alg. 2) | no | outputs (W(T, x), M(T, x) or K(T, x)) are canonical objects (L1939; BC Lemma 10.1). The automorphism groups they need are right subgroups of recursive canonizer calls. Iso_{Nḡ} = Iso_N(y, y^{ḡ⁻¹})ḡ comes from two canonizer calls on the same N-orbits | §1.1 consequences | **[PROVEN]** |
| fullness group F, support S, case split on \|S\|, orbit partition (L2339–2348) | no | strongly canonical assignment | F4 | **[PROVEN]** |
| large orbit C with non-giant F^C: individualize I (≤ k⁴), a relation R_i (≤ k), a vertex (≤ k) (L2350–2365) | no | equivariant branch family; the family {𝔄_j(x)} with r ≤ k⁶ is equivariant as a set | F4 | **[PROVEN]** |
| **\|S\| < k/4: comparison classes → t-ary structure** (Lemma 6.3 used in Lemma 6.6, L2370–2385) | **yes**: classes are named jointly on D′₁ ⊔ D′₂ ("canonical" in GNS's sense, L1886, means only canonical w.r.t. Aut(x_i)) | **canonical tuple colours, Lemma T; same classes (Lemma T′.2), symmetry defect ≥ 1/4 (T′.3)** | **Lemma T** | **[PROVEN]** |
| `find-structure` (Lemma 6.7, L1999): Iso(𝔄₁, 𝔄_{2,j}) by Babai's test, black box | yes (pairs 𝔄₁ with each 𝔄_{2,j}) | for each branch j: canonical subcoset E_j(x) = φ⁻¹(Λ′(𝔄_j(x))), where Λ′ is BC's canonizer of the t-ary structure under φ(G′) on [k] (a string on [k]^t, cost exp(polylog d)). Then combine over j | S, F4, BC | **[PROVEN mod BC]** |
| `find-symmetry` (Lemma 6.9, L2032): H = G_{(Δ₁)}, two cosets h₁, h₂, rebuild with K₁ | yes | canonical subcoset Δ(x) ↦ Δ₀ (P1), then K-collapsed descent: two branch values | S, Lemma K | **[PROVEN]** |
| recursion on H with \|G′^φ : H^φ\| ≥ (4/3)^k; analysis k′ ≤ k − k/(3 log k) (L2104–2131) | no | identical. Canonical right subgroups equal GNS's groups H_j, G_{(Δ₁)} up to conjugation, with the same branch counts (≤ k⁶, ≤ 2) | — | **[SKETCH]**: verbatim transfer |

**Remarks on the table.**
* GNS handle **Cameron and Johnson groups** in two places:
  * Large primitive Γ̂_d-groups with Johnson or Cameron socle are *unfolded* by the change of action
    (subset lattices replaced by tuples). Canonically, this is Lemma R.
  * Inside the almost d-ary algorithm, primitive quotients of degree ≤ d get Babai's giant
    representation on k ≤ d points.

  Babai's Split-or-Johnson and Design Lemma **never run** in GNS. Because k ≤ d, GNS simply apply
  Babai's quasipolynomial test to the k-point structures. That is why the canonical version needs
  only BC's black box there, and no canonical Design Lemma.
* GNS's aggregation output (L1980–1990) is "pairwise" in two places: the comparison structure, and
  find-structure/find-symmetry, which pair x₁'s object with x₂'s. The second kind is routine
  (Lemmas S, F4, K). **The first kind is the only real obstacle, and Lemma T removes it.**

### 3.2 Lemma R: change of action

**Lemma R.** **[PROVEN]**
* *Setting.* G ≤ Sym(Ω), and ι : G → Sym(Ω*), g ↦ g*, is an injective homomorphism. x ↦ x* is
  injective with (x^g)* = (x*)^{g*}. A G*-canonizer is given.
* *Definition.* Put Λ_G(x) := ι⁻¹(Λ_{G*}(x*)), and let F_G(x) be the unique y with y* = F_{G*}(x*).
* *Claim.* This is a G-canonizer.

*Proof.*
* *F_G exists.* F_{G*}(x*) = (x*)^{λ*} = (x^λ)*.
* *(C1).* g* ∈ Λ_{G*}(x*) ⟺ (x^g)* = F_{G*}(x*) ⟺ x^g = F_G(x), by injectivity of *.
* *(C2).* (C2) for G* and (x^h)* = (x*)^{h*}. ∎

*Check against GNS.*
* x*(N^B h, α) = x(α) and g* acts by (Nh, α) ↦ ((Nh)^g, α^g), so equivariance holds (GNS, the
  claims in the proofs of Thms 4.3 and 4.6).
* After restriction to one G*-orbit A*, x ↦ x*|_{A*} is still injective, because every α ∈ Ω occurs as
  a second coordinate when G is transitive (GNS L1211). The action on A* is faithful for the same
  reason.
* All auxiliary choices are made once per group (P1). Rule (i) handles cosets.
* GNS apply the reduction only to transitive constituents at the top level (GNS Thm 7.4, L2191). The
  almost d-ary recursion never re-applies it (GNS Obs. 4.2: the sequence is inherited by subgroups
  and restrictions).

### 3.3 Lemma K: find-symmetry, canonically

**Lemma K.** **[PROVEN]**
* *Setting.* At a node with group G′ and giant representation φ, Option 2 of the aggregation gives a
  canonical Δ(x) ⊆ [k] with |Δ| ≥ 3k/4, and K(x) = F(x) ≤ Aut_{G′}(x) with K(x)^φ|_Δ ≥ Alt(Δ). Both are
  equivariant.
* *Algorithm.*
  1. Lemma S with S(x) = Δ(x) and Δ₀ := {1, …, |Δ|} (P1). Since φ(G′) ≥ A_k, it is transitive on
     |Δ|-sets. This gives E(x) = σ·G′_{Δ₀}. Put z := x^σ, so Δ(z) = Δ₀.
  2. Put L := G′_{(Δ₀)}, which is normal in G′_{Δ₀}. Since K(z)^φ|_{Δ₀} ≥ Alt(Δ₀),
     G′_{Δ₀} = K(z)L ∪ K(z)Lτ, where τ is any element inducing an odd permutation on Δ₀ (if one
     exists).
  3. Every coset ρL with ρ ∈ K(z)L has branch value F_L(z^{kl}) = F_L(z^l) = F_L(z). Cosets in K(z)Lτ
     have branch value F_L(z^τ).
  4. So descent (Lemma F3) needs **two** canonizer calls under L. The output coset
     {g ∈ G′_{Δ₀} : z^g = m} is generated by K(z), Λ_L of the minimizing branch(es), and the
     tie-element τλ′λ⁻¹ if the two values are equal.
* *Cost.* |G′^φ : L^φ| ≥ |Alt(Δ₀)| ≥ (4/3)^k, with 2 recursive branches: exactly GNS's r ∈ {1, 2}.

### 3.4 Lemma T″: computing the colours

**Lemma T″.** **[PROVEN mod GNS Thm 5.9 (= Babai's Affected Orbit Lemma)]**

*Setting.* A non-full T ⊆ D(x) with window chain W₀ = ∅ ⊂ W₁ ⊂ … ⊂ W_ℓ = W(T, x), and an ordering T⃗.

*Claim.* c_x(T⃗) and its canonizer coset can be computed in poly(n) time plus recursive canonizer
calls on pairwise disjoint subsets of W(T, x). Each subset has size ≤ n/2, and the groups are
restrictions of subgroups of H. So the calls inherit the almost d-ary sequence.

*Proof.*
* Let σ map T⃗ to T⃗₀ and put z := x^σ. Then (x^{[W(T,x)]})^σ = z^{[W(T₀,z)]}, and we need
  F_{J₀}(z^{[W(T₀,z)]}).
* Apply Lemma F2 with group J₀ and windows V_{i+1}(z^{[W_i]}) := Aff(Aut_{H_{T₀}}(z^{[W_i]}), ψ) ∖ W_i,
  as long as GNS's loop continues. These windows are H_{T₀}-equivariant: Aff(B^g, ψ) = Aff(B, ψ)^g for
  g ∈ H_{T₀}.
* At stage i:
  * A_i = Aut_{J₀}(F_i) = ker(ψ|_{G_i(F_i)}), where G_i(F_i) := Aut_{H_{T₀}}(F_i), because
    J₀ = ker(ψ : H_{T₀} → Sym(T₀)).
  * G_i(F_i) = G_i(T, x)^{στ_i}, with τ_i ∈ Λ_i. The group G_i(T, x) was already computed in the
    local-certificate phase for the unordered T.
  * V′ = V_{i+1}(F_i) is a union of G_i(F_i)-orbits affected by the giant representation ψ of degree
    t ≥ 9.
* If |V′| ≤ n/2: one call on V′ (Lemma F1). Otherwise: chain rule over the A_i-orbits in V′. Each has
  length ≤ |orbit|/t ≤ n/t by GNS Thm 5.9. This is the analogue of GNS's own case split (L1849–1858),
  **without** their t! descent, because the right subgroup is already the kernel. ∎

Over all ordered tuples, the recursive sizes add up to ≤ k^t·n ≤ d^{O(log d)}·n. This is inside GNS's
budget for the aggregation node, Σn_i ≤ k^{O(t)}n (GNS Lemma 6.6). GNS spend
binom(k, t)²·t!·n on comparisons. The local certificates themselves (binom(k, t)·t!·2n via Iso from
canonizer calls) are as in GNS.

---

## 4. The theorem

### 4.1 Statement

**Theorem A (canonical string labelling for Γ̂_d).**
**[PROVEN mod: GNS Thm 3.13, Thms 4.3/4.6 (structure and change of action), Thm 5.8 (Unaffected Stabilizers), Thm 5.9 (Affected Orbits), Lemma 6.2, Cor. 6.5, the case analysis of Lemma 6.6, Lemma 7.1, and the recursion analysis of Lemma 7.2/Thm 7.3; BC Thm 2.2; canonical generating sets. The running-time transfer is SKETCH.]**

There is an algorithm that does the following, in time n^{O((log d)^c)} for an absolute constant c:
* *Input:* G ≤ Sym(Ω) with G ∈ Γ̂_d, given by generators; a subcoset C = σG; and a string x : Ω → Σ.
* *Output:* a C-canonizer Λ_C(x), i.e. a canonical form F_C(x) together with
  Λ_C(x) = {g ∈ C : x^g = F_C(x)}. In particular it outputs Aut_G(x) and decides G-isomorphism.

**Corollary B (graphs of maximum degree d).** **[same, plus BL83's canonical Luks reduction]**
A canonical form (canonical labelling) for n-vertex graphs of maximum degree d is computable in time
n^{O((log d)^c)}.

**Corollary C (relational structures).** **[same as A]**
* Canonical forms of t-ary relational structures on n points in n^{O(t·(log n)^c)}: the canonical
  twin of GNS Thm 8.3, via the string on D^t under Sym(D) ∈ Γ̂_n.
* This is weaker than Wie20's hypergraph canonization in general. It is listed only for completeness.

**Corollary D (graphs relative to a labelling coset).** **[same as A]**
* *Input:* a graph on V and a coset Δρ whose group Δ has composition width ≤ d.
* *Output:* a canonical labelling relative to Δρ, in |V|^{O((log d)^c)}.
* *Proof.* Encode the edge relation as a string on V² under Δ acting on pairs; Δ stays in Γ̂_d.
* This is the canonical twin of the statement Wie20 imports from GNS (Wie20 Theorem `boundedDegree`).

### 4.2 Proof of Theorem A

The algorithm is GNS's, with every step replaced by its canonical version from §3.1. We prove
correctness (it is a canonizer) and the time bound.

**Step 1: reduction to groups and to the transitive case.** **[PROVEN]**
* Cosets reduce to groups by rule (i) (§1.1).
* Intransitive G is handled by the chain rule over orbits, ordered by (size, least point) (Lemma F2).
  Each transitive constituent is a recursive call on its domain.

**Step 2: change of action.** **[PROVEN]** For a transitive constituent, apply GNS Thm 4.6 (P1) and
Lemma R. Now G* has a G*-invariant almost d-ary sequence 𝔅*₀ ≻ … ≻ 𝔅*_m, and |Ω*| ≤ n^{O(log² d)}.

**Step 3: the almost d-ary canonizer** (GNS Alg. 3, with canonical steps). By induction on the domain
size: assume canonizers for all instances (subgroup restrictions with inherited sequences) on smaller
domains.
* *Intransitive:* chain rule. **[PROVEN]**
* *G^{𝔅₁} semi-regular:* descent to G_{(𝔅₁)} over |G^{𝔅₁}| ≤ |𝔅₁| cosets (Lemma F3), then chain rule
  on the kernel's orbits. **[PROVEN]**
* *|𝔅₁| ≤ d (GNS Lemma 7.2):*
  * Make P = G^{𝔅} primitive by a (P1) coarsening.
  * If |P| ≤ d^{1+log d}, descend. Otherwise, Babai's Lemma 7.1 (P1) gives G′ of index ≤ d (descent),
    and φ : G′ → S_k with ker φ = G′_{(𝒞′)}.
  * If k ≤ 10t, descend to ker φ (≤ k! = 2^{O(log² d)} cosets). **[PROVEN]**
  * Otherwise run the canonical aggregation:
    1. compute local certificates for all t-sets (canonical objects, §3.1);
    2. compute F, S, D and the case split (Lemma F4);
    3. in the case |S| < k/4, build 𝔄(x) by Lemma T, which is strongly canonical with relative
       symmetry defect ≥ 1/4 (Lemma T′), computed by Lemma T″;
    4. in the other cases, build GNS's structures or (Δ, K) (Lemma F4).
  * Then:
    * Option 1: for each branch j (≤ k⁶), canonical subcoset E_j(x) via BC on [k] (Lemma S). The right
      subgroup R_j = φ⁻¹(Aut(𝔄_{j,can}) ∩ φ(G′)) has |φ(G′) : φ(R_j)| ≥ (4/3)^k by GNS Cor. 6.5, since
      the symmetry defect is ≥ 1/4. Recurse in R_j on x^{σ_j}, and combine the branches (Lemma F4).
      **[PROVEN mod BC]**
    * Option 2: Lemma K. **[PROVEN]**
  * Then repeat on the new group, as GNS do (L2104–2131).

*Correctness.* Every step is one of Lemmas F1–F4, S, T, K or R, or a (P1) choice. Each of these maps
canonizers for the sub-instances to a canonizer for the instance. Induction on (domain size, then the
k-potential of the GNS recursion) proves that the output is a C-canonizer. **[PROVEN]**

**Step 4: running time.** **[SKETCH: verbatim transfer of GNS's analysis]**
* The recursion tree of the canonical algorithm has **the same nodes** as GNS's:
  * the same groups, up to conjugation by the canonical transporters;
  * the same domains;
  * the same branch counts at every descent: |G^{𝔅₁}|, |P|, ≤ d, ≤ k!, ≤ k⁶, ≤ 2.
* The only changes:
  * comparisons are replaced by k^t colour computations (Lemma T″), which use fewer recursive sizes;
  * Babai's isomorphism test on structures with ≤ d points and arity t = O(log d) is replaced by BC
    canonization, time exp(O((t log k)^{c₀})) = exp(polylog d) per call, ≤ k⁶ calls per node.
* So GNS Lemma 7.2 holds verbatim. A node makes recursive calls on sizes n_i ≤ n/2 with
  Σn_i ≤ 2^{O(log³ d)}n, plus d^{O((log d)^c)}n^c extra work.
* GNS Lemma 2.8 (the recursion bound) gives |Ω*|^{O(log³ d)}·d^{polylog d} for the almost d-ary
  canonizer on Ω*. With |Ω*| ≤ n^{O(log² d)} this is n^{O((log d)^{c′})}.
* The top-level chain rule over orbits (Step 1) makes ≤ n such calls on disjoint domains. ∎

**Proof of Corollary B.** **[SKETCH: BL83 canonical Luks reduction]**
* Sort the canonical forms of connected components.
* For a connected X, branch over the ≤ nd/2 edges (Lemma F4).
* For a fixed edge, follow Luks's layer-by-layer reduction in its canonical form (BL83; BC §5.6;
  GNS Thm 8.1 cite the same source for the d-independent polynomial overhead). Each layer is one call
  of Theorem A under a coset of a Γ̂_{d−1} group on a domain of size poly(n).
* Total: poly(n)·n^{O((log d)^c)}. ∎

### 4.3 What is new in the proof

| ingredient | status |
|---|---|
| Lemma T (canonical tuple colours) and T′ (exactness, symmetry defect) | new in this application, elementary |
| Lemma T″ (cost, no t-versus-n relation) | new, follows GNS's window analysis |
| Lemma K (find-symmetry with K-collapsed descent) | routine |
| Lemma R (canonical change of action) | routine but needed: GNS's Ω* trick is an equivariant change of action |
| F1–F4, S | standard (BL83, BC §5, §8), restated with fixed conventions |

### 4.4 Residual risks (no known gap)

1. **GNS details not re-derived.**
   * I read the algorithmic parts in full: §§5–7 and App. A. I did not re-verify the group theory
     (Thm 3.13 and its lemmas, Thms 4.3 and 4.6) or the potential argument in Lemma 7.2.
   * The canonical algorithm reuses them unchanged. The only property they need from the replaced step
     is "a family of ≤ k⁶ strongly canonical structures on [k] with relative symmetry defect ≥ 1/4",
     which Lemma T′ supplies.
2. **BC** is a STOC "preliminary report".
   * Used: Theorem 2.2 (string canonization under arbitrary groups in quasipolynomial time), only on
     instances with ≤ d^{O(log d)} positions.
   * Wie20 (Thm `canGraph`) and later work use it the same way.
   * A full version of BC would remove this caveat.
3. **BL83**: the canonical Luks reduction was not re-read. The sketch in §3.1 is standard.
4. **Hidden pairwise steps in GNS.** I checked every place where GNS mention two strings: L1866–1940,
   L1980–1990, L1999–2057, L2370–2385. Nothing else is pairwise. Their Lemma 6.6 is "for i = 1, 2"
   only for presentation.

---

## 5. Babai's logarithmic threshold

### 5.1 Where t ≥ 2 log₂ n enters BC

| place in BC | role | needs |
|---|---|---|
| §6, §9.1: t = max{9, ⌊3 + log₂ n⌋} | Unaffected Stabilizers Lemma (Thm 13.1(a)), for fullness certificates. This is the *isomorphism* algorithm's threshold | m > max{8, 2 + log₂ n}, with m = \|T\| |
| Cor. 13.3 → Lemma 15.1 | the Jordan–Liebeck sandwich S(x) ⊆ T for x ∈ W⁻; the sets Ω(T, u) separate the points of T | binom(t, ⌊t/4⌋) > 2^{t/2} ≥ n ≥ \|orbit\| |
| Prop. 14.2 (+ §11 large window, + transitivity) | Δ(T) determines T, so the string x(T, u) remembers T | stated with t ≥ max{9, 2 log₂ n}, m > 2t, Δ(T) ≠ Ω |

Rows 2 and 3 serve **only** Claim 12.4 (a canonical point u(T) in each asymmetric test set), which
repairs the triviality of the 2t-ary relation R(x) on asymmetric T (Cor. 12.3).

### 5.2 In GNS's regime, and with the trick

**In GNS's regime.**
* Row 1 is replaced by GNS Thm 5.8: t > max{8, 2 + log₂ d}, for groups with almost d-ary sequences.
* Rows 2 and 3 cannot be met:
  * Orbits in W⁻ can have length up to n while t = Θ(log d), so the sandwich of Cor. 13.3 need not
    exist.
  * If d < 20 log₂ n, then t ≥ 2 log₂ n even violates t < k/10 ≤ d/10, so test sets would not fit in the
    ideal domain at all.

  This is precisely why BC's repair "needs t ~ log n".

**With the trick.**
* Lemma T′.3 gives symmetricity ≤ t + 1 directly, for *every* non-full T (asymmetric or not). So Claim
  12.4 and rows 2 and 3 are not needed.
* **The only threshold left is GNS's t > max{8, 2 + log₂ d}.** It is the isomorphism algorithm's own,
  and it does not involve n. **[PROVEN]**

**Remark 5.2 (BC itself).** **[SKETCH]**
* In Babai's own setting, Lemma T with t-tuples, applied to the CP version of the local-certificate
  loop under G_{(T₀)} (BC §16, with the kernel K_i as right subgroup), gives a strongly canonical
  t-ary coloured structure of symmetricity ≤ t − 1. Its cost is m^t ≤ n^{O(log n)}.
* That would replace BC Theorem 12.1, and with it §11 and §§12.4–15.
* This confirms W3's Remark 2.3 in more detail (§1, "Why Babai did not do this").
* It is not needed for Theorem A, and I have not checked it against a full version of BC.

---

## 6. Novelty

| source | statement about n^polylog(d) canonization for degree d / Γ̂_d | checked |
|---|---|---|
| S-W (arXiv 1806.07466, STOC'19) | intro: "For results building on his algorithm [GNS], there are still no known canonization versions." Open questions: GNS "should then be amenable to canonization. However, this remains as future work." | source |
| Wie20 (arXiv 1911.11257, ICALP'20) | intro: GNS, "for which no adequate canonization version is known"; open questions: "whether the bounded-degree isomorphism algorithm of [GNS] extends to canonization". Wie20 uses BC as a black box (Thm `canGraph`) | source |
| Neu20 (arXiv 2002.06997, ICALP'20) | hypergraph isomorphism for Γ̂_d in (n+m)^{polylog d}; **isomorphism only**; it uses the same pairwise comparison structure (L2585–2595) | source |
| Grohe–Neuen–Wiebking, minors (2004.07671); Neuen, topological subgraphs (2011.14730); genus (2106.14869) | isomorphism tests; titles and abstracts contain no canonization | arXiv API |
| Wiebking, dissertation, RWTH 2021 | abstract: a unified canonization framework, "canonization algorithms matching the best isomorphism tests", decompositions improving *isomorphism* tests for treewidth and minors; **bounded degree not mentioned**. The full text was behind a bot wall | abstract only |
| Grohe–Neuen survey (2011.01366), Survey26 | Survey26: "by appropriately extending the tools … Babai obtained a quasipolynomial time canonization … the same is possible for many of the algorithms discussed in this survey"; no degree-d canonization stated | full text |
| GNS SICOMP 2023 | arXiv v3 concluding remarks: open problems are treewidth and FPT; no canonization claim. The SIAM text was not compared | arXiv |
| arXiv API, 2026-11-05 | full author lists of Neuen (38 papers) and Wiebking (7); Schweitzer list; titles with "canonization"/"canonisation"/"canonical labeling" in cs.DS and math.CO since 2019: **no** degree-d canonization | `w4g-arxiv-queries/` |
| web searches (extended, 4 queries) | none found | — |
| HJ (2611.01399) | "Canonization is a separate task"; none | W3 |

**Status.**
* *Theorem A / Corollary B.* To the best of my search, new. They answer the question S-W and Wie20
  leave open.
* *The trick.* Elementary and close to folklore: sending individualized points to reference labels is
  standard in individualization–refinement canonizers. What is new is noticing that it removes the
  pairwise-canonicity obstacle at constant or logarithmic test-set size.
* *Risk.* Experts may regard the result as "expected". S-W and Survey26 both hint so. A short note
  would still be the first written proof.
* *Concurrent work.* None found. Wiebking's thesis should be checked in full before any public claim.

---

## 7. Leads (ranked)

1. **Have it refereed internally.** Ask an independent agent to red-team §1.2, §3.4, §4.2, with special
   attention to:
   * GNS Lemma 7.2's potential under canonical right subgroups;
   * whether GNS's aggregation (App. A) ever uses x₂-dependent information in the |S| ≥ k/4 cases.
2. **Treewidth canonization in n^{polylog k}.**
   * Wie20 says its treewidth isomorphism algorithm "should then be amenable to canonization" once GNS
     is. Its only non-canonical import is GNS's coset-restricted graph isomorphism (Wie20 Thm
     `boundedDegree`), and Corollary D is exactly its canonical twin.
   * Plausible next theorem: canonical forms for treewidth-k graphs in n^{polylog k}.
     **[SPECULATION]**: Wie20's other components are canonical by construction (S-W framework).
3. **Canonical Neu20, then canonical GNW (minors) and Neuen (topological subgraphs) in n^{polylog h}.**
   Neu20's aggregation has the same pairwise structure (L2585–2595), so Lemma T should apply verbatim.
   **[SPECULATION]**
4. **BC simplification (Remark 5.2).** If correct, BC's §§11–15 become unnecessary. Worth a careful
   check against Babai's full version if one exists.
5. **HJ-canon (W3).** Lemma T is W3's Lemma 2.1 in a cleaner form (a special case of Lemma S). W3's
   conditional Theorem C inherits Lemmas F2 and S from this memo; this closes W3's §2.2 convention gap.

---

## 8. Ledger

| item | status |
|---|---|
| Lemma S (canonical subcoset) | **[PROVEN]** |
| Lemma T (tuple colours), T′ (strong canonicity, exactness, symmetry defect) | **[PROVEN]** (T′ uses GNS's local-certificate facts) |
| Lemma T″ (colour cost ≤ k^t·n recursive sizes) | **[PROVEN mod GNS Thm 5.9]** |
| Lemmas F1–F4 (restriction, sequential chain rule, descent, branch families) | **[PROVEN]** |
| Lemma R (canonical change of action) | **[PROVEN]** |
| Lemma K (canonical find-symmetry) | **[PROVEN]** |
| component table §3.1 | **[PROVEN]** row by row, except the Luks reduction (cited/SKETCH) and the recursion transfer (SKETCH) |
| Theorem A | **[PROVEN mod GNS lemmas, BC, canonical generating sets]**; running time **[SKETCH, verbatim transfer]** |
| Corollary B | as Theorem A, plus BL83 **[SKETCH]** |
| Corollaries C, D | as Theorem A |
| §5: Babai's threshold is used only in Claim 12.4, and is not needed | **[PROVEN]** |
| Remark 5.2 (BC simplification) | **[SKETCH]** |
| novelty | §6: open in the literature as far as checked; thesis full text unread |
| no Lean, no solver, no benchmark; CPU negligible | — |
