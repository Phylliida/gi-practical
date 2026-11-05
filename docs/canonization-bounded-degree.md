# Canonical forms for graphs of maximum degree d in time n^{O((log d)^c)}

Draft for expert checking. Branch `w5-writeup`, 2026-11-05. Not refereed. Builds on
`docs/w4-gnscanon.md` (the derivation, "memo") and `docs/redteam-w4-gnscanon.md` (the adversarial
check, "red-team"); see `docs/w3-canon.md` for the origin.

---

## Status of this draft (read first)

| item | status |
|---|---|
| Theorem A (strings under Γ̂_d groups) | proved here, modulo the results listed in §10 |
| Corollary B (graphs of maximum degree d) | proved here; the canonical Luks reduction is written out in full (§8), following Babai–Luks 1983 §4.2–4.3, which was obtained and read for this draft |
| running-time analysis | written out in full (§7) |
| **new problem found** | **[GAP-1] in the GNS paper itself.** The written potential argument in the proof of GNS Lemma 7.2 (repeated verbatim in Neuen, arXiv:2002.06997) asserts H′_{(𝒞′)} ≤ ker φ′. For the algorithm as written this is false: §7.2 gives an explicit input on which the next giant degree k′ equals k. The gap affects the GNS isomorphism test exactly as much as the canonical version. It has an evident fix: keep 𝒞′ as the top partition of the child instance. GNS's remark "recall that 𝒞′ is G′-invariant and thus also H-invariant" suggests this is what they intended. We build the fix into the algorithm (§6.2, step 6); with it, GNS's inequality k′ ≤ k − k/(3 log k) holds (§7.3). We regard this as closed, but it is the first thing a referee should check. |
| minor imprecision | [GAP-2, closed] GNS Lemma 2.8 does not literally cover the semi-regular Luks step, whose recursive sizes sum to b·n with b unbounded. §7.1 states and proves a recursion lemma that covers it. |
| blank symbol | handled by explicit membership tags (§2.5); no freshness assumption is needed |
| treewidth n^{polylog k} canonization | **remark only** (§9.2). Wiebking's treewidth algorithm needs more than GNS canonization. |
| LaTeX version `paper/canon.tex` | **not written** (time); the Markdown uses standard notation and converts mechanically |
| computation | none; no Lean |

Line references "G L…" are to `bounded-degree-polylog-d.tex` of arXiv:1802.04659v3 (GNS).
Result numbers "GNS 7.2" etc. are those of the same version (computed from its LaTeX source).
"BL83" is Babai–Luks, STOC 1983 (OCR copy from Luks's homepage, `ix.cs.uoregon.edu/~luks/CanLabel.pdf`).
"BC" is Babai, STOC 2019. "Thesis" is Wiebking's dissertation (RWTH 2021).

---

## Abstract

Grohe, Neuen and Schweitzer (FOCS 2018; SIAM J. Comput. 2023) showed that isomorphism of graphs of
maximum degree d can be decided in time n^{O((log d)^c)}. Whether canonical forms can be computed
within the same bound was posed as open by Schweitzer and Wiebking (STOC 2019) and by Wiebking
(ICALP 2020), and it is Question 9.6 of Wiebking's dissertation (2021). We answer it. For every group
G ≤ Sym(Ω) all of whose composition factors embed in S_d, we compute a canonical labelling of strings
x : Ω → Σ under G (or under a coset of G) in time n^{O((log d)^c)}, n = |Ω|. With a canonical
version of Luks's reduction, written out following Babai and Luks (1983), this gives canonical forms
for n-vertex graphs of maximum degree d in time n^{O((log d)^c)}.

In the GNS algorithm exactly one step is pairwise: the comparison of local certificates of two input
strings, used to build a t-ary relational structure on the ideal domain. We replace it by a
canonical-subcoset device: move an ordered test tuple to a reference tuple chosen from the current
group alone, and canonize under the pointwise stabilizer of the reference tuple. Wiebking used a
canonical test set over an ordered group in a different role (Thesis, Lemma 5.34). The remaining
steps of GNS canonize with the Babai–Luks toolkit. Along the way we point out, and repair, a gap in
the written potential argument of GNS (Lemma 7.2).

---

## 1. Introduction

### 1.1 The problem

A *canonical form* for a class of graphs assigns to each graph X a graph CF(X) on {1,…,n} such that
CF(X) ≅ X, and X ≅ Y implies CF(X) = CF(Y). A *canonical labelling* is a bijection λ with
X^λ = CF(X). Canonical forms solve isomorphism, and they also allow hashing, database lookup, and
recursive use inside other canonization algorithms. That last use is why the decomposition framework
of Schweitzer and Wiebking needs canonical forms, not isomorphism tests.

History.
* Luks (1982): isomorphism for maximum degree d in n^{O(d)}, via string isomorphism under groups in
  Γ̂_d.
* Babai–Luks (1983) and Fürer–Schnyder–Specker (1983): canonical forms for bounded degree, by making
  Luks's algorithm canonical (BL83 Theorem 4.2: n^{O(d)}).
* Babai (2016): isomorphism in quasipolynomial time. Babai (STOC 2019, "BC"): canonical forms in
  quasipolynomial time. BC explains that the core of the 2016 algorithm, the t-ary structure built
  from local certificates, is only *pairwise* canonical. Repairing it is BC's main new contribution
  (BC Thm 12.1).
* Grohe–Neuen–Schweitzer (2018, "GNS"): isomorphism for maximum degree d in n^{O((log d)^c)}. GNS
  reuse Babai's local-certificate aggregation, so the same pairwise step appears.
* Open-problem statements:
  * Schweitzer–Wiebking (arXiv:1806.07466, STOC 2019): canonization for GNS "remains as future
    work".
  * Wiebking (arXiv:1911.11257, ICALP 2020): "whether the bounded-degree isomorphism algorithm of
    [GNS] extends to canonization as well".
  * Thesis p. 242: "The only isomorphism test we use for which no canonization algorithm is known so
    far is the isomorphism test for bounded-degree graphs given by Grohe, Neuen and Schweitzer
    [GNS18] and its extension to hypergraphs [Neu20a]." This is followed by **Question 9.6**: "Can
    canonical labelings for graphs with n vertices be computed in time n^{polylog(k)} where k is the
    maximum degree of G?"

BC's repair cannot simply be transplanted. It needs test sets of size t ≥ 2 log₂ n (BC Cor. 13.3,
Prop. 14.2, used for Claim 12.4), whereas GNS work with t = Θ(log d) < k/10 ≤ d/10. When d < 20 log₂ n,
test sets of size 2 log₂ n do not even fit into the ideal domain (red-team §7).

### 1.2 Results

**Theorem A.** There is an algorithm that, given G ≤ Sym(Ω) with G ∈ Γ̂_d (by generators), σ ∈ Sym(Ω)
and a string x : Ω → Σ, outputs a canonical form F_{σG}(x) and the canonical placement coset
Λ_{σG}(x) = {g ∈ σG : x^g = F_{σG}(x)} (Definition 2.1). It runs in time n^{O((log d)^c)}, where
n = |Ω| and c is an absolute constant.

**Corollary B.** Canonical forms and canonical labellings of n-vertex graphs of maximum degree d can
be computed in time n^{O((log d)^c)}.

**Corollary D.** Given a graph (or string) on V and a labelling coset Δρ with Δ ∈ Γ̂_d, a canonical
labelling coset with respect to Δρ can be computed in time |V|^{O((log d)^c)}. This is the canonical
twin of the form in which Wiebking (ICALP 2020, Thm "boundedDegree") imports GNS.

### 1.3 The new step and its provenance

The only pairwise step of GNS is in the proof of Lemma 6.6 (Appendix A, G L2366–2385), in the case
where the fullness group has small support. GNS define a "category" whose objects are test sets of
*both* strings. Its morphisms are the bijections produced by Lemma 6.3 (CompareLocalCertificates). The
equivalence classes on ordered t-tuples of D₁ ⊔ D₂ then give the relations of the two t-ary
structures. The classes are named jointly, so the structure built for x₁ depends on x₂.

We instead colour each ordered t-tuple T⃗ of the non-full region D(x) by

> c_x(T⃗) := the canonical form, under the pointwise stabilizer J₀ of a reference tuple T⃗₀, of the
> windowed certificate string of (T, x) transported by any σ ∈ G′ with T⃗^{φ(σ)} = T⃗₀.

T⃗₀ is a function of the current group alone (the first t labels of the ideal domain). Lemma T shows
that c_x is well defined and equivariant, and that it separates orbits of marked pairs. Lemma T′ shows
that the resulting structure is strongly canonical and has relative symmetry defect ≥ 3/4. Lemma T″
shows that all colours together cost at most k^t·n in recursive sizes. No relation between t and n is
needed.

**Credit.**
* The device "send a tuple to a reference tuple chosen from the group alone, then canonize under its
  pointwise stabilizer" is a special case of the canonical-subcoset step of the Babai–Luks framework
  (Lemma S below; BL83 §2; BC §5).
* Its use with a *canonical test set* over an ordered group appears in Wiebking's thesis, Lemma 5.34
  (algorithm ProdCert, pp. 101–103): "In our framework, we define the giant representation … for a
  group over a linearly ordered set V^can. This allows us to choose one single (canonical) test set
  T^can ⊆ W^can only." There it produces fullness certificates and partition families for *multiple
  labelling cosets*, at cost |V|^{polylog|V|}, not a non-fullness structure in GNS's regime.
* Babai (BC, comment after Claim 12.4) notes that a strongly canonical choice "is obvious: we just
  pick … for one representative of each G-isomorphism class … and use G to translate it … Making
  this selection efficient is our problem." BC's "right descent" (end of §16) transports test sets in
  the same way.

What is new here is the observation that, at a fixed reference *ordered* tuple, this device turns
GNS's non-fullness comparison classes into canonical colours at test-set size Θ(log d). That is
enough to settle Question 9.6.

### 1.4 A remark on the GNS analysis

While writing out the running time we found that one step of GNS's potential argument (proof of
Lemma 7.2, G L2118–2134) does not hold for the algorithm as written (§7.2). The fix is one line: make
the partition 𝒞′ the top partition of the child instance. The fixed analysis is §7.3.

### 1.5 Organisation

* §2: preliminaries and a recap of GNS.
* §3: framework lemmas.
* §4: Lemma S and Lemma T.
* §5: canonical aggregation.
* §6: the algorithm and its correctness, including the 17 choice points.
* §7: running time.
* §8: Corollary B.
* §9: further consequences.
* §10: assumptions taken from the literature.
* §11: flags.
* §12: related work.
* §13: questions for experts.

---

## 2. Preliminaries

### 2.1 Conventions

* All domains Ω are finite and **linearly ordered**. Sym(Ω) acts on the right: α^{gh} = (α^g)^h.
* A string is x : Ω → Σ, where Σ is a finite, linearly ordered alphabet. G acts on strings by
  x^g(α) = x(α^{g⁻¹}), so (x^g)^h = x^{gh}.
* Strings on the same domain are compared lexicographically, along the order of Ω.
* Aut_H(x) = {h ∈ H : x^h = x} and Iso_H(x, y) = {h ∈ H : x^h = y}.
* For W ⊆ Ω, Iso^W_K(x, y) = {g ∈ K : x(α) = y(α^g) for all α ∈ W} (GNS §2.2.3).

### 2.2 Canonizers

**Definition 2.1.** Let H ≤ Sym(Ω), and let 𝒳 be an H-invariant set of strings. An *H-canonizer on 𝒳*
assigns to each x ∈ 𝒳 a string F_H(x) and a set Λ_H(x) ⊆ H such that:
* (C1) Λ_H(x) = {h ∈ H : x^h = F_H(x)} ≠ ∅;
* (C2) F_H(x^h) = F_H(x) for all h ∈ H.

**Lemma 2.2 (consequences).** For every H-canonizer:
1. Λ_H(x^h) = h⁻¹Λ_H(x).
2. Λ_H(x) = Aut_H(x)λ = λAut_H(F_H(x)) for every λ ∈ Λ_H(x). We call Aut_H(F_H(x)) the *right
   subgroup*.
3. Iso_H(x, y) = Λ_H(x)Λ_H(y)⁻¹ if F_H(x) = F_H(y), and ∅ otherwise.

*Proof.* Direct from (C1) and (C2). ∎

A canonizer is represented by one element of Λ and generators of the right subgroup.

**Cosets.** For C = σH put F_C(x) := F_H(x^σ) and Λ_C(x) := σΛ_H(x^σ). By (C2) this does not depend
on σ, and Λ_C(x) = {g ∈ C : x^g = F_C(x)}. This is BL83 §2.1 ("CF(X, σG) := CF(X^σ, G)") and BC
Def. 5.1(i).

**Remark 2.3 (labelling cosets).** Schweitzer–Wiebking work with labelling cosets Δρ ⊆ Bij(V, [n]).
Put H := ρ⁻¹Δρ ≤ Sym([n]); this depends only on Δρ. Then CL(x, Δρ) := ρΛ_H(x^ρ) satisfies their
(CL1) and (CL2), and conversely. BL83's CL(X, σG) with properties (I) and (II), and BL83's Lemma 2.1,
are the same notion. All three formalisms are interchangeable. We use Definition 2.1.

### 2.3 The class Γ̂_d

Γ̂_d is the class of groups all of whose composition factors are isomorphic to subgroups of S_d (GNS
Def. 2.3), i.e. groups of composition width ≤ d. It is closed under subgroups and homomorphic images
(GNS Lemma 2.4) and under extensions. A group of degree n lies in Γ̂_n, so we may assume d ≤ n.

### 2.4 Choices that are functions of the group (principle P1)

The output F_H(x) must depend on H only as a *set*. All auxiliary choices are therefore made by
deterministic procedures run on a **canonical generating set**, i.e. a generating set that depends
only on H ≤ Sym(Ω) for ordered Ω and is computable in polynomial time:
* Allender–Grochow–van Melkebeek–Moore–Morgan (2018), Lemma 6.2;
* Grohe–Neuen–Schweitzer–Wiebking (arXiv version), Lemma 21;
* Schweitzer–Wiebking (arXiv:1806.07466), Lemma `canGen`.

Concretely, one takes the lexicographically least coset representatives along the point-stabilizer
chain of the ordered domain.

Choices made this way include:
* block systems;
* Babai's giant representation (GNS Lemma 7.1) and the labelling of its ideal domain [k];
* reference tuples;
* lexicographically least elements of cosets (computable in polynomial time);
* every derived domain (Ω*, [k]^t, slot domains), each with a linear order computed from the group.

We write "(P1)" for such a choice. **Groups computed along different routes, for example as right
subgroups of canonizer calls on different inputs, must be re-normalized to canonical generators
before any P1 choice.**

### 2.5 Windowed and layered strings; the blank-symbol condition

For W ⊆ Ω we define the *windowed string* x^{[W]} with an explicit membership tag:

x^{[W]}(α) = (1, x(α)) if α ∈ W, and (0, ∗) otherwise.

So x^{[W]} determines W, whatever Σ is. This is the "fresh blank" requirement of the red-team (§2.3
there), made explicit. BC (§5.1) uses a dummy symbol β ∉ Σ.

For a chain ∅ = U₀ ⊂ U₁ ⊂ … ⊂ U_r, the *layered string* x^{⟨U_r⟩} records the layer index:

x^{⟨U_r⟩}(α) = (i, x(α)) for α ∈ U_i ∖ U_{i−1}, and (0, ∗) for α ∉ U_r.

Why the tag matters:
* (a) Aut_H(x^{[W]}) = {h ∈ H : W^h = W and x(α^h) = x(α) for α ∈ W}. With an untagged blank that
  occurs in Σ, h need not stabilize W.
* (b) It is needed for the identity G_{i*}(T, x) = Aut_{H_T}(x^{[W(T,x)]}) used in Lemma T′(2).
* (c) It is needed so that Lemma T(c), applied to windowed strings, means "the same window and the
  same values on it".

Recursive calls never receive windowed strings. They receive restrictions x|_V to invariant sets
(Lemma F1), so alphabets do not grow along the recursion. Canonical forms of layered strings live
over Σ × ℕ, with a fixed order.

### 2.6 The GNS framework (recap, with the facts we use)

**Almost d-ary sequences (GNS Def. 4.1, Obs. 4.2).**
* A G-invariant sequence {Ω} = 𝔅₀ ≻ 𝔅₁ ≻ … ≻ 𝔅_m = discrete is *almost d-ary* if, for every i and
  every B ∈ 𝔅_{i−1}, either G_B acts semi-regularly on 𝔅_i[B], or |𝔅_i[B]| ≤ d.
* Such a sequence is inherited by subgroups and by restrictions to invariant subsets (Obs. 4.2).
* Inserting a G-invariant partition 𝒫 between 𝔅_{i−1} and 𝔅_i keeps the sequence almost d-ary,
  provided each class of 𝔅_{i−1} contains ≤ d classes of 𝒫 and each class of 𝒫 contains ≤ d classes
  of 𝔅_i, or the corresponding actions are semi-regular. (Immediate from the definition.)

**Change of action (GNS Thms 4.3, 4.6).** For transitive G ∈ Γ̂_d there are:
* a set Ω* with |Ω*| ≤ n^{(c₁ log d + c₂ + 1) log d};
* a homomorphism ι : G → Sym(Ω*), g ↦ g*, with image G* carrying an almost d-ary G*-invariant
  sequence;
* a map x ↦ x* on strings.

The proofs (G L1131–1178, L1207–1213, L1452–1530) give the following facts, used in Lemma R:
* (x^g)* = (x*)^{g*}, because x*((Nh, α)) = x(α), resp. x*((α, v̄)) = x(α);
* x ↦ x* is injective, because every α ∈ Ω occurs as a second coordinate, also after restriction to
  one G*-orbit A* (G is transitive).

**Giant representations, affected points (GNS Def. 5.6).**
* φ : H → S_k is a giant representation if φ(H) ≥ A_k.
* α is affected if φ(H_α) ≱ A_k. Aff(H, φ) denotes the set of affected points.
* For B ≤ H, Aff(B, φ) is B-invariant.
* Aff is equivariant: Aff(B^h, φ^h) = Aff(B, φ)^h.

**GNS Thm 5.8 (unaffected stabilizers, almost d-ary version).** If H has an almost d-ary sequence,
k > max{8, 2 + log₂ d}, and D is the set of unaffected points, then φ(H_{(D)}) ≥ A_k.

**GNS Thm 5.9 (= Babai 2016, Thm 6(b)).** For k ≥ 5, each orbit of ker φ inside an affected H-orbit Δ
has length ≤ |Δ|/k.

**Local certificates (GNS Def. 6.1, Alg. 2, Lemma 6.2).** Fix a node group H with a giant
representation φ and a t-set T ⊆ [k]. Put H_T := φ⁻¹(φ(H)_T) and let ψ_T : H_T → Sym(T) be the
restriction. The *window chain* is defined by:
* G₀ := H_T and W₀ := ∅;
* while ψ_T(G_i) ≥ Alt(T) and W_i ≠ Aff(G_i, ψ_T): W_{i+1} := Aff(G_i, ψ_T) and
  G_{i+1} := Aut^{W_{i+1} ∖ W_i}_{G_i}(x).

Let i* be the final index. Put W(T, x) := W_{i*} and G(T, x) := G_{i*}. We use:

* (L1) G_i = Aut^{W_i}_{H_T}(x). [GNS proof of 6.2]
* (L2) G_i stabilizes W₁, …, W_{i+1} setwise, because W_{j+1} = Aff(G_j, ψ_T) is G_j-invariant and
  G_i ≤ G_j. Hence G_i = Aut_{H_T}(x^{⟨W_i⟩}) = Aut_{H_T}(x^{[W_i]}), using the tags of §2.5.
* (L3) T is *full* if ψ_T(Aut_{H_T}(x)) ≥ Alt(T).
  * If T is full, every G_i contains Aut_{H_T}(x), so the loop ends with W_{i*} = Aff(G_{i*}). Then
    K(T, x) := (G_{i*})_{(Ω∖W)} ≤ Aut_{H_T}(x) is a fullness certificate (Thm 5.8).
  * If T is not full, the window grows strictly until ψ_T(G_i) is not a giant. Otherwise Thm 5.8
    would make T full (GNS proof of 6.3, G L1931–1934).
  * So: **T is non-full iff ψ_T(G(T, x)) is non-giant.**
* (L4) Equivariance. For h ∈ H: W_i(T^{φ(h)}, x^h) = W_i(T, x)^h and G_i(T^{φ(h)}, x^h) = G_i(T, x)^h.
  Hence W, G and K are equivariant, and fullness is invariant. This holds by induction on i, using
  H_{T^{φ(h)}} = (H_T)^h and equivariance of Aff.
* (L5) Cost (GNS Lemma 6.2). For one T: recursive calls of sizes ≤ n/2 summing to ≤ t!·n, plus
  O(t!·n^c) work. The large-window step uses Thm 5.9.

**Symmetry defect (GNS §6.3).**
* The symmetry defect of A ≤ Sym(Γ) is |Γ| − max{|Δ| : Alt(Δ) ≤ A}. The relative defect divides
  this by |Γ|.
* **GNS Cor. 6.5** (from Dixon–Mortimer Thm 5.2A,B): if A_k ≤ S ≤ S_k, k ≥ 24, A ≤ S, and the
  relative symmetry defect of A is ≥ 1/4, then |S : A| ≥ (4/3)^k.

**Aggregation (GNS Lemma 6.6, App. A); find-structure (6.7); find-symmetry (6.9).** Recapped and made
canonical in §5.

**GNS Lemma 7.1 (= Babai 2015, Thm 3.2.1).** For primitive P ≤ S_b with |P| ≥ b^{1+log b} (b larger
than an absolute constant), one computes in polynomial time:
* N ⊴ P with |P : N| ≤ b;
* an N-invariant equipartition 𝒞 of [b];
* a giant representation ψ : N → S_k with k ≥ log b and ker ψ = N_{(𝒞)}.

**GNS Lemma 7.2 and Alg. 4.** The algorithm handles three cases:
* G intransitive: orbit by orbit.
* G^{𝔅₁} semi-regular: Luks reduction.
* Otherwise (|𝔅₁| ≤ d):
  * coarsen 𝔅₁ to 𝔅 with P = G^𝔅 primitive;
  * if |P| ≤ d^{1+log d}, Luks;
  * otherwise apply Lemma 7.1, set G′ := {g : g^𝔅 ∈ N} (index ≤ d) and
    φ := ψ ∘ (action on 𝔅), so ker φ = G′_{(𝒞′)}, where 𝒞′ is the lift of 𝒞 to Ω;
  * put t := max{9, 3 + log d}; if k ≤ 10t, Luks to ker φ;
  * otherwise aggregate, and recurse on ≤ k⁶ groups H ≤ G′ with |φ(G′) : φ(H)| ≥ (4/3)^k.

The analysis is in §7.

---

## 3. Framework lemmas

All of these are standard (BL83 §2; BC §§5, 8). We restate them in the conventions of §2 and prove
them, because the left/right conventions matter.

**Lemma F1 (restriction).** Let U be H-invariant and let ρ_U : H → H^U be restriction. If
(F′, Λ′) is an H^U-canonizer for x|_U, then x ↦ (F′, ρ_U⁻¹(Λ′)) is an H-canonizer for x^{[U]}. Its
right subgroup is Aut_H(x^{[U]}). It is computable in polynomial time (preimage of a coset; GNS
Thm 2.1(6)).

*Proof.* h ∈ H maps x^{[U]} to the tagged extension of F′ iff ρ_U(h) maps x|_U to F′. ∎

**Lemma F2 (sequential chain rule with input-dependent windows).**
* *Setting.*
  * Windows V_{i+1} are given as functions of the layered string x^{⟨U_i⟩}, with
    V_{i+1} ⊆ Ω ∖ U_i.
  * They are H-equivariant: V_{i+1}(y^h) = V_{i+1}(y)^h.
  * U_{i+1} := U_i ⊔ V_{i+1}.
  * The number of layers r(x) is also equivariant.
* *Recursion.* Given an H-canonizer (F_i, Λ_i) for x^{⟨U_i⟩}:
  * pick τ ∈ Λ_i and put w := x^τ;
  * put A_i := Aut_H(F_i) and V′ := V_{i+1}(F_i), which is A_i-invariant;
  * let (F′, Λ′) be an A_i-canonizer of w^{[V′]};
  * put F_{i+1} := F_i overwritten on V′ by F′ with layer tag i+1, and Λ_{i+1} := τΛ′.
* *Claim.* (F_{i+1}, Λ_{i+1}) is an H-canonizer for x^{⟨U_{i+1}⟩}.

*Proof.*
* *Independence of τ.* Replacing τ by τa (a ∈ A_i) replaces w by w^a. Since V′^a = V′, F′ is
  unchanged and Λ′ becomes a⁻¹Λ′.
* *(C2).* Λ_i(x^h) = h⁻¹Λ_i(x), so for x^h we may use τ′ = h⁻¹τ, which gives the same w.
* *(C1) ⊆.* Let a ∈ Λ′. Then (x^{⟨U_i⟩})^{τa} = F_i^a = F_i, and
  V_{i+1}(x^{⟨U_i⟩})^τ = V_{i+1}(F_i) = V′, so (x^{[V_{i+1}]})^{τa} = (w^{[V′]})^a = F′.
* *(C1) ⊇.* If h maps x^{⟨U_{i+1}⟩} to F_{i+1}, the layer tags force (x^{⟨U_i⟩})^h = F_i, so
  h = τa with a ∈ A_i, and (w^{[V′]})^a = F′, so a ∈ Λ′. ∎

The *ordinary chain rule* is the special case where the windows are the orbits of the current right
subgroup, ordered by (size, least point) (P1), each handled by Lemma F1. Processing the H-orbits of
an intransitive H this way is GNS Alg. 1.

**Lemma F3 (descent).** Let K ≤ H with H = ⊔_{ρ∈R} ρK. Put m := min_ρ F_K(x^ρ) and
Λ_H(x) := ⋃_{ρ : F_K(x^ρ) = m} ρΛ_K(x^ρ). This is an H-canonizer, and Λ_H(x) = {h ∈ H : x^h = m}.

*Proof.*
* *(C2).* For x^h the branch values are F_K(x^{hρ}). The cosets hρK run over all left cosets of K,
  and F_K is constant on K-orbits, so the set of branch values is unchanged.
* *(C1).* Every ρλ in the union maps x to m. Conversely, let x^{ρk} = m. Then m lies in the K-orbit
  of x^ρ, and m = F_K(x^{ρ₀}) for a minimizer ρ₀, so F_K(m) = m. Hence F_K(x^ρ) = m and
  k ∈ Λ_K(x^ρ). ∎

The output depends only on the branch values. Branches whose values are known to coincide need not be
evaluated separately; Lemma K uses this. The right subgroup is generated by Aut_K(m) and one element
λ₁⁻¹ρ_jλ_j per minimizing branch.

**Lemma F4 (equivariant branch families).**
* *Setting.* x ↦ 𝔉(x) is a finite family of objects with 𝔉(x^h) = 𝔉(x)^h, and there is an
  H-canonizer for pairs (x, b).
* *Definition.* F := min_{b ∈ 𝔉(x)} F_H(x, b), with first component F^x, and Λ_H(x) := the union of
  Λ_H(x, b) over the minimizing b.
* *Claim.* Λ_H(x) = {h : x^h = F^x}, so this is an H-canonizer for x.

*Proof.* Let x^h = F^x. Then 𝔉(F^x) = 𝔉(x)^h contains the second component F^b of F. Put
b := (F^b)^{h⁻¹}. Then (x, b)^h = F, so F_H(x, b) = F and b minimizes. ∎

**Lemma R (change of action).**
* *Setting.* ι : G → Sym(Ω*), g ↦ g*, is a homomorphism, and x ↦ x* is injective with
  (x^g)* = (x*)^{g*}. A G*-canonizer for ι(G) on {x*} is given.
* *Definition.* Λ_G(x) := ι⁻¹(Λ_{G*}(x*)), and F_G(x) := the unique y with y* = F_{G*}(x*).
* *Claim.* This is a G-canonizer.

*Proof.*
* *y exists.* F_{G*}(x*) = (x*)^{g*} = (x^g)* for some g ∈ G.
* *(C1).* g ∈ Λ_G(x) ⟺ (x^g)* = F_{G*}(x*) = (F_G(x))* ⟺ x^g = F_G(x), by injectivity.
* *(C2).* From (C2) for G* and equivariance. ∎

*Application.* GNS's Ω*, G*, the almost d-ary sequence and the order on Ω* are computed from G alone
(P1, choice points 1–5 in §6.4).

---

## 4. The canonical subcoset lemma and tuple colours

**Lemma S (canonical subcoset).**
* *Setting.*
  * H ≤ Sym(Ω), and φ : H → Sym(Γ) is a homomorphism.
  * 𝒮 is a φ(H)-invariant set of structures on Γ, with a φ(H)-canonizer Λ′. Write
    S_can := S^{Λ′(S)}.
  * x ↦ S(x) ∈ 𝒮 satisfies S(x^h) = S(x)^{φ(h)}.
  * For R := φ⁻¹(Aut_{φ(H)}(S_can)), an R-canonizer is available on the strings x with
    S(x) = S_can.
* *Definition.* E(x) := φ⁻¹(Λ′(S(x))). This is a left coset σR, and we put Λ_H(x) := Λ_{σR}(x),
  i.e. F_H(x) := F_R(x^σ).
* *Claim.* This is an H-canonizer, with right subgroup Aut_R(F_H(x)).

*Proof.*
* *Shape of E(x).* Λ′(S) = π·Aut_{φ(H)}(S_can), so E(x) = σR.
* *Equivariance.* Λ′(S^π) = π⁻¹Λ′(S) gives E(x^h) = h⁻¹E(x).
* *(C2).* For x^h, the representative h⁻¹σ gives F_R(x^{hh⁻¹σ}) = F_R(x^σ).
* *(C1) ⊆.* e ∈ Λ_{E(x)}(x) satisfies x^e = F_H(x).
* *(C1) ⊇.* Suppose x^h = F := F_H(x). We have F = x^e for some e ∈ E(x), so
  S(F) = S(x)^{φ(e)} = S_can. Then S(x)^{φ(h)} = S(F) = S_can, so φ(h) ∈ Λ′(S(x)) and h ∈ E(x).
  Hence h ∈ Λ_{E(x)}(x). ∎

**Lemma T (tuple colours).**
* *Setting.*
  * H and φ : H → Sym(Γ) as above. T⃗₀ is an injective t-tuple of Γ chosen by (P1).
  * 𝒪 := T⃗₀^{φ(H)}, i.e. φ(H) is transitive on 𝒪.
  * J₀ := {h ∈ H : T⃗₀^{φ(h)} = T⃗₀}.
  * 𝒴 is an H-invariant set of strings, and F_{J₀} is a J₀-canonizer on 𝒴.
* *Definition.* For y ∈ 𝒴 and T⃗ ∈ 𝒪, put c(y, T⃗) := F_{J₀}(y^σ) for any σ ∈ H with
  T⃗^{φ(σ)} = T⃗₀.
* *Claim.*
  * (a) c is independent of σ.
  * (b) c(y^h, T⃗^{φ(h)}) = c(y, T⃗) for all h ∈ H.
  * (c) c(y, T⃗) = c(y′, T⃗′) iff there is h ∈ H with y^h = y′ and T⃗^{φ(h)} = T⃗′.

*Proof.* This is Lemma S with S(y, T⃗) := T⃗ and Λ′(T⃗) := {π ∈ φ(H) : T⃗^π = T⃗₀}; then R = J₀.
Directly:
* (a) Two valid σ, σ′ differ by σ⁻¹σ′ ∈ J₀, and F_{J₀} is constant on J₀-orbits.
* (b) h⁻¹σ is valid for (y^h, T⃗^{φ(h)}).
* (c) "If" is (b). For "only if": equal canonical forms give j ∈ J₀ with y^{σj} = y′^{σ′}. Take
  h := σjσ′⁻¹. Then y^h = y′ and T⃗^{φ(h)} = T⃗₀^{φ(jσ′⁻¹)} = T⃗′. ∎

*The two naive variants fail* (red-team §1.4, with explicit counterexamples):
* without transport (c := F_{H_{(T⃗)}}(y)), (C2) fails;
* with a reference tuple read off a coset representative, strong canonicity fails.

Our T⃗₀ depends only on the right subgroup (P1).

---

## 5. Canonical aggregation

Throughout this section:
* the node group is H (in the algorithm, H = G′ of Lemma 7.2), with an almost d-ary sequence;
* φ : H → S_k with φ(H) ∈ {A_k, S_k};
* t := max{9, 3 + ⌈log₂ d⌉} and k > 10t (so k ≥ 100);
* the ideal domain [k] is ordered (P1).

### 5.1 Local certificates are canonical objects

**Lemma 5.1.** For every t-set T ⊆ [k], the following can be computed with the same recursive budget
as GNS Lemma 6.2 (L5):
* the chain (W_i(T, x), G_i(T, x)), the fullness of T, and K(T, x) for full T.

All of these are set-theoretic functions of (H, φ, T, x), and they are equivariant (L4). In
particular, the way the groups are computed does not affect canonicity.

*Proof.* G_{i+1} = Aut_{G_i}(x^{[W*]}), where W* := W_{i+1} ∖ W_i is G_i-invariant (L2). This is the
right subgroup of a G_i-canonizer of x|_{W*} (Lemma F1).
* If |W*| ≤ n/2: one recursive call on W* under G_i^{W*}. The almost d-ary sequence is inherited.
* Otherwise: descent (F3) from G_i to N := ker ψ_T|_{G_i}, over ≤ t! cosets. In each branch, the
  chain rule over the N-orbits in W*; each has size ≤ |W*|/t by Thm 5.9, since W* is a union of
  affected G_i-orbits.

These are exactly GNS's counts (≤ t! calls per orbit). ∎

### 5.2 The fullness group and the case analysis

Put F(x) := ⟨K(T, x) : T full⟩ ≤ Aut_H(x) and S(x) := supp(F(x)^φ) ⊆ [k]. Both are equivariant: by
(L4), F(x^h) = F(x)^h and S(x^h) = S(x)^{φ(h)}. Following App. A of GNS, but canonically:

| case | GNS (App. A) | canonical object | count |
|---|---|---|---|
| (i) k/4 ≤ \|S\| ≤ 3k/4 | colouring by S | 𝔄 = ([k]; S) | r = 1 |
| (ii) \|S\| > 3k/4, no F^φ-orbit ≥ 3k/4 | orbit partition | 𝔄 = ([k]; orbit partition) | r = 1 |
| (iii) \|S\| > 3k/4, orbit C ≥ 3k/4, F^φ\|_C ≥ Alt(C) | Option 2 | Δ(x) := C, K(x) := F(x) | — |
| (iv) as (iii), F^φ\|_C non-giant | individualize I (\|I\| = deg. of transitivity − 1 ≤ 4, by CFSG, GNS Thm A.2), one non-diagonal orbital R of (F^φ)_{(I)} on C′ = C∖I, possibly a vertex v | the **family of all** structures over all choices of (I, R, v), each on [k] with D = C′ marked | r ≤ k⁶ |
| (v) \|S\| < k/4 | joint comparison classes (pairwise) | **𝔄(x) of Definition 5.3** | r = 1 |

In each structure the domain D ⊆ [k] is marked by a unary relation.

**Proposition 5.2.**
1. The case is an invariant of the H-orbit of x.
2. In cases (i), (ii), (iv), (v) the family 𝔉(x) satisfies 𝔉(x^h) = 𝔉(x)^{φ(h)}, and every member,
   viewed as a structure on [k], has relative symmetry defect ≥ 1/4.
3. In case (iii), Δ(x^h) = Δ(x)^{φ(h)}, K(x^h) = K(x)^h, K(x) ≤ Aut_{H_{Δ(x)}}(x) and
   K(x)^φ|_Δ ≥ Alt(Δ).

*Proof.*
* *Equivariance.* All ingredients are equivariant: F, S, the orbits, the degree of transitivity, the
  orbitals, and for (v) Lemma T′(1). The family in (iv) is the set of all choices, so it is
  equivariant as a set. "WLOG R₁ is the diagonal" (G L2357) is harmless, since the diagonal is an
  invariant. "WLOG |D₁| = |D₂|" (G L2368) is not needed: |D(x)| is an invariant.
* *Defects.* Let Alt(Δ) ≤ Aut(𝔄) with |Δ| ≥ 3. Then Δ ⊆ D or Δ ∩ D = ∅, since D is a unary relation
  and Alt(Δ) is transitive on Δ.
  * (i) max|Δ| ≤ 3k/4.
  * (ii) Alt(Δ) preserves the partition. If Δ meets two classes, primitivity of Alt(Δ) and the fact
    that it fixes Ω∖Δ force every class meeting Δ to be a singleton, i.e. a point of [k]∖S. So
    |Δ| ≤ max(largest orbit, |[k]∖S|) < 3k/4.
  * (iv) The regular graph on C′ has relative defect ≥ 1/2 (GNS Lemma A.3 = Babai 2015,
    Cor. 2.4.13). The in/out colouring splits C′∖{v} into two halves. So
    |Δ| ≤ max(|C′|/2, k − |C′|) ≤ max(k/2, k/4 + 4) ≤ k/2.
  * (v) Lemma T′(3).

  This also covers GNS's slip at G L2324 (|C′| ≥ 3k/4 − 4, not ≥ 3k/4).
* *Case (iii).* GNS Option 2: F ≤ Aut_H(x), and C is an F^φ-orbit, so F ≤ H_C. ∎

### 5.3 The canonical structure in case (v)

* Let D(x) := [k] ∖ S(x), so |D(x)| > 3k/4.
* Every t-set T ⊆ D(x) is non-full: a full T has a certificate in F acting as ≥ Alt(T) with t ≥ 3, so
  T ⊆ S.
* T⃗₀ := (1, …, t), the first t labels of [k] (P1).
* φ(H) ≥ A_k is (k−2)-transitive, so it is transitive on [k]^{⟨t⟩}.
* J₀ := H_{(T⃗₀)} = ker(ψ_{T₀} : H_{T₀} → Sym(T₀)).

**Definition 5.3.**
* For T⃗ ∈ D(x)^{⟨t⟩} with underlying set T, put c_x(T⃗) := c(x^{⟨W(T,x)⟩}, T⃗), as in Lemma T.
  Here the layered certificate string carries the chain of (L1), and F_{J₀} is the canonizer of
  Lemma T″.
* The structure is 𝔄(x) := ([k]; unary D(x); t-ary colouring T⃗ ↦ rank of c_x(T⃗) among all values
  of c_x).
* It is encoded as a string on [k] ⊔ [k]^t, with value 0 on tuples outside D^{⟨t⟩}.

The set of values of c_x is an invariant of the H-orbit of x, by Lemma T(b) and (L4). So the ranking
is canonical.

**Lemma T′.**
1. *Strong canonicity.* 𝔄(x^h) = 𝔄(x)^{φ(h)} for h ∈ H.
2. *Key identity.* For non-full T: G(T, x) = Aut_{H_T}(x^{⟨W(T,x)⟩}), and ψ_T(G(T, x)) is a
   non-giant.
3. *Symmetry defect.* If Alt(Δ) ≤ Aut(𝔄(x)) with |Δ| ≥ 3, then Δ ⊆ [k] ∖ D(x) or |Δ| ≤ t + 1. Hence
   the symmetry defect is ≥ k − max(k/4, t + 1) ≥ 3k/4.

*Proof.*
1. W(T^{φ(h)}, x^h) = W(T, x)^h (L4), D is equivariant, and Lemma T(b) applies.
2. (L2), together with (L3) for non-full T.
3. Δ ⊆ D or Δ ∩ D = ∅. Suppose Δ ⊆ D and |Δ| ≥ t + 2, and pick T ⊆ Δ with |T| = t.
   * Every π ∈ Sym(T) is induced by some element of Alt(Δ): correct the parity on Δ∖T, which has
     ≥ 2 points.
   * So all orderings of T get the same colour.
   * The window W(T, x) depends only on the set T. So Lemma T(c), applied to y = x^{⟨W(T,x)⟩},
     gives for every π an h ∈ H with y^h = y and ψ_T(h) = π.
   * Such h lie in H_T, and y^h = y means h ∈ Aut_{H_T}(y) = G(T, x) by (2).
   * So ψ_T(G(T, x)) = Sym(T), which contradicts (2). ∎

*Remark (exactness, not needed).* Running GNS's Alg. 3 for (T₁, x₁) and (T₂, x₂), the final coset is
{h : T₁^{φ(h)} = T₂, (x₁^{[W(T₁,x₁)]})^h = x₂^{[W(T₂,x₂)]}}. So the colour classes of Definition 5.3,
taken over D(x₁)^{⟨t⟩} ⊔ D(x₂)^{⟨t⟩}, are exactly GNS's comparison classes (memo Lemma T′.2;
red-team §2.2). Our algorithm never uses this. It explains why the GNS analysis applies.

The bound t + 1 differs from GNS's t − 1 (G L2383); both suffice.

### 5.4 Computing the colours

**Lemma T″ (cost of the colours).** For T⃗ ∈ D(x)^{⟨t⟩}, c_x(T⃗) can be computed in poly(n) time
plus recursive canonizer calls. The calls are on pairwise disjoint subsets of W(T, x), each of size
≤ n/2, with groups that are restrictions of subgroups of H. Over all ≤ k^t tuples, the recursive
sizes add up to ≤ k^t·n.

*Proof.*
* *Transport.* Compute σ ∈ H with T⃗^{φ(σ)} = T⃗₀ (a preimage). Put z := x^σ. By (L4),
  (x^{⟨W(T,x)⟩})^σ = z^{⟨W(T₀,z)⟩}, and G_i(T₀, z) = G_i(T, x)^σ.
* *Define F_{J₀}.* Apply Lemma F2 with group J₀ on the J₀-invariant set
  𝒴₀ := {z^{⟨W(T₀,z)⟩}}. The windows are V_{i+1}(F_i) := Aff(Aut_{H_{T₀}}(F_i), ψ_{T₀}) ∖ U_i, for
  as long as ψ_{T₀}(Aut_{H_{T₀}}(F_i)) ≥ Alt(T₀). These windows are H_{T₀}-equivariant, hence
  J₀-equivariant. By (L2) they reproduce the chain of (T₀, z). F_{J₀} is a fixed deterministic
  function on 𝒴₀; this is what Lemma T needs.
* *Stage i.*
  * Aut_{H_{T₀}}(F_i) = G_i(T, x)^{στ_i} with τ_i ∈ Λ_i. This group is known from Lemma 5.1.
  * A_i = Aut_{J₀}(F_i) = ker(ψ_{T₀}|_{Aut_{H_{T₀}}(F_i)}).
  * V′ is a union of orbits of Aut_{H_{T₀}}(F_i) that are affected by the giant representation
    ψ_{T₀}, of degree t ≥ 9.
  * By Thm 5.9 every A_i-orbit in V′ has length ≤ n/t.
  * Canonize w^{[V′]} under A_i by the chain rule over these orbits. Alternatively, if |V′| ≤ n/2,
    make one call on V′.
* *Sizes.* The sizes sum to ≤ |W(T, x)| ≤ n.
* *Comparison with GNS.* GNS's own case split is at G L1849–1858. We need no t! descent here, because
  the right subgroup A_i is already the kernel. ∎

GNS spend binom(k, t)²·t!·n on comparisons. We spend ≤ k^t·n.

### 5.5 Option 1 (canonical find-structure)

**Proposition 5.5.** In cases (i), (ii), (iv), (v), an H-canonizer for x is obtained as follows.
* For each 𝔄 ∈ 𝔉(x):
  * Λ′(𝔄) := Iso_{φ(H)}(s_𝔄, F^{BC}_{φ(H)}(s_𝔄)), where s_𝔄 is the string encoding 𝔄 on
    [k] ⊔ [k]² ⊔ [k]^t, F^{BC} is Babai's canonical form (BC Thm 2.2), and Iso is Babai's string
    isomorphism test.
  * E = φ⁻¹(Λ′(𝔄)) = σ_𝔄R_𝔄, with R_𝔄 = φ⁻¹(Aut_{φ(H)}(𝔄_can)).
  * Recursively canonize x^{σ_𝔄} under R_𝔄.
* Combine over 𝔄 by Lemma S (for pairs (x, 𝔄)) and Lemma F4.

Each R_𝔄 satisfies |φ(H) : φ(R_𝔄)| ≥ (4/3)^k, by Prop. 5.2(2) and GNS Cor. 6.5 (k ≥ 24). The number of
branches is r ≤ k⁶, as in GNS Lemma 6.7, where 𝔄_{1,1} is paired with each 𝔄_{2,j}. The BC calls are
on domains of size ≤ 2k^t = d^{O(log d)}, so each costs exp(O((log d)^{2c_BC})).

*Proof.* Lemma S, with S(x, 𝔄) = 𝔄, is equivariant on pairs. Then apply F4. ∎

### 5.6 Option 2 (canonical find-symmetry)

**Lemma K.** In case (iii), an H-canonizer is obtained with two recursive canonizer calls under
L := H_{(Δ₀)} := φ⁻¹(φ(H)_{(Δ₀)}), where Δ₀ := {1, …, |Δ|} (P1). Moreover
|φ(H) : φ(L)| ≥ |Alt(Δ₀)| ≥ (4/3)^k.

*Proof.*
1. *Move Δ to Δ₀.* Apply Lemma S with S(x) = Δ(x) and Λ′(Δ) = {π ∈ φ(H) : Δ^π = Δ₀}; this is well
   defined because A_k is transitive on |Δ|-sets. We get E(x) = σH_{Δ₀}. Put z := x^σ, so
   Δ(z) = Δ₀ and K(z) ≤ Aut(z) ∩ H_{Δ₀}.
2. *Collapse to two cosets.* L ⊴ H_{Δ₀}, and the image of H_{Δ₀} on Δ₀ contains Alt(Δ₀), so
   H_{Δ₀} = K(z)L ∪ K(z)Lτ. Here τ is any element inducing an odd permutation on Δ₀; omit the second
   part if there is none.
3. *Branch values.* In descent (F3) from H_{Δ₀} to L, a coset ρL with ρ = κl ∈ K(z)L has branch
   value F_L(z^{κl}) = F_L(z^l) = F_L(z). Cosets inside K(z)Lτ = τK(z)L have branch value F_L(z^τ),
   because L is normal.
4. *Output.* Two L-calls. With λ₁ ∈ Λ_L(z) and λ_τ ∈ Λ_L(z^τ):
   * Aut(z) ∩ K(z)L = K(z)·Aut_L(z), since z^{κl} = z forces l ∈ Aut_L(z).
   * Aut(z) meets K(z)Lτ iff F_L(z^τ) = F_L(z). In that case it contains g_τ := τλ_τλ₁⁻¹.
   * So Aut_{H_{Δ₀}}(z) = ⟨K(z), Aut_L(z) [, g_τ]⟩.
   * Λ = Aut(z)·λ₁ if F_L(z) ≤ F_L(z^τ), and Λ = Aut(z)·τλ_τ otherwise.

   By Lemma F3 this is exactly {g : z^g = m}. ∎

This matches GNS Lemma 6.9: r ∈ {1, 2} and H = G_{(Δ₁)}.

---

## 6. The algorithm and its correctness

### 6.1 Instances

An instance is (Ω, H, 𝔅⃗, x):
* Ω ordered;
* H ≤ Sym(Ω), normalized to canonical generators;
* 𝔅⃗ an H-invariant almost d-ary sequence;
* d and t fixed globally.

𝔅⃗ is auxiliary data. It is always computed from groups higher in the recursion, never from x. So
for isomorphic strings the instance differs only in the string.

### 6.2 Algorithm CanAD (canonical almost d-ary string canonization)

1. If |Ω| = 1, return (x, H).
2. **Intransitive.** Chain rule over the H-orbits, ordered by (size, least point). Each orbit is
   handled by CanAD on (orbit, current right subgroup restricted, 𝔅⃗ restricted).
3. **Transitive, H^{𝔅₁} semi-regular.** The action is regular, with b := |𝔅₁| elements. Descend
   (F3) to H_{(𝔅₁)} over b cosets. In each branch, apply the chain rule over the b orbits, of size
   n/b each.
4. **Transitive, |𝔅₁| ≤ d.**
   * Let 𝔅 ⪰ 𝔅₁ be the (P1) coarsest-first minimal block system above 𝔅₁, and P := H^𝔅.
   * If |P| ≤ |𝔅|^{1+log|𝔅|}, or |𝔅| is below the constant of Lemma 7.1: descend to H_{(𝔅)} over
     |P| cosets, then apply the chain rule. Its orbits have size ≤ n/|𝔅| ≤ n/2.
   * Otherwise apply Lemma 7.1 to P (P1), obtaining N, 𝒞, ψ and k. Let G′, φ and 𝒞′ be as in
     §2.6. Descend (F3) from H to G′ (≤ d cosets). In each branch ρ, call Agg(G′, φ, 𝒞′, 𝔅⃗, x^ρ).
5. **Agg(G′, φ, 𝒞′, 𝔅⃗, y).**
   * If k ≤ 10t: descend to ker φ = G′_{(𝒞′)} over ≤ k! cosets, then apply the chain rule. The
     orbits lie inside 𝒞′-classes, of size ≤ n/2, since |𝒞′| = |𝒞| ≥ 2.
   * Otherwise compute the local certificates (Lemma 5.1), F, S, and the case (Prop. 5.2).
     * In cases (i), (ii), (iv), (v), apply Prop. 5.5 (for (v), the colours come from Lemma T″).
     * In case (iii), apply Lemma K.
   * Every recursive call **on the same domain**, under R_𝔄 or L, is made with the sequence
     𝔅⃗ ⊕ 𝒞′ (step 6).
6. **The fix (§7.2).** 𝔅⃗ ⊕ 𝒞′ := ({Ω} ≻ 𝒞′ ≻ 𝔅₁ ≻ 𝔅₂ ≻ …), with duplicates removed.
   * It is invariant under R_𝔄, L ≤ G′, because 𝒞′ is G′-invariant.
   * It is almost d-ary: |𝒞′| ≤ |𝔅| ≤ d, and each 𝒞′-class contains ≤ |𝔅₁| ≤ d blocks of 𝔅₁.
   * Here 𝒞′ ⪰ 𝔅 ⪰ 𝔅₁.

### 6.3 Correctness

**Proposition 6.1.** CanAD returns an H-canonizer for x.

*Proof.*
* *Termination.* Induction on (|Ω|, |H|), ordered lexicographically. Every same-domain recursive
  call is on a proper subgroup: R_𝔄 and L have index ≥ (4/3)^k > 1 in G′ ≤ H. All other calls are
  on smaller domains.
* *Each step preserves canonizers.* Each step is one of Lemmas F1–F4, S or K, Prop. 5.5, or a (P1)
  choice, and each of these maps canonizers of the sub-instances to a canonizer of the instance.
* *Canonicity of auxiliary data.* Every auxiliary object is a function of the node's group (P1), or
  an H-equivariant function of x (Lemma 5.1, Prop. 5.2, Lemma T′). The colours use one fixed
  J₀-canonizer (Lemma T″). ∎

### 6.4 The choice points of GNS

This table follows the red-team's 17 choice points (red-team §3.5), plus our step 6.

| # | GNS place (result; G line) | choice | canonical treatment |
|---|---|---|---|
| 1 | Thm 4.3 proof; L1103 | maximal block B′ of G_B^B, "B arbitrary" | P1 (block of least point, deterministic algorithm on canonical generators) |
| 2 | Thm 4.3; L1120–1121 | numbering B₁, …, B_s; σ_{1→i} | P1 (blocks ordered by least point; lex-least transporters) |
| 3 | Thm 4.3; L1207, L1254 | one G*-orbit A* | P1 (orbit of least point of Ω*, under a P1 order of Ω*) |
| 4 | Thm 4.3; L1216 | 𝒫-sequence of Thm 3.13 for N^{B₁} | P1 (deterministic computation) |
| 5 | Thm 4.6; L1315 | Johnson identifications ρ_{i,B} (BLS87, GNS Lemma 4.4) | P1 |
| 6 | Lemmas 6.2/6.3; L1802, L1908 | windows Aff(G_i, ψ) | equivariant (L4), no choice |
| 7 | Lemmas 6.2/6.3; L1810, L1917 | coset representatives ḡ of N | descent over all cosets (F3) |
| 8 | Lemma 6.3; L1902 | σ₀ with T₁ ↦ T₂ | disappears (Lemma T(a)) |
| 9 | Lemma 7.2; L2087 | coarsening to primitive P | P1 |
| 10 | Lemma 7.2; L2090–2093 | N, 𝒞, ψ (Lemma 7.1); G′; labels of [k] | P1, then descent over ≤ d cosets |
| 11 | Lemma 7.2; L2101 | k ≤ 10t: Luks to ker φ | descent over ≤ k! cosets |
| 12 | Lemma 7.2 / Alg. 1; L2121–2122 | order of orbits | chain rule, (size, least point) |
| 13 | App. A; L2337–2349 | F, S, case split | equivariant (Prop. 5.2) |
| 14 | App. A; L2352, L2359, L2364 | I, orbital R_i, vertex | equivariant family + F4 |
| 15 | App. A; L2357–2358 | "WLOG R₁ diagonal" | the diagonal is an invariant |
| 16 | App. A; L2368 | "WLOG \|D₁\| = \|D₂\|" | pairwise only; \|D(x)\| is an invariant |
| 17 | App. A; L2370–2383 | joint classes on D₁′ ⊔ D₂′ | **Lemma T, the only real change** |
| 18 | Lemma 7.2; L2118–2126 (implicit) | top partition of the next round | **𝒞′ (step 6); see §7.2** |

No other pairwise step exists in GNS. The places where two strings occur are L1866–1940, L1980–1990,
L1999–2057 and L2370–2385 (memo §4.4; red-team §3). Lemma 6.6's "for i = 1, 2" is presentational
everywhere except row 17.

### 6.5 Theorem A from CanAD

* *Cosets.* Reduce to groups by the coset rule (§2.2).
* *Intransitive G.* Chain rule over the orbits. The constituents are recursive calls of the
  Γ̂_d-canonizer; each restricted group is in Γ̂_d.
* *Transitive G.* Compute Ω*, ι, x ↦ x* and the sequence by GNS Thms 4.3 and 4.6 (P1, rows 1–5).
  Run CanAD on (Ω*, G*, 𝔅⃗*, x*) and pull back by Lemma R.

The almost d-ary recursion never re-applies the change of action (GNS Obs. 4.2). Correctness follows
from Prop. 6.1 and Lemma R. The time bound is §7.5.

---

## 7. Running time

### 7.1 A recursion lemma

**Lemma 7.0.** Let τ : ℕ → ℕ with τ(1) = 1, and let K ≥ 1. Suppose that every n ≥ 2 satisfies
τ(n) ≤ Σ_{i=1}^ℓ τ(n_i) with 1 ≤ n_i < n, where either
* (A) n_i ≤ n/2 for all i and Σ_i (n_i/n)^{K+1} ≤ 1, or
* (B) Σ_i n_i ≤ n.

Then τ(n) ≤ n^{K+1}.

*Proof.* Induction: Σ n_i^{K+1} = n^{K+1}·Σ(n_i/n)^{K+1} ≤ n^{K+1} in case (A), and
Σ n_i^{K+1} ≤ (Σ n_i)^{K+1} ≤ n^{K+1} in case (B). ∎

The hypothesis of (A) holds in two situations:
* n_i ≤ n/2 and Σ n_i ≤ 2^K n (GNS Lemma 2.6);
* b² pieces of size n/b with b ≥ 2 (the semi-regular Luks step): Σ(n_i/n)^{K+1} = b^{1−K} ≤ 1.

GNS Lemma 2.8 requires Σ n_i ≤ 2^K n, which the semi-regular step violates when b > 2^K. Lemma 7.0
covers that step. [GAP-2: closed]

### 7.2 [GAP-1] The potential argument of GNS Lemma 7.2 as written

GNS (G L2118–2134; Neuen 2020, L2709–2724 of `hypergraph-gamma-d.tex`, verbatim) argue as follows.
Let φ′ : H′ → S_{k′} be the giant representation of the next round. Then |(H′)^{𝒞′}| ≥ k′!/2,
"because (H′)^{φ′} ≥ A_{k′} and H′_{(𝒞′)} ≤ ker(φ′)". Combined with |H^{𝒞′}| ≤ k!/(4/3)^k, this
gives k′ ≤ k − k/(3 log k), so the recursion has height O(log² d).

**The claim H′_{(𝒞′)} ≤ ker φ′ does not follow for the algorithm as written.** In the next round,
Alg. 4 / Lemma 7.2 coarsens the *given* first partition 𝔅₁ (restricted to the current orbit) to "a"
minimal block system, and builds φ′ on that. Nothing ties it to 𝒞′.

**Counterexample.**
* *Setup.* m is large, d := m², q ≥ 1, Ω := [m]² × [q], and G := (S_m ≀ S₂) × C_q, with the product
  action on [m]² and C_q regular on [q].
* *Sequence.* {Ω} ≻ 𝔅₁ := {{(a,b)} × [q]} ≻ discrete. It is almost d-ary: level 1 has m² = d classes,
  level 2 is semi-regular.
* *First round.*
  * P = G^{𝔅₁} = S_m ≀ S₂ in product action, primitive, with |P| = 2(m!)² ≥ d^{1+log d}.
  * Lemma 7.1's specification is met by N = S_m × S_m, 𝒞 = rows {{a} × [m]}, and ψ the first
    projection, so k = m.
  * For large m, k > 10t = 10(3 + 2 log m).
* *String.* Let U ⊂ [m] with |U| = 0.3m, and x((a, b), c) := [a ∈ U].
  * A test set T ⊆ [k] (a set of rows) is full iff T ⊆ U or T ⊆ U^c.
  * F(x)^φ has orbits U and U^c, so S = [k], and no orbit has size ≥ 3k/4. This is case (ii).
  * The structure is the partition {U, U^c}, so H = R = φ⁻¹(Sym(U) × Sym(U^c)) ∩ G′.
* *Next round.*
  * The large H-orbit is Ω′ = (U^c × [m]) × [q], of size 0.7n.
  * H′ acts on 𝔅₁[Ω′] ≅ U^c × [m] as Sym(U^c) × S_m in product action.
  * This action has two minimal block systems: rows and columns.
  * If the columns are chosen, P′ ≅ S_m in its natural action, and Lemma 7.1 gives k′ = m = k.
  * H′_{(𝒞′)} (fixing all rows) acts as S_m on the columns, so it is **not** in ker φ′.

So the inequality k′ ≤ k − k/(3 log k) fails for this input, under a choice the text permits. The
running time may still be fine; in this example the columns shrink next. But the written proof does
not establish the bound.

**Fix (step 6 of §6.2).** Make 𝒞′ the top partition of every same-domain child. GNS's sentence "Recall
that 𝒞′ is G′-invariant and thus, it is also H-invariant" (G L2120) suggests this was intended. The
fix costs nothing: it is a P1 choice, it keeps the sequence almost d-ary (§6.2, step 6), and it
applies verbatim to the isomorphism test.

### 7.3 The potential argument, with the fix

Consider a same-domain chain:
* an aggregation node (G′, φ, k);
* a child (R, ·) with R ∈ {R_𝔄, L} and |φ(G′) : φ(R)| ≥ (4/3)^k;
* the chain rule on R's orbits; let Ω′ be the unique orbit of size > n/2 (if any), processed under
  some R° ≤ R;
* the next node H′ := (R°)^{Ω′}, transitive, with top partition 𝒞′[Ω′].

Note |𝒞′[Ω′]| ≥ 2, since 𝒞′-classes have size ≤ n/2 < |Ω′|.

At H′, step 3 or 4 is applied with 𝔅₁ = 𝒞′[Ω′]. Let 𝔇 ⪰ 𝒞′[Ω′] be the chosen minimal block system.
If step 4b applies, it produces G″ ≤ H′ (index ≤ d) and φ′ = ψ′ ∘ (action on 𝔇), with
ker φ′ = G″_{(𝒞‴)}, where 𝒞‴ ⪰ 𝔇 ⪰ 𝒞′[Ω′].

**Claim.** k′!/2 ≤ k!/(4/3)^k, and hence k′ ≤ k − k/(3 log k).

*Proof.*
1. An element fixing every 𝒞′[Ω′]-class fixes every 𝔇-class and every 𝒞‴-class. So
   G″_{(𝒞′[Ω′])} ≤ ker φ′, and A_{k′} ≤ φ′(G″) is a quotient of (G″)^{𝒞′[Ω′]}.
2. |(G″)^{𝒞′[Ω′]}| ≤ |(R°)^{𝒞′}| ≤ |R^{𝒞′}|.
3. R^{𝒞′} ≅ R/R_{(𝒞′)} = R/(R ∩ ker φ) ≅ φ(R), and |φ(R)| ≤ k!/(4/3)^k.
4. So k!/k′! ≥ (4/3)^k/2. Since k!/k′! ≤ k^{k−k′}, we get k log₂(4/3) ≤ 1 + (k − k′)log₂ k. Hence
   k − k′ ≥ (0.415k − 1)/log₂ k ≥ k/(3 log₂ k) for k ≥ 13. ∎

**Height.**
* Every giant degree is ≤ d, and aggregation stops once k ≤ 10t.
* By the Claim, k_{j+1} ≤ k_j(1 − 1/(3 log₂ d)).
* So a root-to-leaf path has at most h := 3 log₂ d · ln(d/(10t)) + 1 = O(log² d) aggregation nodes.

### 7.4 One macro step and its branch counts

A *macro step* is the computation for one transitive instance in step 4. It explores the tree 𝒯 of
same-domain nodes described in §7.3. Calls on domains of size ≤ n/2 are its *exits*. Calls in the
intransitive and semi-regular steps are separate macro nodes of Lemma 7.0.

| quantity | GNS | canonical | where |
|---|---|---|---|
| descent H → G′ | ≤ d | ≤ d | F3 |
| Luks, small primitive P | \|P\| ≤ d^{1+log d} | same | F3 |
| k ≤ 10t, to ker φ | ≤ k! | same | F3 |
| semi-regular top | b cosets × b orbits | same | F3 + chain rule |
| local certificates | binom(k,t)·t!·n | same | Lemma 5.1 |
| comparisons / colours | binom(k,t)²·t!·n | ≤ k^t·n | Lemma T″ |
| Option 1 branches | r ≤ k⁶ subcosets H_jh_j | r ≤ k⁶ subcosets σ_𝔄R_𝔄 | Prop. 5.5 |
| Option 2 branches | r ≤ 2 (H = G_{(Δ₁)}) | 2 calls under L = G′_{(Δ₀)} | Lemma K |
| index of children | ≥ (4/3)^k | ≥ (4/3)^k | Cor. 6.5 |
| Babai's test / BC | ≤ k⁶ calls, exp(polylog d) | ≤ k⁶ BC + Iso calls, exp(polylog d) | Prop. 5.5 |
| extra non-recursive work | — | canonical generating sets, lex-least transporters, string comparisons: poly(n) per node | §2.4 |

GNS never prune by "one isomorphism suffices". Their only automorphism pruning is find-symmetry,
which Lemma K reproduces. So no factor is lost anywhere (red-team §4).

**Bounds for one macro step.**
* *Nodes of 𝒯.* Each level branches by ≤ d·k⁶ ≤ d⁷, so 𝒯 has at most d^{7(h+2)} = 2^{O(log³ d)}
  nodes.
* *Exits per node.* At most 2k^t·n (certificates and colours) plus k⁶·n (small orbits of the
  children) plus, at leaves, max(d^{1+log d}, k!)·n. In total 2^{O(log² d)}·n.
* *Total exits.* Σ n_i ≤ 2^{K₀ log³ d}·n with every n_i ≤ n/2, for an absolute constant K₀.
* *Non-recursive work.* 2^{O(log³ d)}·(n^{O(1)} + exp(O((log d)^{2c_BC}))) = d^{O((log d)^{c₁})}·n^{O(1)}.

### 7.5 Proof of the time bound

**Almost d-ary instances** with domain size N (and d ≤ N).
* A macro step satisfies Lemma 7.0(A) with K := K₀ log³ d.
* The semi-regular step satisfies (A).
* The intransitive step satisfies (B), with ℓ ≥ 2.
* So the recursion tree has ≤ N^{K+1} leaves.
* Its depth is ≤ 2 log₂ N + 1: sizes halve at least every two steps, because a (B)-child is
  transitive and is next split by an (A)-step.
* So there are ≤ (2 log₂ N + 2)·N^{K+1} macro nodes, each costing d^{O((log d)^{c₁})}N^{O(1)}.
* Total: N^{O((log d)^{c₂})}, since d ≤ N.

**Γ̂_d instances.**
* A transitive constituent of size n_i becomes N_i := |Ω*_i| ≤ n_i^{O(log² d)}, costing
  n_i^{O((log d)^{c₂+2})}.
* The constituents are disjoint, and the bound is superadditive, so the total is n^{O((log d)^c)}
  with c := c₂ + 2.
* The coset rule and Lemma R add polynomial overhead (preimages: GNS Thm 2.1). ∎

This closes the "Step 4 [SKETCH]" of the memo (§4.2). The only change to GNS's argument is the fix of
§7.2, and the generalized recursion lemma of §7.1.

---

## 8. Corollary B: the canonical Luks reduction

We follow BL83 §4.3 (Theorem 4.2) and BL83 §4.2, "fourth trick, due to Babai". That trick is a
half-edge encoding which keeps the string domain of size poly(n) independently of d. Our only
deviation is that we pad every vertex to d − 1 slots instead of first canonizing the valence string,
and we fold the edges inside the new layer into the same string. Both changes are cosmetic.

**Setting.** Let X be a graph on V, |V| = n, of maximum degree d ≥ 3; for d ≤ 2 everything is
trivial. Put q := d − 1.

**Step 0 (components).**
* Canonize each connected component C, obtaining CF(C) on [|C|] and its coset Λ(C).
* CF(X) places the component forms on consecutive intervals of [n], sorted by (size, form).
* Λ(X) consists of all bijections that map each component, by a member of its own Λ(C), onto an
  interval carrying an equal form.
* Representation: one element, plus generators of ∏Aut(CF(C)) together with the interval swaps
  between equal forms.

This is BL83 §4.3, first paragraph.

**Step 1 (edge rooting).**
* For a connected X with ≥ 2 vertices, and each *ordered* edge (u, v) (≤ nd ≤ n² of them), compute
  CF(X, u, v) on [n] with u ↦ 1 and v ↦ 2, together with
  Λ(X, u, v) = {μ : X^μ = CF(X, u, v), u^μ = 1, v^μ = 2}.
* Then put CF(X) := min CF(X, u, v) over all ordered edges, and Λ(X) := the union of the Λ(X, u, v)
  attaining the minimum.
* This is Lemma F4 with the equivariant family of ordered edges. The root information can be
  forgotten, because the roots always go to 1 and 2.

**Layers.**
* V₀ := {u, v}, and V_r := {w : dist(w, {u, v}) = r} for r ≥ 1.
* X_r := X[V₀ ∪ … ∪ V_r], N_r := |V_{≤r}|, and I_r := (N_{r−1}, N_r] (the labels of layer r).
* Every y ∈ V_r has at most q neighbours in V_{r+1} (its *down-degree* deg↓y). For r ≥ 1 this is
  because y has a neighbour in V_{r−1}; for r = 0, because u and v are adjacent. This is the
  "outvalence ≤ d − 1" of BL83 Lemma 4.4.

**Invariant (I_r).** CF_r is a graph on [N_r] that depends only on the isomorphism type of
(X, u, v), and Λ_r := {λ : V_{≤r} → [N_r] : u ↦ 1, v ↦ 2, X_r^λ = CF_r} is nonempty. Any such λ
maps V_i onto I_i, because isomorphisms preserve distance from the roots. Â_r := Aut(CF_r; 1, 2)
satisfies Λ_r = λÂ_r.

*Base.* CF₀ is the edge {1, 2} on [2], and Λ₀ = {u ↦ 1, v ↦ 2}.

**Step r → r + 1.**

*The group.* Let L := I_r, and let Ĥ := S_q ≀_L Â_r act on Ξ_r := [N_r] ⊔ (L × [q]) ⊔ (L × [q])²:
* (â, s) acts by â on [N_r];
* by (ℓ, i) ↦ (ℓ^â, i^{s_ℓ}) on slots;
* coordinatewise on pairs of slots.

Ĥ is generated by the generators of Â_r and two generators of S_q per ℓ ∈ L. It acts faithfully. It
lies in Γ̂_q if Â_r does, being an extension of S_q^L by Â_r. The domain has |Ξ_r| ≤ n + nq + (nq)²
≤ 3n⁴ points. Ξ_r is ordered: [N_r] first, then slots lexicographically, then pairs lexicographically.

*The string.* Given λ ∈ Λ_r and a slot assignment β (bijections β_y : N↓(y) → [deg↓y] for y ∈ V_r),
define slot(y, w) := (y^λ, β_y(w)) for each down-edge yw, and the string x_{λ,β} on Ξ_r:
* ∗ on [N_r];
* on a slot (ℓ, i): 1 if it is occupied (i ≤ deg↓(ℓ^{λ⁻¹})), 0 otherwise;
* on a pair of occupied slots with endpoints w, w′ ∈ V_{r+1}: "=" if w = w′, "E" if ww′ ∈ E(X),
  "≠" otherwise; 0 if either slot is unoccupied.

*Claim 1 (one orbit).* All x_{λ,β}, for λ ∈ Λ_r and all β, lie in one Ĥ-orbit.

*Proof.* Let λ′ = λâ and let β′ be another slot assignment. For ℓ ∈ L put y := ℓ^{λ⁻¹} and let s_ℓ map
β_y(w) to β′_y(w), extended arbitrarily on the unoccupied slots. Then (â, s) maps
slot_{λ,β}(y, w) = (y^λ, β_y(w)) to (y^{λâ}, β′_y(w)) = slot_{λ′,β′}(y, w). It therefore preserves
occupancy and the pair values. ∎

*Claim 2 (invariance).* Let π : (X, u, v) → (X′, u′, v′) be an isomorphism. Then
x_{π⁻¹λ, β∘π⁻¹}(X′) = x_{λ,β}(X), and Ĥ depends only on CF_r. So the orbit 𝒪_r is an isomorphism
invariant.

*Canonization.* Let F̂ := F_Ĥ(x_{λ,β}) and Λ̂ := Λ_Ĥ(x_{λ,β}), computed by **one call of Theorem A**:
group Ĥ ∈ Γ̂_{d−1}, domain size ≤ 3n⁴. F̂ depends only on 𝒪_r.

*Reading off CF_{r+1}.*
* In F̂, "=" is an equivalence relation on the occupied slots. Order its classes by least slot and
  label them N_r + 1, …, N_{r+1}.
* CF_{r+1} := CF_r together with:
  * an edge {ℓ, N_r + j} for each occupied slot (ℓ, i) in class j;
  * an edge {N_r + j, N_r + j′} when F̂ has "E" on a pair of slots from classes j and j′. This value
    is the same for all such pairs, because it depends only on the endpoints.
* So CF_{r+1} is a function of (CF_r, F̂), hence an invariant.

*The labellings.* For ĥ = (â, s) ∈ Λ̂, define μ = μ(λ, β, ĥ):
* y ↦ y^{λâ} on V_{≤r};
* on V_{r+1}, w ↦ N_r + j, where j is the class of F̂ containing ĥ(slot(y, w)) for any
  up-neighbour y of w. This is well defined: the slots of w are "="-related, and every w has an
  up-neighbour. It is bijective onto I_{r+1}.

*Claim 3.* X_{r+1}^μ = CF_{r+1}.

*Proof.*
* X_r^{λâ} = CF_r^â = CF_r.
* yw ∈ E (y ∈ V_r, w ∈ V_{r+1}) iff slot(y, w) is occupied with endpoint w, iff its ĥ-image (a slot
  of y^μ) lies in class w^μ. This uses that x and F̂ = x^ĥ agree along ĥ, and that the slots of a
  fixed y have distinct endpoints, since there are no multi-edges.
* Edges inside V_{r+1} are read off the "E" values in the same way. ∎

*Claim 4.* {μ(λ, β, ĥ)} = Λ_{r+1} := {μ : rooted, X_{r+1}^μ = CF_{r+1}}.

*Proof.* "⊆" is Claim 3. For "⊇": by Claim 2, applied to an automorphism g of (X_{r+1}, u, v), the
choice (g⁻¹λ, β∘g⁻¹, ĥ) is valid and yields g⁻¹μ. So the set of outputs is closed under
Aut(X_{r+1}, u, v). Λ_{r+1} is a single coset of that group, and it contains an output. ∎

*Claim 5 (generators).* Let θ : Aut_Ĥ(F̂) → Sym([N_{r+1}]) act by â on [N_r] and by the induced
permutation of "="-classes on the new labels. Then θ(Aut_Ĥ(F̂)) = Â_{r+1}.

*Proof.* "⊆" is clear. For "⊇": let b ∈ Â_{r+1}. Set â := b|_{[N_r]} ∈ Â_r. For ℓ ∈ L, the classes
adjacent to ℓ correspond bijectively to the occupied slots of ℓ, and b maps them to the classes
adjacent to ℓ^b. Let s_ℓ follow this bijection, extended arbitrarily on the unoccupied slots (b
preserves down-degrees). Then (â, s) fixes F̂, and θ(â, s) = b. ∎

So Λ_{r+1} = μ₀·Â_{r+1} is obtained in polynomial time from Λ̂. By induction (I_r) holds for all r.
At r = R, the eccentricity of {u, v}, we have X_R = X.

Membership in Γ̂_{d−1}, by induction: Â₀ = 1, and Â_{r+1} is a quotient of a subgroup of
Ĥ ∈ Γ̂_{d−1}. This reproves BL83 Lemma 4.3 (Luks) inside the construction.

**Running time.** There are ≤ n² rooted edges and ≤ n layers. That is ≤ n³ calls of Theorem A on
domains of size ≤ 3n⁴ with groups in Γ̂_{d−1}, costing (3n⁴)^{O((log d)^c)} each, plus polynomial
overhead. **Total: n^{O((log d)^c)}.** The exponent's dependence on d comes only from Theorem A, as in
GNS Thm 8.1 ("the running time of the reduction does not depend on d"). ∎ (Corollary B)

*Comparison with BL83.*
* BL83 §4.3 alternates two steps: canonize Y_r (adding the edges inside V_r) with respect to the
  current coset; then extend through the bipartite graph Z_r between V(X_r) and V_{r+1}, by the
  algorithm of §4.2.
* BL83 §4.2, trick 4: canonize the valence string x : B → {0, …, d_out}; extend the coset to the
  edges, "allowing arbitrary permutations of edges with common origin"; canonize
  y(e₁, e₂) = [e₁, e₂ end at the same vertex] on E × E; order the vertices of C by their least
  incident edge.
* Our padded slots replace the valence step, and our pair values "E" replace Y_{r+1}.

---

## 9. Further consequences

### 9.1 Corollary D, and structures

**Corollary D.** Let a string (e.g. the adjacency string of a graph on V², with Δ acting on pairs) and
a labelling coset Δρ with Δ ∈ Γ̂_d be given. Then CL(x, Δρ) is computable in |V|^{O((log d)^c)}.

*Proof.* Remark 2.3, plus Theorem A for H = ρ⁻¹Δρ acting on V² (H ∈ Γ̂_d). ∎

This is the canonical twin of Wie20 Theorem `boundedDegree` (Iso(G₁; G₂) ∩ Δφ in |V|^{polylog cw Δ}).

Theorem A with Sym(D) acting on D^t also gives canonical forms of t-ary structures and hypergraphs
in n^{O(t (log n)^c)}, the canonical twins of GNS Thm 8.3 and Cor. 8.4. These are weaker than known
results (Thesis Thms 5.2 and 5.4), so we claim nothing new there.

### 9.2 Treewidth: a remark, not a corollary

Wiebking (Wie20, Thm `isoGraph`) decides isomorphism of graphs of treewidth k in n^{polylog k}. Wie20's
outlook says that this algorithm "should then be amenable to canonization" once GNS is. **We do not
claim this as a corollary.** After checking Wie20 §"treewidth", its imports are:
1. **Thm `boundedDegree` (GNS).** Corollary D is its canonical twin. ✓
2. **Lemma `cosetHyper`** = GNSW18 Lemma 9 (via Neuen's dissertation): isomorphism of coset-labelled
   hypergraphs in (|V| + |H|)^{polylog cw Δ}. Its canonical version would need canonization at the
   polylog(cw Δ) level for coset-labelled hypergraphs. That is a Neuen-2020-type (hypergraph Γ̂_d)
   statement, and Theorem A does not give it. Wiebking's canonical `canSetHyper` has the weaker
   exponent polylog|V|. **[GAP for the treewidth corollary.]**
3. **Isomorphism-style steps.** `isoBasic`, `isoBasicClique` and `isoTree` use an "arbitrary
   labeling ρ₁" and a "representative t*". Their canonical rewriting is plausible in the Thesis
   framework (cf. the canonical FPT algorithm, Thesis Thm 6.13), but it has not been done.

The Thesis's n^{polylog k} treewidth result (Cor. 6.30) and its minors result (Thm 6.29) use Neu20a.
The Thesis itself makes Q 9.7 (Hadwiger number) conditional on further work after Q 9.6.

Plausible next steps [SPECULATION]:
* canonical Neu20, by applying Lemma T to Neu20's aggregation, which has the same pairwise structure
  (Neu20 L2561–2595);
* then treewidth and minors.

---

## 10. What is assumed from the literature

Numbers refer to arXiv:1802.04659v3 unless stated otherwise.

| # | result | used for |
|---|---|---|
| 1 | GNS Thm 2.1 (Seress: orders, membership, orbits, pointwise stabilizers, block systems, kernels, preimages) | throughout |
| 2 | GNS Lemma 2.4 (Luks: Γ̂_d closed under subgroups and quotients) | §2.3, §8 |
| 3 | GNS Thm 3.13 (structure of large primitive Γ̂_d groups), via Thm 4.3 | change of action |
| 4 | GNS Thms 4.3 and 4.6, **including the constructions in their proofs**: ι a homomorphism; x ↦ x* injective and equivariant; |Ω*| bound; almost d-ary sequence; computability in poly(|Ω*|). Also GNS Lemmas 4.4 (BLS87) and 4.5 | Lemma R |
| 5 | GNS Obs. 4.2 | inheritance of the sequence |
| 6 | GNS Thm 5.8 (unaffected stabilizers, almost d-ary) | (L3), Lemma 5.1 |
| 7 | GNS Thm 5.9 = Babai 2016, Thm 6(b) (affected orbit lemma) | Lemma 5.1, Lemma T″ |
| 8 | GNS Lemma 6.2 and the termination argument of Lemma 6.3 | (L1)–(L5) |
| 9 | GNS Thm 6.4 / Cor. 6.5 (Dixon–Mortimer Thm 5.2A,B) | index ≥ (4/3)^k |
| 10 | GNS Thm A.2 (CFSG: non-giants are ≤ 5-transitive); GNS Lemma A.3 = Babai 2015, Cor. 2.4.13 | case (iv) |
| 11 | GNS Lemma 7.1 = Babai 2015 (arXiv:1512.03547v2), Thm 3.2.1 | §6.2, step 4 |
| 12 | GNS Lemma 2.6 (inequality) | §7.1 |
| 13 | **Babai, STOC 2019, Thm 2.2** (canonical form of strings under any group, quasipolynomial), used only on domains of size ≤ 2k^t = d^{O(log d)}; and Babai 2016 Thm 2.1 / BC Thm 2.1 (string isomorphism) to get the canonical placement coset | Prop. 5.5 |
| 14 | Canonical generating sets: AGMMM 2018 Lemma 6.2 = GNSW Lemma 21 = Schweitzer–Wiebking `canGen` | P1 |
| 15 | Lexicographically least element of a coset, in polynomial time (standard; point-stabilizer chain) | P1 |

**Not assumed, reproved here:**
* the Babai–Luks framework lemmas F1–F4;
* BL83's canonical bounded-valence reduction (§8), including BL83 Lemma 4.3;
* the recursion lemma (§7.1);
* the potential argument (§7.3).

**New:**
* Lemma T, and its use in Definition 5.3 / Lemmas T′, T″;
* Lemma K (routine);
* Lemma R as stated (routine);
* the fix of §7.2.

---

## 11. Flags

* **[GAP-1] (GNS, closed here; please confirm).** GNS Lemma 7.2's step "H′_{(𝒞′)} ≤ ker φ′" fails for
  the algorithm as written (§7.2, explicit input). It is fixed by making 𝒞′ the top partition of the
  child (§6.2, step 6; §7.3). The same text is in Neuen 2020. We have **not** seen the SICOMP 2023
  version of GNS (paywalled; DOI 10.1137/19M1245293), which may already contain the fix.
* **[GAP-2] (closed).** GNS Lemma 2.8 does not cover the semi-regular step literally (§7.1).
* **BC is a "preliminary report".** Theorem A depends on BC Thm 2.2 for structures on ≤ d points of
  arity O(log d). Wiebking's thesis and Wie20 use BC as a black box in the same way. A full version of
  BC would remove this caveat. Not a gap in this paper, but the main external risk.
* **Thm 4.3/4.6 internals.** Lemma R needs the injective, equivariant x ↦ x*, which is shown inside
  GNS's proofs (Claims), not stated in the theorems. We checked those claims (G L1161–1179,
  L1518–1530). We did not re-verify Thm 3.13 or the group theory behind Lemma 4.5 (uniqueness of π
  needs m ≥ 7).
* **Lemma 7.1 for small degree.** It needs the degree above an absolute constant. Below that, |P| is
  bounded and step 4a applies. GNS leave this implicit.
* **Empty comparison coset.** GNS Alg. 3 is undefined when the coset becomes empty (red-team §2.3).
  This is irrelevant here, since Alg. 3 is never run.
* **Treewidth.** Remark only (§9.2), with a named missing piece.
* No mathematical gap was found in the canonical components (Lemmas S, T, T′, T″, K, R, F1–F4,
  Prop. 5.2, 5.5, §8).

---

## 12. Related work

* **Luks (1982); Babai–Kantor–Luks (1983).** Bounded-valence isomorphism, n^{O(d/log d)}.
* **Babai–Luks (1983); Fürer–Schnyder–Specker (1983).** Canonical forms for bounded valence. BL83
  introduce canonical labelling cosets, the canonical form with respect to a coset, and the
  half-edge trick (§4.2, trick 4, due to Babai).
* **Babai (2016) and Babai (STOC 2019).** Quasipolynomial isomorphism and canonical forms. The
  STOC 2019 paper makes the local-certificate structure strongly canonical (Thm 12.1) by different
  means: R(x) from M(T, x), and selection in asymmetric test sets (Claim 12.4). Those means need
  t ≥ 2 log₂ n.
* **GNS (FOCS 2018 / SICOMP 2023).** n^{polylog d} isomorphism via almost d-ary sequences.
* **Neuen (ICALP 2020).** Hypergraphs under Γ̂_d.
* **GNSW (ICALP 2018 / TALG).** FPT isomorphism for treewidth.
* **Grohe–Neuen–Wiebking (2020).** Minors.
* **Neuen.** Topological subgraphs.
* **Schweitzer–Wiebking (STOC 2019); Wiebking (ICALP 2020); Wiebking's thesis (2021).** The
  canonization framework for labelling cosets and hypergraphs, multiple labelling cosets, canonical
  FPT for treewidth, and DeepWL (Thesis Ch. 8; it applies to polynomial-time DeepWL tests, not to
  group-theoretic ones like GNS). The thesis lists our problem as Question 9.6. Its Lemma 5.34 uses a
  canonical test set over an ordered group.
* **Neuen's survey (Comput. Sci. Rev. 2026).** Says that canonization "is possible for many of the
  algorithms discussed", without an explicit degree-d statement.
* **Practical canonizers** (McKay–Piperno and others). Individualization-refinement routinely
  relabels individualized vertices to reference labels. Lemma T is the group-theoretic analogue at a
  fixed ordered tuple.
* **Prior-art searches.** Red-team §6: arXiv API queries and web searches through 2026-11-05 found no
  n^{polylog d} canonization for degree d.

---

## 13. Questions for experts (check these first)

1. **GNS Lemma 7.2 (§7.2–7.3).** Is our reading right that the written argument needs
   H′_{(𝒞′)} ≤ ker φ′, and that the algorithm as written does not ensure it? Is the fix ("𝒞′ becomes
   the top partition of the child") what was intended? Is it already in the SICOMP version? Does any
   other part of the GNS analysis use the original 𝔅₁ in a way the fix disturbs?
2. **Lemma T′(3) and Lemma T″ (§5.3–5.4).** These are the heart of the matter:
   * that the colour of an ordered tuple, computed under J₀ = H_{(T⃗₀)} after transport, is a single
     well-defined J₀-canonizer on the layered certificate strings;
   * that "all orderings of T have the same colour" forces ψ_T(G(T, x)) = Sym(T), contradicting
     non-fullness;
   * that the colours cost ≤ k^t·n in recursive sizes, with no relation between t and n.
3. **Change of action (Lemma R; rows 1–5 of §6.4).** Can every auxiliary choice in the proofs of GNS
   Thms 4.3 and 4.6 really be made as a function of the group, in particular the 𝒫-sequence of
   Thm 3.13 and the BLS87 Johnson identification? Is Ω* ordered canonically? Is the restriction to
   one G*-orbit still injective on strings?
4. **The BC dependency.** Is BC Thm 2.2 accepted as proved (STOC 2019 preliminary report)? Is there a
   full version? Theorem A uses it only for structures with ≤ d points and arity O(log d).
5. **Prior art.** Do Neuen, Schweitzer or Wiebking know of unpublished work on Question 9.6? The
   device (Thesis Lemma 5.34) is theirs.

---

## References (as used)

* [AGMMM18] Allender, Grochow, van Melkebeek, Moore, Morgan. Minimum circuit size, graph isomorphism,
  and related problems. SICOMP 47(4), 2018. Lemma 6.2.
* [Ba15+] L. Babai. Graph isomorphism in quasipolynomial time. arXiv:1512.03547v2. Thm 3.2.1,
  Cor. 2.4.13.
* [Ba16] L. Babai. STOC 2016. Thm 6(b).
* [BC] L. Babai. Canonical form for graphs in quasipolynomial time: preliminary report. STOC 2019,
  1237–1246. Thm 2.2, Def. 5.1, Claim 12.4, §16.
* [BL83] L. Babai, E. M. Luks. Canonical labeling of graphs. STOC 1983, 171–183. §§2, 4.2, 4.3.
* [BLS87] Babai, Luks, Seress. Permutation groups in NC. STOC 1987.
* [FSS83] Fürer, Schnyder, Specker. Normal forms for trivalent graphs and graphs of bounded valence.
  STOC 1983. (Not obtained.)
* [GNS] M. Grohe, D. Neuen, P. Schweitzer. A faster isomorphism test for graphs of small degree.
  FOCS 2018; SICOMP 52(6), 2023 (DOI 10.1137/19M1245293); arXiv:1802.04659v3.
* [GNSW] Grohe, Neuen, Schweitzer, Wiebking. An improved isomorphism test for bounded-tree-width
  graphs. ICALP 2018; TALG 2020.
* [Lu82] E. M. Luks. Isomorphism of graphs of bounded valence can be tested in polynomial time.
  JCSS 25, 1982.
* [Neu20] D. Neuen. Hypergraph isomorphism for groups with restricted composition factors.
  ICALP 2020; arXiv:2002.06997.
* [SW19] P. Schweitzer, D. Wiebking. A unifying method for the design of algorithms canonizing
  combinatorial objects. STOC 2019; arXiv:1806.07466.
* [Wie20] D. Wiebking. Graph isomorphism in quasipolynomial time parameterized by treewidth.
  ICALP 2020; arXiv:1911.11257.
* [Thesis] D. Wiebking. A decomposition-compatible canonization framework for the graph isomorphism
  problem. Dissertation, RWTH Aachen, 2021. DOI 10.18154/RWTH-2021-06242. Lemma 5.34, Questions
  9.6–9.7.
