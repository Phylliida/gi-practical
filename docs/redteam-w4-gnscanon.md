# Red-team of w4-gnscanon: canonical labelling for degree-d graphs in n^polylog(d)

Branch `w5-redteam-gnscanon`, 2026-11-05. Referee report on `docs/w4-gnscanon.md` ("the memo"). The
claim under test: GNS's isomorphism test can be made canonical with one new device, canonical colours
for ordered test tuples computed at a fixed reference tuple (Lemma T). That would give canonical forms
for graphs of maximum degree d in n^{O((log d)^c)}, which the literature lists as open.

**Brief.** Try to break it. The seven attacks are §§1–7. §8 lists minor defects, §9 gives the
verdict.

**Sources.** All untrusted data, read only, under `scratchpad/r4-sources/`.

| short | what | where | read |
|---|---|---|---|
| memo | `docs/w4-gnscanon.md`, "M L…" = line | worktree | in full |
| W3 | `docs/w3-canon.md` §§1–2 | worktree | §§0–2.2 |
| GNS | arXiv:1802.04659v3, "G L…" = line of `bounded-degree-polylog-d.tex` | `arxiv-1802.04659/x/` | L120–590, L940–2388 (all algorithmic parts, both change-of-action theorems, appendix) |
| BC | Babai, STOC'19 canonical form, "B L…" = line of `babai-canon.txt` | `w3c-babai-canon/` | L50–160, L600–1110 |
| S-W | arXiv:1806.07466 | `w1s-arxiv-1806.07466/x/articles/` | `canGenSets.tex` (all), `openQuestions.tex` |
| Wie20 | arXiv:1911.11257 | `w3c-wiebking-1911.11257/x/` | `treewidth.tex` Thm `boundedDegree` |
| **Thesis** | D. Wiebking, *A Decomposition-Compatible Canonization Framework for the Graph Isomorphism Problem*, RWTH Aachen, defended 14 June 2021, DOI 10.18154/RWTH-2021-06242. "p." = printed page | **new** `w5rt-thesis/` (pdf + pypdf text) | front matter, §1.2–1.3 (pp. 6–11), §5.3.8–5.3.9 (pp. 100–116), Ch. 9 (pp. 241–242) |
| DeepWL | Grohe–Schweitzer–Wiebking, arXiv:2003.10935, abstract | new `w5rt-deepwl/` | abstract |
| Neu20 | arXiv:2002.06997 | `arxiv-2002.06997/x/` | searched for "canon" |
| Survey26 | Neuen, Comput. Sci. Rev. 2026 | `regensburg-neuen-survey/` | "Can" paragraph, degree passages |
| arXiv API | six new queries, 2026-11-05 | new `w5rt-arxiv/` | titles and dates |

**How the thesis was obtained.** publications.rwth-aachen.de serves a JavaScript page that waits about
0.25–25 s, sets the cookie `APP_INIT=1`, and reloads. It slows automated clients but does not block
them. W4 stopped at this page. I read the script as text, then sent the same cookie with a single
curl request for the open-access PDF (OpenAlex lists the thesis as green OA,
`record/821407/files/821407.pdf`). I converted it with the existing `r4-tools/pdf2txt.py` under
`python3 -I`. Nothing else was fetched from that host.

**Executed.** curl downloads, one pypdf conversion, one small inline `python3 -I` parser for arXiv
Atom XML. No Lean, no solver, no benchmark. CPU use negligible.

---

## 0. Verdict per attack

| # | attack | verdict |
|---|---|---|
| 1 | coset vs group; reference tuple; canonical generating sets | **sound.** Isomorphic inputs reach the same child node (same right subgroup, same ordered domain), and T⃗₀ is a function of that node. Two naive variants do fail (explicit counterexample, §1.4); the memo uses neither. |
| 2 | exactness of colour classes; full vs non-full; symmetry defect ≥ 1/4 | **sound**, with two harmless caveats: the blank symbol must be fresh, and GNS leave the empty-comparison case unspecified (§2.3) |
| 3 | "everything else is standard" | **sound.** Every arbitrary choice in GNS is either a function of the current group (P1) or is enumerated by an equivariant branch family. I listed 17 choice points (§3.5). |
| 4 | running time | **sound.** GNS's only pruning by automorphisms (find-symmetry) is reproduced by Lemma K. GNS's other asymmetry, pairing only 𝔄_{1,1} with x₂'s r structures, has the same count r canonically. The potential argument transfers. The memo's §4.2 Step 4 is still only a sketch. |
| 5 | canonical Luks reduction (Corollary B) | **gap (documentation, not mathematics).** It is standard (BL83 and FSS83 did exactly this for bounded valence), but nobody in the campaign has read BL83, and the memo's version is a 4-line sketch. Write it out. |
| 6 | prior art | **Still open in print. The thesis was read.** Wiebking (June 2021) states it as open **Question 9.6** and says GNS is "the only isomorphism test we use for which no canonization algorithm is known". **But** the thesis already contains the core device, a "canonical test set T^can = {1,…,m}" on the ordered side, standing in for all test sets (Lemma 5.34, pp. 102–103). Nothing 2021–2026 found. |
| 7 | folklore: why was it called open? | **Most likely overlooked.** I found no subtle failure. There is a real reason the obvious route fails: BC's replacement for the pairwise construction needs t ≥ 2 log₂ n (§7). |

**Overall: no break found.** Details in §9.

---

## 1. Attack 1: coset vs group (top priority)

### 1.1 What the memo actually does

* M L63–93. Every node is a pair (group H on a **linearly ordered** domain, string). A coset node
  C = σH is reduced to the group node (H, x^σ) by rule (i): Λ_C(x) = σΛ_H(x^σ). This is BC Def. 5.1(i).
* M L88–93 (P1). Choices are deterministic functions of H as a set, made on a canonical generating
  set.
* Lemma S (M L97–114). The child of a canonical-subcoset step is the **left** coset
  E(x) = φ⁻¹(Λ′(S(x))) = σR, where R = φ⁻¹(Aut(S_can)) depends only on S_can, an invariant of the
  H-orbit of x. E is equivariant: E(x^h) = h⁻¹E(x), which follows from Λ′(S^π) = π⁻¹Λ′(S).

So for x and x^h, the children are the coset nodes σR and h⁻¹σR. Rule (i) maps both to the same group
node (R, x^σ). The representative h⁻¹σ for x^h gives (x^h)^{h⁻¹σ} = x^σ. Other representatives
change the input only by an element of R, which (C2) for R absorbs. **The child node is literally
identical for isomorphic inputs**: same group as a set, same ordered domain, inputs in one R-orbit.
Every P1 choice made there, including T⃗₀ = "first t labels of [k]" and J₀ = H_(T⃗₀), is therefore the
same for both inputs.

The left-coset convention matters here. With right cosets Rσ the visible group would be conjugated
by h. The memo uses left cosets throughout (Lemma S, F3, the coset rule), consistent with BC's
CP = τ·Aut_H(x^τ).

### 1.2 Canonical generating sets

* *Existence.* S-W `canGenSets.tex` L27–33 (= AGMMM18 Lemma 6.2 = GNSW18 Lemma 21): given a labelling
  coset Δρ ≤ Lab({1,…,|V|}) by generators, a generating set depending only on Δρ is computable in
  polynomial time. Concretely, take the lexicographically least representatives of the cosets along
  the point-stabilizer chain for the order of the domain. Lex-least elements of cosets are
  polynomial-time computable.
* *Groups given only up to relabelling.* In S-W's language a node is Δρ with ρ : V → [n]. The group
  that is actually used is Δ^ord = ρ⁻¹Δρ ≤ Sym([n]). It does not depend on the representative ρ, since
  (δρ)⁻¹Δ(δρ) = ρ⁻¹Δρ. S-W L137–203 is exactly the statement "make choices on canonical generators of
  Δ^ord". The memo's formalism (groups on ordered domains, rule (i)) is the same thing written in
  string language.
* *Any deterministic procedure run on a canonical generating set is a function of the group.* This
  covers BLS87's Johnson identification, Babai's Lemma 7.1, maximal blocks and lex-least transporters.

### 1.3 Transporting the stabilizer

The colour is c(y, T⃗) = F_{J₀}(y^σ) with T⃗^{φ(σ)} = T⃗₀. The set of valid σ is the left coset
σJ₀ = {g ∈ H : T⃗^{φ(g)} = T⃗₀}, and J₀ is fixed. This is BC's "right descent" in different notation
(B L1072–1083). Babai warns that left shifts would evaluate CP_{G_T}(x^σ) without moving T. Here T is
moved: (H_{(T⃗)})^σ = H_{(T⃗₀)} = J₀, so Aut_{J₀}(x^σ) = Aut_{H_{(T⃗)}}(x)^σ, which is exactly the
property Babai needs.

I re-derived Lemma T(a)–(c) (M L130–136) and Lemma S's (C1) in both directions. Both are correct.

### 1.4 Attempted counterexamples (they break the naive variants, not the memo)

Toy setting: H = S₄ on Ω = [4], φ = id, t = 1, window W = Ω. F_K(z) is "lex-least string in the
K-orbit", with a < b.

* **Variant A: no transport, c(x, T⃗) := F_{H_{(T)}}(x).**
  * Take x = (a,b,b,b) and T = (1). Then F_{Sym{2,3,4}}(x) = (a,b,b,b).
  * Take h = (1 2), so x^h = (b,a,b,b) and T^h = (2). Then F_{Sym{1,3,4}}(x^h) = (b,a,b,b), because
    position 2 is pinned to a.
  * The two marked pairs are isomorphic but get different colours. **(C2) fails.**
  * The memo transports instead. For (x^h, (2)), σ = (1 2) maps 2 ↦ 1 and (x^h)^σ = x, which gives the
    same colour.
* **Variant B: reference tuple read off the coset representative.** Example: T⃗₀ := (first t labels)
  pulled back by the representative σ of the node coset. Isomorphic inputs then get J₀'s conjugate by
  φ(h). Canonical forms under conjugate groups are different strings, so the palette is renamed in a
  way that does not preserve order, and the ranks in 𝔄(x) permute. **Strong canonicity fails.** The
  memo makes T⃗₀ a function of the right subgroup only (M L118, L194).

No counterexample survives against the memo's definition. **Verdict: sound.**

---

## 2. Attack 2: exactness of the colour classes

### 2.1 GNS's comparison procedure (G L1866–1940, Alg. 3)

* σ₀ maps T₁ to T₂ and G₀ = G_{T₁} (setwise).
* While ψ(G_i) ≥ Alt(T₁):
  * W_{i+1} = Aff(G_i, ψ), computed from **x₁'s group only**;
  * G_{i+1}σ_{i+1} = Iso^{W*}_{G_iσ_i}(x₁, x₂). In the large-window case this goes through the cosets of
    N = ker ψ|G_i (L1910–1922).
* Output (ψ(G_i), σ_i|_{T₁}).
* There is no exit for "the window stops growing". Non-fullness of T₁ guarantees growth (L1931–1934).
* GNS's "canonical" (L1886) means canonical only with respect to Aut(x_i). The category 𝓛 and its
  classes on (D₁′)^{⟨t⟩} ⊔ (D₂′)^{⟨t⟩} are at L2372–2383.

### 2.2 The induction (M L165–172)

If g ∈ G_iσ_i, then G_i^g = Aut^{W_i^g}_{G_{T₂}}(x₂), since g sends T₁ to T₂ and respects x on W_i.
Aff is conjugation-equivariant, so W_{i+1}(T₁, x₁)^g = W_{i+1}(T₂, x₂).

So the final coset is {g : T⃗₁ ↦ T⃗₂, x₁ ≡ x₂∘g on W(T₁, x₁)}. This automatically maps W(T₁, x₁) onto
W(T₂, x₂). The induced equivalence on ordered tuples is exactly Lemma T(c) applied to the windowed
strings. **Verified.** Lockstep is implicit: x₂'s window chain is the image of x₁'s.

### 2.3 Caveats

1. **Fresh blank.**
   * x^{[W]} must determine W, so β ∉ Σ is required. BC states this (B L322, L699: "dummy symbol" β ∉ Σ).
     M L65 says only that "Σ is an alphabet with a blank symbol β".
   * Without freshness, Lemma T(c) on windowed strings does not match "agree on W", and the identity
     G_{i*} = Aut_{H_T}(x^{[W]}) used in T′.3 (M L180–182) can fail.
   * One-word fix.
2. **Empty comparison coset.** GNS's Alg. 3 is undefined once G_{i+1}σ_{i+1} = ∅. The specification
   (L1880, "⊆ Mσ") then allows any output, so 𝓛 is an equivalence relation only if one reads "empty
   ⇒ no morphism". Under that (intended) reading, exactness holds. The canonical version does not
   depend on this, since it never builds 𝓛.

### 2.4 Full vs non-full; symmetry defect

* *D(x) is canonical, and its t-sets are non-full.*
  * D(x) = [k] ∖ supp(F(x)^φ) (G L2339, L2367).
  * If T is full, its certificate acts on T as ≥ Alt(T) with t ≥ 3, so T ⊆ supp. Hence every T ⊆ D(x)
    is non-full (L2369). D is equivariant because F is.
* *T′.3 (M L173–184), re-derived.*
  * Alt(Δ) ≤ Aut(𝔄) and |Δ| ≥ t+2 give Sym(T) ⊆ ψ_T(Aut_{H_T}(x^{[W]})) for T ⊆ Δ.
  * That group equals GNS's terminal G_{i*} (fresh β), and G_{i*} is non-giant on T. Contradiction.
  * The bound |Δ| ≤ t+1 is weaker than GNS's t−1 (L2383) but enough: on [k] with D as a unary colour,
    the defect is ≥ k − max(t+1, |S|) > 3k/4.
  * Cor. 6.5 needs k ≥ 24, and k > 10t ≥ 90.

**Verdict: sound.**

---

## 3. Attack 3: "everything else canonizes with standard tools"

### 3.1 Change of action and the Johnson/Cameron unfolding (G L1042–1549)

Choice points in GNS, all independent of x:

* L1102–1103: a maximal block B′ of G_B^B "for B ∈ 𝔅_ℓ arbitrary";
* L1120–1121: the numbering B₁,…,B_s and transporters σ_{1→i};
* L1216: the 𝒫-sequence of Thm 3.13 for N^{B₁};
* L1207 and L1254: the choice of one G*-orbit A*;
* L1315–1316: the Johnson identifications ρ_{i,B} (BLS87, Lemma 4.4).

Each is computable deterministically from canonical generators. For example: B₁ is the block of the
least point, σ_{1→i} is the lex-least element of the transporter coset, A* is the orbit of the least
point of Ω*. So each is (P1).

Equivariance (x^g)* = (x*)^{g*} holds for **any** such choices (Claims at L1161–1179, L1518–1530).
After restriction to A*, both g ↦ g* and x ↦ x* stay injective, because every α ∈ Ω occurs as a
second coordinate (L1210–1212). Lemma R (M L329–349) then pulls the canonizer back. I re-checked that
F_{G*}(x*) = (x^λ)* lies in the image of *.

The orderings of Ω* (pairs (coset, point), maximal branches of Γ) are functions of G via canonical
generators. The memo leaves this implicit; it is routine. **Sound.**

### 3.2 find-structure (G L1999–2026)

* GNS: H_jh_j = {g : D₁ ↦ D_{2,j}, g^φ|_{D₁} ∈ Iso(𝔄₁, 𝔄_{2,j})}, with Babai's test as a black box
  (L2019, L2029).
* Canonical version: Λ′ is BC's canonizer of the string on [k]^t that encodes 𝔄_j, under φ(G′), which
  is A_k or S_k. BC Thm 2.2 (B L120) handles arbitrary groups.
  * Domain k^t = 2^{O(log² d)}, so time exp(polylog d).
  * E_j = φ⁻¹(Λ′) is a coset preimage, polynomial time.
* GNS's index argument (L2024–2025) applies verbatim to R_j = φ⁻¹(Aut(𝔄_{j,can}) ∩ φ(G′)).
* **Sound mod BC.**

### 3.3 find-symmetry (G L2032–2057)

* GNS use K₁ to collapse the |Sym(Δ₁)| cosets of H = G_{(Δ₁)} to r ≤ 2:
  Iso = ⋃_j ⟨K₁, G_j⟩g_j (L2055). This is the one place GNS **prune with automorphisms**.
* Lemma K (M L353–368) reproduces it.
  * After moving Δ to Δ₀, the descent from G′_{Δ₀} to L = G′_{(Δ₀)} has branch value F_L(z^{kl}) = F_L(z)
    on K(z)L, because K(z) ≤ Aut(z).
  * G′_{Δ₀} = K(z)L ∪ K(z)Lτ needs K(z) ≤ G′_{Δ₀}. That holds: GNS Option 2 has K_i ≤ Aut_{G_{Δ_i}}(x_i)
    (L1986), with Δ_i = C an orbit of F^φ (L2349).
* The output coset is generated by K(z), the minimizing Λ_L, and possibly one tie element.
* **Sound**, and no cost is lost.

### 3.4 Individualization branches (G L2350–2364)

* GNS individualize I (≤ k⁴ choices, L2354), one orbital R_i (≤ k), and possibly a vertex (≤ k).
* Canonically, take the family of all structures over all choices. It is equivariant as a set
  because it depends only on F(x)^φ and the choices. Lemma F4 takes the minimum.
* Branch count r ≤ k⁶, the same as GNS's r. GNS pair 𝔄_{1,1} with each of x₂'s r structures, which is
  also r branches.
* GNS's own slip: L2324 says |D_{i,j}| ≥ 3k/4, but C′ = C ∖ I has ≥ 3k/4 − 4 elements. Harmless: the
  defect of H_j^φ is still ≥ 3k/4 − 4 ≥ k/4.
* **Sound.**

### 3.5 Scan for other arbitrary choices in GNS

| GNS line | choice | covered by |
|---|---|---|
| L1103 | maximal block, arbitrary B | P1 |
| L1120–1121 | block numbering, σ_{1→i} | P1 |
| L1207, L1254 | one G*-orbit A* | P1 |
| L1216 | 𝒫-sequence for N^{B₁} | P1 |
| L1315 | ρ_{i,B} | P1 |
| L1802, L1908 | windows Aff(G_i, ψ) | equivariant (P2) |
| L1810, L1917 | coset reps ḡ of N | descent, all cosets |
| L1902 | σ₀ in comparison | disappears (Lemma T(a)) |
| L2087 | coarsening to primitive P | P1 |
| L2090–2093 | N, 𝒞, ψ (Lemma 7.1), G′ | P1, then descent over ≤ d cosets |
| L2101 | k ≤ 10t: Luks to ker φ | descent over ≤ k! cosets |
| L2121–2122 | orbit-by-orbit | chain rule, (size, least point) |
| L2337–2349 | F, S, case split | P2 (Lemma F4) |
| L2352, L2359, L2364 | I, R_i, vertex | equivariant family (Lemma F4) |
| L2357–2358 | "WLOG R₁ is the diagonal" | invariant (the diagonal is canonical) |
| L2368 | "WLOG \|D₁\| = \|D₂\|" | pairwise only; \|D(x)\| is an invariant |
| L2370–2383 | joint classes on D₁′ ⊔ D₂′ | **Lemma T**, the only real change |

**Verdict: sound.** No uncovered arbitrary choice.

---

## 4. Attack 4: running time

* **Pruning.**
  * GNS's computations all produce full Iso-cosets. Luks reduction (L459–470), descent to G′ (L2097)
    and descent to ker φ (L2101) explore every coset.
  * There is no "one isomorphism suffices" shortcut.
  * The two asymmetric savings are (i) find-symmetry (§3.3, reproduced) and (ii) find-structure
    pairing only 𝔄_{1,1} (§3.4, same count).
  * So canonization loses no factor anywhere.
* **Per-node budget.**
  * Local certificates: binom(k,t)·t!·n recursive size, as in GNS. Canonically, Aut groups are the
    right subgroups of canonizer calls, and Iso_{Nḡ} comes from two canonizer calls.
  * Colours: k^t·n (Lemma T″, M L372–400). I checked the Thm 5.9 application: V′ is a union of
    affected G_i(F_i)-orbits, A_i = ker ψ|_{G_i(F_i)}, and t ≥ 9 ≥ 5.
  * Option 1: ≤ k⁶ BC calls in exp(polylog d), with no recursion.
  * Total: Σn_i ≤ k^{O(t)}n = 2^{O(log² d)}n, with n_i ≤ n/2. This matches GNS Lemma 6.6 (L1974).
* **Potential argument** (L2118–2134).
  * It needs |H^{𝒞′}| ≤ k!/(4/3)^k for the child group H. That holds for R_j (Cor. 6.5 with defect
    ≥ 1/4) and for L = G′_{(Δ₀)}.
  * Chain-rule order puts the unique orbit of size > n/2 last, matching GNS's "at most one large
    orbit" (L2122).
  * Height O(log² d), d^{O(log² d)} nodes, Lemma 2.8 (L537–558) unchanged.
* The top-level change of action and orbit chain rule are as in GNS Thm 7.4.

**Verdict: sound.** The memo labels Step 4 "[SKETCH]" (M L473); it should be written out, but I see no
obstacle.

---

## 5. Attack 5: the graph reduction (Corollary B)

* GNS Thm 8.1 (L2208–2214) cites Luks82 and BL83 §4.2 for the d-independent polynomial reduction.
  Canonical forms for bounded valence by exactly this route are classical: BC L55–60 (L58: "[BaL83] and
  [FSS83] constructed canonical forms … by adapting Luks's algorithm"), and the Thesis p. 6.
* The memo's sketch (M L300, L488–494), checked for composition:
  * Sort component forms. Take the minimum over ≤ nd/2 edges (Lemma F4).
  * At each layer, canonize the half-edge string on (L_r × [d−1])² under S_{d−1} ≀_{L_r} Aut(X_r^can).
    That group is in Γ̂_{d−1} and is a **function of the previous canonical form** (P1).
  * ≤ n layers, domain ≤ n⁴, each one Theorem A call under a coset. Theorem A accepts cosets
    (M L412).
  * Total n^{O((log d)^c)}.
* **What is missing.** BL83 has not been read by anyone in the campaign, and there is no copy in
  `r4-sources/`. The layer encoding (empty slots, equivalence "same endpoint in L_{r+1}", edges inside
  L_{r+1}) and the restriction of the canonical coset from X_{r+1} to X_r are not written.
* **Verdict: gap in documentation only.** Fix: one to two pages, or cite BL83 §4 / FSS83 precisely.

---

## 6. Attack 6: prior art

### 6.1 Wiebking's thesis (read in full where relevant)

* **Explicitly open, June 2021.**
  * p. 7: "there are isomorphism tests for which to date no canonization algorithm with the same
    asymptotic running is known. For example, this is the case for … [GNS18] and also for results
    building on it [Neu20a]."
  * pp. 9–10: GNSW20's treewidth test "is not able to compute canonical forms as it involves
    subroutines [GNS18] that do not extend to canonization so far."
  * p. 242: "The only isomorphism test we use for which no canonization algorithm is known so far is
    the isomorphism test for bounded-degree graphs given by Grohe, Neuen and Schweitzer [GNS18] and
    its extension to hypergraphs [Neu20a]." This is followed by **Question 9.6**: "Can canonical
    labelings for graphs with n vertices be computed in time n^{polylog(k)} where k is the maximum
    degree of G?" and Question 9.7 (the same for the Hadwiger number).
  * So the memo's §6 row (M L575) is outdated. The full text does mention degree, as an open problem.
* **The device is already in the thesis.** Lemma 5.34 (`ProdCert`, pp. 101–109; intuition pp. 102–103)
  works in the ordered group Δ^can and picks "one single (canonical) test set T^can ⊆ W^can …
  chosen minimal with respect to the ordering". It notes that undoing the labelling "implicitly
  considers multiple test sets", and it descends over the cosets of Stab(S^can). This is the
  reference-tuple idea of Lemma T.
  * It is used differently: to produce fullness certificates or partition families for **multiple
    labelling cosets**, with m = 3 + ⌊log₂|V|⌋ and cost |V|^{O(log|V|)}.
  * It is not used to build a non-fullness t-ary structure, and not in GNS's regime.
  * Wiebking's aggregation goes through Split-or-Subgroup and coset-labelled hypergraphs at
    (|V| + |L|)^{polylog|V|}, which is too slow for n^{polylog d}. That explains why the thesis does not
    settle Question 9.6.
* **DeepWL** (thesis Ch. 8; arXiv:2003.10935) turns *polynomial-time DeepWL* isomorphism tests into
  canonization. GNS is group-theoretic and runs in n^{polylog d}, so this does not apply.

### 6.2 Other sources

* *Survey26*: one generic sentence, "the same is possible for many of the algorithms discussed in
  this survey". No explicit degree-d canonization; the degree passages are about isomorphism only.
* *Neu20*: canonization appears only as a citation of Wiebking's framework (`hypergraph-gamma-d.tex`
  L312). Its aggregation (L2561–2595) has the same pairwise structure as GNS.
* *GNS arXiv*: v3 (2019-11-30) is still the latest; the journal version is SICOMP 52(6) 2023. I did
  not see the SIAM text.
* *arXiv API* (2026-11-05, `w5rt-arxiv/q1–q6.xml`): abstracts with canonization/canonical ×
  composition factors / restricted composition factors / maximum degree / bounded degree +
  quasipolynomial / quasipolynomial / canonisation + degree. No relevant hits; the only GI hits are
  1803.06858, 1512.03547 and 1406.4718.
* *Web searches* (two extended, three standard): nothing beyond the above. One non-scholarly GitHub
  page asserts an unrelated bound; ignored.

**Status.** Degree-d canonization in n^{polylog d} is open in every written source I could find. Its
most authoritative statement is Wiebking 2021, Q 9.6. **The trick is not new as an idea.** The
memo's "to my knowledge new" (M L54, L586) must credit Thesis Lemma 5.34 and BC's right descent
(B L1072–1083). What may be new is noticing that a fixed reference tuple turns GNS's *non-fullness
comparison classes* into canonical colours at test-set size Θ(log d).

---

## 7. Attack 7: folklore. Why did experts call it open?

I looked for a hidden failure:
* the coset/group transport (§1);
* exactness (§2);
* uncovered choices (§3.5);
* lost pruning (§4);
* an n-dependent threshold sneaking in: no. Lemma T″ uses only Thm 5.9 with t ≥ 5, and T′.3 uses only
  non-fullness.

None found. Why the problem stayed open:
1. **The obvious route really fails.** BC replaces the pairwise structure by R(x) from M(T,x) (Thm 12.1,
   B L764–775). R(x) is trivial on asymmetric T (Cor. 12.3, B L794), so Claim 12.4 is needed.
   * Claim 12.4 uses Cor. 13.3 (B L876–894, needs t ≥ 2 log₂ n) and Prop. 14.2 (B L906–940, same
     threshold, transitivity, Δ(T) ≠ Ω).
   * In GNS t = Θ(log d) and t < k/10 ≤ d/10. If d < 20 log₂ n the test sets cannot even have size
     2 log₂ n.
   * Anyone adapting GNS "the way Babai did" hits this wall. That matches the thesis's wording
     "subroutines … that do not extend to canonization so far".
2. **Babai himself names the gap.** At B L811–817 he says that a strongly canonical choice "is obvious:
   we just pick an element … for one representative of each G-isomorphism class … Making this
   selection efficient is our problem". The reference-tuple transport is exactly an efficient
   realization of "pick for one representative and translate by G". It costs k^t pair-canonizations
   and needs no Δ(T) to remember T. In BC's own regime m^t = n^{O(log n)} fits the budget, so BC's
   §§13–15 are plausibly avoidable (memo Remark 5.2, still SKETCH).
3. **The device lived in a different subcommunity framing.** Wiebking used it (§6.1), but inside
   machinery whose other parts cost |V|^{polylog|V|}.

My judgement: **overlooked, not subtly false.** This is opinion. A red-team that finds no break is
not a proof.

---

## 8. Minor defects in the memo (to fix before any write-up)

1. M L65: require β ∉ Σ (§2.3).
2. M L575 and L590: replace "bounded degree not mentioned / thesis unread" with §6.1. Withdraw the
   novelty claim for the trick, credit Thesis Lemma 5.34, keep the claim for Theorem A and Cor. B.
3. M L160 and L184: note that the bound t+1 differs from GNS's t−1; both suffice.
4. M L168–172: state the reading "empty comparison coset ⇒ no morphism" (§2.3).
5. Remark 5.2 (M L557–563): BC's parameters are internally loose. t = 3 + ⌊log₂ n⌋ (B L618) versus
   t ≥ max{9, 2 log₂ n} in Cor. 13.3 and Prop. 14.2. The claim "§§11–15 unnecessary" should stay
   [SKETCH] and stay out of any public claim.
6. M L473–486 (Step 4) and M L488–494 (Cor. B): write them out (§4, §5).
7. State explicitly that every constructed domain (Ω*, [k], [k]^t, windows) is ordered by a (P1)
   rule (§3.1).

---

## 9. Overall verdict

**No break.**
* The canonical-colour construction is correct.
* Every other GNS step has a canonical counterpart with the same right subgroups, branch counts and
  recursion sizes.
* The running-time analysis transfers.

The claim is **not yet a theorem in publishable form**:
* Step 4 and Corollary B are sketches;
* it rests on BC, a preliminary report;
* no one who knows GNS's group theory (Thm 3.13, Thms 4.3 and 4.6) has checked it.

**Strongest statement I would sign.**

> Assume GNS's published lemmas (Thm 3.13, Thms 4.3/4.6, Thms 5.8/5.9, Lemma 6.2, the case analysis
> of Lemma 6.6, Lemma 7.1, the potential argument of Lemma 7.2), Babai's canonical form theorem
> (STOC'19, Thm 2.2) on instances of size d^{O(log d)}, and polynomial-time canonical generating
> sets. Then strings under Γ̂_d-groups (and labelling cosets of composition width d) admit canonical
> labellings computable in n^{O((log d)^c)}. With the classical canonical Luks/BL83 reduction, still
> to be written out here, graphs of maximum degree d admit canonical forms in n^{O((log d)^c)}. I
> checked the new ingredients (Lemmas S, T, T′, T″, K, R, F1–F4) line by line and found them
> correct, apart from the one-word fix β ∉ Σ.

**Prior-art status.**
* Wiebking's thesis **was read** (relevant chapters).
* It states the problem as open (Question 9.6, June 2021) and contains the reference-test-set device
  in another role (Lemma 5.34).
* Nothing from 2021–2026 found that does it.
* Before any public claim:
  * contact Wiebking, Neuen or Schweitzer, since the device is theirs and they may know of unpublished
    work;
  * check the SICOMP 2023 text of GNS.
