# w8-hypercanon: canonical Neuen 2020, and canonization for treewidth and minors in n^polylog

Branch `w8-hypercanon`, 2026-11-05. Builds on `canonization-bounded-degree.md` (the "write-up": Theorem A,
Corollary B, Corollary D) and `w4-gnscanon.md` (the "memo": Lemmas S, T, F1–F4, R, K). Not refereed.
Nothing here depends on HJ (arXiv:2611.01399).

**Task.**
1. Make Neuen's hypergraph isomorphism test for Γ̂_d groups (Neu20) canonical.
2. Treewidth: what Wiebking's n^{polylog k} test needs, and whether canonization follows.
3. Other corollaries (minors, topological subgraphs, genus, t-CR-bounded graphs).
4. Novelty.

**Labels.** As in the memo.
* **[PROVEN]**: complete argument here, using only cited results and the polynomial-time permutation-group
  toolkit.
* **[PROVEN mod X]**: complete, except that X is used without re-proof.
* **[SKETCH]**: argument given, missing details named.
* **[CONDITIONAL: X]**: holds if X holds.
* **[SPECULATION]**: opinion.

**Sources.** All untrusted data, read only, under `scratchpad/r4-sources/`.

| short | what | where | read |
|---|---|---|---|
| Neu20 | Neuen, arXiv:2002.06997 **v2** (Jul 2022). "N…" = line of `hypergraph-gamma-d.tex` | `arxiv-2002.06997/x/` | N189–336 (intro), N500–616, N618–973 (normalization framework), N974–2790 (all of §4), N2792–2963 (t-CR-bounded), N2965–3160 (genus, conclusion): **the whole paper** |
| Thesis | Wiebking, dissertation, RWTH 2021, DOI 10.18154/RWTH-2021-06242 (printed page numbers) | `w5rt-thesis/thesis.txt` | pp. 7–14 (results), 60–64 (§5.2), 100–104 (Lemma 5.34), 133–154 (§6.1), 155–181 (§6.2), 241–242 (Ch. 9) |
| Wie20 | Wiebking, arXiv:1911.11257 (ICALP'20). "W…" = line of `articles/treewidth.tex` unless stated | `w3c-wiebking-1911.11257/x/` | `treewidth.tex` in full, `openQuestions.tex`, `intro.tex` L150–275, statements of `canHyper`, `canSet`, `canObj` |
| GNSW18 | Grohe–Neuen–Schweitzer–Wiebking, arXiv:1803.06858 **v1** (the only arXiv version). "G…" = line of the named file in `articles/` | new dir `w8-gnsw18/` | `bag_subproblem_iso.tex`, `bag_subproblem.tex` in full, `recursive_algo_iso.tex` L1–130 |
| GNW | Grohe–Neuen–Wiebking, arXiv:2004.07671 v2 (minors). "M…" = line of `gi-excluded-minor.tex` | new dir `w8-2004.07671/` | §3 (M535–782), strategy M790–866, main proof M1880–2165 |
| Neu22t | Neuen, arXiv:2011.14730 v3 (topological subgraphs, TALG version). "P…" = line of `gi-topological-minor-talg.tex` | new dir `w8-2011.14730/` | §6 (P1998–2214), main proof P2215–2490 |
| surveys | Grohe–Neuen 2011.01366; Neuen 2026 (Comput. Sci. Rev.) | existing dirs | "canoni" passages |
| arXiv API | queries of 2026-11-05 | new dir `w8-arxiv-queries/` | parsed with `scratchpad/w8-scripts/atom.py` (`python3 -I`) |

Not obtained: Neuen's dissertation (RWTH 2020, DOI 10.18154/rwth-2020-00160; the repository returned 503,
see `w7rt-neuen-thesis/`), which contains the structure-graph lemma Neu20 cites (Neu19 Lemma 6.1.17) and the
coset-labelled hypergraph theorem Neu19 Thm 6.6.7. The TALG texts of Neu20 (TALG 18(3), 2022) and GNSW18
(TALG 2020) were not compared with the arXiv versions.

**Executed.** curl downloads, `tar`, one XML parse with `python3 -I`. No Lean, no solver, no benchmark. CPU
negligible.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Does canonical Neu20 work? | **Yes. Theorem H:** for Γ ∈ Γ̂_d on Ω (n points) given by generators, a coset σΓ, a Γ-invariant partition 𝔓 and a set 𝔛 of m 𝔓-strings (in particular a hypergraph with m edges), a canonical form and the canonical placement coset of 𝔛 under σΓ are computable in (n+m)^{O((log d)^c)}. | correctness **[PROVEN mod Neu20's constructions (Thms `normalize`, `renormalize`, `simplify-on-window` and their properties), GNS Thm V.3, Babai Thm 6(b), the CFSG facts of Neu20's aggregation, Theorem A, BC]**; running time **[SKETCH: transfer of Neu20's virtual-size recursion; inherits GAP-1 and its fix]** |
| 2 | What in Neu20 is pair-dependent? | 21 choice points and patches (§2.2). Four are genuinely pairwise: (a) the Local Certificates Routine run "on all pairs in parallel" with an arbitrary test object and realignment (N2201–2258), (b) Simplify's representative group Γ''₁ (N2053–2061), (c) the joint category on D′₁ ⊔ D′₂ (N2589–2596), (d) find-structure / find-symmetry (N2603–2653). (c) and (d) are as in GNS. **(a) is new and the main obstacle**: Neuen states that renormalization "is not isomorphism-invariant" (N1930) and synchronizes all pairs to cope. | §2 |
| 3 | How is (a) made canonical? | Run the loop on **one** object, transported to a **reference test set** T₀ chosen from the group (Wiebking's "canonical test set", Thesis Lemma 5.34), and canonize under the **setwise** stabilizer H₀ = Γ_{T₀}. Every renormalization is then computed from the canonical prefix and its right group, so it is a function of canonical data (principle P1), and no synchronization is needed. Ordered-tuple colours are read off the ψ-image of the resulting coset (Lemma T^set). Exactness with Neuen's comparison classes is not needed; only the symmetry defect is. | **[PROVEN mod as in row 1]** (Lemmas LC, T^set, AGG) |
| 4 | Treewidth canonization in n^{polylog k}? | **Yes, Theorem TW, and it needs only Theorem A (via Corollary D), not canonical Neu20.** In Wie20 the coset-labelled hypergraph lemma (`cosetHyper`, W257) is only applied to a coset that **already maps hyperedges to hyperedges** (W258–261, W332–336). For such instances GNSW18's own canonical reduction (GNSW18 v1 Lemma 23, second case) turns the problem into canonization of one graph under a labelling coset of composition width ≤ k+1, which is Corollary D. **This corrects write-up §9.2**, which listed `cosetHyper` as a Neu20-type gap. The other isomorphism-only steps of Wie20 (`isoBasic`, `isoBasicClique`, `isoTree`) rewrite canonically in the Schweitzer–Wiebking framework, using only Corollary D and Wiebking's quasipolynomial canonizers on ≤ k+1 points. | **[PROVEN mod Theorem A, Wiebking's `canHyper`/`canObj`, the invariant decompositions of LPPS/Leimer/Elberfeld–Schweitzer]**; the canonical rewrite of Wie20 is **[SKETCH]** |
| 5 | Is it stated open? | Wie20 outlook (`openQuestions.tex` L19–27): once GNS is canonical, "the present isomorphism algorithm for graphs parameterized by treewidth should then be amenable to canonization as well". Thesis p. 10: the 2^{k·polylog k} FPT test "is not able to compute canonical forms as it involves subroutines [GNS18]". Thesis p. 179 and p. 181: the minor-free test is isomorphism-only because "[GNS18, Neu20a] are not available for canonization so far". Thesis Q 9.6 (degree) and **Q 9.7 (Hadwiger number)**, p. 242. Treewidth n^{polylog k} canonization is not a separate numbered question, but the thesis's own n^{polylog k} treewidth result (Cor. 6.30) is stated for isomorphism only. | sources |
| 6 | Other corollaries | **H1** canonical coset-labelled hypergraphs (hyperedges of size ≤ d) under Γ̂_d labelling cosets, (n+m)^{polylog d}: [PROVEN mod Theorem H, Corollary D]. **H2** canonical t-CR-bounded graphs and pairs, n^{polylog t}: [SKETCH, mod H]. **H3** canonical forms for K_{3,h}-minor-free graphs and Euler genus g, n^{polylog h}, n^{polylog g}: [SKETCH, mod H2 and canonical 3-connected decomposition]. **H4** canonical forms for K_h-minor-free (GNW) and K_h-topological-subgraph-free (Neu22t) graphs in n^{polylog h}, answering Thesis Q 9.7: [CONDITIONAL on Theorem H, H1, H2; DP rewrite SKETCH]. FPT 2^{k·polylog k}·poly(n) treewidth canonization: [SPECULATION]. | §4 |
| 7 | Novelty | No prior or concurrent canonical version of Neu20, GNW, Neu22t or of n^{polylog k} treewidth found (arXiv API 2019–2026-11, three extended web searches, both surveys, the thesis). The devices are Wiebking's (canonical test set, labelling cosets) and Babai–Luks's (canonical subcoset). Experts may call the results expected (Wie20 predicted the treewidth case). | §5 |
| 8 | Gaps | No mathematical gap found in the new canonical steps. Named risks: Neu20 lemmas not re-proved; Theorem A's own status; Neu20 inherits GAP-1 (N2716, same text as GNS) and has a harmless ordering slip in its cost accounting (§2.8); the Wie20 rewrite and H2–H4 are sketches. | §6 |

**Verdict.**
* The canonical-subcoset device does push through Neu20, with one new ingredient: a single-object local
  certificate loop at the *setwise* stabilizer of a group-chosen test set, in which every renormalization
  is computed from canonical data. This gives canonical forms for hypergraphs under Γ̂_d groups in
  (n+m)^{polylog d} (Theorem H).
* Treewidth is easier than expected: it follows from Theorem A alone (Theorem TW). It is exactly the
  canonization that Wie20 predicted would follow once GNS is canonical.
* Minors, topological subgraphs and genus follow from Theorem H plus routine canonical rewrites (H3, H4),
  at sketch level.

---

## 1. Tools

### 1.1 Used from the write-up and memo without change

* Canonizers (write-up Def. 2.1), the coset rule, labelling cosets (Remark 2.3), principle P1 (§2.4),
  windowed strings with membership tags (§2.5).
* Lemmas F1 (restriction), F2 (sequential chain rule), F3 (descent), F4 (branch families), S (canonical
  subcoset), R (change of action), K (canonical find-symmetry).
* **Theorem A** (strings under Γ̂_d cosets, n^{O((log d)^c)}) and **Corollary D** (a graph or string on V
  with a labelling coset Δρ, Δ ∈ Γ̂_d: canonical labelling coset in |V|^{O((log d)^c)}).
* BC Thm 2.2, used only on structures with ≤ k ≤ d points and arity t = O(log d).
* The GAP-1 fix (write-up §7.3): the partition 𝒞′ becomes the top partition of the next round.

Theorem A is a **group** canonizer for strings. Below it is also applied to strings on a set Γ on which the
current group A acts through a homomorphism θ : A → Sym(Γ) (multiplicity strings on 𝔓, linking graphs).
This is Lemma S with S(x) = the string and Λ′ = the Theorem A canonizer under θ(A) ∈ Γ̂_d (quotients stay in
Γ̂_d, GNS Lemma 2.4). **[PROVEN mod Theorem A]**

### 1.2 Equivariant coset maps

Neu20's local-certificate loop changes its domain several times, and the loop's groups are not
automorphism groups of anything defined before the loop starts. The clean bookkeeping is the weak notion
of canonical labelling that Schweitzer–Wiebking use.

**Definition E.** Let H ≤ Sym(Ω) and let 𝒵 be an H-invariant set of objects. An *H-equivariant coset map*
(ECM) assigns to each Z ∈ 𝒵 a left coset C(Z) = πR(Z) ⊆ H of a subgroup R(Z) ≤ H such that
C(Z^h) = h⁻¹C(Z) for all h ∈ H.

**Lemma E1.** **[PROVEN]** For an H-ECM: R(Z^h) = R(Z); and Aut_H(Z) ≤ C(Z)C(Z)⁻¹ = πR(Z)π⁻¹ for any
π ∈ C(Z).
*Proof.* h⁻¹C(Z) has right group R(Z). If a ∈ Aut_H(Z) then C(Z) = C(Z^a) = a⁻¹C(Z), so a ∈ C(Z)C(Z)⁻¹. ∎

The Λ_H of a canonizer is an ECM with R = Aut_H(F_H(x)).

**Lemma E2 (composition at a prefix).** **[PROVEN]**
* *Setting.* C₁ is an H-ECM on 𝒵 with right group R₁(Z). A *prefix* is a value p̄(Z) such that
  * it is computed from Z^π and is the same for every π ∈ C₁(Z);
  * p̄(Z^h) = p̄(Z) for h ∈ H;
  * it determines R₁(Z).
* For each prefix value q with right group R, let 𝒵_q := {Z^π : π ∈ C₁(Z), p̄(Z) = q}. This set is
  R-invariant, since Z^{π}r = Z^{πr}. Let C₂^q be an R-ECM on 𝒵_q.
* *Definition.* C(Z) := π·C₂^{p̄(Z)}(Z^π) for any π ∈ C₁(Z).
* *Claim.* C is a well-defined H-ECM, and C(Z) ⊆ C₁(Z).

*Proof.*
* For π′ = πr (r ∈ R): πr·C₂(Z^{πr}) = πr·r⁻¹C₂(Z^π).
* For Z^h, use π′ = h⁻¹π ∈ C₁(Z^h). Then Z^{hπ′} = Z^π and p̄ is unchanged, so C(Z^h) = h⁻¹C(Z). ∎

When C₁ and C₂ come from canonizers, this is Lemma F2 (memo). The point of E2 is that **anything computed
from the prefix by a deterministic procedure, for example a renormalization, is identical for every object
in the H-orbit.** That replaces Neuen's synchronization of pairs.

**Lemma E3 (change of action at a prefix).** **[PROVEN]** In the setting of E2, suppose that the prefix q
determines an injective homomorphism ι_q : R → Sym(Ω_q) and an injective map Z′ ↦ Z′_* on 𝒵_q with
(Z′^r)_* = (Z′_*)^{ι_q(r)}. If C* is an ι_q(R)-ECM on {Z′_* : Z′ ∈ 𝒵_q}, then C₂(Z′) := ι_q⁻¹(C*(Z′_*)) is an
R-ECM on 𝒵_q.
*Proof.* ι_q⁻¹(C*((Z′^r)_*)) = ι_q⁻¹(ι_q(r)⁻¹C*(Z′_*)) = r⁻¹C₂(Z′). ∎
This is Lemma R with the auxiliary construction allowed to depend on the prefix.

### 1.3 Lemma T^set: ordered colours from a setwise test set

This is the memo's Lemma T, moved from the pointwise stabilizer of a reference *tuple* to the setwise
stabilizer of a reference *set*. That is the form of Wiebking's canonical test set (Thesis Lemma 5.34,
p. 103: "Define T^can := {1, …, m} ⊆ W^can"; "Define Δ^can_T := … stabilize the test set T^can setwise").

**Lemma T^set.** **[PROVEN]**
* *Setting.*
  * H ≤ Sym(Ω), φ : H → Sym([k]) with φ(H) ≥ A_k and k ≥ t + 2. So φ(H) is transitive on t-sets.
  * T₀ := {1, …, t} (P1, since [k] is labelled from canonical generators). H₀ := φ⁻¹(Stab(T₀)), and
    ψ : H₀ → Sym(T₀) is the induced action.
  * C is an H₀-ECM, with right group R, on an H-invariant set 𝒵.
* *Definition.* For Z ∈ 𝒵 and an ordered tuple T⃗ of distinct points with underlying set T:
  * choose σ ∈ H with T^{φ(σ)} = T₀;
  * E(Z, T) := σ·C(Z^σ) ⊆ H and R(Z, T) := R(Z^σ);
  * c(Z, T⃗) := (R(Z^σ), the ψ(R(Z^σ))-orbit of T⃗^{φ(e)}) for any e ∈ E(Z, T).
* *Claim.*
  * (a) E, R and c are well defined (independent of σ and e).
  * (b) c(Z^h, T⃗^{φ(h)}) = c(Z, T⃗) for h ∈ H.
  * (c) If c(Z, T⃗^π) = c(Z, T⃗) for all π ∈ Sym(T), then ψ(R(Z^σ)) = Sym(T₀).
  * (d) ψ_T(Aut_{H_T}(Z)) is conjugate to a subgroup of ψ(R(Z^σ)), with H_T := φ⁻¹(Stab(T)).

*Proof.*
* (a) If σ′ = σg with g ∈ H₀, then σg·C(Z^{σg}) = σg·g⁻¹C(Z^σ). R is unchanged by Lemma E1. Two elements
  of E differ by r ∈ R on the right, and T⃗^{φ(er)} = (T⃗^{φ(e)})^{ψ(r)}.
* (b) Use h⁻¹σ for (Z^h, T^{φ(h)}): the transported object is Z^σ again, E becomes h⁻¹E, and
  (T⃗^{φ(h)})^{φ(h⁻¹e)} = T⃗^{φ(e)}.
* (c) With σ and e fixed, (T⃗^π)^{φ(e)} runs through all t! orderings of T₀. All lie in one ψ(R)-orbit,
  so ψ(R) is transitive on orderings, i.e. ψ(R) = Sym(T₀).
* (d) Lemma E1 for H₀ and Z^σ, conjugated by σ. ∎

*Remark.* Colours are compared through canonical generating sets of R and the lexicographically least
ordering in the orbit. Only (b) and (c) are used below. In particular the colours need **not** reproduce
Neuen's comparison classes. The memo's exactness statement (Lemma T′.2) was never needed for the
recursion, only the symmetry defect (Lemma T′.3).

---

## 2. Neu20, component by component

### 2.1 The algorithm (Neu20 v2)

* **Problem.** Generalized string isomorphism (N1007–1018): a group Γ, a Γ-invariant partition 𝔓, and sets
  𝔛, 𝔜 of 𝔓-strings (P, x : P → Σ). Hypergraphs and sets of strings reduce to it equivariantly (N987–1005).
* **Progress measure.** The *d-virtual size* s = Σ_P |P|·m_𝔛(P)^{f(d)+1}, with f(d) = O(log d) (N1570–1578).
* **Normalization once.** Thm `normalize` (N1126–1200) gives an equivalent instance with an almost d-ary
  sequence. It is built from structure graphs (N618–973).
* **Main algorithm** (Alg. N2736–2760; Lemma `partition-small-size-recursion`, N2671–2728):
  * intransitive → orbit by orbit, combined by Lemma `combine-windows` (N1624–1690);
  * semi-regular top → Luks with BalanceOrbits (N1695–1712, Lemma N1045–1067);
  * otherwise → giant representation (N2664), Local Certificates (Thm N2175, Alg N2201), aggregation
    (Lemma N2499), find-structure / find-symmetry (N2603, N2632), and recursion on the potential k
    (N2710–2725).
* **What differs from GNS.** Inside the local-certificate loop the window automorphisms Γ_(Ω∖W) are not
  automorphisms of a set of strings unless 𝔛[W] is simple (Lemma `extending-window-automorphisms`,
  N1732–1756). So after each window step the instance is *simplified* (Thm `simplify-on-window`, N1935;
  copies of each block for each W-restriction) and *renormalized* (Thm `renormalize`, N1202; implanted
  structure graphs).

### 2.2 Choice points and pairwise steps

| # | Neu20 place | what is chosen or paired | canonical treatment | label |
|---|---|---|---|---|
| 1 | Hypergraph ↔ set of strings ↔ 𝔓-strings (N987–1005) | — | equivariant injective encodings (Lemma R) | [PROVEN] |
| 2 | Structure graphs: γ_{1→i} (N935), v_P (N1152, N1497), Neu19 Lemma 6.1.17 internals | transporters, nodes | functions of (Γ, 𝔓, 𝔅-sequence) only: P1 | [PROVEN mod Neu19 being a deterministic construction] |
| 3 | Thm `normalize` (N1126) | Ω*, φ, f, f′ | group-only construction; 𝔛 ↦ 𝔛* injective (f maps each P* onto a block of 𝔓, every block is hit, and x* = x∘f) and equivariant (proof N1170–1199): Lemma R | [PROVEN mod Neu20 proof] |
| 4 | orbit-by-orbit order (N1676–1692) | order of orbits | chain rule, orbits ordered by (size, least point) | [PROVEN] |
| 5 | `CombineWindows` (N1624–1690): GNS graph iso of linking graphs G(𝔛), G(𝔜) | **pairwise** (routine) | Lemma W (§2.3): canonical subcoset of G(𝔛) by Corollary D | [PROVEN mod Theorem A] |
| 6 | `BalanceOrbits` (N1045–1067): "order … has no influence" (N1066) | order; pairwise iso of multiplicity strings | Lemma B (§2.3): iterated canonical subcoset, orbits in P1 order | [PROVEN mod Theorem A] |
| 7 | Luks transversal (N1695–1712) | coset representatives | descent (F3) | [PROVEN] |
| 8 | minimal block system 𝔅 ≻ 𝔅₁ (N2683), N, 𝒞, ψ (N2664), G′ | block system, giant representation | P1, descent over ≤ d cosets | [PROVEN] |
| 9 | k ≤ 10t: Luks to ker φ (N2696–2700) | — | descent over ≤ k! cosets | [PROVEN] |
| 10 | LC: "pick (𝔜, T) ∈ 𝒯 arbitrary" (N2207) | **reference test object** | T₀ := {1, …, t} (P1); one object only | Lemma LC |
| 11 | LC: λ_i with T^{λ_i^φ} = T_i (N2211) | transporters | disappear: Lemma T^set(a) | [PROVEN] |
| 12 | LC: equivalence classes of 𝒰, "pick 𝔜′₁ ∈ 𝒮′", realignment 𝔜′′_i = 𝔜′_i^{λ_i⁻¹} (N2232–2242) | **pairwise synchronization** | removed: single-object chain (Lemma E2) | Lemma LC |
| 13 | Simplify: ∼ classes, "assume 1, 2 ∈ A … fix Γ′′ = Γ′′₁" (N2053–2061) | **representative group** | canonical subcoset of the multiplicity string x(𝔛′) on 𝔓′ (Theorem A) | Lemma SIMP |
| 14 | Simplify → `Renormalize` (N2078–2100; Thm N1202) | structure-graph choices | P1 on the canonical prefix's right group: Lemma E3 | Lemma SIMP |
| 15 | LC recursion: kernel N of ψ, ≤ t! cosets (N2440–2447) | coset representatives | descent (F3) | [PROVEN] |
| 16 | aggregation: fullness group, support S, cases (N2546–2582) | — | equivariant (fullness certificates of LC are equivariant) | Lemma AGG |
| 17 | F_i "arbitrary" (N2570), "WLOG R_{i,1} diagonal" (N2575–2577), individualized vertex | individualizations | equivariant branch family, ≤ k⁶ (F4) | [PROVEN] |
| 18 | category on D′₁ ⊔ D′₂ (N2589–2596) | **joint naming of classes** | Lemma T^set colours | Lemma AGG |
| 19 | find-structure 𝔄₁ := 𝔄_{1,1} + Babai's test (N2619–2623); find-symmetry γ, τ (N2648) | **pairing** (routine) | Lemma S with BC per branch, then F4; Lemma K | [PROVEN mod BC] |
| 20 | potential argument (N2710–2725): "Λ′_(𝒞′) ≤ ker(φ′)" (N2716) | top partition of the next round | GAP-1 fix: 𝒞′ is the top partition of the child | write-up §7.3 |
| 21 | LC: order of the giant test and the recursive call (N2221–2225 vs. N2438–2452) | — | test ψ(Λ′) right after balancing (§2.8) | [PROVEN] |

No other place in Neu20 involves two inputs. In §4 every lemma is stated "for i = 1, 2" or for pairs
(𝔛, 𝔜), but apart from rows 5, 6, 10–13, 18, 19 this is only presentation: the objects are computed from
one input.

### 2.3 Lemmas W and B (combining windows, balancing)

**Lemma W (canonical CombineWindows).** **[PROVEN mod Theorem A]**
* *Setting.* A ≤ Sym(Ω) is in Γ̂_d. 𝔓 is A-invariant, W₁, W₂ are disjoint and A-invariant, and
  A[W_j] ≤ Aut(𝔛[W_j]) for j = 1, 2.
* *Construction.*
  * V := 𝔛[W₁] ⊔ 𝔛[W₂]. A acts on V through θ, and θ(A) ∈ Γ̂_d (GNS Lemma 2.4).
  * G(𝔛) is the linking graph of N1648–1651.
  * Apply Lemma S with S(𝔛) := G(𝔛), using Corollary D under θ(A).
* *Claim.* E(𝔛) = σ·R is the canonical placement coset of 𝔛[W₁ ∪ W₂] under A, with
  R = θ⁻¹(Aut(G_can)).

*Proof.*
* For σ ∈ E(𝔛), the strings 𝔛^σ[W_j] = 𝔛[W_j] are unchanged, since σ ∈ A.
* The "other direction" of Neu20's proof (N1669–1676) shows that every element of A preserving
  𝔛[W₁], 𝔛[W₂] and the linking graph preserves 𝔛[W₁ ∪ W₂]. So R ≤ Aut(𝔛^σ[W₁ ∪ W₂]) and
  F := 𝔛^σ[W₁ ∪ W₂] is the canonical form.
* Its forward direction gives the converse, so E is exactly the placement coset.
* Cost: one Theorem A call on |V| ≤ 2m points. ∎

**Lemma B (canonical BalanceOrbits).** **[PROVEN mod Theorem A]**
* Repeat while some orbit O of the current right group A has 𝔛[O] unbalanced:
  * take the first such orbit in P1 order (size, least point);
  * apply Lemma S to the multiplicity string μ : 𝔓[O] → ℕ, P ↦ m_{𝔛[O]}(P), canonized under A[𝔓[O]] by
    Theorem A;
  * continue with the transported object and the new right group.
* Each round passes to a proper subgroup, so there are at most n log n rounds (N1063).
* *Output:* a canonizer of the balancing data (the sequence of multiplicity strings), whose right group has
  only balanced orbits. This is Neu20's Lemma N1045 made canonical. ∎

### 2.4 Lemma SIMP (canonical simplification and renormalization)

**Lemma SIMP.** **[PROVEN mod Neu20 Thm `simplify-on-window` and Thm `renormalize` (constructions and
properties as proved there), Theorem A]**

*Setting (inside the loop of §2.5).*
* The prefix q determines: a group A ≤ Sym(Ω) (the current right group), an almost d-ary A-invariant
  sequence with 𝔓 in it, an A-invariant window W, and the windowed part F = 𝔛[W] of every object in
  𝒵_q, with A[W] ≤ Aut(F).
* If F is simple, nothing is done. Otherwise:

*Steps.*
1. **Copy blocks** (N1974–1985).
   * Ω′ = ⋃_P P × {x[W ∩ P] : (P, x) ∈ F}, with partition 𝔓′, faithful action ψ′ : A → Sym(Ω′), and
     𝔛 ↦ 𝔛′.
   * All of these are functions of (A, F), i.e. of the prefix.
   * 𝔛 ↦ 𝔛′ is injective and equivariant (Claim `preserve-isomorphisms`, N1987–2002). Apply Lemma E3.
   * W′ := W × (·) (N2003). Then W′ is invariant, ψ′(A)[W′] ≤ Aut(𝔛′[W′]), and 𝔛′[W′] is simple
     (Claims N2006–2029).
2. **Lift the sequence** 𝔅 → 𝔅′ (N2031–2040). It is a function of (𝔅, F). Only the level of 𝔓′ can violate
   almost d-arity (N2041–2046).
3. **Balance.**
   * The string x(𝔛′) : 𝔓′ → ℕ², P′ ↦ (m_{𝔛′}(P′), m_{𝔛′[Ω′∖W′]}(P′ ∖ W′)) (N2048).
   * Apply Lemma S, canonizing it under ψ′(A)[𝔓′] by Theorem A. Let A′′ be the right group.
   * Claim `respect-block-sizes` (N2069–2074) holds for A′′. That claim is all the virtual-size estimate
     (F) needs.
4. **Renormalize.**
   * Thm `renormalize` applied to (A′′, 𝔓′, 𝔅′) is a construction from these three data only (proof
     N1455–1554: the strings enter only through the definition of 𝔛*, N1521–1525).
   * So it is a P1 function of the new prefix.
   * 𝔛′ ↦ 𝔛′* is injective (each P* maps bijectively onto f′(P*), and f′ is onto) and equivariant (VIII).
     Apply Lemma E3.

*Output.* The new prefix (Ω*, 𝔓*, 𝔅*, W* = f⁻¹(W′), Λ = φ*(A′′), τ : Λ → H₀). It has properties (A)–(G) of
Thm `simplify-on-window` (N1955–1961) **for the single object**:
* almost d-ary;
* the window is invariant, respected and simple;
* isomorphisms transfer;
* the virtual size does not increase, overall or outside the window.

Neuen's version runs steps 3–4 once per equivalence class of pairs, with the representative Γ′′₁. Here
step 3 is a canonizer and step 4 is computed from its canonical output. ∎

### 2.5 Lemma LC (canonical local certificates)

**Lemma LC.**
* *Setting* (the hypotheses of Neu20 Thm N2175):
  * Γ ∈ Γ̂_d on Ω, with an almost d-ary sequence 𝔅₀ ≻ … ≻ 𝔅_ℓ and 𝔓 = 𝔅_i;
  * a giant representation φ : Γ → S_k, and max{8, 2 + log₂ d} < t ≤ k − 2;
  * T₀, H₀ = Γ_{T₀} and ψ as in Lemma T^set;
  * 𝒵 the set of 𝔓-strings sets of d-virtual size ≤ s.
* *Claim.* Algorithm CanLC below computes an H₀-ECM C on 𝒵, with right group R, and an H₀-invariant flag,
  such that:
  * (L1) C(Z^g) = g⁻¹C(Z) for g ∈ H₀;
  * (L2) flag = nonfull ⇒ ψ(R(Z)) ≱ Alt(T₀);
  * (L3) flag = full ⇒ CanLC also outputs Δ(Z) ≤ Aut_{H₀}(Z) with ψ(Δ(Z)) ≥ Alt(T₀) and
    Δ(Z^g) = g⁻¹Δ(Z)g.
* *Cost.* poly(s) work, polynomially many Theorem A calls on domains of size ≤ poly(s), and recursive calls
  of the main canonizer on instances of virtual size ≤ s/2 whose total is ≤ t!·s.
* *Status.* (L1)–(L3) **[PROVEN mod Neu20 constructions (Lemma SIMP), GNS Thm V.3 (= N1098), Babai
  Thm 6(b) (= N1106), Lemma `extending-window-automorphisms` (N1732, proof read), Theorem A]**. Cost:
  same, plus Neu20's accounting (N2418–2452) with the reordering of §2.8.

**State at round i** (for an object Z, with π ∈ C_i(Z)). C_i is an H₀-ECM with right group R_i. Its prefix
p̄_i(Z) consists of:
* a domain Ω_i, a partition 𝔓_i and a sequence 𝔅^i;
* a window W_i;
* a group Λ_i ≤ Sym(Ω_i) with an injective τ_i : Λ_i → H₀ such that τ_i(Λ_i) = R_i;
* the object map Z′ ↦ Z′_* on 𝒵_{p̄_i};
* the window part F_i := (Z^π)_*[W_i], which is the same for all π ∈ C_i(Z).

Invariants:
* (I1) 𝔅^i is an almost d-ary sequence of Λ_i-invariant partitions containing 𝔓_i.
* (I2) W_i is Λ_i-invariant, Λ_i[W_i] ≤ Aut(F_i), and F_i is simple.
* (I3) For λ ∈ Λ_i: λ ∈ Aut((Z^π)_*) ⟺ τ_i(λ) ∈ Aut(Z^π).
* (I4) The virtual size of (Z^π)_* is ≤ s, and s′_i := the virtual size of (Z^π)_*[Ω_i ∖ W_i] strictly
  decreases with i.

Start: C₀ = H₀, Ω₀ = Ω, W₀ = ∅, Λ₀ = H₀, τ₀ = id.

**Round i** (each step is Lemma E2 applied with the named ECM):
* (a) If ψ(R_i) ≱ Alt(T₀): stop with *nonfull*.
* (b) W′ := Aff(Λ_i, ψτ_i) ∖ W_i. This is a function of the prefix, hence identical across the H₀-orbit.
  If W′ = ∅: stop with *full*, and
  Δ(Z) := π·τ_i((Λ_i)_(Ω_i∖W_i))·π⁻¹.
* (c) **Balance:** Lemma B on (Z^π)_* under Λ_i. If ψτ_i of the new right group is not ≥ Alt(T₀): stop with
  *nonfull*.
* (d) **Window:**
  * canonize (Z^π)_*[W′] under the current group Λ′;
  * Λ′-orbits of W′ are taken in P1 order (chain rule F2);
  * within an orbit O: descent (F3) to N′ := ker(ψτ_i|_{Λ′}) over ≤ t! cosets, then the chain rule over
    N′-orbits in P1 order. Each N′-orbit is a recursive call of the main canonizer (Theorem H at smaller
    virtual size), and Lemma W joins the pieces;
  * finally join W_i and W′ by Lemma W.
* (e) **Simplify and renormalize:** Lemma SIMP at the new prefix (window W_i ∪ W′). Lemma E3 yields
  Λ_{i+1}, τ_{i+1}, Ω_{i+1}, W_{i+1}.

**Proof of the claims.**
* *(L1).* Induction on rounds. Each step composes (Lemma E2) an ECM that comes from a canonizer (Theorem A,
  recursive calls, Lemmas B and W), a descent (F3), or a change of action computed from the prefix (Lemma
  E3, Lemma SIMP). The stopping tests depend only on R_i and the prefix, which are H₀-invariant.
* *Invariants.*
  * (I1), (I2): Lemma SIMP output, properties (A), (B), (E).
  * (I3): Claim `preserve-isomorphisms` (N1987), Thm `renormalize` (VIII), and the fact that balancing and
    windowing only pass to subgroups containing the relevant automorphisms (Lemma E1).
  * (I4): Neu20's argument (N2400–2412). W′ ≠ ∅ strictly lowers s′ (Obs. N1582), and Simplify does not
    raise it (property (G)).
  * Hence at most s rounds.
* *(L2).* Holds by the tests at (a) and (c).
* *(L3).*
  * At (b), Aff(Λ_i, ψτ_i) ⊆ W_i. Λ_i is d-normalized (I1), and ψτ_i(Λ_i) is a giant (test (a)). So GNS
    Thm V.3 gives ψτ_i((Λ_i)_(Ω_i∖W_i)) ≥ Alt(T₀).
  * Lemma `extending-window-automorphisms` with (I2) gives (Λ_i)_(Ω_i∖W_i) ≤ Aut((Z^π)_*). (I3) transfers
    this to τ_i(…) ≤ Aut_{H₀}(Z^π). Conjugating by π gives Δ(Z) ≤ Aut_{H₀}(Z), with a conjugate giant
    image.
  * Independence of π: (Λ_i)_(Ω_i∖W_i) ⊴ Λ_i, so its τ_i-image is normalized by R_i.
  * Equivariance follows from (L1).
* *Cost.*
  * Step (d) is Neu20's recursion for one pair (N2436–2452), with one change. Babai Thm 6(b) is applied to
    Λ′ itself. It is a giant by test (c), and the orbits in W′ are affected for Λ′ because Aff is
    antimonotone (N2172).
  * So each N′-orbit A_p in a Λ′-orbit O has |A_p| ≤ |O|/t. Since (Z^π)_*[O] is balanced (Lemma B), the
    virtual size of (Z^π)_*[A_p] is ≤ (|A_p|/|O|)·s((Z^π)_*[O]) ≤ s/2 (Obs. N1589).
  * Σ over rounds of s(window) ≤ s (N2425–2434). With the t! cosets: total ≤ t!·s, each piece ≤ s/2.
  * Theorem A calls (Lemmas B, W, SIMP step 3) are polynomially many, on domains of size ≤ poly(s). ∎

**Comparison with Neu20.** Neuen computes, for every pair of test objects, the coset of isomorphisms. To make
the renormalizations comparable he runs all 4k^{2t} pairs in one synchronized loop (N270–275, N1930–1933).
CanLC runs binom(k, t) independent single-object loops, one per t-set: transport the t-set to T₀, then run
the loop on X^σ. **Consistency between test sets is automatic**: every auxiliary construction is a function
of the canonical prefix, and Lemma T^set(a) makes the result independent of the transporter. The recursive
cost drops from 4k^{2t}·t!·s (N2196) to k^t·t!·s.

*Why the setwise stabilizer, not the pointwise one (as in the memo).* The memo canonizes under
J₀ = ker ψ and takes the windows from the GNS groups G_i(T, x) = Aut_{H_T}(x^{[W_i]}). Those groups are
intrinsic to (T, x), so any algorithm computes the same ones. In Neu20 the corresponding groups live on
renormalized domains, and they depend on the structure-graph choices made at earlier rounds. They are
intrinsic only once those choices are made canonically, which requires canonizing at the level H₀ at which
the windows are defined. Computing H₀-level automorphism groups from a J₀-level chain would need t!
re-runs of the chain per round, compounding over rounds.

### 2.6 Lemma AGG (canonical aggregation)

**Lemma AGG.** **[PROVEN mod Lemma LC and the facts used in Neu20's proof: CFSG degree-of-transitivity
(N2527), Babai Cor. 2.4.13 (N2538), Dixon–Mortimer 5.2A,B (N2473)]**

*Setting.* As Neu20 Lemma N2499, for one 𝔛 (and Γ′, φ, t < k/10 as there).

*Output.* One of:
* (i) a family {𝔄_j(𝔛)}_{j ≤ k⁶} of t-ary structures on subsets V_j ⊆ [k] with |V_j| ≥ 3k/4 and relative
  symmetry defect ≥ 1/4, equivariant as a family: {𝔄_j(𝔛^h)} = {𝔄_j(𝔛)}^{φ(h)};
* (ii) a pair (M(𝔛), Δ(𝔛)) with |M| ≥ 3k/4, Δ ≤ Aut_{Γ′_M}(𝔛), Δ^φ[M] ≥ Alt(M), both equivariant.

*Proof.*
* Run CanLC on X^σ for each t-set T (Lemma LC with Lemma T^set). This gives:
  * the canonical fullness certificates Δ(T, 𝔛) := σΔ(X^σ)σ⁻¹ for routine-full T. They are equivariant,
    since Δ(X^{σg}) = g⁻¹Δ(X^σ)g;
  * colours c(𝔛, T⃗) for all orderings of routine-nonfull T.
* The fullness group Λ_𝔛 := ⟨Δ(T, 𝔛) : T routine-full⟩ and its support S are equivariant.
* The cases |S| ∈ [k/4, 3k/4] and |S| > 3k/4 (N2554–2582) produce GNS's structures from Λ_𝔛 alone. Each
  individualization (F, R_{i,j}, a vertex) is a member of an equivariant branch family of ≤ k⁶ (F4; write-up
  §5.2).
* Case |S| < k/4. D := [k] ∖ S, and
  𝔄(𝔛) := ([k]; unary D; T⃗ ↦ rank of c(𝔛, T⃗) for T⃗ ∈ D^⟨t⟩).
  * Every T ⊆ D is routine-nonfull: a routine-full T has ψ_T(Δ(T, 𝔛)) ≥ Alt(T), so T ⊆ S.
  * 𝔄 is strongly canonical by Lemma T^set(b). Ranking is canonical because the set of colour values is an
    invariant of 𝔛.
  * *Symmetry defect.* Suppose Alt(Δ′) ≤ Aut(𝔄) with |Δ′| ≥ t + 2. Alt(Δ′) is transitive on Δ′ and
    preserves D, so Δ′ ⊆ D or Δ′ ∩ D = ∅. If Δ′ ⊆ D, pick a t-set T ⊆ Δ′. Every π ∈ Sym(T) is induced by
    Alt(Δ′), by fixing parity on Δ′ ∖ T. So all orderings of T have equal colour, and Lemma T^set(c) gives
    ψ(R) = Sym(T₀). That contradicts (L2) for the routine-nonfull T. Hence Δ′ ⊆ S or |Δ′| ≤ t + 1, and the
    relative defect is ≥ 1 − max(1/4, 1/10 + 1/k) ≥ 1/4. ∎

Neu20's own bound "symmetry defect ≥ |D_i| − t + 1" (N2596) is for its jointly named structure. Ours uses a
different, coarser structure. It has the same defect bound, and that bound is all Option 1 needs (index
≥ (4/3)^k by Neu20 Cor. N2483).

### 2.7 Theorem H

**Theorem H (canonical Neu20).**
* *Input:* Γ ≤ Sym(Ω) with Γ ∈ Γ̂_d (by generators); σ ∈ Sym(Ω); a Γ-invariant partition 𝔓; a set 𝔛 of m
  𝔓-strings.
* *Output:* F_{σΓ}(𝔛) and Λ_{σΓ}(𝔛) = {g ∈ σΓ : 𝔛^g = F}.
* *Time:* (n+m)^{O((log d)^c)}.
* *In particular:* canonical labellings of hypergraphs (V, ℰ) with m edges relative to a labelling coset
  Δρ with Δ ∈ Γ̂_d, in (n+m)^{O((log d)^c)}.
* *Status:* correctness **[PROVEN mod: Neu20 Thms `normalize`, `renormalize`, `simplify-on-window`
  (constructions and listed properties), Lemma `extending-window-automorphisms`, the virtual-size facts
  N1580–1614; GNS Thm V.3; Babai Thm 6(b); the aggregation's CFSG facts; Lemma 7.1 of GNS / Babai 3.2.1
  (N2664); Theorem A; BC Thm 2.2; canonical generating sets]**. Time **[SKETCH]**.

*Proof (correctness).* The algorithm is Neu20's Alg. N2736 with the canonical replacements of §2.2:
* cosets → groups by the coset rule;
* normalization by Lemma R (row 3);
* intransitive: chain rule plus Lemma W;
* semi-regular top: Lemma B, descent and the chain rule;
* |𝔅₁| ≤ d: P1 giant representation, descent to G′, then either descent to ker φ (k ≤ 10t) or Lemma AGG
  followed by Option 1 (Lemma S with BC per branch, F4) or Option 2 (Lemma K); then the next round with 𝒞′
  as top partition.

Every step maps canonizers for sub-instances to a canonizer for the instance. Induction on (virtual size,
then the k-potential) gives (C1)/(C2). ∎

*Time (sketch).*
* The recursion tree has the same node types as Neu20's.
* The changes:
  * LC's recursive total drops from 4k^{2t}t!s to k^t t!s;
  * GNS isomorphism calls become Theorem A calls of the same size;
  * Babai's test on ≤ k⁶ structures with k ≤ d points becomes BC canonization, exp(polylog d) each.
* Lemma `partition-small-size-recursion` (N2671–2728), with the GAP-1 fix, gives Σs_i ≤ 2^{O(log³ d)}s at a
  node with s_i ≤ s/2. Lemma `recursion-bound` (N608) then gives s^{O(log³ d)}·(n+m)^{polylog d}.
* With s ≤ (n+m)^{O(log d)} (N1576), this is (n+m)^{O((log d)^c)}.
* The LC loop's s rounds and its descents are inside the same budget as in Neu20. **[SKETCH]**

### 2.8 Two remarks on Neu20 as written

1. **GAP-1 is inherited.** N2716 asserts "|Λ′[𝒞′]| ≥ (k′)!/2 because (Λ′)^{φ′} ≥ A_{k′} and Λ′_(𝒞′) ≤ ker(φ′)".
   This is the step of GNS L2126 that the red-team (`redteam-gns-lemma72.md`) found unjustified. The
   choice at N2683 ("Let 𝔅 ≻ 𝔅₁ be a minimal block system") is equally unconstrained. The same fix
   applies. 𝒞′ ⪰ 𝔅 ⪰ 𝔅₁, and inserting 𝒞′ and 𝔅 at the top keeps the sequence almost d-ary for Γ′, since
   |𝒞′| ≤ |𝔅| ≤ d. **[PROVEN, as in write-up §7.3]**
2. **Order of the giant test (minor, cost accounting only).**
   * In Alg. N2221–2225 the recursive call on W′ (line 2222) comes before the test "(Λ′)^ψ ≱ Alt(T)"
     (line 2224).
   * The proof (N2438–2452) bounds kernel orbits using N ⊴ Λ, the **pre-balancing** group, which is
     giant. But it bounds virtual size using balance, which holds for orbits of the **post-balancing**
     group Λ′.
   * If ψ(Λ′) is not a giant, kernel orbits of Λ′ need not halve. The call is then wasted, and the size
     bound s_i ≤ s/2 is not justified.
   * Fix: test ψ(Λ′) immediately after BalanceOrbits (our step (c)). If it is not a giant, output
     non-fullness at once; otherwise apply Babai's lemma to Λ′. Correctness of Neu20 is unaffected.
     **[PROVEN]**

---

## 3. Treewidth

### 3.1 What is known

| result | statement | canonical? | source |
|---|---|---|---|
| Thesis Thm 6.13 (= GNSW18/20) | canonical labelling, treewidth k, 2^{O(k² log k)}·n^{O(1)} | **yes** | Thesis p. 152–154 |
| GNSW20 | isomorphism, 2^{k·polylog k}·n^{O(1)} | no: "involves subroutines [GNS18] that do not extend to canonization so far" | Thesis p. 9–10 |
| Wie20 Thm `isoGraph` (= Thesis Cor. 6.30) | isomorphism, n^{polylog k} | no: "Only the algorithm given in the last section depends on the bounded-degree isomorphism algorithm of Grohe et al. for which no adequate canonization version is known" | Wie20 `intro.tex` L176–178; Thesis p. 11, p. 180 |
| Wie20 outlook | GNS canonical ⇒ treewidth algorithm "should then be amenable to canonization" | conditional prediction | `openQuestions.tex` L19–27 |
| Thesis Cor. 6.30 via Thm 6.29 | treewidth n^{polylog k} as a corollary of the minor result (hw ≤ tw + 1) | no (uses Neu20a) | Thesis p. 179–180; Remark 6.31 points back to Wie20's simpler route |
| BC | canonical forms, n^{polylog n} | yes | — |

### 3.2 What Wie20's algorithm imports

Wie20 `isoGraph` (W264–359): approximate k; k-improve; clique-separator decomposition; then `isoTree`,
bottom-up.

| component | Wie20 lines | non-canonical element | canonical replacement | label |
|---|---|---|---|---|
| treewidth approximation (Amir) | W271–272 | the output k need not be an isomorphism invariant | invariant doubling search over k ∈ {1, 2, 4, …}, with invariant success checks (§3.4) | [SKETCH] |
| k-improvement G^k | W273, Lemma W53 | — | invariant | [PROVEN mod LPPS] |
| clique-separator decomposition | W68–82, W274 | (equal/distinct adhesion normal form, W64–66) | output isomorphism-invariant (Leimer; Elberfeld–Schweitzer Lemma 3.1) | [PROVEN mod cited] |
| root r_i | W277 | arbitrary root | centre of T, subdividing if it is an edge (Thesis p. 142) | [PROVEN] |
| children: Iso for all pairs | W291–292 | pairwise | canonical labellings of child instances (recursion) | [PROVEN] |
| "ρ₁ arbitrary labeling", "representative t*" | W293–297 | **choice** | colour = canonical form of the child; label = its canonical labelling coset restricted to S_t (Thesis §6.1.3, p. 144–151) | [PROVEN mod Thesis Thm 6.11 construction] |
| equal adhesion sets: `canObj` on the bag | W299–326 | none: already canonical, bag ≤ k+1 | Wie20 Cor. `canObj` (`multiCoset.tex` L1387), time n^{polylog k} | [PROVEN mod Wie20] |
| distinct adhesion: `isoBasicClique` | W176–250, W332 | GNS calls, arbitrary φ | §3.4(b) | [SKETCH] |
| distinct adhesion: `cosetHyper` | W257–262, W336 | Neuen-type iso | **Lemma CH (§3.3): Corollary D only** | [PROVEN mod Corollary D] |
| distinct adhesion: `boundedDegree` on G | W91–95, W340 | GNS iso | Corollary D | [PROVEN mod Theorem A] |
| extension to subtrees | W345–358 | arbitrary extensions of generators | canonical extension (Thesis p. 145–146, Obs. 1–3, Remark 6.12; last case p. 151–152) | [PROVEN mod Thesis] |
| `isoBasic` | W101–167 | "some S₁ ∈ 𝒮₁, S₂ ∈ 𝒮₂", "some bijection φ", GNS calls | §3.4(a) | [SKETCH] |

### 3.3 Lemma CH (the correction to write-up §9.2)

Wie20's Lemma `cosetHyper` (W257–262) assumes "Δφ ≤ iso(H₁; H₂) [is] a coset that maps the hyperedges in H₁
to hyperedges in H₂". It is applied at W336, right after Δφ := iso(Y₁, H₁; Y₂, H₂) was computed by
`isoBasicClique` (W332), so the hypothesis holds. The hypergraph part is therefore already respected; only
the coset labels remain.

**Lemma CH (canonical coset-labelled hyperedges under a hyperedge-respecting coset).**
**[PROVEN mod Corollary D]**
* *Setting.*
  * Λ = ρΔ is a labelling coset of V with Δ ∈ Γ̂_d.
  * Δ preserves a family 𝒮 ⊆ 2^V and a colouring χ : 𝒮 → ℕ.
  * Each S ∈ 𝒮 carries a labelling coset τ_SΘ_S of S, with Θ_S ≤ Sym(|S|) and Θ_S = Θ_{S′} whenever
    χ(S) = χ(S′). Let d′ := max_S cw(Θ_S) ≤ max_S |S|.
* *Claim.* A canonical labelling coset of X = (V, 𝒮, χ, {τ_SΘ_S}) relative to Λ is computable in
  (|V| + Σ_S|S|)^{O((log max(d, d′))^c)}.

*Proof.* This is GNSW18 v1 Lemma 23 (`bag_subproblem.tex` G57–191), second case ("we can assume that Δ
preserves 𝒮 and χ", G82–114).
* U := ⨆_S {S} × S.
* Λ̂ is the labelling coset of V ∪ U that orders V by δ ∈ Λ, orders the blocks U_S by S^δ, and orders
  inside U_S by some ρ_S ∈ τ_SΘ_S.
* Y is the incidence graph v — (S, v).
* Return CL(Y; Λ̂)|_V.
* GNSW18 proves (CL1)–(CL3) for this output (G116–180). The composition width of Λ̂'s group is
  ≤ max(cw Δ, d′) (G109): it is an extension of ∏_S Θ_S by Δ.
* GNSW18 canonize Y with a Luks-type algorithm; we use Corollary D instead. ∎

In Wie20's application:
* the hyperedges are adhesion sets, which are cliques in the k-improved graph, so |S| ≤ k + 1 and
  d′ ≤ k + 1;
* d ≤ k after individualizing one vertex (W338).

So Lemma CH gives (|V| + |H|)^{polylog k}, the bound of `cosetHyper`. **Canonical Neu20 is not needed for
treewidth.** (Write-up §9.2 item 2 reads Lemma `cosetHyper` as a general coset-labelled hypergraph
statement. For a coset that does not respect the hyperedges, as in GNW (M644–656) and Neu22t, Theorem H is
indeed needed: Corollary H1.)

### 3.4 Canonical rewrites of Wie20's isomorphism-only steps

All within the Schweitzer–Wiebking framework: refine an isomorphism-invariant labelling coset step by step.
CL(X₂; CL(X₁; Λ)) is a canonical labelling of (X₁, X₂) relative to Λ (chain rule for labelled objects).
**[SKETCH for each; every step uses only Corollary D, P1 constructions, or Wiebking's quasipolynomial
canonizers on ≤ k+1 points]**

**(a) `isoBasic` (W101–167), G clique-separator-free with sep, tw ≤ k.**
* *Branching.* Branch over S ∈ 𝒮 := {N(v) : deg v = mindeg}, an invariant family (W111–116), by Lemma F4.
  Within a branch start from the labelling coset Lab(S), which is invariant.
* *Step "same separator sizes" (W137–139).* Canonize the complete graph on S, coloured by |S_{v,w}|,
  relative to the current coset: Corollary D.
* *Step "wreath product" (W142–148).* Ŝ := S ⊔ ⨆ Ŝ_{v,w}. The coset Λ̂ orders S by λ, the blocks by
  (v^λ, w^λ), and orders inside each block arbitrarily. This is an invariant construction; cw ≤ max(cw, sep).
* *Step "identify" (W150–155).* Canonize the identification graph X relative to Λ̂ (Corollary D). Pass to
  the induced labelling coset of the quotient S′, ordering classes by least label (Thesis's "↓").
* *Base case S = V (W159–160).* Canonize G relative to the coset (Corollary D).
* At most n rounds (W164). Composition width stays ≤ max(tw, sep) (W148).

**(b) `isoBasicClique` (W176–250).**
* Keep the branch S of (a), so all cosets have cw ≤ k + 1. This replaces the "point v₁ with
  cw Δ_(v₁) ≤ k" device (W227–229).
* The clique cover α (W185–207) is invariant.
* The hypergraphs H_v on α(v), with |α(v)| ≤ k+1, are canonized by Wie20 `canHyper` in
  (k+1+|H_v|)^{polylog(k+1)} (W218).
* Colour v by the canonical form of H_v (W221–224); Corollary D.
* Wreath product over U := V ⊔ ⨆ α(v) × {v} (W232–241): the invariant coset built from the canonical cosets
  of the H_v.
* Identification graph (W243–248); Corollary D.
* The output's group respects H.

**(c) `isoTree` (W283–358).**
* *Root.* The centre of T.
* *Children.* Canonical labellings by recursion. A child's colour is its canonical form (with the adhesion
  set marked); its label is its canonical coset restricted to S_t and compressed, Θ_tτ_t. Equal colours
  give equal Θ_t, as Lemma CH needs.
* *Equal adhesion sets.* The bag has size ≤ k+1 (W78). Wie20 Cor. `canObj` on (G[D], {Θ_tτ_t}, colours)
  runs in n^{polylog k}. (Thesis Thm 6.11's |D|^{O(cw)} route would cost 2^{O(k log k)}. It must **not**
  be used here when k ≫ log n.)
* *Distinct adhesion sets.*
  * Branch S over the min-degree neighbourhoods of Y = G^k[D].
  * Λ₁ := (b) on (Y, H).
  * Λ₂ := Lemma CH relative to Λ₁ (colours and labels from the children).
  * Λ₃ := Corollary D on G[D] relative to Λ₂.
  * Take the minimum over branches (F4).
  * Extend canonically to the subtrees (Thesis p. 151–152, the "partition into singletons" case of
    Thm 6.11's proof).
* *Parameter k.* Run the algorithm for k = 1, 2, 4, …. Accept the first k for which three invariant checks
  pass:
  * every equal-adhesion bag of the decomposition of G^k has ≤ k+1 vertices;
  * every basic bag has min-degree ≤ k;
  * every adhesion set has ≤ k+1 vertices.
  * Correctness (canonicity) holds for every k. The checks only certify the time bound n^{polylog k}, and
    they pass for all k ≥ tw(G) (Lemma W53(3), Thm W68(3)). So the accepted k is ≤ 2·tw(G).

### 3.5 Theorem TW

**Theorem TW.** Canonical forms (canonical labellings) of n-vertex graphs of treewidth k are computable in
time n^{O((log k)^c)}.
**[PROVEN mod Theorem A (via Corollary D); Wie20 `canHyper`, `canObj` (canonical, quasipolynomial in the
ground set); LPPS improvement; Leimer/Elberfeld–Schweitzer invariant decomposition; Thesis canonical
extensions]**. The canonical rewrite of Wie20's three procedures is **[SKETCH]** (§3.4).

*Proof.* §3.2–3.4.
* Each node of the clique-separator tree makes polynomially many Corollary D calls, with composition width
  ≤ k+1 and domains of polynomial size. It also makes Wie20 `canHyper`/`canObj` calls on ≤ k+1 points.
* There are polynomially many nodes and n branches per bag.
* Total: n^{O((log k)^c)}. Components are sorted by canonical form. ∎

*Comparison.* Theorem TW is incomparable with Thesis Thm 6.13 (2^{O(k² log k)}·n^{O(1)}). It is better once
k ≥ (log n)^{1/2+ε}. It is better than BC whenever k = n^{o(1)}.

*Second route.* Thesis Cor. 6.30 derives treewidth from the minor result (hw ≤ tw + 1). Corollary H4 would
give Theorem TW again, but through Theorem H. The Wie20 route needs less.

---

## 4. Other corollaries

**H1 (coset-labelled hypergraphs, GNW Thm M649).** **[PROVEN mod Theorem H, Corollary D]**
* *Statement.* Given a coset-labelled hypergraph (V, ℰ, 𝔭) in GNW's sense (M618–640; labelling cosets of
  the hyperedges, colours) with |E| ≤ d for all E, and a labelling coset Δρ of V with Δ ∈ Γ̂_d: a
  canonical labelling coset is computable in (n+m)^{O((log d)^c)}.
* *Proof.* GNSW18 v1 Lemma 23 in full (G57–191):
  * refine each edge colour c to (c, Θ), which is invariant, since GNW's isomorphisms require equal Θ
    (M628–635);
  * first canonize the coloured hypergraph (V, ℰ, χ) relative to Δρ (Theorem H). Its right group then
    preserves ℰ and χ;
  * then apply Lemma CH with d′ ≤ d.
* GNW's isomorphism version cites Neu20 plus Neu19 Thm 6.6.7 (footnote M644–647).

**H2 (t-CR-bounded graphs and closures; Neu20 Lemma N2860, Thm N2941; GNW Thm M771 = Neu22 Lemma 5.2).**
**[SKETCH, mod Theorem H, Corollary D]**
* Neuen's proof maintains a coset Γ_jθ_j on the colour classes 𝔓_j and refines it. Each refinement is
  either an isomorphism of quotient graphs (GNS) or of the sets {𝔵_v} of strings on 𝔓_{j,r−1} (Neu20).
* Canonical version: maintain an invariant labelling coset of 𝔓_j.
  * *Splitting small classes:* wreath with Sym(P), |P| ≤ t, ordered by the parent label. Then canonize the
    quotient graph G_j: Corollary D.
  * *Refinement rounds:* canonize {𝔵_v} relative to the current coset (Theorem H). Induce a labelling coset
    on {𝔵_v} ≅ 𝔓_{j,r} by the lexicographic order of 𝔵_v^λ. Then canonize G_{j,r}: Corollary D.
* Composition width stays ≤ t; there are polynomially many steps.
* Outputs:
  * for t-CR-bounded (G, S) with a Γ̂_t labelling coset of S: a canonical labelling in n^{polylog t};
  * for closures D = cl_t(X): an invariant Γ̂_t labelling coset of D containing Iso[D]. This is the
    canonical twin of GNW Thm M771, and it suffices as input to the canonical DP below.

**H3 (K_{3,h}-minor-free graphs; Euler genus g; Neu20 §6).** **[SKETCH, mod H2]**
* Canonical forms of 3-connected components combine into canonical forms of the graph by the standard
  canonical decomposition into 2- and 3-connected components (Hopcroft–Tarjan tree; standard in canonical
  planar and bounded-genus algorithms, not re-derived here).
* For a 3-connected coloured component: branch over ordered triples (v₁, v₂, v₃) (n³ branches, F4).
  Corollary N3084 makes the result (h−1)-CR-bounded, and H2 applies.
* With Ringel's bound (N2979), genus g graphs exclude K_{3,4g+3}.
* Result: n^{polylog h}, respectively n^{polylog g}.

**H4 (K_h-minor-free, GNW Thm M1885; K_h-topological-subgraph-free, Neu22t Thm P2221).**
**[CONDITIONAL on Theorem H, H1, H2; canonical DP rewrite SKETCH]**
* *Non-canonical elements of GNW's proof:*
  * "fix one representative j* ∈ Q_j", "an arbitrary bijection λ_{j*}" (M2037–2038);
  * "fix one representative Q*_j", "arbitrary bijection ρ_{Q*_j}" (M2106–2108);
  * "v₁ ∈ X₁ arbitrary" (M2076);
  * the calls to M771 (t-CR closure), M649 (coset-labelled hypergraphs), the multiple-labelling-coset
    theorem (Wie20, canonical already, M691), and Babai's test on < h vertices (M1996).
* *Canonical version:*
  * colours and labels from canonical labellings of the parts, as in Thesis §6.1.3;
  * equal separators: Wiebking's multiple-labelling-coset canonization on |S| < h points (canonical,
    n^{polylog h});
  * distinct separators: H1 relative to the H2 labelling coset of D;
  * branching over v ∈ X (F4); BC on < h vertices.
* The decomposition steps (GNW Thm M846, "initial color", output "isomorphism-invariant", M855;
  Thm M816, small separators) are invariant constructions and are used as black boxes.
* Neu22t (P2215–2490) is identical in structure. Its extra call computes {γ ∈ Γγ : D₁^γ = D₂} with Neu20
  (P2422), a set stabilizer, which Theorem A already handles.
* *Result:* canonical forms for graphs excluding K_h as a minor, or as a topological subgraph, in
  n^{polylog h}. **This would answer Thesis Question 9.7.**

**Hypergraphs under Sym(V).** Theorem H with d = n gives (n+m)^{polylog n}. That is Wiebking's `canHyper`
(Thesis Thm 5.4(1)) again, so nothing new. **[PROVEN mod H]**

**FPT treewidth canonization 2^{k·polylog k}·n^{O(1)}.** **[SPECULATION]**
* GNSW20's FPT isomorphism test uses GNS only for expanded d-ary trees (GNSW18 v1 Thm G79). Those are
  strings on L(T)² under subgroups of Aut(T) ∈ Γ̂_d, so Theorem A covers them.
* Its other non-canonical step is Babai's coset intersection for multiple coloured cosets on O(k²) points
  (Lemma 13, G194–223). Wiebking's canonical `canSet` replaces it at 2^{polylog k}·poly.
* So the thesis's stated obstacle (p. 10) seems removed. The rest of GNSW18's FPT algorithm (labelled
  decompositions; Lemma 14, `recursive_algo_iso.tex` G3) was not traced.

---

## 5. Novelty

| source | what it says about canonization of Neu20 / treewidth / minors | checked |
|---|---|---|
| Thesis (2021) | p. 7: GNS18 and "results building on it [Neu20a]" have no canonization. p. 10: FPT 2^{k polylog k} not canonical. p. 179: Thm 6.29 is "only an isomorphism test … since the bounded-degree techniques [GNS18, Neu20a] are not available for canonization so far". p. 181: "A natural question is whether … our isomorphism test for graphs excluding a minor can be turned into a canonization algorithm." p. 242: Q 9.6, Q 9.7 | full text of the relevant chapters |
| Wie20 (2020) | treewidth "should then be amenable to canonization" once GNS is canonical (outlook L19–27). Intro L176–178 | source |
| Neu20 (2020/22) | isomorphism only. Related work N309–325 attributes the canonization results to Wiebking, which do not exploit restricted groups | source |
| GNW (2020), Neu22t (2020/24) | isomorphism only. GNW uses Wiebking's canonical multiple-labelling-coset algorithm as a black box (M687–709) | source |
| Grohe–Neuen survey (2011.01366); Neuen survey (2026) | no specific statement. 2026: "the same is possible for many of the algorithms discussed in this survey" | grep of full text |
| arXiv API (2026-11-05), `w8-arxiv-queries/` | au:Neuen (37 papers, through 2609.24804); au:Wiebking (7, latest 2020); abs:canonization ∧ {treewidth, hypergraph, composition, degree, quasipolynomial, genus, topological subgraph}; ti:canonization; ti:canonical ∧ labelings. **No** canonization of Neu20, GNW, Neu22t or n^{polylog k} treewidth. Nearest: Levet–Rombach–Sieger, bounded rank-width canonization in parallel (2306.17777); random-graph canonical labelling | queries |
| web search (3 extended queries) | nothing beyond the above | — |

**Status.**
* *Theorem H.* New as far as I can find. The previous best canonization for Γ̂_d hypergraphs is
  Schweitzer–Wiebking's n^{O(d)}m^{O(1)} (Thesis Thm 5.4(3): k^{O(cw Δ)}(|V|+|F|)^{O(1)}).
* *Theorem TW.* New as an explicit result. It is the canonization that Wie20 predicted would follow from
  canonical GNS, and it does follow from Theorem A (plus routine rewriting). Experts will call it expected.
* *H4.* Would settle Thesis Q 9.7. Sketch level only.
* *Credit.*
  * The canonical test set over an ordered group is Wiebking's (Thesis Lemma 5.34).
  * Labelling cosets, canonical extensions and the multiple-labelling-coset canonizer are Schweitzer's and
    Wiebking's.
  * The incidence-graph reduction for coset-labelled hyperedges is GNSW18's own (v1 Lemma 23).
  * New here:
    * the observation that Neu20's synchronization is unnecessary if every renormalization is computed
      from the canonical prefix at the setwise level;
    * the observation that Wie20 needs only canonical GNS.

---

## 6. Gaps, risks, questions

1. **Theorem A's own status** (write-up): PROVEN mod GNS/BC; time SKETCH; GAP-1 fixed. Theorem TW and
   Theorem H inherit all of this. Theorem H additionally needs Theorem A for strings on domains up to
   poly(n+m).
2. **Neu20 lemmas used without re-proof.**
   * Used without re-proof: the normalization constructions; properties (A)–(G) of `simplify-on-window`
     and (I)–(IX) of `renormalize`; the virtual-size accounting.
   * I read their proofs once and checked only the facts used: group-only construction, injectivity,
     equivariance, simplicity, the monotonicity of s.
   * The structure-graph lemma (Neu19 Lemma 6.1.17) is in the unobtained dissertation. It is a group-only
     construction, so P1 applies regardless of its internals.
3. **Running time of Theorem H**: a transfer sketch. Two points in Neu20 as written need the patches of
   §2.8 (GAP-1; giant-test order). Neither affects correctness.
4. **Wie20 rewrite (§3.4)**: sketched step by step against W-lines, not written as full proofs. The
   invariant choice of k is new detail that Wie20 does not need. The Wie20 text is the arXiv v2 (ICALP)
   version. The thesis gives the multiple-labelling-coset and canonical-extension machinery in full.
5. **H2–H4**: sketches. H4 uses GNW's and Neu22t's structure theorems only as invariant constructions;
   their proofs were not checked. The canonical 2/3-connected decomposition in H3 is standard but not
   written out.
6. **Versions**: TALG texts of Neu20 and GNSW18 not compared. GNSW18's "Lemma 9" (as cited by Wie20) was
   matched to arXiv v1 Lemmas 11 (iso) and 23 (canonical) by content, not by number.

**Questions for experts.**
1. Neuen: is the "all pairs in parallel" device (N270–275, N1930) needed for any reason other than making
   renormalization consistent? Our single-object loop at the setwise stabilizer of T₀ claims to make it
   unnecessary.
2. Wiebking: is it right that Wie20's treewidth algorithm needs only GNS, with `cosetHyper` applied only to
   hyperedge-respecting cosets, so that its canonical version follows from canonical GNS plus your
   `canHyper`/`canObj` on ≤ k+1 points?
3. Is the ordering point of §2.8(2) handled in the TALG version of Neu20?

---

## 7. Ledger

| item | status |
|---|---|
| Lemmas E1–E3 (equivariant coset maps, composition, change of action at a prefix) | **[PROVEN]** |
| Lemma T^set (setwise test set → ordered colours) | **[PROVEN]** |
| Lemmas W, B (canonical CombineWindows, BalanceOrbits) | **[PROVEN mod Theorem A]** |
| Lemma SIMP (canonical Simplify + Renormalize) | **[PROVEN mod Neu20 constructions, Theorem A]** |
| Lemma LC (canonical local certificates, single object, setwise) | **[PROVEN mod Neu20 constructions, GNS Thm V.3, Babai Thm 6(b), Theorem A]** |
| Lemma AGG (canonical aggregation, symmetry defect ≥ 1/4) | **[PROVEN mod LC and Neu20's CFSG facts]** |
| Theorem H (canonical Neu20) | correctness **[PROVEN mod as listed]**; time **[SKETCH]** |
| §2.8 remarks on Neu20 (GAP-1 inherited; giant-test order) | **[PROVEN]** (fixes given) |
| Lemma CH (coset-labelled hyperedges under a hyperedge-respecting coset) | **[PROVEN mod Corollary D]** |
| Correction to write-up §9.2: treewidth does not need canonical Neu20 | **[PROVEN]** (W258–261, W332–336) |
| Theorem TW (treewidth k, n^{polylog k}) | **[PROVEN mod Theorem A and cited canonical tools]**; Wie20 rewrite **[SKETCH]** |
| H1 coset-labelled hypergraphs | **[PROVEN mod Theorem H, Corollary D]** |
| H2 t-CR-bounded / closures | **[SKETCH]** |
| H3 K_{3,h}-minor-free, genus | **[SKETCH]** |
| H4 K_h-minor-free, K_h-topological-subgraph-free (Thesis Q 9.7) | **[CONDITIONAL on Theorem H, H1, H2]**, DP **[SKETCH]** |
| FPT 2^{k polylog k} treewidth canonization | **[SPECULATION]** |
| novelty | none found (§5) |
| no Lean, no solver, CPU negligible | — |
