# Red-team of the canonization write-up (§§2.5, 7, 8, 10, 13)

Branch `w8-redteam-writeup`, 2026-11-05. This is an independent referee pass over the new material in
`docs/canonization-bounded-degree.md`, abbreviated "W". "W L…" means a line of W. The first red-team
(`docs/redteam-w4-gnscanon.md`) covered Lemmas S, T, T′, T″, K, R and F1–F4. I re-read those lemmas
only where §7 or §8 depends on them.

**Sources.** All are untrusted data, read only.

| short | what | where |
|---|---|---|
| GNS | arXiv:1802.04659v3; "G L…" = line of `bounded-degree-polylog-d.tex` | `r4-sources/arxiv-1802.04659/x/` |
| BL83 | Babai–Luks, STOC 1983, OCR of `CanLabel.pdf` | `r4-sources/w5w-bl83/` |
| BC | Babai, STOC 2019, text | `r4-sources/w3c-babai-canon/` |
| GAP-1 red-team | `docs/redteam-gns-lemma72.md` and its check script | worktree |
| new | publisher, repository and API responses for SICOMP and Neuen's thesis | `r4-sources/w8rt-*/` |

Parts read in full: W §§2.5, 6.2, 7, 8, 10, 11, 13; GNS L420–570 (Lemmas 2.6–2.8), L1955–2200
(Lemmas 6.6–7.2, Alg. 4, Thm 7.3) and L2300–2388 (App. A); BL83 §4.2–4.3 (OCR L670–875); BC
L95–135 (Thm 2.2).

**Executed.** `nice python3 -I docs/redteam-canonization-writeup-check.py` (new, about 30 s). It
brute-forces §8 on small graphs and checks the §7.3 arithmetic. I also ran two mutants of the script,
which it catches. No Lean, no solver.

---

## 0. Verdicts

| section | verdict | one line |
|---|---|---|
| §7.1 recursion lemma | **sound** | Lemma 7.0 implies GNS Lemma 2.8 and covers the semi-regular step. The text's "b² pieces of size n/b" is imprecise, but the bound holds. |
| §7.2 [GAP-1] | **confirmed** | The gap is in GNS's written proof, not in the theorem. Two wording fixes from the GAP-1 red-team are still not applied. |
| §7.3 fix and potential | **sound** | I checked each step, and the arithmetic numerically for 13 ≤ k ≤ 5000. The fix is a legal run of GNS's algorithm. |
| §7.4 call tree, branch table | **sound** | Every row matches GNS. No branch is explored by canonization and not by the isomorphism test. Two places need clearer wording. |
| §7.5 time bound | **sound, one wrong sub-claim** | "A (B)-child is transitive" depends on which chain rule is meant. The total bound survives. |
| §8 canonical Luks reduction | **sound** | Padded slots, Γ̂_{d−1} membership, the coset bookkeeping, the generators, components and the 3n⁴ bound are all correct. Machine-checked on 47 graphs: Claims 4 and 5 exhaustively; Claims 1 and 3 on all (λ, β) up to 40 per layer, sampled beyond. One presentation gap: Claim 4 applies Claim 2 to automorphisms of X_{r+1}. |
| §2.5 tags | **sound** | It closes the first red-team's "fresh blank" caveat. Recursive calls do receive only plain restrictions. |
| §10 assumptions | **gap (documentation)** | Four items are used but not listed. The main one: every subroutine feeding a (P1) choice, including BC Thm 2.2, must be deterministic and run on canonical generators. |
| §13 questions | adequate | Add one question on BC's dependence on the generating set (§4.3 below). |
| literature | **not accessible** | Neither the SICOMP 2023 text nor Neuen's thesis is openly reachable. No erratum is registered, and nobody has published canonization for degree d (§5). |

**Overall: no break.** Section 6 lists two small slips I found in older sections while checking §7.

---

## 1. §7: running time

### 1.1 Lemma 7.0 against GNS Lemma 2.8 (W L755–770, G L486–558)

* GNS Lemma 2.8 (G L538) allows two kinds of steps:
  * (1) n_i ≤ n/2 with Σn_i ≤ 2^k n;
  * (2) Σn_i ≤ n with ℓ ≥ 2.
  Lemma 2.6 (G L486) turns (1) into Σ(n_i/n)^{k+1} ≤ 1.
* Lemma 7.0(A) assumes this power-sum bound directly, and (B) is GNS's case (2). So Lemma 7.0 implies
  Lemma 2.8. The induction (W L762) is the same as GNS's.
* **Semi-regular step.**
  * GNS Alg. 4 (G L2165–2166) applies "standard Luks reduction" when G^{𝔅₁} is semi-regular. G is
    transitive, so the action is regular with b = |𝔅₁| elements, and b is unbounded (e.g. C_n
    regular, b = n).
  * The recursive sizes sum to b·n, which exceeds 2^k n once b > 2^k. So GNS Thm 7.3's appeal to
    Lemma 2.8 (G L2182) does not literally cover this step. [GAP-2] is real, and minor.
* **Lemma 7.0(A) covers it, but the text's description is imprecise.**
  * W L767 and §6.2 step 3 (W L673–675) say "b orbits of size n/b each", and W L854 says "b cosets ×
    b orbits".
  * In fact the pieces of each branch are the orbits of the successive right subgroups inside
    H_{(𝔅₁)}. Each has size ≤ n/b, they sum to n, and there may be more than b of them.
  * The inequality still holds: per branch, Σ(n_i/n)^{K+1} ≤ (1/b)^K·Σ n_i/n = b^{−K}, so over b
    branches the total is ≤ b^{1−K} ≤ 1 for K ≥ 1.
  * **Fix:** state it this way.

### 1.2 §7.2: the counterexample (W L772–811)

I re-derived the input independently and agree with `docs/redteam-gns-lemma72.md`:
* Round 1 is forced: P = S_m ≀ S₂ is primitive on the cells, and k = m.
* The string gives case (ii), with structure {U, U^c}.
* The large orbit Ω′ = U^c × [m] × [q] carries Sym(U^c) × S_m in product action, so the column system
  is a legal choice at G L2087.
* With that choice k′ = m = k, and H′_{(𝒞′)} acts as S_m on the columns.

The gap is in the written proof only. **Still unapplied from the GAP-1 red-team (§5 there):**
* W L16 and W L808–809 still say that GNS's remark "suggests this was intended". This over-reads
  G L2120; the remark is needed anyway so that H^{𝒞′} makes sense.
* W L774 still calls Neuen's text "verbatim". It differs in notation and at N2683 ("Let 𝔅 ≻ 𝔅₁ be a
  minimal block system").
* The "fewest blocks" reading of G L2087 is not discussed.

### 1.3 §7.3: the fix and the potential (W L813–841)

Setting: an aggregation node (G′, φ, k) has a child R ∈ {R_𝔄, L}. The large orbit Ω′ is processed
under R° ≤ R, and H′ = (R°)^{Ω′} has top partition 𝒞′[Ω′]. At H′ the algorithm picks 𝔇 ⪰ 𝒞′[Ω′],
and φ′ = ψ′ ∘ (action on 𝔇) is defined on G″ ≤ H′.

1. **G″_{(𝒞′[Ω′])} ≤ ker φ′.** An element fixing every 𝒞′[Ω′]-class acts trivially on the coarser
   𝔇. Hence its image under ψ′ is trivial. (This is even more direct than going through 𝒞‴.) ✓
2. **|(G″)^{𝒞′[Ω′]}| ≤ |(R°)^{𝒞′}|.** The 𝒞′-classes meeting Ω′ form an R°-invariant subset of 𝒞′,
   and C ↦ C ∩ Ω′ is a bijection onto 𝒞′[Ω′]. So (H′)^{𝒞′[Ω′]} is a quotient of (R°)^{𝒞′}, and G″
   is a subgroup of H′. ✓
3. **R^{𝒞′} ≅ φ(R).** This uses ker φ = G′_{(𝒞′)}, which follows from ker ψ = N_{(𝒞)} in Lemma 7.1
   and φ = ψ ∘ (action on 𝔅). Then |φ(R)| ≤ |φ(G′)|/(4/3)^k ≤ k!/(4/3)^k. For R = L the index is
   ≥ |Alt(Δ₀)|, and for R = R_𝔄 it comes from Cor. 6.5. ✓
4. **Arithmetic.** The claim is k − k′ ≥ (0.415k − 1)/log₂ k ≥ k/(3 log₂ k), and the second
   inequality needs 0.0817k ≥ 1, i.e. k ≥ 13.
   * The script computes the exact largest k′ with k′!/2 ≤ k!/(4/3)^k for every 13 ≤ k ≤ 5000.
   * The bound holds throughout, with minimum slack 0.255.
   * Aggregation only runs for k > 10t ≥ 90. ✓
5. **The fixed choice exists and is legal.**
   * 𝒞′ is G′-invariant, hence R°-invariant, and 𝒞′[Ω′] is a block system of H′.
   * It has ≥ 2 classes, because 𝒞′-classes have size n_j/|𝒞| ≤ n/2 < |Ω′|. This uses |𝒞| ≥ 2,
     which follows because ψ is a giant with k ≥ 3, so ker ψ ≠ N (see §4).
   * 𝒞′ ⪰ 𝔅 ⪰ 𝔅₁, so "a minimal block system above 𝒞′[Ω′]" is also one above 𝔅₁[Ω′]. The fix is
     therefore a run that G L2087 permits.
6. **The modified sequence is almost d-ary** (W step 6, L690–693). |𝒞′| ≤ |𝔅| ≤ |𝔅₁| ≤ d, where the
   last bound holds because step 4 is entered only when H^{𝔅₁} is not semi-regular. Each 𝒞′-class
   contains ≤ |𝔅₁| ≤ d blocks of 𝔅₁. In later rounds the new partition 𝒞‴ is inserted above
   𝒞′[Ω′] in the same way. So Thm 5.8 still applies to every descendant. ✓
7. **Nothing else in GNS uses the original 𝔅₁.** Local certificates (Thm 5.8) need only some almost
   d-ary sequence. Thm 5.9, Cor. 6.5 and the case analysis do not use the sequence at all. ✓

**Height.** On a root-to-leaf path k_{j+1} ≤ k_j(1 − 1/(3 log₂ d)). Starting at k ≤ d (A_k is a
section of Sym(𝔅)) and stopping at k ≤ 10t, a path has at most 3 log₂ d · ln(d/10t) + 1 = O(log² d)
aggregation nodes. ✓

**Imprecision.** W L820 calls H′ "transitive". Whether it is depends on the chain rule (see §1.6):
* If the windows are the orbits of the current right subgroup, as in W L373, H′ is transitive.
* If the windows are the fixed R-orbits, as in GNS Alg. 1 and the literal wording of W step 2
  (L671–672), then R° may split Ω′ further.
* In the second case, take the unique transitive descendant of size > n/2 (if any) as H′, and a
  subgroup of R as R°. Steps 1–3 go through unchanged.

### 1.4 The branch-count table (W L849–861), row by row

| row | GNS source | check |
|---|---|---|
| descent H → G′ ≤ d | G L2095–2097 (\|G : G′\| ≤ \|P : N\| ≤ \|𝔅\|) | ✓ |
| Luks for small P | G L2088–2089 | ✓ W uses \|𝔅\|^{1+log\|𝔅\|} ≤ d^{1+log d}. That is the correct threshold for applying Lemma 7.1 with b = \|𝔅\|. |
| k ≤ 10t: ≤ k! | G L2101–2102 | ✓ |
| semi-regular | G L2165–2166 | ✓ count b·(pieces summing to n); see §1.1 |
| local certificates binom(k,t)·t!·n | G Lemma 6.2 | ✓ Large windows: ≤ t! cosets, N-orbits ≤ \|W*\|/t (Thm 5.9; W* is a union of affected G_i-orbits). |
| colours ≤ k^t·n | new (Lemma T″) | ✓ A_i = ker(ψ_{T₀}\|_B) with B = Aut_{H_{T₀}}(F_i) = G_i(T,x)^{στ_i}. V′ is a union of affected B-orbits, so A_i-orbits are ≤ n/t. Sizes ≤ \|W\| ≤ n per tuple. |
| Option 1: r ≤ k⁶ | G Lemma 6.7, App. A | ✓ \|I\| ≤ 4 gives ≤ k⁴, orbitals ≤ \|C′\| ≤ k, vertex ≤ k |
| Option 2: 2 calls under L | G Lemma 6.9 (h₁ = g, h₂ = τg) | ✓ Lemma K also covers the case φ(G′) = A_k with no odd τ, which GNS do not address. |
| index ≥ (4/3)^k | G Cor. 6.5; \|Alt(Δ₀)\| | ✓ |
| BC/Iso ≤ k⁶ calls, domain ≤ 2k^t | G L2019 (Babai16 on structures) | ✓ log of the domain size is O(log² d), so the cost is exp(O((log d)^{2c_BC})). |
| poly(n) overhead per node | — | ✓ |

**Totals (W L866–872).**
* Per level: ≤ d branches for the descent, times ≤ k⁶ branches for Option 1, which is ≤ d⁷. So
  𝒯 has ≤ d^{7(h+2)} = 2^{O(log³ d)} nodes.
* Exits per node: 2k^t·n + k⁶·n + max(|P|, k!, b)·n = 2^{O(log² d)}·n. The b term is from a
  semi-regular leaf; see §1.6.
* Every exit has size ≤ n_j/2 ≤ n/2, where n is the domain size at the root of the macro step. ✓

### 1.5 Does canonization explore branches that the isomorphism test does not?

**No.** I went through every place where W takes a minimum or a union over branches.

* **Descents (H → G′, Luks, ker φ, semi-regular, large windows).** GNS also enumerate every coset;
  they never stop after one isomorphism (G L459–470, L2097, L2101).
* **Case (iv) family (F4 over all (I, R, v)).** GNS fix one choice for x₁ and enumerate the same
  family for x₂ (G L2352–2364). The count is equal.
* **Case (iii).** Moving Δ to Δ₀ via Lemma S is not a branch, and Lemma K makes two calls. GNS also
  make two (h₁, h₂).
* **Case (v).** There is one structure per string in GNS and one canonical structure here. The
  colours cost k^t·n, against GNS's binom(k,t)²·t!·n comparisons.
* **Chain rule.** Windows that are orbits of the shrinking right subgroup are finer than GNS's fixed
  orbits, so they never cost more.
* **Early exits.** GNS stop when x₁ and x₂ fall into different cases. Canonization computes one side
  only, and that costs the same as one side of GNS.
* **The fix.** It adds no branch; it picks one of the runs that GNS allow.

### 1.6 Wording in §7.4–7.5

1. **W L847.** "Calls in the intransitive and semi-regular steps are separate macro nodes of
   Lemma 7.0." This is true only at the *root* of a macro node.
   * Inside 𝒯, the chain rule on R's orbits is part of the macro step; that is how §7.3 treats it.
   * A semi-regular step at an inner node H′ (with H′^{𝒞′[Ω′]} semi-regular) must be a leaf of 𝒯
     whose children are exits.
   * The children have size |Ω′|/b ≤ n/2 and total ≤ b·|Ω′| ≤ d·n. If H′ were a separate node of
     Lemma 7.0 instead, (A) would fail, because |Ω′| > n/2.
   * **Fix:** say so, and add b ≤ d to the leaf term.
2. **W L881.** "Depth ≤ 2 log₂ N + 1 … because a (B)-child is transitive."
   * This holds for the chain rule of W L373 (windows = orbits of the current right subgroup).
     There, the window function must be read as the pull-back V(y) := V*(F(y))^{λ⁻¹}, λ ∈ Λ(y),
     to be equivariant; "least point" is not H-invariant.
   * It fails for W step 2 read literally (fixed H-orbits): a child (O, A^O) can be intransitive
     again.
   * The bound itself survives: every node lies on a root-to-leaf path and the depth is ≤ N, so there
     are ≤ (N + 1)·N^{K+1} nodes. Alternatively, merge consecutive (B)-steps.
   * **Fix:** pick one chain rule in §6.2 step 2 and use the matching depth argument.

**Verdict on §7: sound.** The recursion lemma, the potential with the fix, the height, the call tree
and the branch counts are correct. The fixes are wording only (§1.1, §1.3, §1.6), plus the two
pending GAP-1 edits (§1.2).

---

## 2. §8: canonical Luks reduction (W L898–1030)

### 2.1 Comparison with BL83 §4.2–4.3

* **BL83 §4.3.**
  * Reduce to connected graphs, with components taken "in lexicographic order of adjacency
    matrices".
  * Individualize an edge e; Lemma 4.3/4.4 says Aut(X(e)) ∈ Γ̂_{d−1} when the outvalence is ≤ d−1.
  * Alternate two steps: canonize Y_r (edges inside V_r) w.r.t. the current coset, then extend
    through the bipartite graph Z_r by §4.2.
* **BL83 §4.2, trick 4.**
  * Place the valence string; extend the coset to edges, "allowing arbitrary permutations of edges
    with common origin". The kernel is ∏ S_{x(b)}, so the composition width is
    ≤ max(d_out, cw(G)).
  * Place y(e₁, e₂) = [same endpoint] on E × E.
  * Order C by the least incident edge.
* **W's version.**
  * It replaces the valence placement by q = d − 1 padded slots per vertex with an occupancy bit.
  * It folds Y_{r+1} into the pair values "E".
  * It orders the new vertices by the least slot of their "="-class, exactly like BL83's "least
    incident edge".
* Both deviations are cosmetic, as W says. Padding replaces ∏ S_{deg↓} by S_q^L. This group is
  larger, but it is still in Γ̂_{d−1}, and Claim 1 shows that the extra freedom on empty slots is
  harmless.

### 2.2 Group class, padded domain, sizes

* **Ĥ = S_q ≀_L Â_r with Â_r = Aut(CF_r; 1, 2)**, the *doubly rooted* group, not Aut(CF_r).
  * This matters. If CF₁ is the star K_{1,d} centred at the label of u, then Aut(CF₁) ≅ S_d, while
    Aut(CF₁; 1, 2) ≅ S_{d−1}.
  * For r = 0, the down-degree bound q also needs uv ∈ E (W L930–931). ✓
* **Ĥ ∈ Γ̂_{d−1}.** S_q^L is normal with quotient Â_r. By induction, Â_{r+1} = θ(Aut_Ĥ(F̂)) is a
  quotient of a subgroup of Ĥ.
  * This uses closure of Γ̂ under subgroups, quotients and extensions. Extensions are not in the §10
    list (see §4).
  * It reproves BL83 Lemma 4.3. ✓
* **What Theorem A needs:** membership in Γ̂_{d−1}, generators, and an ordered domain. Ĥ is a
  function of CF_r as a set, and Ξ_r and its order are functions of (N_r, L, q). ✓
* **Faithfulness.** Including [N_r] in Ξ_r is needed. Â_r need not act faithfully on L = I_r alone,
  and ĥ must determine â for μ and θ. ✓
* **Sizes.** |Ξ_r| = N_r + |V_r|q + (|V_r|q)² ≤ n + n² + n⁴ ≤ 3n⁴, using q ≤ n. Equally,
  ≤ 3n²d². ✓
* **Calls.** There are ≤ nd ordered edges and ≤ n layers, so ≤ n³ calls of cost (3n⁴)^{O((log d)^c)}
  each. ✓

### 2.3 Coset bookkeeping (Claims 1–5)

I checked every claim by hand, in the conventions of W §2.1 (right actions, x^g(α) = x(α^{g⁻¹})).

* **(I_r): Λ_r = λÂ_r.** Isomorphisms fix the roots and preserve distance. Distances in X_r equal
  those in X, because shortest paths to V_i stay in V_{≤i}. So every λ ∈ Λ_r maps V_i onto I_i. ✓
* **Claim 1.** s_ℓ is indexed by the *source* label ℓ = y^λ, which matches
  (ℓ, i) ↦ (ℓ^â, i^{s_ℓ}). Occupied slots are the first deg↓ slots on both sides. ✓
* **Claim 3.** Two facts are needed:
  * "=" is an equivalence relation in F̂, because it is one in x and F̂ = x^ĥ;
  * the slots of one y have distinct endpoints, because β_y is a bijection.
  Every w ∈ V_{r+1} has an up-neighbour, so μ is a bijection onto I_{r+1}. No edge of X_{r+1} joins
  V_{r+1} to V_{≤r−1}. ✓
* **Claim 4, a presentation gap.** The proof applies Claim 2 to an automorphism g of
  (X_{r+1}, u, v), but Claim 2 (W L966–968) is stated for isomorphisms of (X, u, v).
  * The step is valid because x_{λ,β} depends only on (X_{r+1}, u, v): V_{r+1}, the down-edges and
    the edges inside V_{r+1} are all read off X_{r+1}.
  * I verified directly that x_{g⁻¹λ, β∘g⁻¹} = x_{λ,β}, that g⁻¹λ ∈ Λ_r, and that
    μ(g⁻¹λ, β∘g⁻¹, ĥ) = g⁻¹μ.
  * **Fix:** state Claim 2 for (X_{r+1}, u, v).
* **Claim 5.** b ∈ Â_{r+1} preserves [N_r], because it fixes 1 and 2 and preserves layers. It also
  preserves down-degrees, so s_ℓ extends over the empty slots. The F̂-value on a pair of occupied
  slots is "=", "E" or "≠" according to (same class, edge between classes, neither), and b preserves
  that. ✓
* **Step 1 (min over ordered edges).** The proof is the same as F4. If X^λ = m, then (1, 2) is an
  edge of m and (1^{λ⁻¹}, 2^{λ⁻¹}) is a minimizing root. The right subgroup is generated by
  Aut(CF; 1, 2) together with λ₁⁻¹λ_j for each minimizing root, as in the F3 remark. ✓
* **Step 0 (components).** The components of CF(X) are exactly the intervals, because each form is
  connected. A labelling of X onto CF(X) restricts to a member of Λ(C) on each component, after an
  interval shift. The generators are ∏Aut(CF(C)) together with swaps of equal intervals. ✓

### 2.4 Machine check

`docs/redteam-canonization-writeup-check.py` implements §8 literally. Ĥ, Ξ_r and its order, the string
x_{λ,β}, the read-off of CF_{r+1}, μ and θ are all as in the text. F̂ is the lexicographically least
Ĥ-image, which is a valid Ĥ-canonizer and stands in for Theorem A.

For 47 connected graphs it checks every ordered edge and every layer. The graphs are K₄, C₆, the
prism, K₃,₃, K₅, W₄, a degree-4 star with two extra edges, and 40 random graphs with d ∈ {3, 4} and n ≤ 8. It
checks:
* Λ_r = λ₀Â_r;
* Claim 1 (one F̂ for all (λ, β));
* Claim 3;
* Claim 4, as equality with the brute-force set of rooted labellings onto CF_{r+1};
* Claim 5, as equality with the brute-force Aut(CF_{r+1}; 1, 2);
* Step 1: the union of the minimizing Λ(X, u, v) equals every λ with X^λ = CF(X), by enumeration of
  n!;
* invariance of CF under random relabellings;
* for 6 disconnected graphs, invariance of the component rule.

The (λ, β) pairs are enumerated exhaustively up to 40, and sampled beyond that. Pair (λ₀, β₀) is
always included, and by Claim 5 it alone already yields all of Λ_{r+1}.

All checks pass; the largest Ξ_r had 95 points. Two mutants are caught:
* dropping the "E" values fails Claim 3;
* using the wrong action convention when computing Λ̂ crashes the read-off of μ.

**Verdict on §8: sound.** The only fix is the Claim 2/Claim 4 scope.

---

## 3. §2.5: tagged windows (W L227–249)

* x^{[W]} determines W whatever Σ is. Aut_H(x^{[W]}) = {h : W^h = W, x(α^h) = x(α) on W}, which
  checks directly. ✓
* (L2): G_i ⊆ Aut_{H_T}(x^{⟨W_i⟩}), because G_i stabilizes W₁, …, W_{i+1}. Also
  Aut_{H_T}(x^{⟨W_i⟩}) ⊆ Aut_{H_T}(x^{[W_i]}) ⊆ Aut^{W_i}_{H_T}(x) = G_i by (L1). So all three are
  equal. This is what Lemma T′(2) and (3) need. ✓
* **"Recursive calls never receive windowed strings."** I traced every call site.
  * Lemma 5.1 and the F2 windows in Lemma T″ go through F1, i.e. restrictions x|_V.
  * Option 1, Lemma K and all descents use x^σ.
  * Lemma R uses x*, over the same alphabet.
  * The only tagged objects are the J₀-forms used as colours and the strings s_𝔄 passed to BC.
    Neither is a CanAD input. ✓
* The tags (0, ∗), (1, a) and (i, a) need one fixed total order on {(0, ∗)} ∪ (ℕ × Σ). W says this
  ("with a fixed order"). ✓
* In §8 the symbol sets on [N_r], on slots and on pairs live on different Ĥ-invariant parts of Ξ_r,
  so they cannot collide. ✓

**Verdict on §2.5: sound.** It discharges the first red-team's caveat §2.3(1).

---

## 4. §10: are the assumptions complete? (W L1074–1106); §13

The table covers every external result the arguments cite. These are used **silently**:

1. **Determinism and independence from the generating set, for every subroutine that feeds a (P1)
   choice.** This is the substantive omission.
   * §2.4 says that choices are made "by deterministic procedures run on a canonical generating
     set". The table does not list which procedures this covers.
   * The procedures are:
     * the GNS Thm 2.1 algorithms (Seress's book contains randomized ones; deterministic polynomial
       versions exist and must be the ones used);
     * Babai's Lemma 7.1 algorithm;
     * the constructions inside GNS Thms 4.3 and 4.6 (already flagged);
     * **BC Thm 2.2.** BC's "canonical form of strings" takes "(a set of generators of) the group G"
       as input (BC L116–121), and its invariance (ii) is stated for a fixed input. So the call
       F^{BC}_{φ(H)}(s_𝔄) in Prop. 5.5 must be made on the canonical generating set of the group
       induced on [k] ⊔ [k]² ⊔ [k]^t. Alternatively, cite that BC's form depends only on G.
   * **Fix:** add a row "deterministic versions of 1, 11, 4 and 13, run on canonical generators", and
     one sentence in Prop. 5.5.
2. **Γ̂_d is closed under extensions** (Jordan–Hölder). It is used for Ĥ in §8 and is stated in §2.3,
   but row 2 lists only subgroups and quotients. This is trivial; add it to row 2.
3. **Lemma 7.1 gives |𝒞| ≥ 2 and classes of size n/|𝒞|.** This is used in step 5 (W L684) and
   §7.3 (W L822). It follows from ker ψ = N_{(𝒞)}, ψ a giant with k ≥ 3, and 𝒞 an equipartition.
   Say so.
4. **k ≤ |𝔅| ≤ d** (A_k is a section of Sym(𝔅); stated at G L2092). It is used for the height and
   the call-tree bound. This is trivial; one clause.

These are **not missing**, contrary to my first suspicion:
* Babai's string isomorphism, needed for Λ′ in Prop. 5.5, is in row 13.
* Lexicographically least coset elements are in row 15.
* GNS Lemma 2.6 is in row 12.
* Thm 5.8 is used for the *modified* sequences of step 6. Row 6 covers this, because those sequences
  are almost d-ary (§1.3, item 6).

**§13.** The questions are the right ones. Add to Q4: "BC's canonical form takes a generating set as
input. We call it on canonical generators. Is the output known to depend on G only?" Q1 should
include the "fewest blocks" reading of G L2087 (GAP-1 red-team §1).

**Verdict on §10: gap in documentation, not in mathematics.** All four items hold. Item 1 is the one
a referee would ask about.

---

## 5. Literature: SICOMP 2023 GNS and Neuen's thesis

All downloads are under `r4-sources/w8rt-sicomp/`, `w8rt-neuen-thesis/`, `w8rt-search/` and
`w8rt-gnsw-1803.06858/`. No paywall or bot check was bypassed.

* **SICOMP 52(6) 2023, DOI 10.1137/19M1245293: not accessible.**
  * epubs.siam.org, both `/doi/` and `/doi/pdf/`, returns 403 with a Cloudflare challenge.
  * OpenAlex and Semantic Scholar list only arXiv as an open copy. OpenAlex also lists a submitted
    version at RWTH (record 752231), which is behind a JavaScript check page.
  * dblp returned an Anubis bot check. CORE has no record. Grohe's and Neuen's homepages link only to
    SIAM or arXiv.
  * Unpaywall rejected a placeholder email (422). I did not resend the request with the user's
    address.
  * Crossref: online 2020-02-19, in print 2023-12, pages FOCS18-1 to FOCS18-36. **No erratum or
    update is registered.**
  * arXiv v3 (30 Nov 2019; "adds additional explanations and corrects several typos") predates the
    online date, but whether it equals the journal text is unverified.
  * **Lemma 7.2 in the SICOMP text remains unchecked.**
* **Neuen's thesis (RWTH 2019, DOI 10.18154/RWTH-2020-00160): not accessible.**
  * doi.org redirects to `publications.rwth-aachen.de/record/775652`. The record, its file list and
    the PDF all return the same JavaScript check page, and the OAI endpoint returns 503.
  * CORE (id 286899353) does not offer the full text to public API users, and its download link
    returns a Cloudflare 403.
  * The thesis is not on arXiv or on Neuen's MPI page.
  * The abstract mentions the n^{polylog d} isomorphism test and does not mention canonization.
  * **Note for the user.** The first red-team got Wiebking's thesis from the same RWTH server by
    reading the JavaScript and replaying its cookie (`APP_INIT=1`). I did not do that here, because
    it works around a bot check. Whether to do it for Neuen's thesis (green OA per OpenAlex) or for
    GNS record 752231 is your decision.
* **Searches** (arXiv, Semantic Scholar and OpenAlex citations of GNS, the web, 2024–2026). No
  canonization in n^{polylog d} for degree d, and no erratum. Supporting quotes:
  * Wiebking's thesis, p. 242, Question 9.6, and pp. 17–18: "subroutines [GNS18] that do not extend
    to canonization so far".
  * Grohe–Neuen–Schweitzer–Wiebking, arXiv:1803.06858: its canonization "avoids the results of
    [GNS, Babai16]".
  * Neuen's TALG 2022 paper (= arXiv:2002.06997v2) and his 2026 survey make no degree-d canonization
    claim.

---

## 6. Two slips outside the four sections (found while checking §7)

1. **Lemma F1 (W L345) and Lemma 5.1 (W L486): "right subgroup".**
   * Lemma 2.2 defines the right subgroup as Aut_H(F_H(x)). F1 instead says its right subgroup is
     Aut_H(x^{[U]}), and Lemma 5.1 says G_{i+1} = Aut_{G_i}(x^{[W*]}) "is the right subgroup".
   * Both should read Aut_H(x^{[U]}) = λ·Aut_H(F)·λ⁻¹ for λ ∈ Λ.
   * Taken literally, the window chain would be computed for F rather than x. Lemma T″ (W L597) uses
     the correct conjugation.
   * This slip is also in the first red-team (§4, "Aut groups are the right subgroups"). One-line
     fix.
2. **§6.2 step 3 and §7.1: "b orbits of size n/b".** H_{(𝔅₁)} may have more and smaller orbits
   (§1.1). This is harmless.

---

## 7. Overall verdict

**No break.** §§7 and 8, the parts that no one had checked, are correct.
* The recursion lemma covers the semi-regular step.
* The 𝒞′ fix is a legal run of GNS's algorithm, and it restores GNS's own potential inequality.
* The canonical algorithm keeps every GNS branch count and adds no branch.
* The canonical Luks reduction composes correctly, including the coset bookkeeping, the generators
  and the component rule; it was machine-checked on small cases.

Required edits:
* §10 item 1 (determinism; BC on canonical generators);
* the Claim 2/4 scope in §8;
* the wording points in §1.1, §1.3 and §1.6;
* the F1 "right subgroup" slip;
* the two pending GAP-1 edits.

None of them changes a statement.

**Strongest statement I would sign.**

> Assume the results in W §10 (GNS Thms 3.13, 4.3/4.6 with their internal constructions made
> functions of the group, 5.8, 5.9, Lemma 6.2, Cor. 6.5, Thm A.2, Lemma A.3, Lemma 7.1; Babai's
> canonical form of strings, STOC 2019 Thm 2.2, and his string isomorphism test, both on instances of
> size d^{O(log d)}; canonical generating sets; lexicographically least coset elements). Assume also
> that the group-theoretic subroutines used for these choices are deterministic and are run on
> canonical generators. Then strings under Γ̂_d-groups (and labelling cosets of composition width d)
> admit canonical labellings in time n^{O((log d)^c)}, and graphs of maximum degree d admit
> canonical forms and canonical labellings in time n^{O((log d)^c)}.
>
> I checked the running-time analysis (§7), including the repair of the potential argument of GNS
> Lemma 7.2, and the canonical Luks reduction (§8), line by line, with a machine check of §8 on small
> graphs. The gap in GNS Lemma 7.2 is in the written proof only. The fix is correct and applies
> equally to the isomorphism test, so the GNS theorem is not in doubt.

**Limits of this pass.**
* I did not re-verify GNS's group theory (Thm 3.13, Thms 4.3/4.6, Lemma 4.5). I re-checked §§4–6 of
  W only where §7 depends on them.
* The SICOMP text and Neuen's thesis are unread (§5).
* BC remains a preliminary report.
