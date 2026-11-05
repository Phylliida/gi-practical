# Red-team of w8-gnsexp: the GNS exponent and the multiplicative giant potential

Branch `w9-redteam-gnsexp`, 2026-11-05. Referee report on `docs/w8-gnsexp.md` ("the memo"; "M §x"
is a section of it). Brief: break the claimed unconditional improvement in the exponent c of
n^{O((log d)^c)} for isomorphism of graphs of maximum degree d, or certify exactly what was checked.

**Sources** (untrusted data, read only, under `scratchpad/r4-sources/`).

| short | what | where | read |
|---|---|---|---|
| GNS | arXiv:1802.04659v3, "G L…" = line of `bounded-degree-polylog-d.tex` | `w7rt-gns-versions/x3/` | L1040–1130 (Thm 4.3), L1280–1460 (Thm 4.6, Claim), L1942–2201 (§6.3 aggregation, Lemmas 6.6–6.9, §7), L2288–2388 (App. A) |
| Neu20 | arXiv:2002.06997, `hypergraph-gamma-d.tex` | `arxiv-2002.06997/x/` | intro L170–330; L2677–2724 (the same potential) |
| Bab | arXiv:1512.03547, `main.tex` | `arxiv-1512.03547/x/` | Bochert (L930–975), Lemma `prim-topquotient` (L4795–4840), aggregation (L6040–6075); searched for alternating sections |
| GN21 | Grohe–Neuen survey, arXiv:2011.01366 | `grohe-neuen-2011.01366/` | §4.4 (Thm 4.16–4.18, text L1230–1330) |
| Neu26 | Neuen, Comput. Sci. Rev. 2026 | `regensburg-neuen-survey/` | searched for every exponent statement |
| SICOMP | crossref/OpenAlex metadata of SICOMP 52(6) 2023 | `w8rt-sicomp/` | abstract |
| CB | `docs/canonization-bounded-degree.md` | worktree | §5.2, §5.5–5.6, §7 |
| RT72 | `docs/redteam-gns-lemma72.md` | worktree | all |
| Pago | B. Pago, arXiv:2302.05426, `fullVersion.tex` | `w9rt-arxiv2/2302.05426/x/` (found by the subagent) | Lemmas `G_fixingTheRestPointwise`, `G_groupInduction` (L2960–3000) |

**Executed.** `nice python3 -I docs/redteam-w8-gnsexp-check.py` (sympy only, about 2 s): the
Bochert/Praeger–Saxl tables for Lemma A, Lemma A on 11 explicit groups, and the exponent arithmetic of
Corollary D. A literature search (web, Semantic Scholar/OpenAlex citations) was delegated; see §7.
No Lean, nothing touched outside the worktree and the scratchpad.

---

## 0. Verdict

| # | claim (memo label) | verdict |
|---|---|---|
| 1 | GNS as written has c = 5; with the known n^{O(log d)} domain count, c = 4 for all d [PROVEN] | **sound** as bookkeeping of the written proof (upper bounds, not a lower bound on the algorithm). The Lemma 6.7 overstatement is handled correctly (5 with the true cost of the black box, 6 if GNS's display is read literally). |
| 2a | Lemma A: a subgroup of S_k with an A_m composition factor, m > 3k/4, m ≥ 16, contains Alt(Δ) with \|Δ\| ≥ m [PROVEN, CFSG-free] | **true, and the proof is correct.** It holds exactly for m ≥ 6. It **fails at m = 5** (PSL(2,5) and PGL(2,5) on 6 points), which the memo's hypothesis m ≥ 16 already excludes. CFSG-free: Jordan–Hölder plus Bochert's 1889 index theorem. The conclusion is a genuine subgroup Alt(Δ) fixing [k]∖Δ, not merely a section. |
| 2b | Prop. B: k′ ≤ 3k/4 between consecutive aggregation nodes [PROVEN, with the CB §7.3 fix] | **sound in every branch** of GNS's macro step (§3). It needs the fix. Without it the step fails exactly as GNS's own step does (RT72's counterexample has k′ = k). |
| 2c | Theorem C: main recursion n^{O(L³)}, total n^{O(L³)}·X(d) [PROVEN] | **sound.** |
| 2d | Corollary D: c = 3 if log n ≥ log³ d or log n ≤ log^{1.5} d, c = 4 for all d [PROVEN] | **arithmetic correct; framing needs correcting** (§4.3). "c = 3 for log n ≤ log^{1.5} d" is Babai–Helfgott alone. "c = 4 for all d" is already given by row 2 of the memo's own ladder, without Lemma A. Lemma A changes the exponent only when log n > log² d. |
| 2e | c = 10/3 for all d via a Design-Lemma black box [SKETCH] | **plausible; not checked to proof level.** The gaps the memo names are real (§4.4). |
| 3a | c < 2 would beat general GI's exp(O(log³ n)) | **sound** (put d = n − 1). It is a "would be a breakthrough" statement, not a lower bound. |
| 3b | c = 3 is the floor of GNS's architecture [SKETCH] | **a heuristic about this style of accounting, not a theorem.** Its two inputs (heart-module tightness, 2^{Θ(L²)} test sets) check out. |
| 4 | HJ Thm A.9 weak form σ ≤ C log d log N for Γ̂_d [SKETCH]; Cor. F [CONDITIONAL] | **plausible at reading level.** It avoids HJ's valuation lemma, but **not CFSG**: GNS Thm 3.13 uses CFSG. |
| 5 | novelty | **No explicit or improved c for GNS found anywhere; the multiplicative potential appears new.** Lemma A's technique is in print: Pago, arXiv:2302.05426, Lemma `G_groupInduction`, with a large-index alternative and credited to Wiebking. Cite it. Neuen's thesis and the SICOMP text remain unread (blocked) (§7). |

**Overall: no break.** The new mathematics (Lemma A + Prop. B) is correct. The improvement it buys is
real but narrower than the summary suggests. Over the best bound already derivable from the literature
(c = 4 for all d), it gains only for d < 2^{(log n)^{1/2}}, reaching c = 3 for d ≤ 2^{(log n)^{1/3}}.
In particular, d = polylog n gives n^{O((log log n)³)}, against n^{O((log log n)⁴)} from the known
count (the memo compares against GNS's (log log n)⁵). The statement I would sign is in §8.

---

## 1. Claim 1: GNS as written, c = 5; with the known count, c = 4

**Checked.**
* *Thm 4.6 as stated* (G L1290): \|Ω*\| ≤ n^{(c₁ log d + c₂ + 1) log d}, so log N = O(L²ℓ).
* *Lemma 7.2 as stated* (G L2079, L2132–2135): height O(log² d), at most 2^{O(log³ d)} tree nodes,
  exits per node 2^{O(log² d)} n. So Σ nᵢ ≤ 2^{O(L³)} n and K = O(L³). This uses the inequality
  k′ ≤ k − k/(3 log k), which holds only with the CB §7.3 fix (RT72).
* N^{K+1} = n^{O(L²)·O(L³)} = n^{O(L⁵)}.
* *Black box* (Lemma 6.7, G L2013–2020): Iso(𝔄₁, 𝔄_{2,j}) via Miller's graph on k^{O(t)} vertices,
  t = max(9, 3 + log d), k ≤ d. With Helfgott's exp(O(log³ m)) this costs exp(O((t log k)³)) =
  2^{O(L⁶)} ≤ n^{O(L⁵)} (ℓ ≥ L since d ≤ n). The cost is per node, so the total is
  n^{O(L⁵)}·n^{O(L⁵)} and the exponent stays 5.
* *The overstatement.* GNS display k^{O(t^c (log k)^c)} = exp(O(t^c log^{c+1} k)). Babai on k^{O(t)}
  vertices costs exp(O((t log k)^c)), one factor of log k less in the exponent. So the memo's reading
  is right: 5 with the true cost, 6 if the display is taken literally (2^{O(L⁷)} ≤ n^{O(L⁶)}). The
  general formula max(5, 2c_B − 1) is also right.
* *Known count* (M §1.4, Prop. 2). GN21 Thm 4.16 states \|Br(G, v₀)\| ≤ n^{O(log d)}, citing GNS and
  Neuen's thesis (text L1264–1272). I also checked the memo's own re-derivation from GNS's Claim
  (G L1429–1449). GNS bound ∏_{i∈I} binom(mᵢ, tᵢ) by the step-1 domain n₁. The Johnson branchings
  along a branch multiply to the product of the large-primitive branchings b of the original chain,
  which is at most n. So N ≤ n₁·n^{log d − 1} = n^{O(L)}. (The memo's displayed exponent has a
  harmless +1.)
* With N = n^{O(L)}: n^{O(L⁴)}·2^{O(L⁶)}, and min{max(4, 6 − x), 2x} ≤ 4 with the B–H switch
  (check script, part 3).

**Verdict: sound.** These are upper bounds read off the written proof. Nothing shows that GNS's
algorithm actually takes n^{Ω(L⁵)} time (M §1.5 says so itself).

---

## 2. Claim 2a: Lemma A

**Statement (memo).** L₀ ≤ S_k, A_m a composition factor, m > 3k/4, m ≥ 16 ⇒ there is Δ ⊆ [k] with
\|Δ\| ≥ m and Alt(Δ) ≤ L₀ fixing [k]∖Δ pointwise.

### 2.1 The proof, step by step

* **Intransitive.** K = (L₀)_{(R)} ⊴ L₀ is faithful on O, and L₀/K ≅ L₀^R. By Jordan–Hölder, A_m is a
  composition factor of one of them. Induction applies to both (degrees \|O\|, \|R\| < k, and m > 3·degree/4).
  * *Factor of L₀^R.* M ⊴ L₁ (the part of the preimage that fixes O pointwise) restricts injectively to R,
    and M^R ⊴ Alt(Δ), which is simple. If M^R = Alt(Δ), then M = Alt(Δ) as a subgroup of S_k (M fixes O,
    and Alt(Δ) fixes R∖Δ). If M = 1, L₁ embeds in Sym(O) with \|O\| ≤ k − \|Δ\| < k/4 < \|Δ\|, so it cannot
    have a quotient of order \|Δ\|!/2.
  * Correct. Only m > k/2 is used here.
* **Imprimitive.** Block size b and number of blocks b′ are both ≤ k/2 < m. The composition factors of
  the kernel (≤ S_b^{b′}) and of the top (≤ S_{b′}) have order ≤ (m − 1)! < m!/2. Correct; again only
  m > k/2 is used.
* **Primitive, degree n′.** n′ ≥ m by order. n′ = m forces L₀ ≥ A_m (index ≤ 2). For m < n′ ≤ k < 4m/3,
  Bochert (Dixon–Mortimer Thm 3.3B: a primitive group not containing A_{n′} has index ≥ ⌊(n′+1)/2⌋! in
  S_{n′}) must give \|L₀\| < m!/2.

**Is it a subgroup or only a section?** A subgroup. The conclusion is produced either at a primitive
leaf of the induction (whole orbit) or from M in the intransitive branch. In both cases it is a
literal Alt(Δ) ≤ L₀ fixing the complement.

### 2.2 The exact hypothesis (coordinator's question)

**Lemma A holds for every m ≥ 6. It fails for m = 5, k = 6, and for no other pair.** All of this is
CFSG-free.

* *Counterexample at m = 5.* PSL(2,5) ≅ A₅ and PGL(2,5) ≅ S₅ act transitively on the 6 points of
  PG(1,5): 5 > 3·6/4, but neither contains a 3-cycle. So there is no Alt(Δ) with \|Δ\| ≥ 3 at all
  (check script, part 2). The memo's hypothesis m ≥ 16 excludes it.
* *Where Bochert alone suffices.* Scan of all m < 3000 and m < n′ ≤ ⌊(4m − 1)/3⌋ (part 1): Bochert
  excludes every pair except **(5,6), (7,9), (8,10)**. Beyond 3000 the margin grows. Bochert's bound
  is ≤ n′^{n′/2}, and at n′ = 4m/3 we have (4m/3)^{2m/3} < (m/e)^m/2 for m ≥ 40, with a gap growing like
  (m/3)·log m. So the memo's "m ≥ 16, checked numerically for m < 400, Stirling beyond" is correct,
  and the true Bochert threshold is m ≥ 9.
* *(7,9).* Here 2520 divides \|G\| ≤ 9!/5! = 3024, so G ≅ A₇ with a subgroup H of index 9 (order 280).
  H contains a 7-cycle, so it is transitive of prime degree 7, hence primitive. Bochert gives
  \|H\| ≤ 7!/4! = 210 < 280. Contradiction.
* *(8,10).* Here G ≅ A₈ with \|H\| = 2016 at index 10. H contains a 7-cycle and does not lie in a point
  stabilizer A₇ (2016 ∤ 2520), so H is 2-transitive on 8 points. Bochert gives \|H\| ≤ 8!/4! = 1680 < 2016.
  Contradiction.
* *m = 6.* Only (6,7) arises, and Bochert covers it.
* **Praeger–Saxl** (\|G\| < 4^{n′}, CFSG-free) covers the 3/4 regime for m ≥ 15. The memo's "m ≥ 42 for
  all n′ < 2m" is correct; the exact value is m ≥ 40.

**Compatibility with GNS.** Lemma A is only invoked when the next node has a giant, i.e. k′ > 10t with
t = max(9, 3 + log d). So k′ ≥ 91 ≫ 6, and Cor. 6.5 (n ≥ 24) holds as well. Every other way of
leaving a node (k′ ≤ 10t, small P′, semi-regular top, small orbits) is an exit or a leaf and needs no
decrease (§3.2).

### 2.3 Sharpness and a stronger form (not needed)

* The intransitive and imprimitive branches only use m > k/2. With Praeger–Saxl in the primitive branch,
  **"m > k/2 and m ≥ 40" also suffices** (part 1: the largest uncovered m is 39).
* The threshold k/2 is sharp: diagonal A_m on two copies of [m] (k = 2m).
* Below 40 the k/2 form genuinely fails: PSL(2,9) ≅ A₆ on 10 points and GL(4,2) ≅ A₈ on 15 points
  (part 2).
* This does not help Prop. B, whose 3/4 comes from the symmetry defect 1/4 of GNS's cases (i) and (ii).

### 2.4 "CFSG-free"

True of the lemma: it uses Jordan–Hölder and Bochert 1889 (or Praeger–Saxl 1980). **The algorithm is
not CFSG-free**, and the memo should say so where it advertises the lemma. GNS rely on CFSG through
Lemma 7.1 (Babai Thm 3.2.1, Cameron's theorem), Thm 3.13 ("applying the classification of finite
simple groups", G L212–214), and App. A Thm A.2 (degree of transitivity
≤ 5, G L2298–2304). The improvement adds no CFSG dependence and removes none.

**Folklore?** The statement is not in Babai (searched "involve", "section", "composition factor",
Bochert), GNS, Neu20, GN21 or Neu26. But the proof technique is in print (§7). Pago (arXiv:2302.05426,
Lemmas `G_fixingTheRestPointwise` and `G_groupInduction`, crediting Wiebking) proves, by the same
induction, that an Alt_m composition factor with m ≥ cn gives either Alt(A) ≤ G fixing the complement
(\|A\| ≥ cn) or a large index. Lemma A is a non-asymptotic sibling: for m > 3k/4, Bochert rules out the
index alternative. Present it with that citation.

**Verdict on 2a: true; proof correct; hypothesis m ≥ 16 safe (exact: m ≥ 6).**

---

## 3. Claim 2b: from Lemma A to k′ ≤ 3k/4

### 3.1 The chain of sections, checked against GNS

Notation as in G L2084–2134 and CB §7.3. At a node: P = G^𝔅 primitive, N ⊴ P (index ≤ d),
φ : G′ → S_k with ker φ = G′_{(𝒞′)} (G L2099). Hence H^{𝒞′} ≅ φ(H) for every H ≤ G′.

1. The child is H (Option 1: H_j; Option 2: G_{(Δ₁)}). Its large orbit Ω′ is processed under some
   H° ≤ H; this is GNS's "H′ is the projection of H″ ≤ H" (G L2124).
2. With the fix, the next node chooses 𝔇 ⪰ 𝒞′[Ω′], and P′ = (H′)^𝔇. Lemma 7.1 gives N′ ⊴ P′ and a giant
   on N′. Since N′ is normal, A_{k′} is a composition factor of P′.
3. P′ is a quotient of (H′)^{𝒞′[Ω′]}. That group is a quotient of (H°)^{𝒞′}, which is isomorphic to
   φ(H°) ≤ φ(H) ≤ S_k. So L₀ := φ(H°), a permutation group of degree k, has A_{k′} as a composition
   factor.
4. If k′ > 3k/4, Lemma A gives Alt(Δ) ≤ φ(H°) ≤ φ(H) with \|Δ\| > 3k/4.

Every step is correct. Step 2 is exactly where the fix enters. Without it, P′ need not be a quotient of
(H′)^{𝒞′[Ω′]} (RT72's column choice), and Lemma A says nothing about the kernel part.

### 3.2 Every branch of the macro step

| transition out of a giant node | same domain? | covered by |
|---|---|---|
| Option 1, H_j = {g : D₁^{φ(g)} = D₁, φ(g)\|_{D₁} ∈ Aut(𝔄₁)} (G L2016–2018) | yes | defect (below) |
| Option 2, H = G_{(Δ₁)}, φ(H) fixes Δ₁ pointwise (G L2049) | yes | trivially k′ ≤ k/4 |
| descent G → G′ at the next node (index ≤ d) | yes | no change of k; the giant is defined after it |
| H intransitive: small orbits / large orbit under H° ≤ H | exits / yes | exits; step 3 above handles H° |
| next top semi-regular (Luks) | no | exits (orbits inside blocks) |
| \|P′\| ≤ d^{1+log d} (Luks) | no | exits |
| k′ ≤ 10t (Luks to ker φ′) | no | exits; orbits inside 𝒞‴-classes |
| local certificates, comparisons | no | exits (windows ≤ n/2) |

**Option 1 defect.** φ(H_j) stabilizes D₁ setwise, and Alt(Δ) is transitive on Δ. So Δ ⊆ D₁ or
Δ ∩ D₁ = ∅, and the latter is impossible when \|Δ\| > 3k/4 ≥ k − \|D₁\|. Then Alt(Δ)\|_{D₁} ≤ Aut(𝔄₁), so
\|Δ\| ≤ (3/4)\|D₁\| ≤ 3k/4. This holds in each App. A case:
* (i) and (ii) by GNS's own statement;
* (iv) via CB Prop. 5.2, which also absorbs GNS's slip \|C′\| ≥ 3k/4 − 4;
* (v), where the defect is ≥ \|D\| − t + 1.

The canonical version (CB §5.5–5.6: R_𝔄 = φ⁻¹(Aut_{φ(H)}(𝔄_can)), L = H_{(Δ₀)}) is identical.

**Height.** k₀ ≤ d (a giant section of a subgroup of S_{\|𝔅\|}, \|𝔅\| ≤ d). Each aggregation needs
k > 10t, so there are at most log_{4/3}(d/10t) + 1 = O(L) aggregation nodes on a same-domain path.

**Verdict on 2b: sound (given the CB §7.3 fix, which RT72 checked).**

---

## 4. Claims 2c–2e: the cost accounting

### 4.1 Theorem C

* *Tree size.* Each level branches ≤ d (descent) × max(k⁶, 2) (children). Over O(L) levels this gives
  \|𝒯\| ≤ d^{7·O(L)} = 2^{O(L²)}. The large-orbit continuation does not branch: there is one orbit of
  size > n/2.
* *Exits per tree node.* At most C(k,t)·t!·n (certificates), C(k,t)²·t!·n (comparisons), k⁶n (small
  orbits of children), and at leaves max(d^{1+log d}, d·(10t)!)·n. All of these are 2^{O(L²)}·n.
* *The recursion.* Σ nᵢ ≤ 2^{O(L²)} N, with nᵢ ≤ N/2. So K = O(L²), and CB Lemma 7.0 gives N^{K+1}
  leaves. With N = n^{O(L)} (§1), the main recursion is n^{O(L³)}.
* *What dominates.* The exponent of K is now set equally by the tree size and by the per-node test
  sets: both are 2^{Θ(L²)}. This is why the memo's barrier (b) says 3 is the end of the line for this
  accounting.
* *Per-node work.* At most 2^{O(L²)}·k⁶ black-box calls and poly(N) work. Total:
  n^{O(L³)}·(1 + X(d)).

### 4.2 The black box X(d)

* Only App. A case (v) needs a (log d)-ary structure. Cases (i)/(ii) are colourings and partitions,
  case (iv) is binary (B–H gives 2^{O(L³)}), and case (iii) is Option 2.
* So X(d) = exp(O((t log k)³)) = 2^{O(L⁶)} via Miller + B–H.
* Neuen's hypergraph test does not help. It runs in (n+m)^{O((log n)^c)} with the same unspecified
  GNS-type c (Neu20 L221–228).

### 4.3 Corollary D, and how it should be framed

The arithmetic is right (check script, part 3):
* (α) min{max(3, 6−x), 2x} is 3 exactly when x ≤ 1.5 or x ≥ 3, and its maximum is 4 at x = 2.
* (β) min{max(3, 5−x), 2x} has maximum 10/3 at x = 5/3.

But compare it with the memo's own row 2 (known count, no Lemma A): min{max(4, 6−x), 2x}.
* For x ≤ 2 the two rows are equal. Lemma A lowers the exponent **only for x > 2**, i.e.
  d < 2^{(log n)^{1/2}} (part 3 asserts this).
* **"c = 3 for log n ≤ log^{1.5} d"** is plain B–H: exp(O(log³ n)) = n^{O(log² n)} ≤ n^{O(L³)} when
  ℓ ≤ L^{1.5}. No part of GNS or of the memo is used.
* **"c = 4 for all d"** holds without Lemma A (row 2 of the memo's ladder).
* **"n^{O((log log n)³)} against n^{O((log log n)⁵)} from GNS"** for d = polylog n should also say:
  against n^{O((log log n)⁴)} from GNS plus the known GN21 count.

So the honest headline is this. **For d ≤ 2^{(log n)^{1/3}} (including d = polylog n) the exponent
drops from 4 to 3. For 2^{(log n)^{1/3}} < d < 2^{(log n)^{1/2}} it drops from 4 to 6 − x. The
worst case over all d stays 4.** The memo's table §2.5 has the right numbers; its summary rows 2 and
"Overall c = 3 when … or log n ≤ log^{1.5} d" overstate what is new.

### 4.4 The β-variant (c = 10/3) [SKETCH]

The arithmetic checks: (k^t)^{O(log³ k)} = 2^{O(t log⁴ k)} = 2^{O(L⁵)}. The potential argument also
transfers: children stabilize a canonical colouring with classes ≤ 3k/4, an equipartition (alternating
sections of degree ≤ k/2), or a Johnson scheme J(m″, t″) with t″ ≥ 2 on ≥ 3k/4 points (sections of
degree O(√k) or ≤ k/4).

Unverified:
* the pairwise form of the Extended Design Lemma and Split-or-Johnson inside GNS's aggregation;
* the k^{O(log k)} cost of Split-or-Johnson (taken from HBD's text);
* that I's own case-(v) structures are handled by the Design Lemma with no recursive black box.

The memo names the first two. Keep 10/3 as [SKETCH].

---

## 5. Claim 3: barriers

* **(a) c < 2.** With d = n − 1, n^{O(log^c d)} = exp(O(log^{c+1} n)). Babai's algorithm with Helfgott's
  analysis gives exp(O(log³ n)), and I know of no published improvement (HJ's exp(O(log² n)) is an
  unrefereed 2026 claim). So c < 2 would improve the general GI exponent. **Sound.** It is a statement
  about the state of the art, not a lower bound; c = 2 would merely match B–H at d = n.
* **(b) Floor 3 for GNS's architecture.** Two inputs, both checked.
  * *e = 1.* Heart-module levels E ⋊ A_k (k odd, E the even-weight code, degree 2^{k−1}) have
    unaffected point stabilizers with k = log₂ b + 1. So Babai's threshold k > 2 + log₂ n is tight to
    an additive 1, and such levels must be made semi-regular by step 1 at cost b^{Θ(log k)} each.
  * *a = 2.* Every node with k ≥ d^{Ω(1)} has C(k,t) ≥ 2^{Θ(L²)} test sets.

  The conclusion "K·log N ≥ L²·Lℓ" is about the Lemma 2.8/7.0 accounting, which charges each halving
  separately. It is not a theorem about every algorithm in the GNS family. **Heuristic, correctly
  labelled [SKETCH].** (b)(c) are fine as research guidance.

---

## 6. Claim 4: HJ Thm A.9 weak form

Read at proof-sketch level only, as low priority.
* The option-1 step σ ≤ 6 log₃\|P\| is valid. Marked quotients are sections along a chain, so
  ∏\|Alt(kᵢ)\| ≤ \|P\|. In fact σ ≤ log₃\|P\| already, since k ≤ log₃(k!/2) for k ≥ 64.
* The block inequality F(a) + F(b) ≤ F(ab) holds for F = C log − B with B ≥ 0.
* Theorem E remains [SKETCH], because option 2 uses details of GNS's proof (not its statement).
* Corollary F remains [CONDITIONAL] on HJ §§4–7.

**Correction.** "not on Thm A.9's CFSG lemma" is accurate, but the result still uses CFSG through GNS
Thm 3.13. GNS say so (G L212–214), and their Lemma 3.7 rests on the Cooperstein and Kleidman–Liebeck
minimal-degree tables (G L657–665). Say "independent of HJ's valuation lemma", not "CFSG-light".

---

## 7. Novelty

A subagent searched the literature on 2026-11-05; its downloads are in `r4-sources/w9rt-*`. I re-read
Pago's lemmas, the GNS/Neu20 potential, GN21 §4.4, Neu26's exponent statements and the SICOMP abstract
myself. The rest of this list is the subagent's report.

**Read in full text or searched in full.**
* GNS v3;
* Neu20;
* GN21 (TeX);
* 1911.11257, 2004.07671, 2011.14730, 1806.07466, 1803.06858, 2210.14638, 2104.02994;
* Babai 1512.03547;
* Pago 2302.05426;
* Neu26 (PDF);
* Kantor 1991.

**Citation lists.**
* Semantic Scholar: 35 papers citing arXiv:1802.04659, plus the lists for the SICOMP DOI, 2002.06997 and
  2011.14730.
* OpenAlex: both GNS records (21 and 11 citing papers).

**Partial.**
* the SICOMP abstract (crossref/OpenAlex): "$n^{O((\log d)^c)}$ … $c$ is an absolute constant";
* the first 100k characters of HJ 2611.01399.

**Blocked, not bypassed.**
* SIAM epubs (403), so the SICOMP full text is unread.
* ScienceDirect (403).
* RWTH (bot challenge) and CORE (Cloudflare), so Neuen's 2019 thesis is still unread.

| question | finding |
|---|---|
| explicit c for GNS (3, 4, 5, …) | **none.** GNS, SICOMP abstract, Neu20, GN21 (Thm 4.18 "n^{polylog(d)}") and Neu26 (Cor. 4.7 "n^{polylog(d)}") leave c unspecified. GN21 Thm 4.16 gives the n^{O(log d)} normalization, so c = 4 is one line of bookkeeping away from the published record. |
| multiplicative potential k′ ≤ 3k/4 in the Γ̂_d setting | **none.** Neu20 copies GNS's k′ ≤ k − k/(3 log k) and height O(log² d) verbatim (Neu20 L2722). Babai's general algorithm gains a constant factor via 3/4-partitions and Johnson schemes, but on an ideal domain, not on the giant degree in Γ̂_d. |
| Lemma A | **not found as stated. The closest relative is in print:** Pago, *Lower bounds for Choiceless Polynomial Time via Symmetric XOR-circuits* (arXiv:2302.05426; venue not checked). His Lemma `G_fixingTheRestPointwise` is exactly the memo's M^R argument. His Lemma `G_groupInduction` is the same induction on compositional structure. It concludes either Alt(A) ≤ H fixing the complement, with \|A\| ≥ cn, or a large index of G_n in Sym_d. He credits Wiebking for the primitive case. Lemma A is a non-asymptotic sibling: for m > 3k/4, Bochert rules out the index alternative. **Cite Pago (and Wiebking).** |
| improvements to GNS since 2018 | **none.** HJ 2611.01399 claims exp(O(log² n)) for general GI and cites GNS's n^{polylog d}; it makes no bounded-degree claim in the part read. |

**Novelty verdict.**
* The application to GNS appears new: Lemma A + defect ⇒ k′ ≤ 3k/4 ⇒ height O(log d) ⇒ main recursion
  n^{O(log³ d)}.
* The explicit exponents 5 and 4 are new as statements but are routine.
* Lemma A itself should be presented as a variant of Pago's Lemma (with credit), not as new.
* The residual risk is still Neuen's thesis and the unread SICOMP text. Neu26 (2026, by the same author)
  states only polylog(d), which makes a sharper potential in the thesis unlikely but does not rule it
  out.

---

## 8. What I would sign, and required edits

**Signed statement.** Assume:
* GNS (SICOMP 52(6), 2023), including its CFSG-dependent inputs;
* the CB §7.3 choice of the next block system (𝔇 ⪰ 𝒞′, RT72);
* GN21 Thm 4.16, or the memo's Prop. 2;
* Helfgott's exp(O(log³ m)) analysis of Babai's algorithm.

Then:
* String isomorphism for Γ̂_d-groups on n points, and so GI for graphs of maximum degree d, is decidable
  in time **n^{O(log³ d)}·2^{O(log⁶ d)}**.
* Hence it is decidable in n^{O(log³ d)} for d ≤ 2^{(log n)^{1/3}}; for d = polylog n this is
  n^{O((log log n)³)}.
* Hence, together with B–H, it is decidable in n^{O(log⁴ d)} for all d. This last bound follows already
  without the new lemma.

The new ingredient is that the giant degree drops by a factor 3/4 per aggregation round. Its key input
is elementary and CFSG-free:
* *Lemma A (m ≥ 6).* A permutation group of degree k with an A_m composition factor, m > 3k/4, contains
  Alt(Δ) for some \|Δ\| ≥ m.
* It is false at m = 5.

**Required edits to the memo.**
1. Summary rows 2 and 2″ and §2.5: state that c = 3 for log n ≤ log^{1.5} d is B–H alone, and that c = 4
   for all d needs no Lemma A. State the gain as "4 → max(3, 6 − x) for log n = log^x d, x > 2".
2. §2.5, last paragraph: compare d = polylog n with (log log n)⁴ (known count) as well as with
   (log log n)⁵.
3. §2.1: record the m = 5 counterexample (PSL(2,5) on 6 points) and that the exact threshold is m ≥ 6
   (Bochert alone gives m ≥ 9; (7,9) and (8,10) need one more Bochert step). Record that "CFSG-free"
   refers to the lemma, not the algorithm (GNS Lemma 7.1, Thm 3.13, Thm A.2 use CFSG).
4. §2.2 proof: note that P′ is a quotient of a subgroup's action (H° ≤ H), so L₀ = φ(H°). The memo
   already says "some subgroup L₀", which is right; spell out why N′ ⊴ P′ makes A_{k′} a composition
   factor of P′.
5. §2.1 and §4: cite Pago, arXiv:2302.05426, Lemma `G_groupInduction` (credited to Wiebking), as the
   source of the composition-factor-to-subgroup induction. Lemma A is a non-asymptotic sibling in which,
   for m > 3k/4, Bochert removes the index alternative.
6. §3.3: "not on Thm A.9's CFSG lemma" → add "still CFSG-dependent via GNS Thm 3.13".
7. Prop. 2: the exponent is (c₁+1)L + c₂, not +1 (harmless).
