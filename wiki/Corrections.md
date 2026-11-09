# Corrections and withdrawals

Everything claimed and later fixed, refuted, narrowed, or found to be already known. Later corrections win:
where this page and an older memo differ, this page is right about what the project now claims. Status of the
current statements is on the [Results ledger](Results-Ledger.md).

[Home](Home.md)

## Withdrawn or refuted

### Arity lower bound for the GNS black box

* **Claim** ([w10-blackbox](../docs/w10-blackbox.md) §0 row 1′): reducing the arity of the case-(v) structures canonically
  costs k^{<t} = 2^{Θ(L²)} branches, because PSL(2,q) makes every isomorphism-invariant binary relaxation trivial.
* **Refuted** by [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2. On the memo's own instance, PGL(2,q) is
  sharply 3-transitive, so 3 individualized points make the colouring discrete: the cost there is k³. The
  poly(k)-family remark is false as stated.
* **What remains.** At most k^{<t} by the Design Lemma; at least one individualization on some instances; whether O(1)
  always suffices is open. Prop 1.3 stands as an elementary statement about Aut(𝔄)-invariant binary relaxations.

### "Neuen 2020 Theorem 4.17(G) is false as stated"

* **Claim** ([redteam-canhyp](../docs/redteam-canhyp.md) §2.1): a counterexample shows the statement false.
* **Narrowed** by [verify-neu417](../docs/verify-neu417.md). Theorem 4.17 is an existence statement and a trivial witness
  satisfies (A)–(G), so the *statement* is not refuted. The objects built in the *proof* can violate (G), so
  this is a real error in the proof, at N2141 and propagated to Claim 4.25. The main theorem is unaffected; the potential ŝ repairs
  the accounting. `redteam-canhyp.md` keeps its original wording; `verify-neu417.md` corrects it. The paper's
  Remark `rem:neu20`(3) is now a question to the author. The TALG version was not accessed.

### "λ coefficient halved" in Theorem R\*\*

* **Claim** ([w17-affine](../docs/w17-affine.md) Prop. G, §7): the Sylow trick halves the coefficient of λ in R\*\*.
* **Withdrawn** by [redteam-w17-affine](../docs/redteam-w17-affine.md) §5: R\*\* has one Λ and no tracked coefficient to halve.
  The per-node count |P|_{2′} is right, the composite row is plausible and unproven (actual row cost
  μ_{2′} + 2), and no statement about R\*\*'s constants is supported.

### "Flag method has hit its limit"

* **Claim** ([w17-affine](../docs/w17-affine.md)): Prop. B′ shows the bidirectional flag method is at its limit.
* **Withdrawn** by [redteam-w17-affine](../docs/redteam-w17-affine.md) §3: B′ is a generic birthday bound for
  equality-only access to opaque labels, and says nothing about algorithms that read the labels.

### Draft claims retracted inside memos

* "No faithful tree representation of degree < m" for product-type components: false, retracted in
  [w2-coset](../docs/w2-coset.md) §2.4 (A₅ ≀ C_m is a tree group of degree 5 in its imprimitive action).
* "Every family in §4.5–4.6 costs 2^{O(d)}N^{O(1)}" and "all decoupled families are polynomial"
  ([w1-structure](../docs/w1-structure.md)): false or unproved as worded. The correct list is in
  [redteam-w1-structure](../docs/redteam-w1-structure.md) §7.
* The bound "2^{O(k₀)} poly(d′)" for the twisted instance when Q ≠ 1: unsupported, same report §6.
* w1-structure Prop 4.4's "paid with Λ = O(1)" as a whole: the terminal instance contributes a global factor
  max|P| (same report §6).
* w10's "no black box at all": case (iv) still calls B–H on binary structures, so "no t-ary black box"
  ([redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §4.5, [w12-theoremg](../docs/w12-theoremg.md) §0).

## Found to be known

### Theorem P is Babai–Codenotti–Qiao 2012

[w2-coset](../docs/w2-coset.md) presented Theorem P (string isomorphism for any G ≤ Sym(Δ) ≀ S_k in product action) as a
new FPT ingredient. [redteam-w2-coset](../docs/redteam-w2-coset.md) §2 identifies its recurrence with
Babai–Codenotti–Qiao ICALP 2012 Thm 5 / Codenotti's thesis Thm 4.2.1 (twisted code equivalence), and the
arbitrary top group with one extra coset intersection on V. The memo w1-structure had already sketched this. What remains is the
arithmetic that the CI cost on b·log N points is f(b)N^{o(1)}. Relabel as a corollary. The same report also repairs
the base case (setwise transporters need one CI each) and improves the exponent from 3.17 to 2.33
(states are (1 + b²)^k, so N^{log_b(1+b²)}).

### The coordinate-tanglegram group is AMBC 2025

[w6-tanglegram](../docs/w6-tanglegram.md) Prop C, described as new to the agent's knowledge, is a special case of
Anagnostopoulou-Merkouri–Bailey–Cameron Theorem 4.24(a) (Forum Math. Sigma 2025), found in
[w8-poset](../docs/w8-poset.md) §0, §7.

### "c = 4 for all d" was already known

[w8-gnsexp](../docs/w8-gnsexp.md) counted c = 4 for all d as part of its gain. [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §4.3: this needs
no new lemma. It follows from the known n^{O(log d)} domain count (Grohe–Neuen survey Thm 4.16) and B–H.
Likewise "c = 3 for log n ≤ log^{1.5} d" is B–H alone. Lemma A lowers the exponent only when log n > log² d.
The honest headline: for d ≤ 2^{(log n)^{1/3}} the exponent drops from 4 to 3; the worst case over d stayed 4 until
Theorem X.

### Affine equivalence: "nothing better than brute force"

[moonshot-theory](../docs/moonshot-theory.md) §3.3 and later memos said no algorithm beats brute force for AGL(k,2) string isomorphism.
[w17-affine](../docs/w17-affine.md) §1: false as a statement about available techniques. The generic methods give 2^{k²/2+O(k)}
(Theorem A) and 2^{k²/4+O(k)} (Theorem B). No 2^{o(k²)} algorithm is known; the exponent changed only by a constant
factor. [redteam-w17-affine](../docs/redteam-w17-affine.md): Theorem A is folklore and B is a routine instance of Rosenbaum /
Le Gall–Rosenbaum; the "+k/2" carries no content because 2^{k/2} = N^{1/2} is absorbed by poly(N).

### The PG-fibration form of w30 is Jungnickel–Tonchev

[w30-sts](../docs/w30-sts.md) cited Jungnickel–Tonchev (arXiv:1709.06044) only for counts. [redteam-w30-sts](../docs/redteam-w30-sts.md) §5, reading its Thms 2.5 and 2.7–2.9, identifies them with w30's "general form" of §6 (one-factorizations and arbitrary Latin squares on lines) and the a = s + 1 branch of T1; the k = 3 gadget regime of T2 is D. Zinoviev (arXiv:1512.00187), and the character-space fact behind the classification is Assmus (ELJC 2, 1995). The cocycle description was already cited in w30 as not new. **What stands:** no reduction from Boolean-function, code or tensor equivalence to STS, quasigroup or design isomorphism was found; the red-team calls T2 "probably folklore-level, apparently not written". Treat T1, T2, T3 as "not found", not as new.

### Alternating tuple isometry in characteristic 2 (w35 E(i)) is Sun 2026

[w35-cubic](../docs/w35-cubic.md) E(i) gives alternating matrix tuple isometry over F₂ from Theorem A plus GIQS, with no prior-art search (the tools were at their limit). [redteam-w35-w34](../docs/redteam-w35-w34.md) §6: Sun, arXiv:2611.05920 (4 Nov 2026, unrefereed), Thm 2.1/A.1, gives alternating tuple isometry over Z/p^τ, including F₂, in p^{O(τ n^{7/4} log(τ n))}·poly(m). The tuple case of E(i) is not new as a statement; the two bounds are incomparable. Theorem A is folklore-adjacent. Theorem B and its composite with Theorem C appear new as far as that limited search could determine.

### Other novelty corrections

| Item | Correction | Source |
|---|---|---|
| Lemma T "to my knowledge new" | device credited to Wiebking's thesis Lemma 5.34 and BC's right descent; what may be new is its use at test-set size Θ(log d) | [redteam-w4-gnscanon](../docs/redteam-w4-gnscanon.md) §6 |
| Lemma A | a non-asymptotic variant of Pago arXiv:2302.05426 (Lemma `G_groupInduction`, primitive case credited to Wiebking) | [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §7 |
| Prop 3.3 of w1-fpt | an instance of Schweitzer–Wiebking and ADKT; ADKT Thms 5–6 give the small-faithful-degree remark too | [redteam-w1-fpt](../docs/redteam-w1-fpt.md) §2.4 |
| Prop L of w6 | probably folklore among permutation-group experts | [w6-tanglegram](../docs/w6-tanglegram.md) §2.1 |
| Theorem B of w17 | "possibly folklore", then routine (see above) | [overnight log](../docs/overnight-log.md) |
| Prop 1.3 of w10 | elementary; a 2-transitive group has two orbitals | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §2 |
| GN21 L1253 | w10 over-read it as naming the Design-Lemma option | same §6 |

## Gaps found in published work (questions to authors, not error claims)

### GNS Lemma 7.2

* The written proof asserts H′_(𝒞′) ≤ ker φ′ (v3, l. 2126) without justification. The algorithm lets the next round
  pick any minimal block system above 𝔅₁. For (S_m ≀ S₂) × C_q and x(a,b,c) = [a ∈ U], |U| ≈ 0.3m, the column system
  gives k′ = k, so the displayed k′ ≤ k − k/(3 log k) fails.
* Fix: take the next block system above 𝒞′. This is itself a legal run, so **the algorithm and the theorem are
  unaffected**; the running time is not shown to break.
* Status: confirmed by [redteam-gns-lemma72](../docs/redteam-gns-lemma72.md) and computed for m = 5–8. Numeric hypotheses: the red-team
  says m ≥ 180 with unrounded t; the paper uses t = max{9, 3 + ⌈log d⌉}, hence m ≥ 200. Both are consistent; the
  paper's rounding is the conservative one.
* The write-up's phrase "GNS's remark suggests this was intended" and "verbatim in Neuen" were over-readings
  (red-team §5). The "fewest blocks" reading of l. 2087 would avoid this example, but the text states no such rule.
* Present in all arXiv versions of GNS and Neuen 2020. **The SICOMP 2023 text was not accessible**; check it first.
  The paper poses this as a question, and the [cover note](../paper/cover-note.md) drafts it.

### Neuen 2020

See above for Thm 4.17(G). Also the giant-test order in the local certificates routine: the test must come
after BalanceOrbits; this affects only the cost proof ([w8-hypercanon](../docs/w8-hypercanon.md) §2.8).

### Minor slips in published text

* GNS L2324: |D_{i,j}| ≥ 3k/4 should be ≥ 3k/4 − 4; harmless.
* Babai arXiv v2 Thm 3.2.1 prints 2^{1+log₂ n} for n^{1+log₂ n}; a typo.
* HBD's "H is a pointwise stabilizer" (L1437, L1504) is imprecise at the contraction step; see
  [redteam-theoremg](../docs/redteam-theoremg.md) §1.3.

## Corrections to the project's own statements

### The ETH barrier

The statement "W[1]-hardness would need parameter blow-up ≥ 2^{k^Ω(1)}" was written "under ETH" in
w1-fpt, w2-coset, w4-t2 and w6-tanglegram. An unrefereed October 2026 preprint claims ETH is false. [w21-eth](../docs/w21-eth.md)
§B.3: the argument only ever used that k-Clique has no f(k)n^{o(k)} algorithm (CLIQUE-LB). ETH implies CLIQUE-LB, not
conversely, so the barrier survives if ETH fails. Notes were added to the five memos.
One unedited residue: the `w2-coset` entry in [overnight-log.md](../docs/overnight-log.md) still says "ETH forces".

### "SAT encoding of GI has at least n log n variables"

Said in discussion before w21. [w21-eth](../docs/w21-eth.md) §B.1: that is a statement about encodings whose assignments include every
bijection, not a lower bound on reductions. Natural fixed-width encodings have about n² variables, for which
2^{n²/√log n} is worse than n!. The theorem helps only if N ≲ log² n·√(log log n)/log log log n.

### Theorem R, and its verification

| Item | Correction | Source |
|---|---|---|
| Dispatcher (M) | ambiguous and wrong read with HJ's order test; replaced by the structural rule (M′) | [verify-theorem-R](../docs/verify-theorem-R.md) §4.0, [redteam](../docs/redteam-theorem-R.md) §9(b) |
| (H1) | not a hypothesis: holds, after replacing "Cameron-large" by GNS option 2 | [verify-theorem-R](../docs/verify-theorem-R.md) §2 |
| log log N term | removable via BCP/Maróti, giving R\* | same §4.4 |
| "m ≥ 300" for the overlap of HJ's exceptional range with option 2 | wrong; first overlap at m = 509 (t = 22), or m = 557 for t = ⌈√m⌉ | [redteam-theorem-R](../docs/redteam-theorem-R.md) §9(a) |
| Λ = log(4d̃) | use log(8d̃) to cover both readings of BCP | same §9(c) |
| "n^{O(log d)}" | should read n^{O(log(d+2))} | same §9(d) |
| Literature note on c | w1-fpt "c ≥ 4", red-team "c ≥ 3": replaced by the bookkeeping c = 5 of w8 (upper bound from the written proof) | [w8-gnsexp](../docs/w8-gnsexp.md) §1.3 |

### Speculation that HJ's σx channel is never tight

[moonshot-theory](../docs/moonshot-theory.md) §5 listed as speculation that the x² and σx channels are never tight, and §2.3 knew no instance. Theorem B1 of [w18-latin](../docs/w18-latin.md) (given HJ as written; AI red-teamed by [w26](../docs/redteam-w18-latin.md), asymptotic only) attains the σx channel on the PG(m−1,2) incidence graphs: "visible unaffected steps with polynomial-degree giants" occur there.

### Latin squares and HJ on graphs (w18, w26, w28)

[redteam-w18-latin](../docs/redteam-w18-latin.md) found no claim broken and corrected the items below. Two of them, the cutoff q₁ and the Latin-square-graph exponent (1/8), were applied to [w18-latin](../docs/w18-latin.md) in `w39` (its header says so). **The rest of the report's §5 has not been applied** (for example m ≥ m₀, the A1 repairs and the single-block rigid variant), so read the memo together with the red-team's §5. The last three rows come from [w28-sigma](../docs/w28-sigma.md), red-teamed by [w31](../docs/redteam-w27-w28.md).

| Item | Correction | Source |
|---|---|---|
| B1 enumeration cutoff | the cutoff is not q₀ but q₁, the largest degree accepted by HJ's enumeration test; q₁ = 486290 at Lean's parameters (a = 36000, q₀ = 2064), hence c about 86 at κ = 64. Asymptotics unchanged | [redteam-w18-latin](../docs/redteam-w18-latin.md) §2.4 |
| B1 hypotheses | needs m ≥ m₀(κ, a, N₀), and "fixed κ ≥ 5" must be read as a family of algorithms HJ_κ; it says nothing about automorphism-pruning or memoizing variants | same §2.4, §6 |
| B1 at feasible sizes | at κ = 64 the chain has no levels below m = 150 (n ≈ 2^297) and no nesting below m = 214 (n ≈ 2^425). It is an asymptotic statement about the recursion and says nothing about feasible inputs | same §2.5 |
| Lemma 1, V₃ step | the written argument needs κ ≥ 5 and is false at κ = 3, so the memo's κ = 3 simulations are not exact instances of Lemma 1 and "windows match Lemma 1 exactly" needs that caveat | same §2.2 |
| Theorem A1 proof | four repairs: chains must be extended strictly increasingly; exhausting Q′ before length d certifies non-isomorphism; the three-sorted closure sentence is false for degenerate triples (start each chain with a pair); the Latin-square-graph exponent is (1/8)log₂ N, not (1/4) | same §3 |
| Lemma A3 | wording: count or exclude ∅ (M ≥ 2^r vs 2^r − 1); "index" is a size ratio | same §3 |
| A1 novelty | "not found" stands, but it is a routine one-paragraph application of Rosenbaum's framework | same §3 |
| w18 §2.9 rigid variant | "switching a single block kills Aut" is false: the stabilizer of a line in GL(m,2) still has order 2^{m²−O(m)}. A corrected variant X_{m,R} deletes O(m) lines. Status of the correction: proven in the memo, found sound by the w31 red-team | [w28-sigma](../docs/w28-sigma.md) §8, [redteam](../docs/redteam-w27-w28.md) §8 |
| w18 §2.9: "pruning collapses the chain" | true about the chain only: without also pruning HJ's Case 2b branches, q^{O(1)} continuation branches remain per cap contraction and the tree is again 2^{Ω(m²)} (P2, a sketch; the red-team does not certify it) | same §4 |
| w18 lead: canonically chosen test sets | on X_m any Aut-invariant rule selects all independent T or none (C1), so no sparse canonical family exists there; the lead is revised, not settled | same §5 |

### Height-2 posets and R1_c (w27, w31)

[redteam-w27-w28](../docs/redteam-w27-w28.md) found no claim broken and narrowed or fixed the items below. [w27-tree](../docs/w27-tree.md) was not edited afterwards, so its text still has them; these rows are what the project now claims.

| Item | Correction | Source |
|---|---|---|
| Theorem G "FPT on three sub-classes" (w27 §0) | The cost (b!·b^m)^ρ · b!·2^{O(b)}·N^{O(1)} is correct, but (b^m)^ρ = N^{Θ(ρ)}, so Theorem G is **XP in ρ**: FPT in b for constant ρ (the ρ = 1 case is what w27 uses), not FPT in (b, ρ). The same holds for G+ in ρ; G+ is FPT in r | [redteam](../docs/redteam-w27-w28.md) §2 |
| Cor N.1 scope | sound as stated, narrower than advertised. It uses Aut-reflection only at identity tanglegrams, which are trees, polynomial, and could be special-cased by a reduction. The sharp form is pointwise: if φ reflects at x, then td(Aut(x)) ≤ ℓ·D(f(b₀)) | same §1, §9 |
| "Every reduction in the campaign is Aut-reflecting" | unsupported as worded: true for the reductions from R1_c in T2 Theorem A and W8 Prop H (with the caveat that a CI instance has an "Aut" only once one declares it the group of the answer coset). The campaign has reductions that are not many-one at all | same §1 |
| "Hardness … is impossible, so the question reduces to the FPT side"; "W8's alternative hypothesis survives" (w27 §0, §2.1) | not established. Non-reflecting reductions cannot be excluded this way. What holds: a hardness proof for height-2 posets cannot be of the gadget kind used so far | same §1 |
| Theorem C citation | Luks 1982 alone gives m_P^{O(b)}, i.e. XP. The absolute exponent needs Pálfy–Wolf (cited from memory), and the memo must name it | same §2 |
| Theorem C, the set R | the algorithm must know R. (b!)^{r+2}·N^{O(1)} is for a given R; if R must be searched for, the result is FPT in (b, r) with an extra r^{O(r)} | same §2 |
| Lemma 3.1 "for every code" | a zero column or a weight-1 row leaves a side with no leaf in L₁, so that pair does not straddle (the one failure of 34/35). Fix: a dedicated L₁ leaf per side under a rigid pad, or restrict to H with no zero column and no weight-1 row (still 2^{Ω(s²)} codes) | same §4 |
| Lemma MD "pays 2^{Ω(b^{m+1})}" (w27 §4) | wording: it bounds the orbit size available, so the 2^{O(orbit)} upper bound becomes useless; it does not say any algorithm must spend that | same §3 |

### The σ channel (w28, w31)

Same report, which found no claim broken. [w28-sigma](../docs/w28-sigma.md) was not edited afterwards.

| Item | Correction | Source |
|---|---|---|
| LHJ boundary (w28 §5.1 step 3) | "≤ ¾" should be "< ¾": HJ's hypothesis is "fewer than α times" with α = 3/4. Escalate on ≥ ¾ | [redteam](../docs/redteam-w27-w28.md) §5 |
| P3 | labelled proven, but the existence of R rested on the union bound w28 itself labels a sketch. Repaired by an explicit R (m ≥ 3κ, \|R\| = O(κ²), independent of m), built from an asymmetric graph on 2κ further basis vectors | same §6 |
| L2 "the B1 chain never starts" | a statement about the root; the "every chain state" half only matters if such a state arises by another route. The whole-tree claim stays a sketch | same §5 |
| M1 "saves only n^{O_κ(1)}" | compares to B1's lower-bound product. Clean form: the table of distinct exact states has at least ∏_{i<j} binom(r_i, κ)₂ entries at level j | same §6 |
| R1 error term | "O(log log n)" is loose; O_κ(1) suffices | same §8 |
| Theorem U | "product state" should say that the first window being B × T is part of the hypothesis; §7.2's s^{2/κ} is exact for even κ, odd κ gives s^{2/(κ−1)} | same §7 |

### Steiner triple systems (w30, w33)

[redteam-w30-sts](../docs/redteam-w30-sts.md) found no break. [w30-sts](../docs/w30-sts.md) was not edited afterwards, so its text still has the items below.

| Item | Correction | Source |
|---|---|---|
| T1 constant | the proof works for λ < (log₂10)/3 ≈ 1.1073, not only (log₂9)/3, because m_W ≡ 1, 3 (mod 6). So r > 0.9031ℓ (not 0.947) suffices, d ≥ r − 9.32c (not 17.7c), and d ≥ (1 − 10.3ε)ℓ with \|S\| ≤ n^{10.3ε} (not 18.7). The threshold is sharp at AG(2,3) | [redteam](../docs/redteam-w30-sts.md) §2.3 |
| "The hardest instances are recognisably PG-fibred"; "no method can avoid the GL part"; "exactly the barrier" (w30 §0, §6) | overclaims, not made here (the memo's text still has them). T2 is the implication n^{o(log n)} ⇒ 2^{o(d²)} and nothing more; nothing shows these are the hardest instances. On the T2 family the problem is polynomially equivalent to linear equivalence and easier than the general bound: 2^{d²/4+O(d)}·poly(n), given w17 Theorem B | same §1.5 |
| T2: extra maps from the gauge | isomorphisms do not biject with linear equivalences; they surject onto them with kernel K = Hom(V/⟨supp χ⟩, Z). The reduction is unaffected. w30's "nauty stalls" applies only to the uncoloured graph | same §1.3, §1.4 |
| Latin-square isotopy (w30 §9) | a sketch; replaced by the red-team's Prop A, with the extra gadget condition (c) | same §1.6 |
| Prop 2 (C4) | correct as a statement about the Steiner loop L_g, not as written for the Steiner quasigroup, for which PG already fails w18's definition | same §4.1 |
| T3 | at d = 3 the conclusion is a projective plane of order q, not necessarily PG(2,q). The second term of λ_q can be raised | same §3.1 |
| T5 | add a sentence rejecting X′ that does not decode to a projective structure within D | same §3.2 |

### Conference graphs and cubics (w34, w35, w37)

[redteam-w35-w34](../docs/redteam-w35-w34.md) found no break in either memo. Neither memo was edited afterwards. [w32-conference](../docs/w32-conference.md) was red-teamed later by [redteam-w32-conference](../docs/redteam-w32-conference.md); see the table below.

| Item | Correction | Source |
|---|---|---|
| Thm 3.2 of w34 | say r ≥ 1: at r = 0 no separation occurs and the statement is empty | [redteam](../docs/redteam-w35-w34.md) §7 |
| Prop 4.2 of w34 | two notational slips: "P_B ≥ binom(\|B\|,2)⁻¹" conflates the ordered fraction with p₂, and "equivalently d(τ) ≥ ¼ log_v(1/τ) − O(1)" holds only for τ in range. The stated conclusion stands | same §7 |
| E2 of w34 | should read O(√(A log n) + 1), and assumes log₂(1/τ) in range | same §7 |
| w35 §1.2 obstacle instance | valid, but not specific to characteristic 2 (it fails over F₃ too, as w35 notes). The report gives an instance that is, over R = F₂[ε]/(ε²) | same §5 |
| GIQS Thm 4.9, Step 3 (a defect in the preprint, not in w35) | the running-time overclaim w35 flagged is confirmed; w35's repair is correct, and shorter than it says. Thm 1.2's bound is unaffected once repaired; GIQS's other proofs were not re-verified | same §4 |
| IMQSZ Prop 4.9 in w35's table row O | the row cites it as part of the obstacle while the text treats that step as fine. The text is right: its proof uses no division by 2 | same §5 |

### Status of the Lean formalization

The memo [moonshot-theory](../docs/moonshot-theory.md) (Nov 4) describes the Lean as a "stage 1" formalization with subroutines as
hypotheses, and `RunningTime.lean` L9 says Sections 4–6 are not formalized. These were superseded: the final
`main_theorem` takes no such hypotheses, and building and comparator confirm it (see [Lean audit](Lean-Audit.md)). Separately, the string
theorem 1.2 really is only at "stage 1"; only GI is verified at machine level ([w10-blackbox](../docs/w10-blackbox.md) §2.1).
Also: the "main residual risk" named in round 4 was HJ's σ-budget; it is now machine-checked modulo the axioms.

The earlier statement that nothing of the project's own accounting is machine-checked is superseded in part by [w36-lean](../docs/w36-lean.md): `lean/DegreeD` machine-checks the abstract Λ bound, its recurrence, the (H2) regrouping on the real scripts, and the real-run bound under explicit hypotheses, with only the three standard axioms. For d < N nothing yet shows the required `Good` runs exist, so the n^{O(log d)} theorem itself is still conditional and hand-argued there. See [Lean audit](Lean-Audit.md#the-degree-d-accounting-in-lean-w36).

### Canonization write-ups

| Item | Correction | Source |
|---|---|---|
| Blank symbol in windowed strings | must be fresh (β ∉ Σ); handled by explicit tags in the write-up | [redteam-w4-gnscanon](../docs/redteam-w4-gnscanon.md) §2.3 |
| Lemma F1 / Lemma 5.1 "right subgroup" | stated wrongly; fixed | [redteam-canonization-writeup](../docs/redteam-canonization-writeup.md) §6 |
| §10 assumptions | four missing, chiefly determinism and canonical generators for every subroutine feeding a (P1) choice, including BC | same §4 |
| Write-up §9.2: treewidth needs canonical Neuen | wrong; treewidth needs only Theorem A (`cosetHyper` is applied once, to a hyperedge-respecting coset) | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md) §0, [w8-hypercanon](../docs/w8-hypercanon.md) §3.3 |
| Theorem TW | labelled proven mod; relabelled **sketch**; fixes TW-1 (χ step), TW-2 (mark S), TW-3 (degeneracy check) | [redteam-w8-hypercanon](../docs/redteam-w8-hypercanon.md) §3 |
| Theorem H "correctness proved" | overstated (no written algorithm); §10.9 CanHyp was added and red-teamed; status unchanged: correctness proof modulo §13, time a sketch | [referee](../docs/referee-canon-paper.md) M1, [redteam-canhyp](../docs/redteam-canhyp.md) |
| Babai's STOC 2019 dependency | hidden at headline level; surfaced in abstract and Table 1. The referee's "only graph canonization on ≤ d points" held only in part: BC is called on t-ary structures under A_k/S_k, k ≤ d | [referee](../docs/referee-canon-paper.md) M2, [overnight log](../docs/overnight-log.md) wave 12 |
| Citations | 7 of about 120 fixed | [referee](../docs/referee-canon-paper.md) §5 |

### Exponent memos

| Item | Correction | Source |
|---|---|---|
| Lemma A | hypothesis m ≥ 16; exact threshold m ≥ 6; fails at m = 5, k = 6 (PSL(2,5), PGL(2,5)); "CFSG-free" refers to the lemma only | [redteam-w8-gnsexp](../docs/redteam-w8-gnsexp.md) §2 |
| Corollary F | "not on the CFSG lemma" must add "still CFSG-dependent via GNS 3.13" | same §6 |
| Theorem X framing | c = 3 for d ≥ 2^{(log n)^{2/3}} is B–H alone; gain confined to 5/3 < x < 3 | [redteam-w10-blackbox](../docs/redteam-w10-blackbox.md) §1.5 |
| Split-or-Johnson individualization count | "O(log m) points" wrong; at most O(log² m) (w12), in fact O(log^{3/2} m) (w15) | [w12-theoremg](../docs/w12-theoremg.md) §9, [redteam-theoremg](../docs/redteam-theoremg.md) §1.2 |
| Reading of HBD Split-or-Johnson | "reads one point of Γ" false at contraction: streams read elements of the current V₂ (possibly blocks) | [redteam-theoremg](../docs/redteam-theoremg.md) §1.3 |
| "Legal run of GNS" (Theorem G) | slightly too strong: G2 tests the inserted top | same §3 |
| Theorem G regimes | improvement exactly on 3/2 < x < 2 (x = 3/2 not new); "min(log³ d, log² n)" needs B–H | same §5 |
| Check script cost | memo said about 2 s; took over 2 minutes at nice 19 | same header |

### Core-problem memos

| Item | Correction | Source |
|---|---|---|
| w1-fpt Prop 4.1 | Aut(B) := Iso(B,B) is not a group; needs an x→x table | [redteam-w1-fpt](../docs/redteam-w1-fpt.md) §3.1 |
| w1-fpt Prop 4.2 | virtual root fails for intransitive tree groups; run the DP on the given tree | same §4.1 |
| w1-fpt "every size N" | only suitable m; "c ≥ 4" wording | same §1.6, §5 |
| w1-structure Lemma 4.3 | "≥ N/(dL)" false; correct bound N/((d+1)L) | [redteam-w1-structure](../docs/redteam-w1-structure.md) §5.3 |
| w1-structure "closed under sections" | false for the composition-factor class; use aw and section-closed λ | same §1.4, §2.2 |
| w1-structure Theorem L coset version | missed Aut_R(x); repaired, now proven modulo S-W | same §4.3 |
| w2 Cor 2.2 | full-diagonal PCI in DPs is SI on one child; the hard shape is a diagonal on a full-depth direct factor | [redteam-w2-coset](../docs/redteam-w2-coset.md) §3.3 |
| w2 Example X "ε = 1" | overstated: level 2 can stay coupled, ε_root ≤ \|GL(r,2)\|^{2^{r−1}}; FPT conclusion stands | same §5 |
| w2 Theorem P's exponent and base case | see above | same §1 |

### Moonshot and affine memos

| Item | Correction | Source |
|---|---|---|
| Theorem C (w17) displayed Iso set | wrong direction: it is Iso(c_T′, c_T) | [redteam-w17-affine](../docs/redteam-w17-affine.md) §4 |
| Prop B′ bound | true bound Ω(2^{k²/4+k/4}) | same §3 |
| Theorem B parabolic | a 3- or 4-block parabolic reaches 2^{k²/4+k/4} at a cost in space; harmless | same §2.4 |

### Benchmarks and software

| Item | Correction | Source |
|---|---|---|
| `3reg12-pair` mislabeled | random cubic graphs from seeds 5 and 6 are isomorphic; the solver's answer was right and the benchmark's WRONG was wrong. Fixed (seeds 5 and 7); non-isomorphism labels now verified by networkx or a cited theorem | commit `9180532`, [bench/families.py](../bench/families.py) |
| Baseline "14/29" | counts the mislabeled pair as correct; the raw JSON shows 13 ok, 1 WRONG, 15 timeouts | [bench/results/baseline-nocert.json](../bench/results/baseline-nocert.json) |
| Timed individualization budget | changed output on 7 of 56 instances under simulated preemption; replaced by a counted budget | [README](../README.md), commit `4d47f55` |
| Hypercube regression in `class_plan` | class layers made Q8 > 200 s; plan now falls back to BFS on a twin block ≥ 3 | [w1-scale](../docs/w1-scale.md) §1.6 |
| `gi.canon` | no polynomial guarantee at d ≤ 5; solvable layers not done | [w14-solver](../docs/w14-solver.md) |
| w14 profiles and slowdowns | corrected against measurements in `ef6f8ab` | [w14-solver](../docs/w14-solver.md) |
| README table of canonical times | README's "CFI n = 3200 … 13 s" was w9; w14 reached 1.41 s and w23 0.43 s for canonical forms, and the README now says so. Later numbers in [Benchmarks](Benchmarks.md) win | [README](../README.md), [w23-speed2](../docs/w23-speed2.md) §3 |
| "The kernel does not help bounded or canonical paths" (1.00–1.15×) | true of w16, when that code was off limits; w23 compiled it | [w16-ckernel](../docs/w16-ckernel.md), [w23-speed2](../docs/w23-speed2.md) §2–3 |
| w32 "p reaches 0.28 at n = 6561", "0.24 at 625", "33057 pairs p ≥ 0.2" | S = 300 sampling artefacts. Exact maxima are 0.1867 and 0.1597, and no pair reaches 0.2 (at 6561, the top 200 pairs exact, the rest estimated ≤ 0.058) | [redteam-w32-conference](../docs/redteam-w32-conference.md) |
| w32 "all available" Spence graphs; "only P(25), P(49) have depth 3" | a sample (30/412 at n = 49, 50/1022 at 45, 16/106 at 41, 400/6760 at 37); P*(49) also has depth 3 | same |
| w32 "structure must include tensor products" | does not follow from Thm 4.2, which gives only bounded B_c cliques; the report's Prop R1 gives cliques of size n^{0.23c} | same |
| Traces gaps at w14 (CFI 10–23×, Miyazaki 30–90×, Q12 about 250×, 3-regular about 13×) | narrowed by w23 to about 7×, 23×, 14–29× and 3–6×; Traces is still ahead on every family except multipedes | [w23-speed2](../docs/w23-speed2.md) §3, §6 |

### Lean statements, the small-degree guarantee and quartics (w42, w44, w46)

| Item | Correction | Source |
|---|---|---|
| `graphIso_final`, `graphIso_general`, `graphIso_connected` | vacuous as stated: a zero-call script satisfies them with C = 0. Withdrawn as evidence, renamed `*_weak`, and replaced by `graphIso_reduction` (w43) | [w42](../docs/w42-lean-supply.md), [Lean audit](Lean-Audit.md#stage-1-in-lean-and-a-vacuous-statement-w38-w41-w42) |
| w40 Theorem A, "polynomial when twin blocks ≤ 4" | false as stated for unbounded degree; needs d fixed. Sound at every fixed d ≤ 5 | [redteam-w40-solvable](../docs/redteam-w40-solvable.md) |
| w40 exponent | 3.2439 should be 3.244. "About 53" is an estimate, because g(m) = m⁶ is asserted | same |
| w40 §2.1, "true worst case is Schreier–Sims" | false | same |
| Theorem H threshold, "s ≥ 128" and "s > 128" | "s ≥ 128" is false. Printed parameters first win at s = 132; "s > 128" holds only with R = 8 chosen by hand at s = 130 | [redteam-w45-quartic](../docs/redteam-w45-quartic.md) §1 |
| w45 blow-up claim, "any kernel reduction" | holds for time bounds in L alone, single field, one-input reductions | same §2 |
| T3′ of w45 | needs f_i(0) = 0 | same |
| arXiv:2604.00591 as described in w45 | its 4-tensor algorithm is not "via eigenvalue-free slices" | same §7 |

### HJ's enumeration channel (w47, w48)

| Item | Correction | Source |
|---|---|---|
| Theorem C of w47 | broken as stated: O5 omits HJ's Case 1 and imprimitive partition overcosets, which are wreath products (K_a⊔K_a exposes Sym(a)≀C₂ in product action, degree a²). Repairable by widening O5 and "Young"; the bounded-order conclusion is then checked by hand only, and the wreath block-system classification is missing | [redteam-w47-mu](../docs/redteam-w47-mu.md) |
| Corollary to Theorem C | false as worded; say "superconstant order" | same |
| Theorem A wording, "2-subspaces, d ≈ n/16" | holds only for a coordinate top partition, which is what the Lean selects. At m = 7 the unordered-pair tower acts on 31 hyperplanes. N = n² | same |
| A′ of w47 | gave no test set; use the lines ⟨e_i,**1**⟩ | same |
| Prop D of w47, "removable on X_m", "same status as B1" | Prop D covers one node only, and w28's P2 is a sketch | same |
| Theorem P of w49, "any automorphism pruning" | broken: two-sided pruning leaves one child per double coset Sp\\GL/Sp, polynomial in N. Holds only for left-only pruning | [redteam-w49-pruned](../docs/redteam-w49-pruned.md) |
| Theorem T of w49 | holds for a resolution whose Case 2b orbital is R₁; the Lean fixes this by label order, so it is a worst-case labelling. d must be even, n ≥ 2^33280 | same |
| w47 §5.3 conjecture | false as literally worded; the two-sided form is not refuted | same |

### Gain-graph core (w50, w53)

| Item | Correction | Source |
|---|---|---|
| "H non-enumerable", "non-abelian gains on the family open" | H is tiny and \|C\| = N^{Θ(log log b)}: every gain problem on the family takes f(b)·N^{O(log log b)} | [redteam-w50-gain](../docs/redteam-w50-gain.md) |
| Cor E.1 "on the Theorem-B family" | proved for folded cubes only | same |
| "narrow generation holds exactly when kernels are 2-transitive" | false (S₆ on pairs); 2-transitivity suffices | same |
| double-cover remark | ⌈g/2⌉ values per side-coordinate suffice, not g | same |
| Theorem A constant 4 | improves to 3, optimal | same |

### The video

Fact-checked by `w24-video-review` (`4085217`, merged `6dad6a2`), which fixed 31 errors (10 wrong, 12 misleading, 9 minor) in the narration, cards and code; [REVIEW.md](../video/REVIEW.md) lists each with its source, and what could not be verified. Running time 65:31. Differences between planning documents and data, as of `b1a2d03` (not changed by the fact-check, which left STORYBOARD.md alone):
[STORYBOARD.md](../video/STORYBOARD.md) still says CFI over K₄ has 28 vertices and the window run uses Alt(5); [CLAIMS.md](../video/CLAIMS.md), generated from the code, says 40 vertices (16 middle, 24 edge-end) and Alt(7) on 21 pairs. CLAIMS.md is the later, computed record.

### Cross-document inconsistencies resolved when the paper was assembled

The agent writing [canon.tex](../paper/canon.tex) reconciled 9 such items, always keeping the more conservative statement, for
example: TW is a sketch; the counterexample needs m ≥ 200; "beats BC" is claimed only for k = polylog n
([overnight log](../docs/overnight-log.md), w9-paper).
