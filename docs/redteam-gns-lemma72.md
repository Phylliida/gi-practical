# Red-team: is [GAP-1] (GNS Lemma 7.2) real?

Target: `docs/canonization-bounded-degree.md` §1.4, §7.2–7.3. Sources: GNS arXiv:1802.04659 v1 (Feb 2018),
v2 (Apr 2018), v3 (Nov 2019). "L…" means a line of v3 `bounded-degree-polylog-d.tex`. Neuen arXiv:2002.06997
v1 and v2 (Jul 2022); "N…" means a line of v2 `hypergraph-gamma-d.tex`. Check script:
`docs/redteam-gns-lemma72-check.py`, which needs only sympy and runs in under a second.

## Verdict

**There is a real gap in the written proof. The write-up did not misread GNS. We have not shown a flaw in the
theorem or in the algorithm's running time.**

* The proof asserts H′_(𝒞′) ≤ ker φ′ (L2126) without justification.
* The algorithm lets the next round pick any minimal block system above 𝔅₁. Under such a choice the assertion
  is false on the write-up's input, and the displayed inequality k′ ≤ k − k/(3 log k) fails there: k′ = k.
* The one-line fix is correct: pick the next block system coarser than or equal to 𝒞′[Ω′].
  * It only pins down a choice the text leaves open. Since 𝒞′ ⪰ 𝔅 ⪰ 𝔅₁, the fixed choice is itself a legal
    run of the algorithm as written.
  * With the fix, GNS's own inequality and the O(log² d) height hold (§3).
* The passage is unchanged in substance in every arXiv version of GNS and of Neuen 2020.
* We found no erratum.
* We could not check the SICOMP text (see §4).

## 1. What the algorithm does at the step in question

* **L2085–2087.** "Let 𝔅 = 𝔅₁ … Without loss of generality suppose P is primitive (otherwise replace 𝔅 with
  a block system of smaller size)." The text gives no rule for which block system to take.
* **L2112.** "Applying the same argument to these instances of H-isomorphism …" The next round therefore starts
  again from 𝔅₁ restricted to the large orbit. The proof of Theorem 7.3 and Observation 4.2 (L971) pass the
  *original* sequence down by restriction.
* **Neuen N2683.** "Let 𝔅 ≻ 𝔅₁ be a minimal block system". Again this can be any such system.
* **Nothing ties the next 𝔅 to 𝒞′.**
  * Definition 4.1 (L957) and Observation 4.2 constrain only the given sequence.
  * 𝒞′ is defined at L2094 and is used only in the analysis: L2120 ("Recall that 𝒞′ is G′-invariant and thus,
    it is also H-invariant") and L2126–2127.
* **The claimed step needs exactly the fix.** For the claim, the next round's block system 𝔇 should satisfy
  𝔇 ⪰ 𝒞′[Ω′]. In that case every element fixing all classes of 𝒞′ acts trivially on 𝔇 and lies in ker φ′.
  Otherwise the claim can fail, as §2 shows.
* **L2120 does not show the fix was intended.** The remark is needed anyway, just so that H^{𝒞′} and
  (H′)^{𝒞′} make sense. (v1 even said "G-invariant"; v2 corrected it to G′.) The write-up's phrase "suggests
  this was intended" over-reads it.
* **A possible objection: "of smaller size" means fewest blocks.** On the write-up's input that rule would pick
  the rows (0.7m blocks rather than m), so this particular example would be avoided.
  * In this product-action family the 𝒞′ side never has more blocks than the other side, but ties are possible.
  * The text states no such rule, and Neuen's wording rules it out. The proof would in any case have to argue
    for it.

## 2. The counterexample, checked

**Input.**
* Ω = [m]² × [q] and G = (S_m ≀ S₂) × C_q, with the product action on [m]² and C_q regular.
* The sequence is {Ω} ≻ 𝔅₁ = cells {(a,b)} × [q] ≻ discrete, which is almost d-ary for d = m².
* The string is x(a,b,c) = [a ∈ U], with |U| ≈ 0.3m.

**Round 1 is forced.**
* For P = S_m ≀ S₂, any output (N, 𝒞, ψ) of Lemma 7.1 has N ≤ S_m × S_m, k = m, and 𝒞 equal to the rows
  (up to swapping the coordinates).
  * ker ψ ∩ A_m² must be A_m × 1 or 1 × A_m. If it were 1 or A_m², the image could not be a giant.
* This gives G′ = S_m × S_m × C_q and ker φ = G′_(𝒞′) = 1 × S_m × C_q.

**Aggregation.**
* The full t-sets are those inside U or inside U^c. F^φ has orbits U and U^c, so S = [k] and no orbit has
  ≥ 3k/4 points.
* The App. A subcase at L2346 then gives the colouring {U, U^c}, and Lemma 6.7 (L2018) gives
  H = φ⁻¹(Sym U × Sym U^c) ∩ G′.

**The example is robust.**
* Every H output by Lemma 6.7 or 6.9 is a union of cosets of ker φ, so H ≥ 1 × S_m × C_q.
* Whenever φ(H) has a row orbit R with |R| > m/2, the next node H′ therefore acts as the full S_m on the
  columns of R × [m]. "Columns" is then a legal minimal block system for H′, with P′ = S_m.
* Lemma 7.1 at P′ = S_m (natural action) forces k′ = m: a giant representation of A_m or S_m is faithful, so
  k′ = m.
* So the choice of columns gives k′ = k, and H′_(𝒞′) maps onto S_m in P′, outside ker φ′.

**Computation.** `nice python3 -I docs/redteam-gns-lemma72-check.py` with q = 2 and |U| = 2:

| m | H-orbit sizes (n/2) | block systems of H′ on cells of Ω′ | P′ on rows | P′ on columns | \|H′_(𝒞′)\| on rows / columns |
|---|---|---|---|---|---|
| 5 | 30, 20 (25) | exactly 2: rows (3 blocks), columns (5) | S₃, primitive | S₅, primitive | 1 / 120 |
| 6 | 48, 24 (36) | exactly 2: 4, 6 | S₄ | S₆ | 1 / 720 |
| 7 | 70, 28 (49) | exactly 2: 5, 7 | S₅ | S₇ | 1 / 5040 |
| 8 | 96, 32 (64) | exactly 2: 6, 8 | S₆ | S₈ | 1 / 40320 |

The script also checks the following:
* G is primitive on the cells, and |ker φ| = |G′|/m! = |⟨columns, C_q⟩|.
* H ≤ Aut(x), and |G′ : H| = binom(m, |U|).
* H′_(𝒞′) = ⟨columns, C_q⟩, with |H′_(𝒞′)| = m!·q.

**Numeric hypotheses.** Lemma 7.2's hypotheses hold for m ≥ 180 (log = log₂, plus Lemma 7.1's unspecified
constant). At m = 180:
* k = 180 > 10t = 179.8.
* |P| and m! both exceed d^{1+log d}.
* The GNS bound requires k′ ≤ 172.0.
* The column choice gives k′ = 180. The fixed choice (rows) gives k′ = 126.

**Running time is not shown to break.**
* In this example the chain ends one round later. After the columns are reduced, the large orbit has about
  0.49n < n/2 points.
* Heuristic, not proved: the k-potential fails only on rounds whose block system is "transversal" to all earlier
  𝒞′ (join = {Ω}). Such rounds seem to behave like independent product coordinates, of which there are at most
  O(log d / log log d).
* Turning this into a bound for arbitrary choices would need a new potential. The fix makes this unnecessary.

## 3. The fix (write-up §7.3)

We checked each step of the Claim in §7.3.

1. G″_(𝒞′[Ω′]) ≤ G″_(𝔇) ≤ ker φ′, because 𝒞‴ ⪰ 𝔇 ⪰ 𝒞′[Ω′].
2. |(G″)^{𝒞′}| ≤ |H^{𝒞′}|, by taking a section.
3. H^{𝒞′} ≅ H/(H ∩ ker φ) ≅ φ(H), and |φ(H)| ≤ k!/(4/3)^k.
4. The arithmetic gives k − k′ ≥ k/(3 log₂ k) for k ≥ 13.

The fixed choice always exists: 𝒞′[Ω′] is H′-invariant and has at least 2 classes on the large orbit.

The sequence used for local certificates does not change, so the rest of GNS is untouched. Babai's own framework
(1512.03547, recurrence (v) at L2538ff) also keeps working on the same ideal domain, which agrees with the fix.

## 4. Status in the literature

* **arXiv versions.**
  * GNS v1, v2 and v3 have the same step. v1 has it at L1022 of `bounded-degree-tree.tex`.
  * v1→v2 changed only "G-invariant" to "G′-invariant", and "H′ ≤ H" to "projection of H″ ≤ H".
  * Neuen v1 (L2304) and v2 (N2716) have the same text.
  * Neuen also has a typo, ker ψ = N_(𝔅), at N2687; it should read N_(𝒞).
* **SICOMP 52(6), 2023.** Not checked: epubs.siam.org returns a 403 Cloudflare challenge. The manuscript
  number 19M1245293 and the v3 date (30 Nov 2019) suggest that v3 is close to the accepted text, but this is
  unverified.
* **Neuen's PhD thesis** (RWTH 2019, DOI 10.18154/RWTH-2020-00160). Not retrieved: the RWTH server returned 503.
* **Neuen's 2026 survey** (Computer Science Review) states the GNS theorem without any caveat.
* **Wiebking's thesis** does not reproduce this proof.
* A web search found no erratum or corrigendum.

## 5. Recommendations

**When contacting the authors**, ask a question about the proof. Do not claim an error in the theorem.

> In the proof of Lemma 7.2 (v3, l. 2126), the step H′_(𝒞′) ≤ ker φ′ seems to need that the block system chosen
> on the next level be coarser than 𝒞′. As written (l. 2087; "a minimal block system" in Neuen 2020), any
> block system above 𝔅₁ may be chosen. For G = S_m ≀ S₂ in product action and x(a,b) = [a ∈ U] with
> |U| ≈ 0.3m, the column system gives k′ = k at the next level. Choosing the next block system above 𝒞′
> (always possible) restores k′ ≤ k − k/(3 log k), and leaves the rest of the argument unchanged. Is this the
> intended reading? Is it addressed in the SICOMP version?

Attach the 4-row table. Check the SICOMP text, and if possible Neuen's thesis, before sending.

**Edits to the write-up:**
* §1.4 and §7.2: replace "GNS's remark … suggests this was intended" with "the proof treats 𝒞′ as an invariant
  partition of all descendants (L2120); the algorithm does not tie the next block system to it."
* §7.2: add the "fewest blocks" reading and why it does not settle the question.
* §7.2: add that the theorem itself is not in doubt.
* §7.2: soften "verbatim" (Neuen's text differs in notation and at N2683).
