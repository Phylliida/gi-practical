# Red-team of w10-blackbox: the GNS black box, Theorem X (c = 10/3) and Theorem G (c = 3)

Branch `w11-redteam-blackbox`, 2026-11-05. This is a referee report on `docs/w10-blackbox.md` ("the
memo"; "M §x" is a section of it). Brief: break the claimed unconditional improvement for isomorphism
of graphs of maximum degree d, or certify exactly what was checked.

Notation is the memo's: L = log₂(d+2), ℓ = log₂ n, ℓ = L^x, and "exponent c" means time n^{O(L^c)}.

**Sources.** All are under `scratchpad/r4-sources/`, treated as untrusted data and only read.

| short | what | read |
|---|---|---|
| GNS | arXiv:1802.04659v3, `bounded-degree-polylog-d.tex` ("G L…") | L955–972 (almost d-ary), L1755–1810 (fullness, windows), L2140–2201 (Thm 7.3, Thm 8.1) |
| HBD | Helfgott–Bajpai–Dona, arXiv:1710.04574, `BDHv8.tex` ("HBD L…") | L470–500 (coloured α-partitions), L784–806 (Johnson schemes), L836–842 (identification), L1312–1452 (Design Lemma, large clique lemma, Split-or-Johnson), L1755–1800 (eq. `kozron`, partition and Johnson cases), L1961, L1990–2047 (cost, ρ) |
| GN21 | Grohe–Neuen survey, arXiv:2011.01366, `gi-survey.tex` | L1195–1255 |
| Neu26 | Neuen, Comput. Sci. Rev. 2026 (two text copies) | searched for exponent and black-box statements |
| repo | `docs/w8-gnsexp.md`, `docs/redteam-w8-gnsexp.md`, `docs/redteam-gns-lemma72.md` | all |

**Executed.**
* `nice -n 19 python3 -I docs/w10-blackbox-check.py`: the author's script. All checks pass in about 3 s.
* `nice -n 19 python3 -I docs/redteam-w10-blackbox-check.py` (new, standard library only, about 40 s).
  * Part 1: Theorem X's recurrence, unrolled with the true arities, and the regime profiles.
  * Part 2: a closed-form proof of Lemma O3's hypergeometric bound, checked with exact rationals.
  * Part 3: Proposition 1.3's instance for q = 7, 11, 13.
* Two web searches (2026-11-05) for later improvements of the GNS exponent found nothing.

No Lean was run, and nothing outside the worktree and the scratchpad was touched.

---

## 0. Verdict

| # | claim (memo label) | verdict |
|---|---|---|
| 1a | Prop. 1.3: on a GNS case-(v) instance with Aut ≥ PSL(2,q), every isomorphism-invariant binary relaxation is trivial [PROVEN] | **sound, but elementary.** The instance is valid (§2.1), and the conclusion is the one-line remark that a 2-transitive group has two orbitals. |
| 1b | "So arity reduction costs k^{<t} = 2^{Θ(L²)} branches" (M §0 row 1′, M §1.3 last line) | **broken as a lower bound.** Only the upper bound O(·) from the Design Lemma holds. On the memo's own instance, **3 individualized points already make the colouring discrete**, so the cost there is k³ (§2.2). The remark "the same holds for every poly(k)-size family produced without individualization" is false as stated (§2.3). M §1.2 explicitly allows poly(k)-coset families, so Prop. 1.3 does not exclude a binary black box at poly(k) branching; the memo itself concedes this in M §7, lead 1. |
| 2 | **Theorem X**: black box in 2^{O(t log³ m + log⁵ m)}, so degree-d GI is in n^{O(log³ d)}·2^{O(log⁵ d)}, giving c = 10/3 for all d and c = 3 for d ≤ 2^{√log n} or d ≥ 2^{(log n)^{2/3}} [PROVEN] | **sound; no break found.** Step 5's black-box calls are on ≤ 3m/4 points (Lemma S, checked case by case against HBD's definitions, §1.2). The recurrence and its unrolling are right (§1.3). HBD's lemmas are used within their hypotheses (§3). Framing needs two corrections (§1.5). (i) "c = 3 for d ≥ 2^{(log n)^{2/3}}" is Babai–Helfgott alone. (ii) Against the previously signed n^{O(L³)}·2^{O(L⁶)}, Theorem X gains **exactly for 5/3 < x < 3**, i.e. 2^{(log n)^{1/3}} < d < 2^{(log n)^{3/5}}; the worst case drops from 4 to 10/3. Three presentational fixes are listed in §1.4. |
| 3 | **Theorem G**: c = 3 for all d via a non-reset tower potential [SKETCH] | **SKETCH stands; no obvious break.** The recursion arithmetic and Lemma O1 check. **O3's hypergeometric gap is closed here** by a two-case ratio argument (§4.3). O2's argument works; its parity gap closes with paired transpositions, and its z > 2k/3 branch is vacuous (§4.2). Gap 1 (the pairwise heavy round inside GNS aggregation) remains. **New gap:** ρ must be defined on a *maintained* tower, and GNS's free choice of the next block system must be pinned so that inserted levels stay comparable; this needs a CB-§7.3-style rule (§4.4). "No black box at all" is inaccurate, since case (iv) still calls B–H on binary structures (harmless). |
| 4 | HJ as black box: log M = O(L²), cost 2^{O(L⁴)}, redundant given exp(O(log² n)) on the whole input [CONDITIONAL: HJ Lean] | **sound as a conditional.** Prop. 2.2's encoding, the arithmetic, and Prop. 2.4's redundancy argument all check (§5). |
| 5 | Novelty | **No source found that states 10/3, an explicit black-box cost, or the Theorem X/G routes.** One correction: GN21 L1253 explains GNS's choice to use Babai's algorithm as a black box "instead" of the combinatorial subroutines. It does not propose the subroutine variant as an option, so M §6 over-reads it slightly. Residual risk: Neuen's thesis and the SICOMP text, both still unread (§6). |
| 6 | Assumptions (Prop. B, Theorem C, Lemma A, §7.3 fix, domain count, HBD) | **all established in the repository or in print and used within their hypotheses** (§3). |

**Overall: no break of the headline.** Theorem X is a correct proof, at referee-reading level, of
n^{O(log³ d)}·2^{O(log⁵ d)}, and hence of c = 10/3 for all d. The "Θ(L²)" arity-cost claim is
refuted by the memo's own example. Theorem G remains a credible sketch, with one gap closed and one
new gap found. The statement I would sign is in §7.

---

## 1. Theorem X (attack 1)

### 1.1 What BB does

BB solves the problem behind X(m,t): t-ary structures on m points, satisfying (P1), with twin classes
≤ 3m/4.
1. It runs t-ary WL.
2. It finds the Design-Lemma tuple x⃗ (ℓ < t points) on side 1.
3. Outcome (1) makes Y₁ a colouring with all classes < 3m/4. Outcome (2) has a dominant class C,
   |C| ≥ 3m/4, with X''₁ = (X_{1,x⃗})^{(2)}[C] non-trivial. If X''₁ is imprimitive, take its first
   disconnected colour, which gives an equipartition. If it is uniprimitive, run Split-or-Johnson,
   with O(log m) further points z⃗.
4. On side 2 it enumerates all (y⃗, z⃗′).
5. For each surviving candidate it runs GNS's Theorem 7.3 on the coset Hτ, where
   H = Aut(Y₁) ∩ Sym(D₁)_{(x⃗,z⃗)} acts on Ω = D^{⟨t⟩} with the coordinate sequence. Every case-(v)
   black box in that run is answered by BB recursively.

### 1.2 Why step 5's black boxes are on ≤ 3m/4 points

* **Giants are alternating composition factors of subgroups of H.** Every group in the step-5 run is a
  subgroup of H, or a restriction of one to an invariant set. A GNS giant A_{k″} is a composition
  factor of N ⊴ P, where P is a quotient of such a group. So A_{k″} is a composition factor of a
  subgroup of H. GNS Thm 7.3 (G L2140) needs only an almost d-ary sequence of G-invariant partitions.
  "Agree on the first i coordinates" is H-invariant, and each block has ≤ m children, so d := m works.
* **Lemma S, case by case.** I checked each degree bound against HBD's definitions.
  * (1): the Design Lemma's "no α-dominant colour" means every class is **< αm** (HBD L1350:
    dominant means ≥ α|Γ|).
  * (2a): the first disconnected colour of a non-trivial homogeneous configuration gives ≥ 2 blocks of
    equal size ≥ 2 (HBD L1421). So both the block size and the number of blocks are ≤ |C|/2.
  * (2b), partition. HBD's coloured α-partitions are **admissible**: every block has size ≥ 2 (HBD
    L486–500). That is exactly what gives p_j ≤ |C|/2 in M §3.4. Without admissibility, a colour of
    many singleton blocks would give Sym(p_j) with p_j ≈ |C| and break the lemma. HBD's own text uses
    the trivial partition of a singleton colour class (L1443), which is not admissible, but such a
    class is a fixed point and harmless.
  * (2b), Johnson. HBD *define* J(r,s) with **r ≥ 2s+1** (L794), and the functor is full, so
    Aut = Sym(Λ) (L805). HBD L1797's looser "k_i ≤ m_i/2" would allow r = 2s and
    Aut = Sym(Λ) × C₂, which has the same alternating factors. Then |D∖Γ₀| ≤ m − (3/4)(3/4)m = 7m/16,
    and r ≤ 1 + √(2m).
  * The reduction "a composition factor of a subgroup of ∏Gᵢ or of G₁ ≀ G₂ is one of a subgroup of
    some Gᵢ" is the standard projection–kernel argument. A_j involved in a subgroup of Sym(c) forces
    j ≤ c.
* **The recursive calls meet BB's hypotheses.** Each step-5 case-(v) call has arity t′ = max(9, 3 + log₂ m)
  and lives on m″ = |D″| > 3k″/4 > 7.5t′ points. (P3) (CB Lemma T′.3; HBD L1949 gives the same
  "twin class < t′" from non-fullness) gives twin classes ≤ t′+1 < m″/7 ≤ 3m″/4, and t′ ≤ m″/2. So the
  Design Lemma applies again.

**Verdict:** the claim "every black-box call inside step 5 is on ≤ 3m/4 points" is correct.

### 1.3 The recurrence and branch counts

* *Candidates.* The Design Lemma gives ≤ m^t tuples y⃗ (ℓ < t). Split-or-Johnson gives a pointwise
  stabilizer of index m^{O(log m)} (HBD Thm `coupjohn`, L1423–1434). So there are m^{t+O(log m)}
  candidates, each followed by its own step-5 run.
* *Step 5.* By Theorem C's almost-d-ary part with d := m and N = m^t (checked: its proof uses N only
  through CB Lemma 7.0, and K = O(log² m) is set by the tree size and the 2^{O(log² m)} exits per node),
  the run has N^{O(log² m)} = 2^{O(t log³ m)} nodes. Each node makes ≤ k⁶ black-box calls.
  * Case (iv) calls cost 2^{O(log³ m)} by B–H.
  * Case (v) calls cost X(3m/4, t′).
* *Recurrence.* With absolute constants,
  log X(m,t) ≤ C·t·log³m + C(t + log m)·log m + log(1 + X(3m/4, t′)), with t′ = max(9, 3 + log₂ m).
  The Design-Lemma factor m^t is lower order; the GNS run, 2^{O(t log³ m)}, dominates each level.
* *Unrolling.* m_j = (3/4)^j m, with t_j = 3 + log m_{j−1} for j ≥ 1. The depth is ≤ log_{4/3}(m/20t),
  and the base case m ≤ 20t costs (20t)! = 2^{O(t log t)}. The sum is
  C(t log³ m + Σ_j log⁴ m_j) ≈ C(t log³ m + log⁵ m/(5 log₂(4/3))) ≈ C(t log³ m + 0.48 log⁵ m).
* *Numbers* (red-team script, part 1, constants set to 1, with the true t_j and the base case):
  log X(d, t)/(tL³ + L⁵) is 0.58 at L = 12, falling to 0.49 at L = 256. Over m ∈ {d, √d, d^{1/4}} the
  worst ratio is 0.66. The author's part 2 uses the cruder t_j ≤ 5 + L and gets 0.62–0.85. Both are
  O(L⁵).
* At the top level t = 3 + log d and m ≤ d, so X(d) = 2^{O(L⁴ + L⁵)} = 2^{O(L⁵)}.

**Verdict:** the exponent 5 is right.

### 1.4 Correctness of the round, and three presentational fixes

The pairwise round is HBD's eq. (`kozron`) (L1763): a union over coset representatives of the
individualizing stabilizer. One point should be explicit. Split-or-Johnson itself makes internal
brute-force choices: inside Prop. `bicoup` it runs the Design Lemma with a "first tuple found"
search (L1567), and it fixes vertices "non-canonically" (L1689, L1693, L1712). On side 2 the
enumeration must range over the **whole choice sequence**, internal Design-Lemma tuples included,
and not over "the lexicographically first" choice. M §3.2 step 4 ("every z⃗′ … run the same
deterministic procedure on (X₂, y⃗, z⃗′)") is correct only under this reading. The count is still
m^{O(log m)} (HBD's index bound).

Fixes:
1. M §3.2 step 4: say that z⃗′ encodes every choice Split-or-Johnson makes, including its internal
   Design-Lemma tuples.
2. M §3.4 (2b) partition: cite HBD's admissibility (blocks ≥ 2, L490) as the reason p_j ≤ |C|/2.
3. M §3.4: state the recursive hypotheses explicitly: t′ = max(9, 3 + log₂ m), m″ > 7.5t′, and twin
   classes ≤ t′+1.

None of these changes the statement.

### 1.5 Regimes, and what is actually new

* The profile with the B–H switch is min{max(3, 5−x), 2x}. Its maximum is 10/3 at x = 5/3, and it
  equals 3 for x ≤ 1.5 and for x ≥ 2 (both scripts).
* **"c = 3 for d ≥ 2^{(log n)^{2/3}}" (x ≤ 1.5) is Babai–Helfgott alone,** exp(O(ℓ³)) = n^{O(L^{2x})}.
  The w9 red team required the same correction for w8 (`redteam-w8-gnsexp.md` §4.3).
* **Gain over the signed w9 statement** n^{O(L³)}·2^{O(L⁶)}, whose profile is min{max(3, 6−x), 2x}:
  * equal for x ≤ 5/3 (both are 2x, or ≤ 3);
  * strictly better exactly for **5/3 < x < 3**, i.e. 2^{(log n)^{1/3}} < d < 2^{(log n)^{3/5}};
  * equal (3) for x ≥ 3.
  * The worst case over d drops from 4 to **10/3** (script part 1 asserts this).
* M §0 row 3 and §5 B1 should state the gain in this form.

### 1.6 Things that could have broken, and did not

* *Does step 5 need a change of action, which would blow up N?* No. S_m (and H) on injective tuples is
  already m-ary with N = m^t.
* *Is the recursion self-similar with no progress?* No. Without the Design-Lemma round, GNS on S_m^{(t)}
  has a top giant of degree m and black boxes of size m (w8 §2.6). The round is exactly what pushes
  every alternating section below 3m/4.
* *Hidden multiplicative costs* (candidates × step 5 × inner calls). All are accounted for. The
  candidate factor multiplies the whole step-5 run and is lower order.
* *Combine step.* Every candidate's result is a coset of the same group K = Aut_H(𝔄₁), since H depends
  only on side 1. The union equals Iso(𝔄₁, 𝔄₂), because each π ∈ Iso lies in the candidate
  (x⃗^π, z⃗^π). Correct, up to left/right conventions.

---

## 2. The arity obstruction (attack 2)

### 2.1 The instance is valid

* G = Sym(k) on [k]^{⟨t⟩}, k = q+1, d = k, and x = B, the colouring of injective t-tuples by
  PGL(2,q)-orbits.
* **Aut(B) = PGL(2,q) exactly** for t ≥ 4. An automorphism agrees with one element of PGL on any
  fixed triple, and then, through tuples containing that triple, on every point.
* GNS's fullness is defined with the full Aut_{G_T}(x) (G L1760), not with a window. So
  (Aut_{G_T}(x)^φ)^T = PGL(2,q)_{{T}}|_T, which has order ≤ t(t−1)(t−2) < t!/2. No T is full, F = 1,
  S = ∅, and we are in case (v) with D = [k].
* (P4) gives Aut(𝔄) ≥ PGL(2,q) ∩ φ(G′) ≥ PSL(2,q), which is 2-transitive (script part 3a).
* So the bullet points of Prop. 1.3 hold. The memo itself notes that it did not check whether such an
  instance arises from degree-d GI. That does not matter for an interface claim, but the claim should
  be worded as one about the black-box interface.

### 2.2 The "2^{Θ(L²)}" conclusion is refuted by the same instance

The case-(v) colours **refine the PGL-orbit colouring.**
* A comparison morphism is an isomorphism of local certificates. It preserves x on the window, and the
  window contains T^{⟨t⟩}: those tuples are affected, by G L1770 and L1801.
* Two orderings in one comparison class therefore lie in one PGL-orbit.

PGL(2,q) is sharply 3-transitive (part 3c).
* After individualizing p₁, p₂, p₃, the colour of (p₁, p₂, p₃, u, …) determines u.
* So X^{(1)}_{(p₁,p₂,p₃)} is discrete: the Design Lemma's outcome (1) with ℓ = 3. Part 3c verifies the
  distinct colours for q = 7, t = 4.
* **Arity reduction on this instance costs k³ branches, not k^{Θ(t)}.**

The memo's own M §1.3 remark ("Individualizing 3 points kills PSL(2,q) here") and lead 1 ("whether
O(1) individualizations always suffice is open") contradict its summary sentence. What is proven is:
* *upper bound:* k^{<t} (Design Lemma);
* *lower bound, for some instances:* at least one individualization (Prop. 1.3);
* *the gap between them:* open.

### 2.3 The poly(k)-family remark is false, and M §1.2 allows such families

* M §1.3 says: "the same holds for every poly(k)-size family produced without individualization,
  since the family is permuted by Aut(𝔄)." Being permuted does not make the members trivial. Take
  Y_x := the orbital structure of PSL(2,q)_x on P¹∖{x}. This is a k-member family permuted by
  PSL(2,q), and every member is non-trivial: PSL's point stabilizer has rank 3 (part 3b, q = 7, 11, 13).
  The remark is true only if "without individualization" means "each member is Aut(𝔄)-invariant",
  and then it is a tautology.
* M §1.2 permits "a union of at most poly(k) cosets", and GNS case (iv) already uses k⁶. So Prop. 1.3
  excludes only **one-coset** canonical binary relaxations. It does not show that the black box
  cannot be made binary at poly(k) branching.

**Fix.** Downgrade M §0 row 1′ to "no Aut(𝔄)-invariant binary relaxation exists on some instances, so
at least one individualization is needed; the Design Lemma gives at most k^{<t}; whether O(1)
individualizations suffice is open (on Prop. 1.3's own instance, 3 suffice)". Delete "2^{Θ(L²)}" and
the poly(k)-family remark.

---

## 3. Assumptions (attack 3)

| assumption | where used | status |
|---|---|---|
| HBD Design Lemma (Prop. `design`, L1354) | BB step 2 | Hypotheses: a k-ary coherent configuration with 2 ≤ k ≤ \|Γ\|/2, 1/2 ≤ α < 1, no twin class > α\|Γ\|. BB has t ≤ m/20 (after step 0), α = 3/4, and twin classes ≤ t+1. **Within hypotheses.** Twins are as in HBD L1352 ((γ₁γ₂) ∈ Aut), the same notion as (P3)'s Sym(Δ) ≤ Aut. |
| X''₁ is a non-trivial homogeneous classical coherent configuration | step 3 | HBD L1415 asserts it for the Design Lemma's outcome (2). |
| HBD Split-or-Johnson (Thm `coupjohn`, L1423) | step 3 (2b) | Needs a uniprimitive configuration and 2/3 ≤ α < 1; BB uses α′ = 3/4. Imprimitive X''₁ is handled separately (2a), as in HBD L1421. **Within hypotheses.** The index is \|Γ\|^{O(log \|Γ\|)}. |
| coloured α-partition, Johnson scheme | Lemma S | Definitions as in §1.2: admissible blocks (≥ 2), and r ≥ 2s+1. |
| WL functors F₁, F₂, F₃ with canonical colour order | step 1 | HBD L1338, Ex. `canonord` (L2354). |
| Johnson identification | step 4 | HBD §`subs:idgroup` (used for schemes at L1797). It assumes r > (s+1)² − 2 in this notation. Otherwise r! = \|Γ₀\|^{O(log \|Γ₀\|)} = m^{O(log m)}, and the alignment can be brute-forced within the candidate budget (footnote, L840). Fine. |
| w8 Lemma A, Prop. B, Theorem C | BB step 5, Corollary X | Red-teamed **sound** (`redteam-w8-gnsexp.md` §2–4.1). Lemma A holds for m ≥ 6, and here k′ > 10t ≥ 90. |
| CB §7.3 fix (next block system ⪰ 𝒞′[Ω′]) | inside every GNS run | Red-teamed (`redteam-gns-lemma72.md`). It is a legal run of GNS's algorithm. |
| Domain count N ≤ n^{O(L)} | Corollary X | GN21 Thm 4.16 / w8 Prop. 2; red-teamed. |
| (P3), twin classes ≤ t+1 | X's hypothesis | CB Lemma T′.3; independently HBD L1949 ("no twin class can have ≥ k elements" when T is not full). |
| GNS (SICOMP 2023), CFSG | throughout | Trusted. Theorem X adds no CFSG dependence (HBD's combinatorics are CFSG-free). |

---

## 4. Theorem G (attack 4)

### 4.1 Structure and arithmetic

The recursion lemma is T(n, ρ) ≤ n^A·2^{Bρ}, with A, B = O(L²). It closes under three kinds of
children:
* exits, each ≤ n/2: factor 2^{O(L²)}·2^{−(A−1)};
* shrinks, with orbits ≤ 5n/6: factor 2^{O(L²)}·(5/6)^{A−1};
* O2 rounds, on the same n with ρ−1: factor 2^{O(L²)}·2^{−B}.

With ρ ≤ 2 log N and N ≤ n^{O(L)}, the total is N^{O(L²)} = n^{O(L³)}. This checks.

Per phase:
* Prop. B (whose defect argument covers heavy-round children too: colourings with classes < 3k/4,
  admissible partitions, and Johnson schemes all exclude Alt(Δ) with |Δ| > 3k/4) gives O(L)
  aggregation rounds on a same-domain path.
* Johnson steps satisfy k_{i+1} ≤ 1 + √(2k_i), so Σ t·log k_i = O(tL) = O(L²).

**Lemma 4.0** (DM 5.2B) and **Lemma O1** check. O1's (3k/4)/(9k/10) = 5/6 uses s < t < k/10.

### 4.2 Lemma O2

The argument is better than its "[SKETCH]" label suggests.
* *𝔈 is R-invariant.* 𝔈 is the partition into fibres of Ψ∘σ, and Ψ(S) = (block ↦ |S ∩ block|) is
  L_Y-equivariant.
* *𝔈 is not {Ω′}.* By O1's conditioning applied to blocks, every Ψ-fibre has probability ≤ 5/6. A
  non-shrink orbit has probability > 5/6, so it meets ≥ 2 fibres.
* *𝔈 is not 𝒞′[Ω′].*
  * Suppose every 𝔈-block were one class. Then Ψ is injective on the L_Y-orbit P = σ(Ω′).
  * For a block B with |B| ≥ 3 and 0 < |S ∩ B| < |B|, there is g ∈ Alt(B) with S^g ≠ S. Here
    Alt(B) ≤ Aut(Y₁) ∩ A_k ≤ L_Y, since B contains no individualized point. This contradicts
    injectivity.
  * **Parity fix** for |B| = 2. Multiply the transposition of B by a transposition inside another
    block B′ (|B′| ≥ 2) that fixes S, i.e. two points of B′ both in S or both outside it. If no such
    B′ exists, every other non-singleton block is a 2-block split 1–1 by S; then swap two split
    2-blocks simultaneously. If φ(G′) = S_k, no parity issue arises at all.
  * So every S ∈ P is a union of whole blocks. Draw S as an injective tuple: if u₁ lies in a
    non-singleton block, some fixed partner of u₁ must also be drawn, with probability ≤ (s−1)/(k−1).
    So P(union of blocks) ≤ z/k + 1/10.
* *The branch z > 2k/3 is vacuous.* Singleton blocks are either individualized points
  (O(t + log k) ≪ k of them) or, in GNS case (ii), F-fixed points (< k/4, because |S_i| > 3k/4).
  So the bound is ≤ 1/4 + 1/10 + o(1) < 5/6, and the round is a shrink.

**Verdict:** O2 is sound modulo writing out the parity case.

### 4.3 Lemma O3: the hypergeometric gap, closed

**Claim.** Let K < k/4, s < k/10 and 1 ≤ j ≤ min(K, s), and put N_i = C(K,i)·C(k−K, s−i). Then
P(X = j) < 5/6.

*Proof.* The ratio N_{j−1}/N_j equals j(k−K−s+j)/((K−j+1)(s−j+1)).
* Since k−K−s > 0.65k and (K−j+1)(s−j+1) ≤ Ks, this ratio exceeds 0.65·jk/(Ks).
* **Case A**, Ks ≤ 3.25jk. Then N_{j−1}/N_j > 1/5, so N_j < (5/6)(N_j + N_{j−1}).
* **Case B**, Ks > 3.25jk. Then (K−j)(s−j) ≥ Ks − j(K+s) > 3.25jk − 0.35jk = 2.9jk > 0. In particular
  j < min(K, s). The denominator of N_{j+1}/N_j = (K−j)(s−j)/((j+1)(k−K−s+j+1)) is ≤ (j+1)k ≤ 2jk.
  So N_{j+1}/N_j > 1.45, and N_j < (N_j + N_{j+1})/2.45 < (5/6)(N_j + N_{j+1}).
* In both cases N_j < (5/6)·C(k,s). ∎

Part 2 of the red-team script checks both case inequalities with exact rationals for every
k ∈ [20, 200] and k ≤ 600 in steps of 10, and every admissible K, s, j (about 3.9 million cases). The
largest bound produced is 0.830 < 5/6; the true maximum seen is 0.436.

The hypotheses hold in O3:
* non-shrink forces |Γ₀| > 3k/4 by O1, because every other colour class of Y₁ (S, D∖C, C∖Γ₀) is
  < k/4; hence |O| < k/4;
* s < t < k/10.

The **C₂ step checks.** Let K_O = L_Y ∩ (Sym(O) × 1). For σ(c) ⊆ Γ₀, Lemma 4.0 gives
Alt(O) ≤ Alt([k]∖σ(c)) ≤ S_c, so K_O acts on the classes over Γ₀ through a group of order ≤ 2. And
L_Y/K_O embeds in Aut(J) = Sym(Λ). So every alternating section of the action on the large orbit has
degree ≤ r ≤ 1 + √(2k).

**Verdict:** O3 is sound modulo gap 1.

### 4.4 A gap the memo does not name: which tower ρ lives on

ρ must be the ρ of a **maintained** tower: GNS's sequence plus the inserted levels 𝒞′, 𝔅, 𝔈.
* It cannot be the minimum over all invariant towers. "Inserting 𝔈 lowers ρ by ≥ 1" holds only for
  a tower in which 𝔈 sits strictly between two consecutive levels. An optimal tower may contain a
  level that crosses 𝔈.
* For the maintained tower, GNS's free choice of the next maximal block system (G L2087; "a minimal
  block system" in Neuen 2020) must be pinned. The next 𝔇 must be chosen ⪰ the current top inserted
  level, otherwise a later 𝒞″ ⪰ 𝔇 can be incomparable with 𝔈.
* Choosing 𝔇 ⪰ (top inserted level) ⪰ 𝒞′[Ω′] is a legal run, exactly like the CB §7.3 fix. With it,
  every new 𝒞″ is inserted at the top, and monotonicity holds.
* Restriction to windows and orbits does not increase any r_i (HBD L2013).
* This should be stated as part of Theorem G's algorithm.

### 4.5 What remains

* **Gap 1** (named): the pairwise heavy round inside GNS aggregation, its child cosets
  φ⁻¹(Iso((x⃗,Y₁),(y⃗,Y₂))), and how it composes with case (iv). It is routine in shape (BB does the
  same on a bare structure) but unwritten.
* **Gap 4.4** (new): the tower-maintenance rule.
* **Wording:** "no black box at all" (M §0 row 4) should read "no t-ary black box". Case (iv) still
  calls B–H on binary structures, at 2^{O(L³)}, additively (M §4.2, last bullet).
* **No obvious break.** At d = n, Theorem G gives exp(O(log⁴ n)), which is consistent with
  Babai–Helfgott. Nothing in the phase accounting double-counts.

**Theorem G: [SKETCH], plausible.** O1 is proven, O3 is proven modulo gap 1, O2 is proven modulo
writing out the parity case, and gaps 1 and 4.4 are open.

---

## 5. Claim 4: HJ as the black box

* *Prop. 2.2.* M = m^{2t}(t log m)^{O(1)}, so log M = O(t log m) = O(L²).
  * Pendant leaves: every original vertex gets ≥ Δ+2 leaves, so leaves are exactly the degree-1
    vertices, and colour = (number of leaf neighbours) − Δ − 1.
  * Ports fix positions, and code vertices fix the colour index.
  * **Correct.**
* *Cost.* exp(C log² M) = 2^{O(L⁴)}, so with Theorem C, c = 3. **Correct.**
* *Prop. 2.4, redundancy.*
  * For ℓ ≤ L³, HJ on the whole input gives exp(O(ℓ²)) = n^{O(ℓ)} ≤ n^{O(L³)}.
  * For ℓ ≥ L³, Theorem C with B–H gives n^{O(L³)}.
  * The profile is min(3, x). **Correct.**
* All of this is conditional on HJ's Lean `main_theorem` (an unrefereed 2026 claim; 10 CFSG-based
  axioms). It is correctly labelled.

---

## 6. Novelty (attack 5)

* **GNS v3.** "the only place where we use Babai's … test as a black box"; c is left unspecified.
* **Neuen 2020 and Neu26.** n^{polylog(d)} only. Neu26 has no explicit exponent and no remark on the
  subroutines (searched both text copies).
* **GN21 L1253.** "the algorithm does not exploit the combinatorial subroutines directly, but one can
  simply rely on using Babai's algorithm as a black box instead. In particular, this also simplifies
  the analysis."
  * This explains GNS's design.
  * It implies that a direct-subroutine variant exists, but it does not *propose* one and gives no
    exponent.
  * M §6's "names the option" is a slight over-reading. Reword it.
* **HBD L1961.** "with a little bit of work … c = 3" refers to Babai's *general* bound exp(O(log³ n)),
  not to GNS. HBD's ρ (L2016–2046) is a known ingredient; Theorem G's hybrid of it with GNS's O(log d)
  test sets was not found.
* **Pago (2302.05426).** The relative of Lemma A, already credited by the w9 red team. Nothing on the
  black box.
* **Web (2026-11-05).** Two searches found nothing after GNS / GNSW18 / Neuen 2020 on the exponent:
  [GNS arXiv](https://arxiv.org/abs/1802.04659v2), [GN21](https://ar5iv.labs.arxiv.org/html/2011.01366),
  [Neuen 2020](https://arxiv.org/pdf/2002.06997),
  [GNSW18 (deepai)](https://deepai.org/publication/towards-faster-isomorphism-tests-for-bounded-degree-graphs).
* **Closest conceivable shortcut, checked.** A hypergraph test in time poly(#edges)·exp(polylog n)
  would make the black box 2^{O(L³)} and give c = 3 directly. No such result is known.
  * The best general bound is Neuen 2020's (n+m)^{O((log d)^c)}.
  * Neuen 2020 uses the same GNS black box (Neu20 L2621), so it does not help.

**Verdict:**
* Theorem X (10/3) and Theorem G's hybrid were not found anywhere.
* The explicit black-box cost and the observation that only case (v) is expensive appear new, but
  they are routine.
* Prop. 1.3 is elementary.
* Residual risk: Neuen's 2019 thesis and the SICOMP text, both still unread (blocked, not bypassed).

---

## 7. What I would sign, and required edits

**Signed statement.** Assume:
* GNS (SICOMP 52(6), 2023), with its CFSG-dependent inputs;
* the CB §7.3 choice of the next block system;
* GN21 Thm 4.16 (or w8 Prop. 2);
* w8 Lemma A, Prop. B and Theorem C (red-teamed);
* Helfgott–Bajpai–Dona's Design Lemma, Split-or-Johnson (with Johnson identification) and WL
  functors, as published;
* Babai–Helfgott's exp(O(log³ m)).

Then:
* Isomorphism of two t-ary structures on m points, with all t-sets non-full in GNS's sense (more
  generally: satisfying (P1), with twin classes ≤ 3m/4), is decidable in time
  **2^{O(t log³ m + log⁵ m)}**.
* Consequently, string isomorphism for Γ̂_d-groups on n points, and GI for graphs of maximum degree
  d, is decidable in time **n^{O(log³ d)}·2^{O(log⁵ d)}**.
  * This is n^{O(log³ d)} for d ≤ 2^{(log n)^{1/2}}.
  * Together with Babai–Helfgott, it is **n^{O(log^{10/3} d)} for all d**.
* Against the previously signed n^{O(log³ d)}·2^{O(log⁶ d)}, the improvement is confined to
  2^{(log n)^{1/3}} < d < 2^{(log n)^{3/5}}. The bound n^{O(log³ d)} for d ≥ 2^{(log n)^{2/3}} is
  Babai–Helfgott alone.

**Not signed:**
* any lower bound on the cost of arity reduction;
* Theorem G (c = 3 for all d), which stays a sketch with two open gaps (§4.5).

**Required edits to the memo.**
1. M §0 row 1′, M §1.3 last line, and the brief's claim 1: delete "k^{<t} = 2^{Θ(L²)}" as a cost
   statement. Replace it by "≤ k^{<t} (Design Lemma), ≥ 1 individualization on some instances". Note
   that Prop. 1.3's instance needs only 3 points (§2.2).
2. M §1.3 remarks: delete or restate the poly(k)-family remark (counterexample {Y_x}, §2.3). Say
   explicitly that M §1.2 admits poly(k)-coset families, so Prop. 1.3 does not exclude a binary black
   box at poly(k) branching.
3. M §0 row 3, §3.1 Corollary X and §5 B1: mark "c = 3 for d ≥ 2^{(log n)^{2/3}}" as Babai–Helfgott
   alone. State the gain as "only for 5/3 < x < 3; worst case 4 → 10/3".
4. M §3.2 step 4: the side-2 enumeration covers Split-or-Johnson's whole choice sequence (§1.4).
5. M §3.4: cite HBD admissibility (L490) for p_j ≤ |C|/2 and HBD L794 for r ≥ 2s+1. State t′,
   m″ > 7.5t′ and twin classes ≤ t′+1 for the recursive calls.
6. M §4.2 O3: replace "checked numerically for k ≤ 300" by the two-case proof of §4.3. Upgrade O3 to
   "proven modulo gap 1".
7. M §4.2 O2: add the paired-transposition parity argument, and note that the z > 2k/3 branch is
   vacuous (§4.2).
8. M §4.1/§4.3: define ρ on the maintained tower, and pin GNS's choice of the next block system to be
   ⪰ the top inserted level (§4.4). Add this as gap 4 of Theorem G.
9. M §0 row 4 and §4: "no black box at all" → "no t-ary black box (case (iv) still uses B–H on binary
   structures)".
10. M §6: reword the GN21 L1253 reading (§6).
