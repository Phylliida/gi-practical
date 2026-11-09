# Red-team of the new §10.9 of `paper/canon.tex` (Algorithm CanHyp, Proposition `prop:canhyp`)

Branch `w13-redteam-canhyp`, 2026-11-08. Adversarial referee pass over the text added in commit
`22fb2c0` (M1 of `docs/referee-canon-paper.md`): §10.9, Lemmas E4, F2^set, W, B, SIMP, the complete-occupancy
invariant, the termination argument, and Remark rem:BC / c_BC.

**Sources** (read only, untrusted): Neu20 = arXiv:2002.06997v2 source
(`scratchpad/r4-sources/arxiv-2002.06997/x/hypergraph-gamma-d.tex`, "N…" = line), GNS v3. Read: N986–1240
(problem, BalanceOrbits, Thms 4.8/4.9), N1455–1554 (renormalize), N1570–1700, N1930–2141 (Simplify and its
proof), N2145–2460 (local certificates and its cost), N2470–2800 (aggregation, find-structure, Lemma 4.36,
Thm 4.37). No downloads. Not seen: Neu19 (dissertation, Lemma 6.1.17), as the paper states.

**Executed.** `nice python3 -I docs/redteam-canhyp-check.py` (about 22 s, standard library), §3 below. No Lean,
no solver. `pdflatex` is not installed here, so the edited `canon.tex` was **not compiled**; a brace and
paragraph-by-paragraph `$` balance check of the diff passes and the new macros are defined.

---

## 0. Verdicts

| item | verdict | one line |
|---|---|---|
| Algorithm CanHyp (Chain, Luks, Steps 0–5) | **sound** as an algorithm | Exhaustive case split; every recursive call is a valid instance (§1.1). |
| Prop. `prop:canhyp`: termination via (virtual size, \|Γ\|) | **sound after one fix** | The measure decrease is right; the "CanLC has ≤ s rounds" input used (S4)'s second half, which is false (§2.1). The conclusion of (I4) survives. Fix applied. |
| Complete-occupancy invariant | **sound** | Established at the root (𝔛⁺ then Thm 4.8), preserved by every call, and it does imply the strict decrease. Without it, Obs 4.12 and the decrease fail, as the author says; the check reproduces this (§1.3). |
| Canonicity (no input dependence) | **sound**; no break found | Every order/choice is a function of a prefix or the group; attacks of §1.4 fail. |
| Conventions (left/right cosets) | **sound** | All composition checked; §1.5. |
| Lemma E4 | **sound** | Proof correct as written. |
| Lemma F2^set | **sound** | Direct check of the two nested E2 applications. |
| Lemma W | **sound** | Forward and backward direction of N1648–1690 for one object. |
| Lemma B | **sound** | Canonical choice of orbit; strict descent. |
| Lemma SIMP (modulo Thms 4.9, 4.17) | **gap in (S4) second half, fixed** | (S1)–(S3), (S4) first half right. (S4)'s second half and **Neu20 Thm 4.17(G) are false as stated** (§2.1). Replaced by the corrected potential ŝ; the fix is proved in the text. |
| Lemma AGG, statement (i) | **minor, fixed** | "\|V_j\| ≥ 3k/4" is the GNS slip already noted in Prop. cases. |
| Remark rem:BC and c_BC | **sound after clarification** | New definition makes the exponent bookkeeping consistent; Babai's test (Thm 2.1) must be covered by c_BC; c₁, c₂ were undefined (§2.2). |

**Overall.** One real, fixable break: a false estimate imported verbatim from Neu20 (Thm 4.17(G)) into (S4)/(I4). It
was never used for the *measure* of recursive calls, only for the bound on the number of rounds of CanLC and for
the cost sum, and both survive with a corrected potential. Nothing else in the new text is wrong, modulo the stated
dependencies (Neu19 unseen; constructions of Neu20 under (D3)). Status claims unchanged.

---

## 1. What was checked

### 1.1 The algorithm and its instances

* Step coverage: intransitive / transitive semi-regular on 𝔅₁ / transitive |𝔅₁| ≤ d is exhaustive (definition of
  almost d-ary). Step 3's block system exists (𝔅₁ itself has ≥ 2 classes).
* Luks: D has ≥ 2 classes in every caller (𝔅₁, 𝔅, Cp); so B_(D) is intransitive and Chain applies. Chain's
  windows are proper subsets of its domain.
* Same-domain children: R_𝔸 and L are proper in G′ ((4/3)^k > 1, Prop. opt1/Lemma 5.8, Cor 4.28); 𝔅⊕Cp is
  G′-invariant and almost d-ary (|Cp| ≤ b ≤ d, ≤ d blocks of 𝔅₁ in each class; Cp ⪰ 𝔅 ⪰ 𝔅₁); 𝔓 remains a level.
* Restrictions (V, R_i^V, 𝔓[V], 𝔅[V]): semi-regularity and |·| ≤ d are inherited, using that V is an R_i-orbit
  (the stabilizer of B∩V equals R_{i,B}), so the instance form is valid after removing duplicates.
* Thm 4.8 at the root: f(P\*) is a block, every block is hit (v_P is reachable), and x\* = x∘f; 𝔛 ↦ (𝔛⁺)\* is
  injective and equivariant. Note that f is not injective on P\* in Thm 4.8 (it is in Thm 4.9); the proof needs
  only surjectivity, as written.

### 1.2 Termination: every recursive call lowers (s, |Γ|)

Direct proof of each case of the proposition's list (windows of Chain, windows inside CanLC, same-domain children);
all correct, given Obs 4.12 with complete occupancy and (I4)(first part)/(I5). The only gap is the loop count of
CanLC (§2.1), where the paper's reasoning relied on a false estimate; after the repair the number of rounds is ≤ s.

### 1.3 Complete occupancy

* Root: 𝔛⁺ pads ⊥ on empty blocks (injective, equivariant); (𝔛⁺)\* is completely occupied.
* Restriction: if every block of 𝔓 has a string, every P∩U ≠ ∅ has one.
* Same-domain transport by elements preserving 𝔓: trivial. Copy step: P×{z} exists only because z = x[W∩P]
  for a string of Z (P ↦ copies is onto because Z is completely occupied). Renormalize: ✓ (S1)–(S3).
* It implies the decrease: Obs 4.12 is correct under complete occupancy, and fails without it (a block with no
  string can be the only difference between two windows). The check's `no_occupancy` mutant produces 124 measure
  violations; with occupancy there are 0.

### 1.4 Canonicity attacks (none succeeded)

Every place where the output could see order, generators, or non-canonical data was examined:

| attack | resolution |
|---|---|
| order of Chain windows (R_i-orbits by (size, least point)) | function of R_i and U_i (prefix) |
| choice of π in Chain, Luks, CanLC (d) | E2: independence of π |
| order of Λ′-orbits of W′ in CanLC | P1 |
| left transversal Q in F3 | output depends only on branch values (Lemma F3) |
| renormalization depends only on prefix | true (N1521–1525); (I3) via (S3) and injectivity |
| colour c(𝔛, T⃗): depends on R(Z^σ) | R is a function of the prefix (E1); T^set(a) independence of σ |
| ranking of colours in AGG | the set of colour values is an invariant; ties compared on the canonical generating set of R |
| Lemma K: τ is "any" element of H_{Δ₀}\K(z)L | L is normal in H_{Δ₀}, and z is K(z)-invariant; the branch values do not depend on τ |
| Lemma B's choice among unbalanced orbits | (size, least point) under R_i; independent of input |
| root padding by ⊥ and Thm 4.8 | function of (Γ, 𝔓) alone |

### 1.5 Conventions

Right action x^{gh} = (x^g)^h, left cosets everywhere, checked in: E1–E4, Lemma W (E(Z) = θ⁻¹(Λ_G(G(Z)))),
F2^set (C₊ = πλE(y), independence under λ→λr by r∈R₂, Z→Z^h uses h⁻¹π), Lemma B (E(z^r) = r⁻¹E(z)), F3
(Λ_H = ⋃ρΛ_K(x^ρ)), Luks (F, πΛ), Lemma R, Δ(Z) = πτ(...)π⁻¹ with equivariance g⁻¹Δg, T^set. All consistent.

### 1.6 Lemmas (new proofs)

* **E4.** Every step, including (C1): for h with Z^h = F, 1 ∈ C(F) = h⁻¹C(Z) gives h ∈ C(Z). Right.
* **Lemma W.** The bijection Z[W] ↔ G(Z) requires that vertices on one-sided blocks be recovered from F₁∪F₂: yes
  by hypothesis Z[W_j] = F_j. Canonical graph decoded correctly (F_G lies in the θ(A)-orbit). Right.
* **F2^set.** The hypotheses of Lemma W hold for y; the prefix (U∪V, F₊, R₃) is constant on A-orbits. Right.
* **Lemma B.** O depends only on R_i and the R_i-orbit of z; R_{i+1} is proper (B transitive, μ non-constant); the
  chain bound is correct. Right.
* **SIMP** (Step 1–4): definitions match N1974–2003, N2031–2046, N2048, N1202–1554 (properties (I)–(IX)); (S1),
  (S2) (IX is used for Γ″ = A‴), (S3) (f′ onto via (VIII)), (S4) first half (the (F) computation applies with
  𝔛₁′ = 𝔛₁″ = Z″, Γ″ = A‴). The second half of (S4) is false: §2.1.

---

## 2. Problems and fixes

### 2.1 (Medium severity, fixable; applied.) (S4)'s second half and Neu20 Thm 4.17(G) are false as stated

**Claim.** Lemma SIMP (S4): the d-virtual size of (Z^π)\*[Ω\*∖W\*] is at most that of Z[Ω∖W]. Neuen's Thm 4.17(G)
(N1961) says the same, "proved analogously" (N2141). The paper used it for (I4) (strict decrease of s′ and the
bound "≤ s rounds") and in the cost accounting (N2400–2434 reasoning).

**Counterexample** (Γ = 1, so every hypothesis is met; also in `docs/redteam-canhyp-check.py`, part D):
Ω = {a,b,c,d}, 𝔓 = {{a,b},{c,d}}, W = {a,c}, 𝔛 = {(a,b) ↦ (0,0), (1,0) on the first block; (c,d) ↦ (0,0)}.
𝔛[Ω∖W] has virtual size 2 (one string on {b}, one on {d}). Simplify makes two copies of {a,b}, each with one
string on its copy of b, so 𝔛′[Ω′∖W′] has virtual size 3. Renormalize cannot lower this ((III), (V), f′ onto).

The proof of (F) does not carry over: Σ_{copies} m_{𝔛′[Ω′∖W′]} can exceed m_{𝔛[Ω∖W]}(P∖W), because strings with
different window parts can agree outside the window.

**Effect on the paper.** Lemma SIMP (S4) and the proof of (I4). The *statement* of (I4) (s′_i strictly decreases)
is actually true, but not for the reason given. Neuen's Thm 4.17(G) as used at N2400–2434 needs the same repair;
the proof there needs a correct potential.

**Fix.** Define ŝ(Y,U) := Σ_Q |Q∖U| m_Y(Q)^{f(d)+1}. Then (proved in the text): ŝ(Y,∅) = virtual size; if Y[U] is
simple, ŝ(Y,U) = virtual size of Y[outside U]; (S4′): ŝ((Z^π)\*,W\*) ≤ ŝ(Z,W), by the (F) computation with |P′| replaced by
|P′∖W′|, using only the first half of respect-block-sizes; and ŝ(Y,U) − ŝ(Y,U∪U′) ≥ virtual size of Y[U′], and ≥ |U′| if Y is
completely occupied. Since F_i is simple, s′_i = ŝ(Y_i, W_i), so s′_{i+1} ≤ ŝ(Y_i, W_i∪W′) < s′_i, and the
window virtual sizes sum to at most s. (Check: 0 corrected-potential failures on 86 non-simple windows; the old claim fails on 23.)

Note this is a statement about Neu20 as well; Remark rem:neu20 now has a third point recording it.

### 2.2 (Minor, applied.) c_BC and the exponent bookkeeping

The new definition exp(O((log n)^{c_BC})) is what the computation uses: on n = 2k^t = d^{O(log d)} points it gives
exp(O((log d)^{2c_BC})) (the old definition n^{O((log n)^{c_BC})} would not). With log n = O(log² d) this is consistent
at both occurrences. Two small additions: (i) the calls of Babai's test Thm 2.1 on the same domain also have to be
covered by c_BC (Remark rem:BC says it is used), so c_BC is now defined as an upper bound for both; (ii) c₁ and c₂ were
never defined: c₁ := max(2, 2c_BC − 1), c₂ := max(3, c₁) (c := c₂ + 2 as stated). All other occurrences (Theorem A,
row 13, Remark rem:BC, Question q:BC) are consistent; the A_k parity construction is correct (part E of the check).

### 2.3 (Minor, applied.) Lemma AGG (i)

"|V_j| ≥ 3k/4" repeats the GNS/Neuen slip (case |S| > 3k/4 removes up to 4 individualized points); Prop. cases
already says this. Rewritten "|V_j| ≥ 3k/4 − 4", with the defect bound stated on [k], which is what Step 4 uses.

### 2.4 Editorial items (applied)

SIMP Step 2 notes the P∩W = ∅ convention of Step 1 (the text at N2031 omits it); proof of (I5) cites Lemma SIMP
instead of (S3); the proof of Prop. `prop:canhyp` now says the loops (Chain, Lemma B, CanLC) are finite; the status
box records that (G) is not used; Remark rem:neu20 became "Three points", and its two references were updated.

### 2.5 Not changed, flagged

* §15 says the new text "has not been independently checked". This report is an internal check, so the phrase stands.
* Table 1 and §15.1 status for Theorem H are unchanged (proof modulo §13, running time a sketch). No upgrade.

---

## 3. Executable check (`docs/redteam-canhyp-check.py`)

* **A.** CanHyp-lite on small groups (S₂≀S₃, S₃≀S₂, C₆, D₆, S₃×C₃, S₄, A₄×S₂) and random sets of 𝔓-strings:
  Steps 0, 1, 2, 3(a), Chain, Luks, Lemma B, Lemma W (with decoding of the canonical linking graph), F2^set, E4.
  Checks (C1), (C2), the left-coset shape and the measure decrease at every recursive call.
  **Clean run:** 0 failures, 4868 recursive calls. **Mutants:** cosets multiplied on the wrong side, no linking
  graph, input-dependent orbit choice in Chain, one branch only in Luks, π omitted in E4, and no complete occupancy at the root
  all fail. Lemma B's input-dependent selection is invisible at this level on these groups and is tested directly (A2).
* **A2.** Lemma B on a diagonal action: ECM property; a position-dependent choice of unbalanced orbit fails on 58/120.
* **B.** Lemma SIMP: Step 1 and Step 3 implemented exactly; (S3), simplicity, complete occupancy, the (S4) total and
  corrected bounds with Step 4 simulated at the worst case of (IV). Old (S4) second half fails on 23/86, corrected on 0;
  dropping Step 3 violates the total estimate on 44 instances (so the test has teeth).
* **C.** Toy CanLC loop (H = S₅ on 10 points, H₀ = S₃×S₂, t = 3, a stand-in for Thm 4.17 renormalization with a
  pseudo-random relabelling seeded from the prefix): ECM property, (I2), (I4′), (I5), and Δ(Z) ≤ Aut. Clean: 0 failures; seeding the
  relabelling from the raw input: 15/20 fail.
* **D.** The counterexample of §2.1.
* **E.** The A_k parity construction of Prop. opt1.

Coverage limits: Steps 3(b)/4 (giant steps) need k > 10t ≥ 90 and are not run in the toy; CanLC in part C uses
t = 3 and a stand-in renormalization. These are structural checks, not a proof.

---

## 4. Edits applied to `paper/canon.tex`

1. Prop. opt1 cost: c_BC bounds both BC and Babai's Thm 2.1. Definitions of c₁ and c₂ added (§8).
2. Before Lemma SIMP: definition of ŝ and its three properties.
3. Lemma SIMP (S4): second bound replaced by ŝ((Z^π)\*,W\*) ≤ ŝ(Z,W); proof written out; note that (G) is not used.
4. Lemma LC, invariants: proof of (I4) and (I5) rewritten; cost sum via ŝ.
5. Lemma AGG (i): |V_j| ≥ 3k/4 − 4, defect on [k].
6. Prop. `prop:canhyp`: finiteness of Chain, Lemma B and CanLC stated.
7. Status box of Theorem H: (G) not used.
8. Remark rem:neu20: third point (the counterexample and the repair); references to it updated.
9. SIMP Step 2: P∩W = ∅ convention.

No status was upgraded. Commit on branch `w13-redteam-canhyp`.
