# Verification of the claimed error in Neuen 2020, Thm 4.17(G)

Branch `w13-verify-neu417`, 2026-11-08. Checks §2.1 of `docs/redteam-canhyp.md` and Remark `rem:neu20`(3).

**Verdict: a real error in the proof, not a misreading and not a statement-level error.** The objects built in the proof of
Thm 4.17 can violate (G), also inside an actual call from Thm 4.24. But the theorem as stated (an existence claim)
is not refuted: (A)–(G) are always satisfiable. The sentence "Thm 4.17(G) is false as stated" was an overclaim. The
main theorem is unaffected; the accounting step that cites (G) needs a one-line repair, and the potential ŝ is correct.

Sources, read only: arXiv:2002.06997 v1 and v2 (the campaign's `r4-sources/w7rt-neuen-abs/`), "N…" = line of the v2
source; ICALP 2020 (LIPIcs.ICALP.2020.88, open access, fetched); survey (Comput. Sci. Rev. 2026). TALG 18(3) 2022 was not
accessed. Check: `docs/verify-neu417-check.py`.

## 1. What (G) says

Thm 4.17 (`thm:simplify-on-window`, N1936; numbered 4.17 in v1 and v2, recomputed from the shared counter). Hypotheses: Γ ∈ Γ̂_d;
𝔓 a Γ-invariant partition; an almost d-ary sequence of Γ-invariant partitions with 𝔓 = 𝔅_i, i ≥ 1; sets 𝔛_i of 𝔓-strings,
completely occupied by the standing assumption (N1036); W Γ-invariant, Γ[W] ≤ Aut(𝔛_i[W]), 𝔛_i[W] = 𝔛_j[W]. Conclusion: **there is**
an equivalence ∼ on [p] and, per class, objects Ω\*, Γ\*, λ_i, φ, W\*, 𝔅\*, 𝔛_i\* with (A)–(G), plus an algorithm in time
p²(n+m)^{O((log d)^c)}.

(G) (N1961): virtual size of 𝔛_i\*[Ω\*∖W\*] ≤ virtual size of 𝔛_i[Ω∖W]. Definitions: 𝔛[A] := {(P∩A, x[A∩P]) : (P,x) ∈ 𝔛, P∩A ≠ ∅}, a
**set** (N1042; strings equal on A collapse); virtual size := Σ_P |P|·m(P)^{f(d)+1} (N1572), with f = f_norm ≥ 0.

"Analogously" (N2141) refers to the proof of (F) (N2115–2139): s\* ≤ s via (IV), and a power-sum estimate on orbits of copies.
Its key identity is m_{𝔛₁}(P) = Σ_{copies P′} m_{𝔛₁′}(P′) (N2130 ff.).

## 2. The counterexample

Γ = 1, Ω = {a,b,c,d}, 𝔓 = {{a,b},{c,d}}, W = {a,c}, sequence {Ω} ≻ 𝔓 ≻ singletons (almost d-ary, as Γ = 1 is semi-regular),
𝔛 = {(ab; 00), (ab; 10), (cd; 00)}, p = 1. Every hypothesis holds; 𝔛[W] is not simple (m({a}) = 2), so the proof does not exit early.

* Before: 𝔛[Ω∖W] = {({b},0), ({d},0)}; both first-block strings restrict to b↦0 and collapse. Virtual size **2**.
* Step 1 (N1974–1985): blocks {a,b}×{a↦0}, {a,b}×{a↦1}, {c,d}×{c↦0}, one string each. 𝔛′[Ω′∖W′] has three
  singleton blocks with m = 1. Virtual size **3**.
* Renormalize (Thm 4.9): Γ″ = 1, so orbits A are singletons, (IV) gives |f′⁻¹(P′)| ≤ 1, f′ is onto by construction (N1518), (III), (V) make f a
  bijection on blocks. So Ω\* ≅ Ω′ and the value stays **3 > 2**, for every f ≥ 0. (F) is fine: 6 ≤ 2·2^{f+1}+2.

The failure of the "analogous" argument is exactly the set reading: the key identity would need m(P∖W) ≥ Σ m(copies), but 𝔛[Ω∖W]
collapses strings that differ only on W.

It also occurs at the call in the algorithm (Thm 4.24, N2176): Γ = Sym(T) on T ⊔ {u,v}, |T| = k = t = 9, d = 10, φ = id, blocks
T∪{u}, {v}, two strings on T∪{u} constant on T with values 0, 1 and agreeing at u. Then W′ = Aff = T, balancing and the window test
leave Γ, and at Simplify the outside virtual size goes 2 → 3, so t_{p+2} ≤ t′ (N2434) and Claim 4.25 fail as written.

## 3. Why the statement itself is not refuted

The theorem quantifies existentially over Ω\*, Γ\*, W\*. Let ∼ be ≅_Γ, fix r ∈ A, take Γ\* := Aut_Γ(𝔛_r), Ω\* := Ω, W\* := Ω, the same sequence,
λ_i ∈ Iso_Γ(𝔛_r, 𝔛_i), and 𝔛_i\* := one constant string per block. Then (A) holds (subgroup, N685), (B), (C), (E) are immediate,
(D) holds since Iso_Γ(𝔛_i,𝔛_j) = λ_i⁻¹ Aut_Γ(𝔛_r) λ_j, (F) holds by complete occupancy (n ≤ s), (G) holds as Ω\*∖W\* = ∅. The algorithmic
clause then follows from the main theorem, so proving the main theorem cannot use this witness; what is needed is (G) for the objects of the proof.
So: **proof error**, located at N2141 and propagated to Claim 4.25 and N2406–2434.

## 4. Repair and effect

ŝ(Y,U) := Σ_Q |Q∖U|·m_Y(Q)^{f(d)+1} is correct (checked against the exact text): (i) ŝ(Y,∅) is the virtual size; (ii) if Y[U] is simple, ŝ(Y,U) =
virtual size of Y[outside U], as strings then differ only outside U; (iii) ŝ(𝔛\*,W\*) ≤ ŝ(𝔛,W) by the (F) computation with |P′| replaced by |P′∖W′|,
which needs only the first half of Claim `respect-block-sizes`; for i ≠ 1 in the class, ŝ(𝔛_i,W) = ŝ(𝔛_1,W) since Γ′ matches the per-block multiplicity sums; (iv) ŝ(Y,U) − ŝ(Y,U∪U′) ≥
virtual size of Y[U′] and ≥ |U′| if completely occupied, for U′ disjoint from U. Equivalently, ŝ is (G) read with the multiplicities of the whole instance, the
reading for which "analogously" is literally true; whether Neuen meant it is the question to ask him.

Effect: replace in N2433–2434 "s_{p+1}+t′ ≤ t_{p+1}, t_{p+2} ≤ t′" by "s_{p+1}+ŝ(ℨ₁′,W∪W′) ≤ t_{p+1}, t_{p+2} ≤ ŝ(ℨ₁′,W∪W′)" (t_i = ŝ on simplified instances, by (I.4)); strictness of N2408 holds likewise. So
Σ s′_i ≤ s and the ≤ s iteration bound survive, and the statement of Thm 4.24 and the main theorem are unaffected. Only an intermediate accounting step changes.
(Side note: the listing's W′ := Aff(Λ,ψ) (N2219) must be read as Aff(Λ,ψ)∖W, as the partition step N2433 requires; `canon.tex` does this.)

## 5. Versions and acknowledgement

(G) is in v1 (statement N1546, "analogously" N1725; the theorem is 4.17 there and the local certificates theorem is 4.20) and v2, and (F), (G) are stated in the ICALP
version as Thm 11. The proof text is unchanged between v1 and v2 apart from presentation. The survey has no erratum or discussion (it only cites [27] as background). Neither arXiv abs page nor v2's
comment mentions a correction.

## 6. Changes

`paper/canon.tex`: Remark `rem:neu20`(3) rewritten as a question to the author, with the Sym(T) instance added and the existence-statement caveat. "False"/"corrects" removed in the note after (S4), the (I4) proof, the
CanHyp status line; question to Neuen extended. `docs/redteam-canhyp.md` keeps its original wording; this memo corrects its "false as stated". `paper/canon.pdf` is not rebuilt.
