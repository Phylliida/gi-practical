# Red team: what the Lean Stage-1 theorem means (w38, branch w41)

Referee question: do the statements in `lean/DegreeD/M/` (`Main.lean`, `Final.lean`, `Axioms.lean`,
`Cited.lean`) mean what `docs/w38-lean-stage1.md` claims? Kernel-checking is not re-done, the only
thing compiled here is the chain of oleans (to scratch, removed) and one scratch non-vacuity file
(appendix A).

## Verdict

| Question | Finding |
|---|---|
| 1. `gnsPrimitive` | **Not found false.** Every case of GNS's proof is either bounded or gives exactly the product form; the normalizer step is correct (proof below, GAP check m ≤ 14). All 15,100 primitive groups of degree ≤ 2500 fit (§1.4). It remains a trusted axiom resting on CFSG literature (Liebeck, Liebeck–Shalev, GSS98, Maróti) that I read but did not re-derive. |
| 2. `bcp` | **True.** Short proof below from Maróti (or Praeger–Saxl) plus an induction; `n = 0` is fine. |
| 3. `GammaHat` | **Correct** for finite groups: matches GNS Def 2.3 by Jordan–Hölder. |
| 4. Hypotheses | **Satisfiable, not vacuous** (new, kernel-checked: `NodeBoundD` for `w ≡ 1`; `Supply P D` for `D ≤ q₀`). `Supply` for `D > q₀` is not built. "Cost" is `Σ_nodes w`, not machine cost. |
| 5. `M.Run` vs HJ | Differs in exactly one constructor guard plus the dispatch step (checked by diff). Correctness is unconditional. `Structural` is a real but non-computed `Prop` guard. |
| 6. English claim | The Lean theorem is a statement about the size of an abstract recursion tree. Five items separate it from "GI of max degree `d` in `n^{O(log d)}` time" (§6). |

No statement was found to be false, vacuous, or mis-parametrized. Two points to fix in the write-up:
§4.4 (`NodeBoundD.work` is strictly stronger than HJ's `NodeBound`; nothing shows HJ's machine meets it) and
§5.3 (HJ's proved recognition does not cover all structural quotients).

---

## 1. Is `gnsPrimitive` true?

`Cited.lean`: `∃ c₁ c₂ ≥ 0, ∀ d ≥ 6, n ≥ 2, G ≤ Sym(n) preprimitive, G ∈ Γ̂_d →
|G| ≤ n^{c₁ log₂ d + c₂} ∨ ∃ m k r e, ProductForm G m k r e ∧ m ≤ d ∧ 2k ≤ m ∧ 4 log₂ C(m,k) < m`,
where `ProductForm` says: every `g ∈ G` acts on `e`-coordinates as `(σ; h_1…h_r)` with `h_i ∈ S_m`
acting on `k`-sets (`e(gx)_i = h_i · e(x)_{σ i}`), and `G` contains every coordinatewise tuple from `A_m^r`.

### 1.1 Going through the proof of GNS Theorem 3.13 (arXiv:1802.04659v3, labels `thm:first-main-theorem`, `la:primitive-size-type-2..5`)

O'Nan–Scott types as in GNS §3.1: every primitive `G` on `n ≥ 2` points is in one of the five types below.

* **Type I (affine).** Option 1 only, via `cor:primitive-size-type-1`: `b(G) = O(log d)` from Liebeck–Shalev 2014 / GSS98 Lemma 4.2 and Lemma `lem:rank:vs:size:d`. Not routed to option 2. **Trust** the citations; the argument for the imprimitive `G_0` is a few lines and reads correctly.
* **Type II (almost simple).** Liebeck 1984 (`thm:large-primitive-almost-simple-classification`): socle `T = A_m^{(t)}`, or `T = A_m` on `b`-partitions, or classical on subspaces, or `|G| ≤ n^9`. The partition case gives `n = 2^{Ω(m)}`, so `|G| = n^{O(log m)}` with `m ≤ d` (Γ̂_d). Classical: `|T| ≤ d'^{1+log d'}` with `d' =` the minimal degree of `T`, `d' ≤ min(d, n)` (Maróti, `T` not Cameron). `A_m^{(t)}` with `m ≤ 4 log₂ C(m,t)`: `|T| ≤ n^{4 log m}`. Otherwise `m > 4 log₂ s`, `G ⊵ T = A_m^{(t)}`, `|G:T| ≤ 2`. Exactly the `r = 1` product form, given §1.2.
* **Type III (diagonal, including k=2/holomorph).** Option 1 only. Elementary re-derivation: `|G| ≤ |T|^k · |Out T| · |K|` with `K ≤ S_k` a quotient of `G` (so `K ∈ Γ̂_d`, BCP: `|K| ≤ d^{k-1}`), `n = |T|^{k-1}`, `k ≥ 2`. So `|T|^k ≤ n²`, `|Out T| ≤ |T| ≤ n`, `k-1 ≤ log₂ n`: `|G| ≤ n^{3 + log₂ d}`. Correct without GSS98.
* **Type IV (product).** `G ≤ P ≀ K`, `P` Type II or III, `K ≤ S_k` the (transitive) image of `G` on the coordinates, a quotient of `G` and so in Γ̂_d, and `Soc(G) = T^k` acts coordinatewise. `|K| ≤ d^{k-1}` (BCP, this is where `d ≥ 6` enters), so `|G| ≤ n^{log d} |P|^k`. If `|P| ≤ |M|^{O(log d)}`, option 1. Otherwise, by the Type III and Type II lemmas, `P` has socle `A_m^{(t)}`, `|P:T| ≤ 2`. If `m ≤ 4 log₂|M|`: `|N| = |T|^k ≤ n^{4 log d}` and `|G| ≤ n^{O(log d)}` (uses `|G:N| ≤ n^{1+log d}`). If `m > 4 log₂ |M|`: `G ≤ S_m^{(t)} ≀ S_k` (§1.2), and `G ⊇ T^k = A_m^k` coordinatewise (this is the O'Nan–Scott statement of the socle). Product form with `r = k` holds. **Correct.**
* **Type V (twisted wreath).** `n = |T|^k`, `G = T^k ⋊ P`, `|P| ≤ d^{k-1}`, `k ≤ log n`: `|G| ≤ n^{1+log d}`. Correct; option 1 only.

**So the proof really does give, for every primitive `G ∈ Γ̂_d`: bounded, or (Type II/IV) `G ≤ S_m^{(t)}≀S_r`, `G ⊇ A_m^r`, `m ≤ d`, `t ≤ m/2`, `m > 4 log₂ C(m,t)`.** This is the product form, with `r = 1` for Type II and `r = k` for Type IV. No other type reaches option 2.

### 1.2 The normalizer step (GNS do not spell this out)

Claim: if `T ≤ Sym(M)` is permutationally `A_m^{(t)}` with `m ≥ 17`, `t < m/2`, and `P ≤ Sym(M)` normalizes `T`, then `P ≤ S_m^{(t)}`, in the same identification of `M` with `t`-sets. Proof: each `p ∈ P` induces an automorphism of `T ≅ A_m` which, since `m ≠ 6`, is conjugation by some `τ ∈ S_m`; then `p · (τ^{(t)})⁻¹` centralizes `T` in `Sym(M)`. The centralizer of the transitive group `T` is `≅ N_T(T_α)/T_α`, and `T_α = (S_t × S_{m-t}) ∩ A_m` is maximal in `T` (the action on `t`-sets, `t < m/2`, is primitive) and non-normal, so self-normalizing; the centralizer is trivial, `p = τ^{(t)}`. ∎

Both hypotheses are forced: `4 log₂ s < m` with `s = C(m,t) ≥ m` gives `m ≥ 17` (`k=1`: `m ≥ 17`; `k=2`: `m ≥ 38`; `k=3`: `m ≥ 61`), and `t = m/2` would give `4 log₂ C(m,m/2) ≥ 4(m - log₂(m+1)) > m`. Checked by GAP for `m = 7..14`, `t ≤ 3` (degree ≤ 364): `N_{S_n}(A_m^{(t)}) = S_m^{(t)}` in all 24 cases, index `|N:A_m| = 2`. Lean's `2k ≤ m` (rather than `<`) is harmless: `k = m/2` cannot satisfy the numeric condition.

**Conclusion of Type IV is exact.** `G ≤ P≀K` and `P ≤ S_m^{(t)}` give `G ≤ S_m^{(t)}≀S_k`; `Soc(G) = T^k` gives the coordinatewise `A_m^k ≤ G`.

### 1.3 Lean edge cases

* `MulAction.IsPreprimitive G (Fin n)`: Mathlib's definition is `IsPretransitive` + "every block is trivial (subsingleton or univ)". For `n ≥ 2` this is exactly "primitive". `G : Subgroup (Perm (Fin n))` acts through the natural action on `Fin n`. ✓
* `n ≥ 2` excludes the degenerate `n = 1` (where only option 1 could be claimed for the trivial group). ✓ `n ∈ {2,3,4}`: only `S_2, A_3, S_3, A_4, S_4`, all absorbed by `c₂`.
* `d ≥ 6`, `Real.logb 2 d` is fine (positive). The bound is monotone in `d`, and it is about any `d` with `G ∈ Γ̂_d`, the strongest instance being the minimal `d(G)`.
* `r = 0`, `k = 0`: forced out by `n ≥ 2` (`|KSet m 0| = 1`, `n = C(m,k)^r`).
* `C(m,k) = 0` cannot occur (`2k ≤ m`); `Real.logb 2 0 = 0` would be vacuous anyway.
* The conventions (`e(gx)_i = h_i e(x)_{σ i}`) are one of the standard forms; since `σ, h` range freely, any form is covered. ✓
* `S_n ∈ Γ̂_n` for `n ≥ 17`: option 2 with `m = n, k = r = 1` (and `4 log₂ n < n` from `n ≥ 17`). `n ≤ 16`: option 1 via constants. ✓

**No degenerate instance refutes the axiom.** Falsity would need an infinite family, since the constants `c₁, c₂` are existential; §1.1 rules them out type by type.

### 1.4 Computation

GAP 4.15 `primgrp`, all **15,100 primitive groups of degree `2 ≤ n ≤ 2500`** (scripts in appendix B). For each `G`: `dlow := max(6, largest prime dividing |G|, m if the socle is alternating A_m)`, a lower bound on the minimal `d` with `G ∈ Γ̂_d`; `R(G) := log₂|G| / (log₂ n · log₂ dlow)`, an upper bound on `(log|G|)/(log n · log d_min)`.

* `R` is unbounded only on the structural family (S_n on points etc., `R(S_2500) = 193`), which is option 2.
* Over all non-structural groups (structural = socle `A_m^r`, `n = C(m,t)^r`, `m > 4 log₂ C(m,t)`): `max R = 2.93` (`A_37` on 2-sets, degree 666; a Cameron case with `m ≤ 4 log₂ s`, i.e. option 1 of the proof). Cameron-shaped groups with `m ≤ 4 log₂ s` reach `R ≤ 2.93`; every other non-structural group has `R ≤ 1.85` (affine `≤ 1.85`, almost simple `≤ 1.30`, diagonal `≤ 0.87`, product `≤ 1.40`).
* The structural/other split uses the socle type and degree (a heuristic for the action, confirmed by the O'Nan–Scott label). Twisted-wreath and compound-diagonal groups do not occur below degree 2500 (the smallest twisted wreath has degree `60^6`), so those types are tested only by the elementary arguments above.
* A finite census cannot settle an asymptotic bound; it is a consistency check. Nothing here contradicts the proof.

**Verdict on Q1.** `gnsPrimitive` is, as far as I can determine, **true**, and the "product form" is exactly what comes out of the proof, in all cases, for all parameters. The trust boundary is: O'Nan–Scott, Liebeck 1984, Liebeck–Shalev 2014 / GSS98 (Type I), Maróti, plus GNS's own proof text. The `d ≥ 6` restriction in the Lean statement is the only quantifier change from GNS's theorem, and only used range.

---

## 2. Is `bcp` true?

`Nat.card G ≤ d^(n-1)` for `G ≤ Sym(n)` in Γ̂_d, `d ≥ 6`. At `n = 0`: `Perm (Fin 0)` is trivial, `1 ≤ d^0 = 1` (natural subtraction `0-1 = 0`). ✓ `n = 1`: same.

Lean's `BCP` assumes `G ∈ Γ̂_d`, which is weaker than BCP's "no composition factor `A_k`, `k > d`" (`le_of_embedsSym_alt`: `A_k ≤ S_d` forces `k ≤ d` by orders, for `d ≥ 2`). Also Γ̂_d is closed under subgroups and quotients (Lemma 2.4 of GNS; `GammaHat.subgroup`, `.of_surjective` are proved in Lean). Sources: GNS Lemma 2.2 quote; Burness–Shalev 2012.12818 quote it as BCP Lemma 2.2 and give a proof for all `d ≥ 2`.

**Self-contained proof** (Praeger–Saxl 1980 `|G| < 4^n` for primitive `G ≠ A_n, S_n`, CFSG-free; or Maróti Cor 1.2 `|G| < 3^n`). Induction on `n`.
1. `n ≤ d`: `|G| ≤ n! ≤ n^{n-1} ≤ d^{n-1}`.
2. `n > d` (so `n ≥ 7`): `G ≠ A_n, S_n` since `A_n ∉ Γ̂_d`.
   * Intransitive, orbits of sizes `n_1, n_2`: `|G| ≤ d^{n_1 - 1} d^{n_2 - 1} ≤ d^{n-1}` (restrictions stay in Γ̂_d).
   * Transitive with a nontrivial block system, block size `k`, `n/k` blocks: `|G| ≤ (d^{k-1})^{n/k} · d^{n/k - 1} = d^{n-1}`.
   * Primitive: `|G| < 4^n ≤ 6^{n-1} ≤ d^{n-1}` for `n ≥ 5` (`4^n ≤ 6^{n-1}` holds at `n = 5`: `1024 ≤ 1296`; `n ≥ 7` here). ∎

GAP census (degree ≤ 2500, 15,100 groups, `d := dlow`, a lower bound on the true `d`): zero violations of `|G| ≤ dlow^{n-1}`. The induction above is also the reason `d ≥ 6` appears.

**Verdict on Q2.** `bcp` is true. It needs only Praeger–Saxl (or Maróti).

---

## 3. Is `GammaHat` the right class?

`GammaHat d X` (`DegreeD/GammaHat.lean`) is an inductive: `X` trivial, or `X/K` simple with `X/K ↪ S_d` (`EmbedsSym d (X ⧸ K)` = injective hom to `Perm (Fin d)`) and `K ∈ Γ̂_d`. GNS Def 2.3: "for `d ≥ 2` the class of all groups whose every composition factor is isomorphic to a subgroup of `S_d`". By Jordan–Hölder the existence of one series with all factors embedded is the same as all series, for finite groups; `gammaHat_iff_sectionsEmbed` proves the equivalent "every simple section embeds", and `GammaHat.subgroup`, `.of_surjective`, `.extension` are proved, not assumed. GNS's `d ≥ 2` caveat is irrelevant (Lean's `d` is used through `max d 6`).

It is Luks's `Γ̂_d`, not BCP's `Γ_d` (which allows large Lie type factors); GNS's remark after 3.13 shows 3.13 fails for BCP's `Γ_d` (`AGL(d,p)`). Note `Z_p`, `p > d`, is **not** in Γ̂_d, matching GNS. Right class for the claim.

**Verdict on Q3.** Correct.

---

## 4. Are the hypotheses vacuous or impossible to meet?

### 4.1 What `degreeD_stage1_ax` says, exactly

There exist `c₁, c₂ ≥ 0` (from `gnsPrimitive`) such that for all parameters `P, cc`, weights `w : Node P → ℝ` and constants `cw, af, cσ ≥ 0` with

`P.Terminating`, `Compat P cc`, `2α ≤ γ`, `AboveBase P cc`, `∀ n > N₀, 4 ≤ n^{(1-γ)/2}`, `2κ + log 9/log 48 ≤ cc.aStar`, `c₁/log 2 + c₂/log 48 ≤ cc.a + cc.aStar/log 2`, `(log q₀!/log 48 + 1)/log 17 ≤ cc.a + cc.aStar/log 2`, `NodeBoundD w cw af`, `af + 1 ≤ cc.a`,

there is `C'` (depending on `P, cc, w, cw, af, cσ`, **not on `d`**) with: for every `d`, every finite `Ω`, every `S : State Ω C` with `S.G ∈ Γ̂_d`, every `Run P .solve S none A` with `RootsOK cσ (max d 6)`:
`A = {g ∈ G | y(g v) = x v ∀ v ∈ dom}` and `A` is empty or a coset of the automorphism group, and
`r.total w ≤ exp(C' · log(8 max(d,6)) · log(s+2))`, `s = S.size = |dom|`.

`Run` and `total` are as described: `Run` is the inductive proof-relevant trace of the recursion, `total` sums `w` over all nodes including all script-call subtrees (`Run.total_eq`). The conclusion is correct as a statement about traces: every branch of the tree is counted.

### 4.2 Numeric conditions

`params_exist`/`params_fit_gns` (`ParamsExample.lean`, kernel-checked) give concrete `P, cc` (HJ's values: `α = 2/5, γ = 9/10, κ = 64, θ = 3/4, β = 9/10, q₀ = 2064, b₀ = 2, a` large, `N₀` large) satisfying every numeric hypothesis, for any given GNS constants. In that instance `P.a = a - 1` and `cc.a = a`, so `af = P.a` meets `af + 1 ≤ cc.a`. **Not vacuous.**

### 4.3 `NodeBoundD` and `w`

`NodeBoundD w cw af` requires, for all nodes of all runs (`Node P` is the sigma type of a run and its parameters):
`0 ≤ w`; if mode ≠ solve, `size ≤ N`, not a row terminal: `w ≤ (1 + fanout)(N+2)^cw`; row terminal: `w ≤ exp(cw log²(N+2))`; solve mode: `w ≤ (s+2)^cw`; `#scriptCalls ≤ N^af`. Here `fanout` is the number of cosets at a dispatcher node, `0` elsewhere.

* **The weight `w` is any function of the node** subject to these bounds: `w ≡ 0` and `w ≡ 1` are allowed. `w` is not tied to any machine. "Cost" is exactly `Σ_{nodes} w(node)`. For `w ≡ 1` it is the **number of nodes of the run**; the theorem is then a bound on the size of the recursion tree.
* `cw` is free (any `≥ 0`), `C'` grows with it (`C₂ = 4cw + 4 + C₁`). `af` must satisfy `af + 1 ≤ cc.a`. Neither depends on `d`. A real implementation must supply a constant `cw`.
* **New, kernel-checked (appendix A):** `nodeBoundD_one : 5 ≤ P.a → NodeBoundD (fun _ => 1) 0 P.a`, axioms `propext, Classical.choice, Quot.sound`. The only nontrivial field is `calls`, ported from HJ's `Run.scriptCalls_le` to `M.Run` in 40 lines. So `NodeBoundD` is inhabited, for `w ≡ 1`, for all `M.Run` nodes, with the numeric instance of §4.2. In particular `calls` is true of every run and need not be a hypothesis (M does not prove this; HJ did).

### 4.4 Is the per-node bound realistic?

`work` is the per-node hypothesis of HJ's §7.4 ("all structural work ... `N^a K_N`"; `TotalCost.lean` docstring), with two changes:

(a) HJ's `NodeBound.work` allows `exp(cw log²(N+2))` at every non-solve node; M requires a polynomial `(N+2)^cw` at every non-row-terminal node, and allows `exp(cw log²)` only at row terminals. This is a **stronger** hypothesis than HJ's. It is what HJ's paper claims (structural work polynomial, Section 7.4), and the row terminal is exactly where the extra cost lives. HJ's Stage-2 budgets have the `expLogSq` shape throughout (w36 §3), so I do not read per-node polynomiality as established there. An actual implementation must prove `w ≤ (1+fanout)·poly` at each non-row-terminal node, including the aggregation node.
(b) It is weakened relative to a flat polynomial by the factor `(1+fanout)`: an enumeration node has `|ρ(G)|` cosets and does `poly` per coset. This is what any implementation does, including the recognition of structural quotients, which is polynomial (see §5).

Per-node work conventions are inherited from HJ: a `.solve` node's `w ≤ (s+2)^cw` depends only on `s = |dom|`, not on `|Ω|`; the work of restricting a group from `Ω` to `dom` and lifting back has to be charged to the (phase-sized) caller. HJ's Stage 2 does this; a Stage-2 for `M.Run` would have to do the same.

So: **`NodeBoundD` is not impossible**; whether a machine implementation meets it is a Stage-2 obligation, not established.

### 4.5 `Supply`

`Supply P D`, used only in the existence statement, has two fields: `cont` (built unconditionally: `contData`) and `giant`, for states in Γ̂_D with labels `L`, `q₀ < L.q`.

* **New, kernel-checked (appendix A):** `supplyOfLe : max D 6 ≤ P.q₀ → Supply P D` and `exists_run_of_le`. For `D ≤ q₀` (in the example, `d ≤ 2064`) `giant` is vacuous: a Γ̂_D state has `L.q ≤ max D 6` (`labels_q_le`), contradicting `q₀ < L.q`. So for `d ≤ q₀` every Γ̂_d state has a run with exact answer and root bounds, unconditionally (modulo Thm A.9's `hσ`, which `degreeD_stage1_full` assumes anyway). No aggregation data is needed in this range.
* For `D > q₀`: not built. HJ's concrete aggregation (`Aggregation.ofLabels`, from the cited `KaryCoherentRefinement, SixTransitive, DesignLemma` and `Params.Aggregates`) has as its only fresh `.solve` queries `cfgQuery` (`AuxConfig.lean:436`; `pairState` on `Sym(C)`, `|C| = n ≤ L.q`), which are in Γ̂_D by `pairState_class` and `labels_q_le`. The rest of the script (certificate, comparison, rectangle queries) is `.cont` (`certPhase_cont`, `comparePhase_cont`; all of `AuxRectQuery` is `mode := .cont`), and row-terminal `Solve` calls are in Γ̂_D (`rowTerminal_calls_class`, proved). So `cls` is true for `Aggregation.ofLabels` by inspection, but the proof is a few hundred lines that was not written. **Neither `Supply P D` for `D > q₀`, nor `Params.Aggregates`/`Params.RowThreshold` for the P of `params_exist`, is established in Lean.** I found no obstruction.

### 4.6 `RootsOK`

Only a hypothesis, but true of the runs that `exists_run_solve` builds (and the proof of `exists_run_aux` provides the bounds for all Γ̂_D states). It bundles: `Finite dom`, root bounds at each fresh phase (`σ ≤ cσ log s`, from Thm A.9, needing cited `AutCardLeSq`, `SimpleValuationDegree`; `Q ≤ log² s`, `h ≤ 2`, ρ bound), and that each `Solve` call of a script has group in Γ̂_D. The last clause means the theorem's bound applies only to scripts whose fresh calls stay in the class; the Stage-2 program must arrange this, see §4.5.

**Verdict on Q4.** No hypothesis is vacuous or unsatisfiable. The numeric conditions and `NodeBoundD` are inhabited (checked). The run-existence part for `d > q₀` needs a `Supply` that has not been constructed.

---

## 5. Does `M.Run` deviate from HJ?

### 5.1 The code change is exactly as claimed

Diff of `GI.Algorithm.Run` (`Procedure.lean`) against `lean/DegreeD/M/Run.lean`: exactly one constructor guard differs, on `normalize`: HJ's `¬ Q.SmallZ P.smallExp` becomes `Structural P Q ∧ ExposedSplit Q`. `I : DispatchStep P S` in `dispatch` is `M.DispatchStep` (same constructors, `enumeration`'s `hsmall : Q.Small P.a` replaced by `¬ Structural P Q ∧ ExposedSplit Q`, `product` gains `ExposedSplit Q`). The rest of `gen.py`'s patches are proof-level: `ClassOK.mult`'s enumeration case replaced by `n_le_multL` from Bounds, cost accounting for `fanout`. These cannot change the meaning of the theorem, because the theorem is about `Run`/`Run.total`, whose definitions are unchanged except above.

* **Correctness is unconditional**: `Run.exact` holds for every `M.Run` (proved; no guard is used), inherited structure from HJ. Correctness of the `Aggregation` and `RowTerminal` abstractions inside a run is the same interface as HJ's.
* **Nothing is hidden in cost**: all work is `w`, and the theorem sums `w` over every node. The only new per-node factor `(1+fanout)` is explicit in the hypothesis.

### 5.2 The dispatcher guard

`Structural P Q` (`Dispatch.lean`): `ρ(G)` is the product action of `S_m ≀ S_r` on `r`-tuples of `k`-sets, containing `Alt(m)^r`, `2k ≤ m`, `q₀ < m`, `m > 4 log₂ C(m,k)`. It is a classical `Prop`. Enumeration is allowed only under `¬ Structural`; structural quotients go to normalization (`r = 1`, `NormChoice`) or product refinement (`r ≥ 2`). This is the rule (M′) of `docs/redteam-theorem-R.md` §9(b) (the corrected structural form, without GNS's `d`-dependent index condition).

It is a **real guard** in the sense that a run must satisfy it: no run exists that enumerates a structural quotient. It is not an assumption that removes the difficulty: the case split is by classical logic, exhaustive for every group (`exists_run_aux`), and the cost bound `enumeration_card_le` derives the needed bound on `|ρ(G)|` from `¬ Structural` via GNS. What the guard does assume away is *decidability in polynomial time*: at this level the test is `Prop`, nothing computes it. A program must decide `Structural` correctly (and recognize the structure `e`) in polynomial time, or at least recognize every structural quotient (soundness of the found `e`, and completeness in the direction: if a quotient is structural the program must find it, else it enumerates and leaves the theorem's scope). This is the Stage-2 recognition task of `docs/w38-lean-stage1.md`.

### 5.3 A concrete Stage-2 gap (recognition)

HJ's proved recognition (`Cited/AlgoCameron.lean`, `Impl/CamFinal.lean`) outputs a Johnson identification only for `m > (k'+1)² − 2`, `k' = min(k, m−k)`; otherwise it outputs `[2]` ("HBD's range is enumerated"). `Structural` is broader: `m > 4 log₂ C(m,k)` allows, e.g., `(m,k) = (2065, 45)` (where `4 log₂ C = 1234 < 2065` but `m ≤ (k+1)² − 2`), so these are structural with `m > q₀ = 2064` but HJ's recognition cannot produce `e`. In the example the guard demands recognition precisely in a range HJ's program does not cover. The fix is GNS Lemma 4.4 (for `m > 4 log₂ s`, citing BLS) or the elementary identification for `m ≥ 3t` in `docs/verify-theorem-R.md` §2.2 (option 2 forces `m > 3t`). This is a Stage-2 obligation only, and not an error in the Stage-1 statement.

**Verdict on Q5.** `M.Run` is a faithful, minimal modification of HJ's `Run`. Correctness is unaffected, and no cost is hidden in the proof. `Structural` is a genuine, but non-computed, guard.

---

## 6. Relation to the English claim

Claim: *GI of graphs with maximum degree `d` is solvable in time `n^{O(log d)}`.*

**Machine-checked (Lean kernel, axioms standard + `bcp` + `gnsPrimitive`):**

> There are absolute `c₁, c₂` such that for every choice of the (explicitly satisfiable) numeric parameters and every weight `w` meeting the per-node bound `NodeBoundD` (e.g. `w ≡ 1`), there is `C'` such that, for every `d`, every state `S` on a finite set of positions whose group lies in `Γ̂_d`, and every run `r` of the abstract recursion `M.Run` on `S` with the phase-root bounds `RootsOK`: the output of the run is exactly the transporter set `{g ∈ G | y∘g = x on dom}`, and `Σ_{nodes of r} w ≤ exp(C' · log(8 max(d,6)) · log(|dom|+2))`, with `C'` independent of `d`.

With `w ≡ 1` this says that the recursion tree of `Solve` has `(|dom|+2)^{O(log d)}` nodes. That is a real and non-trivial theorem of the analysis (the row-by-row charging with weight `Λ = log(8 max(d,6))`, including the (H2) regrouping).

**Not machine-checked** (the gap to the English claim):

1. **It is a statement about traces, not a program.** `M.Run` is an inductive relation: a run is a completed tree with all choices and side conditions already supplied (the primitive quotient, `Structural`, coset representatives). There is no algorithm, and no machine model. Nothing proves an implementation produces a run, let alone that a run's `Structural` is decidable in polynomial time (§5.2).
2. **`w` is not time.** `Σ w` is machine cost only under a Stage-2 theorem that a program has per-node work `≤ (1+fanout) poly(N)` (plus row terminals), i.e. `NodeBoundD` for real work. HJ's Stage 2 does not provide this shape (§4.4). The work of `dispatch` at a node includes the socle/Johnson recognition of `Structural` (Kantor–Luks, BLS/GNS 4.4; HJ's recognition covers only part of the range, §5.3).
3. **Run existence for `d > q₀` requires `Supply`,** which requires the cited aggregation results and the `cls` lemma (§4.5); neither is in `lean/DegreeD/`. For `d ≤ q₀` existence is complete (`exists_run_of_le`, appendix A).
4. **The reduction GI(max deg `d`) → string isomorphism with a group in Γ̂_d** (Luks 1982, GNS Thm 8.1) is not formalized at all. English "degree `d`" means this reduction composed with the above.
5. **The trusted inputs** are `bcp` (true, §2) and `gnsPrimitive` (no refutation found, §1), plus, for run existence, Thm A.9's `AutCardLeSq` and `SimpleValuationDegree` (hypotheses of `degreeD_stage1_full`, axioms in HJ's tree), and all of HJ's correctness interface. (H0) is inherited in the sense that the script-level correctness of `Aggregation`/`RowTerminal` is an interface, kernel-checked within HJ's development.

There is **no statement in `lean/DegreeD/` about graphs, about running time, or about a machine**. Even granting items 1–5, the numeric statement matches the English claim: with `s = O(n²)` positions, `(s+2)^{C' log(8 max(d,6))} = n^{O(log d)}` for `2 ≤ d ≤ n`.

---

## Appendix A: scratch non-vacuity checks (kernel-checked)

`Redteam.lean` (not committed to the Lean tree; it imports the compiled development). `#print axioms`: `nodeBoundD_one`, `supplyOfLe`, `exists_run_of_le` each depend on `[propext, Classical.choice, Quot.sound]` only.

```lean
import DegreeD.M.Main
import DegreeD.M.Existence
import Workspace.Paper.ScriptCalls

namespace GI.DegreeD.M
open Equiv Equiv.Perm GI.Algorithm GI.Paper
open scoped Pointwise
variable {P : Params}

/-- `M`-version of `GI.Algorithm.Exec.calls_length`. -/
theorem Exec.calls_length' {α : Type} {s : Script α} {a : α} (e : Exec P s a) :
    e.calls.length = s.numCalls := by
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun s _ e => e.calls.length = s.numCalls)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?done ?ask e
  case done => intro α a; rfl
  case ask =>
    intro α Ω' C' m S k A a r e' _ ih
    have hA : A = S.answer := r.exact
    subst hA
    change (e'.calls.length + 1) = 1 + (k S.answer).numCalls
    omega

-- `Run.scriptCalls_le'`: verbatim HJ proof with `Exec.calls_length'` (see w41 scratch).

theorem nodeBoundD_one (ha : 5 ≤ P.a) :
    NodeBoundD (P := P) (fun _ => (1 : ℝ)) 0 P.a where
  nonneg _ := zero_le_one
  work nd _ _ _ := by
    have h : (0 : ℝ) ≤ (nd.run.fanout : ℝ) := Nat.cast_nonneg _
    simp only [Real.rpow_zero, mul_one]; linarith
  rowTerminal nd _ _ _ := by simp [expLogSq]
  solve nd _ := by simp
  calls nd _ hsz := Run.scriptCalls_le' ha nd.run hsz

noncomputable def supplyOfLe (hP : P.Terminating) (hγ : 0 ≤ P.γ) {D : ℕ}
    (hD : max D 6 ≤ P.q₀) : Supply P D where
  cont S hinv hN _ htr hs _ := contData hP hγ S hinv hN htr hs
  giant S _ _ _ _ _ L hq hg := absurd (labels_q_le hg L) (by omega)

theorem exists_run_of_le (hP : P.Terminating) (hγ : 0 ≤ P.γ) {cσ : ℝ}
    (hσ : ∀ (V : Type) [Fintype V] (H : Subgroup (Perm V)) (v : V),
      (GI.sigma P.κ v H : ℝ) ≤ cσ * Real.log (Fintype.card V))
    (hcσ : 0 ≤ cσ) {D : ℕ} (hD : max D 6 ≤ P.q₀) {Ω C : Type} [Finite Ω]
    (S : State Ω C) (hg : GammaHat D S.G) :
    ∃ r : Run P .solve S none S.answer, r.RootsOK cσ D :=
  exists_run_solve hP hσ hcσ (supplyOfLe hP hγ hD) S hg

end GI.DegreeD.M
```

`#print axioms` on `degreeD_stage1` (standard three) and `degreeD_stage1_ax`, `degreeD_stage1_axioms` (+ `bcp`, `gnsPrimitive`) was re-run and matches w38.

## Appendix B: scripts

GAP 4.15.1, `primgrp`. Census (`scan.g`): for all `n ≤ 2500`, all `i ≤ NrPrimitiveGroups(n)`, print `n, i, ONanScottType, SocleTypePrimitiveGroup (series, parameter, width), LogInt(Size,2), max prime divisor of Size`; `dlow = max(6, pmax, m if socle series "A")`; `R = log₂|G|/(log₂n · log₂dlow)`, and test `log₂|G|+1 ≤ (n-1) log₂ dlow`. Normalizer check: `Normalizer(SymmetricGroup(C(m,t)), Action(AlternatingGroup(m), Combinations([1..m],t), OnSets))` equals the action of `SymmetricGroup(m)`, for `m = 7..14`, `t ≤ 3`.
