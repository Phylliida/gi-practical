# Red-team report on Theorem R (memo §4.1) and its verification

Branch `r4-redteam`, 2026-11-04. Target: `docs/moonshot-theory.md` §4.1 (L493–570) and
`docs/verify-theorem-R.md` (the first verifier's report, "VR" below), which claims:

> **Theorem R\*.** HJ with dispatcher (M′) solves string isomorphism for $G\in\hat\Gamma_d$ on $N$
> points in $\exp(O(\log(N+2)\log(d+2)))\cdot\mathrm{poly}$ time, so graph isomorphism of maximum
> degree $d$ is in $n^{O(\log(d+2))}$, conditional only on (H0) = "HJ's algorithm and analysis are
> correct".

**Sources.** "L…" is a line of HJ's `graph_isomorphism.tex` (arXiv:2611.01399v1, the only version,
submitted 2026-11-01). "G…" is a line of GNS's `bounded-degree-polylog-d.tex` (arXiv:1802.04659v3).
Lean files are under `~/math/GraphIsomorphismLog2/Workspace` and were read only, never built.
New downloads went into fresh directories under `scratchpad/r4-sources/`, were read only, and
were converted to text with a script kept outside those directories:

* `burness-shalev-2012.12818/`: Burness–Shalev, *Permutation groups with restricted stabilizers*.
* `maroti-thesis/`: A. Maróti, doctoral thesis (Szeged).
* `grohe-neuen-2011.01366/`: Grohe–Neuen, *Recent advances on the graph isomorphism problem*.

**Bottom line.** I found **no hole outside (H0)**. Every attack below either checks out or turns
up only a minor or cosmetic defect, and each defect has an easy fix (§9). The real risk is
concentrated in (H0) itself, specifically in HJ's σ-budget mechanism (§7).

---

## 0. Verdicts

| # | attack | verdict |
|---|---|---|
| 1 | Lemma 7.1 with $\Lambda$ in place of $x$ | **sound.** Every use of $x\ge\gamma\log N$ is either removed by the (H2) regrouping or was slack. Node tolls are paid by the prefactor $(s+2)^D$, never by $\Phi$. Explicit inequalities in §1.3. |
| 2 | (H2) disjoint families | **sound.** Lean `branch_disjoint` is literally "sum of child sizes ≤ parent size". Window and comparison calls are on increments disjoint from the current window (Lean confirms). Many children of size $s/\kappa$ cause no problem. |
| 3 | constants, all $d$ | **sound.** The constant $A$, not $\Lambda$, absorbs the $2\kappa$. All inequalities hold uniformly because $\Lambda\ge\log 48$. For $d\le q_0$ there are no giant steps at all. |
| 4 | GNS Thm 3.13 | **sound.** The base of the bound is the primitive degree $d'$. The exponent's $d$ is any $d$ with $P\in\hat\Gamma_d$. It applies to every primitive quotient HJ exposes. $c_1,c_2$ are not explicit. |
| 5 | closure of $\hat\Gamma_d$ | **sound.** |
| 6 | BCP Lemma 2.2 | **sound, with a better citation.** Two independent faithful restatements were found, plus a stronger published composition-factor version (Maróti, Cor. 1.5). |
| 7 | prior art | **none found.** No $n^{O(\log d)}$ bound anywhere. The literature names exactly the obstacle that HJ's σ-budget claims to bypass. |
| 8 | sanity limits | **no contradiction.** The bound sits exactly at the "enumeration floor" $d'^{\Theta(\log d)}$ of Luks-type recursion. |
| — | VR itself | three minor errors and one wording gap (§9), all fixable in a line. |

---

## 1. Attack 1: the potential induction with $\Lambda$

### 1.1 What the induction uses

HJ's Lemma 7.1 (L1643–1716), formalized as `GI.Paper.PhaseTree.Hyp`
(`Paper/RunningTime.lean` L197–242), needs four things.

1. **Node toll.** Every internal node costs $\le N^aK_N+\sum$children (`toll`, L213–214). This is
   paid by $W\ge(s+2)^D\ge N^{\gamma D}\ge2N^a$ (L1682–1686, L1840–1844). It uses only
   $s>N^\gamma$ and $\Phi\ge0$. **$\Phi$ plays no role here**, so replacing $x$ by $\Lambda$ inside
   $\Phi$ cannot affect it.
2. **Pure orbit nodes.** Here $W-\sum_jW_j\ge e^{\Phi}\,[(s+2)^D-\sum(s_j+2)^D]\ge N^a$
   (L1697–1706, eq. main-orbit-slack L1583–1589). Again only the prefactor is used. The one
   $\Phi$-dependent item is the $h$-reset of a later child (L1596–1598, Lean `OrbitChild`
   L192–193). With $\Phi_\Lambda$ it is paid by $A\Lambda\log\frac{s+2}{s/2+2}\ge A\Lambda\log\frac85\ge2B$.
3. **Charged nodes.** Children are grouped into $\le J$ classes. Each class needs
   $\mathcal M e^{-\Delta\Phi}\le1/(8J)$, where $\mathcal M$ is the number of branches and every
   child in every branch has drop $\ge\Delta\Phi$. Each branch must also have
   $\sum s_{\text{child}}\le s$ (L1668–1684; Lean `class_mult`, `branch_disjoint`, `branch_child`).
4. **Root bound.** $W(\text{root})$ (L1708–1715).

### 1.2 Every place HJ uses $x\ge\gamma\log N$ to pay an $N^a$

I searched L1416–1848 for uses of $x$ beyond the $x^2$ domain charge. There are exactly three:

* **L1795–1798.** The physical and symmetry rows have "logarithmic multiplicity at most $a_*x$"
  (via eq. main-phase-active, L1468–1472). This is the only *essential* use. The $N^a$ counts the
  $\le s$ window updates per test (L2720: "The multiplicity absorbs the at most $n$ updates"). The
  (H2) regrouping replaces it by a $q$-only family count (§2).
* **L1800–1806 (enumeration) and L1808–1812 (product).** The $a_*x$ term pays an $N^a$ that HJ
  calls "harmless upper bounds" (L1557–1558). In Lean the dispatcher class has **one branch per
  coset** (`Algorithm/PhaseTree.lean` L32–33, L474). So the true multiplicity is $|P|$ or
  $|P:\text{Soc}|$, with no $N^a$.

The other polynomial-in-$s$ or $N$ factors:

* window updates ($\le s$), orbit-chain leaves ($\le s$), comparisons ($\le s$ updates each):
  regrouped into families (§2);
* configuration fresh calls ($\le2q^{\kappa+1}$ per node, each on $\le q^2<N^\gamma$ positions):
  terminal oracle work inside $N^aK_N$ (L1635–1641), paid by the prefactor;
* CombineExact / LiftAndContinue bookkeeping, P_T and A_i computations, coherent refinement,
  constructive membership: structural, polynomial in $N$, inside the toll. Lean confirms that the
  certificate and comparison scripts ask only `Continue` (`Paper/ScriptCalls.lean` L13–17).

None of these touch $\Phi$.

### 1.3 Row-by-row inequalities for $\Phi_\Lambda$

Notation:

* $\Phi_\Lambda=A(\Lambda x+\Lambda\rho+\Lambda\sigma+Q_d)+Bh$ and $W=(s+2)^De^{\Phi_\Lambda}$.
* $\Lambda=\log(8\tilde d)$ with $\tilde d=\max(d,6)$. I use 8 rather than VR's 4 so that both
  readings of BCP are covered (§6).
* $q\le d$, so $\log q\le\Lambda$, and $\Lambda\ge\log48$. $H_*=2B+\log(8J)$.
* HJ's sample constants are $\kappa=64$, $\theta=3/4$, $\beta=9/10$ (L1820–1823).

Each condition below is "$\log\mathcal M+H_*\le\Delta\Phi+2B$".

| class | branches $\mathcal M$ (true count) | drop of every child | sufficient condition |
|---|---|---|---|
| affected: affected-type certificate and comparison families, large-symmetry chains, intransitive normalization | $\le2\,(2q^\kappa+4q^{2\kappa}+6q^{\kappa+1})\le32q^{2\kappa}$ (×2 normalization cosets included) | $s'\le\theta s$, so $\ge A\Lambda c_\theta-2B$ (eq. main-domain-payment, first part, L1485) | $Ac_\theta\ge2\kappa+(\log32+H_*)/\log48$ |
| unaffected: extra-type families | $\le2\,(2q^\kappa+4q^{2\kappa})\le12q^{2\kappa}$ | $\sigma'\le\sigma-\kappa$, so $\ge A\Lambda\kappa-2B$ (L2700–2704) | $A\ge2+(\log12+H_*)/(\kappa\log48)$ |
| product refinement, $k\ge2$ | $\lvert P:A_m^k\rvert\le2^k\lvert K\rvert\le2^k(\tilde d+1)^{k-1}$, so $\log\mathcal M\le(k-1)\Lambda$ | $\rho'\le\rho-(k-1)$, so $\ge A(k-1)\Lambda-2B$ (L3060–3061) | $A\ge1+H_*/\log48$ |
| enumeration, GNS option 1 | $\lvert P\rvert\le d'^{\,c_1\log d+c_2}$, so $\log\mathcal M\le c'\Lambda\log d'$ | $s'\le s/d'$, so $\ge\frac A3\Lambda\log d'-2B$ ((s+2)/(s/d'+2) ≥ d'^{1/3}, L1498) | $\frac A3\ge c'+H_*/(\log2\cdot\log48)$ |
| enumeration, structural option 2 with $m\le q_0$ | $\le(q_0!)^k(\tilde d+1)^{k-1}$, $d'\ge17^k$ | same | $\frac A3\ge\frac{\log q_0!/\log48+1}{\log17}+\frac{H_*}{\log2\cdot\log48}$ |
| continuation (LiftAndContinue) | $\le2q^{\kappa+1}$ (Lean `overs_length_le`, `Algorithm/Aggregation.lean` L583) | $Q_d'\le Q_d-c_\beta\log q$ (L1522–1531) | HJ's (main-constant-cap) L1786, unchanged, no $N$ |
| row events | do not occur ($q\le d\le\lambda$) | — | — |

Where the counts come from:

* $2q^\kappa$ endpoint families: string × test × coset image × type.
* $4q^{2\kappa}$ comparison pairs.
* $3\cdot2q^{\kappa+1}$: the large-symmetry calls. Items number $q^{\ell}$ with $\ell=\kappa+1$
  (`Aggregation.lean` L133, L417), with $\le3$ calls each (`ScriptCalls.lean` L145).

Each child in each row also satisfies $\rho'\le\rho$, $\sigma'\le\sigma$, $Q'\le Q$ and
$h'\le h+2$. These hold under subgroup and orbit restriction (L1434–1439, L671–674, L3046–3049).
So the $-2B$ in each drop is the only slack spent on resets.

**Verdict on attack 1: sound.** All inequalities hold for one absolute $A\approx2\kappa/c_\theta+O(1)\approx10^3$.

---

## 2. Attack 2: (H2), the disjoint families

**The Lean hypothesis.** `branch_disjoint` (`RunningTime.lean` L228–229) is
`((b.map fun u => (T.state u).s).sum) ≤ (T.state v).s`. `branch_child` (L231–232) asks each child
to satisfy its row's `Child` relation. Lemma 7.1's proof uses exactly
$\sum_{u\in b}(s_u+2)^D\le(s+2)^D$ from these (L1670–1676). So a branch may be **any** set of
children with total size $\le s$ that all satisfy one row. VR's reading is correct.

**Lean's own branches are finer.** `callBranches` (`Algorithm/PhaseTree.lean` L440–447) makes one
branch per `Continue` call. It splits the call's orbit-forest leaves at size $\theta s$ (not by
update type), and Lean bounds the count by $N^a$ (`Aggregation.lean` L553–602:
$2\binom q\kappa s\kappa!+4q^{2\kappa}s+3q^{\kappa+1}\le N^a$). The regrouping is a change of
*analysis*, not of the algorithm.

**Disjointness across updates, checked in Lean.**

* `increment` (`CertificateEndpoint.lean` L214–218) is either `affectedSet` or `extraSet`, both
  filtered by `v ∉ W` (L190–196). `stage` sets $W_{t+1}=W_t\cup V_t$ (L222–227).
* `windowCall` (`Algorithm/Certificates.lean` L295–300) queries domain $V$ only, once per coset
  representative (`checkNewWindowLift` L332–341). `endpointScriptLift` passes exactly the
  increment (L375–383).
* The comparison update `lockstepStepLift` (`Algorithm/ComparisonPhase.lean` L105–110) makes one
  call under $N_j$ on `inc … x j` = $V_j$.

So for fixed (string, test, coset index, type), or (comparison pair, type), the leaves across all
updates lie in pairwise disjoint subsets of $\Omega$. Coset index means any injective labelling
of the $\le\kappa!$ cosets at each update, for example by the image in $\mathrm{Alt}(T)$.

**Type split versus size split.** VR splits families by update type; Lean splits by leaf size.
Both satisfy `Child`:

* affected-type leaves have size $\le\lvert\Delta\rvert/\kappa\le\theta s$ (L2686–2689);
* extra-type leaves always have $\sigma'\le\sigma-\kappa$ (L2700–2704; later leaves of the same
  chain lie in other extra orbits $\Delta'$ of the same $V_i$, each passing the test of L2639–2640).

**Many children of size $\sim s/\kappa$, with $\Lambda$ unchanged.** This is harmless. Each child
has $\Phi_{\text{child}}\le\Phi-A\Lambda(x-x_{\text{child}})\le\Phi-A\Lambda c_\theta$, since
$\rho,\sigma,Q_d$ are only inherited upper bounds. The prefactors of up to $\kappa$ children of
size $s/\kappa$ sum to $\le(s+2)^D$. The fact that $\Lambda\rho$ and $\Lambda\sigma$ do not shrink
with $x$ is irrelevant: HJ's own induction never uses the shrinkage of $\rho x$ or $\sigma x$
either. Sequential dependence (later windows depend on earlier answers) does not matter, because
the induction runs over the finite execution tree.

**Verdict on attack 2: sound.**

---

## 3. Attack 3: does a halving child pay $q^{O(\kappa)}$, for all $d$?

A child with $s'\le s/2$ drops $A\Lambda\log\frac{s+2}{s/2+2}\ge A\Lambda c_\theta$. The family
count is $\le32q^{2\kappa}$, so $\log\mathcal M\le2\kappa\Lambda+\log32$.

The condition is $A c_\theta\ge2\kappa+O(1)/\Lambda$. The constant $2\kappa$ is absorbed by the
coefficient $A$, not by $\Lambda$; one never needs $\Lambda\gg\log d$ by a specific factor. Since
$\Lambda\ge\log48$ uniformly, the same $A$ works for every $d\ge1$.

Small $d$ is covered too:

* If $d\le q_0$, no giant step occurs, because a giant needs $q>q_0$ (L1766–1773) and $q\le d$.
  The algorithm is then pure enumeration plus product refinement. Option 2 with $m>q_0$ is
  impossible since $m\le d$. Every $\lvert P\rvert$ is $d'^{O(1)}$, which gives $N^{O(1)}$, consistent
  with Luks.
* If $d\le2$, the claim should read $n^{O(\log(d+2))}$, not $n^{O(\log d)}$ (§9).

**Verdict on attack 3: sound.**

---

## 4. Attack 4: GNS Theorem 3.13

I read the statement and the full proof (G864–928) and its inputs (G762–822).

* **Which degree.** "$\lvert G\rvert\le n^{c_1\log d+c_2}$", where $n=\lvert\Omega\rvert$ is the
  degree of the **primitive group itself**. For HJ that is the quotient degree $d'$.
* **Which $d$.** The class parameter: any $d$ with $G\in\hat\Gamma_d$. Since $P$ is a quotient of
  a subgroup of the input group, $P\in\hat\Gamma_d$ for the input's $d$ (GNS Lemma 2.4, G400–408).
  The quotient's own $\mathrm{cw}(P)\le d$ would give an even smaller exponent.
* **Constants.** $c_1,c_2$ are absolute and not explicit. They come from GSS98, Liebeck–Shalev,
  Maróti and BCP.
* **Small $d$.** The proof uses BCP Lemma 2.2, which needs $d\ge6$, even for smaller $d$
  (G789, G809). That is harmless: apply the theorem with $\tilde d=\max(d,6)$, since
  $\hat\Gamma_d\subseteq\hat\Gamma_6$.
* **Scope.** It applies to every primitive quotient HJ exposes. HJ's $P$ is by construction the
  faithful image of the current transitive group on a block system that is maximal under the
  tower (L1153, L3177–3183), and it is primitive. Nothing more is required.

**What option 2 actually says.** Option 2 is a socle condition plus an index bound,
$\lvert G:N\rvert\le n^{1+\log d}$ (G884–918). It is not "large order". The proof also shows the
following for any primitive $G\in\hat\Gamma_d$ that does **not** have socle
$(A_m^{(t)})^k$ in product action with $m>4\log_2\binom mt$: $G$ falls in option 1 (types I,
III and V; type II/IV with non-Johnson socle; or Johnson socle with $m\le4\log_2\binom mt$).

**Verdict on attack 4: sound.** One wording consequence is in §9(b).

---

## 5. Attack 5: closure of $\hat\Gamma_d$

Every recursive group is a subgroup of a faithful orbit image of a subgroup of the input.

* Certificate kernels $N_i$, groups $A_i$ and transporter cosets: L2621–2647, L2737–2741.
* Large-symmetry groups $H,H_0,K=\pi^{-1}(\cdot)$: L2896–2908.
* Normalization preimage of $\mathrm{Alt}$: L1157, L1195.
* Product-refinement preimage of $A_m^k$.
* Overcoset lifts into the frozen $G_0$: L1077–1082, L3201–3207.
* Threshold fresh calls on faithful images: L568–571.

All of these lie in $\hat\Gamma_d$ by GNS Lemma 2.4.

**Configuration fresh calls** run on $\mathrm{Sym}(C)$ acting on $C^2$, with $\lvert C\rvert\le q$
(L1065–1066). $\mathrm{Alt}(\Gamma)$ is a quotient of $G_0\in\hat\Gamma_d$, so it lies in
$\hat\Gamma_d$. Its only composition factor $\mathrm{Alt}(q)$, with $q>q_0\ge258$, then embeds in
$S_d$. The minimal degree of $A_q$ is $q$, so $q\le d$ and $\mathrm{Sym}(C)\in\hat\Gamma_d$.

**Phase regime of those calls.** Such a call has $N'=\lvert C\rvert^2$ and class parameter
$\lvert C\rvert=N'^{1/2}>N'^{\alpha}$. So it always runs in the "HJ verbatim" regime, at cost
$\exp(O(\log^2N'))=\exp(O(\log N'\log d))$ because $\log N'\le2\log d$. The recursion closes; VR
did not say this explicitly.

The overcoset $E\subseteq\mathrm{Sym}(\Gamma)$ (Young groups, extensions, parity: L907–916,
L3123–3126) is never recursed on. It is only lifted.

**Verdict on attack 5: sound.**

---

## 6. Attack 6: BCP Lemma 2.2

The original (J. Algebra 79 (1982) 161–168) is paywalled; the earlier download in `bcp1982/`
holds only a redirect page with no article text. I found three independent sources.

* **Maróti's doctoral thesis**, §1 (text lines 115–122): "Babai, Cameron, Pálfy [4] showed that a
  subgroup of $S_n$ that has no composition factors isomorphic to an alternating group of degree
  greater than $d$ ($d\ge6$) has order at most $d^{n-1}$." This is the **same hypothesis as GNS's
  quote** (G384–389).
* **Maróti's thesis, Corollary 1.5**, a stronger version with the composition-factor hypothesis:
  "Let $G$ be a permutation group of degree $n$, and let $d$ be an integer not less than 4. If $G$
  has no composition factor isomorphic to an alternating group of degree greater than $d$, then
  $\lvert G\rvert\le d!^{(n-1)/(d-1)}$." Since $d!\le d^{d-1}$, this gives $\le d^{n-1}$. I believe
  this is Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002); I did not confirm
  the numbering in the journal version.
* **Burness–Shalev** (arXiv:2012.12818v3, L86–87 and Lemma 2.2 at L134–145) restate BCP as
  "if $d\ge6$ then $\lvert G\rvert\le d^{n-1}$ for every permutation group $G\in\Gamma_d$ of degree
  $n$". Here their $\Gamma_d$ is "**no section** isomorphic to $A_d$", a different reading. Their
  own Lemma 2.2 gives $\lvert G\rvert<d^{n-1}$ for $d\ge2$, and their proof sketch (orbits, blocks,
  primitive case) is visible in the text.

**Application to the top group $K\le S_k$.** $K$ is a quotient of $P$, so $K\in\hat\Gamma_d$.

* By the composition-factor reading (GNS, Maróti), $\lvert K\rvert\le\tilde d^{\,k-1}$.
* $K$ has no $A_{d+1}$ section, because every simple section of a $\hat\Gamma_d$ group embeds in
  $S_d$. So by the Burness–Shalev reading, $\lvert K\rvert<(d+1)^{k-1}$.

Either way $\log\lvert K\rvert\le(k-1)\log(\tilde d+1)$, which is covered by $\Lambda=\log(8\tilde d)$
(§1.3).

**Verdict on attack 6: sound.** The hypothesis matches. Cite Maróti Cor. 1.5 or Burness–Shalev
Lemma 2.2 in addition to BCP.

---

## 7. Attack 7: prior art and known obstructions

**Searched.**

* Web searches (standard and extended) for $n^{O(\log d)}$ with degree $d$, "composition width"
  with an improved exponent, 2024–2026 follow-ups, Neuen's thesis, and HJ follow-ups.
* GNS's introduction and conclusion (G140–200, G2257–2280): they ask only for $n^{\mathrm{polylog}\,d}$
  and leave open FPT. They state no $O(\log d)$ question.
* Babai arXiv:1512.03547 (`main.tex`): no degree-$d$ bound; L353 mentions Luks only.
* Grohe–Neuen survey 2011.01366, §4.4 and open questions (text L1043–1080, L2108–2125).
* Neuen's 2026 survey (Thm 4.6, Cor 4.7, Q4.8): still $n^{\mathrm{polylog}(d)}$.
* HJ L196–300: cite GNS; no degree corollary. HJ's abstract mentions no degree parameter.

**Result.** No $n^{O(\log d)}$ bound is stated anywhere. GNS's own proof gives
$c\ge3$ ($2^{O(\log^3d)}$ recursion nodes, G2133–2136), plus a domain blow-up
$n^{O(\log^2d)}$. So the corollary would be a genuine improvement. HJ v1 is three days old, so no
one else has had time to derive it.

**Known obstruction.** Grohe–Neuen (2011.01366, §4.4) say the following. To get the desired
running time for $\hat\Gamma_d$, one wants certificates of size $t=O(\log d)$. Babai's Local
Certificates Routine needs the Unaffected Stabilizers Theorem with $t>\max\{8,2+\log n\}$, and
"the natural variant of the Unaffected Stabilizers Theorem (where we restrict the input group to
be in $\hat\Gamma_d$ and update the bound on $t$ as desired) does not hold (see, e.g., [Neuen's
thesis, Example 5.5.10])." GNS get around this only partly, by normalization, which costs them
polylog.

HJ use **constant** $t=\kappa=64$ for *all* groups. They replace the Unaffected Stabilizers
threshold by the extra-orbit rule plus the σ-budget (L2615–2617, Theorem A.9 at L2474–2486). So
Theorem R\* is, in effect, the statement "HJ's σ mechanism overcomes the known obstruction".

* This is **not** a contradiction: the obstruction is a counterexample to one lemma, not a lower
  bound.
* But it means the corollary rests most heavily on the most novel part of HJ. If Theorem A.9 or
  the extra-orbit rule fails, Theorem R\* fails with it, and so does HJ's own $\log^2$ result.

No lower bound for Luks/Babai-type recursions is known (memo §3.5 agrees).

**Verdict on attack 7:** new relative to everything found; the risk is concentrated in (H0)'s
σ-budget.

---

## 8. Attack 8: sanity limits

* **$d=O(1)$:** $n^{O(1)}$, matching Luks. **$d\ge n^{\varepsilon}$:** $n^{O(\log n)}$, matching HJ.
* **$d=\mathrm{polylog}\,n$:** $n^{O(\log\log n)}$, versus GNS's $n^{(\log\log n)^c}$ and
  Babai–Kantor–Luks's $n^{O(d/\log d)}$. Nothing known contradicts this.
* **A floor from below for this algorithm class.** Primitive $\hat\Gamma_d$ groups of order
  $d'^{\Theta(\log d)}$ exist, for example $\mathbb F_2^{\,k}\rtimes S_{k+1}$ on $d'=2^k$ points
  with $d=k+1$. A Luks-style recursion that enumerates them pays $d'^{\Theta(\log d)}$ per level,
  and iterating gives $N^{\Theta(\log d)}$. So the claimed bound sits exactly at the natural floor
  of the method; it does not beat it.
* **Problems believed hard.** Tournament isomorphism, $p$-group isomorphism and general GI do not
  reduce to small-cw string isomorphism. Odd-order groups have prime composition factors $C_p$
  with $p$ up to $n$, and $\mathrm{GL}(k,p)$ sections are not in small $\hat\Gamma_d$. So no
  intermediate regime yields a too-good-to-be-true consequence.

**Verdict on attack 8: no contradiction.**

---

## 9. Defects found in the verifier's report (VR)

None of these affects the theorem.

**(a) Numeric error, minor.** VR §2.2 and §2.3 say that for $t\approx\sqrt m$ and $m\ge300$, HJ's
exceptional range ($m\le(t+1)^2-2$) lies inside GNS option 2. That is false at $m=300$: there,
option 2 forces $t\le13<16.4$, so HBD's construction covers every option-2 group. I computed
directly that the first overlap is at $m=509$ ($t=22$); for $t=\lceil\sqrt m\rceil$ it is at
$m=557$. The qualitative point (HJ's enumeration of that range overspends for large $m\le d$, so
(M′) is needed) stands, since $d$ is unbounded.

**(b) Wording gap in (M′), minor; the fix is already implicit.** VR §4.0 defines (M′) as
"enumerate unless P is **GNS-option-2** with $m>q_0$". GNS's option 2 includes the $d$-dependent
index condition (a). The rule should be the **structural** test:

* recognize, and run product refinement plus `GiantStep`, iff
  $\mathrm{Soc}(P)\cong(A_m^{(t)})^k$ in product action with $m>4\log_2\binom mt$ and $m>q_0$;
* otherwise enumerate.

A group that passes the structural test but fails (a) is fine under product refinement, because
its index is $\le2^k\lvert K\rvert$ and BCP bounds $\lvert K\rvert$ without using (a). Groups that
fail the structural test are option 1 by GNS's proof, or structural option 2 with $m\le q_0$
(§4). The rule then needs no knowledge of $d$, as VR claims.

**(c) Constant, cosmetic.** $\Lambda=\log(4\tilde d)$ covers only the composition-factor reading
of BCP. Use $\log(8\tilde d)$ to cover the Burness–Shalev reading too (§6).

**(d) Statement, cosmetic.** "$n^{O(\log d)}$" should read $n^{O(\log(d+2))}$.

**(e) Lean status, a caveat.** The header of `Paper/RunningTime.lean` (L9) says "The algorithm of
Sections 4 to 6 is not formalized yet". Meanwhile `Algorithm/PhaseTree.lean` builds the phase tree
from `GI.Algorithm.Run` and states `phaseTree_hyp`. I did not determine how complete that is.
Either way, Lean formalizes only HJ's dispatcher and the $N^a$ table. **Neither (M′) nor the
$\Lambda$-potential nor the regrouping is machine-checked.**

---

## 10. Overall verdict

**No hole found outside (H0).** I independently re-derived the parts the first verifier marked as
its own arguments:

* the regrouping, checked against both HJ's pseudocode and the Lean scripts;
* the row inequalities;
* the closure argument;
* the (M′) case analysis;
* "option 2 ⇒ $m>3t$" and the identification $C(x,y)=\{S:i\in S\}$ for $m\ge3t$ in VR §2.2.

They hold, apart from the defects in §9.

**The strongest statement I would sign off on.**

> Assume (H0): HJ's algorithm is as described in Sections 4–6 and Appendix A of arXiv:2611.01399v1,
> and the following hold: Lemma 7.1's framework, Theorem A.9 (σ-budget), the local-test interface
> and lockstep comparisons, the aggregation/Design interface with $q^{O(\kappa)}$ branches, Lemma
> large-symmetry, Lemma exact-configuration, and the cap payment (eq. main-cap-payment). Assume
> also these published results: GNS Thm 3.13 and Lemma 4.4 (with CFSG, GSS98, Liebeck–Shalev,
> BLS87 and Kantor–Luks as trusted inputs), BCP Lemma 2.2 (or Maróti Cor. 1.5), and the Luks /
> Babai–Luks reduction (GNS Thm 8.1).
>
> Then HJ's algorithm, with the structural dispatcher (M′) of §9(b) in phases with $d\le N^\alpha$,
> solves string isomorphism for $G\in\hat\Gamma_d$ on $N$ points deterministically in
> $\exp\big(O(\log(N+2)\log(d+2))\big)\cdot\mathrm{poly}(\text{input})$. Consequently, graph
> isomorphism for maximum degree $d$ is in $n^{O(\log(d+2))}$.

The hidden constant is roughly $A\cdot C_{A.9}$ with $A\gtrsim2\kappa/c_\theta\approx10^3$. It is
absolute but not computable from the papers, because $c_1,c_2$ and $C$ are not explicit.

**Where I would put the residual risk, in order.**

1. (H0), especially Theorem A.9 and the extra-orbit rule. This is exactly the component the
   literature identified as blocked (§7).
2. Correct and deterministic recognition of all structural option-2 groups. This is taken on trust
   from GNS Lemma 4.4 / BLS87; VR §2.2 gives a self-contained identification step, and I
   re-checked it.
3. The absence of any machine check of the $\Lambda$ version.

## 11. What I could not check

* (H0) in any part, including Theorem A.9, the Design Lemma with $\alpha=3/4$, and
  Split-or-Johnson.
* The BCP original text (paywalled). I used Maróti's and Burness–Shalev's restatements and
  Maróti's Cor. 1.5. I did not confirm the journal numbering of Cor. 1.5.
* The proofs behind GNS 3.13: GSS98, Liebeck–Shalev, the affine case.
* BLS87 and Kantor–Luks (determinism, polynomial time).
* Neuen's thesis, including Example 5.5.10 and Thm 5.3.4. I could not retrieve it.
* The Luks / Babai–Luks reduction's internals.
* No Lean was built or run.
