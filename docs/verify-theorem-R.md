# Verification of Theorem R (moonshot memo §4.1, "Attempt A")

Branch `r4-verify`, 2026-11-04. This memo checks `docs/moonshot-theory.md` §4.1 (Theorem R and
its corollary), the references it cites, and next steps 1–3 of §6.

**Sources read.** All sources were downloaded into separate directories under
`scratchpad/r4-sources/` and only read; no code from them was run.

* HJ: the LaTeX source `graph_isomorphism.tex` (arXiv:2611.01399). "L…" below means a line of
  this file.
* The HJ Lean development, read only, at `~/math/GraphIsomorphismLog2/Workspace`. Lean and lake
  were not run.
* GNS: Grohe–Neuen–Schweitzer, arXiv:1802.04659v3 source, `bounded-degree-polylog-d.tex`.
  "G…" below means a line of this file. Theorem numbers were recomputed from the shared
  `theorem` counter: Def. 2.3, Lemma 2.2, Thm 3.13 and Rem. 3.14 match the memo's citations.
* Babai: arXiv:1512.03547v2 source, `main.tex`.
* HBD: Helfgott (with Bajpai and Dona), arXiv:1710.04574 source, `BDHv8.tex`.
* Neuen20: Neuen, arXiv:2002.06997 source (ICALP 2020 / TALG 2022).
* Survey: Neuen, *Parameterized complexity of graph isomorphism testing*, Comput. Sci. Rev. 60
  (2026) 100918. The open-access PDF is in the Regensburg repository (epub.uni-regensburg.de/78630).
* BCP 1982 could not be downloaded (ScienceDirect returns 403). Its Lemma 2.2 is used here only
  as GNS quote it (GNS Lemma 2.2).

**Status tags.** **[VERIFIED]**: checked line by line against the cited text.
**[ARGUED HERE]**: a new argument written out in this memo. **[TRUST]**: taken from the
literature without re-proof. **(H0)** is the standing assumption that HJ's algorithm and its
analysis (Sections 4–7 and Appendix A) are correct as written.

---

## 0. Verdict

| item | verdict |
|---|---|
| (H0) HJ correct | **assumption**; cannot be checked here. Everything below depends on it, including HJ's own analysis, not only its final theorem. |
| (H1) recognition of Cameron constituents | **holds, so it is not a hypothesis.** The memo's wording needs one repair. Recognition is needed for GNS-option-2 groups, i.e. those with socle $A_m^{(t)}$ in product action and $m>4\log_2\binom mt$, not for "Cameron-large" groups. For those groups it is deterministic polynomial time: GNS Thm 3.13's algorithm plus GNS Lemma 4.4 (BLS87), or the self-contained variant in §2. The requirement is genuine: HJ's fallback for this range is enumeration (L3082–3086), which is outside the $\hat\Gamma_d$ budget (§2.3). |
| (H2) call grouping | **holds** [VERIFIED against HJ L774–800, L2655–2760 and the Lean scripts]. There are at most $10q^{2\kappa}$ families (split by string, test, coset image and type), and the window calls in each family have pairwise disjoint domains. This fits HJ's Lemma 7.1 exactly as formalized: `PhaseTree.Hyp.branch_disjoint` only needs the child sizes in a "branch" to sum to at most $s$. |
| dispatcher (M) | **fixable gap; fix given.** "Never enumerate Cameron-large groups with $m>q_0$" is ambiguous. Read with HJ's order test (L1766–1772), it is wrong. The correct rule (M′, §4.0) enumerates P exactly when P is not GNS-option-2 with $m>q_0$. |
| no wide giants (step 1) | **holds** [VERIFIED]. With $q\le d\le N^\alpha$, `GiantStep` never takes the $q>\lambda$ branch (L1164). So RowStep, row terminals, column floors and in-domain rectangles never occur, and $E_N$ becomes $N^{O(1)}$. |
| closure of $\hat\Gamma_d$, including overcosets | **holds; this is not a gap.** HJ recurses only on preimages inside the frozen parent $G_0$ (L1077–1082, L3000, L3207). The overcoset $E\subseteq\mathrm{Sym}(\Gamma)$ itself has degree $q\le d$. Configuration calls use $\mathrm{Sym}(C)$ with $\lvert C\rvert\le q\le d$ (§5). |
| potential $\Phi_\Lambda$, row by row (step 3) | **holds with explicit constants** (§4). Every multiplicity is $d^{O(1)}$ or $\lvert P\rvert\le d'^{O(\log d)}$, so no $N^{\Omega(1)}$ factor remains. |
| enumeration of non-Cameron P | **holds** [VERIFIED]. GNS Thm 3.13(1) gives $\lvert P\rvert\le d'^{\,c_1\log d+c_2}$ in terms of the quotient degree $d'$. $c_1,c_2$ are absolute but not explicit. |
| small Cameron P and the $\log\log N$ term | **holds, and the $\log\log N$ term is removable.** By BCP (GNS Lemma 2.2), $\lvert\text{top}\rvert\le d^{\,k-1}$. This settles memo next-step 3 (§4.4, §4.5). |
| root bound, phase recurrence (steps 4–5) | **holds** [VERIFIED]. |
| corollary | **holds**: survey Lemma 4.5 / GNS Thm 8.1, polynomial-size instances (§6). |
| novelty | **No $n^{O(\log d)}$ or $n^{O(\log d+\log\log n)}$ bound found** (§7). The result is a conditional corollary of HJ combined with GNS 3.13 and BCP. |

**Strongest statement that holds (conditional on (H0) only).**

> **Theorem R\*.** HJ's string-isomorphism algorithm with dispatcher (M′) solves string isomorphism
> for $G\le\mathrm{Sym}(\Omega)$, $G\in\hat\Gamma_d$, $\lvert\Omega\rvert=N$, deterministically in time
> $$\exp\big(O(\log(N+2)\cdot\log(d+2))\big)\cdot\mathrm{poly}(\text{input}).$$
> **Corollary R\*.** Graph isomorphism for graphs of maximum degree $d$ can be decided in
> $n^{O(\log(d+2))}$ time.

This is stronger than the memo's $\exp(O(\log N(\log d+\log\log N)))$: (H1) and (H2) are discharged,
and the $\log\log N$ term is removed. If one prefers not to rely on BCP Lemma 2.2, which we
could only read as quoted by GNS, the memo's version with $\log\log N$ still holds via Maróti's
$2^rr!$.

**The decisive point.** There is no hole outside (H0). Two places did need repair.

1. Read literally, (M) uses the wrong criterion ("Cameron-large" by order), and so does HJ's
   own exceptional enumeration range. Both enumerate Johnson groups $A_m^{(t)}$ with
   $t\approx\sqrt m$ (or product actions with $r\gtrsim m/\log m$) at cost $d'^{\Theta(\sqrt m)}$
   (respectively $\approx d^{\,m}$), which is far above $d'^{O(\log d)}$ when $m$ is near $d$.
2. The fix needs a recognition algorithm that works throughout GNS option 2. It exists.

Everything else in the sketch checks out once the families in (H2) are made precise.

---

## 1. Citations: exact statements and mismatches

### 1.1 GNS (arXiv:1802.04659v3)

* **Def. 2.3** (G391–394) [VERIFIED]: "For $d\ge2$ let $\hat\Gamma_d$ denote the class of all groups $G$
  for which every composition factor of $G$ is isomorphic to a subgroup of $S_d$."
* **Lemma 2.4** (Luks; G400–408) [VERIFIED]: $\hat\Gamma_d$ is closed under subgroups and
  homomorphic images. Closure under extensions holds too, because composition factors of an
  extension are the union of those of the kernel and the quotient.
* **Lemma 2.2** ("[BCP82], Lemma 2.2"; G384–389) [VERIFIED as a quotation; original not read]:
  "Suppose $d\ge6$. Let $G$ be a permutation group of degree $n$ such that $G$ has no composition
  factor isomorphic to an alternating group $A_k$ of degree $k>d$. Then $\lvert G\rvert\le d^{n-1}$."
* **Theorem 3.13** (G864–928) [VERIFIED]: "Let $G\le\mathrm{Sym}(\Omega)$ be a primitive
  $\hat\Gamma_d$-group. Then one of the following holds:
  1. $\lvert G\rvert\le n^{c_1\log d+c_2}$ for some absolute constants $c_1,c_2$, or
  2. for the normal subgroup $N=\mathrm{Soc}(G)$ there is a sequence of partitions
     $\{\Omega\}=\mathfrak B_1\succ\dots\succ\mathfrak B_k=\{\{\alpha\}\}$ such that
     (a) $\lvert G:N\rvert\le n^{1+\log d}$, (b) each $\mathfrak B_i$ is $N$-invariant, and (c) there are
     $m\le d$ and $t\le m/2$ with $m>4\log s$, where $s=\binom mt$, such that for all $i$ and
     $B\in\mathfrak B_i$ the group $N_B^{\mathfrak B_{i+1}[B]}$ is permutationally equivalent to
     $A_m^{(t)}$.

  Moreover, there is a polynomial-time algorithm that determines one of the options that is
  satisfied and in case of the second option computes $N$ and the partitions."

  The proof (G901–928) also shows that in option 2, $G\le P\wr K$ in product action, with $P$
  almost simple with socle $A_m^{(t)}$ and $K\le S_k$ transitive in $\hat\Gamma_d$ (Lemma 3.9,
  G772–797). The algorithm computes $\lvert G\rvert$ (Schreier–Sims), computes the socle (Kantor–Luks
  1990) and builds maximal block chains. All steps are deterministic.
* **Remark 3.14** (G930–941) [VERIFIED]: the theorem fails for the BCP class $\Gamma_d$, since
  $\mathrm{AGL}(d,p)\in\Gamma_d\setminus\hat\Gamma_d$ has order $n^{\Omega(d)}$.
* **Lemma 4.4** ("[BLS87]"; G1261–1266) [VERIFIED as stated; BLS87 itself not read]: "Let
  $G\le\mathrm{Sym}(\Omega)$ and suppose $G$ is permutationally equivalent to $A_m^{(t)}$ or $S_m^{(t)}$ for
  $m>4\log n$ and $t\le m/2$. Then a permutational isomorphism $\rho:\Omega\to\binom{[m]}t$ can be
  computed in polynomial time."
* **Lemma 7.1** ("cf. [Babai15-full], Theorem 3.2.1"; G2065–2071): giant representations for
  primitive $G\le S_d$ with $\lvert G\rvert\ge d^{1+\log d}$.
* **Theorem 8.1** ([luks82, BL83]; G2208–2213) [VERIFIED]: "There is a polynomial-time
  Turing-reduction from the Graph Isomorphism Problem for graphs of maximum degree $d$ to the
  String Isomorphism Problem for $\hat\Gamma_d$-groups (the running time of the reduction does not
  depend on $d$)."
* **Theorem 1.1 / 7.4** (G148–151, G2191–2199): $n^{O((\log d)^c)}$ "for an absolute constant
  $c$".

  GNS's own route, for comparison: Lemma 7.2 uses tests of size $t=\max\{9,3+\log d\}$ and a
  recursion of height $O(\log^2d)$, i.e. $2^{O(\log^3d)}$ nodes. Thm 4.6 blows the domain up to
  $n^{(c_1\log d+c_2+1)\log d}$. So $c$ is at least 4 or 5. GNS do **not** run Babai's giant step
  on Johnson constituents in place. They "unfold" them into an almost $d$-ary sequence and then
  apply Babai-type certificates to blocks of size at most $d$.

### 1.2 Neuen's 2026 survey (Comput. Sci. Rev. 60 (2026) 100918, pp. 4–6) [VERIFIED]

* **Def. 4.3**: $\hat\Gamma_d$ is the class of groups whose composition factors are all
  isomorphic to subgroups of $S_d$. The composition width $\mathrm{cw}(\Gamma)$ is the least such $d$.
* **Remark 4.4**: some results hold only for this restricted class, not for the BCP variant.
* **Lemma 4.5**: "There is a polynomial-time Turing reduction from the Graph Isomorphism
  Problem for graphs of maximum degree $d$ to the String Isomorphism Problem for groups of
  composition width at most $d-1$." The survey attributes the reduction to Babai–Luks [16] and
  to Neuen's thesis, Thm 5.3.4.
* **Theorem 4.6** (GNS): string isomorphism for $\mathrm{cw}\le d$ in $n^{\mathrm{polylog}(d)}$.
  **Corollary 4.7**: graph isomorphism for maximum degree $d$ in $n^{\mathrm{polylog}(d)}$.
* **Theorem 4.9** (Neuen [27]): Set-of-Strings Isomorphism for $\mathrm{cw}\le d$ in
  $(n+m)^{\mathrm{polylog}(d)}$.

The memo cites these correctly.

### 1.3 Babai (arXiv:1512.03547v2), §3.2 [VERIFIED]

* **Theorem 3.2.1** (main.tex 2334–2342), as printed: "Let $G\le S_n$ be a primitive group of
  order $\lvert G\rvert\ge 2^{1+\log_2n}$" (a typo; the following text and GNS Lemma 7.1 read
  $n^{1+\log_2n}$) "…Then $G$ has a normal subgroup $N$ of index $\le n$ such that $N$ has a system
  of imprimitivity on which $N$ acts as a Johnson group $A_k^{(t)}$ with $k\ge\log_2n$. Moreover,
  $N$ and the system of imprimitivity in question can be found in polynomial time."
* **Cameron groups** (2352–2360) are defined for all parameters with $k\ge\max(2t,5)$. Babai
  then states (2396–2398): "The algorithmic part is well known: Cameron groups can be
  recognized and their structure mapped out in polynomial time (and even in NC [BLS87])."

### 1.4 HBD (arXiv:1710.04574)

* **Theorem 3.1** (Cameron, Maróti; BDHv8 1006–1022) [VERIFIED]: for primitive $H<\mathrm{Sym}(R)$
  with $r$ large, either $\lvert H\rvert<r^{1+\log_2r}$, or there is $M\triangleleft H$ with $[H:M]\le r$ acting as
  $A_m^{(k)}$ on blocks. The text adds that $M$ and the blocks can be found in polynomial time
  [BLS] (1030–1032).
* **§2.8** (809–889) [VERIFIED]: the explicit BLS identification
  $\iota:\Gamma\to\mathscr S_k(\Lambda)$ uses the smallest and largest orbitals and **assumes
  $m>(k+1)^2-2$**. Footnote: below that bound, "$m!=n^{O(\log n)}$ … we will be able to afford
  to remove $G$ brutally". This is HJ's "exceptional recognition range" (L3082–3086).

### 1.5 Mismatches flagged

1. **Option 2 of GNS 3.13 is not "G is a Cameron group" in Maróti's order sense.** It is a
   socle condition, $\mathrm{Soc}=(A_m^{(t)})^k$ in product action with $m>4\log_2\binom mt$, together
   with $\lvert G:N\rvert\le n^{1+\log d}$. Cameron groups with $m\le4\log_2\binom mt$ fall in option 1.
   This helps the memo: those groups are cheap to enumerate.
2. **"Cameron-large" in (M) and (H1).** In HJ and Maróti, "large" means order
   $\ge n^{1+\log_2n}$. Neither (M) nor (H1) can use that criterion (§2.3, §4.0).
3. **$\Gamma_d$ versus $\hat\Gamma_d$.** The memo is correct to use $\hat\Gamma_d$. Over $\Gamma_d$
   the enumeration row fails outright (GNS Rem. 3.14). HBD's BCP theorem is stated for bounded
   composition factors, so it is a different statement again.
4. **Orders versus degrees.** In GNS 3.13(1), the bound $n^{c_1\log d+c_2}$ uses the
   **primitive degree** $n$ (HJ's quotient degree $d'$) and the **class parameter** $d$. That is
   exactly what the enumeration row needs. In BCP Lemma 2.2, $n$ is the degree of the top group
   ($k\le\log_5d'$).
5. **Constants.** $c_1,c_2$ are absolute but not explicit: they come from Liebeck–Shalev base
   bounds, GSS98, Liebeck 1984 and Maróti. This is fine for $O(\cdot)$, but Theorem R\*'s constant
   is not computable from the papers read.
6. **Deterministic versus randomized.** Every ingredient is deterministic: Schreier–Sims;
   Kantor–Luks socle [TRUST]; BLS87 NC algorithms [TRUST]; HJ claims determinism.
7. **The reduction's target class.** GNS Thm 8.1 lands in $\hat\Gamma_d$; survey Lemma 4.5
   lands in $\hat\Gamma_{d-1}$. Either is enough.
8. **Babai Thm 3.2.1 alone is not enough for (H1).** It covers only order $\ge n^{1+\log n}$.
   (M′) must also recognize option-2 groups below that order. Babai's text and GNS Lemma 4.4
   cover them; HBD's §2.8 construction as written does not cover all of them (§2.2).

---

## 2. (H1): recognition of Cameron constituents

### 2.1 What is needed

(M′) (§4.0) must decide, in deterministic polynomial time, whether a primitive quotient
$P\le\mathrm{Sym}(d')$ is GNS-option-2 with $m>q_0$. If it is, (M′) must output what HJ's product
refinement and `GiantStep` consume (L3067–3071): "an explicit natural or Johnson realization and a
supplied quotient homomorphism", i.e. the product coordinates, the bijections
$\iota_j:\text{coordinate}_j\to\binom{[m]}t$, and $P\to S_m\wr S_k$.

### 2.2 The literature provides it

* Option 1 versus option 2, $N=\mathrm{Soc}(P)$ and the block chains: the algorithm of GNS
  Thm 3.13 [VERIFIED statement; TRUST on Kantor–Luks for the socle].
* The Johnson identification per coordinate: GNS Lemma 4.4 for $m>4\log_2\binom mt$, which is
  exactly option 2's condition (c). It cites BLS87 §4 "implicitly" [TRUST].
* Babai §3.2 asserts polynomial-time (NC) recognition of all Cameron groups [TRUST].

**A self-contained check of the identification step** [ARGUED HERE]. HBD's §2.8 needs
$m>(t+1)^2-2$, which excludes part of option 2: for $t\approx\sqrt m$ and $m\ge300$ we have
$m>4t\log_2(m/t)$ but $m\not>(t+1)^2-2$. The following variant needs only $m\ge3t$.

* *Option 2 implies $m>3t$.* If $t\ge m/3$, then $4\log_2\binom mt\ge4\log_2\binom m{\lceil m/3\rceil}\ge
  4\cdot\frac m3\log_23>2m$, contradicting $m>4\log_2\binom mt$.
* *Orbitals.* For $m\ge2t+2$ the orbitals of $A_m$ on $t$-sets equal those of $S_m$: the
  relations $R_i=\{\lvert S_1\cap S_2\rvert=t-i\}$, $i=0..t$. Each pair has an odd permutation in its
  $S_m$-stabilizer, because at least $m-2t\ge2$ points are outside $S_1\cup S_2$.
* *Construction.* Take $\Upsilon=R_1$ and $\Delta=R_t$ (disjointness). For $(x,y)\in R_1$ with
  $x\setminus y=\{i\}$, put $B(x,y)=\{z:z\cap x\ne\emptyset,z\cap y=\emptyset\}=\{z:i\in z,\ z\cap y=\emptyset\}$
  and $C(x,y)=\{S:\ S\cap z\ne\emptyset\ \forall z\in B(x,y)\}$. If $i\in S$, then $S\in C(x,y)$. If $i\notin S$,
  pick $z=\{i\}\cup Z'$ with $Z'$ a set of $t-1$ points outside $y\cup S\cup\{i\}$; this is possible
  since $m-(2t+1)\ge t-1$ when $m\ge3t$. Such a $z$ is disjoint from $S$. Hence
  $C(x,y)=\{S:i\in S\}$, and HBD's $\iota(\omega)=\{\gamma\in\Lambda:\omega\in\gamma\}$ identifies $\Omega$ with
  $\binom{\Lambda}{t}$.
* *Finding $R_1$ and $R_t$ without the size heuristic.* Try every ordered pair among the at
  most $t+1$ nontrivial orbitals. For each, check that the output $\iota$ is a bijection onto
  $\binom\Lambda t$ and that the induced image of $N_B$ in $\mathrm{Sym}(\Lambda)$ has order $\lvert\Lambda\rvert!/2$ or
  $\lvert\Lambda\rvert!$. The true pair passes, and any pair that passes is a valid identification. The
  cost is $\mathrm{poly}(\binom mt)$, deterministic.

For $2t<m<3t$ we have $\binom mt\ge2^{\Omega(m)}$, so $\lvert A_m\rvert\le\binom mt^{O(\log m)}$ and enumeration is
within budget anyway (GNS option 1). So every Cameron constituent with $m>q_0$ can be handled
within budget, by recognition or by enumeration.

### 2.3 Is (H1) needed at all? Yes: HJ's dispatcher overspends on $\hat\Gamma_d$

* *HJ's order test* (L1766–1772) enumerates P when $\lvert P\rvert\le\exp(a\log^2d')$. For
  $(A_m^{(t)})^r$ with $r\gtrsim m/(at\log m)$ the order is about $\exp(rm\log m)$ while
  $\log d'\approx rt\log(m/t)$. Paying this with $\tfrac A3\Lambda\log d'$ needs $\Lambda\gtrsim m/t$,
  which can be close to $d$. The memo's remark at §4.1 (M) is correct.
* *HJ's exceptional recognition range* (L3082–3086) enumerates the constituent when HBD's
  construction does not apply ($m\le(t+1)^2-2$). Example: $A_m^{(t)}$ with $t=\lceil\sqrt m\rceil$,
  $m\le d$. Then $\log\lvert P\rvert\approx m\log m$ and $\log d'\approx\tfrac12\sqrt m\log m$, so the cost is
  $d'^{\Theta(\sqrt m)}$, while the budget is $d'^{O(\log d)}$. This range lies inside option 2 when
  $m\ge300$, so it must be recognized (§2.2), not enumerated.

**Verdict on (H1).** Holds, in the corrected form "recognize GNS-option-2 groups". It is a
theorem from the literature (GNS 3.13 + Lemma 4.4, or §2.2), not a hypothesis.

---

## 3. (H2): the call grouping

### 3.1 What HJ charges

* Eq. (constant-recurrence) (L2713–2721) charges certificates and comparisons
  $n^{O(1)}(1+F(n/\kappa,\sigma)+F(n,\sigma-\kappa))$: "The multiplicity absorbs the at most $n$
  updates, orbit calls, $k!$ cosets, and all test tuples and pairwise comparisons".
* The table (L1540–1550) uses $N^a$ for the affected and unaffected rows. This is paid via
  $N^a\le e^{a_*x}$ (eq. main-phase-active, L1468–1472) and the margins at L1794–1812.

### 3.2 The true structure [VERIFIED]

**Endpoint procedure.** Algorithm 3 (L774–793), `CheckNewWindow` (L797–803) and the window rules
(L2627–2700).

* Update $i$ adds $V_i\subseteq\Omega\setminus W_i$, and $W_{i+1}=W_i\cup V_i$. So the windows
  $V_0,V_1,\dots$ are **pairwise disjoint** (L2669: "Every update adds a nonempty
  $A_i$-invariant set").
* Update $i$ enumerates the $\lvert A_i:N_i\rvert=\lvert\mathrm{Alt}(T)\rvert=\kappa!/2$ cosets. If the image is not
  full the procedure stops (rule 1). It "appl[ies] the usual orbit chain rule only on the newly
  added window $V_i$" (L2680–2681).
* Each update is either purely affected (rule 2, kernel orbits of size $\le\lvert\Delta\rvert/\kappa$,
  L2683–2690) or purely "extra orbit" (rule 4, $\sigma$ drops by at least $\kappa$, L2694–2708).

The Lean code confirms this. In `Algorithm/Certificates.lean`, `checkNewWindowLift` (L332–341)
makes one `Continue` call per coset representative, each with domain equal to the window $V$
(`windowCall`, L295–300). In `endpointScriptLift` (L375–383) the window grows as
`AW.2 ∪ increment`. In `CertificateEndpoint.lean` L214–218, `increment` is a subset of the
complement of $W$ (`v ∉ W`) and is all-affected or all-extra.

**Families.** Index a coset at update $i$ by its image $\pi\in\mathrm{Alt}(T)$. This is canonical
because $\phi_T(A_i)=\mathrm{Alt}(T)$ at every non-final update. For a string $z\in\{x,y\}$, a test $T$,
an image $\pi$ and a type $\in\{$affected, extra$\}$, the calls form a list whose domains are
disjoint subsets of $\Omega$. This gives $2\cdot\binom q\kappa\cdot\frac{\kappa!}2\cdot2\le2q^\kappa$ families.

**Comparisons** (L2731–2760; `Algorithm/ComparisonPhase.lean` `lockstepStepLift` L105–110,
`comparePhase` L310–313). Each of the $(2q^\kappa)^2$ ordered comparisons runs under the full
ordered-tuple transporter. Its update $j$ makes one call, "string isomorphism on the new window
under $N_i$" (L2746). Its domain is the new window of the source endpoint, so the windows of one
comparison are disjoint. That gives at most $4q^{2\kappa}$ families, or $8q^{2\kappa}$ after
splitting by type.

**Total.** At most $10q^{2\kappa}$ disjoint-domain families. The Lean call counts are
$2\binom q\kappa s\kappa!$ and $4q^{2\kappa}s$ (`Paper/ScriptCalls.lean` L5–25); the factor $s$
there is exactly the update index, and it is absorbed.

**Aggregation children.** HJ says there are polynomially many choices in $q$ (L826–828, L2800–2822),
at most $q^{a_0}$ branches.

* Large symmetry (Case 2a, Lemma L2869–2977): "The number of orbit-chain families is an absolute
  constant" (L2976), with domains at most $s/2$.
* Balanced overcosets and configurations: one `LiftAndContinue` child per branch (L1052–1075).

### 3.3 Does the replacement survive Lemma 7.1? Yes [VERIFIED]

Lemma 7.1 (L1644–1712) needs, for each class, $\sum_{\text{children}}W\le\mathcal M e^{-\Delta\Phi}W(\mathcal S)$,
where $\mathcal M$ counts branches and "within one branch, the prefactors of its disjoint orbit
children sum to at most $(s+2)^D$" (L1670–1671). That inequality uses only $\sum_is_i\le s$
(eq. main-orbit-slack, L1584–1597: for $t\ge2$, $\sum(s_i+2)^D\le(s+1)^D+3^D<(s+2)^D$).

The Lean formalization of the lemma has exactly this interface:

* `PhaseTree.Hyp.branch_disjoint` (`Paper/RunningTime.lean` L228–230) requires only
  `(b.map size).sum ≤ parent size`;
* `class_mult` (L220–221) bounds the number of branches;
* `branch_child` requires each child to satisfy its row's drop.

So a disjoint-domain family **is** a branch in HJ's own (formalized) sense, provided each family
lies within one row, which is why families are split by type. Replacing `Row.mult` by the family
counts is a change of hypotheses only; the induction itself is unchanged. The sequential
dependence of later calls on earlier answers does not matter, because each call is a separate
subtree with its own bound.

**Verdict on (H2).** Holds. Each affected or unaffected class has at most $10q^{2\kappa}+c\,q^{a_0}$
branches, a quantity polynomial in $q$ (exponent $O(\kappa)$), not $N^{O(1)}$.

---

## 4. The potential argument, row by row

### 4.0 The dispatcher (M′)

At a transitive node, HJ exposes a primitive quotient $P$ of degree $d'$ (L1153). Under (M′):

* (a) If $P$ is GNS-option-2 with $m>q_0$, recognize it (§2) and do HJ's product refinement:
  enumerate the cosets of the preimage of $\mathrm{Soc}(P)=A_m^k$, then normalize, then run `GiantStep`.
* (b) Otherwise enumerate $P$.

By GNS 3.13's proof (G884–900), in case (b) either $\lvert P\rvert\le d'^{\,c_1\log d+c_2}$ (option 1), or $P$
is option 2 with $m\le q_0$. The rule does not need to know $d$.

For safety, use (M′) only in phases with $d\le N^\alpha$ and HJ's dispatcher verbatim otherwise.
This is legitimate because phases are analyzed independently, through $F(M_N)$, and both
reductions are exact (L1365–1367).

### 4.1 Closure facts used by every row

Every group the algorithm acts on is in $\hat\Gamma_d$ (§5). So every giant has
$q\le\mathrm{aw}\le d$. The reason: $\mathrm{Alt}(\Gamma)$ is a quotient of a subgroup $G_0$, and a
composition factor $\mathrm{Alt}(q)$, $q\ge5$, embeds in $S_d$ only if $q\le d$. And $q>q_0$ for every
giant step (L1766–1773), so a giant step happens only if $d>q_0$.

### 4.2 The potential

Put $\tilde d=\max(d,6)$, $\Lambda=\log(4\tilde d)$ ($\ge\log24$) and
$$\Phi_\Lambda=A\big(\Lambda x+\Lambda\rho+\Lambda\sigma+Q_d\big)+Bh,\qquad
W=(s+2)^De^{\Phi_\Lambda}.$$

* $x,\rho,\sigma,h$ are HJ's quantities (L1424–1450).
* $Q_d=\sum_i\log d_i\,\log\max\{c_i,2\}$ with caps initialized at $c_i=\min(d_i,d)$. This is valid
  because caps are analysis-only bounds on alternating width (L643–653), and
  $\mathrm{aw}\le d$ on $\hat\Gamma_d$. Inheritance stores $\min\{c,d'\}$ (L650–652). Product refinement sets the cap
  to $q=m\le d$ (L3186–3190). So every cap stays a valid bound and $Q_d\le\log s\cdot\log d$.
* $B,D,J,\kappa,q_0,\theta,\beta,a$ are HJ's constants (L1749–1790).
* $a$ is enlarged so that $q^{a}$ bounds every family or branch count above. Also
  $H_*=2B+\log(8J)$.

Lemma 7.1 needs, for each class with branch count $\mathcal M$ and minimum drop $\Delta\Phi$:
$$\log\mathcal M+H_*\le\Delta\Phi+2B.$$

### 4.3 The table

Here $q\le d\le\tilde d$, so $\log q\le\Lambda$.

| row | HJ multiplicity | true branch count (Γ̂_d, (M′)) | drop of $\Phi_\Lambda$ | condition on $A$ |
|---|---|---|---|---|
| affected test, large symmetry, normalization halving, later orbit children | $N^a$ | $\le q^a$ (§3) | $\ge Ac_\theta\Lambda-2B$ (eq. main-domain-payment L1484–1489, using $x-\log(\theta s+2)\ge c_\theta$) | $Ac_\theta\ge a+H_*/\log24$ |
| visible unaffected test | $N^a$ | $\le q^a$ (§3) | $\ge A\kappa\Lambda-2B$ ($\sigma\to\sigma-\kappa$, L2700–2708) | $A\kappa\ge a+H_*/\log24$ |
| product refinement, $k\ge2$, $m>q_0$ | $N^a2^kk!$ | $\lvert P:A_m^k\rvert\le2^k\lvert K\rvert\le2^k\tilde d^{\,k-1}$ (BCP Lemma 2.2 for $K\le S_k$, $K\in\hat\Gamma_d$); $\log\le(k-1)\log(4\tilde d)=(k-1)\Lambda$ | $\ge A(k-1)\Lambda-2B$ ($\rho$ drops by $\ge k-1$, L3060–3062) | $A\ge1+H_*/\log24$ |
| enumeration, option 1 | $N^ae^{a\log^2d'}$ | $\lvert P\rvert\le d'^{\,c_1\log d+c_2}$ (GNS 3.13); $\log\lvert P\rvert\le c'\Lambda\log d'$ | $\ge\frac A3\Lambda\log d'-2B$ ((s+2)/(s/d'+2) ≥ d'^{1/3}, L1497–1504) | $\frac A3\ge c'+\frac{H_*}{\log2\,\log24}$ |
| enumeration, option 2, $m\le q_0$ | same | $\lvert P\rvert\le(q_0!)^k\tilde d^{\,k-1}$ with $d'\ge17^k$; $\log\lvert P\rvert\le\frac{\log q_0!+\Lambda}{\log17}\log d'$ | same | $\frac A3\ge\frac{1+\log q_0!/\log24}{\log17}+\frac{H_*}{\log2\,\log24}$ |
| auxiliary continuation (overcoset lift) | $q^a$ | $\le q^a$ (L1473–1476) | $\ge Ac_\beta\log q-2B$ (eq. main-cap-payment L1522–1535, with "old cap $\ge q$", new cap $\le\beta q$, $d_i\ge q$) | HJ's (main-constant-cap) unchanged |
| row initialization or enlargement | $b_0$ | **does not occur** ($q\le\lambda$) | — | — |

Remarks on the table.

* *Product refinement for $k=1$.* There are at most 2 normalization cosets, bundled with the next
  giant step as in HJ (L1195–1210).
* *Bounded exceptions.* Constant-size enumerations ($\mathrm{Alt}(m)$, $m\le q_0$; bounded $q$ in
  Lemma exact-configuration; Mathieu groups) are covered by the option-1 and option-2 rows.
* *Fresh calls.* Configuration calls ($\le q^{a}$ per node, each on $\le q^2\le N^{2\alpha}<N^\gamma$
  positions) and threshold leaves are terminal oracle work, paid through
  $K_N=N^{O(1)}(1+F(M_N))$ (L1626–1641). $E_N=\exp(c_T\log^2N)$ was the row-terminal toll; it
  becomes $N^{O(1)}$ because the row terminal never runs.
* *Node toll.* $W\ge2N^a$ and the orbit slack still pay the polynomial node toll, since
  $s>N^\gamma$ and $D>a/\gamma+2$ (L1683–1690, L1599–1603, L1843–1844). Neither the $\Phi$ term nor $\Lambda$ is
  involved.
* *Every place HJ used $x\ge\gamma\log N$.* These are the $a_*x$ terms at L1796, L1800–1806 and
  L1808–1812, and every one of them pays the $N^a$ factor. In the true counts above that factor is
  either absent (enumeration and product rows: HJ calls it a "harmless upper bound", L1557–1558)
  or replaced by $q^{O(\kappa)}$ families (affected and unaffected rows). No same-domain branch
  count of size $N^{\Omega(1)}$ remains anywhere in the $q\le\lambda$ path.

### 4.4 The $\log\log N$ term

In the memo, $\log\log N$ arises only from (i) Lemma 1's $2^rr!$ and (ii) small-Cameron
enumeration. In $\hat\Gamma_d$ the top group $K\le S_k$ is a quotient of $P$, so it is in
$\hat\Gamma_d$ and BCP Lemma 2.2 gives $\lvert K\rvert\le\tilde d^{\,k-1}$. Both rows above then need only
$\Lambda=O(\log\tilde d)$. This answers memo next-step 3 positively: the bound is exactly the
"$\lvert\text{top}\rvert\le d^{O(r)}$" it asked for, in published form.

### 4.5 Root bound and phase recurrence [VERIFIED]

At a phase root (L1704–1711): $\rho\le2\log_2N$, $\sigma\le C\log N-B$ (Thm A.9, L2475–2485),
$Q_d\le\log N\log\tilde d$ and $h\le2$. So
$$\Phi_\Lambda(\text{root})\le A\Lambda\big(\log(N+2)+2\log_2N+C\log N\big)+A\log N\log\tilde d+2B=O(\Lambda\log(N+2)).$$
Lemma 7.1 then gives a phase cost of $K_NW(\text{root})=\exp(O(\Lambda\log(N+2)))(1+F_d(\lceil N^\gamma\rceil))$.

In phases with $d>N^\alpha$, HJ's own phase bound $\exp(C\log^2N)$ is at most
$\exp(\frac C\alpha\log N\log d)$. HJ's summation $\sum_j\hat\gamma^j=O(1)$ (L1722–1737) then gives
$F_d(N)=\exp(O(\log(N+2)\log\tilde d))$, since $\Lambda$ does not depend on $N$. ∎

---

## 5. Is $\hat\Gamma_d$ closed under everything the algorithm does? Yes

| operation | group produced | in $\hat\Gamma_d$ because |
|---|---|---|
| orbit chain, stabilizers, kernels $N_i$, $A_i=\mathrm{Aut}_{A_{i-1}}^{V}(x)$, transporter cosets $J_T\tau$ | subgroups (cosets) of the current $G$ | subgroup closure |
| faithful image on an orbit or at a fresh call (L568) | quotient of a subgroup | Lemma 2.4 |
| primitive quotient $P$; children of enumeration | quotient; kernel | closure |
| product refinement, normalization | preimage of $\mathrm{Soc}(P)$; index $\le2$ subgroup | subgroup |
| Lemma large-symmetry $H,H_0,K$ (L2898–2912) | $\pi^{-1}(\cdots)\le G$ | subgroup |
| **overcoset lift** (`LiftAndContinue`, L1077–1082: "lifts $E$ to a coset $H\tau$ in the original parent action"; L3000: "Its preimage is taken inside the actual current parent group"; L3207: "Lift each final full-$\Gamma$ ideal overcoset into $G_0$") | $H=\pi^{-1}(E)\le G_0$ | subgroup |
| the overcoset $E$ itself: Young groups, $\mathrm{Sym}(\Gamma\setminus W)$, parity (L907–916, L1056) | subgroup of $\mathrm{Sym}(\Gamma)$, $\lvert\Gamma\rvert=q\le d$ | degree $\le d$; never recursed on directly |
| configuration fresh call (L1044–1046, L1065–1067) | $\mathrm{Sym}(C)$ on $C^2$, $\lvert C\rvert\le q\le d$ | $S_{\lvert C\rvert}\le S_d$ |

So the overcosets do not leave $\hat\Gamma_d$. The "extra relabelings" that an overcoset admits
(L564–566) are elements of $G_0$, never of a larger group. Even the ideal group extended by
$\mathrm{Sym}(\Gamma\setminus W)$ with parity has degree $q\le d$.

---

## 6. The corollary

* Survey Lemma 4.5 and GNS Thm 8.1 [VERIFIED statements; the reduction itself is TRUST]: a
  polynomial-time Turing reduction, independent of $d$, from graph isomorphism of maximum degree
  $d$ to string isomorphism over $\hat\Gamma_{d-1}$ (or $\hat\Gamma_d$). Because the reduction runs
  in polynomial time, each instance has domain size $N\le\mathrm{poly}(n)$ and there are
  $\mathrm{poly}(n)$ instances.
* So the total time is $\mathrm{poly}(n)\cdot\exp(O(\log\mathrm{poly}(n)\cdot\log(d+2)))=n^{O(\log(d+2))}$.
  The memo's version, $n^{O(\log d+\log\log n)}$, also follows. The bounds compose.

Sanity checks: for $d=O(1)$ the bound gives $n^{O(1)}$ (Luks); for $d\ge n^{\Omega(1)}$ it gives
$n^{O(\log n)}$ (HJ); for $d=\mathrm{polylog}\,n$ it gives $n^{O(\log\log n)}$, beating GNS's
$n^{(\log\log n)^c}$. For $d<\log n$ the memo's version could be worse than GNS; Theorem R\* never
is.

---

## 7. Novelty

Sources checked, and the bounds they state:

| source | bound | how checked |
|---|---|---|
| GNS (arXiv v3; FOCS'18; SICOMP 52(6) 2023 per the survey) | $n^{O((\log d)^c)}$, absolute $c$ | full source |
| Neuen, ICALP'20 / TALG'22 (2002.06997) | $(n+m)^{O((\log d)^c)}$ (Thm 1.1); the open question asks only for $n^{O((\log d)^c)}m^{O(1)}$ | full source |
| Neuen, survey 2026 | $n^{\mathrm{polylog}(d)}$ (Thm 4.6, Cor 4.7, Thm 4.9) | full PDF |
| Babai 2015/16 | no degree-$d$ bound | full source |
| HBD 2017 | no degree-$d$ bound | full source |
| HJ 2026 | cites GNS's $n^{\mathrm{polylog}\,d}$ (L260–270); no $\hat\Gamma_d$ or degree corollary | full source |
| Wiebking (treewidth), Grohe–Neuen–Wiebking (minors), Grohe–Neuen "Recent advances" | $n^{\mathrm{polylog}(k)}$ | abstracts and survey only |
| Neuen's thesis (RWTH 2019) | not retrieved | its author's 2026 survey, which cites it, still lists $\mathrm{polylog}$ |

* Web searches for $n^{O(\log d)}$, "composition width" with an improved exponent, and
  post-HJ follow-ups found nothing.
* One unverified GitHub "problem" page (`tangle-solve/problem-de578945…`) attributes
  "$2^{O(d\log d)}n^{O(\log d)}$" to GNS 2020. GNS's text does not support this: it states
  $n^{O((\log d)^c)}$. It is a misattribution, not prior art.

**Status.** New relative to everything found, but **conditional on HJ**. It is a short corollary
of HJ's analysis combined with GNS 3.13 and BCP, so HJ's authors or a referee may well regard it
as routine. The genuinely needed inputs beyond HJ are: the (H2) re-grouping, the (M′) dispatcher
with GNS-option-2 recognition (replacing HJ's exceptional enumeration), and BCP for the top group.

---

## 8. Cleaned-up proof of Theorem R\*

**Algorithm.**

* In phases with $d>N^\alpha$, run HJ (Algorithm `alg:main-recursion`) verbatim.
* In phases with $d\le N^\alpha$, run HJ with (M′) (§4.0). Recognition is done as in §2.2.
* Correctness is HJ's Lemma 6.1 (L1357–1393). Enumeration and product refinement are both exact
  reductions, so the dispatcher choice does not affect correctness.

**Analysis.** Fix a phase with $d\le N^\alpha$.

1. Every group in the phase lies in $\hat\Gamma_d$ (§5). Hence every alternating label set has
   $q\le d\le N^\alpha=\lambda$. `GiantStep` therefore never takes the $q>\lambda$ branch (L1164).
   So there are no RowStep, row terminals, column floors or in-domain rectangles, and
   `AuxiliaryReduction` always makes the small-configuration call (L1043–1047).
2. The children of a node fall into HJ's classes. After re-grouping as in §3, the number of
   branches is at most $q^{a}$ for the certificate, comparison and aggregation classes, at most
   $2^k\tilde d^{\,k-1}$ for product refinement, and at most $\lvert P\rvert$ for enumeration. Each branch
   has $\sum s_i\le s$.
3. With $\Phi_\Lambda$ as in §4.2 and $A$ satisfying the conditions in the last column of §4.3,
   every class carries at most $W/(8J)$. Lemma 7.1's induction, in HJ's text and in its Lean
   form (`PhaseTree.Hyp`), gives cost $\le K_NW(\text{root})$ with $K_N=N^{O(1)}(1+F_d(M_N))$.
4. $\Phi_\Lambda(\text{root})=O(\log(N+2)\log\tilde d)$ (§4.5).
5. Summing over phases gives $F_d(N)=\exp(O(\log(N+2)\log\tilde d))\cdot\mathrm{poly}$. ∎

---

## 9. Ledger: verified versus trusted

**Verified line by line here.**

* HJ's Algorithm 3, `CheckNewWindow`, window disjointness, the coset count per update, and
  lockstep comparisons (L774–803, L2627–2760). These match the Lean scripts `windowCall`,
  `checkNewWindowLift`, `endpointScriptLift`, `increment`, `lockstepStepLift` and `comparePhase`,
  and the call counts in `ScriptCalls.lean`.
* HJ's dispatcher and `GiantStep` branching on $q$ versus $\lambda$ (L1136–1181), and
  `AuxiliaryReduction` (L1033–1075).
* Every place an overcoset is lifted (L907–916, L1077–1082, L2994–3000, L3201–3210, L3127–3130).
* HJ's potential, table, payments, constants and Lemma 7.1 (L1416–1858), and the Lean
  `PhaseTree.Hyp` interface (`RunningTime.lean` L153–240).
* The exact statements and numbering of GNS Def 2.3, Lemmas 2.2, 2.4 and 4.4, Thm 3.13,
  Rem 3.14 and Thm 8.1, and the case analysis in the proof of GNS 3.13 that (M′) relies on.
* Survey Def 4.3, Lemma 4.5, Thms 4.6 and 4.9. Babai §3.2. HBD Thm 3.1 and §2.8.
* The new arguments: §2.2 (option 2 implies $m>3t$; identification for $m\ge3t$), and the
  family counts and constants in §3–§4.

**Taken on trust.**

* (H0): HJ's correctness. This includes Thm A.9 ($\sigma=O(\log s)$), the certificate/aggregation
  interface (Design Lemma with $\alpha=3/4$), Lemma exact-configuration, and the claim that the
  children listed in HJ's Sections 4–7 are all the children.
* The proof of GNS Thm 3.13, which relies on Liebeck–Shalev, GSS98, Liebeck 1984, Cooperstein,
  Kleidman–Liebeck and Maróti.
* BCP Lemma 2.2, read as quoted by GNS.
* Kantor–Luks and BLS87: deterministic polynomial-time socle and Cameron recognition.
* The Luks / Babai–Luks reduction (GNS Thm 8.1, survey Lemma 4.5).
* No Lean was built or run. The statement that the Λ-variant fits `PhaseTree.Hyp` comes from
  reading the hypotheses, not from a proof check.
