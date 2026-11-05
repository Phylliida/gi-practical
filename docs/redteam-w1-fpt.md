# Red-team report on `docs/w1-fpt.md`

Branch `w2-redteam-fpt`, 2026-11-05. Target: the claims labelled **[PROVEN]** in `docs/w1-fpt.md`
("W1" below; "W1 L…" is a line of that file). Background used: `verify-theorem-R.md` ("VR"),
`redteam-theorem-R.md` ("RT"), `moonshot-theory.md`.

**Sources.**
* "HJ L…" is a line of `scratchpad/paper/graph_isomorphism.tex` (arXiv:2611.01399v1).
* "Lean" means `~/math/GraphIsomorphismLog2/Workspace`. It was read only; lean and lake were never run.
* "ADKT txt L…" is a line of `r4-sources/w1fpt-adkt/adkt.txt`, the text of ECCC TR09-093 rev. 1.
* "SW19" is Schweitzer–Wiebking, arXiv:1806.07466 (STOC'19); its source is already in
  `r4-sources/w1s-arxiv-1806.07466/`.
* Survey: Neuen, Comput. Sci. Rev. 60 (2026) 100918, `regensburg-neuen-survey/survey.txt`.
* GNS: `arxiv-1802.04659/x/bounded-degree-polylog-d.tex` ("G…").
* Grohe–Neuen: `grohe-neuen-2011.01366/paper.txt`.
* Neuen ICALP'20: `arxiv-2002.06997/x/hypergraph-gamma-d.tex`.
* New download: Otachi–Schweitzer arXiv:1403.7238, in `r4-sources/w2rt-otachi-schweitzer/`. It was
  converted to text by a script kept in `scratchpad/w2rt-scripts/` and run with `python3 -I`.
* Neuen–Schweitzer arXiv:1705.03283: introduction read through ar5iv.

The only thing executed was a one-line numeric check of the order inequality (python, under a
second of CPU).

**Severity scale.** *Break*: the claim is false. *Gap*: the claim is true but the written proof
misses a step. *Cosmetic*: wording or citation.

---

## 0. Verdicts

| # | claim | verdict | defects |
|---|---|---|---|
| 1 | Barrier: HJ+(M′) and HJ verbatim make $\ge\lvert G_{d,m}\rvert\ge N^{\log_2D-0.443}$ branches; GNS 3.13 is sharp at fixed $d$ | **sound** | cosmetic: "every size $N$" holds only for suitable $m$ (§1.6) |
| 2 | Prop. 3.3: the family is FPT, $2^{2^{O(D)}}N^{2+o(1)}$ | **sound** | gap (low): how the automorphism group of each table entry is obtained (§2.2); cosmetic: BCP needs $d\ge6$; novelty: an instance of published theorems (§2.4) |
| 3a | Prop. 4.1: block-pair DP, $O(N^2)$ types, combine step = PCI | **sound** | the same gap as 2, in the definitions: "$\mathrm{Aut}(B):=\mathrm{Iso}(B,B)$" is not a group (§3.1) |
| 3b | Theorem E: time $\pi_0\,\varepsilon\,\mathrm{poly}(N)$ | **sound** | gap (low): the corollary "$b!\,\varepsilon$ for tree groups" needs the block tree aligned with the given tree (§3.3). The abelian-entanglement [SKETCH] can be upgraded to proven (§3.4). |
| 4 | Prop. 4.2: SI is FPT iff CI is FPT, for tree groups | **sound** | gap (low-medium): (⇒) via Prop. 4.1's virtual root fails for intransitive groups as written; fixed by running the DP on the given tree. Gap (low): (⇐) needs leaves at equal depth (§4). |
| 5 | Literature: FPT open, no W-hardness, ETH blow-up, Q4.8 | **sound** | cosmetic: ADKT p. 3 poses the question but does not quote Downey–Fellows (§5) |

**No break found.** Every [PROVEN] statement I checked is true as stated, or true after a one-line
repair.

---

## 1. Claim 1: the barrier (W1 L190–263)

### 1.1 $P_d$ is primitive and not regular (W1 L209–214): sound

* $D$ is odd, so $\mathbf 1\notin W$ and $\mathbb F_2^D=\langle\mathbf1\rangle\oplus W$.
* **Irreducibility, checked directly.** Let $U\le W$ be a nonzero $S_D$-submodule and pick
  $0\ne v\in U$. Then $v\ne\mathbf1$, because $\mathbf1$ has odd weight. Choose $i$ with $v_i=1$ and
  $j$ with $v_j=0$. Then $v+v^{(ij)}=e_i+e_j\in U$, so $U\supseteq\langle e_i+e_j\rangle=W$.
* **Faithful** for $D\ge3$.
* Parity matters as the task says: for $D$ even, $\mathbf1\in W$ is a proper submodule, $W\rtimes S_D$
  would be imprimitive, and the construction would fail. W1 correctly uses $D$ odd.
* An affine group $V\rtimes H$ is primitive iff $H$ is irreducible. Since $|P_d|=2^dD!>2^d$, $P_d$ is
  not regular.
* $P_2=\mathrm{AGL}(2,2)\cong S_4$ is correct.

### 1.2 Primitivity and socle of $G_{d,m}$ (W1 L216–220): sound

* Dixon–Mortimer Lemma 2.7A (checked from memory, not from the book): $H\wr_\Gamma K$ in product
  action is primitive iff $H$ is primitive and **not regular** and $K$ is transitive on the finite
  set $\Gamma$. Both hypotheses hold for $m=2^j\ge2$; for $m=1$, $G=P_d$.
* $W^m$ is a regular abelian normal subgroup. In a primitive group it is then the unique minimal
  normal subgroup, so the socle is elementary abelian. GNS's proof (G882–885) puts every Type I
  (affine) group in option 1.

### 1.3 Class (W1 L222–223): sound

The composition factors are $C_2$ (from $W^m$, from $S_D/A_D$ and from $C_{2^j}$) and $A_D$
($A_3=C_3$ when $D=3$). All embed in $S_D$, so $G_{d,m}\in\hat\Gamma_D$. It is not in
$\hat\Gamma_{D-1}$, so the class parameter really is $D$, which W1 states correctly.

### 1.4 Order (W1 L225–227): sound, checked exactly

* Exact value:
  $\log_N|G|=1+\frac{\log_2D!}{D-1}+\frac{\log_2m}{(D-1)m}$ with $N=2^{(D-1)m}$ and
  $|G|=2^{dm}(D!)^mm$.
* The inequality chain uses $D!\ge(D/e)^D$, which holds for all $D$ since $e^D\ge D^D/D!$, and
  $\log_2e=1.442695$. So $\log_N|G|>\log_2D-0.4427$ for every $D$ and $m$.
* Numeric check over odd $D\le201$ and $m\le2^{11}$: the minimum slack over $\log_2D-0.443$ is
  $0.057$.
* The small-$D$ exponents (W1 L248) are $2.292$, $2.727$, $3.309$ and $4.835$. They are correct.

### 1.5 HJ really enumerates $G$ at the root (W1 L229–239): sound

This is the step the task singled out. I traced it in the paper, in the Lean dispatcher and in
(M′).

**HJ verbatim.**
1. `Solve`/`Continue` (HJ L1136–1172). With $N>N_0$ and $s=N>N^\gamma$, the action is transitive and
   there is no column floor. "Expose the next primitive quotient" then gives the coarsest primitive
   quotient compatible with the tower (HJ L3177–3183). $G$ is primitive, so that quotient is $G$
   itself on $d'=N$ singleton blocks. **There is no smaller quotient.**
2. "**if** enumeration or a product refinement applies" (HJ L1154). The Lean dispatcher makes the
   order of the tests explicit (`Algorithm/Dispatch.lean` L29–41 and L856–872):
   * first `Small`, i.e. $|\rho(G)|\le\exp(a\log^2d')$, which leads to **enumeration**;
   * only if not small, Maróti's product case with $r\ge2$, which leads to product refinement;
   * otherwise a single alternating factor, which leads to normalization and `GiantStep`.

   HJ L1766–1772 has the same test. With $\ln|G|\le(\log_2D+1.5)\ln N$ (from $D!\le D^{D-1}$),
   `Small` holds once $a\ln N\ge\log_2D+1.5$. W1's "$+2$" is a valid sufficient condition, and Lean
   takes $a\ge128$.
3. **Why there is no giant step**, although $A_D$ is a section:
   * HJ's giants come only from a *primitive quotient* that is Cameron-large, i.e. Maróti's case
     with socle $\mathrm{Alt}(m)^r$ in product Johnson action (HJ L3067–3087, L3270–3276). $A_D$
     here is a section of the point stabilizer, not of the socle of any quotient.
   * In fact, for $m\ge2$, $S_D\wr C_m$ has no quotient $A_D$ or $S_D$. Its minimal normal subgroup
     is $A_D^m$, and a normal subgroup meeting it trivially would centralize it, hence be trivial.
4. **Why there is no product refinement**, although the action is a product action:
   * HJ's product refinement exists only for Maróti's Cameron product case, whose index is measured
     over $\mathrm{Alt}(m)^r$ (HJ L1506–1512, L3072–3080).
   * `Small` is tested first anyway.
5. With trivial kernel, enumeration "partitions the allowed relabelings into exhaustive cosets"
   (HJ L1365–1367). Lean `DispatchStep.ofEnumeration` makes one child per coset representative. So
   there are $|G|$ `Continue` children, each of which runs an orbit chain over $N$ singletons, and
   all of them are solved because the output is the full coset.

**(M′)** (RT §9(b), VR §4.0) recognizes only socle $(A_m^{(t)})^k$ with $m>4\log_2\binom mt$ and
$m>q_0$. Here the socle is abelian, so (M′) enumerates. It is used in phases with $d\le N^\alpha$,
which holds since $D$ is fixed.

**"Whatever the strings."** No early exit exists in `Solve` or `Continue`. W1's caveat about a
colour-count pre-check is appropriate.

**Remark (W1 L242–247), $P_d^m$ without primitivity: sound.** The coarsest primitive quotient is a
coordinate projection; its kernel is $1\times P_d^{m-1}$, acting identically on every slice. HJ's
orbit chain solves the first (largest) slice under the full kernel coset, which gives
$T(m)\ge|P_d|\,T(m-1)$.

### 1.6 Corollary 3.2 (W1 L251–263): sound, with two remarks

* **(1) is sound.** The tightness concerns string isomorphism only, as stated, and the GI transfer
  is explicitly disclaimed.
* **(2), sharpness of GNS 3.13(1).** It is correctly phrased as: for every odd $D$ there are
  infinitely many $n$ with option-1 primitive $\hat\Gamma_D$ groups of order
  $\ge n^{\log_2D-0.443}$. So $c_1\log d+c_2$ cannot be replaced by $o(\log d)$.
  * GNS contains no sharpness remark (searched for "tight", "sharp", "best possible": no hits).
  * Its proof of the affine case (G670–690, Thm `cor:primitive-size-type-1`) treats exactly this
    "irreducible but imprimitive linear group" case, $P\wr H$.
  * The example is standard, and I would not call the observation new; W1 itself says it is
    standard.
* **Cosmetic.** The summary table (W1 L30) says "instances of every size $N=2^{(D-1)m}$". The
  construction needs $m=2^j$, or more generally $m$ whose prime factors are all $\le D$. If a prime
  $p>D$ divides $m$, no transitive $K\le S_m$ lies in $\hat\Gamma_D$, since $p$ divides $|K|$.

**Verdict on claim 1: sound.** The lower bound is a genuine property of HJ's dispatcher as written
in the paper and formalized in Lean, and of (M′).

---

## 2. Claim 2: Prop. 3.3, the family is FPT (W1 L265–299)

### 2.1 The recurrence is correct

* With $w=(p,w')$ and $z=(a,z')$, the condition $y(u',p(a),w'(z'))=x(u,a,z')$ for all $a,z'$ is
  exactly $w'\in\bigcap_a\mathrm{ISO}_{i+1}(ua,u'p(a))$ (W1 L280).
* The base case is $i=m$. The answer is $\mathrm{ISO}_0$.
* Enumerating $K$ reduces $G$ to $P^m$, since $G=P^m\rtimes K$.

### 2.2 Gap (low): the group part of each table entry

* $\mathrm{ISO}_i(u,u')$ is defined from $x$ to $y$, so $\mathrm{ISO}_i(u,u)$ is **not**
  $\mathrm{Aut}_{W_i}(x_u)$, and the "$p=1$ part" (W1 L285) is a coset, possibly empty, not a group.
* The algorithm still works, but the text should say how the group is obtained:
  * the group part of every nonempty $C_p$ is $\bigcap_a\mathrm{Aut}(x_{ua})$, returned by
    Coset-Inter;
  * $\mathrm{Aut}_{W_i}(x_u)$ is generated by that kernel together with
    $\sigma_{p_0}^{-1}\sigma_p$ over the feasible $p$, where $\sigma_p=(p,\tau_p)$.

  Alternatively, keep a second table for $x\to x$.
* The cost is unchanged.

### 2.3 ADKT is cited correctly

* **Coset-Inter** (ADKT txt L258–261) requires the partition $\Omega=\bigsqcup C_i$ to be stable
  under $G$, $H$ **and both representatives**.
* **Thm 5** (txt L320) gives $2^{O(b)}n^{O(1)}$.
* In Prop. 3.3, all cosets live in $P^{m-i-1}$ acting on $V=\bigsqcup_j\Delta_j$, and every
  $\Delta_j$ is stable under groups and representatives. So Thm 5 applies with $n\le bm$ and
  $b=2^{D-1}$, which gives $2^{2^{O(D)}}$.
* The count is $\sum_i b^{2i}\le2N^2$ table entries, times $|P|$, times $b$ intersections, times
  $|K|\le m\le\log N$. That gives $2^{2^{O(D)}}N^2\mathrm{polylog}\,N$, as claimed.
* ADKT Thm 1 (Schreier generators, txt L167) and Thm 6 (the DP over $(i)$-blocks, txt L341) say
  what W1 §1.2 says they do.

**Cosmetic.** "$|K|\le D^{m-1}$ by BCP" (W1 L272) needs $d\ge6$ in every version (RT §6). For
$D=3,5$, use Dixon's solvable bound $24^{(m-1)/3}$ or Maróti Cor. 1.5. The conclusion
$|K|\le N$ still holds.

### 2.4 Novelty: Prop. 3.3 is an instance of published theorems

* **SW19 Thm `theo:obj`** (`articles/hereditarilyFiniteObjects.tex` L19–27): canonical labelling of
  any object $(\mathcal X,\Delta\rho)$ over $V$ in $2^{O(k)}n^{O(1)}$, where $k$ is the largest
  $\Delta$-orbit on $V$. Encode $x$ as the coloured set of transversals
  $\{(\{(j,z_j)\}_j,x(z))\}$ over $V$. With $\Delta=P^m$ we get $k=b$. So
  $\mathrm{SI}(P\wr K)\le|K|\cdot2^{O(b)}N^{O(1)}$ directly.
* The **"small faithful degree" remark** (W1 L293–299) is the same theorem with $k=|V|$, or ADKT
  Thm 6 followed by Thm 5 with a single colour class. So it can be relabelled "[PROVEN mod ADKT
  Thms 5–6 / SW19]", both of which were read. It does not need Luks 1999, which was never read.
* W1 says "the idea is ADKT's DP, written for strings", so no novelty is overclaimed. But W1 lists
  SW19 as "abstract only" and misses that SW19 settles this family outright.

**Verdict on claim 2: sound.** One presentation gap (§2.2). The FPT algorithm is off the shelf.

---

## 3. Claim 3: Prop. 4.1 and Theorem E (W1 L361–482)

### 3.1 Prop. 4.1 (W1 L377–409): sound, with the same group-part slip

* **Recurrence.** I checked both directions of "$h\in K_Bh_\sigma$ lies in
  $\mathrm{Iso}(B,B')$ iff $h|_{C_i}\in\mathrm{Iso}(C_i,C'_{\sigma(i)})$ for all $i$":
  * "if": the string condition depends only on the restriction;
  * "only if": take $g$ itself.
* **Translation.** $(K_Bh_\sigma\cap\Pi_\sigma)h_\sigma^{-1}=K_B\cap\prod_iA_iz_i$ with
  $z_i=\tau_i\,(h_\sigma^{-1})|_{C'_{\sigma(i)}}$. This is the restriction of an element of
  $G_{C_i}$, so $z_i\in H_{C_i}$, using $G_{C_i}\le G_B$.
* **Counting.** At most $|P_B|$ choices of $\sigma$. At most $(2N+1)^2$ block pairs, since levels
  at least double.
* **Slip.** W1 L374–375 defines $\mathrm{Aut}(B):=\mathrm{Iso}(B,B)$ with $\mathrm{Iso}$ going from
  $x$ to $y$, which is not a group. PCI needs $A_i=\mathrm{Aut}_x(C_i)$. The fix is as in §2.2: an
  $x\to x$ table, or differences of representatives. It at most doubles the cost.
* **Primitivity and maximality are never used.** The proof needs only a $G$-invariant nested
  hierarchy with $G_C\le G_B$ for every child $C$ of $B$. This matters in §3.3 and §4.

### 3.2 Theorem E (W1 L424–467): sound

I re-derived every step.

* **$R_i\trianglelefteq H_{C_i}$.** $G_{C_i}|_B\subseteq H_B$ normalizes $K_B$. Restriction to
  $C_i$ is a homomorphism on the stabilizer of $C_i$, and $K_B$ fixes $C_i$.
* **$\prod_i|R_i:M_i|=\varepsilon_B$.** $K_{\ge1}=K$, $K_{\ge r+1}=1$ (faithful on $B$), and
  $|K_{\ge i}:K_{\ge i+1}|=|M_i|$.
* **Step 1.**
  * $A_iz_i\cap R_i$ is empty or a right coset of $A_i\cap R_i$.
  * Intersecting with a subgroup normalized by $A_i$ is polynomial. Concretely: $\{(gh,g)\}$ is a
    group on $\Omega\sqcup\Omega'$, and its pointwise stabilizer of $\Omega$ projects to
    $A_i\cap R_i$.
  * A decomposition $z_i=ar$ comes from tracking the "$A$-part" along the Schreier–Sims
    straight-line programs.
  * Both are in the standard toolkit, as W1 claims.
* **Step 2.**
  * The solution set is $\{yw:y\in Y,\ yc\in X\}$, a single coset $Y_0y_jw$ or empty.
  * $|Y:Y_0|=|YX|/|X|\le|R_i:X|\le|R_i:M_i|$, using $M_i\le X$ because
    $K_{\ge i}\le L_{i-1}$.
  * The transversal and the generators of $Y_0$ come from Schreier with a membership oracle for
    $X$ (ADKT Thm 1).
* **Step 3.** $L_i=\pi_i|_{L_{i-1}}^{-1}(Y_0)$ and $w_i=\ell w_{i-1}$ with
  $\pi_i(\ell)=y_jc\in X$. Both are correct.

**How the cosets compose, and whether $\max_B\varepsilon_B$ is the right parameter.**
* *Inside one PCI* nothing branches past a step: each step returns one exact coset.
  * The cost is $\sum_i|R_i:X_i|\le\sum_i|R_i:M_i|\le\varepsilon_B+r-1$, since the factors are
    $\ge1$ and their product is $\varepsilon_B$.
  * So W1's bound $r\varepsilon$ is generous. The sharper parameter is
    $\max_i|R_i:M_i|$ for the best child ordering, which is at most $\varepsilon_B$.
* *Across levels* nothing compounds. Every PCI output is stored as an exact coset in the memo table,
  and parents read it without branching.
* So the maximum over blocks is the right quantity. A product of indices over levels would arise
  only in a no-memo top-down recursion, which is the compounding of W1 §3.3. The total is
  $\le\sum_{(B,B')}|P_B|(\varepsilon_B+r_B)\mathrm{poly}\le\pi_0\,\varepsilon\,\mathrm{poly}(N)$.

### 3.3 Gap (low): the tree-group corollary needs an aligned tree

* "For tree groups of node degree $\le b$ this is $b!\,\varepsilon\,\mathrm{poly}(N)$" (W1 L433)
  assumes every $|P_B|\le b!$.
* Prop. 4.1's tree comes from *arbitrary* maximal chains, one per orbit. W1 does not say they refine
  the given tree $T_0$, and I could not rule out a non-aligned chain with a primitive component of
  degree $>b$.
* **Fix.** Run Prop. 4.1 on $T_0$ itself, which is legitimate by §3.1's last bullet, or on a maximal
  chain refining $T_0$'s level partitions. Then $P_B\le S_b$, and $\varepsilon$ is measured on that
  tree.
* $\varepsilon$ depends on the chosen tree, so it is $\varepsilon(G,\mathcal T)$, not an invariant of
  $G$. W1 L427 writes $\varepsilon(G)$ (cosmetic).

### 3.4 Upgrade: abelian entanglement is provable with the standard toolkit

W1 L475–477 is a [SKETCH] that invokes Kantor–Luks. A simpler argument:

* If $R_i/M_i$ is abelian, every subgroup between $M_i$ and $R_i$ is normal in $R_i$. In particular
  $X\trianglelefteq R_i$, and $X$ is normalized by $Y\le R_i$.
* Then $Y_0=Y\cap X$ is an intersection with a normalized subgroup (polynomial).
* The coset step $yc\in X$ asks whether $c\in YX$, a group because $X$ is normal. The decomposition
  comes from the same straight-line-program trick as step 1.
* No index bound is needed. So arbitrary abelian (more generally, Dedekind) $R_i/M_i$ gives
  $\pi_0\,\mathrm{poly}(N)$.

This argument is mine ([ARGUED HERE]) and was checked once.

### 3.5 Novelty

* **Prop. 4.1** is ADKT Thm 6 / Luks-1999 DP transplanted from "$(i)$-blocks of hyperedges" to "a
  block hierarchy of $G$". The transplant is routine, and W1 says so (L479).
* **Theorem E.**
  * The $\varepsilon=1$ case is folklore: it is labelled-tree isomorphism with $P_B$-restricted
    child permutations, and for canonization "sort the children's forms", as W1 §4.5 itself notes.
  * The bounded-index step is the classical Sims / Furst–Hopcroft–Luks bounded-index tower
    (ADKT Thm 1).
  * I found **no prior statement** of the parameter $\varepsilon_B$ or of Theorem E. Places
    checked: ADKT; SW19's framework, which is parameterized by orbit size on the ground set, not by
    subdirect index; Wiebking arXiv:1904.10454; GNS; Neuen ICALP'20; the survey; and two web
    searches (one extended).
  * The search was limited. The Luks–Miyazaki normalizer papers and Babai–Luks 1983 were not read.
* **Assessment.** It is plausibly new as a stated parameterization, but it is an elementary
  combination of known tools. Treat it as a lemma that locates the difficulty, which is exactly how
  W1 L480–482 describes it.

**Verdict on claim 3: sound.** Prop. 4.1 has a group-part slip, and the tree-group corollary needs
the alignment remark.

---

## 4. Claim 4: Prop. 4.2, SI ⇔ CI for tree groups (W1 L484–513)

### 4.1 (⇒), $\mathrm{SI}\le4N^2b!\cdot\mathrm{CI}$: gap (low-medium), fixable

* As written, it goes "by Prop. 4.1", whose tree has a **virtual root whose children are the
  $G$-orbits**.
* For an intransitive tree group (the common case, including every $K_B$ in a PCI), the root PCI is
  $G\cap\prod_O A_Oz_O$.
  * The root then has one child per orbit, which can be far more than $b$.
  * $\prod_OA_O$ is in general **not** a subgroup of $\mathrm{Aut}(T_0)$.
* **Example.** Leaves $\{1,2\},\{3,4\}$ and $G=\langle(13)(24)\rangle$. The orbits are $\{1,3\}$ and
  $\{2,4\}$. The product of orbit restrictions contains $(13)$, which breaks the block $\{1,2\}$.
* So the root instance is not in $\mathrm{CI}(b,\cdot)$.
* **Fix.**
  * Run the DP on $T_0$ directly (§3.1). Every PCI is then $K_B\cap(\prod_iA_i)z$ with both groups
    in $\mathrm{Aut}(T_0|_B)$ and $\le b$ children.
  * Alternatively, replace the virtual root by a binary tree over the orbits and use chains aligned
    with $T_0$.
  * Contract unary nodes so that there are $O(N)$ nodes. Add "$+\mathrm{poly}(N)$" per instance.

### 4.2 (⇐), $\mathrm{CI}(b,N)\le\mathrm{SI}(b,N^2)$: sound, with a padding remark

* $(g_1,g_2)$ fixes the diagonal indicator iff $g_1=g_2$ (faithful action).
* The interleaved pair tree has node degree $\le b$ and $N^2$ leaves, and $G_1\times G_2$
  preserves it.
* A coset instance becomes a group instance by $y\mapsto y^{(a,c)^{-1}}$, so $a,c$ need not lie in
  $\mathrm{Aut}(T)$.
* This is the classical Luks diagonal trick; it is literally the proof of ADKT Thm 5
  (txt L322–330).
* **Gap (low).** "Pairs of equal-depth nodes" needs all leaves at the same depth. Pad $T$ with unary
  nodes; tree automorphisms preserve depth.

**Equivalence.** With both repairs, FPT for SI and FPT for CI (both over tree groups, both
parameterized by node degree) imply each other: $f(b)N^c$ for SI gives $f(b)N^{2c}$ for CI.

**Novelty.** Both directions are standard reductions (the DP of ADKT/Luks-1999 and Luks's diagonal).
What is new is the observation that both stay inside tree groups of node degree $\le b$. I found no
earlier statement of the tree-group CI question. The nearest precedent is ADKT p. 3: "an fpt
algorithm for Set Transporter w.r.t. groups in $\Gamma_d$ … would result in an fpt algorithm for …
graphs of degree $\le d$". It is a useful formulation, not a deep result.

**Verdict on claim 4: sound after the two repairs.**

---

## 5. Claim 5: literature and the ETH argument (W1 L53–149)

| item | checked against | verdict |
|---|---|---|
| Downey–Fellows posed FPT by degree | survey L67–68 ("already the first book by Downey and Fellows [17] asks for fpt algorithms for GI parameterized by the maximum degree and the tree-width"); Grohe–Neuen concluding remarks | **sound**. *Cosmetic:* W1 L58–59 says it is also "quoted … in ADKT p. 3". ADKT p. 3 (txt L110–114) poses the question for degree, tree width and genus itself and cites Downey–Fellows only as the founders of the field. |
| GNS conclusion | G2278–2280, verbatim | **sound** |
| Grohe–Neuen Q4 | `paper.txt`, concluding remarks, Q4, "Is GI parameterized by maximum degree number fixed-parameter tractable?" | **sound** |
| Survey: "wide open", Q4.8, Lemma 4.5, SSI | survey L485–490, L507–516, L538–543 | **sound**, all four statements match |
| Neuen ICALP'20 asks $n^{O((\log d)^c)}m^{O(1)}$ | conclusion, `hypergraph-gamma-d.tex` L3137–3145 | **sound** |
| Otachi–Schweitzer obstacle quote | new download, `paper.txt` L56–57: "the uncertainty whether the standard reduction techniques, like showing W[1]-hardness, can be applied" | **sound** (W1 had only read the abstract) |
| Arvind–Köbler–Kuhnert–Torán W[1]-hardness | search snippets only (STACS'17 LIPIcs 66:7; IPEC'17): exact-weight automorphism is W[1]-hard with colour classes of size 4 inside Red | **consistent**; full text not read |
| Neuen–Schweitzer graphs have bounded colour classes | ar5iv introduction: "seen as colored graphs, our graphs have bounded color class size and as such isomorphism … can be decided in polynomial time using simple group theoretic techniques" | **sound** (W1 had only read the abstract, which does not say this) |
| No W-hardness known; no lower bound for coset-recursion classes | survey (no hardness statement for these parameters), RT §7, my own knowledge | **consistent**; not provable by search |
| Best bounds: Luks, BKL, GNS, R\* | standard | **sound** |

**ETH argument (W1 L128–130): sound.**

Suppose an fpt-reduction maps $k$-Clique instances of size $n$ to GI instances of size
$\le f(k)n^c$ and maximum degree $\le g(k)$. GNS then decides $k$-Clique in
$f'(k)\,n^{O((\log g(k))^{c'})}$. ETH forbids $f(k)n^{o(k)}$ (Chen et al.). So
$(\log g(k))^{c'}\ne o(k)$, i.e. $g(k)\ge2^{\Omega(k^{1/c'})}$ for infinitely many $k$.

* This holds for Turing fpt-reductions too.
* Under R\* (conditional on HJ) it strengthens to $g(k)\ge2^{\Omega(k)}$.
* Babai's quasi-polynomial bound alone would not suffice; GNS is what makes the argument work. W1
  uses GNS, so this is correct.

*Cosmetic.* W1 L84 says "from their proof $c\ge4$". A proof yields an upper bound, so the
intended statement is "their proof gives an exponent $c$ of about 4". RT §7 says $c\ge3$ plus a
domain blow-up.

**Verdict on claim 5: sound.**

---

## 6. Also checked (not in the task list)

* **§3.3 compounding reduction (W1 L303–312).** It is a tautology about a model (cost $\ge c(q)^L$),
  correctly labelled. The application to HJ is correctly labelled [CONDITIONAL]/[SKETCH] and is not
  claimed as proven.
* **$\mathcal W_L$ has $\varepsilon=1$ (W1 L314–320).** Checked level by level: the root kernel is
  the full base group $W_{L-1}^{q(q-1)}$; at a row the kernel is $W_{L-1}^{q-1}$; at a point the
  kernel is the base of $W_{L-1}$. All primitive components are $S_q$ or $S_{q-1}$, so Theorem E
  gives $q!\,\mathrm{poly}(N)$. Correct. One clarification is needed: "$S_q$ on ordered pairs" must
  mean *off-diagonal* pairs for the action to be transitive.
* **§4.5, "canonization fails for diagonal kernels".** Correct. Example: $H=S_3$ acting diagonally,
  $x_1=x_2=100$ and $x_2'=010$. The separate canonical forms agree, but the joint orbits differ.

---

## 7. What I could not check

* Dixon–Mortimer Lemma 2.7A and the submodule lattice of the $\mathbb F_2S_D$ permutation module are
  checked from memory and by the direct argument in §1.1, not from the books.
* (H0), i.e. HJ's correctness. It is irrelevant to claim 1, which is a lower bound on what HJ's
  dispatcher *does*. That behaviour is read off the pseudocode (HJ L1136–1172, L1154, L1365–1367)
  and the Lean `dispatch`, but not executed.
* Luks STOC'99, Babai–Luks 1983, the Luks–Miyazaki normalizer papers, and the full text of
  Arvind–Köbler–Kuhnert–Torán. The novelty search for Theorem E and Prop. 4.2 is therefore not
  exhaustive.
* Whether a non-aligned maximal chain of a tree group can have a primitive component of order
  $>b!$. I sidestepped this with the alignment fix (§3.3).

---

## 8. Overall verdict and the statements I would sign

**Overall.** No break. Claims 1, 2 and 5 are sound. Claims 3 and 4 are sound after low-severity
repairs: give the automorphism group of each table entry explicitly, and run the DP on the given tree
rather than on per-orbit maximal chains under a virtual root. Novelty is modest throughout:
* Prop. 3.3 is an instance of SW19 / ADKT.
* Prop. 4.1 is ADKT/Luks DP on a block hierarchy.
* Theorem E is new as a parameterization but elementary.
* Prop. 4.2 is a clean formulation built from two standard reductions.
* The barrier is the real contribution. It is not deep, but it is correct and specific to HJ.

**Signed statements.**

1. **(Barrier)** For odd $D\ge3$, $d=D-1$ and $m=2^j$, the group $G_{d,m}=(\mathbb F_2^d\rtimes S_D)\wr C_m$
   in product action on $N=2^{dm}$ points has these properties:
   * it is primitive and affine, and lies in $\hat\Gamma_D\setminus\hat\Gamma_{D-1}$;
   * $\log_N|G_{d,m}|=1+\frac{\log_2D!}{D-1}+\frac{\log_2m}{(D-1)m}>\log_2D-0.443$;
   * on every instance $\mathrm{SI}(G_{d,m},x,y)$ with $N>N_0$, HJ's `Solve` as specified (HJ
     L1136–1172 with the order test L1766–1772; Lean `PrimitiveQuotient.dispatch`) and HJ with
     dispatcher (M′) both create $|G_{d,m}|$ enumeration children at the root.

   Hence R\*'s exponent $O(\log d)$ is tight for that algorithm, for string isomorphism. Likewise,
   $c_1\log d+c_2$ in GNS Thm 3.13(1) cannot be improved to $o(\log d)$.
2. **(FPT family)** $\mathrm{SI}(P\wr K)$ in product action on $\Delta^m$, with $|\Delta|=b$, is
   solvable in $|K|\cdot|P|\cdot2^{O(b)}N^2\mathrm{poly}(bm)$ (ADKT Thm 5), or in
   $|K|\cdot2^{O(b)}N^{O(1)}$ (SW19 `theo:obj`). For $G_{d,m}$ this is $2^{2^{O(D)}}N^{2+o(1)}$.
3. **(DP and Theorem E)** Let $\mathcal T$ be any $G$-invariant nested block hierarchy with
   $G_C\le G_B$ for every child $C$ of $B$. String isomorphism reduces to
   $\sum_{(B,B')}|P_B|$ PCI instances, with $O(N^2)$ block pairs. Each PCI at $B$ is solvable in
   $(\varepsilon_B+r_B)\,\mathrm{poly}(N)$, where
   $\varepsilon_B=|\prod_i\pi_i(K_B):K_B|$. So the total is
   $\max_B|P_B|\cdot\max_B\varepsilon_B\cdot\mathrm{poly}(N)$. The same holds with
   $\varepsilon_B$ replaced by 1 when every $\pi_i(K_B)/M_i$ is abelian. For $G\le\mathrm{Aut}(T_0)$
   with node degree $\le b$, taking $\mathcal T=T_0$ gives $b!\,\varepsilon\,\mathrm{poly}(N)$.
4. **(Tree groups)** For subgroups of $\mathrm{Aut}(T)$, with $T$ of node degree $\le b$ and leaves
   at equal depth after padding:
   $$\mathrm{SI}(b,N)\le O(N^2)\,b!\,(\mathrm{CI}(b,N)+\mathrm{poly}(N)),\qquad
   \mathrm{CI}(b,N)\le\mathrm{SI}(b,N^2)+\mathrm{poly}(N).$$
   So the two are FPT-equivalent.
5. **(Literature)** FPT for GI by maximum degree is open (Downey–Fellows; GNS; Grohe–Neuen Q4;
   survey §4.1). Survey Q4.8 is as quoted. Under ETH, any W[1]-hardness proof must blow the
   parameter up to $2^{k^{\Omega(1)}}$ infinitely often (to $2^{\Omega(k)}$ if R\* holds).
