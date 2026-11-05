# Red-team report on `docs/w1-structure.md`

Branch `w2-redteam-structure`, 2026-11-05. Target: the claims of `docs/w1-structure.md` ("W" below;
"W L…" is a line of that file). Background: `verify-theorem-R.md` ("VR"), `redteam-theorem-R.md`
("RT"), `w1-fpt.md` ("FPT"), `redteam-w1-fpt.md`, `moonshot-theory.md`.

**Sources.**
* "HJ L…" is a line of `scratchpad/paper/graph_isomorphism.tex` (arXiv:2611.01399v1).
* "Lean" means `~/math/GraphIsomorphismLog2/Workspace`. It was read only (`Algorithm/Dispatch.lean`);
  lean and lake were never run.
* "G…" is a line of GNS, `r4-sources/arxiv-1802.04659/x/bounded-degree-polylog-d.tex` (and its `.bbl`).
* "SW `file` L…" is a line of Schweitzer–Wiebking arXiv:1806.07466, source in
  `r4-sources/w1s-arxiv-1806.07466/x/articles/`. I read `hereditarilyFiniteObjects.tex` (Theorem
  `theo:obj`), `heredit.tex` (definitions, CL1/CL2, input size), `objectReplacement.tex` and
  `preliminaries.tex`.
* Wiebking arXiv:1904.10454: introduction and open questions, `r4-sources/w1s-arxiv-1904.10454/`.
* No new downloads were needed.

**Executed.** One 30-line Python script (`scratchpad/w2rs-scripts/check.py`, run with `python3 -I`,
a few milliseconds). It recomputed Table 2.3, the constant in $\lvert\mathrm{GL}(r,2)\rvert$, the
option-2 threshold of §4.2, and the inequality chain of Lemma 4.3. Nothing else was run.

**Severity scale.**
* *Break*: the claim is false and cannot be repaired.
* *Gap*: the claim is true, or true after a stated repair, but the written argument misses a step
  or states it wrongly.
* *Overstatement*: the claim as worded covers more than is proved.
* *Cosmetic*: a wrong constant or wording that does not affect the result.

---

## 0. Verdicts

| # | claim (W lines) | verdict | defects |
|---|---|---|---|
| 1 | Prop. 2.1 $\mu$ bound, Prop. 2.2 coordinate type, Table 2.3 (L108–202) | **sound as a SKETCH; no counterexample** | Gap (low): parameters must be section-closed (§1.4). Gap (low, in 2.2): the case list leans on an unstated classification of large irreducible linear groups, and "components of degree $\le f(d)$" fails for products of diagonal groups with large top groups (§1.5). W's own GSS98 caveat is unnecessary, because W's own bullet already proves the bound (§1.2). Table: all 8 rows recomputed exactly. |
| 2 | Theorem R\*\*, Cor. 3.1 (L206–237) | **sound, conditional on (H0) + Prop. 2.1** | Gap (low): "the class is closed under sections" is **false** for the composition-factor class, because classical factors have alternating subgroups and vice versa. Fix: use HJ's own $\mathrm{aw}$ and a section-closed $\lambda$; the exponent changes only by a constant (§2.2). The per-channel costs check out (§2.1). The replacement of GNS 3.13 by Prop. 2.1 is legitimate: every input is $d$-free (§2.3). |
| 3 | "Recurse on $H$" trap, §4.2–4.4 (L254–308) | **sound** | Cosmetic: the option-2 threshold "$2j\gtrsim m/(4\log m)$" is wrong. The true threshold is larger ($t^*=12$ at $m=257$, $44$ at $1025$, $419$ at $10^4$). The conclusion uses only middle layers, so it is unaffected (§3). |
| 4 | Theorem L, Prop. 4.1 (L310–396) | **sound** (decision, mod S-W) | S-W `theo:obj` says exactly what is used (§4.1). Orbit-objects, invariance, completeness and equivariance re-derived (§4.2). Gap (low): the coset sketch omits generators of $\mathrm{Aut}_R(x)$. A complete repair is given (§4.3), so the coset version is **PROVEN mod S-W**. Gap (low): the tower data are assumed given (§4.4). |
| 5 | Example C $G_{r,L}$, Prop. 4.2, Lemma 4.3, entanglement (L398–445) | **sound** | HJ really enumerates: the block systems of $G_{r,L}$ form a chain (proved here), the quotient is affine, and Lean tests `Small` first (§5.2). Cosmetic: Lemma 4.3's "$\ge2^{r(L-1)}/L\ge N/(dL)$" is false as a chain. The correct bound is $N/((d+1)L)$ (§5.3). Cosmetic: "$-o(1)$" hides $-1.8/r$, which is not $o(1)$ at fixed $d$ (§5.2). |
| 6 | Prop. 4.4, decoupled HJ row (L447–469) | **sound as a reduction; children payable with $\Lambda=O(1)$** | Gap (low–medium): the terminal twisted instance costs $\lvert P\rvert\,\mathrm{poly}(s)$. That is not a toll HJ's Lemma 7.1 can absorb (it allows $N^aK_N$). It needs a global factor $\max\lvert P\rvert$ in $K_N$. The "$2^{O(k_0)}$" alternative is unsupported when $Q\ne1$ (§6). |
| 7 | Consequences, $d=O(\log n)$ (L58, L540–547, L65–67) | **overstatement, fixable** | "Every family in §4.5–4.6 costs $2^{O(d)}N^{O(1)}$" is false for row (c) with $\lvert Q\rvert=2^{\omega(d)}$ and for Theorem L with superpolynomial $\lvert R_j\rvert$. "All decoupled families are polynomial" is not proved. The correct list is in §7. **No overclaim for graphs**: W disclaims the GI transfer everywhere it matters. |

**No break found.** Every [PROVEN] item is true as stated or after a one-line repair. The two
[SKETCH] items (Prop. 2.1/2.2 and Theorem L's coset assembly) hold up. Theorem L's coset version
can be upgraded to PROVEN mod S-W. The real defects are an overstated consequences paragraph and
a toll-accounting gap in Prop. 4.4.

---

## 1. Claim 1: classification (W L95–202)

### 1.1 What I checked

I went through the O'Nan–Scott types in W L117–146 against the inputs GNS uses (G600–822): Thm
3.7 (= LS02/LS14, G632–655), Lemma 3.8 (Cooperstein/Kleidman–Liebeck, G657–667), Thm 3.10
(Liebeck 1984, G711–730), Lemmas 3.11–3.13 (G735–822), and BCP / Maróti Cor. 1.5 as checked in
RT §6. For each type I re-derived W's inequality and looked for a primitive group that beats it.

### 1.2 The bound type by type

* **Type I, primitive linear** (W L122–126). GNS Thm 3.7 is stated for *every* primitive affine
  group with $G_0$ primitive linear (G632–645), with no $\hat\Gamma_d$ hypothesis. The proof cites
  LS14 Prop. 2, $b^*\le9d_i+22$ or $3\log_pm_i+22$ (G653), which already separates
  classical-dimension and alternating contributions. A component $\mathrm{Alt}(m)$ or a cover of it
  in $F^*(H^0)$ acts faithfully on $V$. Its minimal projective degree is $\ge m-2$ for $m\ge9$
  (Wagner), so $\log m\le\log\log d'+O(1)$, as W says. Mixed alternating/classical $F^*$ gives
  $b\le C(1+\lambda+\log m_{\max})$, which is still the claimed form. **Sound** [TRUST LS14 via GNS].
* **Type I, imprimitive linear** (W L127–131). W's own bullet proves the order bound directly:
  * choosing $\ell$ maximal makes $H_0$ primitive (a finer decomposition of $W$ transports
    consistently along coset representatives);
  * $\lvert H\rvert\le\lvert H_0\rvert^\ell\lvert K\rvert$ and $\lvert H_0\rvert\le\lvert W\rvert^{b(H_0)}$;
  * $\log\lvert K\rvert/\log d'\le\min(\log_2w,\log_2\ell)$, using BCP (Maróti Cor. 1.5) and $\ell\le\log_2d'$.

  This **does not need GSS98 Lemma 4.2(a)**. W's caveat at L148–151 can be dropped: GNS need
  GSS98 for a *base* bound, but W only needs an order bound. Here $K$ is a quotient of
  $H\cong P/V$, so its composition factors are among $P$'s and BCP applies.
* **Type II** (W L132–138). Liebeck's four cases (G712–730) are handled correctly.
  * Johnson outside option 2 gives $\log_2d'\ge m/4$, so $\mu\le4\log_2m!/m=O(\log m)$.
  * Partitions give $d'=2^{\Omega(m)}$ (G758–762).
  * Classical on subspaces gives $\mu\le r^2/(r-1)+o(1)\le r+2$ for $\mathrm{PSL}$; it is smaller
    for $\mathrm{Sp}$, $\Omega$, $\mathrm{SU}$. $\log\lvert\mathrm{Out}\rvert\le\log(2rf)$ is negligible.
  * Non-standard groups: $\lvert G\rvert\le n^9$.

  W's route through the natural dimension $r$ replaces GNS's minimal-degree argument (G764–776)
  and needs no $\hat\Gamma_d$. **Sound.**
* **Types III, V** (W L139–146). The direct count $\lvert P\rvert\le\lvert T\rvert^k\lvert\mathrm{Out}\,T\rvert\lvert K\rvert$ with
  $d'=\lvert T\rvert^{k-1}$, or $\lvert P\rvert=d'\lvert K\rvert$, plus BCP replaces GNS Lemma 3.12 (GSS98 with $\ell=\log d$). **Sound.**
* **Type IV** (W L142–144). $\mu(P)\le\mu(Q)+\log\lvert K\rvert/(k\log m')$ is correct, and $K$ is a
  quotient of $P$. The component $Q$ is only a quotient of a subgroup of $P$, which needs the
  section-closed parameters of §1.4. **Sound after §1.4.**

**Counterexample search.** A violation needs $\mu\gg\lambda+\min(\log w,\log\log d')$. That forces
large order from alternating sections at small degree. Each placement fails:
* in the socle: option 2, excluded, or Johnson with $d'\ge2^{m/4}$;
* in a top group: $d'\ge5^k$;
* in a linear point stabiliser: $d'\ge2^{m-2}$.

I also tried the following, and none comes close:
* tensor products $\mathrm{GL}(a)\otimes\mathrm{GL}(b)$, where $\mu\approx1+b/a$ but $\lambda\ge b$;
* tensor-induced $\mathrm{GL}(2,3)\wr S_\ell$ and extraspecial normalisers, where $\mu\to1$;
* $\mathrm{AΓL}$ over huge fields, where $\mu\le3+o(1)$;
* $A_m$ on cosets of maximal subgroups (Liebeck case 4);
* exceptional groups and sporadics.

**No counterexample.**

### 1.3 Table 2.3 (W L177–188)

All eight rows were recomputed with exact formulas:
* $\mu$ = 7.609, 9.573, 6.406, 6.995, 6.234, 2.286, 12.851, 11.851;
* $\log_2d'$ = 256, 1024, 811.5, 315.5, 1188.8, 3018.4, 12, 12.0.

All match W. The $S_{320}$ row is indeed outside option 2 ($4\log_2\binom{320}{159}=1262>320$). The
irreducibility claims (L189–192) are standard and correct; for the monomial group, the sign
characters are distinct, so the isotypic components are the coordinate lines.

### 1.4 Gap: the parameters must be section-closed

$w$ and $\lambda$ are defined through **composition factors** (W L100–102). But Prop. 2.1 is applied
to quotients of subgroups (Type IV components; in R\*\* every primitive quotient HJ meets).
Composition factors of a subgroup are only *sections* of the original factors, and:
* $\mathrm{PSL}(\lambda,q)$ has subgroups with factor $A_{\lambda+1}$ (permutation matrices on the
  deleted permutation module);
* $A_w$ contains $\mathrm{PSL}(r,2)$ for $2^r-1\le w$.

**Fix.** Use $w^\sharp:=\mathrm{aw}(G)$ (HJ's own alternating width, HJ L653–656 and L3090–3096, defined through
quotients of subgroups) and $\lambda^\sharp$ := the largest dimension of a classical *section*.
* Both are monotone under subgroups and quotients, and both dominate the composition-factor
  versions, so Prop. 2.1 holds with them verbatim.
* Conversely, $w^\sharp\le\max(w,\lambda+2,c)$ by Feit–Tits/Kleidman–Liebeck minimal degrees of
  sections, and $\lambda^\sharp\le\max(\lambda,\log_2w+O(1))$.
* So any statement of the form $C(1+\lambda+\log w)$ is unchanged up to the constant.

For $\hat\Gamma_d$, $w^\sharp\le d$ and $\lambda^\sharp\le\log_2d+O(1)$ by GNS Lemma 2.4 and Lemma 3.8.

### 1.5 Prop. 2.2 (W L153–173)

The logic is: if $\mu(P)>C_0$ and $P$ is not of coordinate type, then $d'\le f(d)$. I checked each
bullet of L163–168.
* Heart: $d'\le p^m$ with $p,m\le d$.
* Classical natural module: $q^{r-1}\le d$, so $d'=q^r\le d^2$.
* Almost simple: $d'\le\lvert T\rvert\lvert\mathrm{Out}\,T\rvert\le d!^{O(1)}$.

Two defects.
1. *Unstated input.* "Every other primitive linear case with $\mu>C_0$ has bounded $\lvert V\rvert$"
   needs more than LS14's *upper* bound on $b$. It needs that $\lvert H\rvert>\lvert V\rvert^{C_0-1}$
   forces a natural classical module, a heart module, or an extension- or subfield version of
   them. That is a Liebeck-1985-type classification of large irreducible subgroups ($\lvert H\rvert<q^{3n}$
   outside a list). It is true, but it is neither cited nor derived. The "tensor-decomposable"
   bullet (L167) is hand-waved; tensor products have $\mu\le3+o(1)$ and so never reach $C_0$.
2. *Compound diagonal products.* Take $P\le Q\wr K$ in product action with $Q$ diagonal,
   $T^j.(\mathrm{Out}\times K')$, and $K'$ a large solvable or affine-tower top group. Then
   $\mu(Q)\approx2+\log\lvert K'\rvert/((j-1)\log\lvert T\rvert)$ can exceed $C_0$ while $\deg Q=\lvert T\rvert^{j-1}$ is
   unbounded in $d$. So "components of degree $\le f(d)$" (L161) fails for the product
   coordinates. The fix is to take as coordinates the $jk$ simple factors of the socle, each of
   order $\le d!$, as in the diagonal bullet. The coordinate structure then exists, but the domain
   is not a product of component domains.

**Verdict on claim 1: sound as SKETCH**, with the two repairs above. It remains conditional on
LS14, Liebeck 1984 and the unstated classification.

---

## 2. Claim 2: Theorem R\*\* (W L206–237)

### 2.1 Per-channel costs (Cor. 3.1)

* **Product refinement (PR).** The multiplicity is $2^k\lvert K\rvert$ and the drop is
  $A(k-1)\Lambda$ (HJ L1506–1512, L3060–3062; RT §1.3). Per unit of $\rho$ the cost is
  $\log(2^k\lvert K\rvert)/(k-1)\le3\log2+\min(\log w^\sharp,\log k)$, with $k\le\log_5d'\le\log N$. The
  chain total is bounded by $\rho_{\rm root}\le2\log_2N$. So the cost per unit of $\log N$ is
  $O(1+\min(\log w,\log\log N))$. **Correct.**
* **(E2).** $\log((q_0!)^k\lvert K\rvert)/\log d'\le\log q_0!/\log17+\min(\log w,\log k)/\log17$. **Correct.**
* **(E1) α-part.** Prop. 2.1 gives $\mu\le C(1+\min(\log w,\log\log d'))$ per unit of $\log d'$,
  and $\sum\log d'_i\le\log N$ along a chain. **Correct.**
* **Formal form.** The proof uses one $\Lambda=C(\log w+\lambda+1)$ for all rows, so the exponent
  is a maximum of channels, not a sum. The table is a correct heuristic decomposition of where
  $\Lambda$ is needed.

### 2.2 Closure (W L215–220): gap, fixable

"The class is closed under sections" (L215) is false for the composition-factor class, for the
reason in §1.4. The places in the proof that need closure are:
* "giants have $q\le w$";
* caps initialised at $\min(d_i,w)$;
* BCP for top groups;
* Prop. 2.1 for every exposed quotient;
* $\mathrm{Sym}(C)$ configuration calls.

All of them hold with $w^\sharp=\mathrm{aw}(G)$ and $\lambda^\sharp$. HJ's caps are bounds on
$\mathrm{aw}$ by definition (HJ L642–656, L1431), and $\mathrm{aw}$ is what bounds giant degrees.
$\mathrm{Sym}(C)$ has $\lambda^\sharp\approx\log_2\lvert C\rvert$, which is within the budget. These calls run in
the HJ-verbatim regime anyway (RT §5).

The phase switch "w > N^α ⇒ HJ verbatim" (L220) remains valid: $\lambda\le\log_2N+O(1)$, since a
classical factor of a group on $N$ points embeds in $S_N$.

**Repaired statement.** With $w:=\mathrm{aw}(G)$ and $\lambda$ := the largest classical section
dimension, the bound $\exp(O(\log(N+2)(\log w+\lambda+1)))$ holds under (H0) + Prop. 2.1. By §1.4
this is equivalent, up to the constant, to W's composition-factor version.

### 2.3 "GNS 3.13 does not cover this class" (W L235–237)

This is handled correctly. The class contains groups such as $\mathrm{AGL}(\lambda,p)$ with $p\to\infty$
and $\mathrm{PSL}(2,q)$ with $q$ huge, which lie in no small $\hat\Gamma_d$. GNS 3.13's $\log d$
comes from $d$-dependent inputs:
* Lemma 3.8 (Cooperstein), turning rank into $\log d$;
* the minimal-degree argument of Lemma 3.11;
* GSS98 with $\ell=\log d$ in Lemma 3.12;
* BCP with parameter $d$.

R\*\* replaces 3.13 by Prop. 2.1, whose inputs are all $d$-free: LS14 through GNS Thm 3.7, which
has no class hypothesis (G632–645); Liebeck 1984; $\lvert\mathrm{Out}\,T\rvert=O(\log\lvert T\rvert)$; BCP/Maróti with
parameter $w^\sharp$; and direct counting. **The order bound used is valid** to the extent that
Prop. 2.1 is.

**Verdict on claim 2: sound**, conditional on (H0) and Prop. 2.1, after the §2.2 definition fix.

---

## 3. Claim 3: "recurse on $H$" re-creates enumeration (W L254–308)

* **Heart.** Individualising $B_0$ gives $G_{B_0}\to S_m$ acting on the weight layers as the Johnson
  action $S_m^{(2j)}$. Middle layers are not option 2: at $m=257$ and $t=128$,
  $4\log_2\binom{257}{128}\approx1008>257$. So (M′) enumerates $S_m$ there, at cost $m!$. HJ's orbit
  chain takes the largest orbit, the middle layer, first under the full $G_{B_0}$. The total is
  $d'\cdot m!=\lvert P\rvert$, with no saving. **Correct.**
  * Cosmetic: "for $2j\gtrsim m/(4\log m)$" (L260) is the wrong threshold. With $t=m/(4\log_2m)$
    one gets $4\log_2\binom mt\approx(m/\log m)\log(4\log m)<m$, so those layers *are* option 2.
    The exact first non-option-2 $t$ is 12 for $m=257$ (versus $m/(4\log_2m)=8.0$), 44 for
    $m=1025$ (25.6), and 419 for $m=10^4$ (188). It grows like $m/(4\log_2\log_2m)$. Only
    the middle layers are used, so the claim stands.
* **$\mathrm{AGL}(r,2)$.** $\mathrm{GL}(r,2)$ is transitive on $V\setminus0$. A second individualisation
  leaves blocks $\{w,w+v\}$ with quotient $\mathrm{GL}(r-1,2)$. So $T(2^r)\approx2^rT(2^{r-1})$, which
  gives $2^{\Theta(r^2)}=d'^{\Theta(\log d')}$. **Correct.**
* **§4.3 drop computation** (L272–285). I recomputed it:
  * middle layer of relative size $2\sqrt{2/(\pi m)}$;
  * $\rho$-drop $2(m-1)-2\lfloor\log_2\binom m{(m-1)/2}\rfloor\le\log_2m+2$;
  * $Q_d$-drop $\le\tfrac12\ln m\ln\tilde d$.

  The prefactor $(s+2)^D$ gains only $m^{O(D)}$, which is far below $2^{m}$. **Correct** as a
  statement about Lemma 7.1's induction (HJ L1643–1716).
* **§4.4** (L294–303). It is a correct upper bound on what $\Phi_\Lambda$ allots to a level of
  degree $2^{\Theta(m)}$. It is correctly labelled as a statement about the analysis.

**Verdict on claim 3: sound** (one cosmetic threshold).

---

## 4. Claim 4: Theorem L (W L310–396)

### 4.1 What S-W actually proves

* **Theorem `theo:obj`** (SW `hereditarilyFiniteObjects.tex` L19–27): a function
  $\mathrm{CL}(\mathcal X,\Delta\rho)$ solving Problem `prob:CL:Obj` "can be computed in time
  $2^{O(k)}n^{O(1)}$ where $n$ is the input size and $k$ is the size of the largest $\Delta$-orbit
  of $V$". The input is $(\mathcal X,\Delta\rho)\in\mathrm{Obj}(V)$ with $\Delta\rho\le\mathrm{Lab}(V)$, given by
  generators. **There is no other hypothesis**: no $\hat\Gamma_d$, no transitivity, and $V$ is an
  unordered set.
* **Output** (L10–16 there; definitions in SW `heredit.tex` L159–169):
  * (CL1) isomorphism invariance;
  * (CL2) $\mathrm{CL}=\mathrm{Aut}((\mathcal X,\Delta\rho))\pi$, where $\mathrm{Aut}((\mathcal X,\Delta\rho))=\mathrm{Aut}(\mathcal X)\cap\Delta$ (SW `heredit.tex` L117–120).

  An isomorphism $(\mathcal X,\Delta\rho)\to(\mathcal Y,\Delta\rho)$ must satisfy $\varphi^{-1}\Delta\rho=\Delta\rho$, i.e.
  $\varphi\in\Delta$. So **comparing canonical forms decides $\Delta$-isomorphism**, and the coset is
  $\mathrm{Aut}\cdot\lambda_x\lambda_y^{-1}$ (left-to-right composition). W's Prop. 4.1 step 3 (L327–328) is
  exactly right.
* **Input size** (SW `heredit.tex` L229–247): polynomial in $\lvert\mathrm{tranCl}(\mathcal X)\rvert+\lvert V\rvert+t_{\max}$,
  with objects stored as DAGs. The runtime proof (SW L75–85) is a DP over $\mathrm{tranCl}$. So W's
  tree-size bound $\prod_j\lvert R_j\rvert\lvert C_j\rvert$ (L393) is valid but pessimistic: the DAG size is
  $\mathrm{poly}(N\max_j\lvert R_j\rvert)$.
* **Atoms.** Points of $V$ and labelling cosets. Pure sets (from $t=0$) and tuples are native. So
  $\ulcorner x(p)\urcorner$, pairs and $\iota_j(c)$ are all legal.
* **Prop. 4.1's generic encoding** (L330–332), $\omega_0^g\mapsto g^{-1}\Delta_{\omega_0}\rho$, is well
  defined, injective and equivariant, with $(\Theta\tau)^\mu=\mu^{-1}\Theta\tau$ (SW `heredit.tex` L82–83).
  **Correct.**

### 4.2 The orbit-object proof, re-derived (W L360–394)

* **Definitions.** "Synchronised" (L365–366): $S\le\prod S_j$ acts by
  $(c_1,\dots,c_L)\mapsto(s_1c_1,\dots,s_Lc_L)$, so the same $s_j$ acts at every node of level $j$.
  Normality of $R$ holds: $s\,\tau_{j,p,\varrho}\,s^{-1}=\tau_{j,s(p),s_j\varrho s_j^{-1}}$.
  "Orbit-objects" (L377–378): $\mathrm{Obj}_x(p)$ is the $R_j$-orbit of the labelled arrangement
  $c\mapsto(\iota_j(c),\mathrm{Obj}_x(pc))$. Both definitions are precise.
* **Step 1 (invariance).**
  * A move at $p$ permutes the arrangements ($\varrho\mapsto\sigma^{-1}\varrho$).
  * A move below $pc$ fixes $\mathrm{Obj}(pc)$ by induction.
  * A move above $p$ or off its path changes no object on the root path except by relocation.

  So $\mathrm{Obj}_{x^r}(\varnothing)=\mathrm{Obj}_x(\varnothing)$. **Correct.**
* **Step 2 (completeness).** Since $\iota_j$ is injective, each arrangement contains exactly one
  pair with first coordinate $\iota_j(c)$. Equality of arrangements therefore gives
  $\mathrm{Obj}_x(pc)=\mathrm{Obj}_y(p'\varrho(c))$ for every $c$. The base case is equality of colours. The
  children are independent because $R$ is the *full* wreath product (entanglement index 1).
  **Correct.**
* **Step 3 (equivariance).** I redid the substitution $c=s_jc'$, $\varrho'=s_j^{-1}\varrho s_j$. It
  uses normalisation and equivariance of $\iota_j$, and $s$ acts on deeper atoms through
  $s_{j+1},\dots$. **Correct.**
* **Step 4.** $x\cong_Gy$ iff $\mathrm{Obj}_y=\mathrm{Obj}_x^s$ for some $s\in S$. The kernel of $S$ on $U$ acts
  trivially on $\Omega$ by injectivity of the $\iota_j$, so working with $\Delta=S|_U$ loses nothing.
  **Correct.**
* **Do canonical forms compose up the tower?** This is not needed. Theorem L builds an exact
  $R$-orbit invariant bottom-up and canonises **once**, globally, under $S$. Composition is used
  only for the orbit-objects, and Steps 1–3 prove it by induction.

### 4.3 Coset assembly (W L395–396): gap, repaired

The sketch gives $s_0$ and one $r_0$ by witness tracking, plus lifts of the generators of
$\mathrm{Aut}_S(\mathrm{Obj}_x)$. **It omits generators of $\mathrm{Aut}_R(x)$**, without which the coset is
incomplete. Repair:

1. **$\mathrm{Aut}_R(x)$, bottom-up.** At a node $p$ of depth $j-1$,
   $\mathrm{Aut}_{R_p}(x|_p)=\bigl\langle\prod_c\mathrm{Aut}(x|_{pc}),\ \{(\varrho,(f_c)_c):\varrho\in\mathrm{Stab}_{R_j}(\text{arrangement})\}\bigr\rangle$.
   Here $f_c:x|_{pc}\to x|_{p\varrho(c)}$ is found by witness tracking. This uses
   $\varepsilon=1$, as in FPT Thm E. The cost is $\le\lvert R_j\rvert$ witness constructions per node,
   each $\mathrm{poly}(\prod_j\lvert R_j\rvert\lvert C_j\rvert)$; sift with Schreier–Sims.
2. **Lifting.** $\mathrm{Aut}((\mathrm{Obj}_x,\Delta\rho))\le\mathrm{Sym}(U)$. Map each generator to $S$ on $\Omega$ by
   constructive membership in the diagonal copy of $S$ on $U\sqcup\Omega$, then multiply by a
   witness $r_s$ with $x^{r_ss}=x$.
3. **Exactness.** For $g=rs\in G$: $x^g=x$ implies $\mathrm{Obj}_x^s=\mathrm{Obj}_x$; conversely every such $s$
   lifts. So $\mathrm{Aut}_G(x)=\langle\mathrm{Aut}_R(x),\{r_ss\}\rangle$ and
   $\mathrm{Iso}_G(x,y)=\mathrm{Aut}_G(x)\,r_0s_0$. A non-trivial $R\cap S=S\cap\prod_jR_j$ only makes the
   decomposition non-unique; it does no harm.

With this, **Theorem L (coset version) is PROVEN mod S-W `theo:obj`**, at the stated cost.

### 4.4 Gap: input format

Theorem L takes $(C_j,R_j,S,\iota_j)$ as given. Recovering it from generators of $G$ is not
addressed. For $G_{r,L}$ it looks routine: the block chain, $R=O_2(G)$ (as $\mathrm{GL}(r,2)$ is simple for
$r\ge3$), and a synchronised complement. W itself flags the general "global dispatcher" as missing
(L473–479). The statement "$G_{r,L}$ is FPT" should read "FPT when given with its tower data".

**Verdict on claim 4: sound.** The decision version is correct mod S-W. The coset version is
correct after §4.3.

---

## 5. Claim 5: the synchronised affine tower $G_{r,L}$ (W L398–445)

### 5.1 FPT

Take $\lvert R_j\rvert=\lvert C_j\rvert=2^r$, $U_j=X$, and $S=\mathrm{GL}(r,2)^L$ with orbits $\{0_j\}$ and $X_j\setminus0_j$, so
$k=2^r-1=d$. Theorem L then gives $2^{O(d)}\cdot\mathrm{poly}(4^{rL})=2^{O(d)}N^{O(1)}$. $\mathrm{GL}$ normalises the
translations, and $G_{r,L}\in\hat\Gamma_{2^r-1}$ for $r\ge3$, $r\ne4$ (factors $C_2$ and
$\mathrm{PSL}(r,2)$). **Correct** (given the tower data, §4.4).

### 5.2 HJ+(M′) lower bound (Prop. 4.2, W L405–417)

This is the step the task singled out. I checked that HJ enumerates and does nothing else.
* **The block systems of $G_{r,L}$ form a chain** (proved here; W asserts it).
  * Let $B\ni\omega=0^L$ be a block. Let $\omega'\in B$ be a point that first differs from $\omega$
    at coordinate $i$, with $i$ minimal over $B$.
  * $G_\omega$ contains $\mathrm{GL}_i$ and all local translations off $\omega$'s path. So $B$ contains
    $\{0^{i-1}\}\times(X\setminus0)\times X^{L-i}$, and $B\subseteq\{0^{i-1}\}\times X^{L-i+1}$.
  * $\lvert B\rvert$ is a power of 2 and exceeds half of $2^{r(L-i+1)}$. So $B$ is the prefix fibre.

  Hence `Expose` (HJ L1153, L3177–3183) must return $\mathrm{AGL}(r,2)$ on $x_1$-fibres.
* **Dispatcher.** Lean `Algorithm/Dispatch.lean` L29–41 tests `Small` first:
  $\lvert\rho(G)\rvert\le\exp(a\log^2d')$, in integer form $d'^{\,b\lfloor\log_2d'\rfloor}$ with $b=\lfloor a\log2\rfloor$ (L350–358).
  $\lvert\mathrm{AGL}(r,2)\rvert<2^{r^2+r}\le2^{br^2}$ for $b\ge2$, so it **enumerates**. There is no product
  refinement (that needs Maróti's Cameron product case, and `Small` is tested first) and no giant
  (the socle is affine). (M′) enumerates too, since the socle is not $(A_m^{(t)})^k$.
* **Recursion.** The kernel is $\prod_aR_{\ge2}|_a\rtimes\mathrm{GL}^{L-1}_{\rm diag}$; it acts on each fibre as
  $G_{r,L-1}$. For constant strings there is no early exit (redteam-w1-fpt §1.5). The orbit chain's
  first call is under the full $G_{r,L-1}$. In fact every fibre's conditional call is: the
  restriction to the first fibre has kernel $\prod_{a\ne a_0}R|_a$, so the preimage of the full
  first answer is the whole kernel. So W's bound $T(L)\ge\lvert\mathrm{AGL}\rvert\,T(L-1)$ holds, and can be
  strengthened by a factor $2^r$ per level.
* **Numbers.** $\lvert\mathrm{GL}(r,2)\rvert/2^{r^2}\ge0.2887$ (recomputed: $0.3281$ at $r=3$, $0.2888$ at $r=20$), so
  $\lvert\mathrm{AGL}\rvert^{L-L_0}\ge N^{r+1-1.80/r-o(1)}$. Here $L_0$ depends on $r,\alpha,\gamma,N_0$.
  * Cosmetic: W writes this as $N^{\log_2(d+1)+1-o(1)}$ (L408, L56). At fixed $d$ the $-1.8/r$ is a
    constant, not $o(1)$. Write $N^{\log_2(d+1)+1-2/\log_2(d+1)-o(1)}$.

**Sound.** The proof is independent of (H0): it uses only the pseudocode and the dispatcher.

### 5.3 Lemma 4.3 and entanglement (W L422–445)

* Steps 1–5 are correct:
  * $T_L\cong\mathbb F_2[Y]\otimes X$;
  * 2-group fixed points lie in $\mathbf1_Y\otimes X$;
  * $\mathrm{GL}(X)$ is irreducible, so every nonzero $G$-invariant subgroup contains $Z$;
  * the kernel on an orbit is normal;
  * $R\le\lvert O\rvert\log_2\lvert O\rvert$.
* **Cosmetic:** the final chain "$\lvert O\rvert\ge2^{r(L-1)}/L\ge N/(dL)$" is false. The second inequality
  would need $2^r-1\ge2^r$. The proof gives $\lvert O\rvert>R/\log_2R>2^{r(L-1)}/L=N/((d+1)L)$. Also, "S-W
  costs $2^{\Omega(N/(dL))}$" means S-W's *bound* is that large, not that the algorithm provably is.
* **Entanglement index.** The kernel at depth $j-1$ is $\bigl(\prod_cR_{>j}|_{pc}\bigr)\rtimes\mathrm{GL}^{L-j}_{\rm diag}$, and
  $\mathrm{GL}\cap\text{translations}=1$. So the index in the product of projections is
  $\lvert\mathrm{GL}(r,2)\rvert^{(L-j)(2^r-1)}$. **Correct.**
* **"Not sufficient"** (L442–445). This is correct as a statement about FPT §0's two features. FPT
  never claimed they were sufficient; it called them the profile of the candidate family.

**Verdict on claim 5: sound** (two cosmetic constants).

---

## 6. Claim 6: the decoupled HJ row (Prop. 4.4, W L447–469)

* **Reduction: correct.**
  * Since $K=\prod_BK^B$, the map $G\to Q\wr P$ has kernel exactly $K$. So $\bar G\cong P$ is the
    graph of a cocycle $P\to Q^{\mathfrak B}$.
  * The fibre over $(q_B;\sigma)$ is $\prod_B q_B$ (each $q_B$ is a $K_0$-coset). It contains an
    isomorphism iff every $q_B$ meets $\mathrm{Iso}_{G_0}(x_B,y_{B^\sigma})$, i.e. iff $q_B\in C(B,B^\sigma)$.
  * The fibre over a solution is a coset of $\prod_B(\mathrm{Aut}_{G_0}(x_B)\cap K_0)$.
  * Membership $q\in C(B,B')$ is membership in $\mathrm{Aut}_{G_0}(x_B)K_0\,g'$, which is polynomial.
  * The count $4d'^2$ is $(2d')^2$ ordered pairs over both strings; $d'^2$ suffice.
* **Children, checked against Lemma 7.1** (HJ L1643–1716):
  * Each child is an inherited orbit restriction: $G_0$ is the faithful image of $G_{B_0}$ on its
    orbit $B_0$. So $\rho$ drops by $2\lfloor\log_2d'\rfloor-1$, $\sigma,Q$ do not increase (HJ L1434–1439,
    L3046–3049), and the $h$-reset is paid by the domain drop.
  * The drop is $\ge\tfrac A3\Lambda\log d'-2B$ by eq. (main-enumeration-payment) (HJ L1497–1504).
  * One branch per pair gives $\mathcal M=d'^2$. The condition is
    $2\log d'+H_*\le\tfrac A3\Lambda\log d'$, which holds for $\Lambda=O(1)$ and $A$ large.
  * One new class keeps $J$ bounded. **The children are payable with $\Lambda=O(1)$: correct.**
* **Gap (low–medium): the terminal instance's toll.**
  * Lemma 7.1's induction allows a per-node toll of $N^aK_N$ (HJ L1636–1638, L1689–1692). The twisted
    instance costs $\lvert P\rvert\,\mathrm{poly}(s)$, which can be $d'^{\Theta(\log d)}\gg N^a$.
  * It cannot be paid from $\Phi_\Lambda$ at $\Lambda=O(1)$: that would need
    $e^{\Phi}\ge\lvert P\rvert$, i.e. $\Lambda\gtrsim\mu(P)$.
  * The correct accounting is $K_N\leftarrow K_N\cdot\max\lvert P\rvert$, a *global* factor. The total is
    then $\max_P\lvert P\rvert\cdot\exp(O(\Lambda\log N))$ instead of $\prod_i\lvert P_i\rvert$.
  * So "additive" (L468) is right, but the row is not "paid with $\Lambda=O(1)$" as a whole. W's
    summary row 5 (L57) is worded correctly ("the children are paid"); the task paraphrase
    overstates it.
* **The "$2^{O(k_0)}\mathrm{poly}(d')$" alternative** (L465–466, [SKETCH]) is unsupported when $Q\ne1$.
  * The constraints live in $Q$, which does not act on the small domain $U$, and the cocycle twists
    them. I see no equivariant encoding over $U$ with small orbits.
  * When $Q=1$ (full wreath towers) the instance *is* string isomorphism under $P$ on $\mathfrak B$,
    coloured by $G_0$-isomorphism type. Then $2^{O(k_0)}\mathrm{poly}(d')$ holds via Prop. 4.1.

**Verdict on claim 6: sound as a reduction; accounting gap in the terminal toll.**

---

## 7. Claim 7: consequences (W L58, L65–67, L540–556)

**Overstatement 1.** "Every family in §4.5–4.6 costs $2^{O(d)}N^{O(1)}$" (L543) is false as worded.
* *Row (c)* (L340) costs $\mathrm{poly}(d')\lvert Q\rvert^{O(1)}$. For $Q=S_m$ in natural action, $\lvert Q\rvert=m!=2^{\Theta(d\log d)}$,
  and $S_m\wr S_k$ in product action is not covered at $2^{O(d)}$ by anything in W:
  * the literal encoding has orbits $mk\gg\log d'$;
  * FPT Prop. 3.3 pays $\lvert P\rvert=m!$;
  * a top group $K$ of order up to $d^{k-1}$ must still be enumerated.
* *Theorem L* costs $2^{O(k)}\mathrm{poly}(\prod_j\lvert R_j\rvert\lvert C_j\rvert)$. That is not $2^{O(d)}\mathrm{poly}(N)$ when
  $\lvert R_j\rvert$ is superpolynomial in $\lvert C_j\rvert$ (e.g. $R_j=\mathrm{Sym}(C_j)$, or heart local groups with
  $\lvert R_j\rvert=\lvert C_j\rvert^{\log m}$), or when $k\gg d$.

**Overstatement 2.** "All decoupled … families are polynomial" (L58) is not proved.
* For decoupled towers Theorem E / Prop. 4.4 pay $\max\lvert P\rvert$. That is $2^{\Theta(d\log d)}$ for heart
  components with $Q\ne1$, and $N^{\Omega(\log d)}$ for a large-degree primitive component.
* Getting $2^{O(d)}$ would need a $2^{O(d)}\mathrm{poly}(d')$ algorithm for *every* primitive
  $P\in\hat\Gamma_d$ in the twisted setting. Prop. 2.2 + BCQ give at best $\mathrm{poly}(d')\,f(d)$ with
  $f(d)=2^{O(d\log^2d)}$ (component orders).
* Similarly, the verdict's "full wreath towers are all $f(d)\cdot\mathrm{poly}(N)$" (L66) needs components
  of order $\le f(d)$. Theorem E's $\pi_0$ is the largest component order, which for a
  large-degree primitive component can be $N^{\Omega(\log d)}$.
* "AGL(r,2)-towers" (L56) should read "level-synchronised AGL(r,2)-towers". Unsynchronised
  entangled ones (Example X) are open by W's own §4.8.

**What is proved at $d=O(\log n)$** (string isomorphism, all $2^{O(d)}N^{O(1)}$, hence polynomial):
* axis-preserving products (row (b)) whose components have $O(d)$-orbit encodings:
  $\mathrm{AGL}(r,2)^L$, $\mathrm{PGL}(r,2)^L$, $S_m^L$, $(E\rtimes S_m)^L$ with literals, and $V^L\rtimes\mathrm{GL}_{\rm diag}$;
* Theorem L towers with $\lvert R_j\rvert\le\lvert C_j\rvert^{O(1)}$ and $k=O(d)$: $G_{r,L}$ and synchronised heart
  towers (L403);
* row (c) with $\lvert Q\rvert\le2^{O(d)}$, e.g. $\mathrm{AGL}(r,2)\wr S_k$, mod BCQ;
* full wreath towers ($Q=1$) whose components have $O(d)$-orbit encodings, via Prop. 4.4 with the
  §6 observation.

**Graphs.**
* §5.2 (L546–547) and §5.3 explicitly disclaim any GI transfer. Prop. 4.2 and Theorem L are
  string-isomorphism statements throughout, and the verdict (L70–71) says nothing removes $\log d$
  for graphs.
* "R\*\* = R\* for GI" (L233) is a correct worst-case statement over $\hat\Gamma_{d-1}$; whether
  degree-$d$ towers actually contain $\mathrm{PSL}(\log d,2)$ sections is not claimed.
* **No graph overclaim found.**

**Verdict on claim 7: overstatement, fixable** by replacing L58 and L543 with the list above.

---

## 8. Overall verdict

**No break.** W's mathematics is correct where it is labelled PROVEN. The SKETCHes are sound in
substance, and the defects are fixable:
* the parameter definition in R\*\*;
* the missing $\mathrm{Aut}_R(x)$ step in Theorem L's coset version;
* the terminal toll of Prop. 4.4;
* the overstated consequences paragraph;
* three cosmetic constants.

**Strongest statements I would sign.**

1. **Theorem L (mod S-W `theo:obj`).** Suppose $G=RS\le\mathrm{Sym}(C_1\times\cdots\times C_L)$ is given
   with its tower data: $R=R_1\wr\cdots\wr R_L$, and $S\le\prod_jN(R_j)$ acting coordinatewise through
   injective equivariant $\iota_j:C_j\to\mathrm{HF}(U_j)$. Then the full isomorphism coset
   $\mathrm{Iso}_G(x,y)$ is computable in $2^{O(k)}\cdot\mathrm{poly}(\sum_j\lvert U_j\rvert+N\max_j\lvert R_j\rvert)$, where $k$ is the
   largest $S$-orbit on $U$.
2. **$G_{r,L}$ (mod S-W; given its tower data):** string isomorphism in $2^{O(d)}N^{O(1)}$, $d=2^r-1$.
   Every faithful action has an orbit $>N/((d+1)L)$. The entanglement index at depth $j-1$ is
   $\lvert\mathrm{GL}(r,2)\rvert^{(L-j)(2^r-1)}$.
3. **HJ lower bound (from the pseudocode and the Lean dispatcher; independent of (H0)).** On
   $G_{r,L}$ and on $\mathrm{AGL}(r,2)^L$ in product action, with constant strings, HJ verbatim and
   HJ+(M′) create $\ge\lvert\mathrm{AGL}(r,2)\rvert^{L-L_0}\ge N^{r+1-1.8/r-o(1)}$ coset branches.
4. **Prop. 2.1** (mod LS14 via GNS Thm 3.7, Liebeck 1984, BCP/Maróti and Wagner's minimal
   degrees), with $w=\mathrm{aw}(P)$ and $\lambda$ the largest classical section dimension: for primitive
   $P$ not of structural option 2, $\mu(P)\le C(1+\lambda+\min\{\log w,\log\log d'\})$.
5. **Theorem R\*\*** (conditional on (H0) and item 4), with the same section-closed parameters:
   $\exp(O(\log(N+2)(\log w+\lambda+1)))$.
6. **Prop. 4.4** as a reduction. Under (H0), its $d'^2$ children are payable with $\Lambda=O(1)$,
   and the terminal instance contributes a global factor $\max\lvert P\rvert$.
7. **At $d=O(\log n)$**, polynomial-time string isomorphism holds for exactly the families listed
   in §7, and for no graph class.

I would **not** sign Prop. 2.2 beyond SKETCH, the "$2^{O(k_0)}$" twisted-instance bound for
$Q\ne1$, or "all decoupled families are polynomial".

**Novelty assessment.**
* **Theorem L / $G_{r,L}$ / Lemma 4.3.** Not found in S-W, Wiebking 1904.10454, FPT's sources or
  the campaign's literature. It is a short combination of S-W with an orbit-object trick, of a
  kind experts would find quickly. Its value is the clean counterexample to "entangled + no small
  faithful domain ⇒ hard": $G_{r,L}$ has $\varepsilon$ unbounded and Lemma 4.3, yet it is FPT,
  because its entanglement lives entirely in a quotient with a small-orbit action. **Modest but
  genuine.**
* **Prop. 4.2.** The same template as FPT's $P_d^m$ remark and moonshot Prop. 2. The new example
  has exponent $\log_2(d+1)+1$ at $d'\approx d$. **Low.**
* **Prop. 2.1.** A reorganisation of GNS §3. LS14 Prop. 2, as quoted at G653, already separates
  the classical term $9d_i$ from the alternating term $3\log m_i$. The $\min(\cdot,\log\log d')$
  refinement is elementary. **Low**, but useful bookkeeping. Prop. 2.2 is consistent with known
  structure theory (Liebeck 1985, Aschbacher classes).
* **R\*\*.** A routine refinement of R\*, conditional on HJ. HJ v1 is four days old, so any
  HJ-specific statement is trivially unpublished.
* **Prop. 4.4.** FPT §4.1 written as an HJ row. **Low.**

---

## 9. What I could not check

* (H0), which includes Lemma 7.1's framework as used in claims 2 and 6.
* LS02/LS14, Liebeck 1984/1985, GSS98, BLS87 and Feit–Tits: only as quoted by GNS or from
  memory.
* S-W's internal lemmas (`canInt`, `canSet`, `canSetHyper`): only the statement of `theo:obj`, the
  framework definitions and the runtime proof were read.
* BCQ12 / Codenotti Thm 4.2.1 (row (c)): not read; W's caveat stands.
* §4.8–4.9 (relative S-W failure, Example X, heart-type σ-machinery): labelled SKETCH/SPECULATION
  in W and not audited.
* No Lean was built or run.
