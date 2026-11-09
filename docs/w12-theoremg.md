# w12-theoremg: closing Theorem G (degree-d GI in n^{O(log³ d)} for all d)

Branch `w12-theoremg`, 2026-11-08. Wave 12. **Not refereed and not red-teamed.** No Lean was run. The
only computation is `docs/w12-theoremg-check.py` (standard library, about 2 s at `nice 19`).

**Labels.**
* **[PROVEN]**: a complete argument is written here. It relies only on the published and repository
  results in the ledger (§11).
* **[SKETCH]**, **[CONDITIONAL: …]**, **[SPECULATION]**: as in earlier memos.

Every [PROVEN] below means "complete argument, one author's pass". The earlier waves' convention is
that a result is not signed until a separate red-team has attacked it. Theorem G has not had that.

**Notation.** As in `docs/w10-blackbox.md` ("M"). $L:=\log_2(d+2)$ with $d\ge2$; $\ell:=\log_2n$;
$\ell=L^x$. "G L…" is a line of GNS `bounded-degree-polylog-d.tex` (v3), "HBD L…" a line of `BDHv8.tex`.

---

## 0. Summary

| # | open item (from the w11 red-team) | status | where |
|---|---|---|---|
| 1 | Gap 1: pairwise heavy round inside GNS's aggregation; composition with case (iv) | **closed** [PROVEN]. The two sides meet only through a candidate family of cosets of one group $R$, exactly as in Theorem X. Case (iv) never composes with a heavy round: the App. A cases are mutually exclusive and invariant. | §3 |
| 2 | Maintained tower; GNS's choice of block system | **closed** [PROVEN]. Rule: *the next block system is taken above the top of the maintained tower.* It is a legal run of GNS. Every use of the block system was checked (§2.4). The §7.3 fix is the special case "top = $\mathcal C'[\Omega']$". | §2 |
| 3 | O2's parity case | **closed** [PROVEN], and simpler than the red-team's version: one double transposition suffices and it need not fix $S$. Also handled: individualized points inside blocks, which neither w10 nor w11 treated. | §5 |
| 4 | "No black box at all" | **corrected and verified** [PROVEN]. Case (iv) still calls Babai–Helfgott on graphs with $\le k$ vertices. Each call costs $2^{O(\log^3k)}\le n^{O(L^2)}$, because $k\le n$. It is additive per node and is absorbed. So the true wording is "no $t$-ary black box". | §6, §7 |

**Final bound.** [PROVEN, modulo §11; not red-teamed] String isomorphism for $\hat\Gamma_d$ groups on $n$
points, and isomorphism of graphs of maximum degree $d\ge2$, is decidable in time
$$n^{O(\log^3d)}\qquad\text{for all }d.$$
With the Babai–Helfgott switch, the exponent of $L$ is $\min(3,2x)$, so $c=3$ everywhere and strictly
better than 3 only where B–H alone already wins ($x<3/2$). Details by regime are in §8.

**If §5–§7 are later refuted,** Theorem X (red-teamed) still gives $n^{O(\log^3d)}2^{O(\log^5d)}$, i.e.
$c=10/3$ for all $d$ and $c=3$ for $d\le2^{\sqrt{\log n}}$.

**Two corrections to the record** (§9):
* In Split-or-Johnson the number of individualized points is **not** $O(\log m)$. Only the number of
  choice sequences is $m^{O(\log m)}$. The point count is $O(\log^2m)$ at most. This changes no bound.
* Lemma O2 of w10 was stated for GNS case (ii) as well. That case is light and does not need O2.

---

## 1. Setting and inputs

**Fixed parameters.** $d\ge2$; $t:=\max\{9,\,3+\lceil\log_2d\rceil\}$; $\tau_0:=\max\{40t,\,k_0\}$, where
$k_0$ is the absolute constant of (H3) below. GNS use $10t$ in place of $\tau_0$. Raising the threshold
is free: below it the Luks step costs $k!\le2^{O(L\log L)}$.

**Instances.** An instance is $(H,\mathbb T,x,y)$ with $H\le\mathrm{Sym}(\Omega)$, strings $x,y$ on $\Omega$, and a
*tower* $\mathbb T$: a chain $\{\Omega\}=\mathfrak T_0\succ\mathfrak T_1\succ\dots\succ\mathfrak T_m=$ discrete of
$H$-invariant partitions that is almost $d$-ary (GNS Def. 4.1). The output is $\mathrm{Iso}_H(x,y)$. Cosets
$H\tau$ are reduced to this by replacing $y$ with $y^{\tau^{-1}}$.

**Inputs from the literature** (precise references in §11).
* (G1) Change of action: GNS Thms 4.3, 4.6 with the count of w8 Prop. 2 / Grohe–Neuen survey Thm 4.16.
  A transitive $\hat\Gamma_d$ instance on $n$ points becomes one on $N\le n^{O(L)}$ points with an almost
  $d$-ary tower.
* (G2) Unaffected stabilizers, local certificates, comparisons, aggregation: GNS Thm 5.8, Lemmas 6.2, 6.3,
  6.6 and App. A, 6.7, 6.9.
* (G3) GNS Lemma 7.1 (Babai's Thm 3.2.1; uses CFSG).
* (H1) HBD's WL functors $F_1,F_2,F_3$ with a canonical colour order.
* (H2) HBD's Design Lemma (Prop. `design`).
* (H3) HBD's Split-or-Johnson (Thm `coupjohn`), read as follows. There is a deterministic procedure
  $\mathrm{Proc}$ that takes a uniprimitive classical coherent configuration $\mathfrak X$ on a set $\Gamma$ of
  size $m$ together with a *choice stream* $\zeta$. Every non-canonical step of HBD's proof (L1423–1700) reads
  one point of a specified subset of $\Gamma$ from $\zeta$. In particular:
  * *Functoriality.* $\mathrm{Proc}(\mathfrak X^\pi,\zeta^\pi)=\mathrm{Proc}(\mathfrak X,\zeta)^\pi$ for bijections $\pi$.
  * *Branching.* Along every path of the stream tree, the product of the numbers of options at the choice points is at most
    $m^{c_H\log m}$. This is HBD's index bound $[\mathrm{Sym}(\Gamma):H]=m^{O(\log m)}$, a worst-case bound over executions, read off the proof,
    which multiplies $\lvert V_2^{(j)}\rvert^{d_j}$ over $O(\log m)$ steps. The tree therefore has at most $m^{c_H\log m}$ leaves (leaves below a node are at most its
    number of children times the maximum below a child; the tree need not be balanced).
  * *Individualized points.* Along any path, at most $c_H\log^2m$ points are read from a set with at least 2 options, since each
    contributes a factor at least 2 to that product. Points read from a singleton set are canonical, so they are fixed anyway.
  * *Output.* Either a coloured $\tfrac34$-partition of $\Gamma$ (each colour equipartitioned into blocks of size
    in $[2,\tfrac34m]$, except possibly singleton colour classes), or a Johnson scheme $\mathcal J(r,s')$ on
    $\Gamma_0\subseteq\Gamma$, $\lvert\Gamma_0\rvert\ge\tfrac34m$, $s'\ge2$, $r\ge2s'$, given with an explicit identification
    with the $s'$-subsets of an $r$-set $\Lambda$.
  * $k_0$ is chosen so that $c_H\log^2k\le k/40$ for $k\ge k_0$.
* (BH) Babai–Helfgott: graph isomorphism on $k$ vertices in $\exp(O(\log^3k))$.
* (A) Lemma A (w8; variant of Pago's Lemma `G_groupInduction`, whose primitive case Pago credits to Wiebking):
  if $L_0\le S_k$ has a composition factor $A_m$ with $m>3k/4$, $m\ge16$, then $\mathrm{Alt}(\Delta)\le L_0$ for some
  $\Delta\subseteq[k]$ with $\lvert\Delta\rvert\ge m$.

---

## 2. Item 2: the maintained tower [PROVEN]

### 2.1 The potential

For an integer $r\ge1$ put $f(1)=0$ and $f(r)=2\lfloor\log_2r\rfloor-1$ for $r\ge2$. If $H$ is transitive on
$\Omega$, each level has a well-defined branching $r_i:=\lvert\mathfrak T_i[B]\rvert$ ($B\in\mathfrak T_{i-1}$), and
$\rho(\mathbb T):=\sum_if(r_i)$, repeated levels being dropped. For intransitive $H$, $\rho$ is the maximum over
orbits of the $\rho$ of the restricted tower.

**Lemma 2.1.**
(a) $\rho(\mathbb T)\le2\log_2\lvert\Omega\rvert$.
(b) *Monotone under restriction.* If $H^\circ\le H$ and $\Omega'$ is an $H^\circ$-orbit, then
$\rho(\mathbb T[\Omega'])\le\rho(\mathbb T)$.
(c) *Strict insertion.* If $H$ is transitive and $\mathfrak E$ is $H$-invariant with
$\mathfrak T_{i-1}\succ\mathfrak E\succ\mathfrak T_i$ strictly, inserting $\mathfrak E$ lowers $\rho$ by at least 1.
Non-strict insertion leaves $\rho$ unchanged.

*Proof.* (a) $\sum_i\log_2r_i=\log_2\lvert\Omega\rvert$ and $f(r)\le2\log_2r$. (b) Each $r_i$ does not increase and $f$ is
non-decreasing. (c) $r_i=ab$ with integers $a,b\ge2$, by transitivity, and
$f(a)+f(b)=2(\lfloor\log_2a\rfloor+\lfloor\log_2b\rfloor)-2\le2\lfloor\log_2ab\rfloor-2=f(ab)-1$. ∎

Inserting a level never raises $\rho$, and inserted levels are coarser than $\mathfrak T_1$, so the tower stays
almost $d$-ary whenever the inserted partitions have at most $d$ classes (each inserted level branches at
most $d$ ways).

### 2.2 Algorithm G

On an instance $(H,\mathbb T,x,y)$ on $n$ points:

* **G1 (intransitive).** Chain rule over the orbits, with restricted towers.
* **G2 (semi-regular top).** If $H$ is transitive and $H^{\mathfrak T_1}$ is semi-regular, use Luks reduction to
  $H_{(\mathfrak T_1)}$: $b=\lvert\mathfrak T_1\rvert$ cosets, each with $b$ orbit-pieces of size $n/b$.
* **G3 (block system: the rule).** Otherwise $\lvert\mathfrak T_1\rvert\le d$. **Choose $\mathfrak D$, a maximal proper
  $H$-invariant partition with $\mathfrak D\succeq\mathfrak T_1$**, so that $P:=H^{\mathfrak D}$ is primitive. If
  $\lvert P\rvert\le d^{1+\log d}$, use Luks reduction to $H_{(\mathfrak D)}$.
* **G4 (giant).** Apply GNS Lemma 7.1 to $P$ to get $N\trianglelefteq P$, a partition $\mathcal C$ of $\mathfrak D$, and
  $\psi:N\to S_k$. Put $G':=\{g\in H:g^{\mathfrak D}\in N\}$ (index $\le\lvert\mathfrak D\rvert\le d$),
  $\varphi:=\psi\circ(\text{action on }\mathfrak D)$ and $\mathcal C'$ := the lift of $\mathcal C$ to $\Omega$. So
  $\ker\varphi=G'_{(\mathcal C')}$. Split into cosets of $G'$. If $G'$ is intransitive, its orbits are blocks of $H$
  of size $\le n/2$: go to G1. If $k\le\tau_0$, use Luks reduction to $\ker\varphi$.
* **G5 (aggregation).** Compute local certificates and comparisons for all $t$-sets, and distinguish cases
  (i)–(v) of GNS App. A. The case is an isomorphism invariant of the string, so if the two strings land in
  different cases, output $\emptyset$.
* **G6 (light rounds).** Cases (i)–(iv): GNS Lemmas 6.7, 6.9 give one group $R\le G'$ and at most $k^6$ cosets.
  Case (iv) makes one B–H call per coset.
* **G7 (heavy round).** Case (v): §3.
* **G8 (recursion).** For each child coset $R\tau$, process the orbits of $R$ in order, a largest one first, so
  that the large orbit is processed under $R$ itself. An orbit $O$ receives the tower
  $$\mathbb T_O:=\big(\,[\mathfrak E\text{ if the round was a tower round and }O=\Omega'],\ \mathcal C'[O],\ \mathfrak D[O],\ \mathbb T[O]\,\big),$$
  with repeats removed.

**Lemma 2.2 (the tower is maintained).** $\mathbb T_O$ is an almost $d$-ary tower of $R^O$-invariant partitions, and
$\rho(\mathbb T_O)\le\rho(\mathbb T)$. If $\mathfrak E$ is present, $\rho(\mathbb T_O)\le\rho(\mathbb T)-1$.

*Proof.* Invariance: $\mathfrak D$ and $\mathbb T$ are $H$-invariant, $\mathcal C'$ is $G'$-invariant, $\mathfrak E$ is $R^{\Omega'}$-invariant
(Lemma 5.2). All are chains because $\mathcal C'\succeq\mathfrak D\succeq\mathfrak T_1$ and $\mathfrak E\succeq\mathcal C'[\Omega']$. The inserted levels
have at most $\lvert\mathfrak T_1\rvert\le d$ classes, and lower levels are inherited (GNS Obs. 4.2). Lemma 2.1 gives the rest:
inserting $\mathfrak D,\mathcal C'$ does not raise $\rho$, restriction does not, and inserting $\mathfrak E$ between $\{\Omega'\}$ and
$\mathcal C'[\Omega']$ lowers it (strict by Lemma 5.2). ∎

### 2.3 Why a maximum-over-towers potential is avoided

$\rho$ is computed on the one tower the algorithm holds. Nothing is minimized, so the red-team's objection (an
optimal tower may cross $\mathfrak E$) does not arise. Levels stay comparable because rule G3 places each new level above
the current top.

### 2.4 Which runs are legal: every use of the block system [PROVEN]

| place in GNS | what it needs | status with rule G3 |
|---|---|---|
| Lemma 7.2 proof, "WLOG $P$ primitive" (G L2087) | some block system above $\mathfrak B_1$ | G3 picks one above $\mathfrak T_1\succeq$ (restriction of) $\mathfrak B_1$. A legal choice. |
| Lemma 7.1 hypotheses | $P$ primitive, degree $\le d$, large order | $\lvert\mathfrak D\rvert\le\lvert\mathfrak T_1\rvert\le d$; large order is checked in G3 against $d^{1+\log d}\ge b^{1+\log b}$. If $b$ is below Lemma 7.1's absolute constant then $\lvert P\rvert$ is bounded and Luks applies. |
| $\ker\varphi=G'_{(\mathcal C')}$ (G L2099) | none | unchanged |
| Semi-regular test (Alg. 4) | top level of the sequence | run on the top of $\mathbb T$. Inserted tops have $\le d$ classes, so Luks is affordable either way. |
| Thm 5.8, Lemmas 6.2, 6.3 | *some* almost $d$-ary invariant sequence | $\mathbb T$ qualifies (Lemma 2.2, Obs. 4.2). The theorems quantify over sequences, so a refinement is allowed. |
| Windows, comparisons, kernel orbits | restriction of the sequence to invariant sets | Obs. 4.2 and Lemma 2.1(b). |
| Height / $k'$ bound (G L2118–2134) | that $H'_{(\mathcal C')}\le\ker\varphi'$ | **Now true by construction**: $\mathfrak D'\succeq$ top of $\mathbb T_{\Omega'}\succeq\mathcal C'[\Omega']$. This is the only place where the choice matters, and it is the §7.3 fix. |
| Thm 7.3 (induction over the recursion) | every recursive group is the projection of a subgroup, with a tower | Lemma 2.2. |
| Thm 8.1 and change of action | top level only | unaffected |

So rule G3 selects, among the runs GNS's text allows, one in which all the invariances hold. Nothing else in GNS
consults the block system.

---

## 3. Item 1: the pairwise heavy round [PROVEN]

**Setting.** A node $(G',\varphi,k>\tau_0,x_1,x_2)$ in case (v) for both strings. If $\lvert D_1\rvert\ne\lvert D_2\rvert$, output
$\emptyset$. Put $m:=\lvert D_i\rvert>3k/4$. The structures $\mathfrak A_i$ on $D_i$ come with jointly named colours (GNS App. A). Three
facts are taken from GNS and used below.
* Every $g\in\mathrm{Iso}_{G'}(x_1,x_2)$ satisfies $\varphi(g)|_{D_1}\in\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$ (G L2382; canonicity of the comparison
  classes).
* Every injective $t$-tuple of $D_i$ has exactly one colour.
* The symmetry defect of $\mathfrak A_i$ is at least $\lvert D_i\rvert-t+1$ (G L2383), so twin classes have size at most $t-1$.

**The round.**
1. *WL.* Apply $F_3F_2F_1$ to both structures with one naming scheme, to get $t$-ary coherent configurations
   $\mathfrak X_1,\mathfrak X_2$ with $\mathrm{Iso}(\mathfrak X_1,\mathfrak X_2)=\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)$. Time $m^{O(t)}$.
2. *Design Lemma* with $\alpha=3/4$, on $\mathfrak X_1$: search $D_1^{<t}$ for the lexicographically first tuple $\vec x$ satisfying
   an outcome. Hypotheses: $2\le t\le m/2$ and twin classes $<\tfrac34m$. Both hold.
3. *Structure.* Let $\mathrm{Proc}^+(\mathfrak X,\vec x,\zeta)$ be the deterministic procedure:
   * outcome (1): output the colouring $\mathfrak X_{\vec x}^{(1)}$;
   * outcome (2), $\mathfrak X''$ imprimitive: output the colouring and the components of the first disconnected
     colour on the dominant class $C$;
   * outcome (2), $\mathfrak X''$ uniprimitive: output the colouring and $\mathrm{Proc}(\mathfrak X'',\zeta)$.

   Its output $Y$ is one of three types: a *colouring*, a *coloured partition* (with $C$'s partition), or a *Johnson
   structure*. In every case $Y$ contains the set $I$ of points of $\vec x$ and $\zeta$, to be fixed pointwise, together with
   the colour of $[k]\setminus D$. Run this on side 1 with the first valid $\zeta$. Let $L_Y$ be
   $\mathrm{Aut}(Y)\cap\varphi(G')$ acting on $[k]$, with $I$ fixed pointwise and $D_1$ preserved, and let
   $R:=\varphi^{-1}(L_Y)$. Both have explicit generators. For the three types, $\mathrm{Aut}(Y)$ is an explicit product of
   symmetric groups, wreath products, and $\mathrm{Sym}(\Lambda)$ acting on $s'$-subsets.
4. *Other side.* For every $\ell$-tuple $\vec y\in D_2^{\ell}$ with $\ell=\lvert\vec x\rvert$ and every leaf $\zeta'$ of the stream tree of
   $(\mathfrak X_2,\vec y)$, compute $Y_2:=\mathrm{Proc}^+(\mathfrak X_2,\vec y,\zeta')$. Discard candidates of a different type or different
   numerical parameters. For each remaining candidate compute the aligning coset $\{g\in G':\varphi(g)$ carries $(D_1,Y_1,I_1)$ to $(D_2,Y_2,I_2)\}$.
   This is $\emptyset$ or $R\tau_j$; on Johnson structures alignment uses the explicit identification with $\Lambda$.
5. *Children.* The cosets $R\tau_j$.

**Lemma 3.1.** [PROVEN] (a) $\mathrm{Iso}_{G'}(x_1,x_2)=\bigcup_j\mathrm{Iso}_{R\tau_j}(x_1,x_2)$.
(b) The number of children is at most $C_h:=m^{t+c_H\log m}\le2^{O(L^2)}$, and steps 1–4 take time $2^{O(L^2)}$.
(c) Given the children's outputs, $\mathrm{Iso}_{G'}(x_1,x_2)$ is computed in polynomial time.

*Proof.* (a) "$\supseteq$" is immediate. For "$\subseteq$", let $g\in\mathrm{Iso}_{G'}(x_1,x_2)$ and $\pi:=\varphi(g)|_{D_1}$. Then
$\pi\in\mathrm{Iso}(\mathfrak A_1,\mathfrak A_2)=\mathrm{Iso}(\mathfrak X_1,\mathfrak X_2)$. The procedure $\mathrm{Proc}^+$ only uses functorial operations and the
stream: the WL colour names, the configuration operations, the first-disconnected-colour rule (colour names are joint, so
"first" means the same on both sides), and $\mathrm{Proc}$ by (H3). Hence
$\mathrm{Proc}^+(\mathfrak X_2,\vec x^\pi,\zeta^\pi)=Y_1^\pi$, and $(\vec x^\pi,\zeta^\pi)$ is a candidate on side 2 (the Design outcome and the
choice sets transport under $\pi$). So $g$ lies in the corresponding coset.

(b) Tuples: at most $m^{t}$. Streams: at most $m^{c_H\log m}$. Their product is $2^{O(t\log m+\log^2m)}=2^{O(L^2)}$.

(c) All nonempty $\mathrm{Iso}_{R\tau_j}(x_1,x_2)$ are cosets of $K:=\mathrm{Aut}_R(x_1)$. Say the results are $K\rho_j$. Their union is
$\mathrm{Iso}_{G'}(x_1,x_2)$, a coset of $\mathrm{Aut}_{G'}(x_1)$, and $\mathrm{Aut}_{G'}(x_1)=\langle K,\rho_j\rho_0^{-1}\rangle$. ∎

The point of the lemma is that **the two sides are compared only by aligning explicit objects**. No "isomorphism of a
$t$-ary structure" is computed; this is exactly how HBD's Case 3 (L1940–1956) and BB (M §3.2) work, with $G'$ in place of
$\mathrm{Sym}(D)$. The lift through $\varphi$ is an explicit homomorphism.

**Composition with case (iv).** There is none. App. A's cases are mutually exclusive and are invariants of the string (G5).
The family of $k^6$ structures exists only in case (iv), and heavy rounds occur only in case (v). So Gap 1's "composition"
worry is empty.

---

## 4. Classes as subsets of $[k]$ [PROVEN]

**Lemma 4.1.** Let $G'$ be as in G4 with $k>\tau_0$. There are an integer $1\le s<t$ and a $\varphi(G')$-equivariant surjection
$\sigma:\mathcal C'\to\binom{[k]}{s}$ with fibres of equal size such that for each class $c$ the setwise stabilizer of $c$ in
$\varphi(G')$ contains $\mathrm{Alt}([k]\setminus\sigma(c))$. Moreover $k\le\lvert\mathcal C'\rvert\le n$ and the classes have equal size.

*Proof.*
* $\varphi(G')$ acts transitively on $\mathcal C'$: $N\ne1$ is normal in the primitive group $P$, so $N$ is transitive on $\mathfrak D$. It
  acts faithfully, since $\ker\varphi=G'_{(\mathcal C')}$. The classes have equal size by transitivity.
* Let $S_c$ be the stabilizer of $c$ in $\varphi(G')$. Then $\lvert\varphi(G'):S_c\rvert\le\lvert\mathcal C'\rvert\le d$. With $r:=\lceil\log_2d\rceil+1<k/2$
  we have $d<2^r\le\binom kr$. By GNS Thm 6.4 (Dixon–Mortimer 5.2A,B) there is $\Delta$ with $\lvert\Delta\rvert>k-r$ and
  $\mathrm{Alt}(\Delta)\le S_c$.
* Maximal such $\Delta$ is unique. Two such sets each have more than $k/2$ points, so they meet, and
  $\langle\mathrm{Alt}(\Delta_1),\mathrm{Alt}(\Delta_2)\rangle=\mathrm{Alt}(\Delta_1\cup\Delta_2)$, since a transitive group generated by 3-cycles is
  alternating. Call the maximum $\Delta(c)$, and put $\sigma(c):=[k]\setminus\Delta(c)$, of size $s<r<t$.
* $\sigma$ is equivariant: $S_{c^h}=h^{-1}S_ch$, so $\Delta(c^h)=\Delta(c)^h$. Transitivity makes $s$ constant, and transitivity of $A_k$ on
  $s$-subsets makes $\sigma$ onto with equal fibres.
* $s\ge1$: if $s=0$ then $A_k\le S_c$ for all $c$, so $A_k$ acts trivially on $\mathcal C'$, contradicting faithfulness.
* $\binom ks\ge k$ gives $\lvert\mathcal C'\rvert\ge k$. ∎

**Notation for §5.** Write $\mu$ for the uniform probability on $\binom{[k]}s$. Recall $s<t\le k/40$. Let $L:=L_Y$ act on $s$-subsets.
For an $R$-orbit $\Omega'\subseteq\Omega$, the set $P:=\{\sigma(c):c\text{ meets }\Omega'\}$ is an $L$-orbit (the image of an $R$-orbit under the
equivariant map), and $\lvert\Omega'\rvert/n\le\mu(P)$, by equal class size and equal fibres. Call the round a **shrink** if every
$R$-orbit has at most $\tfrac56n$ points. If it is not a shrink, there is a unique orbit $\Omega'$ with $\mu(P)>\tfrac56$.

A uniform $s$-subset is realized as a uniform injective tuple $(u_1,\dots,u_s)$ throughout.

---

## 5. Item 3: the trichotomy [PROVEN]

**Lemma 5.1 (colourings shrink).** If $L$ preserves a colouring $\gamma$ of $[k]$ with all classes of size at most $\tfrac34k$, then the
round is a shrink.

*Proof.* The colour-count vector of $S$ is $L$-invariant. Fixing $u_2,\dots,u_s$, a given vector forces the colour of $u_1$. So its
probability is at most $(\tfrac34k)/(k-s+1)<\tfrac56$, as $s<k/10$. ∎

**Lemma 5.2 (partitions: shrink or insert).** Suppose $Y$ is a coloured partition and no colour class of size greater than $\tfrac34k$ exists
*or* the unique such class $E$ carries an $L$-invariant partition $\Pi_E$ into blocks of equal size $b$ with $2\le b\le\tfrac34k$, where $L$ contains
all elements of $A_k$ that fix $I$ pointwise and fix each block setwise. Suppose $\lvert I\rvert\le k/20$. Then either the round is a shrink, or the
large orbit $\Omega'$ carries an $R^{\Omega'}$-invariant partition $\mathfrak E$ with $\mathcal C'[\Omega']\prec\mathfrak E\prec\{\Omega'\}$, both strict.

*Proof.* If all classes have size at most $\tfrac34k$, Lemma 5.1 gives a shrink. Otherwise let $E$ be as stated. Put $E^\circ:=E\setminus I$,
$\Pi^\circ:=\{B\setminus I:B\in\Pi_E\}\setminus\{\emptyset\}$ and $Q:=[k]\setminus E^\circ$, so $\lvert Q\rvert<k/4+\lvert I\rvert$. Define
$$\Psi(S):=\big(\lvert S\cap B^\circ\rvert\big)_{B^\circ\in\Pi^\circ}.$$
Since $L$ permutes $\Pi^\circ$, the fibres of $\Psi$ form an $L$-invariant partition of $\binom{[k]}s$. Let $P$ be the $L$-orbit of measure greater than
$\tfrac56$ and let $\mathfrak E$ be the partition of $\Omega'$ into fibres of $\Psi\circ\sigma$ (well defined on classes). It is $R^{\Omega'}$-invariant
and $\mathfrak E\succeq\mathcal C'[\Omega']$.

*(a) $\mathfrak E\ne\{\Omega'\}$.* Fix a value of $\Psi$ and condition on $u_2,\dots,u_s$. Then $u_1$ is forced to lie in one specific block of $\Pi^\circ$, or in
$Q$. That event has probability at most $\max(b,\lvert Q\rvert)/(k-s+1)\le(\tfrac34k)/(0.9k)=\tfrac56$. So each fibre has measure at most $\tfrac56$, and $P$ meets
at least two fibres. Since $P$ is the image of $\Omega'$, $\mathfrak E$ has at least two blocks.

*(b) $\mathfrak E\ne\mathcal C'[\Omega']$.* It suffices to show some $\Psi$-fibre contains two elements of $P$: each element of $P$ is $\sigma$ of a class
meeting $\Omega'$, so such a fibre yields two classes in one $\mathfrak E$-block. Suppose instead that $\Psi$ is injective on $P$. Let $S\in P$ and let
$g\in L$ preserve every block of $\Pi^\circ$. Then $\Psi(S^g)=\Psi(S)$ and $S^g\in P$, so $S^g=S$.
  * Let $B^\circ\in\Pi^\circ$ have $\lvert B^\circ\rvert\ge3$ and $0<\lvert S\cap B^\circ\rvert<\lvert B^\circ\rvert$. Take $a\in S\cap B^\circ$, $b'\in B^\circ\setminus S$, and a third
    point $c$ of $B^\circ$. The 3-cycle $(a\,b'\,c)$ is even, fixes $I$ pointwise, preserves all blocks, and moves $a$ to $b'\notin S$. So $S^g\ne S$. Contradiction.
  * **The parity case.** Let $B^\circ=\{a,b'\}$ with $a\in S$, $b'\notin S$. Such a $B'^\circ\ne B^\circ$ of size at least 2 exists. If not, every other block of $\Pi_E$ lost at least $b-1\ge1$ of its points to $I$, so there are at most $\lvert I\rvert$ other blocks, each contributing at most one point to $E^\circ$. Then $\lvert E^\circ\rvert\le2+\lvert I\rvert$, which is impossible because $\lvert E^\circ\rvert>\tfrac34k-\lvert I\rvert$ and $\lvert I\rvert\le k/20$.
    Take $c\ne c'$ in $B'^\circ$ and $g:=(a\,b')(c\,c')$. It is even, fixes $I$ pointwise, preserves all blocks, and $g$ sends $a$ to $b'$. So $b'\in S^g\setminus S$, and
    $S^g\ne S$. Contradiction. *(Note that $g$ need not fix $S$ on $B'^\circ$; the red-team's version required it and needed extra cases.)*

  Hence every $S\in P$ meets each block of size at least 2 in nothing or in the whole block. Condition on $u_1=v$. If $v$ lies in a block of size at least 2, then $S$ must contain a fixed other
  point of that block, which has probability $(s-1)/(k-1)<\tfrac1{10}$. So
  $$\mu(\text{every }S\text{ is such a union})\le\frac{\lvert Q\rvert+\lvert I\rvert}{k}+\frac1{10}\le\frac14+\frac1{10}+\frac1{10}<\frac56,$$
  using that singleton blocks number at most $\lvert I\rvert$ and $\lvert Q\rvert<k/4+\lvert I\rvert$, so $\lvert Q\rvert+\lvert I\rvert\le k/4+2\lvert I\rvert\le k/4+k/10$. This contradicts $\mu(P)>\tfrac56$. ∎

**Remark.** Earlier versions treated singleton blocks by a case $z>2k/3$. With blocks of size at least 2 on $E$ (admissibility) and $\lvert I\rvert\le k/20$, that branch
is empty. If the colour classes of $Y$ are all at most $\tfrac34k$, the partition is not used at all, which covers HBD's trivial (singleton) partitions at L1443.

**Lemma 5.3 (Johnson).** Suppose $Y$ is a Johnson structure: $\mathcal J(r,s')$ on $\Gamma_0$, with $O:=[k]\setminus\Gamma_0$ coloured, and $r\ge2s'$, $s'\ge2$. Then either the round is a
shrink, or the giant degree of the next node on the large orbit satisfies $k'\le r\le1+\sqrt{2k}$ (if a next giant exists).

*Proof.* $L$ preserves the colouring with classes $\Gamma_0$ and the colour classes of $O$.

*Step 1.* If $\lvert\Gamma_0\rvert\le\tfrac34k$, Lemma 5.1 gives a shrink. Else $K:=\lvert O\rvert<k/4$.

*Step 2.* $j:=\lvert S\cap O\rvert$ is $L$-invariant. For $1\le j\le\min(K,s)$ the hypergeometric probability is less than $\tfrac56$. Let
$N_i:=\binom Ki\binom{k-K}{s-i}$.
  * If $Ks\le3.25jk$: $N_{j-1}/N_j=\frac{j(k-K-s+j)}{(K-j+1)(s-j+1)}\ge\frac{0.65\,jk}{Ks}\ge\frac15$, so $N_j\le\tfrac56(N_{j-1}+N_j)$.
  * If $Ks>3.25jk$: then $(K-j)(s-j)\ge Ks-j(K+s)>2.9jk>0$ and $N_{j+1}/N_j\ge\frac{2.9jk}{(j+1)k}\ge1.45$, so $N_j\le\tfrac56(N_j+N_{j+1})$.

  So a large $P$ has $j=0$: every $S\in P$ lies in $\Gamma_0$.

*Step 3.* Let $M:=L\cap\mathrm{Alt}(O)$. For $c$ meeting $\Omega'$, $\sigma(c)\subseteq\Gamma_0$, so $\mathrm{Alt}(O)\le\mathrm{Alt}([k]\setminus\sigma(c))\le S_c$ and $M$ fixes every class
meeting $\Omega'$. So $(R^{\Omega'})^{\mathcal C'[\Omega']}$ is a quotient of $L/M$. Restricting to $\Gamma_0$ has kernel $L\cap\mathrm{Sym}(O)$, which contains $M$ with index at most 2, and has image
in $\mathrm{Aut}(\mathcal J)$ $=\mathrm{Sym}(\Lambda)$, or $\mathrm{Sym}(\Lambda)\times C_2$ when $r=2s'$. So every alternating composition factor $A_j$ ($j\ge5$) of $L/M$ has $j\le r$.

*Step 4.* The next node's giant $A_{k'}$ ($k'>40t$) is a composition factor of $P'=(H')^{\mathfrak D'}$. Since $\mathfrak D'\succeq\mathcal C'[\Omega']$ (rule G3), $P'$ is a quotient
of $(H')^{\mathcal C'[\Omega']}$. So $k'\le r$. Finally $\binom r2\le\binom r{s'}=\lvert\Gamma_0\rvert\le k$, so $r\le1+\sqrt{2k}$. ∎

**Proposition 5.4 (trichotomy).** [PROVEN] A heavy round in case (v) is one of:
* **(S) shrink**: every $R$-orbit has at most $\tfrac56n_v$ points;
* **(T) tower**: a unique orbit $\Omega'$ has more than $\tfrac56n_v$ points, and $\mathfrak E$ of Lemma 5.2 is inserted, so $\rho$ drops by at least 1;
* **(J) Johnson**: a unique orbit $\Omega'$ has more than $\tfrac56n_v$ points, and the next giant on $\Omega'$ has $k'\le1+\sqrt{2k}$.

*Proof.* Design outcome (1) is a colouring with classes $<\tfrac34m\le\tfrac34k$, plus the class $[k]\setminus D$ of size $<k/4$. Lemma 5.1 gives (S). Outcome (2a), and (2b) with a
coloured $\tfrac34$-partition, satisfy Lemma 5.2's hypotheses: if a colour class $E$ has more than $\tfrac34k$ points it is contained in $C$ (as $\lvert D\setminus C\rvert$ and
$\lvert[k]\setminus D\rvert$ are less than $k/4$), and $\Pi_E$ has blocks of size in $[2,\tfrac34\lvert C\rvert]$. $L$ contains the required elements since permutations within a
block preserve the colouring and the partition, and $A_k\le\varphi(G')$. Also $\lvert I\rvert\le t+c_H\log^2k\le k/20$ by $k>\tau_0$. Outcome (2b) with a Johnson scheme is Lemma 5.3. ∎

---

## 6. Light rounds and item 4 [PROVEN]

**Proposition 6.1 ($k'\le3k/4$ for light rounds).** Let $(G',\varphi,k)$ be a node with $k>\tau_0$ and $R$ a light child (cases (i)–(iv)). If the next node on a large
orbit $\Omega'$ has giant degree $k'$, then $k'\le3k/4$.

*Proof.* $A_{k'}$ is a composition factor of $N'\trianglelefteq P'=(H')^{\mathfrak D'}$ with $\mathfrak D'\succeq\mathcal C'[\Omega']$. So it is a composition factor of $(H')^{\mathcal C'[\Omega']}$, a
quotient of $R^{\mathcal C'}\cong R/(R\cap\ker\varphi)\cong\varphi(R)$. If $k'>3k/4$ then Lemma A gives $\mathrm{Alt}(\Delta)\le\varphi(R)$ with $\lvert\Delta\rvert>3k/4$. This contradicts the symmetry
defect at least $1/4$ of the structures in cases (i), (ii), (iv) (GNS Lemma 6.6 and CB Prop. 5.2; red-team w9 §3.2), and in case (iii) $\varphi(R)$ fixes at least $\tfrac34k$
points. ∎

**Item 4, cost of the binary calls.** Case (iv) calls B–H on graphs with at most $k$ vertices, at most $k^6$ times per node. Each call costs $\exp(O(\log^3k))$. Since
$k\le\lvert\mathcal C'\rvert\le n$ (Lemma 4.1) and $\log k\le L$,
$$\log^3k\le L^2\log n,\quad\text{so}\quad\exp(O(\log^3k))\le n^{O(L^2)}.$$
This is additive per node and is absorbed in §7. [PROVEN] Case (iii), (i), (ii) need no isomorphism test. So the correct statement is **no $t$-ary black box**, not "no black
box".

---

## 7. The recurrence [PROVEN]

Let $T(n,\rho)$ be the maximum running time of Algorithm G on instances with at most $n$ points and $\rho(\mathbb T)\le\rho$.

**Macro step.** For a transitive instance on $n$ points that reaches G5, define its tree $\mathcal T$:
* nodes are transitive instances reached by *same-domain edges*: from a node, descend to each coset of $G'$, then take each child coset of a light round or of a heavy round of type (J), and follow
  its orbit of more than $n/2$ points (there is at most one);
* heavy rounds of type (S) or (T) end the path.

**Lemma 7.1 (size of a macro step).** $\lvert\mathcal T\rvert\le Z:=2^{c_1L^2}$. [PROVEN]

*Proof.* Along a root-to-leaf path, each aggregation node with giant degree $k$ gives $k'\le3k/4$ (Prop. 6.1) or $k'\le1+\sqrt{2k}$ (Prop. 5.4(J)). Hence there are $O(L)$ aggregation nodes on a path,
starting from $k\le d$. The branching at a node is at most $d$ (descent) times at most $2k^6$ (light) or $C_h$ (type (J)). The light rounds contribute $2^{O(L\cdot L)}$ in total. The type (J) rounds have
$k_{i+1}\le1+\sqrt{2k_i}\le k_i^{2/3}$ (as $k_i>360$), and consecutive giants never increase; so
$\sum_i(t\log k_i+c_H\log^2k_i)=O(tL+L^2)=O(L^2)$. ∎

**Exits per node.** At most $2^{c_2L^2}n$ total domain, each piece at most $n/2$. These are: certificates and comparisons (at most $k^{2t}\cdot t!$ pieces of total domain $n$ each, GNS Lemmas 6.2, 6.3); orbits of
children of size at most $n/2$; Luks steps G3 and G4 ($d^{1+\log d}$ or $k!$ cosets, each with pieces inside blocks); and intransitive $G'$. Non-recursive work per node is at most
$n^{c_4}\,2^{c_5L^2}\exp(c_6\log^3k)$.

**Theorem 7.2.** [PROVEN, modulo §11] There are $A,B=O(L^2)$ with $T(n,\rho)\le n^A2^{B\rho}$ for all $n\ge1,\rho\ge0$.

*Proof.* Induction on $n+\rho$. Let $U:=n^A2^{B\rho}$. All pieces use $\rho'\le\rho$ (Lemmas 2.1, 2.2).
* G1, intransitive: $\sum T(n_i,\rho)+\mathrm{poly}(n)$ with $\sum n_i=n$, $n_i<n$. So at most $((n-1)^A+1)2^{B\rho}+\mathrm{poly}(n)\le U$ for $A$ large.
* G2, semi-regular: $b^2T(n/b,\rho)\le b^{2-A}U\le U/4$ for $A\ge4$.
* Macro step (the remaining case), summing over $\mathcal T$:
  * Exits: $Z\cdot2^{c_2L^2}n\cdot(n/2)^{A-1}2^{B\rho}=Z2^{c_2L^2}2^{-(A-1)}U\le U/4$.
  * Type (S), at most $C_h$ children per node, each with $\sum n_i\le n$ and $n_i\le\frac56n$: at most $ZC_h(5/6)^{A-1}U\le U/4$.
  * Type (T), at most $C_h$ children per node, each with large orbit at $\rho-1$ and small orbits at $\rho$ of size at most $n/6$: at most $ZC_h2^{-B}U+ZC_h(1/6)^{A-1}U\le U/4$.
  * Work: $Z\,n^{c_4}2^{c_5L^2}\exp(c_6\log^3k)\le n^{A-1}\le U/4$, using $\log^3k\le L^2\log n$ for $n\ge2$.

  These hold for $A,B=O(L^2)$ (explicit constants in the check script, part 4). ∎

**Theorem G.** [PROVEN, modulo §11; not red-teamed] String isomorphism for $\hat\Gamma_d$ groups on $n$ points, and hence isomorphism of graphs of maximum degree $d\ge2$, is decidable in
time $n^{O(\log^3d)}$.

*Proof.* By orbit-by-orbit processing assume transitive. (G1) yields an instance on $N\le n^{O(L)}$ points with an almost $d$-ary tower. By Lemma 2.1(a), $\rho\le2\log_2N$, so Theorem 7.2 gives
$N^A\,2^{2B\log_2N}=N^{O(L^2)}=n^{O(L^3)}$. The reduction from GI is GNS Thm 8.1. ∎

---

## 8. Regimes and the final statement (task 2)

| regime ($\ell=L^x$) | range of $d$ | bound [PROVEN modulo §11] | what gives it |
|---|---|---|---|
| $x\ge3$ | $d\le2^{(\log n)^{1/3}}$ | $n^{O(L^3)}$ | Theorem G (also Theorem C alone: signed already) |
| $2\le x<3$ | $2^{(\log n)^{1/3}}<d\le2^{(\log n)^{1/2}}$ | $n^{O(L^3)}$ | Theorem G (also Theorem X: signed already) |
| $3/2\le x<2$ | $2^{(\log n)^{1/2}}<d<2^{(\log n)^{2/3}}$ | $n^{O(L^3)}$ | **Theorem G only.** This is the range that was open. |
| $1\le x<3/2$ | $d\ge2^{(\log n)^{2/3}}$ | $\exp(O(\log^3n))=n^{O(L^{2x})}$, better than $L^3$ | Babai–Helfgott alone. Theorem G also gives $n^{O(L^3)}$, which is worse here. |

* **Overall:** $n^{O(\min\{\log^3d,\ \log^2n\})}$ for all $d$. The worst $c$ over all regimes is exactly 3, attained for $x\ge3/2$.
* At $d=n^{\Omega(1)}$ this is weaker than Babai–Helfgott and contradicts nothing. Barrier 1 of w8 ($c<2$ would beat B–H) is unchanged.
* The exponent 3 is the accounting floor from w8 §2.7: $\log N=\Theta(L\ell)$ times $K=\Theta(L^2)$.

**Strongest statement independent of §5–§7** (if a red-team finds a hole in Theorem G): Theorem X, $n^{O(\log^3d)}2^{O(\log^5d)}$. Its region of exponent 3 is
$x\ge2$ together with $x\le3/2$, leaving $3/2<x<2$ at exponent $\min(5-x,2x)\le10/3$.

---

## 9. Corrections to earlier memos

1. M §3.2, M §4.2: "$\lvert\vec z\rvert=O(\log m)$" is **wrong as a point count**. HBD's base case individualizes all of $V_2$, which can have $(6\log m)^{3/2}$ points, and the $d_j$ add up to more than
   $\log m$. What is $m^{O(\log m)}$ is the number of stream leaves. So Theorem X's and Theorem G's branch counts stand, but statements of the form "tuple of length $O(\log m)$" must be read as "stream with
   $m^{O(\log m)}$ leaves", and the side-2 enumeration runs over the stream tree (each point chosen from its current canonical set), not over $D_2^{O(\log m)}$. This confirms and sharpens red-team w11 §1.4.
2. M §4.2 lists GNS case (ii) under Lemma O2. Case (ii) is light; O2 is not needed there.
3. M §4.3 states phases with "constant $\rho$". The cleaner formulation is §7: a macro step ends at (S) or (T), and the potential is applied through $T(n,\rho)$.
4. M §3.4 and red-team §1.2: HBD's Johnson schemes as produced by Prop. `bicoup` may have $r=2s'$ (when $d_1=\lvert V_2\rvert/2$). Then $\mathrm{Aut}=\mathrm{Sym}(\Lambda)\times C_2$. Nothing changes.
5. M §1.3's "arity reduction costs $k^{<t}$" remains refuted (red-team w11 §2.2) and is not used anywhere here.

---

## 10. Novelty (task 5), checked 2026-11-08

* **GNS v3; Neuen 2020 (2002.06997); Grohe–Neuen survey 2021; Neuen survey 2026.** Local copies re-grepped: exponent stated only as "polylog(d)" or "for an absolute constant $c$". GN21 L1079 (text) explains the black-box design and proposes no subroutine variant.
* **Pago (2302.05426).** Lemma `G_groupInduction` (composition factor to subgroup, with index alternative), credited to Wiebking for the primitive case. Must be cited for Lemma A. Contains nothing on the GNS exponent.
* **Citing papers.** Semantic Scholar's citation list for arXiv:1802.04659, entries from 2024–2026 (7): none concerns the exponent. The only related one is Neuen's 2026 survey.
* **Web searches** (2 on the exponent, 1 on Neuen's thesis): nothing after GNS/GNSW/Neuen 2020 states an explicit $c$ or a subroutine-based analysis.
* **Still unread:** Neuen's thesis (the record page at publications.rwth-aachen.de returned an empty response; not pursued further) and the SICOMP text.
* **Verdict:** I found no prior statement of $c=3$, of $c=10/3$, or of the hybrid of GNS with HBD's $\rho$. HBD's $\rho$, Design Lemma and Split-or-Johnson are known and are credited. The residual risk is the unread thesis and SICOMP text.

---

## 11. Ledger

**Proven in this memo (complete argument, not red-teamed):** Lemmas 2.1, 2.2; the §2.4 audit; Lemma 3.1; Lemma 4.1; Lemmas 5.1–5.3 and Prop. 5.4; Prop. 6.1; Lemma 7.1; Theorem 7.2; Theorem G.

**Trusted (published).**
* GNS (SICOMP 52(6), 2023; read as arXiv v3): Thms 4.3, 4.6, 5.8, 5.9, 6.4, 8.1; Lemmas 6.2, 6.3, 6.6, 6.7, 6.9, 7.1; App. A, including Thm A.2. CFSG enters through Lemma 7.1, Thm 3.13/4.3 and Thm A.2.
* Grohe–Neuen survey Thm 4.16 (domain $n^{O(\log d)}$).
* HBD (Astérisque 407, 2019; arXiv:1710.04574): Prop. `design`, Thm `coupjohn` with Props `bicoup`, `cohcoup`, the WL functors, §`subs:idgroup`, and B–H's $\exp(O(\log^3N))$.
* Bochert's theorem or Praeger–Saxl (for Lemma A).

**Trusted (repository, red-teamed).** Lemma A (w8, w9); Prop. 2 (domain count); CB §7.3 fix (subsumed by rule G3); CB Prop. 5.2 and Lemma T′ for symmetry defects; Theorem X.

**Used only from HBD's proof, not its statement** (read at L1423–1700, not re-proved): the functorial reading of Split-or-Johnson (H3), namely stream tree, leaf bound, point bound. This is the least-audited input. If the leaf bound were weaker than $m^{O(\log m)}$, say $m^{\omega}$, then $C_h$ and hence $A,B$ would grow by that factor and the exponent would change accordingly; nothing else breaks.

**Not checked.** The SICOMP text; Neuen's thesis; the proofs of GNS Thm 5.8 and of Lemma 7.1 (trusted). No machine verification of anything.

---

## 12. Checks run

`nice -n 19 python3 -I docs/w12-theoremg-check.py`, all passing:
* Part 1: $f(a)+f(b)\le f(ab)-1$ for $a,b<600$; monotonicity; 3000 random tower simulations, with restriction and strict insertion.
* Part 2: exact rational enumeration of 97,569 wreath-type orbit types (1,531 of measure $>5/6$) confirming Lemma 5.2(a,b); 16,640 $\Psi$-fibres, largest measure 0.513.
* Part 3: the hypergeometric bound in 23,940 cases (max 0.443); the Johnson chain sum at most $18.3L^2$ with constant 12.
* Part 4: the five inequalities of Theorem 7.2 close with $A,B=O(L^2)$.
* Part 5: exponent profiles.

These are consistency checks of the elementary combinatorics. They do not test the group-theoretic inputs.

**Single point I would attack first as a referee.** Lemma 3.1's functoriality of $\mathrm{Proc}^+$ through the deep recursion of Prop. `bicoup` (choices of $S$, recursion on $V_2'$, the complement switch), together with the per-path bound on the branching product. It is mechanically true of the procedure as written, but it has been read, not formalized.
