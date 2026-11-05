# w8-gnsexp: the exponent in Grohe–Neuen–Schweitzer, and how far it can be pushed without HJ

Branch `w8-gnsexp`, 2026-11-05. Wave 8. Not refereed. No Lean; the only computation was two
one-line factorial comparisons (§3.1), which took milliseconds.

**Labels.**
* **[PROVEN]**: a complete argument is given here. It relies only on published results, which
  are listed in §7, and on the repository's §7.3 fix to GNS Lemma 7.2.
* **[SKETCH]**: the argument is given and its gaps are named.
* **[CONDITIONAL: …]**: proven or sketched under the named hypothesis.
* **[SPECULATION]**: an opinion.

**Notation.**
* $L:=\log_2(d+2)$ and $\ell:=\log_2 n$, with $d\le n$ throughout.
* "Exponent $c$" means time $n^{O(L^c)}$.
* Regimes are written $\ell=L^x$ with $x\ge1$.
* "G L…" is a line of GNS's `bounded-degree-polylog-d.tex` (arXiv:1802.04659v3), and "HJ L…" a line
  of HJ's `graph_isomorphism.tex` (arXiv:2611.01399v1).
* CB is `docs/canonization-bounded-degree.md`.
* B–H is Babai's algorithm with the Helfgott–Bajpai–Dona analysis, exp$(O(\log^3 m))$ for string
  isomorphism on $m$ positions (arXiv:1710.04574, `BDHv8.tex` L2047).

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Exponent of GNS as written (with the CB §7.3 fix) | **$c=5$.** Two independent terms each give exactly $L^5$. (i) The main recursion is $N^{K}$, with $\log N=O(L^2\ell)$ as GNS Thm 4.6 states it and $K=O(L^3)$ from GNS Lemma 7.2 (height $O(L^2)$ times branching $d^{O(1)}$). (ii) The per-node black box (Babai's test on $t$-ary structures, $t\approx L$) costs $\exp(O((t\log k)^3))=2^{O(L^6)}\le n^{O(L^5)}$. Reading GNS's displayed bound for Lemma 6.7 literally gives 6. | [PROVEN] |
| 1′ | Same algorithm, sharper bookkeeping | GNS's own proof of Thm 4.6 gives $N\le n^{O(L)}$, not $n^{O(L^2)}$. This is known: Grohe–Neuen survey Thm 4.16, citing Neuen's thesis. The main recursion becomes $n^{O(L^4)}$. With a top-level switch to B–H when $\ell\le L^2$, the bound is **$c=4$ for all $d$**. | [PROVEN] |
| 2 | Best unconditional improvement | **New: the giant degree drops multiplicatively, $k'\le 3k/4$**, in place of $k'\le k-k/(3\log k)$ (Lemma A + Prop. B). The height falls from $O(L^2)$ to $O(L)$, the macro step from $2^{O(L^3)}$ to $2^{O(L^2)}$, and **the main recursion to $n^{O(L^3)}$**. With the black box: **$c=3$ whenever $\log n\ge\log^3 d$**, which includes $d=\mathrm{polylog}\,n$ (giving $n^{O((\log\log n)^3)}$, against $n^{O((\log\log n)^5)}$ from GNS), and also whenever $\log n\le\log^{1.5}d$. **$c=4$ for all $d$.** | [PROVEN] |
| 2′ | With a better black box | Solving the black box with a black-box-free GNS variant (Babai's Design Lemma + Split-or-Johnson) gives $X\le 2^{O(L^5)}$. That yields **$c=3$ whenever $\log n\ge\log^2 d$**, and **$c=10/3$ for all $d$**. | [SKETCH] |
| 2″ | Barriers | (a) **$c<2$ would beat B–H for general GI**: put $d=n$. So $c\in[2,3]$ is the realistic unconditional range. (b) GNS's architecture has floor $c=e+a=1+2=3$. Here $e=1$ is forced by the change of action (the heart module $\mathbb F_2^{k-1}\rtimes A_k$ breaks Thm 5.8 for every $k$), and $a=2$ by $\binom kt\ge2^{\Theta(L^2)}$ exits per node. (c) The black box is self-similar: GNS-type methods applied to it need the same black box again. | (a) [PROVEN]; (b), (c) [SKETCH] |
| 3 | HJ Thm A.9 (hereditary budget) independently, in $\hat\Gamma_d$ | **Not easier in $\hat\Gamma_d$.** I re-derived HJ's proof skeleton (inheritance, localization, blocks, Cartesian, Johnson anchors with the entropy inequality, the final induction) and the extra-orbit mark. All of it checks, with one harmless slip in a constant. The only unchecked input is HJ's primitive-valuation lemma (standard CFSG facts), and $\hat\Gamma_d$ does not simplify it. **Weak form, new:** replacing that lemma by GNS Thm 3.13 gives $\sigma\le C\log d\cdot\log N$ for transitive $G\in\hat\Gamma_d$. That yields $n^{O(\log^2 d)}$ for degree-$d$ GI **conditional on HJ §§4–7 but not on Thm A.9's CFSG lemma**. | weak form [SKETCH]; consequence [CONDITIONAL] |
| 4 | Novelty | No explicit value of $c$ appears anywhere. The $n^{O(\log d)}$ change-of-action count is known (Grohe–Neuen survey Thm 4.16). The multiplicative potential, the black-box regime analysis and the weak budget were **not found** in GNS v1–v3, Neuen ICALP'20/TALG'22, the 2021 and 2026 surveys, or web searches. Neuen's thesis could not be retrieved, so it is the main residual novelty risk. | — |

**Exponent ladder (unconditional).**

| version | change of action $e$ | macro step $a$ | black box | exponent, all $d$ | exponent, $\log n\ge\log^3d$ |
|---|---|---|---|---|---|
| GNS as written | 2 (Thm 4.6 as stated) | 3 | $2^{O(L^6)}$ | **5** | 5 |
| GNS + Thm 4.16 count + B–H switch | 1 | 3 | $2^{O(L^6)}$ | **4** | 4 |
| + multiplicative potential (this memo) | 1 | **2** | $2^{O(L^6)}$ (B–H) | **4** | **3** [PROVEN] |
| + black box by the β-variant | 1 | 2 | $2^{O(L^5)}$ | **10/3** [SKETCH] | 3 |
| conditional on HJ (Theorem R\*) | — | — | — | 1 | 1 |

---

## 1. Task 1: the exponent of GNS as written

### 1.1 The two layers

GNS's algorithm for string isomorphism under $G\in\hat\Gamma_d$ ($n$ positions) has two layers.
1. **Change of action** (Thms 4.3, 4.6). Each transitive constituent becomes an instance on $N$
   points carrying an almost $d$-ary sequence.
2. **The almost $d$-ary recursion** (Lemma 7.2, Thm 7.3). Every *macro step* (a transitive instance
   with $|\mathfrak B_1|\le d$) produces recursive calls on domains $\le N/2$ whose sizes sum to at
   most $2^{K}N$. Lemma 2.8 (or CB Lemma 7.0) then gives $N^{K+1}$ leaves.

The total time is $N^{K+1}\cdot(\text{work per macro node})$, and each node does an additive
amount of non-recursive work, dominated by the black-box isomorphism test.

### 1.2 Ledger of factors

| factor | where | size | role |
|---|---|---|---|
| cosets of $\mathrm{Soc}(G^B)$, or regular action of small $G^B$ | Thm 4.3 (G1088, G1113) | $\lvert\Omega^*\rvert\le n^{c_1L+c_2+1}$ | $\log N$ |
| Johnson unfolding $\binom mt\to[m]^{\langle t\rangle}$ | Thm 4.6 (G1290, Claim G1429) | factor $t_i!\le\binom{m_i}{t_i}^{\log m_i-1}$ per Johnson level | $\log N$ |
| test sets | Lemma 6.2, $t=\max\{9,3+\log d\}$ | $\binom kt\cdot t!\cdot n\le k^t n=2^{O(L^2)}n$ exits per node | $K$ |
| comparisons | Lemma 6.3 | $\binom kt^2\, t!\, n=2^{O(L^2)}n$ exits | $K$ |
| aggregation individualizations | App. A case (iv) | $\le4$ points, one orbital, one vertex: $r\le k^6$ branches | per level |
| descent $H\to G'$ | Lemma 7.1, index $\le\lvert\mathfrak B\rvert\le d$ | $\le d$ branches | per level |
| recursion depth | Lemma 7.2: $k'\le k-k/(3\log k)$ | height $O(L^2)$, so $\lvert\mathcal T\rvert\le(dk^6)^{O(L^2)}=2^{O(L^3)}$ nodes | $K=O(L^3)$ |
| small primitive $P$, Luks | Lemma 7.2 | $\lvert P\rvert\le d^{1+\log d}=2^{O(L^2)}$ exits | $K$ |
| leaves $k\le10t$ | Lemma 7.2 | $k!=2^{O(L\log L)}$ | — |
| black box: $\mathrm{Iso}(\mathfrak A_1,\mathfrak A_{2,j})$, $t$-ary on $\le k$ points | Lemma 6.7 (G2016) | Miller graph on $k^{O(t)}$ vertices, then B–H: $\exp(O((t\log k)^3))=2^{O(L^6)}$ | additive per node |
| enumeration of primitive groups of order $d'^{O(\log d)}$ | — | in GNS this is not enumeration but the regular-action blow-up of Thm 4.3 | in $\log N$ |

### 1.3 Theorem 1 (GNS as written)

**Theorem 1.** [PROVEN] GNS's algorithm, with the CB §7.3 fix, runs in time $n^{O(L^5)}$. The
bounds written in its proof add up to exactly this exponent and no less.

*Proof.*
* *The change of action.* By Thm 4.6 as stated, $N\le n^{(c_1L+c_2+1)L}=n^{O(L^2)}$.
* *The macro step.* Lemma 7.2 gives $\sum n_i\le2^{O(L^3)}N$, so $K=O(L^3)$. With the fix the
  inequality $k'\le k-k/(3\log k)$ holds (CB §7.3); without it the written proof has a gap (CB §7.2).
* *Leaves.* GNS Lemma 2.8, or CB Lemma 7.0 when the semi-regular step violates $\sum n_i\le2^Kn$,
  gives $N^{K+1}=n^{O(L^5)}$ leaves.
* *Work per node.* Each macro node has $2^{O(L^3)}$ tree nodes. Each tree node makes at most $k^6$
  black-box calls on structures with $k^{O(t)}=2^{O(L^2)}$ elements. With B–H each call costs
  $2^{O(L^6)}$. This is additive per node, and $2^{O(L^6)}=d^{O(L^5)}\le n^{O(L^5)}$.

Both terms are $L^5$, so neither can be dropped without changing the algorithm or the analysis. ∎

*Remarks.*
* GNS's display in Lemma 6.7, $k^{O(t^c(\log k)^c)}$, overstates Babai's test by a factor $\log k$
  in the exponent. Taken literally with $c=3$ it is $2^{O(L^7)}$, which would give exponent 6. The
  real cost of the step as described is $2^{O(L^6)}$.
* GNS cite Babai with an unspecified $c_B$. In general the exponent is $\max(5,2c_B-1)$, and HBD's
  $c_B=3$ gives 5.
* An earlier red-team (`docs/redteam-theorem-R.md` §7) estimated $c\ge3$. That estimate counted
  only the $2^{O(\log^3d)}$ macro nodes.

### 1.4 Sharper bookkeeping for the same algorithm

**Proposition 2 (change of action).** [PROVEN; known, see below] The domain built in GNS
Thms 4.3 and 4.6 has size $N\le n^{(c_1+1)L+c_2+1}$.

*Proof.*
* Step 1 (Thm 4.3) gives $n_1:=\lvert\Omega^*_1\rvert\le n^{c_1L+c_2+1}$.
* In step 2, Claim G1429's own count is exact. Every leaf has $\prod_{i\in I}t_i!$ maximal branches
  above it, so $\lvert M\rvert=n_1\prod_{i\in I}t_i!$, with the product taken along one branch.
  Lemma 2.9 gives $\binom mt^{\log m}\ge m^t\ge\binom mt\,t!$, so $t_i!\le s_i^{\log d-1}$ where
  $s_i=\binom{m_i}{t_i}$.
* GNS then bound $\prod_{i\in I}s_i\le n_1$. The sharper bound is $\prod_{i\in I}s_i\le n$, the
  *original* domain size. The Johnson levels arise only in case 2 of Thm 4.3. There, the chain
  $\mathcal P_1,\dots,\mathcal P_t$ refines the $b$ classes of $\mathfrak B_{\ell+1}[B_1]$ into
  singletons, so its branchings multiply to exactly $b$. Each induction step divides the block size
  $q$ by its $b$, so the $b$'s along a branch multiply to at most $n$. The coset levels and the
  case-1 levels are semi-regular and lie outside $I$.
* Hence $N\le n_1\cdot n^{\log d-1}$. ∎

This is how the Grohe–Neuen survey (arXiv:2011.01366, Thm 4.16) states the normalization:
$\lvert\mathrm{Br}(G,v_0)\rvert\le n^{O(\log d)}$, citing GNS and Neuen's thesis. GNS's own
Thm 4.6 is weaker only because its last inequality is loose.

**Corollary 3.** [PROVEN]
* With the fix, GNS's algorithm runs in $n^{O(L^4)}\cdot2^{O(L^6)}$. This is $n^{O(L^4)}$ when
  $\ell\ge L^2$.
* If one runs B–H on the whole input whenever $\ell<L^2$ (cost $2^{O(\ell^3)}\le n^{O(L^4)}$), the
  bound is $n^{O(L^4)}$ for all $d$.

### 1.5 Is that bookkeeping tight? [SKETCH]

Each factor is attained by the bounds, though I have no instance on which the algorithm itself is
known to take that long.

* **Johnson unfolding.** Take $A_m^{(t)}$ with $t\approx m/40$; this satisfies $m>4\log\binom mt$,
  so it is option 2. Then $t!=\binom mt^{\Theta(\log m)}$. Product actions of such groups give
  $N=n^{\Theta(L)}$ from step 2 alone.
* **Coset blow-up.** Step 1's factor $\prod\lvert G^B\rvert$ is also $n^{\Theta(L)}$, for example on
  towers of $\mathrm{AGL}(r,2)$ with $d\approx2^r$ (see `docs/w1-structure.md` §2.3 for this class).
* **Exits.** When $k\ge d^{\Omega(1)}$, a node has $\binom kt\ge(k/t)^t=2^{\Theta(L^2)}$ test sets,
  each making a window call that may be as large as $N/2$.

---

## 2. Task 2: unconditional improvements

### 2.1 Lemma A (large alternating sections force large alternating subgroups)

**Lemma A.** [PROVEN] Let $L_0\le S_k$, and suppose $A_m$ is a composition factor of $L_0$ with
$m>3k/4$ and $m\ge16$. Then there is $\Delta\subseteq[k]$ with $\lvert\Delta\rvert\ge m$ and
$\mathrm{Alt}(\Delta)\le L_0$, acting on $\Delta$ and fixing $[k]\setminus\Delta$ pointwise.

*Proof.* We use induction on the degree. Every degree $n'$ that occurs satisfies $n'\le k<4m/3$, so
$m>3n'/4>n'/2$.

* **Intransitive.** Let $O$ be an orbit, $R$ its complement, and $K:=(L_0)_{(R)}\trianglelefteq L_0$.
  The group $K$ acts faithfully on $O$, and $L_0/K\cong L_0^R$. By Jordan–Hölder, $A_m$ is a
  composition factor of $K$ or of $L_0^R$.
  * *Factor of $K$.* Induction gives $\Delta\subseteq O$ with $\mathrm{Alt}(\Delta)\le K\le L_0$.
    Since $K$ fixes $R$ pointwise, this $\mathrm{Alt}(\Delta)$ fixes $[k]\setminus\Delta$.
  * *Factor of $L_0^R$.* Induction gives $\Delta\subseteq R$ with
    $\mathrm{Alt}(\Delta)\le L_0^R$, acting on $\Delta$ and fixing $R\setminus\Delta$. Let $L_1$ be
    the preimage of this $\mathrm{Alt}(\Delta)$ in $L_0$. Let $M\trianglelefteq L_1$ consist of the
    elements that fix $O$ pointwise. Then $M^R\trianglelefteq\mathrm{Alt}(\Delta)$, so $M^R$ is
    $\mathrm{Alt}(\Delta)$ or trivial.
    * If $M^R=\mathrm{Alt}(\Delta)$, then $M=\mathrm{Alt}(\Delta)\le L_0$, since $M$ fixes $O$ and
      $R\setminus\Delta$ pointwise. We are done.
    * If $M^R=1$, then $M=1$, so the restriction $L_1\to\mathrm{Sym}(O)$ is injective. Then
      $\mathrm{Alt}(\Delta)$, a quotient of $L_1$, is a quotient of a subgroup of $\mathrm{Sym}(O)$.
      That is impossible, because $\lvert O\rvert\le k-\lvert\Delta\rvert<k/4<\lvert\Delta\rvert$
      and $\lvert O\rvert!<\lvert\Delta\rvert!/2$.
* **Transitive and imprimitive**, with $b'$ blocks of size $b$ ($b,b'\ge2$). Both $b$ and $b'$ are
  at most $k/2<m$. The block-action kernel embeds in $S_b^{b'}$. By the projection–kernel argument
  its composition factors are composition factors of subgroups of $S_b$, so they have order at most
  $b!<m!/2$. The block action is a subgroup of $S_{b'}$ and is excluded the same way.
  Contradiction.
* **Primitive of degree $n'$.** Since $\lvert A_m\rvert\le n'!$ we have $n'\ge m$.
  * If $L_0\ge A_{n'}$, take $\Delta$ to be the whole orbit.
  * If $n'=m$, then $\lvert L_0\rvert\ge m!/2$ forces $L_0\ge A_m$.
  * Otherwise $m<n'<4m/3$. By Bochert's theorem (Dixon–Mortimer Thm 3.3B),
    $\lvert L_0\rvert\le n'!/\lfloor(n'+1)/2\rfloor!$. This is $<m!/2$ for all $m\ge16$ and
    $m<n'\le4m/3$. I checked this numerically for $m<400$; beyond that, Stirling shows the gap
    only widens. So $L_0$ cannot have $A_m$ as a section. Contradiction.

  Alternatively, Praeger–Saxl ($\lvert L_0\rvert<4^{n'}$) covers $m\ge42$ for every $n'<2m$. ∎

This is a CFSG-free statement. It is in the spirit of GNS Lemmas 5.1–5.5 and is probably folklore,
but I did not find it stated in this form.

### 2.2 Proposition B (multiplicative potential)

**Proposition B.** [PROVEN, using the CB §7.3 fix] Along a same-domain path of the macro-step tree,
consecutive aggregation nodes satisfy $k'\le 3k/4$. Hence the height is at most
$\log_{4/3}(d/(10t))+2\le2.41\log_2d+2$.

*Proof.* We use the notation of CB §7.3.
* Let $R\in\{R_{\mathfrak A},L\}$ be the child. The next node's giant comes from Lemma 7.1 applied
  to $P'=(H')^{\mathfrak D}$ with $\mathfrak D\succeq\mathcal C'[\Omega']$ (this is the fix). So
  $A_{k'}$ is a composition factor of $N'\trianglelefteq P'$, hence of $P'$, hence of
  $(H')^{\mathcal C'[\Omega']}$.
* This last group is a section of $R^{\mathcal C'}\cong R/(R\cap\ker\varphi)\cong\varphi(R)$. Indeed
  $H'=(R^\circ)^{\Omega'}$, and its action on $\mathcal C'[\Omega']$ is a quotient of $R^\circ$'s
  action on the $\mathcal C'$-classes that meet $\Omega'$.
* So $A_{k'}$ is a composition factor of some subgroup $L_0\le\varphi(R)\le S_k$.
* **Option 1** (cases (i), (ii), (iv), (v)). Here $\varphi(R)\le\mathrm{Aut}(\mathfrak A_{\rm can})$,
  and $\mathfrak A$ has relative symmetry defect $\ge1/4$ (CB Prop. 5.2(2), GNS Lemma 6.6). So no
  $\mathrm{Alt}(\Delta)\le\varphi(R)$ has $\lvert\Delta\rvert>3k/4$, and the same holds for $L_0$.
  In GNS's own $H_j$, $\varphi(H_j)$ preserves $D_1$ and acts on it inside
  $\mathrm{Aut}(\mathfrak A_1)$. This gives the same conclusion, since $\lvert[k]\setminus D_1\rvert\le k/4$.
* **Option 2.** Here $\varphi(L)\le\mathrm{Sym}([k]\setminus\Delta_0)$ with
  $\lvert[k]\setminus\Delta_0\rvert\le k/4$.
* In both options, if $k'>3k/4$ then Lemma A applies, because $k'>10t\ge90\ge16$. It produces a
  forbidden $\mathrm{Alt}(\Delta)$. ∎

*Remarks.*
* The index bound $(4/3)^k$ (GNS Cor. 6.5) is not used. Only the defect matters.
* This is the GNS-route analogue of Babai's and Helfgott's progress measure ("$m'\le m/2$, or
  $m'\ll\sqrt m$", HBD L1346). GNS's index-counting argument lost it.
* The fix is necessary. CB §7.2 gives an input where $k'=k$ without it, and Lemma A says nothing
  about the kernel part $R\cap\ker\varphi$.

### 2.3 Theorem C (the improved main recursion)

**Theorem C.** [PROVEN, modulo the results in §7] Let $X(d)$ be the cost of one black-box call,
that is, isomorphism of two $t$-ary structures, $t\le 3+\lceil\log d\rceil$, on at most $d$ points
under $\mathrm{Alt}$ or $\mathrm{Sym}$. Then GNS's algorithm with the fix runs in time
$$n^{O(L^3)}\cdot\big(1+X(d)\big)$$
for string isomorphism under $\hat\Gamma_d$, and so for GI of maximum degree $d$.

*Proof.*
* By Prop. B, each level of $\mathcal T$ branches at most $2dk^6\le2d^7$ ways and the height is
  $O(L)$. So $\lvert\mathcal T\rvert\le2^{O(L^2)}$.
* The exits per tree node total at most $(k^{2t}+2k^6+d^{1+\log d}+(10t)!)\,N=2^{O(L^2)}N$.
* So one macro step has $\sum n_i\le2^{K_0L^2}N$ with every $n_i\le N/2$, i.e. $K=O(L^2)$.
* By CB Lemma 7.0, there are at most $N^{K+1}$ leaves and $O(\log N)\,N^{K+1}$ macro nodes. Each
  costs $2^{O(L^2)}\big(N^{O(1)}+X(d)\big)$.
* Prop. 2 gives $N\le n^{O(L)}$.
* The step from GNS's $\hat\Gamma_d$ instances to GI is GNS Thm 8.1. ∎

The same change applies verbatim to the canonical algorithm (CB Theorem A). CB §7.4's
$d^{7(h+2)}$ becomes $2^{O(L^2)}$, so canonization runs in $n^{O(L^3)}\cdot\exp(O(L^{2c_{BC}}))$,
where $c_{BC}$ is the unspecified exponent of Babai's canonization.

### 2.4 The black box

* **(α) B–H.** [PROVEN] $X(d)\le\exp(O((t\log d)^3))=2^{O(L^6)}$. Only case (v) of the aggregation
  needs it:
  * cases (i), (ii) are colourings and partitions, whose automorphism groups take polynomial time;
  * case (iv) is binary, so B–H costs $2^{O(L^3)}$;
  * case (iii) uses no black box.
* **(β) A black-box-free variant on the inner instance.** [SKETCH] Solve the black box by running
  GNS's almost $k$-ary algorithm on the inner instance $I=(S_k\text{ on }[k]\sqcup[k]^2\sqcup[k]^t)$.
  * $I$ needs no change of action: $S_k$ on injective tuples is already $k$-ary, by fixing
    coordinates one at a time.
  * In cases (iv)/(v) of $I$, replace GNS's black box by Babai's Extended Design Lemma.
    * The Design Lemma individualizes $\le t'-1$ points ($k^{t'}$ branches, $t'=3+\log k$).
    * UPCC Split-or-Johnson costs $k^{O(\log k)}$ branches (HBD L2030–2032).
  * In every branch the child group stabilizes a canonical colouring with classes $\le3k/4$, an
    equipartition, or a Johnson scheme on $\ge3k/4$ points. So its alternating sections have degree
    $\le3k/4$, and the height is $O(\log k)$ as in Prop. B.
  * The macro step of $I$ is therefore $2^{O(\log^3k)}$, and $I$ costs
    $(k^t)^{O(\log^3k)}=2^{O(t\log^4k)}=2^{O(L^5)}$.
  * *Gaps.* The pairwise (isomorphism) form of the Design Lemma/Split-or-Johnson inside GNS's
    aggregation is standard but not written out. The bound $k^{O(\log k)}$ for Split-or-Johnson is
    taken from HBD's text.

### 2.5 Corollary D: what this buys, by regime

With $\ell=L^x$, combine Theorem C with the switch "run B–H on the whole input" (cost $2^{O(\ell^3)}$).

* Using (α), the exponent is $\min\{\max(3,6-x),\,2x\}$. [PROVEN]
* Using (β), it is $\min\{\max(3,5-x),\,2x\}$. [SKETCH]

| regime | exponent [PROVEN] | exponent [SKETCH] |
|---|---|---|
| $\ell\ge L^3$ (e.g. $d=\mathrm{polylog}\,n$, $d\le2^{(\log n)^{1/3}}$) | **3** | 3 |
| $L^2\le\ell<L^3$ | $6-x\in(3,4]$ | **3** |
| $L^{5/3}\le\ell<L^2$ | $2x\in[10/3,4)$ | $5-x\in(3,10/3]$ |
| $L^{3/2}<\ell<L^{5/3}$ | $2x\in(3,10/3)$ | $2x$ |
| $\ell\le L^{3/2}$ ($d\ge2^{(\log n)^{2/3}}$) | **3** (B–H) | 3 |
| **worst case over all $d$** | **4** (at $\ell=L^2$) | **10/3** (at $\ell=L^{5/3}$) |

So the unconditional statements are these.

* **Degree-$d$ GI is in $n^{O(\log^3d)}$ whenever $d\le2^{(\log n)^{1/3}}$ or
  $d\ge2^{(\log n)^{2/3}}$, and in $n^{O(\log^4 d)}$ always.** [PROVEN]
* **It is in $n^{O(\log^3 d)}$ whenever $d\le2^{(\log n)^{1/2}}$, and in $n^{O(\log^{10/3}d)}$
  always.** [SKETCH]

In the most-studied regime, $d=\mathrm{polylog}(n)$, the bound is $n^{O((\log\log n)^3)}$. GNS as
written gives $n^{O((\log\log n)^5)}$, and HJ (conditionally) $n^{O(\log\log n)}$.

### 2.6 The other ideas in the brief, and why they do not move the exponent

* **Smaller test sets.** [PROVEN for the lemma, not for the algorithm] GNS Thm 5.8 needs
  $t>2+\log_2d$. The threshold in Babai's Lemma 8.3.1, which Thm 5.8 uses level by level, is tight
  up to an additive constant. Take $k$ odd and $G=E\rtimes A_k$, with $E\le\mathbb F_2^k$ the
  even-weight code (the heart module), acting affinely on $E$. This is a transitive group of degree
  $b=2^{k-1}$ with $G\twoheadrightarrow G/E\cong A_k$, and the point stabilizer $A_k$ maps onto
  $A_k$ although $k=\log_2b+1$. In any case, even with tests of size $O(1)$, the same-domain tree
  can have $d^{\Theta(L)}=2^{\Theta(L^2)}$ nodes (descent factor $d$ per level, $\Theta(L)$
  levels), so $a$ would stay 2. Going lower needs HJ's global accounting (caps $Q_d$, $\sigma$),
  not smaller tests.
* **Smarter aggregation / the canonical subcoset device.** [PROVEN] Lemma T″ of CB cuts the
  comparison exits from $\binom kt^2t!\,n$ to $k^tn$. Both are $2^{\Theta(L^2)}n$, so only the
  constant in $K$ changes.
* **Sharper split-or-Johnson for $\hat\Gamma_d$.** [PROVEN as accounting] This only affects route
  (β). There, the Design Lemma's $k^{t-1}=2^{\Theta(L^2)}$ individualizations already dominate a
  level, so even a $\mathrm{poly}(k)$ Split-or-Johnson leaves $a=3$ for (β).
* **Enumeration-channel classification (w1-structure).** In GNS this channel lives in step 1's
  coset blow-up, i.e. in $e$, not in $K$.
  * Avoiding step 1 is not possible in this architecture. Take the heart-module group above as one
    level of a $\hat\Gamma_k$ group. It has degree $b=2^{k-1}\gg k$ and order
    $2^{k-1}k!/2\le b^{O(\log k)}$, so it is GNS option 1. Every point is unaffected by the giant
    $G\to A_k$, while $G_{(\Omega)}=1$. So no unaffected-stabilizer theorem whose threshold depends
    only on the class parameter ($k$ here, not $b$) can hold for sequences containing such a level.
    It must first be made semi-regular, which is GNS's step 1 at cost $\lvert P\rvert$. [PROVEN]
  * HJ's extra-orbit rule is exactly what handles this example: it is a visible mark, and $\sigma$
    drops by $k$.
* **The black box itself.** [SKETCH] The instance "iso of $(\log d)$-ary structures on $d$
  points" has $\ell'=\log(k^t)\approx L^2$, so it sits in the hard regime of Corollary D. Running a
  GNS-type algorithm on it reproduces the same black box at its top level. The derived structure
  $\mathfrak A'$ built from $I$'s certificates and the original $\mathfrak A$ determine each other
  canonically, so $\mathrm{Aut}(\mathfrak A')=\mathrm{Aut}(\mathfrak A)$. So $X(d)\le2^{O(L^4)}$,
  which would give exponent 3 for all $d$, needs a non-GNS algorithm for $t$-ary structures, or a
  finer analysis of B–H on $S_k^{(t)}$.

### 2.7 Barriers

1. **$c<2$ would beat B–H for general GI.** [PROVEN] Every $n$-vertex graph has maximum degree
   $<n$, so $n^{O(\log^c d)}$ gives GI in $\exp(O(\log^{c+1}n))$. The best published unconditional
   bound is $\exp(O(\log^3n))$ (HBD). HJ's claimed $\exp(O(\log^2n))$ corresponds to $c=1$. So any
   unconditional $c<2$, including $n^{O(\log d\log\log d)}$, would improve the general GI exponent.
2. **The floor of GNS's architecture is $c=3$.** [SKETCH] Per-halving bookkeeping charges
   $K\cdot\log N$. Here $\log N=\Theta(L\ell)$ is forced by step 1 (§2.6) and step 2 (§1.5), and
   $K\ge\log\binom kt=\Omega(L^2)$ while tests have size $\Theta(\log d)$.
   * Charging per *level* instead of per halving would give $c=2$. It fails because window exits
     need not lie inside blocks: a window of size $N/2$ can meet every top block, and then pays for
     the same level again.
   * HJ's caps $c_i$ and $\sigma$ are precisely a level-based ledger.
3. **What $c=2$ would need.** [SPECULATION] Either an unaffected-stabilizer theorem that tolerates
   small primitive levels (to remove $e$), or constant-size tests (to remove the $\binom kt$ exits).
   The latter is HJ's route and needs a hereditary budget, which brings us to Task 3.

---

## 3. Task 3: HJ's Theorem A.9 (hereditary budget)

### 3.1 What is used

* HJ Thm A.9 (L2474–2486): for transitive $G\le\mathrm{Sym}(\Omega)$ of degree $n\ge3$,
  $\sigma(G,\Omega)\le C\log n-B$.
* Here $\sigma$ is the largest total weight $\sum k_i$ of marked steps $H_i\trianglerighteq H_{i+1}$
  along a chain of subgroup restrictions and orbit images. A step is marked when
  $H_i/H_{i+1}\cong\mathrm{Alt}(k_i)$ with $k_i\ge\kappa=64$, $H_{i+1}$ is transitive on the active
  orbit, and the quotient is visible.
* In Theorem R\*'s potential $\Phi_\Lambda=A(\Lambda x+\Lambda\rho+\Lambda\sigma+Q_d)+Bh$,
  $\sigma$ enters only at phase roots (`verify-theorem-R.md` §4.5). The rest of the analysis uses
  only the elementary "marked decrease" (Lemma budget-inheritance).

### 3.2 Re-derivation of HJ's proof

I re-derived the following from HJ L1942–2580 and found them correct.
* **Inheritance and marked decrease.** [PROVEN] Lift chains through preimages, prefix the
  restriction that creates the child, and add the step $G\ge N$, which is visible because
  $G_{(\Omega)}=1$.
* **Simple-quotient localization.** [PROVEN] An iterated commutator lies in
  $\bigcap K_j\le\ker\varphi$, and $S$ is perfect. For the orbit form, use $H$-conjugacy of the
  $U$-orbit kernels.
* **Blocks:** $\sigma(G)\le\sigma(G^{\mathcal B})+\sigma(G_C^C)$. [PROVEN] Let $U$ be the kernel on
  the active blocks.
  * If $\varphi(U)=1$, charge the step to the top. There $U\le N$ gives visibility, and $N$ is
    transitive on the blocks.
  * Otherwise localization kills the slice kernel. Let $T$ be the pointwise kernel of $H_C$ on
    $\Delta\cap C$. Then $[U,T]\le U_{(\Delta\cap C)}$, so $\varphi(T)$ centralizes $S$ and is
    trivial. Also $H=NH_\alpha$ with $H_\alpha\le H_C$ gives $\varphi(H_C)=S$, and $N_C$ is
    transitive on $\Delta\cap C$. Charge the step to the local chain.
* **Cartesian:** $\sigma\le3(s-1)+\sum_i\sigma(A_i)$. [PROVEN]
  * If $\varphi(K_v)=1$: the marked quotients are consecutive quotients of one chain in $\mathrm{Sym}(s)$
    (because $H_{j+1}=N_j$), so $\sum k\le4v_3(s!)\le2(s-1)$.
  * Otherwise the coordinate kernels $\ker(K\to\mathrm{Sym}(C_i))$ intersect in $K_{(\Theta)}$, and
    localization picks a coordinate $i$. With $T_i$ the pointwise kernel of the component action,
    $[K,T_i]$ is killed, so $\varphi(T_i)=1$. Since $K_v$ maps onto $S$ and fixes $v_i$,
    $N\cap H_i$ is transitive on $D_i$.
* **Johnson anchors.** [PROVEN, with one slip noted below]
  * *Case split.* If $\varphi(H_{(T)})=1$, the marks live in a chain in $\mathrm{Sym}(t)$, with
    weight $\le a_0(t-1)$. Otherwise localization over the natural orbits meeting $T$ yields a
    visible mark on an anchored natural orbit $E$, and $N$ is transitive on $E$.
  * *Tokens.* Charge each such mark to a token on $E$. A token keeps its allowance through splits
    by inheritance. A charged orbit does not split at its mark, since $N$ is transitive on $E$.
    The terminal anchor sets are disjoint, so there are $r\le t$ tokens.
  * *Entropy inequality.* $W\le r\log(m/r)+(r-1)$. I re-derived it:
    $F(w,r)-\sum F(w_i,r_i)=r\sum p_i\log(p_i/x_i)+d-1\ge\log(1/z)+\log d\ge\log(w/w_h)$, by the
    log-sum inequality and $x_h\ge z/d$.
  * *Final arithmetic.* It checks, using $\binom mt\ge(m/t)^t$.
  * *The slip.* HJ write $f'(u)\ge\log4-1$ for $f(u)=u\log(m/u)$. This holds for natural logarithms.
    For $\log_2$ the true bound is $\log_2(m/u)-\log_2e\ge0.557$. The step only needs
    $C\cdot(\text{that constant})\ge a_0=3$, which $C\ge128$ satisfies either way. Harmless.
* **The final induction.** [PROVEN] It covers imprimitive groups, product actions, single Johnson
  actions, and the natural giants. For the last case, skip the initial segment where the active
  orbit is still a natural giant (no marks can occur there), then use strong induction or the
  same-degree non-giant cases already proved.
* **The extra-orbit mark** (L2694–2708), the only place the algorithm consumes $\sigma$. [PROVEN]
  Unaffected points give $A_i=N_i(A_i)_a$, so $N_i$ is transitive on $\Delta$. The test
  $\varphi_T((A_i)_{(\Delta)})=1$ gives visibility.
* **Not re-derived: HJ's primitive-valuation lemma** (L2364–2470). It shows $6v_\ell(\lvert P\rvert)\le A_0\log n$
  for affine, almost-simple non-alternating, diagonal and twisted-wreath groups, and for almost
  simple groups with alternating socle that are neither natural nor Johnson actions.
  * The affine case is elementary: $v_\ell(\lvert\mathrm{GL}_D(q)\rvert)\le D\log_\ell q+D/(\ell-1)$
    for $\ell\nmid q$.
  * The rest uses standard CFSG consequences: Lie-type order formulas and minimal degrees (the same
    Cooperstein/Kleidman–Liebeck tables that GNS Lemma 3.7 uses); $\lvert\mathrm{Aut}\,T\rvert\le\lvert T\rvert^2$;
    and Maróti, where Praeger–Saxl also suffices.

**Verdict on the proof of A.9.** [SKETCH] It is correct at reading level, modulo that lemma's
standard CFSG inputs. The residual risk in Theorem R\* is therefore not in A.9's proof. It is in
HJ §§4–7: the use of $\sigma$ inside the local-test/aggregation/auxiliary machinery, and the
Lemma 7.1 induction.

### 3.3 Is $\hat\Gamma_d$ easier? No. A weak form is free

$\hat\Gamma_d$ restricts the alternating factors to degree $\le d$. It does not simplify the
CFSG-based valuation lemma: Lie-type socles of rank $\approx\log d$ are allowed, and their
valuations need the order formulas. What $\hat\Gamma_d$ does offer is GNS Thm 3.13, which is
refereed (SICOMP 2023).

**Theorem E (weak hereditary budget for $\hat\Gamma_d$).** [SKETCH] There is an absolute $C_0$ such
that every transitive $G\in\hat\Gamma_d$ of degree $n\ge3$ satisfies
$$\sigma(G,\Omega)\le C_L\log n-B_L,\qquad C_L:=C_0(c_1L+c_2),\ B_L:=C_L+6.$$

*Proof.* Run HJ's induction over transitive $\hat\Gamma_d$ groups (not over $\mathrm{Sym}(n)$),
with $C\to C_L$.
* **Imprimitive.** Use the block lemma: $F(a)+F(b)\le F(ab)$ for $F=C_L\log-B_L$.
* **Primitive, GNS option 1.** Here $\lvert P\rvert\le b^{c_1L+c_2}$, so
  $\sigma\le6\log_3\lvert P\rvert\le C_L\log b-B_L$ for $b\ge3$. This uses $\log b-1\ge0.37\log b$.
* **Primitive, GNS option 2.** By GNS's proof (Lemma 3.9), $G\le P_0\wr K$ in product action with
  almost simple components whose socle is $A_m^{(t)}$.
  * If $k\ge2$, use the Cartesian lemma. It needs $3(s-1)\le(s-1)B_L$, and its components are
    $\hat\Gamma_d$ groups of smaller degree.
  * If $k=1$ and $t\ge2$, use the Johnson anchor lemma. Its constant inequalities hold for any
    $C\ge128$ with $B=C+6$, and it needs only the natural bounds for degrees $r\le m<n$.
* **Natural giants** ($n\le d$). Use HJ's final step.

The gap: this inherits the reading-level status of HJ's elementary lemmas (§3.2), and the details
of option 2 come from GNS's proof rather than its statement. ∎

**Corollary F.** [CONDITIONAL: HJ §§4–7 and its Lemma 7.1 framework, the (M′) dispatcher and the
(H2) regrouping, exactly as in the red-team's sign-off (`redteam-theorem-R.md` §10), **but not HJ's
CFSG primitive-valuation lemma**] String isomorphism for $\hat\Gamma_d$ on $N$ points takes
$\exp(O(\log N\cdot\log^2d))$ time, so degree-$d$ GI is in $n^{O(\log^2d)}$.

*Proof.* Use Theorem E at each phase root in place of A.9. The root potential becomes
$A\Lambda\sigma=O(L\cdot L\log N)$. Every drop in the table of `verify-theorem-R.md` §4.3 is
unchanged; the $\sigma$-row uses only the marked decrease. In phases with $d>N^\alpha$, HJ's
verbatim potential gives $\exp(O(L\log^2N))\le\exp(O(L^2\log N/\alpha))$. ∎

### 3.4 What $n^{O(\log d)}$ would still need

An independent proof of the strong A.9 for $\hat\Gamma_d$ would amount to HJ's own proof, i.e. the
elementary lemmas (§3.2) plus the valuation lemma. Even with it, Theorem R\* still needs all of the
following.
* **HJ §§4–7:**
  * the constant-size endpoint procedure and lockstep comparisons;
  * the aggregation/Design interface with $q^{O(\kappa)}$ branches;
  * Lemma large-symmetry and Lemma exact-configuration;
  * the first-bipartite-graph cap payment (eq. main-cap-payment);
  * the Lemma 7.1 potential induction and the phase recurrence.
* **The repository's additions:** the dispatcher (M′) with structural option-2 recognition; the
  (H2) regrouping; and the $\Lambda$-version of the table.
* **Published inputs:** GNS Thm 3.13 and Lemma 4.4; BCP Lemma 2.2 (or Maróti Cor. 1.5); the
  Luks/Babai–Luks reduction.

With Theorem E in place of A.9, these same items give exponent 2 (Corollary F). The CFSG valuation
lemma is worth exactly one factor of $\log d$.

---

## 4. Task 4: novelty

| source | what it says about the exponent | how checked |
|---|---|---|
| GNS arXiv v1–v3, FOCS'18 | $n^{O((\log d)^c)}$, $c$ unspecified; height $O(\log^2d)$, $2^{O(\log^3d)}$ nodes; Thm 4.6 as $n^{O(\log^2d)}$ | full v3 source |
| Neuen, ICALP'20 / TALG'22 (2002.06997) | the same Lemma 7.2 analysis verbatim ($k'\le k-k/(3\log k)$, L2720–2724) | full source |
| Grohe–Neuen survey (2011.01366, 2021) | Thm 4.16: normalization with $\lvert\mathrm{Br}\rvert\le n^{O(\log d)}$ [GNS, Neuen thesis]; Thm 4.18: $n^{\mathrm{polylog}(d)}$; says GNS use Babai as a black box | full text |
| Neuen, Comput. Sci. Rev. 60 (2026) | Thm 4.6, Cor. 4.7: $n^{\mathrm{polylog}(d)}$ | full text |
| HJ (2611.01399) | cites GNS's $n^{\mathrm{polylog}\,d}$; no $\hat\Gamma_d$ corollary | full source |
| web searches (2026-11-05): "$n^{O(\log^2d)}$" bounded degree, composition width with an improved exponent, 2024–2026, Neuen thesis | nothing beyond the above | standard + extended |
| Neuen's thesis (RWTH 2019) | **not retrieved**: RWTH and CORE give no PDF to scripted access; not bypassed | — |

**Status.**
* Explicit values $c=5$ (GNS as written) and $c=4$ (with the known count): **not stated anywhere
  found**. It is routine bookkeeping.
* The multiplicative potential (Lemma A + Prop. B), the black-box regime analysis
  (Corollary D, giving 3 for $\log n\ge\log^3d$, 4 always and $10/3$ [SKETCH]), and Theorem E with
  Corollary F: **not found**.
* Main risk: Neuen's thesis, which re-derives GNS and might contain a sharper potential. Its author's
  2021 and 2026 surveys still state only $\mathrm{polylog}(d)$.

---

## 5. Where attempts broke

* **Charging per level instead of per halving** (aiming at $c=2$): window exits need not lie
  inside blocks (§2.7).
* **Self-reducing the black box** (calling the algorithm recursively on the $k^t$-element
  structure): this is a genuine regress (§2.6). When $k^t\le N/2$ the call is an ordinary exit, and
  that is why $c=3$ holds for $\ell\ge L^2$. Below that, every bound I could set up compounded,
  e.g. $X(k)\le2^{O(L^4)}X(3k/4)$.
* **The β-route in the outer algorithm:** per-level cost $k^{t-1}k^{O(\log k)}=2^{\Theta(L^2)}$ over
  $\Theta(L)$ levels gives $a=3$, so $n^{O(L^4)}$. No gain.
* **A Γ̂_d-specific strong budget via GNS 3.13:** option 1 gives only order bounds
  $b^{O(\log d)}$. Valuation arguments need the structure that HJ's CFSG lemma supplies.

## 6. Leads

1. **$X(d)\le2^{O(\log^4d)}$** for isomorphism of $(\log d)$-ary structures on $d$ points. This
   would give exponent 3 for all $d$, unconditionally. Candidates: a direct analysis of B–H on
   $S_k^{(t)}$, where the giant is reduced once over $O(\log k)$ rounds; or a canonical form for
   case-(v) structures that exploits $\mathrm{Aut}(\mathfrak A)_T^T\le M_T$ for every $t$-set $T$.
2. **Prove HJ's valuation lemma in the form needed** (or check it against the literature). This
   would turn Corollary F's hypothesis into "HJ §§4–7 only" for exponent 1 as well.
3. **An unaffected-stabilizer theorem for towers with "small primitive" levels**, excluding
   heart-module-type levels by a budget. This would remove $e$ and give exponent 2 within GNS's
   architecture.

---

## 7. Ledger

**Proven here.**
* Theorem 1, Prop. 2, Corollary 3.
* Lemma A (CFSG-free: Bochert or Praeger–Saxl).
* Prop. B (with the CB §7.3 fix).
* Theorem C, the (α) half of Corollary D, and barrier 1.
* The tightness of Babai's Lemma 8.3.1 ($E\rtimes A_k$), and the failure of Thm 5.8 on heart-module
  levels.
* Re-derivations of HJ's inheritance, localization, block, Cartesian and Johnson-anchor lemmas, and
  of the extra-orbit mark.

**Sketched.**
* The β-variant ($X\le2^{O(L^5)}$) and the β half of Corollary D ($10/3$).
* Theorem E.
* The architectural floor $c=3$, and the tightness of the bookkeeping (§1.5).

**Trusted (published).**
* GNS (SICOMP 2023), including Thms 3.13, 4.3, 4.6, 5.8, Lemmas 6.2–6.9, 7.1, Thm 8.1.
* B–H's $\exp(O(\log^3m))$ (Helfgott, Astérisque 2019 / arXiv:1710.04574).
* Babai's Design Lemma and Split-or-Johnson (arXiv:1512.03547), with HBD's cost statements.
* Bochert's theorem; Praeger–Saxl 1980.
* Miller's reduction from structures to graphs.
* CB Lemma 7.0 and the §7.3 fix, which are repository results already red-teamed
  (`docs/redteam-gns-lemma72.md`).

**Conditional.** Corollary F, under HJ §§4–7 as listed in §3.4.

**Not checked.**
* HJ's primitive-valuation lemma.
* Neuen's thesis.
* No machine check of anything.
