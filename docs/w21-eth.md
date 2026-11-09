# w21: "The Exponential Time Hypothesis is False" and the GI campaign

Branch `w21-eth`, 2026-11-08. Preprint: OpenAI Math Release, dated 17 Oct, revised 25 Oct 2026 (67 pp).
Read from the extracted text in the session scratchpad; not modified. Code and log: `docs/w21-eth-code/`.

**Labels.** [PROVEN] complete argument here plus cited theorems. [SKETCH] gaps listed.
[CONDITIONAL: X] proven under hypothesis X. [SPECULATION] opinion.

---

## 0. Summary

**Verdict on the preprint: I found no flaw in what I checked.** That covers the bounded-occurrence core
(Secs. 2-4) and the Sec. 5 parity lift. It does not cover the sharper exponent of Appendix D, the bit-size
accounting, or a full line-by-line reading of the sparsification appendix. This is an adversarial read and a
small-case test by one reviewer, not a verification. See §A.5.

**Transfer to GI: none found.** The method is a sum over Boolean witness bits, and it needs three things at
once: few witness bits, fixed-width (or very sparse) constraints, and few occurrences per variable. Every
GI-type problem in the campaign fails at least one (§B).

**Docs.** The "ETH barrier" statements need one change: re-base them on the hypothesis "no $f(k)n^{o(k)}$
algorithm for $k$-Clique". Nothing else in the campaign depends on ETH (§B.3).

| Item | Status |
|---|---|
| Sec. 4 construction ($M_0$, $C^B$, rows $P_u$, Lemmas 4.1-4.3) | checked exactly for $(r,Q,R)$ with $D\le 256$; re-derived by hand; no error |
| Separation identity (Lemma 3.2), Taylor identity (Lemma 3.3 / eq. 3.13), Hermite recovery, $H(0)=\#F$ | tested exactly against brute force, 7 instance families |
| Parameter balance (2.19), (4.17) | arithmetic re-derived; asymptotic only, cannot be tested |
| Sec. 5 lift (Lemmas 5.1, 5.2, $A_\ell$-valued pipeline) | tested exactly on small systems |
| Sec. 6, Appendix A (sparsification), Appendix B | read and partly re-derived; not run |
| Appendix D (tensor contraction) | read; only Lemma D.4, (D.9), (D.10) tested; the recursion was not |
| Lean formalizations | exist per public repositories; not run (campaign rule) and not read |
| Transfer to GI, TI, AGL, TreeCI | **no**, with precise break points (§B.2) |

---

## Part A. Does the core hold up?

### A.1 What the proof actually needs

The refutation of ETH needs only Sec. 2.2-2.8 (or Secs. 3-6). Appendix D improves the exponent and is not
needed for $2^{o(n)}$. The argument has this skeleton:

1. **Replacement forms.** Replace each clause input by $\langle P_{e,v}(T),x\rangle$ with $P_{e,v}(0)=\delta_v$
   and $\deg_T P\le R-1$. Then $H(T)=\sum_x\prod_e\Phi_e(\langle P(T),x\rangle)$ has $H(0)=\#F$ and
   $\deg H\le M(R-1)$, where $M=\sum_e|I_e|\le 3n$.
2. **Separation at $t\in[Q]$.** Given the group of each variable and clause, every form depends only on the
   clause's group and a few integer measurements of the other groups (Def. 2.1, Lemma 3.2).
3. **Taylor data.** Near $t$ the formal input $X$ is separated from the summation variable $x$. The coefficient
   of $z^j$ has $X$-degree $\le j$, so inclusion-exclusion over $U\subseteq E$, $|E|\le q$ recovers it (Lemma 3.3).
4. **Hermite interpolation** of $H$ from $QJ>\deg H$ jet coefficients gives $H(0)$.
5. **The auxiliary matrix** $M_0=V_0f(W_0)$ on $B=([r]^2)^Q$. Here $V_0$ swaps all pairs and $f$ interpolates
   $(-1)^j$ on $R$ consecutive integers around $Q(r-1)/(2r)$. Then $I-M_0$ has rank $\le D\Pr[W\notin I]$, and
   $M_0[u,y]\ne0$ only when $a_y$ and $d_u$ agree in all but $\le R-1$ positions.
6. **Cost:** $\sum_{|E|\le q}2^{|E|}\binom{n}{|E|}\cdot(2D+1)^{2\tau n}\cdot2^{2n/r}$.

### A.2 Targeted re-derivation (by hand)

I went through the places a false proof would most likely break. No error found in any of them.

* **Rank bound (Lemma 4.1).** $\Pi_s$ commute and square to $I$; the product basis $\psi=\bigotimes_s\psi_s$
  diagonalizes them; $V_0\psi=(-1)^j\psi$, $W_0\psi=j\psi$, so $M_0\psi=(-1)^jf(j)\psi$. Choosing $f(j)=(-1)^j$
  on $I$ fixes all $\psi$ with $j\in I$. So $I-M_0$ vanishes on the span of those, and $C^B$ can be the
  remaining $\psi$. Correct. The number of rows equals $D\Pr[W\notin I]$ with
  $W\sim\mathrm{Bin}(Q,\frac{r-1}{2r})$.
* **Support (Lemma 4.2).** $V_0\Pi_J=\Pi_{[Q]\setminus J}$ for $|J|\le R-1$; the $(u,y)$ entry is nonzero only
  if $y$ is $u$ with positions outside $J$ swapped, hence $a_y(s)=d_u(s)$ off $J$. Correct.
* **Row properties (Lemma 4.3).** $P_u(0)=\delta_u$; degree $\le R-1$; at $T=t$ a surviving term needs
  $a_y(t)=d_u(t)$; $(I-M_0)$ rows lie in the row space of $C^B$, and restricting to a group keeps this.
  Correct.
* **Transfer to variables (Sec. 4.5).** The $h$ copies, the shared Boolean values, and the group restriction of
  each measurement give rows of absolute sum $\le D$ and at most $2\tau n$ rows in total. Correct.
* **Balancing (Lemma 4.5).** $\mathbb E\Phi\le M(b+w)$: only pairs of incidences that share a factor or
  variable are dependent, at most $M(b+w)$ of them. Conditional expectation then yields both bounds. Correct.
* **Degree bound.** $\deg_T H\le M(R-1)$; the paper uses the looser $MR$. With the multilinear $\Phi_e$ the
  bound holds per occurrence. Correct.
* **Parity lift (Lemmas 5.1, 5.2).** $p_\ell$ is the classic Beigel-Tarui polynomial; the truncation mod
  $V^\ell$ loses only terms divisible by $2^\ell$, across factors. Correct, and it is what keeps the input
  degree $O(n)$ at $m_{test}=O(n)$.
* **Greedy tests (Sec. 6).** The expander-code parameter arithmetic ($P$, $D_0$, row counts, mixing) and the
  $3/4$ decrease per round re-derive. The $(2m)^P=2^{\mathrm{polylog}}$ candidate enumeration is subexponential.
* **Sec. 2.8 (weaker route).** Sparsification to $B=(\log n)^{O_k(1)}$ occurrences plus Tovey copying and
  (2.12). Standard, and it is enough for $2^{o(n)}$.

The one structural observation worth recording: Secs. 2-4 use nothing but linear algebra and polynomial
interpolation. There is no hidden black box. If it is wrong, the error must be in an elementary step. I did not
find one, and the tests below did not find one.

### A.3 Exact tests on small cases

`docs/w21-eth-code/eth_core.py` implements everything over `Fraction`. `test_core.py`, `check_lift.py` and
`check_appendix_d.py` run the tests. Full log: `results.txt`.

**Exercised, all passing, exact rationals:**

1. Remark 4.4's worked example ($r=Q=R=2$): the row is $\zeta_0-\frac{T}{2}\zeta_1-T\zeta_2$ exactly.
2. Matrix checks for $(r,Q,R)\in\{(2,2,2),(2,3,2),(3,2,2),(2,4,2),(2,4,3)\}$: eigen-relation (sampled for
   $D>81$), support (Lemma 4.2), and rank$(I-M_0)$ equal to the number of exceptional rows, exactly, for
   $D\le 81$.
3. Lemma 4.3 at the array level (exact row-space membership): 0 failures in 480 checks across three
   parameter sets (all 16 and 64 labels for $r=2$; a sample of 64 of the 81 labels for $(3,2,2)$).
4. Pipeline on bounded-occurrence formulas, random schedules, 7 instance families, $n\le7$: $H(0)=\#F$,
   $\deg_TH\le M(R-1)$, Def. 3.1(4) on actual variables, Lemma 3.2 (group sums over achieved measurement
   tuples) equals brute-force $H(t)$, eq. (3.13) equals brute-force Taylor coefficients, and Hermite recovery
   returns $\#F$.
5. The truncation $|E|\le q$ is exercised with $q<n$ (`dense-C`, $n=7$, $q=4$): the minimal sufficient
   truncation is 3 (seed 0) and 1 (seed 1), never above $q$.
6. Lemmas 5.1 and 5.2 ($\ell\le 11$, 4000 random trials); degree of the truncated product $\le m+2(\ell-1)$; the
   $A_\ell=\mathbb Q[V]/(V^\ell)$ pipeline on small $\mathbb F_2$ systems returns the exact number of common zeros.
7. Appendix D: $W(0)=I$ and 2-adic integrality of $W(t+\alpha z)$ (Lemma D.4, $a\le3$); (D.9) as an identity
   over $\mathbb Q$; (D.10) as a valuation identity and bound.

**Deliberately broken variants (the test can fail).** Each is a single defect in the construction or recovery.

| Defect | Array-level (Lemma 4.3 / matrix checks) | Instance-level, 6 instances |
|---|---|---|
| wrong interpolation value (`f_wrong`) | caught, 16-96 failures | caught 4/6 |
| $V_0$ omitted (`no_V0`) | caught (eigen and support) | 5/6 |
| one measurement row dropped (`C_drop`) | caught, 8 failures | 2/6 |
| all measurements dropped (`C_empty`) | caught | 6/6 |
| vanishing factor removed from $\varphi$ (`phi_drop`) | caught | 4/6 |
| clause assigned to two groups (`sigma_split`) | n/a (instance-level) | 4/6 |
| measurements coarsened mod 2 (`measure_mod2`) | n/a | 1/6 |
| restoration at $T=0$ removed (`no_restore`) | n/a | 6/6 |
| Hermite with $QJ\le\deg H$ (`J_short`) | n/a | 6/6 |
| $|E|$ truncated too early (`E_short`) | n/a | 1/6 at $q\ge n$; 2/2 at $q<n$ |

"n/a" means the defect does not exist at array level. Instance-level misses are expected at this size: with
small $n$ the auxiliary array is sparsely filled, so a dropped row or a mild coarsening often touches no
occupied coordinate. That is why the array-level test exists. The instance-level test has weak power against
mild defects (`measure_mod2` especially), and its "1/6" should not be read as much of a confirmation.

**What the tests cannot reach (asymptotics only):**

* The whole parameter regime. With the paper's constants, $r\ge2$, $R\ge32$, $6R\le Q$ first hold at
  $\lambda=\lceil\log_2n\rceil\approx2^{33.4}$, and the exponent (3.16) first drops below 1 at
  $\lambda\approx2^{36.1}$, that is, $n\approx2^{7\times10^{10}}$ (`check_params.py`). The algorithm is galactic, and
  $R\ll Q$ cannot be exercised at any computable size. The tests use $R\approx Q$ and fixed tiny $r$.
* Lemma 4.5's balance bounds at scale ($h$ here is whatever random schedules give).
* The deterministic searches of Sec. 6 and Appendix B's bit-size bounds. Not run.
* The recursion of Appendix D (D.12)-(D.16), and the mode-count bound (D.15). Not tested.

### A.4 Reported elsewhere (searched 2026-11-08)

No source I could read reports an error or erratum in either proof.

* OpenAI's PDF and README are in `github.com/openai/math`, labelled preprint. Their scope note says Lean
  proves exact counting for canonically encoded $k$-CNF with exponent $n(\log\log n)^2/\sqrt{\log n}$. That is
  **weaker than the manuscript's** $n\log\log n/\sqrt{\log n}$, which it does not claim to formalize.
  [Scope note](https://github.com/openai/math/blob/main/lean/docs/378.md)
* Anthropic published a separate claim with a Lean formalization, `ETHIsFalse`, for #3-SAT in
  $2^{O(n\log\log n/\sqrt{\log n})}$, by tensor networks. Its README says the result is purely asymptotic and "no
  machine checks that this file says what the paper says."
  [README](https://github.com/anthropics/formal-math/tree/main/eth)
  This review was written by a Claude model, so its reading of that claim is not independent of Anthropic.
* An open examination is organized by Impagliazzo, Paturi and R. Williams. Their open letter says their
  involvement "should not be taken as certification of the claim", and as of late October it was ongoing.
  [Williams](https://x.com/rrwilliams/status/2114833319431209352),
  [Xenospectrum](https://xenospectrum.com/en/openai-exponential-time-hypothesis-false-claim/),
  [lilting.ch](https://lilting.ch/en/articles/eth-exponential-time-hypothesis-refuted-openai-anthropic)
* Wikipedia (November 2026) describes both claims as unverified, noting OpenAI's has not been peer-reviewed.
  [ETH](https://en.wikipedia.org/wiki/Exponential_time_hypothesis)
  A tracker found no completed independent verdict as of 26 October.
  [Kingy](https://kingy.ai/mathematics-science-breakthrough-tracker/records/cs-exponential-time-hypothesis-refutation-openai-2026/)
* Not read: the science.org article (HTTP 403, not bypassed) and one member-only article (not attempted).
* One claimed gap concerns the Lean scope and the sharper exponent, not an error in the proof.
  [popularai](https://www.popularai.org/p/openai-exponential-time-hypothesis-proof)

Two formalizations of closely related statements, if they say what they claim, would be much stronger evidence
than my checks. I did not run or read them.

### A.5 Verdict

**Found nothing wrong in what I checked.** Specifically:

* **Covered by re-derivation and exact small-case tests:** Lemmas 3.2, 3.3 and Prop. 3.4's identity; Def. 3.1 for
  the construction; Lemmas 4.1-4.3; Lemma 4.5's expectation bound; Lemma 5.1, 5.2; recovery of $H(0)=\#F$.
* **Covered by re-derivation only:** the parameter arithmetic of (2.19), (4.17), Lemma 4.8, the running-time
  bound (2.11)-(2.12), Sec. 2.8's reduction, Sec. 5.5, Sec. 6.
* **Read, not independently re-derived in full:** Appendix A's insertion accounting, Appendix B's bit sizes.
* **Read, with only three local identities tested:** Appendix D. Its recursion is the only support for the sharper
  exponent in Theorem 1.1.

The refutation of ETH itself needs only Sec. 2.8's route (Secs. 2-4, sparsification, Tovey copying). So the core
of the claim sits inside the part I checked best. My checks cannot exclude a subtle error in the sparsification
bookkeeping or at parameter scales no test can reach.

[SPECULATION] The argument looks correct to me. It would be prudent to wait for the expert examination before
any campaign document states ETH is false as fact.

---

## Part B. Relevance to the campaign

Convention: the "current bound" below is $n^{O(\log n)}=2^{O(\log^2n)}$, as in `docs/moonshot-theory.md`. That is
the unrefereed Hajiaghayi-JafariRaviz preprint (arXiv:2611.01399; see `docs/verify-theorem-R.md`). The refereed
state of the art remains Babai/Helfgott $2^{O(\log^3n)}$. The conclusions below hold against either.

### B.1 Direct use: no

**[PROVEN]** A polynomial-time reduction from GI to SAT with $N(n)$ variables gives GI in $2^{N}\mathrm{poly}(n)$ by
brute force. Theorem 1.1 replaces this by $2^{O(N\log\log N/\sqrt{\log N})}$ when the clause width is fixed.
So it beats $2^{\log^2n}$ only in the window
$$
N\ \lesssim\ \log^2 n\cdot\frac{\sqrt{\log\log n}}{\log\log\log n}.
$$
Below $N\approx\log^2n$ the reduction would already beat the bound by brute force. This is a window of
$\sqrt{\log\log n}$ around $\log^2n$, and it requires a $\log^2 n$-variable fixed-width encoding of GI, which
nobody has.

**Correction to the framing "at least $n\log n$ variables":** that is a statement about encodings whose
assignments include every bijection, not a lower bound on reductions. For the natural encodings the true
fixed-width number is worse:

* Unary ($x_{uv}$, width 2): $N=n^2$. Then $2^{n^2/\sqrt{\log n}}$ is *worse than* $n!$.
* Binary (witness $n\log n$ bits): the constraint "$(\sigma(u),\sigma(v))\in E(H)$" has width $2\lceil\log n\rceil$, not
  fixed. Tseitin auxiliaries restore fixed width at the cost of at least the shared decoder, about $n$ auxiliary
  variables per vertex, so $N\approx n^2$ again. [SKETCH: I know no fixed-width encoding with $o(n^2)$ variables.]

Either way the exponent is far above $\log^2n$. Confirmed.

**Why fixed width is not cosmetic. [PROVEN from Prop. 3.4 and Lemma 6.3's $B$]** The quantities that matter are
the total incidence $M=\sum_f|I_f|$ and the polynomial degree $d$; both must be $N\,\mathrm{polylog}\,N$. A clause
polynomial has degree equal to its width, so $d=\sum_e|I_e|$. Sparsification's occurrence bound
$B=O_k((\sigma^{-1}\log(2/\sigma))^{k-1})$ is exponential in the width $k$, and Sec. 2.8 turns each width-$k$ clause into
$O(k)$ auxiliary variables. The permutation-style encodings have at least one constraint per vertex pair, so
$M\gtrsim t^2\log t$ on $N=t\log t$ witness bits, and $q=dR/Q\gg N$ even at base cases of size $t=\mathrm{polylog}\,n$.
So no polylog-size base case inside Babai's or Luks's recursion helps either.

**FPT-style factors.** [SKETCH] The factors $2^{O(k)}$ and $f(d)$ in our docs are DP over subsets or orbit
objects (Schweitzer-Wiebking, BCQ, Luks 1999; `docs/w1-structure.md` L315-L374) or enumeration of $S_b$ or
$\mathrm{GL}$. None is a Boolean sum with fixed-width local constraints: the constraints read whole group
elements. Even in the best case, the theorem would improve $f$ by a factor of $\sqrt{\log}$ in its exponent. It
cannot turn XP into FPT.

**XP witnesses.** A brute-force $n^b$ over $b$-tuples has $b\log n$ witness bits. If its predicate were fixed-width
in bits, Theorem 1.1 would give $n^{o(b)}$. But the predicates compare whole vertex names, so they read
$\Theta(\log n)$ bits per vertex. This is exactly the gap between mini-SAT and W[1] (see §B.3).

### B.2 The technique: where it breaks

The machinery is more general than SAT. Prop. 3.4 counts $Z=\sum_{x\in\{0,1\}^n}\prod_f\Phi_f(x_{I_f})$ over a commutative
$\mathbb Q$-algebra, in terms of $n$ (witness bits), $M=\sum_f|I_f|$, $b$ (max occurrences), $w$ (max scope), and $d$ (total
degree).

**Proposition (feasibility bound). [PROVEN]** If Lemma 4.7's hypotheses hold with $R<Q$, then
$M\ge 32\,b^2(b+w)$.

*Proof.* $I$ omits at least two integers of $\{0,\dots,Q\}$, hence an endpoint. So
$\Pr[W\notin I]\ge\min(p^Q,(1-p)^Q)\ge 4^{-Q}$ with $p=\frac{r-1}{2r}\in[\frac14,\frac12)$. Lemma 4.7 needs
$\Pr[W\notin I]\le\tau/(rb)\le 1/(4b)$, so $4^Q\ge 4b$. Since $D=r^{2Q}\ge 4^{Q}$, we get $D\ge 4b$. Then
$M\ge2(b+w)D^2\ge32b^2(b+w)$. ∎

So when variables occur evenly, $M\approx nb$, the construction needs $b\lesssim\sqrt{n/32}$. For a useful bound it
needs far more: $R\ll Q$ with $Q=O(\log M)$ forces $\log b=o(\log M)$, and Lemma 4.8 takes $b=\mathrm{polylog}(n)$.

The degree condition is separate. $C_q$ is useful only if $q=\lfloor dR/Q\rfloor<n$, and $D\le 2M$ caps $Q$ at
$O(\log M)$. With $R\ge\sqrt{Q}$ up to log factors, this gives $d\lesssim n\sqrt{\log n}$ at best. [SKETCH: uses
binomial anti-concentration for the lower bound on $R$.]

**Candidates.** In each, the check is against the actual instance (`check_transfer.py`, exact binomial tails).

* **Affine equivalence, $f(Ax+b)=g(x)$.** $n=k^2+k$ witness bits, but one factor per $x\in\mathbb F_2^k$: $N=2^k$ factors.
  Each reads about $k^2/2$ bits, so $b\approx N/2$ and $M\approx Nk^2/2$. **Fails the feasibility bound by far**
  ($32(N/2)^3\gg Nk^2/2$). Its degree is also $d\ge Nk$, so $q\gg n$. Introducing auxiliaries $y^{(x)}=Ax+b$ restores
  fixed width with $Nk$ bits, so the exponent is about $Nk/\sqrt{\log N}$, against the target $k^2/4$.
* **Tensor isomorphism ($k\times k\times k$, $\mathbb F_2$).** $n=3k^2$. Direct: $k^3$ equations of degree 3, each variable
  in $k^2$ of them, so $M=3k^4$, $b=k^2$: fails the bound. Applying Sec. 6's parity compression, optimistically
  with test length 1, gives $b\approx3k$, $M\approx9k^3$: **still fails the bound.** Tovey-style copying restores
  $b=3$ with $n\approx 9k^3$ bits, so the exponent is at least about $k^3/\sqrt{\log k}$, above brute force
  $2^{3k^2}$. The break is the occurrence count of $\sqrt n$, not the width.
* **TreeCI.** A witness is one local permutation per node, $\Theta(N\log b)$ bits, with $N$ leaves. The exponent would be
  $N\log b/\sqrt{\log N}$, against the target $N^{\mathrm{polylog}\,b}=2^{\mathrm{polylog}(b)\log N}$. The witness is
  exponentially larger than the target exponent. Fixed $b$ has fixed width, but Luks already gives
  polynomial time there.
* **Counting automorphisms / isomorphisms.** Poly-time equivalent to decision (Mathon 1979). The interpolation
  offers nothing here, because the difficulty is not counting versus deciding.

**Appendix D does not rescue these. [PROVEN for the rectangle encoding below; SKETCH otherwise]** Theorem D.1
counts wires $s$ and allows degree up to $s^{9/10}$. A variable read by many factors still costs one wire per
reader. For TI, if a vertex reads $\alpha,\beta,\gamma$ rows it holds at most $\alpha\beta\gamma$ of the equations, so a
degree cap $\Delta$ forces $k^3\le(\Delta/3k)^2\cdot s/(3k)$, that is, $s\ge27k^6/\Delta^2$. With $\Delta\le s^{0.9}$
this gives $s=\Omega(k^{2.14})$, exponent $\Omega(k^{2.14}/\sqrt{\log k})$, again above brute force. For AGL,
the all-ones $x$ forces a vertex reading all $k^2$ bits, so $s\ge k^{2.22}$.

**Control.** Bounded-occurrence 3-SAT passes the feasibility bound, as it must. At computable sizes its exponent
is still above 1 (`results.txt`), consistent with the galactic threshold of §A.3. So the table's "feasible but
$\ge1$" means the same as for the paper's own target. The meaningful difference is "direct: infeasible at every
size" versus "after copying: feasible, but with the wrong $n$".

**[SPECULATION]** The idea of "low-rank plus restricted-support" for the matrix on $[r]^Q\times[r]^Q$ is reminiscent of two
trees sharing a leaf set, as in tanglegrams. I see no way to turn that resemblance into a method: tanglegrams
are not a Boolean sum-product with near-linear degree.

### B.3 Effect on existing claims

**What ETH was used for.** One argument, stated several times: "W[1]-hardness of degree-$d$ GI / TreeCI / tanglegrams
would need parameter blow-up $g(k)\ge2^{k^{\Omega(1)}}$." Its structure:

1. **[PROVEN mod GNS, unconditional]** An fpt-reduction from $k$-Clique with parameter $g(k)$ gives $k$-Clique in
   $f(k)n^{\mathrm{polylog}\,g(k)}$.
2. **[CONDITIONAL: ETH]** $k$-Clique has no $f(k)n^{o(k)}$ algorithm (Chen et al.).
3. Hence the blow-up.

**What survives if ETH fails.** Step 1 stands. Step 2 is an implication *from* ETH, and it is not reversed: Chen et al.
give "$n^{o(k)}$ Clique $\Rightarrow$ ETH false", not the converse. So the statement remains true under the hypothesis

> **CLIQUE-LB:** $k$-Clique has no $f(k)n^{o(k)}$ algorithm.

ETH implies CLIQUE-LB. CLIQUE-LB is not known to imply ETH. If ETH is false, CLIQUE-LB is neither implied nor refuted.
The barrier was never about ETH itself, only about Clique.

**Does this failure say anything about Clique or W[1]-hardness? No. [PROVEN for the encoding route below;
SKETCH otherwise]**

* The standard $k$-Clique encoding has $n'=k\log N$ variables, clause width $2\log N$, and up to one clause per non-edge
  per pair of positions: $M\gtrsim k^2N^2\log N\gg n'$ on dense instances. So the incidence and degree conditions of §B.1
  and §B.2 fail, and Theorem 1.1 (fixed width only) gives nothing.
* The unary encoding has $kN$ variables: $2^{kN/\sqrt{\log}}$ is useless against $N^k$.
* The classical structure says the same [standard: Downey et al., Flum-Grohe]: $\mathrm{FPT}\subseteq\mathrm{M}[1]\subseteq\mathrm{W}[1]$, and
  $\mathrm{M}[1]=\mathrm{FPT}$ iff ETH fails. So, [CONDITIONAL: the preprint is correct], $\mathrm{M}[1]=\mathrm{FPT}$, with
  the collapse happening below W[1]. $\mathrm{W}[1]\ne\mathrm{FPT}$ is untouched. Mini-3-SAT ($k\log N$ variables, fixed
  width) becomes FPT; Clique, whose encoding has unbounded width, does not follow.

So a W[1]-hardness proof for these problems remains as hard to imagine as before. What changes is only that the
stated hypothesis must be CLIQUE-LB instead of ETH.

**The $R^*$ strengthening** ($g(k)\ge2^{\Omega(k)}$) is conditional on the same hypothesis, plus HJ.

**Changes the docs need (not made here).**

| File | Line(s) | Change |
|---|---|---|
| `docs/w1-fpt.md` | 128-130 | "contradicting ETH" → "contradicting CLIQUE-LB (implied by ETH)". Label [CONDITIONAL: CLIQUE-LB]. |
| `docs/w2-coset.md` | 49 | "(under ETH)" → "(under CLIQUE-LB)" |
| `docs/w2-coset.md` | 553-560 | Rename "ETH barrier" to "Clique-lower-bound barrier". "ETH forbids" → "CLIQUE-LB forbids". |
| `docs/w2-coset.md` | 739 | Label [CONDITIONAL: CLIQUE-LB, mod GNS]. |
| `docs/w4-t2.md` | 38, 489, 630 | Same rename and hypothesis. |
| `docs/w6-tanglegram.md` | 29, 269-270 | Same. |
| `docs/redteam-w1-fpt.md` | 38, 360, 375-385, 465 | Note: the argument is sound, its hypothesis is CLIQUE-LB, and the "ETH" line is one implication of it. |
| `docs/overnight-log.md` | 161 | "ETH forces" → "CLIQUE-LB forces (implied by ETH)". |

I recommend these changes regardless of the preprint's fate: CLIQUE-LB is the hypothesis actually used, and ETH was only a
stronger, more familiar sufficient condition. `docs/w17-affine.md`'s hypothesis 4-TI$_2$, the $n^{O(\log n)}$ barriers in
`docs/moonshot-theory.md`, and the Weisfeiler-Leman and IR lower bounds do not mention ETH and need no change.

---

## C. Code

All in `docs/w21-eth-code/` (under 200 KB; `nice`, `timeout`, one process at a time).

| File | Purpose |
|---|---|
| `eth_core.py` | Exact implementation: $M_0$, $C^B$, $P_u$, design on a formula, Lemma 3.2 sum, eq. (3.13), Hermite |
| `test_core.py` | Matrix checks, Lemma 4.3, pipeline, broken variants |
| `check_lift.py` | Sec. 5: Lemmas 5.1, 5.2, the $A_\ell$ pipeline |
| `check_appendix_d.py` | Lemma D.4, (D.9), (D.10) |
| `check_params.py` | Parameter thresholds and the (3.16) exponent |
| `check_transfer.py` | Feasibility of the Sec. 4 construction for TI, AGL, copying variants (exact binomial tails) |
| `results.txt` | Log of all the above |

Sources are linked inline in §A.4.
