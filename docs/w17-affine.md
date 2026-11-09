# String isomorphism under AGL(k,2): what is really known, and what a moonshot attempt found

Branch `w17-affine`, 2026-11-08. Code: `docs/w17-affine-code/` (`bidirectional_check.py`, `ir_affine.c`).

**Labels.** [PROVEN] complete argument here plus cited theorems. [SKETCH] gaps listed.
[CONDITIONAL: X] proven under hypothesis X. [SPECULATION] opinion.

Throughout, $V=\mathbb F_2^k$, $N=2^k$, $G=\mathrm{AGL}(k,2)$, $|G|\approx0.29\cdot2^{k^2+k}$, and a
string is $f:V\to\Sigma$ with $G$ acting by $f\mapsto f\circ A$ (a right action, $(f\circ A)\circ B=f\circ(AB)$).
$\mathrm{Iso}(f,g)=\{A\in G: f\circ A=g\}$.

---

## 0. Summary

**Target.** Is there a $2^{o(k^2)}=N^{o(\log N)}$ worst-case algorithm for $\mathrm{Iso}(f,g)$?

**Answer: no such algorithm found, and we give a conditional reason to expect difficulty. But the
campaign's "nothing better than brute force" is wrong by a constant factor in the exponent.**

| # | Statement | Status |
|---|---|---|
| A | Canonical form / $\mathrm{Iso}$ under $G$ in time $\lvert G:B\rvert\cdot\mathrm{poly}(N)=2^{k^2/2+O(k)}\mathrm{poly}(N)$ ($B$ = Borel 2-group) | [PROVEN] mod Luks/Babai–Luks for 2-groups |
| B | $\mathrm{Iso}$ under $G$ in **deterministic** time $2^{k^2/4+k/2}\mathrm{poly}(N)$ (flags + bidirectional collision) | [PROVEN] mod same; verified on $k\le4$ |
| B′ | For the bidirectional method, this is tight in a black-box model: $\Omega(2^{k^2/4})$ flag-canon queries | [PROVEN] (oracle model) |
| C | $d$-tensor isomorphism of format $k^{\times d}$ over $\mathbb F_2$ reduces to AGL$(dk,2)$-SI in poly$(2^{dk})$ time. So AGL-SI in $2^{o(K^2)}$ implies $d$-TI in $2^{o(k^2)}$ for every fixed $d$ | [PROVEN] reduction; the *hardness* is [CONDITIONAL: 4-TI hypothesis] |
| D | Instance bound: $T(f,g)\le 2^{(\mathrm{sep}(g)+1)k}\mathrm{poly}(N)$; random $g$: $\mathrm{sep}\le\log_2k+3$, so $2^{k\log k+O(k)}$ | [PROVEN] |
| E | Subclass with $2^{o(k^2)}$ (literature): vectorial quadratic colourings $\mathbb F_2^k\to\mathbb F_2^m$: $2^{O((m+k)^{1.5})}$, $m=o(k^{4/3})$ gives $2^{o(k^2)}$ | [PROVEN] mod arXiv:2610.00874 Thm 1.3 (decision) |
| F | Cubic forms char $>3$: $2^{\tilde O(n^{1.5})}$ per [GQ IV + IMQSZ]. **Cubic Boolean functions (char 2): not established** by any source found | literature check |
| G | Sylow trick in HJ's dispatcher: enumerate $\lvert P\rvert_{2'}$ cosets at affine/classical nodes instead of $\lvert P\rvert$; replaces Prop. 2's $0.288N^{1+\log N}$ by $\approx N^{(\log N)/2+O(1)}$ and turns $\lambda$ into $\lambda/2$ in Thm R** | [SKETCH] |

Bottom line for the campaign (§7): Theorem A/B show Prop. 2's tightness is specific to HJ's dispatcher, not to the
problem, but they change only constants: no $o(\log N)$ for the Lie term. Theorem C identifies what any $2^{o(k^2)}$
algorithm would have to do: at least beat brute force for all $d$-tensors. Experiments (§6) found no rigid function
needing more than $k$ levels of branching on anything up to $k=10$; the refinement is exact (leaves $=|\mathrm{Aut}|$)
on all but a factor-2 exception. The data is too small to say anything about scaling.

---

## 1. State of the art (checked 2026-11-08)

* **Group-theoretic.** Luks 1982 (string isomorphism in polynomial time for groups with bounded composition
  factors; canonical forms via Babai–Luks 1983); Luks 1999 (hypergraph isomorphism $2^{O(n)}$, Boolean functions
  up to variable permutation, by DP, i.e. $S_k$ acting on $\mathbb F_2^k$; note **not** $\mathrm{GL}$); Schweitzer–Wiebking canonization;
  Babai–Codenotti–Qiao SODA 2011 / ICALP 2012 (code equivalence $2^{O(n)}$ in code length $n$, adapting Luks;
  irrelevant at $n=N$ scale, but the DP-over-subsets idea is the model for §4.3).
* **Bidirectional collision.** D. Rosenbaum, *Bidirectional collision detection and faster deterministic isomorphism
  testing* (arXiv:1304.3935): generic deterministic $\sqrt{\ }$ for collision-structured isomorphism problems,
  giving $n^{(1/2)\log_pn+O(1)}$ general groups and $n^{(1/4)\log_pn+O(\log n/\log\log n)}$ solvable groups.
  **The exponents $1\to1/2\to1/4$ here are the direct analogues of Theorems A, B.** The analogy is exact: both have a
  $2^{(\log N)^2}$ search space and a poly-time solvable "2-part" (composition series / Borel).
* **Tensor isomorphism.** Grochow–Qiao TI-completeness (cubic forms, algebras, $d$-tensors reduce to 3-TI, SICOMP 2023);
  Part IV (arXiv:2306.16317, STOC 2025): linear-length reductions among the five 3-tensor actions, giving
  $q^{\tilde O(n^{1.8}\log q)}$ for cubic forms in char $>3$ with Sun's algorithm and hence, plugging in IMQSZ, $q^{\tilde O(n^{1.5})}$
  [routine combination, Thm 1.10 + IMQSZ]. Sun, STOC 2023 (arXiv:2303.15412) $p$-groups class 2 exponent $p$:
  $N^{O((\log N)^{5/6})}$. IMQSZ FOCS 2024 (open-access PDF eprints.sztaki.hu/10827): $N^{\tilde O((\log N)^{1/2})}$ and Thm 3.2: matrix-space equivalence $q^{\tilde O(\ell^{1.5})}$.
  Their last step uses Ivanyos–Qiao's *-algebra machinery in **odd characteristic** (IMQSZ Prop. 4.9 "Let $q$ be an odd prime
  power"). **Grochow–Ivanyos–Qiao–Sun, arXiv:2610.00874 (1 Oct 2026)** does $p=2$: quadratic form *tuple* and *space*
  isometry over $\mathbb F_2$ in $2^{O((m+n)^{1.5})}$ (Thms 1.2, 1.3), 2-groups of Frattini class 2 in $N^{O(\sqrt{\log N})}$.
  It states explicitly that the Sun/IMQSZ tensor algorithms "do not work for tensors over $\mathbb F_2$".
* **Beyond 3-TI.** $d$-TI reduces to 3-TI [GQ23], but with polynomial dimension blow-up, so $d\ge4$ gets nothing from
  IMQSZ at the $2^{o(k^2)}$ scale. Worst-case 4-TI: brute force $q^{2k^2}\mathrm{poly}$ (enumerate two factors, then a matrix-tuple
  equivalence, polynomial by Brooksbank–Luks); average-case 4-TI: arXiv:2604.00591 (polynomial on a $1/q^{\Theta(1)}$ fraction).
  **No worst-case 4-TI algorithm with exponent $o(k^2)$ found.** (Enumerating one factor leaves a tuple of 3-tensors under a *simultaneous* $\mathrm{GL}^3$, which is not plain 3-TI, so IMQSZ does not obviously give $q^{k^2+o(k^2)}$.)
* **Affine equivalence of Boolean functions / S-boxes.** Biryukov–De Cannière–Braeken–Preneel EUROCRYPT 2003
  (permutation S-boxes, $n^32^{2n}$; uses a two-sided affine action and permutation structure; for arbitrary $f$ with
  fixed output the injective case is trivial and the interesting case is Boolean); Canteaut–Couvreur–Perrin (eprint 2021/225,
  "Recovering or Testing Extended-Affine Equivalence", worst case at quadratics); a method with bound $o(2^{r^2/2+n(n-r)})$ (IEEE 8882230, $r$ a rank parameter, not worst-case).
  Dickson's classification handles degree $\le2$ in polynomial time. **Nothing better than the group order is stated in this literature for arbitrary truth tables.** The IP problem (Patarin) and Beullens/NQT
  graph-theoretic attacks on alternating trilinear forms are average-case/birthday, for structured instances, $q^{\Theta(n)}$-type heuristic bounds.
* **Code equivalence.** Support splitting (Sendrier) is polynomial except when hulls are large; Bardet–Otmani–Saeed-Taha
  (arXiv:1905.00073) reduce trivial-hull PCE to weighted GI. Weakly self-dual codes are the hard core (§3.5).

**Checked claim: "affine equivalence of arbitrary colourings: no algorithm better than brute force found."**
False as a statement about the literature: the generic techniques give exponent 1/2 and 1/4 of $\log_2|G|$ immediately (§2),
even though I found no paper that writes this out for truth tables. It remains true that no $2^{o(k^2)}$ algorithm is known.
[Hedged: absence of evidence after several targeted searches.]

---

## 2. Theorems A, B: the Borel 2-group and bidirectional collision

Let $B=U\ltimes V$ be the upper-unitriangular maps $x\mapsto Ux+t$ with respect to the standard flag
$V_i=\langle e_1,\dots,e_i\rangle$; $B$ is a 2-group of order $2^{k(k-1)/2+k}$. Index: $[G:B]=\prod_{i=1}^k(2^i-1)\approx0.289\cdot2^{k(k+1)/2}$
(the complete flags of $V$). Babai–Luks give **canonical forms** $\mathrm{Can}_B(x)$ for $x:V\to\Sigma$ under $B$ in poly$(N)$ time (2-groups have bounded composition factors), along with the $B$-coset of canonizers.

**Theorem A (flag enumeration).** [PROVEN mod Babai–Luks] Canonical forms and $\mathrm{Iso}$ under $G$ take $2^{k^2/2+k/2}\mathrm{poly}(N)$ time.

*Proof.* Let $S$ be coset representatives of $B$ in $G$. Then $\mathrm{Can}(f):=\mathrm{lexmin}_{s\in S}\mathrm{Can}_B(f\circ s)$ is a $G$-canonical form, because any $h\in G$ permutes left cosets $sB$ and $\mathrm{Can}_B$ is $B$-invariant. The cosets of minimizers give $\mathrm{Aut}(f)$. ∎

**Theorem B (bidirectional collision).** [PROVEN mod Babai–Luks] Decide $f\cong_G g$ and compute $\mathrm{Iso}(f,g)$ in deterministic time $2^{k^2/4+k/2}\mathrm{poly}(N)$ and space $2^{k^2/4}\mathrm{poly}(N)$.

*Proof.* Set $m=\lfloor k/2\rfloor$, $W_0=V_m$, and let $H$ be the stabilizer in $G$ of $W_0$ (linear part stabilizes $W_0$, translations arbitrary); $B\le H\le G$.
Let $S_1$ be representatives of left cosets $G/H$ ($\leftrightarrow$ $m$-subspaces of $V$), $|S_1|=\binom km_2\le3.47\cdot2^{m(k-m)}$.
Let $S_2$ be representatives of right cosets $B\backslash H$ ($\leftrightarrow$ pairs (complete flag of $W_0$, complete flag of $V/W_0$), using $B$ contains all translations), $|S_2|=[m]_2!\,[k-m]_2!\approx0.083\cdot2^{m^2+m}$ for $k=2m$.
Every $h\in G$ factors uniquely as $h=s\,b\,t$ with $s\in S_1$, $b\in B$, $t\in S_2$. Hence
$$\text{$f\circ h=g$ for some $h$} \iff \exists s,t:\ \mathrm{Can}_B(f\circ s)=\mathrm{Can}_B(g\circ t^{-1}).$$
Tabulate $\{\mathrm{Can}_B(f\circ s)\}_{s\in S_1}$ (hashed) and look up each $\mathrm{Can}_B(g\circ t^{-1})$, $t\in S_2$. Each matched pair yields explicit elements $s\,b\,t\in\mathrm{Iso}(f,g)$ from the Luks coset of canonizers.

For the whole coset: fix a bucket, $s_0,t_0$. All of $\mathrm{Aut}(f)$ is generated by $\{s\,\beta\,s^{-1}: \beta\in\mathrm{Aut}_B(f\circ s)\}$ together with, per bucket, $x_s=s b_{s,t_0}t_0$ and $y_t=s_0 b_{s_0,t}t$: for a matched triple $z=sbt$ one checks $z(x_sx_{s_0}^{-1}y_t)^{-1}=s(bb'^{-1})s^{-1}\in s\,\mathrm{Aut}_B(f\circ s)\,s^{-1}$. So $|S_1|+|S_2|$ group elements (each sifted by Schreier–Sims in poly$(N)$) suffice for $\mathrm{Aut}(f)$ (the run on $(f,f)$), and $\mathrm{Iso}(f,g)=\mathrm{Aut}(f)\,h$ for any one matched $h$. ∎

*Verified:* `docs/w17-affine-code/bidirectional_check.py`: $k=3,4$: $|S_1||B||S_2|=|G|$ exactly (322560 at $k=4$), unique factorization by exhaustion at $k=3$, and the collision test matches brute force on all random pairs tried (300 at $k=3$; 6 at $k=4$).

In $N$: Theorem B is $N^{(1/4)\log_2N+O(1)}$ against HJ's $0.288N^{1+\log_2N}$.

**Same proof, general form.** For any permutation group $G$ on $N$ points with subgroups $B\le H\le G$ where $B$ has polynomial canonization:
$\mathrm{Iso}_G$ in $(|G:H|+|H:B|)\mathrm{poly}(N)$. For Lie type in natural characteristic $p$, $B$ = Sylow $p$ and $H$ a middle parabolic give $|G|^{1/4+o(1)}$. Non-canonical versions (Theorem A form with Sylow$_p$, no collision) give $|G|^{1/2+o(1)}$.

**Proposition B′ (black-box tightness of the method).** [PROVEN in the oracle model] Say an algorithm has access to $f,g$ only through oracles $v_f(F),v_g(F)$ returning, for a complete flag $F$, an opaque value with $v_g(F)=v_f(h\cdot F)$ for a hidden $h\in\mathrm{AGL}(k,2)$ (or, in the non-isomorphic case, $v_g$ an independent random labelling). The opaque values are the Borel canonical forms. Then any algorithm deciding "$\exists h$" with constant advantage makes $\Omega(2^{k^2/4})$ queries.

*Proof.* Take $v_f$ a uniformly random injective labelling of the flags, $h$ uniform. Before the first cross-collision, every query is answered by a fresh random label whatever the case. A pair of queries (one on $f$, one on $g$) collides with probability $\le 1/\#\text{flags}$ over the choice of $h$; union bound over $T^2$ pairs gives $T=\Omega(\sqrt{\#\text{flags}})$, and $\#\text{flags}\approx2^{k^2/2}$. ∎

So beating Theorem B needs an algorithm that *does not* factor through flag-Borel canonical forms. Natural in hindsight, and worth stating: the flag method has hit its limit.

**Consequence of the general form for the campaign:** §7.

---

## 3. Hardness: AGL-SI contains all $d$-tensor isomorphism problems

**Theorem C.** [PROVEN] Let $d\ge1$ be fixed and $T,T':(\mathbb F_2^k)^{d}\to\mathbb F_2$ be $d$-linear forms (arbitrary). Let $K=dk$. Define $c_T:\mathbb F_2^K\to\Sigma$ (with $|\Sigma|\le2^d+1$) on $x=(x_1,\dots,x_d)$ by:
$c_T(0)=\star$; if $S=\{i:x_i\ne0\}\ne\emptyset,[d]$, $c_T(x)=(\text{partial},S)$; if $S=[d]$, $c_T(x)=(\text{full},T(x_1,\dots,x_d))$.
Then $\mathrm{Iso}_{\mathrm{AGL}(K,2)}(c_T,c_{T'})=\{(A_1,\dots,A_d)\in\prod\mathrm{GL}(k,2):T'\circ(A_1,\dots,A_d)=T\}$.

*Proof.* The colour $\star$ forces every affine map in $\mathrm{Iso}$ to fix $0$, so it is linear, $A$. For $i\in[d]$ the points with support exactly $\{i\}$ are $V_i\setminus0$, so $A(V_i)=V_i$; hence $A=A_1\oplus\dots\oplus A_d$. On full-support points $c_{T'}\circ A=c_T$ reads $T'(A_1x_1,\dots,A_dx_d)=T(x_1,\dots,x_d)$, and both vanish when some $x_i=0$. Conversely any such tuple preserves colours. ∎

The table has size $N=2^{dk}$; the reduction is polynomial in $N$. Consequently:

**Corollary C1.** If AGL-SI runs in $2^{o(K^2)}$ (even as decision, even non-canonical), then for each fixed $d$, $d$-TI over $\mathbb F_2$ of format $k^{\times d}$ runs in $2^{o(k^2)}$. For $d\ge4$ this is new and appears out of reach of the current literature (§1): 4-TI's best worst-case bound known to us is $2^{\Theta(k^2)}$ (§1).

**Hypothesis 4-TI$_{2}$.** No $2^{o(k^2)}$-time algorithm for $k\times k\times k\times k$ tensor isomorphism over $\mathbb F_2$.

**Corollary C2.** [CONDITIONAL: 4-TI$_2$] AGL$(K,2)$ string isomorphism on arbitrary colourings requires $2^{\Omega(K^2)}$ time; so no $N^{o(\log N)}$ algorithm. Combined with Theorem B: complexity is $2^{\Theta(K^2)}$ under this hypothesis (if 4-TI needs $2^{ck^2}$, then AGL$(K,2)$ needs $2^{(c/16)K^2}$; Theorem B gives $\le2^{K^2/4+O(K)}$).

Honest calibration: 4-TI$_2$ is a fine-grained hypothesis with no independent support beyond "open since Grochow–Qiao". The generic 4-tensor instance is easy (individualize $t\approx k^{1/3}$ vectors per block and read off linear functionals; §4.2), so any hard instance is structured. A Sun-style dichotomy for $d=4$ might refute it (§4.3 for what would be required). What is **not** in doubt is that Corollary C1 is a real barrier: a $2^{o(k^2)}$ AGL-SI algorithm would resolve 4-TI as a *corollary*.

Remarks. (a) The reduction uses a colouring ($2^d+1$ colours). Reducing to 2 colours needs a dimension-reduction gadget of size $O(\log|\Sigma|)$ extra coordinates; [SKETCH] routine, not attempted in detail. (b) The reduction is not degree-preserving: the colour classes (indicators of coordinate subspaces) have full degree. **Hardness for bounded algebraic degree is not established.** (c) Conversely, this shows AGL-SI on tensor-structured instances is at least $d$-TI for all $d$, while the campaign's Prop. 3 places it below GI at $N^{O(\log N)}$ scale; consistent.

### 3.5 Other hardness channels considered

* Group isomorphism: class-2 Frattini 2-groups reduce to AGL$(n+m,2)$-SI with $K=\log_2|G|$ via the graph $\{(x,Q(x))\}$ of the squaring map with colours pinning $V,W$. [PROVEN, easy] But such groups are already $N^{O(\sqrt{\log N})}$ (2610.00874). Gives no hardness.
* Linear code equivalence: for $\mathrm{colour}$ classes $S_c$, $\mathrm{Iso}$ under $\mathrm{GL}$ is permutation equivalence of the codes with generator columns $S_c$ (with simultaneous classes). Weakly self-dual codes (hull = code) are the hard core of SSA; they correspond to all second moments vanishing (§4.2). Link noted, no reduction to a named hard problem.

---

## 4. Algorithmic attempts: precise statements and where they break

### 4.1 Hyperplane / flag recursion and memoization [PROVEN statements; break identified]

*Recursion:* $T(k)\le 2^{k+1}\cdot2T(k-1)$: enumerate hyperplanes+side and recurse. This is flag enumeration: gives $2^{k^2/2+O(k)}$, no better than Theorem A.

*Memoization (Held–Karp analogue).* DP over subspaces: for each subspace $W$ of dimension $i$ compute the lexmin of $f|_W$ over linear frames of $W$ with the coset of minimizers. Number of states $\sim2^{k^2/4+O(k)}$ (Gaussian binomial sum). The transition from hyperplane $W'\subset W$ needs: the coset $C(W')=A_0\mathrm{Aut}(f|_{W'})$, and to lexmin the string $h_a=f(a+\,\cdot)$ on $W'$ over $C(W')$, for each $a\in W\setminus W'$.

**Where it breaks.** (The comparison below draws on secondary descriptions of Luks 1999; I did not read the paper in full.) The transition is itself string isomorphism under the group $\mathrm{Aut}(f|_{W'})\le\mathrm{GL}(W')$, of arbitrary shape; in the worst case (e.g. $f|_{W'}$ constant) that group is $\mathrm{GL}(i,2)$, and the best transition bound is Theorem A's $2^{i^2/2}$. Worst-case total: $\max_i 2^{i(k-i)+i^2/2}=2^{k^2/2}$: no gain over Theorem A, though if *all* $f|_W$ are rigid (Aut $\le2^{o(k)}$) the DP is $2^{k^2/4+o(k^2)}$ and canonical. The Luks-style trick that makes the analogous $S_n$ DP ($k!\to2^k$, Luks 1999) work does not transfer: there, the DP over subsets is nested inside a recursion on the structure of the (non-Boolean) group, and the "$\mathrm{Aut}$ huge" case is the symmetric group, which is then attacked by *another* halving; here $\mathrm{GL}$ has no analogue of "$S_A\times S_B$ acting on $2^A\times2^B$" splitting (the unipotent radical couples the blocks). [SKETCH of the comparison.]

### 4.2 Degree parameter, derivatives, moment forms

**Facts.** [PROVEN] Over $\mathbb F_2$, a degree-$D$ polynomial $f$ has top form $\tau_f$, an alternating $D$-linear form (iterated polarization), and $f\circ A=g$ forces $\tau_g=\tau_f\circ(L,\dots,L)$. Each derivative lowers degree by one and is equivariant: $D_{La}g=(D_af)\circ A$. Colour $V$ by derivative classes ${\rm cl}(D_af)$: invariant.

Dually, for a colour class $S$, the **moment forms** $M_S^{(e)}(a_1,\dots,a_e)=\sum_{s\in S}\prod_ia_i(s)$ on $V^*$ are invariant, and vanish for $e<k-\deg1_S$; the first nonvanishing moment is the Hodge dual of $\tau_{1_S}$, an alternating $(k-\deg 1_S)$-form on $V^*$. [PROVEN]

**Second moment.** [SKETCH: routine] If $f\circ A=g$ with $A$ linear and some colour class has $M_S^{(2)}$ nondegenerate, then $A^*$ is an isometry, a coset of $\mathrm{Sp}$ or $\mathrm{O}$ of order $2^{k^2/2+O(k)}$; with the Lagrangian parabolic and Sylow 2, Theorem B-form gives $2^{k^2/8+O(k)}\mathrm{poly}(N)$. If degenerate, the radical is an invariant subspace (a parabolic reduction). The worst case is all $M^{(2)}_S\equiv0$ (self-orthogonal/weakly self-dual), which is exactly why high-degree colour classes and hull-rich codes are the hard core. (For affine maps, enumerate the translation first: only a factor $2^k$.)

**Degree $\le2$.** Dickson/Albert: polynomial. Coset computable. Colourings by $m$-tuples of quadratics: 2610.00874 Thm 1.3 after enumerating translations (function equality equals formal-form equality because $x_i^2\equiv x_i$): **$2^{O((m+k)^{1.5})}$** — the only non-trivial $2^{o(k^2)}$ subclass we can claim [PROVEN mod 2610.00874, decision].

**Degree 3 (cubic Boolean functions).** $\tau_f\in\Lambda^3V^*$ is an alternating trilinear form (ATFE). Three facts:
1. *Individualization still works.* Individualize $t\approx\sqrt{2k}$ vectors $u_i$ in $g$'s domain (cost $2^{tk}=2^{O(k^{1.5})}$, guess their images): the functionals $\tau(u_i,u_j,\cdot)$ number $\binom t2\approx k$. If they span $V^*$, then $L$ is determined. **[PROVEN] $T\le2^{t(\tau)k}\mathrm{poly}(N)$, where $t(\tau)$ is the least $t$ such that some $t$-tuple's contractions span $V^*$.** For random $\tau$, $t(\tau)=O(\sqrt k)$ w.h.p. [SKETCH of the rank argument.]
2. *Where the literature stops.* The worst case for $\tau$ needs the low-rank machinery (Sun, IMQSZ), whose final tuple-congruence step is odd-characteristic; 2610.00874 solves quadratic-form *tuples* over $\mathbb F_2$, not alternating-matrix tuples / alternating trilinear forms, and GQ IV's Thm 1.10 output gadget in char 2 only promises "symmetric (or anti-symmetric)" slices. So: cubic Boolean function equivalence is **not** known to be $2^{o(k^2)}$ in the worst case from anything we could find. [Hedged.] This is a concrete, possibly tractable open target (lead 1).
3. Lower-order terms: after the top form, the quadratic part must be matched under $\mathrm{Aut}(\tau)$ (an orbit problem for an uncontrolled group); via homogenization on $k+O(1)$ variables plus partition gadgets (GQ IV Thm 1.14) this should fold in; [SKETCH, not verified in char 2].

**Degree $D\ge4$: the derivative reduction, and exactly where it breaks.**
Statement: $\mathrm{Iso}$ for degree $D$ reduces to computing the $2^k$ canonical forms of $D_af$ (degree $D-1$) plus a colouring problem. It breaks because (i) no canonical form algorithm for lower degree is available beyond degree 2, (ii) when all derivatives are equivalent (monomial traces $\mathrm{Tr}(x^d)$, or bent functions where every $D_af$ is balanced with no invariant information), the colouring is flat and one must individualize a direction anyway, (iii) after individualizing $u_1,\dots,u_{D-3}$ the only thing canonically available is the cubic $D_{u_1}\cdots D_{u_{D-3}}f$; its automorphisms leave a huge coset. Recursion $T_D(k)\le2^{k}T_{D-1}(k)$ terminates at $D\to3$ only with $D$ levels of $2^k$ individualization, then the unresolved cubic-plus-rest problem. Bounded-degree generic gain: for random $D$-forms, $t\approx k^{1/(D-1)}$ individualized vectors span $V^*$ by contractions, giving $2^{k^{1+1/(D-1)}}$ on average. [SKETCH]

**The structural gap for $D\ge4$** (the honest analogue of Sun's low-rank lemma): for $D=3$, the kernel of individualization consists of low-rank slices, and low-rank matrix spaces have canonical shrunk subspaces (noncommutative rank, polynomial time). For $D\ge4$ the analogous object is a space of $(D-1)$-tensors of small rank, with no canonical structure theorem (partition rank is hard; analytic rank $=$ partition rank only up to quantitative losses, Janzer, Milićević; none is canonical) and the final tuple problem is itself TI-hard. [SPECULATION: a $d=4$ version would need a canonical regularization of low-partition-rank spaces, which is a new mathematical object.]

### 4.3 Sun-style individualization beyond bilinear

Sun's method (matrix-space individualization + low-rank characterization + tuple congruence) depends on (i) bilinearity of $T(u,\cdot,\cdot)$ in the vector being individualized, (ii) the noncommutative rank / Flanders structure of low-max-rank matrix spaces, (iii) polynomial algorithms for matrix tuples ($*$-algebras). For arbitrary-degree colourings, (i) is replaced by "patterns on cosets of a small subspace": individualize $t$ points to define $U$ of dimension $t$; each point $x$ gets the pattern $(f(x+w))_{w\in U}$.

**Proposition D (pattern separation).** [PROVEN] Call a frame $u=(u_0,\dots,u_t)$ of $V$ *separating for $g$* if the patterns $P_{g,u}(x)=(g(x+w))_{w\in U}$ ($U=\langle u_i-u_0\rangle$, positions ordered by the frame) are pairwise distinct over $x\in V$. If a separating frame for $g$ has $t+1$ points, then $\mathrm{Iso}(f,g)$ is found in $2^{(t+1)k}\mathrm{poly}(N)$ (guess the frame images in $f$'s domain, read $A$ off the pattern match, verify). For uniformly random $g$, a fixed frame $(0,e_1,\dots,e_t)$ with $t=\lceil\log_2k\rceil+3$ is separating w.h.p. (union bound: $\le2^{2k}2^{-2^t}$ for pairs outside the same $U$-coset, $\le2^{k+t}2^{-2^{t-1}}$ inside). So random functions: $2^{k\log k+O(k)}$.

**Where it fails.** If $\alpha\in\mathrm{Aut}(g)$ fixes the frame pointwise then $P_{g,u}(\alpha x)=P_{g,u}(x)$, so a separating frame must contain a base of $\mathrm{Aut}(g)$; for quadratic bent $g$ this forces $t\ge k-O(1)$, i.e. $\mathrm{sep}(g)=\Theta(k)$, although that instance is easy (Dickson). So $\mathrm{sep}$ is a *sufficient* parameter, not a complexity measure: for structured $g$ (bent, low degree) patterns collapse (a degree-$D$ polynomial's patterns for $t\ge D$ are determined by derivative data of degree $<D-|I|$) and the bound is brute force. There is no "structure vs randomness" theorem for colourings of unbounded degree that would convert failure of separation into a usable structure; higher-order Fourier analysis (bias implies low rank; Green–Tao, Kaufman–Lovett, Milićević, Janzer) is bounded-degree and its regularization is non-canonical. This is, we believe, the exact point where Sun-style reasoning stops generalizing to arbitrary colourings. [SPECULATION on impossibility.]

### 4.4 Individualization-refinement on the affine structure

See §6. The refinement used is "point–direction 1-WL" ($c_D(d)=$ multiset of $(c(x),c(x+d))$; $c'(x)=(c(x),\text{multiset of }(c_D(d),c(x+d)))$), optionally with a dual/Walsh sort. Search tree with first-path invariant pruning.

---

## 5. Summary of where each idea stopped

| Attempt | Outcome |
|---|---|
| Borel + Luks | exponent 1/2 (Thm A) |
| + bidirectional collision | exponent 1/4 (Thm B), and this is optimal in the flag-oracle model (Prop B′) |
| Larger tractable subgroups (Levi blocks $r$) | $\Gamma_d$ cost $N^{O(r)}$ vs gain $kr/4$: no net gain (Levi canon needs flag enumeration inside each block, $2^{kr/2}$) |
| Subspace DP (Held–Karp) | breaks at Aut-coset transitions: no worst-case gain |
| Degree/derivatives | only degree $\le2$ classical; degree 3 open in char 2; $D\ge4$ no canonical structure |
| Sun-style / patterns | random and generic ok; worst case needs rank-structure theorem beyond bilinear |
| TI-hardness | $d$-TI $\le$ AGL-SI: conditional $2^{\Omega(k^2)}$ |

---

## 6. Experiments

`docs/w17-affine-code/ir_affine.c` (one process, `nice`, seconds per run). Measured on the search tree (target = smallest non-singleton cell; pruning by first-path invariant): depth = number of individualizations to a discrete partition; cell sizes along the first path; tree size; $|\mathrm{Aut}|$ = number of leaves whose string equals the first leaf; excess = leaves/$|\mathrm{Aut}|$.

| family ($k$) | depth | cells on first path | tree nodes | leaves / auts |
|---|---|---|---|---|
| random, balanced ($k=6,8,10$) | 0–1 | root discrete | 1–3 | 1–2 / same |
| random cubic ($k=8,9,10$) | 0 | root discrete | 1 | 1 / 1 |
| random cubic ($k=6,7$) | 1–6 | small group structures | up to $7\cdot10^4$ | excess 1 |
| Maiorana–McFarland, random $\pi$ ($k=8$) | 3–5 | 120, 119, 8, (2, 2) | 177–193 | **32/32 or 64/32 (excess 2)** |
| MM ($k=10$) | 3 | 496, 495, 16 | 40 (cap) | partial |
| PS$_{ap}$ bent ($k=8$) | 6 | 120, 119, 2, 2, 8, 2 | cap | $\approx$ auts |
| quadratic bent inner product ($k=6,8,10$) | $k+1$ | 28,27,10,8,4,3,2 ($k=6$) | $|\mathrm{Aut}|$-sized | excess 1 |
| Gold $\mathrm{Tr}(x^3)$ ($k=6,\dots,10$) | $k+1$ ($k$ even), $k$ ($k$ odd) | group orbits | $|\mathrm{Aut}|$-sized | excess 1 |
| monomial traces $\mathrm{Tr}(x^7),\mathrm{Tr}(x^{11})$, inverse ($k=6$–$9$) | 1–6 | small | $\le$ few 100 | excess 1 |
| structured cubic $x_1x_2x_3+\cdots$ ($k=6,8,10$) | 6, 9, 10 | small group orbits | $|\mathrm{Aut}|$-sized | excess 1 |
| cyclotomic / random-on-cosets ($k=6,8$) | 0–5 | | | excess 1 |
| 2×2×2×2 tensor (coloured reduction, $k=8$) | 0 | root discrete | 1 | 1 |

Caveats on the data. Refinement uses 64-bit hashes (collisions not excluded, but negligible at this scale). Runs marked "cap" or "$|\mathrm{Aut}|$-sized" hit the node limit, so their leaf counts cover only the explored part of the tree, supplemented by 2–20 Knuth probes; "excess 1" there means no non-automorphism leaf was *seen*, not that none exists. The probe estimator returned 0 on MM at $k=8$ (it discards paths whose target-cell size differs from the first path), so MM figures come from complete trees only. $k=10$ runs are first-path only.

Findings. (1) Where the tree was explored completely, every family except MM has excess exactly 1 at these sizes: every surviving branch is an automorphism; the largest excess observed anywhere is 2 (MM with random $\pi$, $k=8$). (2) Depth is at most $k+1$ trivially; the observed maximum is $k+1$ and only for functions with huge automorphism groups (quadratic bent, Gold, Aut-rich cubics). Functions with small automorphism groups ($|\mathrm{Aut}|\le64$, the MM family) at $k\le10$ needed at most 5 individualizations; those with $|\mathrm{Aut}|=1$ were discrete at the root. (3) Bent functions cost two uninformative individualizations ($c_D$ is constant when the autocorrelation vanishes) and then refine quickly; first-path cells 120, 119 are two free individualizations. (4) Two hill-climbs on $k=6$ for excess stayed at excess 1 (random starts are rigid: no room to climb). **So the experiments give no evidence of $k^2$-type behaviour, and also cannot refute it: $k\le10$ is below the scale where CFI-type effects show; I did not construct an affine CFI analogue.**

I do not claim anything about the worst case from this data.

---

## 7. Consequences for the campaign (Theorem R**, HJ's enumeration channel)

1. **Theorem A / Sylow trick in HJ's dispatcher (Proposition G).** [SKETCH] At a node with primitive quotient $P$ of $G$ and kernel $K$: instead of enumerating $|P|$ cosets, enumerate the transversal of $H=\pi^{-1}(\mathrm{Syl}_2(P))$ in $G$ and recurse on $H$. The next dispatch step sees a 2-group on the blocks, handled by Luks halving (domain halves each step, cost a constant factor per unit of $\log$ domain). The multiplicity $|P|$ is replaced by $|P|_{2'}$. Gaps: (a) HJ's rows would need a new "Sylow enumeration" row paid by the potential; I checked only that $|P|_{2'}\le|P|$ and the subsequent chain consists of $O(\log d)$ halving steps with $O(1)$ branching; a careful potential accounting is needed but the row is *no more expensive* than enumeration. (b) For Lie type in characteristic $p\ne2$ use Sylow$_p$ instead (Luks for $p$-groups: polynomial, branching $p$ at $\le\log_pd$ halvings).
   * For $\mathrm{AGL}(r,2)$, $\mathrm{PGL}(r,2)$ on points, and the classical sections generally: $\log|P|_{2'}=(1/2+o(1))\log|P|$. **Effect on Theorem R\*\*:** $\exp(O(\log N(\log w+\lambda+1)))$ with the coefficient of $\lambda$ halved (the $\beta$-channel of Prop. 2.1 goes from $\mu\approx r+1$ to $\mu\approx(r+1)/2$). No change in form: still $\Theta(\log^2N)$ for AGL at the root; Prop. 2's lower bound applies to HJ as written, not to HJ+Sylow, which on $\mathrm{AGL}(k,2)$ does $\approx N^{(\log N)/2+O(1)}$ work.
   * Bidirectional collision (Theorem B's further halving to $|P|^{1/4}$) requires canonical forms of the recursive sub-instances; HJ is isomorphism-only (redteam, W1 §8 Lead 5). So it composes only with a canonical HJ; in the campaign's "canonical HJ" lead, this becomes $|P|^{1/4+o(1)}$ per node (a constant factor in exponent) and only then.
2. **Full enumeration channel.** Classical sections in towers are covered by the same trick level by level: each level pays $|P_i|_{2'}$ independently. Products in product action: factors independent. Primitive $P$ with large alternating sections (not classical): no gain (odd part of $S_m$ is $(m!)^{1-o(1)}$; these are handled by the giant channel anyway; (α)-channel unchanged). PGL on points: Sylow$_2$ is the unitriangular group modulo scalars (no scalars at $q=2$).
3. **What a true $2^{o(k^2)}$ would do.** If AGL$(k,2)$-SI had a $2^{o(k^2)}$ algorithm *relatively* (accepting strings over kernel-cosets alphabet) and canonically: the Lie part of the enumeration channel of R** disappears, leaving $\exp(O(\log N(\log w+1+o(\log d))))$. Without canonicity or relative form: only constants. The campaign's Attempt D (§4.4 of moonshot-theory) remains correct that the hypothesis needed is at least as strong as $2^{o(k^2)}$ affine equivalence. Our Theorem C shows that hypothesis itself implies new results for $d$-tensors.
4. **Unchanged:** $\log^2$ bound for GI (other channels, giant-breaking). Nothing here touches them.

---

## 8. Leads

1. **Cubic Boolean equivalence in $2^{\tilde O(k^{1.5})}$** (ATFE and lower-order terms over $\mathbb F_2$). Needs either alternating matrix-tuple congruence over $\mathbb F_2$ in polynomial time (adapt 2610.00874's quadratic-form tuple algorithm to the alternating quotient, i.e. "up to linear terms"), or a direct proof that GQ IV's reductions plus 2610.00874 suffice. Concrete and possibly tractable; would be the first $2^{o(k^2)}$ result for a natural high-degree-like Boolean class.
2. **4-TI vs individualization.** Worst-case 4-TI in $2^{o(k^2)}$ needs a low-partition-rank analogue of Sun's characterization. Either that exists (killing hypothesis 4-TI$_2$) or a CFI-style 4-tensor family proves the barrier for all individualize-and-tuple algorithms.
3. **Affine CFI.** Construct rigid $f$ on $\mathbb F_2^k$ where point–direction refinement needs $\omega(1)$ non-automorphism individualizations. Experiments suggest the current refinement is exact up to $k=10$ on natural families, so a construction (not a search) is needed.
4. **Canonical HJ + collision.** Makes Theorem B's $1/4$ reach HJ's classical enumeration nodes.
5. **Beyond flags.** Prop. B′ says any improvement must use more than flag-indexed Borel canonical forms; invariants that cut the flag variety (moment forms, bent "dual" structure) are the candidates; §4.2's nondegenerate case reaches exponent $1/8$ and the worst case is weakly self-dual structure.

---

## References

Theorem-E-type claims rest on arXiv:2610.00874, a five-week-old unrefereed preprint whose proofs I did not check; its statements were read directly from the PDF. Verified 2026-11-08 unless noted: Rosenbaum arXiv:1304.3935; Grochow–Qiao part IV arXiv:2306.16317; Sun arXiv:2303.15412; IMQSZ FOCS 2024 (eprints.sztaki.hu/10827); Grochow–Ivanyos–Qiao–Sun arXiv:2610.00874; arXiv:2604.00591 (average-case 4-TI); Bardet–Otmani–Saeed-Taha arXiv:1905.00073; Biryukov et al. EUROCRYPT 2003 (DOI 10.1007/3-540-39200-9_3); Canteaut–Couvreur–Perrin eprint 2021/225; Luks STOC 1999 (via citations); Babai–Codenotti–Qiao (via abstracts); Grochow–Qiao part III arXiv:2306.03135; Beullens/NQT ATFE attacks (via search listings). Luks 1982, Babai–Luks 1983, Dickson: from memory, standard. Janzer/Milićević, Green–Tao, Kaufman–Lovett: from memory.
