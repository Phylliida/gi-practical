# Referee report: w45-quartic

Branch `w46-redteam-quartic`, 2026-11-09. Adversarial referee of `docs/w45-quartic.md` (code in `docs/w45-code/`). Tools: `docs/redteam-w45-code/` (`h_arith.py`, `h_check.py`, `tiso.c`, `t2_check.py`, `t2_full.py`, `t3_check.py`), written independently of the author's harnesses. Lean was not run. Sources read: Grochow–Qiao arXiv:1907.00309 (GQ), Grochow–Qiao IV arXiv:2306.16317 (GQ IV), Qiao–Sun arXiv:2409.12457 (QS), Li–Li–Qiao–Tao–Wang arXiv:2604.00591, downloaded fresh for this report into new scratchpad subdirectories (the PDFs are not committed). ePrint 2026/1665 was not fetched: only the abstract text in a search result was seen, as for the author; no bot check was bypassed.

## 0. Verdict table

| # | Claim | Verdict | Severity of anything found |
|---|---|---|---|
| 1a | Thm H: algorithm, proof, rank hypothesis, invariance and computability of $s$ | **sound** | none; three improvements in §1 |
| 1b | Thm H: the threshold "$s\ge128$" / "$s>128$" | **broken as printed, repairable.** $s$ is even (ranks of alternating forms), so "$s>128$" means $s\ge130$. Printed parameters give $t/d>1/4$ at $s=128,130$; first success is $s=132$. With $R=8$ chosen by hand, $s\ge130$ works, so "$s>128$" is true after this repair; "$s\ge128$" is false (even with the sharp bound, exactly $1/4$) | arithmetic; no effect on the exponent's order |
| 1c | Thm H: random quartics, $s=\Theta(d)$ [SKETCH] | **sound, and the sketch closes in three lines** (§1.4); $s\ge d-2\sqrt d-O(1)$ whp | none |
| 2 | Blow-up analysis (S1, Prop 1, Cor 2), source quotes | **sound as counting; quotes verified verbatim.** Wording gap: "any kernel reduction" holds only for time bounds in $L$ alone, single field, one-input reductions; a format-sensitive bound escapes it | wording; fix in §2 |
| 3 | T1, 4-TI in $q^{n^2}\mathrm{poly}$ | **sound mod QS Thm 1.1** (statement verified; QS proof not re-derived) | none |
| 4 | T2 and T2′ | **sound**, both directions checked by hand; reverse tested by exact isomorphism decision | notation clash only |
| 5 | T3 and T3′ | **T3 sound; T3′ needs the hypothesis $f_i(0)=0$** (gap, small) | minor; a convention slip about $T_\beta$ |
| 6 | Prop B (weak barrier) | **sound** | none |
| 7 | Novelty and sources | checked; **one misdescription**: the 4-tensor algorithm of arXiv:2604.00591 is not "via eigenvalue-free slices" | correction in §7 |

**No break of any theorem statement other than the threshold 1b.** Every [PROVEN] claim holds as far as I can check, with fixes below.

## 1. Theorem H

### 1.1 What was checked

*The pair-rank lemma.* $1[\phi\in W]=\mathbb E_{\lambda\in W^\perp}(-1)^{\phi(\lambda)}$ and $\mathbb E_{v,v'}(-1)^{B(v,v')}=2^{-\mathrm{rk}B}$ for any bilinear $B$ (not only alternating) are correct. For $\lambda\notin\{0,w\}$ the form $\tau(\cdot,\cdot,\lambda,w)$ has rank $\ge s$; the two exceptional $\lambda$ give at most $2/|W^\perp|=2^{R-d}$. So $\Pr\le2^{R-d}+2^{-s}$, and $\le2^{1-s'}$ because $s'\le d/2$ and $R\le d/2$. Exact enumeration on $d=6$ (612 triples $(\tau,w,W)$ with $R=1,2,3$; `h_check.py` §1) confirms the identity to floating precision and the bound.

*Steps 1 and 2.* The count of $(R-1)$-subspaces ($\le4\cdot2^{(R-1)(d-R+1)}$), independence of the $m$ disjoint pairs, $m(s'-1)\ge Rd+4$, the union over $2^d$ values of $w$ and over $w$ in Step 2 with $b\ge(d+2)/R$: all correct. Success probability is at least $9/16$.

*Algorithm.* Correct and exactly as cheap as stated. If $f\circ L=g$ then $\tau_g(x,y,z,w)=\tau_f(Lx,Ly,Lz,Lw)$, so for any good $(A,B)$ on the $f$ side the images $L^{-1}(A,B)$ on the $g$ side give functional matrices with $\Phi^f L=\Phi^g$, and $L=(\Phi^f)^{-1}\Phi^g$. Exact verification $f\circ L=g$ on ANFs makes the test sound. `h_check.py` §3: on $d=8$, $L$ was recovered exactly from the functionals in 30/30 instances, with 600 decoys rejected.

*Rank hypothesis and $s$.*
- $s(\tau\circ L)=s(\tau)$ since $\tau\circ L(w,\lambda,\cdot,\cdot)=L^{\mathsf T}\tau(Lw,L\lambda,\cdot,\cdot)L$; adding terms of degree $\le3$ or translating does not change $\tau_f$. Checked by machine at $d\le8$.
- $s$ is computable in $2^{2d}\mathrm{poly}$ by enumerating 2-subspaces ($\tau(w,\lambda,\cdot,\cdot)$ depends only on the wedge $w\wedge\lambda$, hence only on the subspace, over $\mathbb F_2$). This is dominated by $2^{td}$ once $t\ge2$. Not needed by the algorithm: it can loop on $t=2,3,\dots$ and stop at the first $t$ with a spanning configuration; the bound still holds.
- The *all-pairs* minimum is genuinely what the proof uses: for fixed $w$ the sum runs over an arbitrary subspace $W^\perp$ of codimension $R-1$, which may concentrate on low-rank $\lambda$. So this proof cannot weaken the hypothesis to analytic rank, as §4.1 of w45 says.
- Hypothesis used correctly: $s\ge2$ is needed for $s'-1\ge1$.

No problem in any of these. **Theorem H as a statement about time $2^{td}\mathrm{poly}(d)$ with the printed $t$ is proved.**

### 1.2 The threshold is wrong as printed [broken, repairable]

The summary row says "beats $2^{d^2/4}$ for $s\ge128$" and the theorem says "$s\ge(128+\varepsilon)$". Both use the approximation $t\approx2\sqrt2\,d/\sqrt{s'}$ in a regime where the ceilings and the $-1$ matter. One fact first: **$s$ is even**, since a nonzero alternating form has even rank; so "$s>128$" means $s\ge130$.

Exact limit of $t/d$ as $d\to\infty$ for fixed even $s$ (so $s'=s$), from `h_arith.py`:

| $s$ | printed $R=\lceil\sqrt{s/2}\rceil$, $t/d=2R/(s-1)+1/R$ | best integer $R$ (still $2^{1-s'}$) | sharp pair bound $2^{-s}(1+o(1))$, best $R$ |
|---|---|---|---|
| 128 | $R=8$: 0.25098 $>1/4$ | $R=8$: 0.25098 | $R=8$: exactly $1/4$, no gain |
| 130 | $R=9$: 0.25065 $>1/4$ | $R=8$: **0.24903** | $R=8$: 0.24808 |
| 132 | $R=9$: **0.24852** | $R=8$: 0.24714 | $R=8$: 0.24621 |

The first column is the theorem as printed, where $R$ is the ceiling of $\sqrt{s/2}$.

**Fix.** Replace "$s\ge128$" by "$s\ge132$ with the printed parameters; or $s\ge130$ taking $R=8$". Then "$s>128$" is true, but only with the repair; at $s=128$ the method does not beat $2^{d^2/4}$ even with the sharp bound ($t/d=1/4$ exactly, and the additive terms of $t$ are positive). Also "$2\sqrt2+o(1)$" must be read as $o(1)$ when $s'\to\infty$; at $s'=130$ the coefficient is 2.86, at $s'=2$ it is 4.24.

Finite $d$. The printed parameters first satisfy $td<d^2/4$ at $d=282$ (any $s\ge140$; `h_arith.py`), at $d=538$ for $s=132$, at $d=294$ for $s=134$. So the theorem has content only from $d=282$, and at the threshold only for much larger $d$. The limits in the table are for fixed $s$ with $d\ge2s$ (so $s'=s$).

### 1.3 The cap $d/2$ is unnecessary

$2^{R-d}\le2^{-s'}$ needs only $s'\le d-R$. With $s'=\min(s,d-R)$ the exponent for $s=d-O(\sqrt d)$ improves from $4d^{1.5}$ to $(2\sqrt2+o(1))d^{1.5}$. Cosmetic.

### 1.4 Random quartics

[SKETCH] in w45 closes in three lines. Number of $n\times n$ alternating matrices of corank $\ge c$ is at most $4\cdot2^{c(n-c)}\cdot2^{\binom{n-c}2}$ (choose the radical, then a form on the quotient), so $\Pr[\mathrm{corank}\ge c]\le4\cdot2^{-\binom c2}$. Contraction by $w\wedge\lambda$ is a linear surjection $\Lambda^4\to\Lambda^2((V/\langle w,\lambda\rangle)^*)$, so for $\tau$ uniform each pair contraction is uniform on $n=d-2$ dimensions. A union bound over $\le2^{2d}$ pairs gives $s\ge d-2-c$ with $\binom c2\ge2d+\omega(1)$, i.e. $s\ge d-2\sqrt d-O(1)$ whp. `h_check.py` §4 checks the corank bound for uniform alternating $10\times10$ matrices.

Note: `check_pins.py` reports a *sampled* minimum of pair ranks. That is an upper bound on $s$, not an estimate: exact $s$ of random forms at $d=8,9,10,11$ is 2 (`h_check.py slow` §2), while the sampled figure at $d=10,12,14$ is near $d-4$. This is expected: at these sizes the union bound over $\approx2^{2d}$ pairs is what makes $s$ small. §6 of w45 should not be read as evidence about $s$ at those sizes. The theorem is unaffected.

### 1.5 Relation to prior work in this project

The algorithm is `w35-cubic.md` §3.6 / w17 §4 fact 1 ("guess images of $t$ vectors, $L$ is determined, verify"). The content of H is the pair-rank existence bound under the hypothesis on $s$. Correctly hedged in §7 of w45.

## 2. Blow-up analysis (S1, Prop 1, Cor 2)

**Source checks (PDFs read directly).** GQ Thm B: verbatim "d-Tensor Isomorphism reduces to Algebra Isomorphism. If the input tensor has size $n_1\times\dots\times n_d$, then the output algebra has dimension $O(d^2n^{d-1})$ where $n=\max\{n_i\}$" (§9, p.40). GQ Remark 9.1: verbatim, over $\mathbb F_q$: at least $q^{n^d-dn^2}$ orbits, at most $q^{N^3}$ algebras of dimension $N$, "Thus we need $N^3\gtrsim n^d$, whence $N\gtrsim n^{d/3}$", stated as a "rigorous lower bound on the size blow-up of any kernel reduction". GQ OQ 10.8: verbatim. GQ IV Thm 1.10 (the five 3-way actions, linear length, including action 5 = structure constants of algebras) and Thm 2.1 (TI to alternating matrix space isometry, linear): verbatim, and GQ IV has no $d>3$ result (grep). All as the document says.

**Prop 1 and Cor 2.** Correct counting. Two sharpenings (not corrections): with $L=n_1+n_2+n_3$ the target has at most $q^{(L/3)^3}$ tensors per format, so $L\ge3n^{4/3}(1-o(1))$; for quartics $L\ge3(d^4/24)^{1/3}(1-o(1))$.

**Gap in the conclusion's wording.** "The cubic results cannot propagate to degree 4 through *any* kernel reduction unless $\beta<3/2$" is true only for a 3-TI bound expressed as a function of $L$ alone, one field, one-input kernel maps. Counting is about strings and orbits, not running time, so:
- Field: a kernel reduction to 3-TI over $\mathbb F_{q^k}$ has $q^{kL^3}$ strings, so $L^3k\ge n^4$; with a bound $(q^k)^{\tilde O(L^\beta)}$ the composition is $q^{\tilde O(kL^\beta)}\ge q^{\tilde\Omega(n^{4\beta/3})}$ since $\beta\le3$, so the conclusion survives. Say so.
- Format-sensitive bounds escape. Format $(3,n^2,n^2)$ has $\ge q^{n^4}$ orbits (counting permits a kernel reduction from 4-TI), and every instance of that format is solved in $q^{9}\mathrm{poly}(n)$ by enumerating $\mathrm{GL}_3$ and running Brooksbank–Luks. No such reduction is known, but "any kernel reduction" must not be read as excluding it.

**Fix.** State Cor 2 as: if 3-TI is solved in $2^{\tilde O(L^\beta)}$ *uniformly over formats of total length $L$*, then the bound obtained by composing with any kernel reduction (one input, same field) is no better than $2^{\Omega(n^{4\beta/3})}$ as a function of $n$; it is $o(n^2)$ only if $\beta<3/2$. With this, the threshold statement is sound, the current $\beta=3/2$ is exactly the threshold, and the $L=O(n^3)$ published route gives $2^{\tilde O(n^{4.5})}$ as claimed.

## 3. T1

Re-derived the slice identity: if $T\circ(P_1,P_2,P_3,P_4)=T'$ then $P_3^{\mathsf T}A(P_1)_{ij}P_4=B(P_2)_{ij}$, indexed tuples of $n_1n_2$ matrices of size $n_3\times n_4$. Conversely equality of canonical forms gives a pair $(P_3,P_4)$. QS Thm 1.1 (PDF p.4): "randomized Las-Vegas algorithm to compute a canonical form of a matrix tuple in $M(n\times m,\mathbb F_q)^\ell$ under the equivalence relation in $\mathrm{poly}(n,m,\ell,\log q)$", and QS define a canonical form as producing the same output on equivalent inputs (p.2; §8 proof sentence: "the outputs for $A$ and $A'$ are the same"). The left-right action there is $LAR^{-1}$, which covers $P_3^{\mathsf T}AP_4$. Bound $\sum_i|\mathrm{GL}(n_i,q)|\le2q^{\max(n_1,n_2)^2}$ and the witness from Brooksbank–Luks are right.

I did not re-derive QS's 96-page proof; T1 is sound conditional on it. Also noted: the *collision* method is exactly the birthday-with-canonical-forms pattern in NQT24 cited by QS on p.3 ("canonical forms for tensors are used as an isomorphism invariant for birthday paradox-based algorithms"); T1 is the 4-tensor instance of that template with QS's forms, not a new technique. **Verdict: sound mod QS.**

## 4. T2 and T2′

### 4.1 Hand proof (⇐)

Line-by-line, correct, including the two parts the author could not test. Step 1: $Z_0=\{z:\mathrm{rk}<m\}$ needs $m>n_2$ (it is). Step 2: conciseness in factor 2 gives $Y_L$ as the annihilator of $S(\cdot,\cdot,Z_0)$. Step 3: the claim on left kernels of rank-$m$ elements is exactly right: rank-one patterns are stars by $C_4$-freeness, $X_{\ne i}$ supports a $\ge2$-dimensional space of rank-$m$ elements by $\deg\ge2$, $u^\perp$ with $|\mathrm{supp}\,u|\ge2$ supports a one-dimensional space by $C_4$-freeness. Step 4: $P$ preserves $D$ because it maps the common radical of $T$ to that of $T'$; $B$ and $R$ are well defined on the quotient/restriction. Factor-3 conciseness is not needed, harmless. Padding with zero tensors for $h<9$ is fine (joint radicals unaffected).

Notation clash: $R$ is used for the gadget tensor, the third matrix and the restriction of $P_Z$. Fix.

### 4.2 Exact tests

`tiso.c` decides isomorphism of two $n_X\times n_Y\times n_Z$ tensors over $\mathbb F_2$ with no structural assumption: rank of all $2^{n_Z}$ slice combinations, backtracking on $P_Z$ (rank equality is necessary), exact linear solve for $(P_X,P_Y)$ at each complete $P_Z$. Ground truth: brute force over $\mathrm{Aut}_{\text{side}}(H)\times\mathrm{GL}(n_1)\times\mathrm{GL}(n_2)\times\mathrm{GL}(n_3)$. The doc's construction is used with any bipartite $H$; the proof gives $T'_i=T_{\pi(i)}\circ(P,B,R)$ with $\pi\in\mathrm{Aut}_{\text{side}}(H)$, so non-rigid $H$ are valid tests of the mechanism.

| Instance | Pairs | Result |
|---|---|---|
| Controls: random $5\times5\times4$ tensors, planted isomorphism / one-bit perturbation | 30 + 30 | 30 found iso; 30 classified non-iso |
| $C_6$, $(n_1,n_2,n_3)=(1,1,1)$ exhaustive; $C_8$; theta$(1,5,7)$ (rigid, $h=6$, $|E|=13$) | 49, 225, 3969 | 0 disagreements |
| $C_6$ at $(1,1,2)$, $(2,1,1)$, $(1,2,1)$, exhaustive | 1764 each | 0 disagreements |
| theta $(1,1,2)$, $(2,2,1)$ ($m=3$), samples | 720, 260 | 0 disagreements |
| Doc's own $H_9$, $(1,1,1)$, sample pairs | 20 | 0 disagreements |

The harness detects broken variants: replacing $H$ by the 4-cycle $C_4$ produces 4 false isomorphisms in 9 pairs ($(0,1)$ vs $(1,1)$ etc.), so $C_4$-freeness is doing work and the test is not vacuous. (Dropping the extra padding dimension $m=\max(n_1,n_2)$ produced no disagreement at $(1,1,1)$ on $C_8$; that is too small to matter and I do not claim padding is necessary there.)

Exhaustive by rank-profile class (same-profile pairs solved by the exact search; pairs with different rank profiles are non-isomorphic by that invariant alone), `t2_full.py`:

| Instance | Tuples | Same-profile pairs solved | Result |
|---|---|---|---|
| Doc's own $H_9$, $(1,1,1)$, $m=2$: dims $18\times19\times21$ | all 511 concise | 511 profile classes, one tuple each, so all 130 305 pairs of distinct tuples are non-isomorphic and all 511 reflexive pairs solved ISO | **0 disagreements** |
| theta$(1,5,7)$ rigid, $(1,1,2)$ | all 3906 concise | 13 887 | **0 disagreements** (216 non-isomorphic with equal profile, by exact search) |
| $C_6$, $(2,2,1)$, $m=3$: $9\times11\times7$ | all 3780 concise | 355 626 | **0 disagreements** (69 984 non-isomorphic with equal profile, by exact search) |

These exercise $m\ge2$ (rigidity of the blocks $X_i$), which `check_graph.py` (pattern stabilizers only, $m=1$) could not.

**Verdict: T2 sound.** T2′ is arithmetic: $2^{h^2}$ for $P_1$, then $T2$ with $h\ge9$ padding; $h=o(n^{1/3})$ ✓. Conditional on 3-TI$_2$ as stated.

## 5. T3 and T3′

### 5.1 Hand proof (⇐)

Line-by-line, correct. Steps 1–2 are machine-verified per instance in the tests below (low-rank set of $\Phi$ exactly $\Phi_Q$; common radical exactly $U$). Step 3: $F\circ S$ has no $u^2$ terms, so no $Q$ component; the cross term forces $(Pu)^{(i)}=L^{-\mathsf T}\sum_j\beta_{ij}u^{(j)}$. Step 4: the $u$-square part matches $\sum_j\beta_{ij}Q^{g_j}_{L^{-1}a}$ (Frobenius additivity of squares and linearity of $a\mapsto Q^j_a$). Step 5: polars, $x$-diagonals, $(*)$ of w35 §2.3 apply coordinatewise; $(*)$ was the point of the w35 machinery and is exact.

Convention slip (no mathematical effect): with $f_i\circ L=\sum_j\beta_{ij}g_j$ and $\tilde g_i=f_i\circ L$, the needed block relabel is $T_\beta$ (with $(Tu)^{(i)}=\sum_j\beta_{ij}u^{(j)}$), not $T_{\beta^{-1}}$; `check_tuple.py` reports "inv" because it uses $g_i=\sum_j\beta_{ij}(f_j\circ L)$, i.e. the opposite convention. Fix the sentence.

### 5.2 Exact tests of (⇐)

`t3_check.py` decides isometry exactly: after verifying Steps 1–2 on the instance, every $S$ has $S(U)=U$, and for each $L\in\mathrm{GL}(n,2)$ the condition $\Phi(f)\circ S\subseteq\Phi(g)$ is linear over $\mathbb F_2$ in $(C,P,$ span coefficients$)$; solved exactly. Truth: brute force over $(L,\beta)$ on truth tables (all lower-order terms included).

| Family | Coverage | Result |
|---|---|---|
| $n=3,a=2$: all 16384 tuples, 12288 concise, 40 orbits of $\mathrm{GL}_3\times\mathrm{GL}_2$ | invariant (polar rank, #zeros) over all $\binom{40}2+40$ pairs; remaining 178 same-invariant pairs solved exactly | **0 disagreements** (40 isometric, 138 non-isometric); 40/40 planted $(L,\beta)$ found isometric |

| $n=3,a=3$: all 2097152 tuples, 1835008 concise, 166 orbits of $\mathrm{GL}_3\times\mathrm{GL}_3$ | same invariant: 7 classes; 4013 same-invariant pairs; 60 solved exactly (15 reflexive, 45 others, random) | **0 disagreements** (15 isometric, 45 non-isometric) |

| $n=4,a=2$, random concise tuples (truth by brute force over $20160\cdot6$ pairs) | one planted $(L,\beta)$ pair; one quadratic-flip pair with equal invariants, all 20160 $L$ solved; 5 more flip pairs (separated by the invariant) | **0 disagreements** |

Harness sensitivity: the broken variant with $\ell_i$ dropped from $F^i$ produces false isometries on 32–34 of 40 pairs that are truly inequivalent, so it can see the failure mode. All Steps 1–2 facts were verified per instance before relying on $S(U)=U$.

### 5.3 T3′

T3 assumes $f_i(0)=0$; T3′ does not state it (as an implicit hypothesis it is fine; as written for general cubics it does not follow). If $f_i(0)=c_i\neq0$ the quartic $\sum y_if_i$ has a term $\sum c_iy_i$ (constant $c_i$ in the tuple), and T3's construction has no slot for it. Add "$f_i(0)=0$" to T3′ (or handle the constant vector; the obvious $t^2$ gadget does not work directly, since then $F^i\circ S$ can pick up $u$-squares). With $f_i(0)=0$, T3′ is correct: images of $(V_0,Y)$ enumerated in $\le2^{2ad}$ ways, the shape and conciseness of the restriction are invariants, T3 on the $O(an)$-size output, GIQS Thm 1.2 applies with $m+N=O(an)$; $a=o(d^{1/3})$ gives $2^{o(d^2)}$ ✓.

**Verdict: T3 sound; T3′ sound with the added hypothesis.**

## 6. Proposition B

Correct. Each ordered $k$-tuple restricts $f$ to a function in $\mathbb F_2^k$ of degree $\le4$ (at most $2^{\sum_{i\le4}\binom ki}$ possibilities), so at most $(2^{kd}+1)^{2^{\sum_{i\le4}\binom ki}}$ histograms; at least $2^{\binom d4-d^2}$ orbits; pigeonhole. The inequality needs $2^{\sum_{i\le4}\binom ki}(kd+1)<\binom d4-d^2$, i.e. $k^4/24(1+o(1))\le3\log_2d-O(\log\log d)$, which is the stated $k\le(72\log_2d)^{1/4}(1-o(1))$. `h_arith.py` computes the largest $k$ that passes the printed inequality for $d=2^{10},\dots,2^{800}$: $k=4,5,6,7,8,8,11,15$ against $(72\log_2d)^{1/4}=5.2,\dots,15.5$. Note the true sum is slightly below $k^4/24$ for moderate $k$ (it equals $k^4/24-k^3/12+O(k^2)$), so the bound is not tight in the $1-o(1)$ but the statement as written is safe. **Verdict: sound, and as the paper says, a counting artifact.**

## 7. Novelty and sources

Verified directly: GQ (Thm B, Rmk 9.1, OQ 10.8), GQ IV (Thms 1.10, 2.1), QS (Thm 1.1; the canonical-form definition), Li–Li–Qiao–Tao–Wang arXiv:2604.00591 v2 (Theorem 1.3).

**Misdescription.** §1 of w45 says the 4-tensor algorithm of 2604.00591 works "via eigenvalue-free slices". It does not. Their 4-tensor algorithm (Thm 1.3, §4) is polynomial time poly$(n,q)$ for $q$ fixed and $n$ large, on a fraction at least $3q^{-9}/4096$ of inputs, via the left and right kernel codes of a corank-3 flattening $n^2\times n^2$ matrix. Eigenvalue-free counting belongs to their Theorem 1.2 and §6 (matrix code conjugacy). Fix the sentence; the $1/q^{\Theta(1)}$ fraction is right. Both Ma–Liu–Huang (ePrint 2026/1665, abstract text only, not fetched) and Li–Li–Qiao–Tao–Wang are average-case and do not bear on T1.

**Prior art searches** (web, 2026-11-09): collision/birthday on canonical forms for 4-tensors; tuple-of-tensors to one tensor with linear size; degree-4 Boolean equivalence algorithms. Found only what QS already cites (canonical-form birthday attacks at 3-tensors, NQT24) and the GQ IV linear-length gadget programme; nothing stating T1, T2, T3 or H. Searches were web-only and limited; "not found" means exactly that. As the author hedged, T1 and the Theorem H algorithm are templates instantiated, T2 is GQ-style gadgetry at linear size, T3's novelty is the $P=\beta\otimes L^{-\mathsf T}$ tensor structure forced by the pairing.

## 8. The strongest statements I would sign

1. **Theorem H (corrected).** $f,g$ quartic, $s=s(\tau_f)\ge2$: $f\circ L=g$ decided and all $L$ produced in $2^{td}\mathrm{poly}(d)$, with the printed $R,m,b,t$. Valid for all $d\ge4$, with $t=(2\sqrt2+o(1))d/\sqrt{s'}$ as $s'\to\infty$. $s$ is even. Beats w17 Thm B ($t/d\to c_s<1/4$) for even $s\ge132$ (printed parameters), and for $s\ge130$ taking $R=8$; $s=128$ does not, with any choice here. For finite $d$ (printed parameters): $d\ge282$ suffices for every $s\ge140$; $s=132$ needs $d\ge538$.
2. **Random quartics.** $\tau$ uniform: $s\ge d-2\sqrt d-O(1)$ whp (proved here, §1.4), so random quartics decided in $2^{(2\sqrt2+o(1))d^{1.5}}$ with the relaxed cap (or $2^{4d^{1.5}}$ as printed).
3. **Blow-up.** A 3-TI bound $2^{\tilde O(L^\beta)}$ *uniform in the format* composed with a one-input kernel reduction gives an upper bound for 4-TI no better than $2^{\Omega(n^{4\beta/3})}$ in $n$; it is $o(n^2)$ only if $\beta<3/2$. Not a statement about format-sensitive algorithms.
4. **T1.** 4-TI in $(|\mathrm{GL}(n_1,q)|+|\mathrm{GL}(n_2,q)|)\mathrm{poly}$, conditional on QS Thm 1.1.
5. **T2** (⇒ and ⇐), and T2′ conditional on 3-TI$_2$.
6. **T3**; T3′ with the added $f_i(0)=0$, conditional on GIQS Thm 1.2.
7. **Prop B** as stated.

## 9. Reproduce

All commands use `nice`, one process. Solver built with `gcc -O2 -o tiso docs/redteam-w45-code/tiso.c` outside the tree.

```
python3 -I docs/redteam-w45-code/h_arith.py
python3 -I docs/redteam-w45-code/h_check.py
python3 -I -u docs/redteam-w45-code/t2_check.py /path/to/tiso   # ~3 min
python3 -I -u docs/redteam-w45-code/t2_full.py  /path/to/tiso   # ~30 min, exhaustive families of section 4.2
python3 -I -u docs/redteam-w45-code/t3_check.py quick           # n=3,a=2; ~1 min
python3 -I -u docs/redteam-w45-code/t3_check.py full            # adds n=3,a=3 capped pairs
python3 -I -u docs/redteam-w45-code/t3_check.py n4              # n=4,a=2 pair tests
```

**What these tests do not show.** T2 is exact only at very small $(n_1,n_2,n_3)$ and $h\le9$; T3 exact at $n=3,a\le3$ and two pairs at $n=4$. Theorem H is exercised on $d\le9$ for $s$ and lemma identities, where the theorem's actual parameters give $t>d$ (it has content only from $d=282$), so no test touches the regime where H beats $2^{d^2/4}$. $s$ is exact only for $d\le11$. The experiments of w45 §6 (`ir_quartic.c`) were not re-run.
