# Quartic Boolean functions and 4-tensor isomorphism: state of the art, partial algorithms, and what blocks more

Branch `w45-quartic`, 2026-11-09. Code: `docs/w45-code/` (`check_graph.py`, `check_tuple.py`, `check_pins.py`, `ir_quartic.c`).

**Labels.** [PROVEN] complete argument here plus cited theorems. [SKETCH] gaps listed. [CONDITIONAL: X] proven under hypothesis X. [SPECULATION] opinion.
**Hypotheses.** GIQS = Grochow–Ivanyos–Qiao–Sun arXiv:2610.00874 (unrefereed; Thm 1.2 = quadratic-form space isometry over $\mathbb F_2$ in $2^{O((m+n)^{1.5})}$, §4 of `redteam-w35-w34.md` notes one repairable defect). 3-TI$_2$ := 3-tensor isomorphism over $\mathbb F_2$ of total length $L$ in $2^{\tilde O(L^{1.5})}$ (w35 E(ii), conditional on GIQS and GQ IV Thm 2.1).

Notation: $V=\mathbb F_2^d$; a *quartic* is $f:V\to\mathbb F_2$ of degree $\le4$, with top form $\tau_f\in\Lambda^4V^*$ (iterated polarization, alternating). Equivalence is $f\circ L=g$, $L\in\mathrm{GL}(d,2)$ (affine: enumerate $2^d$ translations). Throughout, targets are $2^{o(d^2)}$; "brute force" is $2^{d^2/4+O(d)}$ (w17 Thm B).

---

## 0. Summary

**Target reached? No.** No $2^{o(d^2)}$ algorithm for general quartics, and no CFI-type barrier. What exists at the end:

| # | Statement | Status |
|---|---|---|
| S1 | **Blow-up is real and essential.** Grochow–Qiao $d$-TI $\to$ algebra iso has output dimension $O(d^2n^{d-1})$ (their Thm B); any kernel reduction needs $L\gtrsim n^{d/3}$ (their Rmk 9.1). Consequence: a 3-TI algorithm $2^{\tilde O(L^{\beta})}$ gives $2^{o(n^2)}$ for 4-TI *through any kernel reduction* only if $\beta<3/2$; the current best $\beta=3/2$ is **exactly** the threshold (§1.1). | [PROVEN] (counting, elementary) |
| T1 | **4-TI in $q^{n^2}\mathrm{poly}$**: two-sided collision using Qiao–Sun canonical forms (§2.1), replacing w17's $q^{2n^2}$. | [PROVEN] mod Qiao–Sun FOCS 2024 |
| T2 | **Tuple-to-single 3-tensor reduction of linear size**: an $h$-tuple of $n\times n\times n$ tensors over $\mathbb F_2$ under simultaneous $\mathrm{GL}^3$ reduces to one 3-tensor of total length $O(hn)$ (§2.2) | [PROVEN] |
| T2′ | Corollary: format $h\times n\times n\times n$ 4-TI over $\mathbb F_2$ in $2^{h^2+\tilde O((hn)^{1.5})}$; $o(n^2)$ for $h=o(n^{1/3})$ | [CONDITIONAL: 3-TI$_2$] |
| T3 | **Tuples of cubics up to $\mathrm{GL}_a$ mixing** reduce to one space of quadratic forms, generalizing w35 Thm B: concise $a$-tuples on $\mathbb F_2^n$ give a space of $a(n+1)$ forms on $n(a+1)$ variables; equivalence iff isometry (§3) | [PROVEN] (forward direction machine-tested; reverse hand-proved) |
| T3′ | Quartics of the shape $f(x,y)=\sum_{i\le a}y_if_i(x)$ ($f_i$ cubic, concise tuple) have $\mathrm{GL}(d,2)$-equivalence in $2^{O(ad)+\tilde O((ad)^{1.5})}$, so $2^{o(d^2)}$ for $a=o(d^{1/3})$ | [CONDITIONAL: GIQS Thm 1.2] |
| H | **Rank dichotomy, first half.** Let $s=s(\tau)$ be the minimum rank of pair contractions $\tau(w,\lambda,\cdot,\cdot)$ over independent $(w,\lambda)$. Then equivalence is decided deterministically in $2^{(2\sqrt2+o(1))d^2/\sqrt{\min(s,d/2)}}\mathrm{poly}(d)$. Beats $2^{d^2/4}$ for $s\ge 128$; for $s=\Theta(d)$ (random quartics, [SKETCH]) gives $2^{O(d^{1.5})}$ (§4) | [PROVEN] |
| B | Weak barrier: pigeonhole shows inequivalent quartics with equal histogram of restrictions to $k$-tuples for $k\le(72\log_2d)^{1/4}(1-o(1))$ (§5) | [PROVEN], easy |
| — | "Affine CFI", low-rank-branch recursion, degree-preserving 4-TI $\le$ quartic | **not achieved**; where they break in §5–6 |

Novelty check: searches (2026-11-09) found neither T2, T3, H nor the 4-TI collision bound stated; each is close to known techniques and is hedged in §7.

## 1. State of the art (checked 2026-11-09, PDFs read directly unless noted)

* **3-TI completeness and blow-up.** Grochow–Qiao, arXiv:1907.00309 (SICOMP 2023). Theorem B: "$d$-Tensor Isomorphism reduces to Algebra Isomorphism. If the input tensor has size $n_1\times\cdots\times n_d$, then the output algebra has dimension $O(d^2n^{d-1})$", $n=\max n_i$. Their Remark 9.1 gives the counting lower bound $N\gtrsim n^{d/3}$ (over $\mathbb F_q$, $q^{N^3}\ge q^{n^d-dn^2}$) on the size of any kernel reduction to algebras, and Open Question 10.8 asks for $\mathrm{poly}(d)\,n^{d/3(1+o(1))}$. So yes, 3-TI is complete for all $d$-TI under polynomial reductions, and at $d=4$ the published blow-up is $n^3$ (algebra dimension $N=O(n^3)$, and AlgIso reduces to 3-TI with linear length by GQ IV Thm 1.10, so the total length is $L=O(n^3)$).
* **3-TI algorithms.** IMQSZ (FOCS 2024) $q^{\tilde O(\ell^{1.5})}$ matrix-space equivalence (Thm 3.2), and Sun STOC 2023. Odd characteristic via IQ19. Over $\mathbb F_2$: GIQS conditional route, plus Sun arXiv:2611.05920 (class-2 $p$-groups $N^{O((\log N)^{25/26}\log\log N)}$, weaker exponent, independent).
* **4-TI worst case.** No algorithm with exponent $o(n^2)$ found in any search. Brute force: $q^{2n^2}$ (w17). **Improved here to $q^{n^2}$** by collision with canonical forms (§2.1). Average-case: Li–Li–Qiao–Tao–Wang arXiv:2604.00591 (read: polynomial on a $1/q^{\Theta(1)}$ fraction of 4-tensors via eigenvalue-free slices; they still call the problem TI-complete in the worst case); Ma–Liu–Huang eprint 2026/1665 (average-case nullity one; **not read: the PDF fetch returned a bot-check page, so I relied on its search snippet only and did not attempt to circumvent it**).
* **Canonical forms for matrix tuples.** Qiao–Sun, arXiv:2409.12457, FOCS 2024, Thm 1.1: a Las Vegas algorithm computing a canonical form of matrix tuples under left-right action in $\mathrm{poly}(n,m,\ell,\log q)$ time. Read directly. This is new input not used in w17.
* **Rank notions.** Partition rank, slice rank, analytic rank. Cohen–Moshkovitz (Duke 2023): PR$\le$ constant$\cdot$AR over large fields; over $\mathbb F_2$ only polynomial relations (Janzer, Milićević; from memory, not re-read). **No algorithmic use for isomorphism found** in the searches; the partition rank decompositions are non-canonical, as w17 §4.3 noted.
* **Bounded-rank upper bounds and proof-complexity barriers.** Galesi–Grochow–Pitassi–She CCC 2023 (arXiv:2305.19320): over any field, $n\times n\times n$ TI instances require PC degree $\Omega(n)$ to refute; Sum-of-Squares degree $\Omega(n)$ over $\mathbb R$; reduction from CFI-based GI lower bounds. This is the closest thing to a CFI barrier for tensors; note it shows PC-style refutation is exponential while IMQSZ succeeds, i.e. the PC barrier does not bind algorithms like Sun's. Their Section with an upper bound for bounded-rank tensors: read only via search snippet.
* **Group-WL analogues.** Brachter–Schweitzer (LICS 2020, arXiv:2003.13745): CFI-based class-2 groups of exponent $p$, but WL-II dimension *bounded by 3*. So the obvious "lift CFI to groups" does not produce a WL lower bound; the natural linear-algebra object is not a CFI barrier. Other works: arXiv:2212.11247 (Mekler's construction applied to CFI). I did not find a linear-algebraic CFI (this is hedged, absence of evidence).
* **Quartic / RM cosets.** Classification tables (RM cosets $R(4,6)/R(1,6)$ etc.; Braeken et al. eprint 2004/248, 2005/025; Gillot–Langevin arXiv:2208.02469): practical $n\le$ 10-ish via invariants; no asymptotic worst-case statement. Quartic form equivalence appears only inside the Agrawal–Saxena / TI framework.

### 1.1 Why the blow-up kills propagation [PROVEN]

**Proposition 1.** Let $\Phi$ be a kernel reduction (many-one, injective on isomorphism classes) from 4-TI on format $n^{\times 4}$ over $\mathbb F_q$ to 3-TI on total length $L$. Then $L\ge(1-o(1))\,n^{4/3}$ up to a constant. The same holds for reductions from quartic Boolean equivalence on $\mathbb F_2^d$: number of $\mathrm{GL}(d,2)$-orbits $\ge 2^{\binom d4-d^2}$, number of 3-tensors $\le2^{L^3}$, so $L\ge(1-o(1))(d^4/24)^{1/3}=(1-o(1))\,d^{4/3}/24^{1/3}$.

*Proof.* Count orbits: $4$-tensors $q^{n^4}$, group $\le q^{4n^2}$, so at least $q^{n^4-4n^2}$ classes; the target has $\le q^{L^3}$. Injectivity on classes gives $L^3\ge n^4-4n^2$. ∎

**Corollary 2 (threshold).** A 3-TI algorithm of time $2^{\tilde O(L^\beta)}$ composed with any kernel reduction gives 4-TI in $2^{\tilde O(n^{4\beta/3})}$ at best; $o(n^2)$ requires $\beta<3/2$. With today's $\beta=3/2$ the *optimal* reduction gives $2^{\tilde O(n^2)}$, i.e. no gain; the published reduction ($L=O(n^3)$) gives $2^{\tilde O(n^{4.5})}$, far worse than brute force. For quartic Boolean equivalence the same computation gives $2^{\tilde O(d^2)}$ at best, with the constant hidden in the $\tilde O$. **So the cubic results cannot propagate to degree 4 through any kernel reduction unless the 3-TI exponent improves below 3/2.** Turing reductions that enumerate may evade this count; §2 and §4 are of that kind.

A measure-of-input remark: 3-TI's best algorithm costs $2^{\tilde O(\mathrm{bits}^{1/2})}$ and 4-TI's brute force is already $2^{O(\mathrm{bits}^{1/2})}$, which is another way of seeing why no size-respecting reduction helps.

---

## 2. Upper bounds for 4-tensors

### 2.1 Theorem T1: 4-TI in $q^{n^2}$ [PROVEN mod Qiao–Sun]

**Theorem T1.** 4-TI of format $n_1\times n_2\times n_3\times n_4$ over $\mathbb F_q$ is decided, with a witness, in Las Vegas time $(|\mathrm{GL}(n_1,q)|+|\mathrm{GL}(n_2,q)|)\,\mathrm{poly}(n,\log q)\le q^{\max(n_1^2,n_2^2)}\mathrm{poly}$ and that much space, enumerating the two smaller factors.

*Proof.* For $P_1\in\mathrm{GL}(n_1)$ define the indexed matrix tuple $A(P_1)_{ij}=T(P_1e_i,e_j,\cdot,\cdot)$; for $P_2\in\mathrm{GL}(n_2)$ define $B(P_2)_{ij}=T'(e_i,P_2^{-1}e_j,\cdot,\cdot)$. Substituting $x_2\mapsto P_2^{-1}x_2$: $T\circ(P_1,P_2,P_3,P_4)=T'$ iff for all $i,j$, $P_3^{\mathsf T}A(P_1)_{ij}P_4=B(P_2)_{ij}$ (slices in factors 3,4). So $T\cong T'$ iff some $A(P_1)$ and $B(P_2)$ are in the same left-right orbit as *indexed* tuples, i.e. have equal Qiao–Sun canonical forms (arXiv:2409.12457 Thm 1.1). Tabulate $\mathrm{Can}(A(P_1))$ over $P_1$, look up each $\mathrm{Can}(B(P_2))$. A collision gives $P_1,P_2$ and, by re-solving the left-right equivalence (Brooksbank–Luks), $P_3,P_4$. ∎

The exponent $n^2$ replaces w17's $2n^2$. It does not change the scale ($o(n^2)$ remains open). Note the same trick applied with a further enumeration inside factor 1 alone is no gain; bidirectionality is what buys the factor of 2.

### 2.2 Theorem T2: tuples of 3-tensors reduce to one 3-tensor, linear size [PROVEN]

*Problem TUPLE3.* Given $h$-tuples $(T_1,\dots,T_h),(T'_1,\dots,T'_h)$ of tensors in $\mathbb F_2^{n_1}\otimes\mathbb F_2^{n_2}\otimes\mathbb F_2^{n_3}$, decide whether $\exists(P,Q,R)\in\mathrm{GL}(n_1)\times\mathrm{GL}(n_2)\times\mathrm{GL}(n_3)$ with $T_j\circ(P,Q,R)=T_j'$ for all $j$ (indices $j$ pinned).

**Theorem T2.** TUPLE3 with $h\ge9$ reduces in polynomial time to a single 3-TI instance on three spaces of total dimension $O(h(n_1+n_2+n_3))$. For $h<9$ pad with zero tensors.

*The graph.* $H=H_h$: bipartite on $\{X_1,\dots,X_h\}\sqcup\{Y_1,\dots,Y_h\}$, edges $X_iY_i$, $X_{i+1}Y_i$ (indices mod $h$, a $2h$-cycle) and chords $X_1Y_4$, $X_2Y_6$. Properties for $h\ge9$ (all checked by `check_graph.py` for $h\le60$; hand proof for all $h$ below): (a) connected, $\deg\ge2$; (b) $C_4$-free; (c) the only side-preserving automorphism is the identity. Hand proof of (c): the degree-3 vertices are $D=\{X_1,X_2,Y_4,Y_6\}$; the graph contracts to a multigraph on $D$ whose arcs are the chords (length 1) and the four cycle arcs of lengths $X_1X_2:2$, $X_2Y_4:5$, $Y_4Y_6:4$, $Y_6X_1:2h-11$. A side-preserving automorphism permutes $D$ preserving sides and arc lengths. Swapping $X_1\leftrightarrow X_2$ forces $Y_4\leftrightarrow Y_6$ (chord neighbours) and sends arc $X_2Y_4$ (length 5) to $X_1Y_6$ (length $2h-11$): impossible for $h\ne8$. Fixing $X_1,X_2$ and swapping $Y_4,Y_6$ sends length-5 arc to a length-1 chord: impossible. So $\phi$ fixes $D$, hence every arc, hence $V(H)$. $C_4$-freeness: a 4-cycle would need a chord together with a length-3 path between its ends; the cycle distances are at least 7 for $h\ge9$ and chord pairs share no 4-cycle.

*The tensor.* Preprocess: remove common radicals in each of the three factors (both tuples must then have the same dimensions; a tuple equivalence maps radicals to radicals and lifts freely), so assume concise. Let $m=\max(n_1,n_2)+1$. Pad each $X_i$ to $X_i=\mathbb F_2^{m}=\mathbb F_2^{n_1}\oplus D$ where $T_j$ ignores $D$. Spaces:
$X=\bigoplus_iX_i$ (dim $hm$), $\;Y=Y_0\oplus\bigoplus_{j}Y_j$ ($Y_0=\mathbb F_2^{n_2}$, $Y_j=\mathbb F_2^m$), $\;Z=Z_0\oplus C$ ($Z_0=\mathbb F_2^{n_3}$, $C=\mathbb F_2^{E(H)}$ with basis $c_{ij}$ for edges $(i,j)$). Define
$$S_T(x,y,z)=\sum_{i=1}^hT_i(x_i,y_0,z_0)+\sum_{(i,j)\in E(H)}c_{ij}\langle x_i,y_j\rangle,\qquad y=(y_0,(y_j)),\ z=(z_0,(c_{ij})).$$
Note the $T_i$ share $Y_0,Z_0$ automatically; only factor 1 must be synchronized.

**Theorem T2 (precise).** $(T_j)\cong(T_j')$ as tuples iff $S_T\cong S_{T'}$ as 3-tensors.

*Proof.* ($\Rightarrow$) Given $(P,Q,R)$ (acting on padded $X_i$ by $P$ on $\mathbb F_2^{n_1}$, identity on $D$): $P_X=\mathrm{diag}(P,\dots,P)$, $P_Y=\mathrm{diag}(Q,P^{-\mathsf T},\dots)$, $P_Z=\mathrm{diag}(R,\mathrm{id}_C)$.

($\Leftarrow$) Let $(P_X,P_Y,P_Z)$ with $S_T\circ(P_X,P_Y,P_Z)=S_{T'}$. Write the $z$-slice as a matrix on $X\times Y$:

1. *$Z_0$ is canonical.* For $z\in Z_0$ the slice has column space in $Y_0$, rank $\le n_2<m$. For $z=(z_0,c)$, $c\ne0$: the block on $X\times\bigoplus Y_j$ is $A(c)\otimes I_m$ ($A(c)$ the biadjacency matrix with entries $c_{ij}$), so rank $\ge m$. Hence $Z_0=\{z:\mathrm{rk\,slice}(z)<m\}$ and $P_Z$ preserves it.
2. *$Y_L=\bigoplus_{j}Y_j$ is canonical.* By conciseness of the tuple in factor 2, functionals $S(x,\cdot,z_0)$, $z_0\in Z_0$, span the dual of $Y_0$ only (annihilator $=Y_L$), so $P_Y(Y_L)=Y_L$. Restricting to $X\times Y_L\times(Z/Z_0)$ gives the fixed tensor $R=\mathbf A\boxtimes I_m$ (slices $A(c)\otimes I_m$, $A(c)$ the pattern matrices of $H$): $R\circ(P_X,P_Y|_{Y_L},\bar P_Z)=R$.
3. *Automorphisms of $R$.* Rank-$m$ elements of the slice space $\mathcal S=\{A\otimes I_m\}$ correspond to rank-1 pattern matrices, which, $H$ being $C_4$-free, are exactly stars $e_iv^{\mathsf T}$ (supp $v\subset N(X_i)$) or $ue_j^{\mathsf T}$. A rank-$m$ element $e_iv^{\mathsf T}\otimes I$ has left kernel $X_{\ne i}=\{x:x_i=0\}$; an element $ue_j^{\mathsf T}\otimes I$ with $|\mathrm{supp}\,u|\ge2$ has left kernel of the form $\{\sum u_ix_i=0\}$. Using $\deg\ge2$: a codimension-$m$ subspace $K\subset X$ is the left kernel of a space of $\ge2$-dimensional rank-$m$ elements iff $K=X_{\ne i}$ for some $i$ ($C_4$-freeness caps the others at dimension 1). So $P_X$ permutes the $X_{\ne i}$, hence the blocks $X_i$ (since $X_i=\bigcap_{i'\ne i}X_{\ne i'}$), with invertible blocks; dually $P_Y|_{Y_L}$ permutes blocks $Y_j$, $\pi,\pi'$. Each edge element $E_{ij}\otimes I$ maps to the unique element of $\mathcal S$ supported on the image block pair (over $\mathbb F_2$ the only nonzero scalar is 1), so $(\pi,\pi')$ is a side-preserving automorphism of $H$, hence trivial, and $P_i^{\mathsf T}Q_j=I_m$ on each edge. Connectedness gives $P_i=P$ for all $i$, $Q_j=P^{-\mathsf T}$.
4. *Recover the tuple.* $P$ preserves $D$ (radical of the padded tuple, by conciseness), inducing $\bar P\in\mathrm{GL}(n_1)$; $P_Y$ induces an invertible $B$ on $Y/Y_L\cong Y_0$ (i.e. $P_Y|_{Y_0}$ has $Y_0$-component $B$); $P_Z$ restricts to $R$ on $Z_0$. Evaluating on $X\times Y_0\times Z_0$ (where the gadget part vanishes): $T_j\circ(\bar P,B,R)=T'_j$. ∎

**Corollary T2′.** [CONDITIONAL: 3-TI$_2$] 4-TI of format $h\times n\times n\times n$ over $\mathbb F_2$ decides in $2^{h^2+\tilde O((hn)^{1.5})}$: enumerate $P_1\in\mathrm{GL}(h,2)$, then run TUPLE3 via T2 and 3-TI$_2$. It is $2^{o(n^2)}$ for $h=o(n^{1/3})$. The same holds for odd $q$ with IMQSZ replacing 3-TI$_2$ except the torus handling in Step 3 must be redone (not done).

*Why not all of 4-TI?* The reduction demands $h\ge n$ to capture a full 4-tensor (each slice is one 3-tensor): then total length is $\Omega(n^2)$, giving $2^{\tilde O(n^3)}$, and one cannot enumerate fewer slices without losing information. This is §4's core tension.

Verification: `check_graph.py` proves (a–c) for $h\le 60$, and exhaustively computes the stabilizer of pattern spaces (stabilizer pairs in $\mathrm{GL}\times\mathrm{GL}$ on $C_6$, $C_8$ patterns are exactly the graph automorphisms: 6 and 8 respectively). The direct (⇐) on padded instances was not machine-tested at full size ($|\mathrm{GL}(hm)|$ too large); the proof is by hand.

---

## 3. Theorem T3: tuples of Boolean cubics to one quadratic-form space

Generalizes w35 Thm B to tuples, with the mixing group $\mathrm{GL}_a$ arising exactly as the action on $y$ in the quartic $\sum y_if_i$.

Let $f=(f_1,\dots,f_a)$ be Boolean functions of degree $\le3$ on $V=\mathbb F_2^n$, $f_i(0)=0$. Write $f_i=C_i+Q_i+\ell_i$ (multilinear cubic, quadratic, linear), $\Gamma^{i}_b$ the zero-diagonal lift (w35 §2.1) of $\tau_{f_i}(b,\cdot,\cdot)$. Call the tuple **concise** if $\bigcap_i\mathrm{Rad}\,\tau_{f_i}=0$. On $W=V\oplus U^{(1)}\oplus\dots\oplus U^{(a)}$ ($\dim U^{(i)}=n$, total $N=n(a+1)$), define
$$Q^{i}_b(x,u)=\Gamma^{i}_b(x)+(b^{\mathsf T}u^{(i)})^2,\qquad F^{i}(x,u)=Q_{i}(x)+\ell_i(x)+x^{\mathsf T}u^{(i)},$$
$\Phi(f)=\langle Q^i_{e_k},F^i:i\le a,k\le n\rangle$ (dimension $a(n+1)$, all forms linearly independent).

**Theorem T3.** Let $f,g$ be concise $a$-tuples on $V$. Then there are $L\in\mathrm{GL}(n,2)$, $\beta\in\mathrm{GL}(a,2)$ with $f_i\circ L=\sum_j\beta_{ij}g_j$ for all $i$, iff the spaces $\Phi(f),\Phi(g)$ are isometric ($\exists S\in\mathrm{GL}(W)$: $\Phi(f)\circ S=\Phi(g)$). [PROVEN]

*Proof.* ($\Rightarrow$) Set $\tilde g_i=f_i\circ L$. Exactly as in w35 Thm B applied coordinate-wise with a *common* $L$: $S_0(x,u)=(Lx,(L^{-\mathsf T}u^{(i)}+C_ix)_i)$, $C_i=L^{-\mathsf T}N^i$, satisfies $Q^{f_i}_{Lb}\circ S_0=Q^{\tilde g_i}_b$, $F^{f_i}\circ S_0=F^{\tilde g_i}$. Then a block relabel of the $u^{(i)}$ by $\beta^{-1}$ transports $\Phi(\tilde g)$ to $\Phi(g)$ (the sign/convention is confirmed by `check_tuple.py`: $T_{\beta^{-1}}$ works on 60/60 random mixed instances).

($\Leftarrow$) Let $\Phi(f)\circ S=\Phi(g)$. Write $\Phi_Q$ for the span of the $Q$'s.

1. *Rank separation.* Polars of elements of $\Phi_Q$ have rank $\le n$ (supported on $V\times V$). An element with some $F^i$-component restricted to $V\oplus U^{(i)}$ has polar block $\left(\begin{smallmatrix}*&I\\I&0\end{smallmatrix}\right)$, rank $\ge2n$. So $S$ maps $\Phi_Q(f)$ onto $\Phi_Q(g)$.
2. *Radical.* Conciseness makes the common radical of polars of $\Phi_Q$ exactly $U=\bigoplus U^{(i)}$ on both sides. So $S(U)=U$: $S(x,u)=(Lx,Cx+Pu)$.
3. *$F$ gives the tensor structure.* $F^{f_i}\circ S\in\Phi(g)$. Pure-$u$ diagonal monomials appear only in $Q^{g_j}_b$ with coefficients matching $b$, and $F^{f_i}\circ S$ has none, so $F^{f_i}\circ S=\sum_j\beta_{ij}F^{g_j}$ with no $Q$ terms. Cross terms: $x^{\mathsf T}L^{\mathsf T}(Pu)^{(i)}=\sum_j\beta_{ij}x^{\mathsf T}u^{(j)}$, so $(Pu)^{(i)}=L^{-\mathsf T}\sum_j\beta_{ij}u^{(j)}$: $P=\beta\otimes L^{-\mathsf T}$. **The tensor-product structure is forced by the pairing.** $\beta$ is invertible since $P$ is.
4. *Squares pin the index.* The $u$-square part of $Q^{f_i}_a\circ S$ is $\sum_j\beta_{ij}((L^{-1}a)^{\mathsf T}u^{(j)})^2$, forcing $Q^{f_i}_a\circ S=\sum_j\beta_{ij}Q^{g_j}_{L^{-1}a}$ (match $u$-squares in $\Phi_Q(g)$ basis-by-basis).
5. *Conclusion.* Set $\tilde g_i=\sum_j\beta_{ij}g_j$. As $\Gamma$, $Q$, $\ell$ are linear in the function, Step 4's polars give $\tau_{f_i}\circ L=\tau_{\tilde g_i}$, and the $x$-diagonal part gives $L^{\mathsf T}C^{(i)}=N^{i}$ exactly as w35 Thm B; the $x$-part of $F$ then gives $(Q_{f_i}+\ell_{f_i})(Lx)+x^{\mathsf T}N^ix=(Q_{\tilde g_i}+\ell_{\tilde g_i})(x)$, and $(*)$ of w35 §2.3 gives $f_i\circ L=\tilde g_i$. ∎

For $a=1$, $\beta$ trivial, this is w35 Thm B. The new content is that the pairing, not a gadget, forces $P=\beta\otimes L^{-\mathsf T}$ and so simultaneity of the $L$'s, and that $\beta$ is exactly the action on the quartic's $y$-variables.

**Corollary T3′.** [CONDITIONAL: GIQS Thm 1.2] Let $f(x,y)=\sum_{i\le a}y_if_i(x)$ and $g(x,y)=\sum y_ig_i(x)$ on $\mathbb F_2^{n+a}$ with concise cubic tuples. The block-equivalence (under $\mathrm{GL}_n\times\mathrm{GL}_a$) decides in $2^{\tilde O((an)^{1.5})}$ time ($m+N=O(an)$). For equivalence under all of $\mathrm{GL}(d,2)$, $d=n+a$: enumerate the images of a decomposition $V_0\oplus Y$ ($\le 2^{2ad}$ pairs) and test each with block equivalence, total $2^{O(ad)+\tilde O((ad)^{1.5})}$, which is $2^{o(d^2)}$ for $a=o(d^{1/3})$.

**Limitations.** (i) Conciseness is required; non-concise tuples need a radical-elimination analogue of w35 Thm C, only sketched by the obvious gadget $\sum t\,x^{\mathsf T}y$ (would need the same care in the rank argument). (ii) GIQS is decision-only, so no witness or automorphism group; (iii) the class is $y$-linear; adding pure-$x$ cubics $C_0(x)$ or $y_iy_jq_{ij}(x)$ needs pinned labels the space version does not give (§6 lead 2).

Tests: `check_tuple.py` confirms the forward direction, the rank separation, and the radical identification on 51 concise instances ($n\le6$, $a\le3$) and the $\beta$-mixed action on 60 instances. The ($\Leftarrow$) direction is hand-proved only: exhaustive search over $\mathrm{GL}(9,2)$ at $n=3,a=2$ was not attempted.


---

## 4. Theorem H: a rank dichotomy, first half

For $\tau\in\Lambda^4V^*$ let $s(\tau)=\min\mathrm{rk}\,\tau(w,\lambda,\cdot,\cdot)$ over linearly independent $w,\lambda\in V$. (Note $\mathrm{Rad}\,\tau\ne0$ forces $s=0$; apply this after quotienting $\mathrm{Rad}\,\tau$, with lower-order data handled separately.) The pair contraction is the correct analogue of Sun's pencil at $d=4$: individualizing vectors, *and the first object that is a matrix* is the contraction by two vectors.

**Theorem H.** [PROVEN] Let $f,g$ be quartics with top forms $\tau_f,\tau_g$, and $s=s(\tau_f)\ge 2$, $s'=\min(s,d/2)$. Set $R=\lceil\sqrt{s'/2}\,\rceil$, $m=\lceil(Rd+4)/(s'-1)\rceil$, $b=\lceil(d+2)/R\rceil$, $t=2m+b=(2\sqrt2+o(1))d/\sqrt{s'}$. Then $f\circ L=g$ is decided, and all $L$ produced, in deterministic time $2^{td}\mathrm{poly}(d)$ from the ANFs. In particular:
* $s\ge(128+\varepsilon)$: time $2^{(1-\delta)d^2/4}$, beating w17 Thm B;
* $s=\Theta(d)$ (includes almost every quartic: for a uniformly random alternating 4-form, the pair matrices are random alternating, so $s\ge d-O(\sqrt d)$ with high probability [SKETCH: tail of rank of random alternating matrices, union bound over $\le2^{2d}$ pairs]): $2^{O(d^{1.5})}$.

**Proof.** Let $u_1,\dots,u_{2m},b_1,\dots,b_b$ be uniform independent in $V$ and set $A=(u_j)$, and call the $m$ disjoint pairs $(u_{2l-1},u_{2l})$. Fix $w\ne0$; let $\rho=\tau(\cdot,\cdot,\cdot,w)$, $\phi_l=\rho(u_{2l-1},u_{2l},\cdot)\in V^*$.

*Pair-rank lemma.* For a subspace $W\subset V^*$ of dimension $R-1$ and uniform independent $v,v'$: $\Pr[\rho(v,v',\cdot)\in W]=\mathbb E_{\lambda\in W^\perp}2^{-\mathrm{rk}\,\tau(\lambda,w,\cdot,\cdot)}\le 2^{R-d}+2^{-s}\le2^{1-s'}$. Indeed $1[\phi\in W]=\mathbb E_{\lambda\in W^\perp}(-1)^{\phi(\lambda)}$ and $\mathbb E_{v,v'}(-1)^{\rho_\lambda(v,v')}=2^{-\mathrm{rk}\,\rho_\lambda}$ for an alternating form; here $\rho_\lambda=\tau(\cdot,\cdot,\lambda,w)$ has rank $\ge s$ unless $\lambda\in\{0,w\}$. The two exceptional $\lambda$ contribute at most $2/|W^\perp|=2^{R-d}$. (This Fourier identity is the same one giving $2^{-\mathrm{AR}}$ below.)

*Step 1 ($A$ good).* If $\mathrm{rank}\{\phi_1,\dots,\phi_m\}<R$ then all lie in some $(R-1)$-dimensional $W$; independence of the $m$ pairs and the union bound over at most $4\cdot2^{(R-1)(d-R+1)}\le2^{(R-1)d+2}$ subspaces gives probability at most $2^{(R-1)d+2}2^{(1-s')m}\le2^{-d-2}$. Union over the $2^d$ values of $w$: with probability $\ge3/4$, every nonzero $w$ has $\mathrm{rank}\{\rho^w(u_j,u_k,\cdot)\}_{j<k\le 2m}\ge R$.

*Step 2 ($B$ kills every $w$).* Given such $A$, fix $w\ne0$. The conditions $\tau(u_j,u_k,b_i,w)=0$ for all pairs and all $i$ say every $b_i$ is in a subspace of codimension $\ge R$; probability $\le2^{-Rb}\le2^{-d-2}$. Union over $w$: with probability $\ge3/4$, conditioned on good $A$, no nonzero $w$ annihilates all functionals $\tau(u_j,u_k,b_i,\cdot)$. Hence with probability $\ge1/2$ these functionals span $V^*$ — the choice of $(A,B)$ for $\tau_f$ exists.

*Algorithm.* (Swapping $f,g$ as needed: $s$ is an invariant of the orbit.) Find a good $(A,B)$ for one side by enumeration (or randomly): $2^{td}\mathrm{poly}(d)$. For each of $2^{td}$ candidate images $(u'_j,b'_i)\in V^{t}$ under $L$ on the other side, the functionals determine $L$ (or $L^{-1}$) uniquely, since they span $V^*$ on $f$'s side and transform by $L^{\mathsf T}$; verify $f\circ L=g$ on ANFs in $\mathrm{poly}(d)$. ∎

*Remarks.* (1) Mixed-order contractions (triples only) are all the proof uses; adding quadratic and cubic derivative data can only help. (2) $\mathbb E_{a,b}2^{-\mathrm{rk}\,\tau(a,b,\cdot,\cdot)}=2^{-\mathrm{AR}(\tau)}$ (analytic rank of the 4-form viewed as a 4-tensor), so large AR means *most* pairs have high rank. The hypothesis of H is the much stronger *every* pair. The next section is about that gap.

### 4.1 Where the dichotomy breaks (the second half is missing)

Attempted low-rank branch: if $s(\tau)=s_0$ is small, pick a low-rank pair $(w,\lambda)$. The radical $\mathrm{Rad}\,\tau(w,\lambda,\cdot,\cdot)$ is a canonical subspace of codimension $\le s_0$ *given the pin* of $(w,\lambda)$ (cost $2^{2d}$). Then:

* *Recursion on the restriction is too expensive.* It is the same as enumerating a flag: extending $L$ from a codimension-$s_0$ subspace costs $2^{s_0d}$ per level over $d/s_0$ levels, total $2^{d^2}$ (the same $1/4$ only after bidirectional collision, i.e. no gain). Sun escapes this because in his case the *absence* of further individualization progress exhibits a *canonical* shrunk subspace (from the submodularity of $W\mapsto\dim\mathcal AW-\dim W$) requiring no enumeration of a complement. I could not find a submodular certificate for pair-contraction rank.
* *What is the right structure?* Let $S_r$ be the set of pairs with rank $\le r$. If $S_r$ spans $V$ and carries many pairs then $\mathbb E2^{-\mathrm{rk}}$ is large, so AR small, and (Janzer/Milićević) $\mathrm{PR}(\tau)\le\mathrm{poly}(\mathrm{AR})$: $f$ has a decomposition $\sum\ell_ic_i+\sum q_jq_j'$ with few terms. But the decomposition is non-canonical, so one cannot pin the pieces, and the "thin locus" case (a few low-rank pairs, $\tau$ otherwise generic) is not covered at all. The missing statement (a *canonical* regularity lemma for 4-forms): every $\tau$ has an invariant subspace chain of length $\mathrm{poly}(1/\varepsilon)$ on whose quotients $\tau$ is, or induces, an $\varepsilon$-regular form. Whether this exists is exactly the gap between w17 §4.3's "new mathematical object" and a real algorithm. [SPECULATION]

### 4.2 Other attempts, briefly

| Attempt (exact statement) | Outcome |
|---|---|
| Contract with $a$ vectors, solve cubic tuple via T3. Needs: $f$ determined by the $a$-tuple of derivatives plus lower-order pinned data | Exponent budget $(an)^{1.5}=o(n^2)$ forces $a=o(n^{1/3})$, but a generic quartic has $\ge n$ independent cubic derivative directions, so an $a$-tuple does not determine $f$; pinned tuples only give necessary conditions. T3 applies only when $f$ *is* linear in a small block. |
| Theorem H-style individualization plus GIQS on a residual | Not developed; the residual after $t$ pins with $\mathrm{rk}<$ full is a tuple of up to $\binom t2$ quadratics plus cubic data on $W$ under $\mathrm{GL}(W)$; those tuples have size $\gg n^{1/2}$ exactly when H's hypothesis fails. |
| Low-rank 4-tensor decomposition (2+2 and 1+3) directly | Needs a canonical object; the known partition-rank bounds give only existence. |
| Canonize $f$ under a bigger subgroup than Borel using 2+2 flattening ($\mathrm{GL}(A)\times\mathrm{GL}(B)$ Levi) | The Levi factors are independent, so enumeration of $\mathrm{GL}(A)$ alone leaves $\mathrm{GL}(B)$ on $f_{2,2}$, a bi-quadratic in Levi factors; no polynomial canonical form for that known (it is exactly matrix-tuple space equivalence over $\mathrm{GL}(B)\times\mathrm{GL}(A)$, which is TI-complete-flavoured). Same $d^2/4$. |

---

## 5. Barrier side

**What I tried.** (a) Local indistinguishability ($k$-dimensional restrictions and derivative histograms) for pairs built by twisting local pieces on a sparse base with gauge signs. Failure mode: the group $\mathrm{GL}(d,2)$ has no locally supported symmetries to parametrize a twist (a linear map that is the identity on a coordinate subspace of codimension $k$ is forced to act on the rest), and rigidifying the base to act only by permutations needs gadgets that themselves increase dimension; I could not produce a family with verified parity obstruction. (b) Lifting CFI: reductions from GI to linear equivalence of Boolean functions with **linear** dimension blow-up, which would give a WL-type lower bound $\Omega(d)$; none found, and the natural route via 4-TI gadgets has polynomial blow-up (GI$\le$TI, GQ). Also Brachter–Schweitzer's lifted-CFI class-2 groups have WL-dim 3 (above): the naive lift fails.

**What is provable.** Define $\mathrm{Hist}_k(f)$ = the multiset, over ordered $k$-tuples $(v_1,\dots,v_k)$, of the restriction $f|_{\langle v_1,\dots,v_k\rangle}$ in the coordinates $v_i$ (a Boolean function on $\mathbb F_2^k$).

**Proposition B.** [PROVEN] For $k\le(72\log_2d)^{1/4}(1-o(1))$, there exist quartics $f,g$ on $\mathbb F_2^d$ with $\mathrm{Hist}_k(f)=\mathrm{Hist}_k(g)$ and $f\not\cong g$. *Proof:* at least $2^{\binom d4-d^2}$ orbits against at most $(2^{kd}+1)^{2^{\sum_{i\le4}\binom ki}}$ possible histograms. ∎ This is a counting artifact (it says nothing about refinement or explicit families). It does match the intuition that low-order local statistics cannot identify a quartic, and matches the spirit of the classical "invariants of bounded degree don't separate" story; but it is not a CFI analogue.

**Honest statement.** No CFI-style barrier for the affine/tensor setting has been constructed here. Two calibrating remarks: (i) the PC barrier for 3-TI (GGPS) does not stop IMQSZ-type algorithms, so any barrier for the $o(n^2)$ algorithm must rule out algebraic reasoning, not just refutation-size measures; (ii) a true CFI barrier would need a family where *matrix-space shrunk-subspace and adjoint-algebra* computations (not only WL-type ones) lose: none is known even at $d=3$.

---

## 6. Experiments

`docs/w45-code/ir_quartic.c` (from `w17-affine-code/ir_affine.c`, added quartic families), run single-process `nice`, seconds per run. Measures: first-path depth, cells, tree size, leaves, automorphisms (equal leaves), excess = leaves/|Aut|. Families: random quartic ($\texttt{q4rand}$), homogeneous degree-4 only ($\texttt{q4top}$), product of 2 random quadratics, sum of 3 products, $e_4$, $y$-linear ($\texttt{liny}$: $y_0C_0(x)+y_1C_1(x)$), degree-4 Maiorana–McFarland ($\texttt{mm4}$, $k=8$), $k=6,7,8$ (some with node caps).

Results (all complete trees unless noted): random quartic, $k=6$–$8$: root discrete. $q4top$: $k=6$: depth 6, $\mathrm{Aut}$ 6144/1296, excess 1; $k=7,8$: root discrete. Products of two quadratics: depth 3–5, $\mathrm{Aut}$ 8–768, excess 1. $e_4$: depth $k$, $\mathrm{Aut}=S_k$ of order $k!$ (excess 1; $k=8$ timed out by leaf count). $\texttt{liny}$: excess 1 where complete; $k=6$ one seed capped at $3\cdot10^5$ nodes. $\texttt{mm4}$ $k=8$: depth 4, cells 120,119,8,2, $\mathrm{Aut}$ 7680, excess 1. $k=8$ Kronecker product ($\texttt{krn}$) timed out.

`check_pins.py` (forms on $d=10,12,14$): random forms and products: 6–7 random pins suffice (functionals span $V^*$), sampled pair-rank near $d-4$. Forms with disjoint-monomial or $x_1x_2\cdot q$ structure, or a radical: pins fail for $t\le d$ (pair ranks 0–2 or a big radical), exactly the low-$s$ regime of Theorem H.

**What these cannot show.** Everything is at $d\le14$, far below the regime where Sun's $2^{\tilde O(n^{1.5})}$, or any $d^{1+\Omega(1)}$ depth effect, could matter; the node counts are dominated by the sizes of automorphism groups. Excess 1 everywhere means "no non-automorphism leaf seen in explored trees"; there is no evidence either way about worst-case scaling. No locally-indistinguishable pair family was tested because none was constructed.

---

## 7. Novelty and leads

**Novelty checks.** Searches on: tuple-to-single 3-tensor reductions, 4-TI bounds, partition-rank-based isomorphism, Weisfeiler–Leman for tensors, and the Qiao–Sun canonical forms (found). T1 is a one-line application of [QS24] and T1's improvement over $q^{2n^2}$ was not found stated; T2 is close to GQ-style gadgetry (graph-with-rigidity gadgets are standard) but the explicit linear-size tuple-to-single reduction was not found; T3's $P=\beta\otimes L^{-\mathsf T}$ extension of w35 is new here in the sense of "not found"; H follows the Sun/IMQSZ individualization template (their Lemma 3.4) one dimension up, and analytic-rank Fourier identities are standard. **All marked as "not found", not as new.**

**Leads.**
1. *Canonical regularity for 4-forms* (§4.1): a statement implying that a low-pair-rank locus yields an invariant subspace without complement enumeration. This is the single missing object for a full dichotomy. Probably a new kind of "submodular certificate" (or a proof none exists).
2. *Extend T3 to all low-(1+3)-strength quartics*: $f=\sum_iy_iC_i(x)+\sum y_iy_jq_{ij}(x)+\dots$ with a pinned-label version of GIQS (the "tuple of spaces"), or a labelling gadget that respects the $\mathbb F_2$ quadratic structure. Then Theorem H plus T3 would handle all quartics of bounded strength.
3. *Degree-preserving 4-TI $\le$ quartic equivalence.* w17's C uses colourings of degree up to $K$. A degree-4 gadget (forcing the block decomposition via radicals/rank of pair contractions, in the style of w35 Thm C) would make the "quartic = the wall" statement a theorem: 4-TI $2^{\Omega(k^2)}$ $\Rightarrow$ quartic $2^{\Omega(d^2)}$. Not attempted to completion.
4. *Barrier: a CFI family where adjoint-algebra/shrunk-subspace computations lose at $d=3$ first*, then $d=4$.

**References (read directly unless stated).** Grochow–Qiao arXiv:1907.00309 (Thm B, Rmk 9.1, OQ 10.8); Qiao–Sun arXiv:2409.12457; Li–Li–Qiao–Tao–Wang arXiv:2604.00591; Brachter–Schweitzer arXiv:2003.13745; GQ IV arXiv:2306.16317 (linear-length; read for what it covers, not for $d$-tensors, which it does not address; grep confirms no $d>3$ results); Sun 2303.15412 and GIQS 2610.00874, IMQSZ via w35/redteam; Galesi–Grochow–Pitassi–She CCC 2023 arXiv:2305.19320 (abstract via search results only); Cohen–Moshkovitz Duke 2023 (via search results only); Janzer, Milićević (from memory); Ma–Liu–Huang eprint 2026/1665 (search snippet only; PDF fetch blocked by bot check, not circumvented).
