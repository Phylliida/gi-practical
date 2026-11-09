# Cubic Boolean equivalence in $2^{\tilde O(n^{1.5})}$: an exact reduction to quadratic-form space isometry over $\mathbb F_2$

Branch `w35-cubic`, 2026-11-09. Code: `docs/w35-cubic-check.py`.

**Labels.** [PROVEN] complete argument here plus cited textbook facts. [SKETCH] gaps listed.
[CONDITIONAL: X] proven under hypothesis X. [SPECULATION] opinion.

Notation: $V=\mathbb F_2^n$; $f:V\to\mathbb F_2$ of degree $\le 3$, $f(0)=0$ after normalization, with unique ANF $f=C_f+Q_f+\ell_f$ (multilinear cubic, quadratic, linear parts). Maps act by $f\mapsto f\circ L$. "Quadratic form" means a formal homogeneous degree-2 polynomial over $\mathbb F_2$, i.e. a Boolean function of degree $\le2$ with zero constant term ($x_i^2$ and $x_i$ are the same function, so a form is a function and conversely). $\mathrm{Pol}(q)$ is the polar bilinear form. **GIQS** = Grochow–Ivanyos–Qiao–Sun, arXiv:2610.00874v1 (1 Oct 2026, unrefereed). **IMQSZ** = Ivanyos–Mendoza–Qiao–Sun–Zhang (FOCS 2024). **GQ IV** = Grochow–Qiao part IV, arXiv:2306.16317. **IQ19** = Ivanyos–Qiao, SICOMP 2019 (read only as quoted in the others).

---

## 0. Summary

| # | Statement | Status |
|---|---|---|
| O | The characteristic-2 obstacle is exactly one step: the $*$-symmetric decomposition $X^*X=E$ inside the IQ19 subroutine (Sun Thm 1.3; IMQSZ §4.3, Prop. 4.9 and the following paragraph). Explicit failing instance on $\mathbb F_2^6$, $m=3$ (§1.2) | [PROVEN] (the instance); located by reading the sources |
| A | **Squares gadget.** Alternating matrix tuple/space isometry on $(n,m)$ reduces to quadratic-form tuple/space isometry on $(n+m,m)$ | [PROVEN] §2.2 |
| B | **Exact cubic reduction.** If $\mathrm{Rad}\,\tau_f=\mathrm{Rad}\,\tau_g=0$: $f\circ L=g$ for some $L\in\mathrm{GL}(n,2)$ iff the $(n+1)$-dimensional spaces of forms $\Phi(f),\Phi(g)$ on $\mathbb F_2^{2n}$ are isometric | [PROVEN] §2.3 |
| C | **Radical elimination.** $f^+(x,y,t)=f(x)+t\,x^{\mathsf T}y$ has $\mathrm{Rad}\,\tau=0$, and $f\sim g$ iff $f^+\sim g^+$ | [PROVEN] §2.4 |
| D | **Main theorem.** Decide $\mathrm{AGL}(n,2)$- or $\mathrm{GL}(n,2)$-equivalence of cubic Boolean functions in $2^{\tilde O(n^{1.5})}$ time, worst case, all cubics, exact (all lower-order terms) | [CONDITIONAL: GIQS Thm 1.2] §3 |
| E | Consequences mod the same hypothesis: alternating matrix tuple and space isometry over $\mathbb F_2$; 3-tensor isomorphism over $\mathbb F_2$ (mod GQ IV Thm 2.1); ATF equivalence over $\mathbb F_2$ (mod GQ IV Cor. 5.4 + Thm 2.1); all in $2^{\tilde O(L^{1.5})}$ | [CONDITIONAL] §3.2 |
| F | Unconditional: exact $\mathrm{GL}$-equivalence of cubics reduces, in time polynomial in $\lvert G\rvert=2^{O(n)}$, to Cayley-table isomorphism of 2-groups $G$ of Frattini class 2 | [PROVEN] mod Higman's criterion as cited in GIQS §3; §3.3 |
| G | T2 consequence: STS instances $X_\chi$ of w30 with $\chi$ cubic are decided in $2^{\tilde O(d^{1.5})}=n^{\tilde O(\sqrt{\log n})}$. Hard instances for T2, if any, have colourings of algebraic degree $\ge4$ | [CONDITIONAL: GIQS Thm 1.2] §5 |

The theorem is conditional on one five-week-old unrefereed preprint, whose proofs I read and partly audited (§3.4: one running-time overclaim, repairable, plus proofs I could not certify). Everything specific to cubics is elementary, proved by hand here, and tested by exact computation at small sizes (not formally verified). **No novelty claim**: the web-search tools were unavailable (session limit) when I tried to check prior art, so §3.5 records only what the four papers I read do and do not say.

---

## 1. The obstacle, pinned

### 1.1 Where characteristic 2 breaks

Reading Sun (arXiv:2303.15412) and IMQSZ, the algorithm has three phases.

1. *Individualization* (IMQSZ Lemma 3.4). Field-independent: the probability bound is proved for every $q$.
2. *Low-rank characterization* (IMQSZ Lemma 3.6, $\mathrm{ncrk}\le O(r\log r)$; shrunk subspaces). Field-independent: the proof handles small fields by passing to an extension. Together these reduce matrix space equivalence to Problem 3.7, then (Thm 3.10) to Cond-Alt-MTC, conditioned alternating matrix tuple congruence, with a factor $q^{(d+f)n}$.
3. *The tuple step* (IMQSZ Lemma 3.9, proved in §4.3). The conditioning reduction (Prop. 4.8) and the left-right equivalence step are unproblematic. The final sentence of §4.3 (paper p. 18) reads: $A,B$ are diagonally congruent iff there is $X\in\mathrm{DAdj}$ with $X^*X=E$, and "This $*$-symmetric decomposition problem admits a deterministic $\mathrm{poly}(n,m,\log q)$-time or a randomised $\mathrm{poly}(n,m,q)$-time solution **over finite fields of odd characteristics** [IQ19]". Sun's corresponding input is his Theorem 1.3 ($=$ IQ19 Thm 1.7), stated for $p>2$.

**On IMQSZ's route this is the only step I found that uses odd characteristic.** (Sun assumes $p>2$ globally, so for his lemmas this is a reading of GIQS Thm 2.7, not something I re-derived; see §3.4 item 6. IMQSZ Lemma 3.9 says "over finite fields" without restriction, but its proof in §4.3 depends on odd characteristic; GIQS PDF p.5 states this failure explicitly: the lifting "inherently involves dividing by 2, and can fail badly", "there can be solutions to the quotient problem that have no lifts".) GIQS Thm 2.7 confirms that the reduction part is valid for every prime. GQ IV's Thm 2.1 (TI to alternating matrix space isometry, linear size) does not divide by 2 in its proof; its block-diagonal variant Thm 2.5 needs and supplies a characteristic-2 clearing step, the $Y_u$ matrix (PDF p.17); footnote 10 records a characteristic-2 caveat only for Thm 6.1 (the direction I do not use).

The memo's reading (`w17-affine.md` §1) that "the tuple step fails" is accurate. Its proposed remedy (adapt GIQS's quadratic tuple algorithm to the alternating quotient) turns out not to need any adaptation (§2.2).

### 1.2 An explicit failing instance [PROVEN: hand argument for $Y^{\mathsf T}Y$, exhaustive search for non-congruence]

Let $C$ be a basis of all alternating $3\times3$ matrices. $A=C\otimes I_2$, $B=C\otimes\mathrm{Swap}$, $E=I_3\otimes\mathrm{Swap}$ on $\mathbb F_2^6$, with $m=3$. Then $A_iE=B_i$, so $(I,E)$ is a left-right equivalence; $B$ is alternating; $E^*=E$ in the adjoint algebra. But $Y^{\mathsf T}Y=\mathrm{Swap}$ has no solution over $\mathbb F_2$: a zero diagonal forces both columns of $Y$ to have even weight, so each is $00$ or $11$, and then the two columns are orthogonal. Exhaustive search confirms $A$ and $B$ are **not** congruent, with a positive control (`obstacle` section).

What the example shows is the *decision problem* the tuple step must solve; it is not a claim that $X^*X=E$ is always solvable in odd characteristic (over $\mathbb F_3$ the same $E$ also fails, since $\det\mathrm{Swap}=-1$ is a non-square). The difference is that IQ19 decides the equation for odd $q$ by a lifting argument over the radical of the adjoint algebra that divides by 2, and no such procedure is available over $\mathbb F_2$. Left-right equivalence plus the adjoint algebra does not settle congruence, and over $\mathbb F_2$ the published route to settling it is gone.

### 1.3 What is specific to cubics

Three facts govern the cubic problem (the last two [PROVEN] by direct expansion; the first is context).

* $f\mapsto\tau_f(a,b,c)=D_aD_bD_cf$ is a surjection $A_3\to\Lambda^3V^*$, where $A_3$ is the space of Boolean functions of degree $\le3$ with $f(0)=0$; kernel $A_2$ (the quadratic forms). The filtration $V^*\subset A_2\subset A_3$ is not expected to split $\mathrm{GL}(V)$-equivariantly for $n\ge3$ (it does split at $n=2$, via the invariant form $x^2+xy+y^2$). This is motivation only, is not re-proved here, and no proof below uses it.
* $D_a$ is equivariant but not linear in $a$: for $h_a(x):=f(x+a)+f(x)+f(a)$ one has $h_{a+b}=h_a+h_b+\tau(a,b,\cdot)$.
* The zero-diagonal lift $\Gamma_a$ of $\tau(a,\cdot,\cdot)$ (below) is linear in $a$ but not equivariant.

So the obvious approach, "contract to alternating bilinear forms and treat the lower-order part as a separate Dickson-type step", loses exactly the information an equivariant reduction needs. §2 shows that the two gadgets (squares and pairing) restore it exactly.

---

## 2. The reductions [PROVEN]

### 2.1 Notation and two identities

For $f=C+Q+\ell$, $C=\sum_{i<j<k}c_{ijk}x_ix_jx_k$, define
$$\Gamma_a(x)=\sum_{i<j<k}c_{ijk}\bigl(a_ix_jx_k+x_ia_jx_k+x_ix_ja_k\bigr),$$
a quadratic form in $x$ with **zero diagonal** (no $x_i^2$ terms), linear in $a$. $\mathrm{Pol}(\Gamma_a)=\tau(a,\cdot,\cdot)$.

**(I1)** $\Gamma_v(v)=C(v)$ for all $v$ (three equal terms; $3$ is odd).
**(I2)** $C(v+w)+C(v)+C(w)=\Gamma_v(w)+\Gamma_w(v)$ (expand one monomial).

Consequently $h_a(x)=\Gamma_a(x)+\Gamma_x(a)+\mathrm{Pol}(Q)(a,x)$.

### 2.2 Squares gadget (Theorem A)

**Theorem A.** Let $A=(A_i)$, $B=(B_i)$ be $m$-tuples of alternating $n\times n$ matrices over $\mathbb F_2$ with zero common radical, $q_i,q_i'$ any quadratic forms polarizing to $A_i,B_i$ (e.g. zero-diagonal lifts). Put $Q_i(x,u)=q_i(x)+u_i^2$ on $\mathbb F_2^{n+m}$, similarly $Q_i'$. Then:
(tuple) $\exists L\in\mathrm{GL}(n,2)$, $L^{\mathsf T}A_iL=B_i\ \forall i$ iff $\exists S\in\mathrm{GL}(n+m,2)$ with $Q_i\circ S=Q_i'\ \forall i$.
(space) $\exists L$ with $L^{\mathsf T}\langle A_i\rangle L=\langle B_i\rangle$ iff $\exists S$ with $\langle Q_i\rangle\circ S=\langle Q_i'\rangle$.

*Proof.* ($\Rightarrow$, tuple) $q_i(Lx)+q_i'(x)$ has zero polar, so equals $(c_ix)^2$ for a row $c_i$; put $S(x,u)=(Lx,Cx+u)$ with rows $c_i$; then $Q_i\circ S=q_i(Lx)+(c_ix)^2+u_i^2=Q_i'$. ($\Leftarrow$) The common radical of the polars of the $Q_i$ is $U=0\oplus\mathbb F_2^m$ (zero common radical on $V$), so $S(U)=U$ and $S(x,u)=(Lx,Cx+Pu)$. Comparing $u$-parts, $(P_iu)^2=u_i^2$ gives $P=I$; polars give $L^{\mathsf T}A_iL=B_i$. The space version is identical with $P=M$, $(M_iu)^2=\sum_jM_{ij}u_j^2$. ∎

(If the common radical is nonzero, first pass to a complement: isometry of the non-degenerate parts is equivalent, IMQSZ Prop. 4.10-type argument; standard.)

The asymmetry to note: this is "absorption". The square term $u_i^2$ forgives the unavoidable diagonal ambiguity of lifting an alternating matrix to a form. It is the opposite of the exactness we want for cubics; §2.3 obtains exactness by pairing.

### 2.3 Exact reduction (Theorem B)

For $f$ with $f(0)=0$ define on $W=V\oplus U$, $U=\mathbb F_2^n$, $\dim W=2n$, the $n+1$ forms
$$Q^f_i(x,u)=\Gamma^f_{e_i}(x)+u_i^2,\qquad F^f(x,u)=Q_f(x)+\ell_f(x)+x^{\mathsf T}u.$$
Linear extension: $Q^f_a=\Gamma^f_a(x)+(a^{\mathsf T}u)^2$. Let $\Phi(f)=\langle Q^f_1,\dots,Q^f_n,F^f\rangle$.

**Theorem B.** Let $f,g:V\to\mathbb F_2$ have degree $\le3$, $f(0)=g(0)=0$, $\mathrm{Rad}\,\tau_f=\mathrm{Rad}\,\tau_g=0$. Then there is $L\in\mathrm{GL}(n,2)$ with $f\circ L=g$ iff there is $S\in\mathrm{GL}(W)$ with $\Phi(f)\circ S=\Phi(g)$.

*Proof.* ($\Rightarrow$) Let $g=f\circ L$ and $\mathbf N_{ij}=\Gamma^f_{Le_i}(Le_j)$, $C=L^{-\mathsf T}\mathbf N$, $S(x,u)=(Lx,\,L^{-\mathsf T}u+Cx)$. For $b=L^{-1}a$,
$$Q^f_a\circ S=\Gamma^f_{Lb}(Lx)+(b^{\mathsf T}u)^2+\bigl(a^{\mathsf T}Cx\bigr)^2.$$
Since $\tau_g=\tau_f\circ L$, the forms $\Gamma^f_{Lb}\circ L$ and $\Gamma^g_b$ have equal polars, so they differ by a sum of squares $\sum_j\mathbf N_{bj}x_j^2$ with $\mathbf N_{bj}=\Gamma^f_{Lb}(Le_j)$ (the diagonal of $\Gamma^g_b$ is zero). The choice of $C$ cancels this exactly (recall $(a^{\mathsf T}Cx)^2=\sum_j(a^{\mathsf T}C)_jx_j^2$). So $Q^f_a\circ S=Q^g_b$.

For $F$: $F^f\circ S=(Q_f+\ell_f)(Lx)+x^{\mathsf T}\mathbf Nx+x^{\mathsf T}u$, using $L^{\mathsf T}C=\mathbf N$. It remains that as Boolean functions
$$x^{\mathsf T}\mathbf Nx=C_f(Lx)+C_g(x),\tag{$*$}$$
for then $(Q_f+\ell_f)(Lx)+x^{\mathsf T}\mathbf Nx=f(Lx)+C_g(x)=g(x)+C_g(x)=(Q_g+\ell_g)(x)$. Both sides of $(*)$ have degree $\le2$ and zero constant. On $e_j$: left $\mathbf N_{jj}=\Gamma^f_{Le_j}(Le_j)=C_f(Le_j)$ by (I1), right $C_f(Le_j)+0$. Polar coefficient at $(j,k)$: left $\mathbf N_{jk}+\mathbf N_{kj}$; right, by (I2), $\Gamma^f_{Le_j}(Le_k)+\Gamma^f_{Le_k}(Le_j)$, and $C_g$ contributes $0$ on weight $\le2$. $(*)$ holds.

($\Leftarrow$) Let $\Phi(f)\circ S=\Phi(g)$. The polars of elements of $\langle Q^f_i\rangle$ have rank at most $n$, while every element of $F^f+\langle Q^f_i\rangle$ has polar rank $2n$ (matrix $\begin{psmallmatrix}*&I\\I&0\end{psmallmatrix}$), so $S$ carries $\langle Q^f_i\rangle$ onto $\langle Q^g_i\rangle$. Common radical of the polars is exactly $U$ on both sides (here $\mathrm{Rad}\,\tau=0$ is used), hence $S(U)=U$ and $S(x,u)=(Lx,Cx+Pu)$ with $L,P$ invertible. Write $Q^f_a\circ S=Q^g_{Ra}$ with $R$ linear ($Q_a$ are linearly independent, and $R$ is bijective). Also $F^f\circ S=F^g+\sum_ic_iQ^g_i$.

Compare terms in $F^f\circ S$: it has no $u_i^2$ terms, so all $c_i=0$. Its $x$–$u$ cross term $x^{\mathsf T}L^{\mathsf T}Pu$ must equal $x^{\mathsf T}u$: $L^{\mathsf T}P=I$. In $Q^f_a\circ S$: the $u$-squares give $(a^{\mathsf T}Pu)^2=((Ra)^{\mathsf T}u)^2$, so $R=P^{\mathsf T}=L^{-1}$: **the index action on the slices is forced to be $L^{-1}$ by the squares and the pairing**, with no separate link gadget. Polars of $Q$ give $\tau_f\circ L=\tau_g$. The $x$-part of $Q$ gives $(a^{\mathsf T}Cx)^2=\Gamma^f_a(Lx)+\Gamma^g_{L^{-1}a}(x)$, which (zero diagonal of $\Gamma^g$) forces $L^{\mathsf T}C=\mathbf N$. The $x$-part of $F$ then gives $(Q_f+\ell_f)(Lx)+x^{\mathsf T}\mathbf Nx=(Q_g+\ell_g)(x)$. With $g':=f\circ L$: by $(*)$, $Q_{g'}+\ell_{g'}=(Q_f+\ell_f)\circ L+x^{\mathsf T}\mathbf Nx=Q_g+\ell_g$, and $\tau_{g'}=\tau_g$ forces $C_{g'}=C_g$. So $g=g'=f\circ L$. ∎

### 2.4 Radical elimination (Theorem C)

For $f$ on $V$ define $f^+(x,y,t)=f(x)+t\,x^{\mathsf T}y$ on $V^+=V\oplus V\oplus\mathbb F_2$ (dimension $2n+1$). Direct check: $\mathrm{Rad}\,\tau_{f^+}=0$.

**Theorem C.** For $n\ge2$ and $f,g$ on $V$ with $f(0)=g(0)=0$: $f\circ L=g$ for some $L\in\mathrm{GL}(n,2)$ iff $f^+\circ M=g^+$ for some $M\in\mathrm{GL}(2n+1,2)$.

*Proof.* ($\Rightarrow$) $M(x,y,t)=(Lx,L^{-\mathsf T}y,t)$. ($\Leftarrow$) The slice of $\tau_{f^+}$ at $v=(x,y,t)$ has rank $\ge2n$ if $t=1$ and rank $\le\mathrm{rk}\,\tau_f(x,\cdot,\cdot)+2\le n+1$ if $t=0$. Since $M$ conjugates slices, it preserves $H=\{t=0\}$, so $M(x,y,0)=(Ax+By,\,\cdot,\,0)$. Restricting $f^+\circ M=g^+$ to $H$ gives $f(Ax+By)=g(x)$ for all $x,y$. So $(x,y)\mapsto Ax+By$ is onto $V$ (projection of a bijection on $H$), $f$ is invariant under translation by $I=\mathrm{Im}\,B$, and $f\circ A=g$. Take $L\equiv A\pmod I$ bijective: $A$ induces a surjection $V\to V/I$, whose kernel has dimension $\dim I$; define $L=A$ on a complement and any isomorphism $\ker\to I$ on the kernel. Then $f\circ L=f\circ A=g$ by invariance. ∎

### 2.5 Composite statement

**Theorem (composite, [PROVEN]).** For cubic $f,g:\mathbb F_2^n\to\mathbb F_2$ with $f(0)=g(0)=0$ and $n\ge2$: $f\sim_{\mathrm{GL}}g$ iff the spaces $\Phi(f^+),\Phi(g^+)$ of $2n+2$ quadratic forms on $\mathbb F_2^{4n+2}$ are isometric. The reduction is polynomial in $n$. The map is $f\mapsto\Phi(f^+)$, no enumeration. For $\mathrm{AGL}(n,2)$: enumerate $t\in V$, test $f(t)=g(0)$ and $x\mapsto f(x+t)+f(t)$ against $g+g(0)$ ($2^n$ reductions).

### 2.6 How this answers the planned reduction

The brief's plan was: cubic $\to$ third derivative $\to$ tuples of alternating forms $\to$ tuple algorithm, then a separate Dickson-type step for the kernel. What actually happens:

* **The third-derivative step alone is insufficient**, and the separate step was the wrong shape. The fibre of $f\mapsto\tau_f$ is acted on by the (uncontrolled) group $\mathrm{Aut}(\tau)$, and GIQS is decision-only, so no generators are available to run Dickson under. Also quadratic-form tuple isometry already embeds in that fibre ($f=\sum_iy_iq_i(x)$, where the diagonal of $q_i$ appears as the degree-2 term $y_ix_j$) [SKETCH: the rigidity gadget pinning the $y$-block is not written]. So the lower-order part carries GIQS-level difficulty and cannot be a polynomial afterthought.
* **The kernel is folded into the same instance.** The form $F^f$ records the degree-$\le2$ part. Its transformation law under $L$ is twisted by $x^{\mathsf T}\mathbf Nx$, and the block $C$ forced by the squares gadget supplies exactly that twist; identity $(*)$ (from (I1), (I2)) says the twist equals what the ANF of $f\circ L$ requires. Exactness of the diagonal is then GIQS's job, which is what quadratic forms (as opposed to alternating matrices) are for.
* **No link gadget between slice index and variables is needed**: the $u_i^2$ terms and the pairing $x^{\mathsf T}u$ force the index action to be $L^{-1}$.
* **Does GIQS supply the required tuple congruence?** Yes in the form needed, via Theorem A for alternating tuples and directly for Theorem B, subject to §3.4.

---

## 3. The theorem, its status, and the corollaries

### 3.1 Theorem D [CONDITIONAL: GIQS Thm 1.2]

Assume GIQS Theorem 1.2: *given sequences of quadratic forms $f_1,\dots,f_m$ and $g_1,\dots,g_m$ in $n$ variables over $\mathbb F_2$, decide whether some invertible $S$ satisfies $\langle f_i^S\rangle=\langle g_i\rangle$, in time $2^{O((m+n)^{1.5})}$.*

**Theorem D.** Given cubic $f,g:\mathbb F_2^n\to\mathbb F_2$ in ANF, one can decide $\mathrm{GL}(n,2)$-equivalence and $\mathrm{AGL}(n,2)$-equivalence in time $2^{\tilde O(n^{1.5})}$, for every cubic, including degenerate $\tau$ and all lower-order terms. (GIQS states $O$ in the exponent, but its own Thm 2.7 has $\tilde O$ and the tail bound it quotes comes from IMQSZ's $h=O(\sqrt n\log n)$; see §3.4 item 6. I state $\tilde O$. Either way this is $2^{o(n^2)}$.)

**Status of the details.**

* *Decision only.* GIQS is decision. Search reduces to decision by the standard self-reduction (individualize one image at a time, $2^n$ candidates per basis vector, adding a rigidifying variable each time) [SKETCH: I did not write out the rigidifying gadget for quadratic-form spaces]. Full coset: not obtained.
* *Deterministic* insofar as GIQS is. The theorem statements give "an algorithm". The individualization step (IMQSZ Lemma 3.4) is phrased probabilistically but is used only via existence; the search over $L,R$ is exhaustive anyway. [not independently certified]
* Not a canonical form.

### 3.2 Corollaries of Theorem A [CONDITIONAL: GIQS Thm 1.2]

(i) Alternating matrix tuple congruence, and alternating matrix space isometry, over $\mathbb F_2$ of shape $(n,m)$, in $2^{\tilde O((n+m)^{1.5})}$ (Theorem A plus Thm 1.3, resp. 1.2).

(ii) 3-tensor isomorphism of total length $L$ over $\mathbb F_2$ in $2^{\tilde O(L^{1.5})}$, via GQ IV Thm 2.1 (TI $\le$ alternating matrix space isometry, linear size; I read the proof and it uses no division by 2, though I did not re-prove its Lemmas 4.1 and 5.2).

(iii) ATF equivalence over $\mathbb F_2$ in $2^{\tilde O(n^{1.5})}$, via GQ IV Cor. 5.4 (action $U\otimes U\otimes U$ to TI, linear) plus (ii). The ATF problem is a special case of action 4. The hypothesis on Cor. 5.4 includes FGS19 Thm 4.1; I did not re-verify it over $\mathbb F_2$. Same statement for ATF follows from Theorem D only in the exact form; ATF "modulo lower terms" is not literally a special case of Theorem D, so (iii) is the correct route. **This is the memo's lead 1 ("needs alternating tuple congruence over $\mathbb F_2$"), now resolved conditionally.**

### 3.3 Reduction to group isomorphism [PROVEN mod Higman]

Via GIQS §3: Higman's criterion (as cited there from Blackburn–Neumann–Venkataraman, Lemma 4.3) gives a bijection between isometry classes of subspaces of $Q(n,2)$ of dimension $m$ and isomorphism classes of 2-groups $G$ of Frattini class 2 with $G/\Phi(G)\cong\mathbb F_2^n$, $|\Phi(G)|=2^m$ (take the quotient of the relatively free group by the annihilator). Composing with the composite theorem: exact cubic equivalence on $n$ variables reduces to Cayley-table isomorphism of 2-groups of Frattini class 2 of order $2^{6n+4}$, polynomial in the table size for the affine problem up to the $2^n$ translation factor.

### 3.4 What I checked in GIQS

Read: §§1–2 (statements), §3, §4 (all of it), §5, §7, §8. Partly read: §6.

Findings.

1. **Thm 4.9, Step 3 of the Restricted Algorithm: running-time overclaim.** The algorithm as written enumerates *all* $S'\in M(d_f\times(\beta_0+\beta_1-d_f),\mathbb F_2)$, which is $2^{d_f(\beta_0+\beta_1-d_f)}$, not the claimed $2^{O((m-\alpha_0-\alpha_1)n)}$; $d_f$ can be $\Theta(n)$. **Repair.** The degenerate basis vectors are polar-radical and vanish on the $\le\alpha_0+\alpha_1$ forms, so $S'$ affects only the diagonal of the $m-\alpha_0-\alpha_1$ tail forms, through $\sum_iS'[i,j]a_i$, with $a_i=(f_{\alpha_0+\alpha_1+t}[i,i])_t$. Enumerating $S'$ only on a set of pivot rows for the matrix $(a_i)$ has the claimed cost. [SKETCH] The repair looks routine; it is not in the paper.
2. Fig. 1 Step 7 uses subscript $f_{\alpha_0+\alpha_1+i}$ with $i$ up to $\alpha_0+\alpha_1$, which overflows $m$; it should be $f_i$. Typo-level.
3. §6, Thm 6.2's connectivity argument under local operations is compressed ("By Theorem 2.3 and Theorem 5.1 ... such a local operation exists"; one line appears to say "non-zero" where "zero" is meant). I could not certify this proof.
4. Lemma 7.6 (bound $nD$ on $\dim A/\mathrm{Rad}\,A$) and the count in Thm 7.2: I checked the argument and found no problem. Lemma 8.7's count and Lemmas 8.4–8.6: read, no problem noticed, not checked line by line. Fact 7.5 (unipotent vector transporter) is a reconstruction of Luks–Miyazaki that I read but did not verify against those papers.
5. Lemma 4.16(2) ("$M_1=M_2$ and $N_1=N_2$ by construction") is stated with little proof. Not certified.
6. **Thm 2.7 is "rephrased" from papers that assume odd $p$, and its parameters are not consistent with later statements.** Sun's §2 opens "over $\mathbb F_p$ for a prime number $p>2$"; his Lemma 5.14 has exponent $n^{0.8}$, and the $n^{0.5}$ form needs IMQSZ's Lemmas 3.4 and 3.6. GIQS asserts the combination "continues to work over $\mathbb F_2$" without proof; I checked that IMQSZ Lemmas 3.4/3.6 are field-independent, but did not re-derive Sun's semi-canonical-form Lemmas 5.9–5.12 at $p=2$ (where "skew-symmetric" must be read as alternating). Separately, Thm 2.7 has $\tilde O$ in the exponent, while its tail bound $\le n^{0.5}$ and Thm 4.6's $O$ are stated without polylogs, although IMQSZ's $h=O(\sqrt n\log n)$ suggests the tail is $\tilde O(\sqrt n)$. This changes $O$ to $\tilde O$ in the conclusion and nothing else.
7. §6 proof of Thm 6.2: the claim that $X_i=0$ for $i<\beta$ is not justified where stated, but follows from block orthogonality plus the paper's non-degeneracy convention. The two-block exchange step is the part I could not certify; Appendix A's non-uniqueness of congruent block decompositions is exactly why it needs care.

**Bottom line:** the theorem I rely on is plausible and the proof architecture coheres, but I have not verified it. Theorem D is conditional on it, full stop.

### 3.5 What the four papers do and do not say (no novelty claim)

None of Sun, IMQSZ, GQ IV, GIQS states Theorem A, Theorem B, or Theorem D. GIQS says (PDF p.5) that previously "only a trivial algorithm" was known for alternating matrix tuple isometry in characteristic 2 and that Sun/IMQSZ "do not work for tensors over $\mathbb F_2$", and does not state the consequences in §3.2. Theorem A is a one-line observation that the authors may well regard as obvious or may have intended to state separately; I would not present it as a result without a careful literature check, which I could not perform (web tools at session limit).

### 3.6 Unconditional subclass [PROVEN]

Let $t(\tau)$ be the least $t$ such that some $t$-tuple $u_1,\dots,u_t$ has $\{\tau(u_i,u_j,\cdot)\}$ spanning $V^*$. Then exact $\mathrm{AGL}$-equivalence (full coset) is decidable in time $2^{(t(\tau)+1)n}\mathrm{poly}(n)$: guess $t$ images, $L$ is determined by the functionals, then check $f\circ A=g$ on the whole function. This is w17-affine §4 fact 1, and exactness is automatic because $L$ is fully determined. For random $\tau$, $t=O(\sqrt n)$ w.h.p. [SKETCH in w17], so generic cubics are $2^{O(n^{1.5})}$ unconditionally. This handles the generic instances; it says nothing about degenerate $\tau$ (e.g. $\tau=x_0\wedge\omega$ has $K\neq 0$ for all $O(\sqrt n)$-tuples).

---

## 4. Experiments

`nice python3 -I docs/w35-cubic-check.py` (pure Python, one process). Sections and results:

| Section | What is tested | Result | Broken variants (must be caught) |
|---|---|---|---|
| `identity` | (I1), (I2); forward direction of Thm B: $Q^f_a\circ S=Q^g_{L^{-1}a}$, $F^f\circ S=F^g$ exactly | 1345 random $(f,L)$, $n=3,\dots,10$: all pass | $C=0$: caught 115/120; no $x^{\mathsf T}\mathbf Nx$ correction: 113/120; linear part dropped from $F$: 106/120 |
| `reverse3` | Both directions of Thm B, all $64^2=4096$ pairs of functions on $\mathbb F_2^3$ with $\mathrm{Rad}\,\tau=0$. $S$ searched over all of $\mathrm{GL}(6,2)$ (pruning uses only invariants valid for any span isometry) against exact truth | 4096/4096 agree (1324 equivalent) | 300 sampled pairs. No $u_i^2$: 192 spurious, 0 missed. No pairing: 21 spurious, 70 missed. No $\ell$ in $F$: 88 spurious, 45 missed |
| `samples` | $n=5,6$, random $\mathrm{Rad}=0$: planted equivalent, and same $\tau$ with one quadratic term flipped (truth from exact search) | $n=5$: 12 planted, 12 perturbed; $n=6$: 2 and 2. All agree; of the 14 perturbed, 10 are truly inequivalent | none (Thm B's broken variants are tested above) |
| `gadget` | Thm C exactly on orbit representatives of all functions: $n=2$ (4 orbits), $n=3$ (10 orbits), $f^+$ on $5$ and $7$ variables, plus 10 conjugates per orbit | All 16 and 100 representative pairs agree; all 40 and 100 conjugates found | Replace $t\,x^{\mathsf T}y$ by the single monomial $t x_0y_0$: 10 of 64 pairs wrong |
| `chain` | Composite: $f\mapsto\Phi(f^+)$, $n=2$, span isometry on $\mathbb F_2^{10}$ | 64/64 agree | (inherited) |
| `squares` | Thm A tuple case, $n=4,m=2$, random lifts on both sides | 60/60 agree (34 congruent, 26 not) | Random lifts, no gadget: wrong on 31 of 60 |
| `obstacle` | §1.2 instance: non-congruence by exhaustive search; positive control with planted congruence | as stated | n/a |

`degenerate` (informational): $\Phi$ applied *without* the $f^+$ gadget, with $\mathrm{Rad}\,\tau\ne0$ allowed: 0 disagreements on all 100 pairs of the 10 orbit representatives at $n=3$, and on 40 sampled pairs at $n=4$ (where every cubic has a nonzero radical). So the hypothesis $\mathrm{Rad}\,\tau=0$ in Theorem B is what the *proof* needs; these small cases do not show it is necessary. Theorem C makes the question moot.

All sections were run with fixed seeds. The full run covered `identity reverse3 samples gadget chain obstacle squares`; `degenerate` and a cosmetically edited `identity` (a dead counter removed, same numbers) were run separately afterwards. The longest single pieces are the `samples` at $n=6$ (tens of seconds); total under five minutes.

**What these do not show.** All exhaustive checks are at $n\le3$ (and the gadget at $n\le3$, chain at $n=2$). The GIQS algorithm is not implemented; "truth" is exact search over $\mathrm{GL}$, which also serves as the oracle replacing Thm 1.2. No statement about the running time or correctness of GIQS follows.

---

## 5. Consequences for STS and the barrier

**T2 instances.** Let $\chi:V\setminus0\to\{0,1\}$ be non-constant, $V=\mathbb F_2^d$. By `w30-sts.md` Theorem 2, $X_\chi\cong X_{\chi'}$ iff $\chi'\circ A=\chi$ for some $A\in\mathrm{GL}(V)$, and (redteam-w30 §1.5) $(V,\chi)$ is recovered from the STS in polynomial time. If $\chi$ extends to a function of degree $\le3$ on $V$ (for $d\ge4$ at most one value at $0$ can do this): **[CONDITIONAL: GIQS Thm 1.2]** deciding isomorphism of such $X_\chi$ costs $2^{\tilde O(d^{1.5})}\mathrm{poly}(n)=n^{\tilde O(\sqrt{\log n})}$ on $n=2^{d+3}-1$ points, against $n^{(1/4+o(1))\log_2n}$ for general T2 instances. Recognition: check that the extracted $\chi$ has degree $\le3$.

**What this does not do.** T2 encodes arbitrary colourings, of degree up to $d$. A cubic-only result gives nothing for STS in general, and **no improvement to $n^{o(\log n)}$ for STS follows**.

**What it does say about the barrier.** [CONDITIONAL] T2 cannot be hard at degree $\le3$: any $2^{\Omega(d^2)}$ hardness for $\mathrm{GL}(d,2)$-string isomorphism, if it exists, needs colourings of degree at least $4$. The chain "string iso under $\mathrm{GL}$, degree $\le3$" collapses to quadratic-form spaces. For degree 4 the mechanism breaks: the absorption is the Frobenius additivity of squaring, and the corresponding device for cubic lifts has no additive analogue, so the natural target would be a problem on spaces of cubics, for which no $2^{o(n^2)}$ algorithm is known to me. [SPECULATION on whether a substitute exists.] This matches w17's hypothesis 4-TI (degree $\ge4$ behaviour is where the difficulty survives).

---

## 6. Status

Files: `docs/w35-cubic.md` (this file), `docs/w35-cubic-check.py`. Sources (untrusted, read only) were kept in the scratchpad, not committed: GIQS, IMQSZ, Sun, GQ IV.

**Not done.** Novelty search (web tools hit the session limit; none attempted through other routes). GIQS not implemented, and §6 of it not certified. The search-to-decision sketch and the full coset. Experiments larger than the stated sizes. Lean was not run.
