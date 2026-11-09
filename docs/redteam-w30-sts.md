# Red-team of w30-sts: Steiner triple systems, rank and the GL barrier

Branch `w33-redteam-sts`, 2026-11-09. Referee report on `docs/w30-sts.md` ("the memo"; "M §x" is a section of it).
Brief: break T1, T2, T3, T5, the w18 refutation and the near-top sketch, or certify exactly what was checked.

Notation as in the memo: $n=2^\ell-1$ where relevant, $r=\mathrm{rk}$, $c=\ell-r$, $V=\mathbb F_2^d$, $Z=\mathbb F_2^3$, $\lambda_0=\tfrac13\log_29$.

**Executed.** `nice -n 19 python -I docs/redteam-w30-sts-check.py` (pynauty venv; one process; §8 records the output).
The script rebuilds $X_\chi$ from the memo's definition without using the memo's code, then compares with the memo's `sts.x_fib`.
Eight web searches for prior art (§5). Jungnickel–Tonchev and D. Zinoviev were read in extracted PDF text; other sources only as search summaries, and I say which.
No Lean. Nothing outside the worktree and the scratchpad was written.

---

## 0. Verdict

**No break.** T2 is correct and I now regard the reduction as **exhaustively confirmed at $d\le 3$ and on every orbit at $d=4$** by exact methods (not hashed invariants). The memo's main defects are a weakly stated constant in T1 (the real constant is larger and sharp), a conflation in the w18 refutation, an unsupported "hardest instances" reading, and an under-cited prior construction.

| # | claim | verdict |
|---|---|---|
| T2 | reduction $\chi\mapsto X_\chi$; iso iff GL-equivalent for non-constant $\chi$ | **sound.** Hand proof re-derived step by step. Exact checks: all $8256$ colouring pairs at $d=3$, all pairs of the $46$ orbits at $d=4$, samples at $d=5$. Iso set maps **onto** $\{A:\chi'\circ A=\chi\}$ with fibres cosets of $K=\mathrm{Hom}(V/\langle\mathrm{supp}\,\chi\rangle,Z)$: extra gauge automorphisms exist but only as a kernel (§1.4) |
| T2-QG | Steiner quasigroups: quasigroup isomorphism $\ge$ linear equivalence | **sound and immediate** |
| T2-LS | Latin-square isotopy | memo's bullet is only a sketch; **I give a proof below** (Prop. A, §1.6) for the Steiner loop square of order $2^{d+3}$, valid for gadgets whose $8\times8$ square is not the elementary abelian one, which includes the memo's table |
| T2-reading | "hardest instances are PG-fibred", "no method can avoid GL" | **overstated.** T2 gives $n^{o(\log n)}\Rightarrow2^{o(d^2)}$ only; nothing shows these are the hardest instances. On the T2 family the problem is polynomially **equivalent** to linear equivalence, hence solvable in $n^{(1/4+o(1))\log_2 n}$ unconditionally on the sketch (§1.5) |
| T1 | PG quotient above a $\Psi_\lambda$ maximizer | **sound**, including Lemma 1 and the $2^{\rho+c}-1$ bound. **The constant $(\log_29)/3$ is not the truth of the method**: the same proof gives $\lambda<(\log_210)/3\approx1.1073$ (so $r>0.9031\,\ell$ and $d\ge r-9.32\,c$), and this is **sharp**: $\mathrm{AG}(2,3)$ is a counterexample just above (§2.3) |
| P1 | converse rank bound | **sound** |
| T3 | $\mathrm{PG}(d-1,q)$ under index gap | **sound**. Small fixes: at $d=3$ the conclusion is a projective plane of order $q$, not nec. $\mathrm{PG}(2,q)$; the second term of $\lambda_q$ can be raised by a divisibility argument (§3) |
| T5 | near-PG decision in $(6D)^{\min(m,6D)}\mathrm{poly}(n)$ | **sound**. Add one sentence on rejecting $X'$ not of this form (§3.2) |
| C4 | refutation of w18 "locally algebraic" | **sound as a statement about the Steiner loop**, not as written for the Steiner quasigroup, for which $\mathrm{PG}$ itself already fails w18's definition (§4) |
| near-top | $n^{(1/4+o(1))\log n}$ for $c=O(1)$ | **remains a sketch**. Named gaps in §4; special case of the T2 family is proven |
| novelty | T2, T1 "not found" | Hedges stand for the iso reduction. **The fibration description is prior art** and is not cited: Jungnickel–Tonchev Thm 2.8/2.9 and the Zinoviev papers (§5) |

---

## 1. Theorem 2

### 1.1 The construction and the (⇐) direction

Rebuilt from the memo's text in the check script; identical to `sts.x_fib` on every colouring at $d=2,3$. Every output is a valid STS (each pair covered exactly once, checked at construction, $n=2^{d+3}-1$, block count $n(n-1)/6$). The displayed table $F^1$ is a genuine 1-factorization of $K_8$ with (a) and (b), and equals the seed-7 output of the memo's script.

(⇐): checked block-by-block for **every** $(\chi,A)$ at $d=2$ and $d=3$ ($48$ and $21504$ pairs).

### 1.2 The (⇒) direction, step by step

I re-derived the proof. Each step is correct:

* $f|_{Z\setminus0}=\lambda$ linear (lines of the Fano plane).
* On a line $\{c_1,c_2,c_3\}$, type (iii) forces $f(c_i,\cdot)$ to be affine with common linear part (setting $a=0$ then $b=0$), and $v_1+v_2+v_3=0$ for the constants. Every two points of $\mathrm{PG}(V)$ are collinear, so the linear part is one $\mu$ for all fibres and $v$ is linear on $V$ (for $d\ge2$).
* Type (ii) on a $\chi(c)=0$ fibre gives $\lambda=\mu$; on a $\chi(c)=1$ fibre, combined with $\lambda=\mu$, gives $\mu(a+b+z)=0$ for all pairs, so $\mu=0$ by (b). Both fibre types exist exactly because $\chi$ is non-constant. So characters are exactly $V^*$.
* Common kernel $=Z\setminus0$; level sets are the fibres; an isomorphism carries characters to characters linearly, so induces $A\in\mathrm{GL}(V)$; $S\cup C_c$ is $\mathrm{PG}(3,2)$ iff $\chi(c)=0$ by (a). Hence $\chi'\circ A=\chi$.

Each hypothesis is really used. (a) is needed only in the last step; (b) only for $\mu=0$. Machine: the steps "char dim $=d$", "kernel is $Z\setminus0$", "fibres are level sets", "subsystem $S\cup C_c$ is PG iff $\chi(c)=0$" hold on all nonconstant orbit representatives at $d=2,3,4$. The one (a)-true, (b)-false gadget tested has char dim $d+1$ at $d=3$, so the step "characters are exactly $V^*$" really needs (b); no collision occurred for it, so (b) is a hypothesis of the proof and not shown necessary for the conclusion.

The reduction statement is correct for arbitrary $f$: compare $f(0),g(0)$ and handle constant restrictions on $V\setminus0$ directly (output a fixed YES/NO pair, for instance two fixed non-equivalent non-constant colourings, which exist for $d\ge2$). $n=O(2^d)$, so this is a linear-size many-one reduction.

### 1.3 Exact decisions

Exact tools (no hashing anywhere): integer cycle-type invariants of $x\mapsto p\cdot(q\cdot x)$ (trivially invariant), and an exact generator-enumeration search with closure propagation that either returns a verified witness or exhausts. Cross-validated against plain nauty at $d=2$ on all $64$ ordered pairs, and against nauty with the exact point-invariant colouring at $d=3$ (the memo's "nauty stalls" applies only to the uncoloured graph; with the colouring each certificate at $n=63$ took under $0.05$ s).

| $d$ | $n$ | what | result |
|---|---|---|---|
| 2 | 31 | all $36$ unordered pairs of the $8$ colourings, constants included | iso iff same GL-orbit: $14$ witnesses, $22$ exact non-isomorphisms |
| 3 | 63 | all $8256$ unordered pairs of the $128$ colourings, constants included | iso iff same GL-orbit, no mismatch; $1388$ verified witnesses; $6868$ exact non-isomorphisms (nonconstant: $1386$ iso, $6615$ not) |
| 4 | 127 | all $46$ GL(4,2)-orbit representatives, all $1035$ pairs; $40$ planted equivalent pairs; $196$ colourings through coloured nauty | all orbit pairs exactly distinct (exact invariant multisets all differ); planted pairs found by independent search with verified witness; nauty classes are exactly the GL-orbits |
| 5 | 255 | $3$ planted positive, $3$ negative (equal weight, $\lvert$Walsh$\rvert$ multiset differs) | certificates equal / differ as predicted |

Also with other gadgets (d=3, every nonconstant orbit pair): at most $8$ random gadgets from each of the $6$ isomorphism types of 1-factorization of $K_8$ that satisfy (a),(b), and $10$ adversarial gadgets $F^1_z=F^0_{\pi(z)}$ with $\pi$ non-linear (whose $8\times8$ square is the elementary abelian one): no non-equivalent pair isomorphic.

Controls: with $F^1=F^0$ the tester reports every non-equivalent nonconstant pair isomorphic (all are $\mathrm{PG}(5,2)$), so it is not vacuously saying "non-isomorphic". For the (a)-false gadget $F^1_z=F^0_{Az}$ ($A$ a fixed element of $\mathrm{GL}(3,2)$), $X_\chi$ is not isomorphic to $X_{\bar\chi}$ on all $8$ nonconstant orbit representatives, so complementing $\chi$ does not collapse there; (a) is what the last proof step uses and I have not shown it necessary.

### 1.4 "No extra maps from the fibres or gauge"

The statement that matters for the reduction is decision-level, and it holds. Precisely: every isomorphism induces $A$ with $\chi'\circ A=\chi$, every such $A$ lifts by the explicit map, and the fibre over $A$ is a coset of the automorphisms inducing $A=I$. For the memo's table, Stab$(F^1)$ in $\mathrm{GL}(3,2)\times$translations is trivial (computed). An automorphism inducing $A=I$ acts on a fibre by $\psi_c$ with $\psi_{c_3}(a+b)=\psi_{c_1}(a)+\psi_{c_2}(b)$ on lines, so $\psi_c(a)=Ma+t(c)$ with $t$ linear; colour-$0$ fibres force the action on $Z\setminus0$ to be $M$; colour-$1$ fibres force $(M,t(c))\in\mathrm{Stab}(F^1)$. Hence
$$K=\{(c,a)\mapsto(c,a+t(c)) : t\in\mathrm{Hom}(V/\langle\mathrm{supp}\,\chi\rangle,Z)\},$$
and this $K$ fixes $S$ and every fibre over $\langle\mathrm{supp}\,\chi\rangle$ pointwise and translates the remaining fibres. Exact match, nauty group orders on all nonconstant orbit reps at $d=2,3,4$: $|\mathrm{Aut}(X_\chi)|=|\mathrm{Stab}_{\mathrm{GL}}(\chi)|\cdot|K|$ (e.g. $d=3$, $\chi$ the indicator of one point: $1536=24\cdot64$). So gauge automorphisms exist when $\mathrm{supp}\,\chi$ does not span $V$, but they do not change which $A$ occur. So isomorphisms do not biject with linear equivalences; they surject onto them with kernel $K$. The memo claims only the decision-level statement, which is what the reduction needs; it should mention $K$.

### 1.5 What T2 says and does not say

T2 is an implication: $n^{o(\log n)}$ for STS $\Rightarrow2^{o(d^2)}$ for GL-string. Correct and a real obstruction to a certain style of proof. It is not a lower bound, and the $2^{o(d^2)}$ question is open with no hardness known. The best bound in the campaign is w17's $2^{d^2/4+O(d)}$; Babai's general string-isomorphism bound has exponent above $2$ in $\log N$ in the published analyses (exponent $3$, from memory), so it does not settle $2^{o(d^2)}$ here either.

The memo's M §0/§6 reading ("the hardest instances are recognisably PG-fibred", "T2 shows no method can avoid the GL part") goes further than the theorem. T1 only addresses rank $\ge0.903\ell$; T2 says the fibred class contains GL-string; nothing says hard instances are there, and on the T2 family the problem is *easier* than the general bound: recover $(V,\chi)$ from the STS by the characters and the $\mathrm{PG}(3,2)$ test (polynomial time), then run Theorem B of w17 (it is stated for $\mathrm{AGL}$; give the point $0$ a third colour so that translations cannot move it). So for T2 instances STS isomorphism is polynomially equivalent to linear equivalence and is decided in $2^{d^2/4+O(d)}\mathrm{poly}(n)=n^{(1/4+o(1))\log_2 n}$, against the campaign's general $n^{(1/2)\log_2n}$. The $1/4$ for this family needs no part of the near-top sketch.

Measured exact ranks of nonconstant $X_\chi$: $r=d+1=\ell-2$ at $d=2,3$ (so these instances have $c=2$, not $3$, at small $d$; the proven bound $r\ge d$ is an inequality).

### 1.6 Quasigroups and Latin squares

* **Quasigroup isomorphism:** immediate, as the memo says: STS isomorphism is isomorphism of Steiner quasigroups.
* **Latin-square isotopy:** M §9 is a sketch. I give a proof for the natural choice, the **Steiner loop** $L_\chi$ of $X_\chi$ of order $2^{d+3}$. Let $M_1$ be the $8\times8$ square $M_1[a][b]=z$ iff $\{a,b\}\in F^1_z$ (diagonal $0$).

**Proposition A.** Suppose $F^1$ satisfies (a),(b) and additionally **(c)** $M_1$ is not isotopic to the Cayley table of $\mathbb F_2^3$. For non-constant $\chi,\chi'$, the Latin squares of $L_\chi$ and $L_{\chi'}$ are isotopic iff $\chi,\chi'$ are GL-equivalent.

*Proof.* (⇐) An isomorphism is an isotopy. (⇒) Let $(\alpha,\beta,\gamma):L_\chi\to L_{\chi'}$ be an isotopy, $\alpha(x)\beta(y)=\gamma(xy)$. A triple $(f_1,f_2,f_3)$ of functions $L\to\mathbb F_2$ with $f_1(x)+f_2(y)+f_3(xy)=0$ has the form $(h+c_1,h+c_2,h+c_1+c_2)$ with $h\in\mathrm{Hom}(L,\mathbb F_2)=\mathrm{Char}(X_\chi)=V^*$ (put $x=e$, then $y=e$). Pulling back $h'\in V^{*\prime}$ through the isotopy gives a linear bijection $h'\mapsto h$, so $\alpha,\beta,\gamma$ permute the cosets of $N=(Z\setminus0)\cup\{e\}$ and induce affine maps on $V=L/N$ with common linear part $A$: $\bar\alpha(c)=Ac+t_1$, $\bar\beta(c)=Ac+t_2$, $\bar\gamma(c)=Ac+t_1+t_2$. The subsquare on (row coset $r$, column coset $s$, symbol coset $r+s$) of $L_\chi$ is the Cayley table of $\mathbb F_2^3$ except at the positions $(c,c),(0,c),(c,0)$ with $\chi(c)=1$, where it is $M_1$ or a conjugate (not isotopic to the Cayley table by (c), as that table is totally symmetric). So the isotopy gives a bijection $S_\chi\to S_{\chi'}$ of these position sets, $(r,s)\mapsto(Ar+t_1,As+t_2)$. If $t_1\neq0$, every $r\in W=\mathrm{supp}\,\chi$ has $Ar+t_2\in\{t_1,0\}$, so $|W|\le2$; symmetrically if $t_2\ne0$. If $t_1=t_2=0$ then $A(W)=W'$. If $|W|\le 2$ then $|W'|=|W|$ and $W,W'$ are GL-equivalent because two distinct nonzero vectors are independent. ∎

(c) holds for the memo's table (machine) and for every 1-factorization of $K_8$ except the $30$ translation ones (the five other isomorphism types, computed with nauty). The relabelled-Cayley gadgets above violate (c); there the proof does not apply, though at $d=2,3$ the loop squares still separate the $8$ nonconstant orbits. By nauty at $d\le3$, the loop squares and the Steiner-quasigroup squares (order $2^{d+3}-1$) of both gadgets fall into exactly as many isotopy classes as there are nonconstant orbits ($2$ at $d=2$, $8$ at $d=3$). For the quasigroup squares this is evidence only; I do not prove that version. **Fix:** replace the M §9 sentence by Prop. A and note the extra hypothesis (c).

---

## 2. Theorem 1, Lemma 1 and the constant

### 2.1 The proof

Re-derived line by line. Only doubling, $\rho(\langle S,x_1,\dots,x_t\rangle)\le\rho(S)+t$, and the potential inequality are used; the proof nowhere assumes exchange, modularity, or that subsystem index is multiplicative. ($\rho$ is not monotone under inclusion and the proof does not need it to be.) Lemma 1 and "(1)" are correct, and so is the bound "every $\rho$-generated subsystem has at most $2^{\rho+c}-1$ points", whether $\rho$ means $\rho(T)$ or any number of generators of $T$ (it is monotone in the exponent).

Every step of T1 passes: minimality of $T_x$ ($\beta_1<4$), coset partition, $m_U=3$ ($\beta_2<5$ suffices), the third coset is well defined and the quotient is an STS (the memo's "$x'\cdot y'$ lands in the same third coset" uses that $\langle S,x',y'\rangle=U$ for all representatives; correct), equal coset sizes, numerics, $r\le\rho(S)+d$ (using that cosets meeting a subsystem $R\supseteq S$ lie in $R$).

Small tidying: the exact form of the dimension bound is $d\ge r-c/(\lambda-1)=(\lambda r-\ell)/(\lambda-1)$, which is positive exactly when $\lambda r>\ell$, i.e. exactly when $S\ne X$ is forced. The rounded "$d\ge(1-18.7\varepsilon)\ell$" is positive only for $\varepsilon<0.05348$, so it is slightly lossy on $[0.05348,0.0536)$. Nothing stated is affected.

### 2.2 Machine checks

Exact subsystem lattices (every subsystem, exact $\rho$ by BFS) on all PG up to $\mathrm{PG}(5,2)$, $\mathrm{AG}(2,3),\mathrm{AG}(3,3)$, every orbit representative of $X_\chi$ at $d=2,3$, $X_g$ at $d=3,4,5$, doubled $\mathrm{PG}(3,2)$, hill-climbed STS of orders $15,19,27,31,33$, and $72$ point-invariant types of STS$(15)$: $114$ systems in all. Checked for all $\lambda\in\{1.001,1.02,1.05,1.0566,1.08,1.10,1.1072\}$ **and every maximizer** (ties included): Lemma 1 on every subsystem, the size bound, S$\neq X$ when forced, the partition, equal sizes, $a\ge s+1$, the third-coset property, quotient an STS with all triangles Fano, $n=s+a(2^d-1)$, and the numeric bounds. No failure. Non-trivial $S\neq\emptyset$ occur, e.g. $X_g$ with $d=5$ yields $s=15,a=16$, $\mathrm{PG}(1,2)$.

### 2.3 The constant: where $(\log_29)/3$ comes from and what the truth is

It comes only from the Planes step: "$m_W(s+1)\le|W|-s<(\beta_3-1)(s+1)$, need $m_W\le7$", i.e. $\beta_3-1\le8$, i.e. $\lambda<\tfrac13\log_29$.

But $m_W$ is the order of a subsystem of the STS $P$ containing a triangle, so $m_W\equiv1,3\pmod6$ and $m_W\ge7$. Then $\beta_3<10$ already forces $m_W\in\{7\}$ (values $8$ is excluded by the congruence, $9$ needs $\beta_3\ge10$). The Lines step needs only $\beta_2<5$, which holds for $\lambda<(\log_210)/3$. So **the proof works for all $1<\lambda<\lambda_1:=\tfrac13\log_210\approx1.10731$**.

Consequences, replacing the memo's numbers: $S\ne X$ whenever $r>\ell/\lambda$, so **$r>0.9031\,\ell$ suffices** (and $3/\log_210=0.90309$); $d\ge r-9.32\,c$ (coefficient $1/(\lambda_1-1)$ after a small adjustment of $\lambda$), so $r\ge(1-\varepsilon)\ell$ gives $d\ge(1-10.3\varepsilon)\ell$ and $|S|\le n^{10.3\varepsilon}$. M §9's "band $1.0566<\lambda<1.153$" where the planes argument gives order at most $9$ should read: order exactly $7$ for $\lambda<\lambda_1$, order $\le 9$ for $\lambda<(\log_2 11)/3$, and the value $9$ is first possible at $\lambda_1$.

**This is sharp.** For $X=\mathrm{AG}(2,3)$: $n=9$, $r=3$, $\ell=\log_210$, so $r/\ell=0.90309$ exactly. For $\lambda>\lambda_1$ the unique maximizer is $S=\emptyset$ and the coset structure is $\mathrm{AG}(2,3)$ itself, not a projective space. (Machine: $\lambda=1.1072$ gives $S=X$, $\lambda=1.1074$ gives $S=\emptyset$.) So $\lambda_1$ is the exact threshold of this statement, and the conclusion "PG" fails just above it; a further improvement needs a different conclusion (a structure theorem allowing $\mathrm{AG}(2,3)$-type planes).

### 2.4 The converse and the remarks

P1 is correct. The remark that $a>s+1$ requires $s\ge24$ is correct at $\lambda<\lambda_0$ (and would be $s\ge 12$ at $\lambda<\lambda_1$). The Steiner-loop remark for $a=s+1$ is right, and that case is exactly the Jungnickel–Tonchev structure (§5).

---

## 3. Theorems 3 and 5

### 3.1 T3

Proof re-derived: minimality ($\lambda<2$), lines ($m_U\le(q^{2\lambda}-1)/(q-1)<q+2$ and $m_U>q$ from $|U|\ge q^2s$, $|C|\le(q^\lambda-1)s$), two-point determination (needs $2\lambda<3$), planes (the $\lambda_q$ second term). All correct. Examples checked exactly: $\mathrm{AG}(2,3),\mathrm{AG}(3,3)$ with $q=3$ give line size $4$ and plane size $13$; $\mathrm{PG}$ with $q=2$ gives $\mathrm{PG}$ of the right dimension. Hypotheses matter (index gap) and are verified where used.

Fixes: (i) for $d=3$ the conclusion is a projective plane of order $q$; call it a projective plane, not $\mathrm{PG}(2,q)$; Desarguesian only from $d\ge4$. (ii) The planes term can be improved: a linear space with all lines of size $q+1$ has $m\equiv1\pmod q$ and $m(m-1)\equiv0\pmod{q(q+1)}$, so the next admissible order after $q^2+q+1$ is $(q+1)^2$; replace $q^3+q-1$ by $q^3+q^2-q$ in $\lambda_q$. At $q=2$ this recovers $\lambda_1$ exactly (the check script prints both). At $q=3$ the memo's $\lambda_3\approx1.0217$ becomes $\approx1.0609$; at every $q$ tested the second term stays the binding one.

### 3.2 T5

Proof correct: for clean $z$ and clean $x+z$ (at most $12D$ failures), $M(x,y)=x+y$; so $D<(n-2)/24$ gives a strict majority. An isomorphism preserves $M$, the base, and the defect sets; a basis of the span of defect points must map into defect points; the count $(6D)^{\min(m,6D)}$ is correct, and defect checking makes the converse immediate. Machine: $M=x+y$ on all pairs for $(m,D)=(7,4),(8,8),(9,20)$ (right up to the bound $21.2$ at $m=9$), and the decision procedure agrees with the exact search on positive and negative pairs at $m=7,8$. Add: "if $X'$ does not decode to a projective structure within $D$, reject", needed for a decision procedure on arbitrary input and easy.

---

## 4. The w18 refutation and the near-top sketch

### 4.1 The w18 lead

The memo's proposition is correct as a statement about Steiner loops: machine over **all $128$** cochains on a Fano plane, $g$ is a coboundary iff the loop $L_g$ of order $16$ is associative iff it is Moufang ($16$ coboundaries, $112$ non). The associator formula equals the Pasch sum missing $x+z$ on all cochains and all bases. The 3-generated section argument is right: take lifts of a basis of a plane $E$ with $g|_E$ not a coboundary; the generated subsystem projects onto $E$, and if it missed the point over $0$ it would be a section, making $g|_E$ a coboundary; so it contains both lifts of every point of $E$ and has order $15$. "A loop isotopic to a Moufang loop is Moufang" and Albert's theorem are standard.

**Wording problem.** The lead in w18 is about the *quasigroup*. For the Steiner **quasigroup** (order $n$, the object an STS naturally is) the "locally algebraic" condition already fails for $\mathrm{PG}$: the Fano plane's order-$7$ Steiner quasigroup has a non-associative, non-Moufang principal loop isotope (machine, and similarly $\mathrm{PG}(3,2)$), so it is not isotopic to a group or Moufang loop. So the correct reading is: the refutation concerns the **Steiner loop** $L_g$ of order $2^{d+1}$, which is itself a quasigroup of rank $\ge d$ with a 3-generated non-Moufang subloop. Stated that way the refutation is sound; "a section isotopic to a group or Moufang" in the memo's Prop. 2 should say "the Steiner loop of a 3-generated subsystem". (The trilinear/bilinear claims of M §6 check out on all cochains.)

### 4.2 Near-top sketch

The claimed $n^{(1/4+o(1))\log n}$ for $c=O(1)$ is a [SKETCH], correctly labelled. Exact state:

* What is fine: $S$ is found by enumerating $\le c/(\lambda-1)$-generated subsystems ($n^{O(c)}$) because maximizers have small $\rho$; $|S|,a\le2^{O(c)}$ so $a=O_c(1)$; with $S$ fixed the problem is string isomorphism on $X^{\times3}$ under $\mathcal G\rtimes\mathrm{GL}(d,2)$ with $\mathcal G=\mathrm{Sym}(a)^{2^d-1}$. Flags/Borel plus Babai–Luks for $\Gamma_a$ handle $\mathcal G\rtimes B$ (time $n^{O(a)}$, independent of the $2^{d^2/2}$ issue).
* Named gaps: (i) the bidirectional step needs a canonical form on the $B$-side relative to the gauge, written out; (ii) for $a>s+1$ the gauge is on larger blocks with internal structure, not checked; (iii) the claim is for fixed $c$; the constants hide $n^{O(a)}$ with $a=2^{O(c)}$, so "$c=O(1)$" is load-bearing and $c=\omega(1)$ gives nothing.

Plausible, but do not cite as proved. **The special case that is proved:** the family $\{X_\chi\}$ itself (§1.5).

---

## 5. Prior art

| what | source (how read) | relation to w30 |
|---|---|---|
| $\mathrm{STS}(2^n-1)$ with 2-rank $\le 2^n-1-n+t$ have the form: STS on $V_0$ of order $2^t-1$, groups $G_i$ of size $2^t$ indexed by points of $\Pi=\mathrm{PG}(n-t-1,2)$, a 1-factorization of each group labelled by $V_0$, and a transversal design on each line of $\Pi$ | Jungnickel–Tonchev, arXiv:1709.06044, Thms 2.5, 2.7–2.9 (extracted PDF text, read directly) | **This is the memo's "general form" of §6 (one-factorizations and arbitrary Latin squares on lines), and the $a=s+1$ branch of T1, with characters replaced by the code $C_{n,t}$.** The product formula $s(n,t)=N_1\cdot(N_2T!)^M\cdot N_3^{M(M-1)/6}$ is the memo's "these data are independent". The memo's §1 cites JT only for counts. Should cite as the source of the fibration. JT Thm 2.5 (Assmus Cor. 3.7) also gives the group $S_T\times S_{T+1}^M\rtimes\mathrm{PGL}(n-t,2)$ of the code: the "GL with gauge" group of the near-top sketch, in print for $a=s+1$. |
| rank $2^m-m+2$ ($t=3$) with $K_8$ factorizations, 6240 labelled, six orbits | D. Zinoviev, arXiv:1512.00187 (extracted PDF text; §2 and Thm 3.1 region) | exactly the $k=3$ gadget regime of T2 |
| Assmus: code of an STS determined by 2-rank | ELJC 2 (1995) R9 | character-space fact behind the classification |
| central extension $\mathbb F_2$-cocycles for Steiner loops | Grishkov et al., arXiv:1508.03399 (search summary only; cocycle identities not compared line by line) | as cited in the memo |
| GI $\le$ code equivalence (Petrank–Roth), other direction reductions; Babai string isomorphism quasipoly; Miller $n^{\log n}$; Babai–Wilmes | search summaries | none reduce GL-string/code equivalence to STS isomorphism |

Of the eight searches, three aimed directly at a reduction from Boolean-function, code or tensor equivalence to STS, quasigroup or design isomorphism; none found one. "Not found", not "new". My searches did not exhaust Russian-language or older design-theory literature. The reduction's method (colour a base geometry by choosing a fibre gadget) is elementary; I would present T2 as "probably folklore-level, apparently not written", and the cite above should go in.

---

## 6. Requested memo fixes

1. M §0/T1 row and §3: replace $\lambda_0$ by $\lambda_1=(\log_210)/3$, the parity step in Planes, and state sharpness via $\mathrm{AG}(2,3)$. Fix the §9 Lead 4 band.
2. §0, §6 "barrier" sentences: state the implication only; remove "hardest instances are recognisably PG-fibred" and "exactly the barrier"; add the equivalence with linear equivalence on the T2 family.
3. §6: mention the kernel $K$ (§1.4 above); record $d=4$ and $d=5$ checks; delete "nauty stalls" or qualify it.
4. Prop. 2: state for the Steiner loop.
5. §9: replace the Latin-square sketch by Prop. A with hypothesis (c).
6. §1 novelty: cite Jungnickel–Tonchev Thm 2.8 and the Zinoviev papers for the fibration form.
7. T3: projective plane at $d=3$; improved $\lambda_q$ optional.
8. T5: add rejection of non-decoding $X'$.

---

## 7. The strongest statements I would sign

1. (T2) For $d\ge2$ and non-constant $\chi,\chi'$ on $V\setminus0$, with $F^1$ satisfying (a),(b): every isomorphism $X_\chi\to X_{\chi'}$ induces $A\in\mathrm{GL}(V)$ with $\chi'\circ A=\chi$, every such $A$ lifts, and the isomorphisms inducing $A$ are a coset of the gauge group $K$. Hence linear equivalence of Boolean functions on $\mathbb F_2^d$ many-one reduces in time $\mathrm{poly}(2^d)$ to STS isomorphism on $2^{d+3}-1$ points, with $r\ge\ell-3$; $n^{o(\log n)}$ for STS (or quasigroup) isomorphism implies $2^{o(d^2)}$ for it. Hand proof re-derived; exact checks $d\le 4$ exhaustive on orbits and all pairs at $d\le3$; sampled at $d=5$.
2. (Prop. A) Same reduction to Latin-square isotopy of order $2^{d+3}$ for gadgets with (a),(b),(c), including the memo's table.
3. The problem restricted to the T2 family is polynomially equivalent to linear equivalence and solvable in $2^{d^2/4+O(d)}\mathrm{poly}(n)$ given Theorem B of w17.
4. (T1, sharpened) For $1<\lambda<(\log_210)/3$, every maximizer $S\ne X$ has cosets forming $\mathrm{PG}(d-1,2)$ with the stated numerics; $S\ne X$ when $r>\ell/\lambda$; $d\ge r-c/(\lambda-1)$. Lemma 1 and the size bound hold. The threshold $(\log_210)/3$ is exact.
5. (T3) Under the index-gap hypothesis, with $\lambda<\lambda_q$: linear space with lines of size $q+1$ and planes projective planes of order $q$; PG when $d\ge4$ (with $q$ a prime power).
6. (T5) As stated, with the rejection sentence.
7. (C4) For $d\ge3$: the Steiner loop $L_g$ of a cochain not a coboundary on some plane has rank $\ge d$ and contains a 3-generated subloop of order 16 that is not Moufang, hence not isotopic to a group or Moufang loop.
8. The near-top $n^{(1/4+o(1))\log n}$ for all $c=O(1)$: not signed; only signed for the T2 family.

---

## 8. Run record

`docs/redteam-w30-sts-check.py`, one process under `nice -n 19`, two passes. Pass 1 ran `gadget t2 t2d4 t2d5 nauty` (395 s) and then crashed on a referee bug in `alt`: my control matrix `(3,5,6)` was singular. I changed that constant to `(3,5,7)`. Pass 2 ran `alt trace t1 t3 t5 c4 iso aut` (429 s). Afterwards I removed one no-op line and added the condition-(c) check to `alt`, and re-ran `gadget`, `aut` and `alt`. All sections completed with no `MISMATCH` and no `FAIL`. Output key lines:

```
gadget  1-factorization True; (a) True; (b) True; table equals seed-7 output True
t2      d=2: 36 pairs, 14 witnesses, no mismatch; 48 (chi,A) forward maps verified
t2      d=3: 8256 pairs, 1388 witnesses, no mismatch; 21504 (chi,A) forward maps verified
t2d4    46 orbits, 44 nonconstant; exact invariant multisets distinct 46/46; 40 planted pairs witnessed
t2d5    3 planted positives equal, 3 negatives differ (nauty, invariant colouring)
nauty   d=2 search = plain nauty on 64 ordered pairs; d=3 10 colourings -> 10 classes;
        d=4 196 colourings -> 46 classes, each one orbit, each orbit one class
alt     6240 factorizations, 6 types [30,420,630,960,1680,2520]; 45 sampled gadgets and 10 relabelled-Cayley: 0 collisions
        condition (c): M_1 isotopic to the Cayley table only for the type of size 30
        F^1=F^0 control: all pairs isomorphic True; (b)-false gadget: char dim 4 at d=3, 0 collisions
trace   proof steps ok on 2/8/44 nonconstant orbit reps (d=2,3,4)
t1      114 systems, 0 failures; exact rank of nonconstant X_chi: 3 at d=2, 4 at d=3
        AG(2,3): lambda=1.1072 -> S=X; lambda=1.1074 -> S=empty (quotient not PG)
t3      AG(3,3), q=3: line size 4, plane size 13; lambda_3 memo 1.02168, with divisibility 1.06089
t5      M = XOR for (m,D) = (7,4),(8,8),(9,20); decisions agree with exact search at m=7,8
c4      128 cochains: (cobound,assoc,Moufang) = (T,T,T) x16, (F,F,F) x112; associator formula True
        PG(2,2) and PG(3,2) Steiner quasigroups: principal isotope not associative, not Moufang
iso     memo M_1 not isotopic to Z_2^3; d=3 loops and quasigroups: 8 orbit reps -> 8 isotopy classes
aut     Stab(F^1) trivial; |Aut X_chi| = |Stab_GL(chi)|*|K| on 2/8/44 nonconstant orbit reps
```

Not checked: the proofs of w17 Theorem B beyond the existing red-team, and any asymptotic behaviour (all machine checks are at $n\le511$). Non-isomorphism verdicts rest on exact integer invariants, on exhaustive search, and on nauty. All-pairs coverage at the level of colourings is for $d\le3$; at $d=4$ it is all pairs of orbit representatives, with the within-orbit direction proved and sampled.
