# Referee report: w35-cubic and w34-vc

Branch `w37-redteam-cubic`, 2026-11-09. Adversarial referee of `docs/w35-cubic.md` and `docs/w34-vc.md`. Tools: `docs/redteam-w35-w34-code/{check_w35.py, check_w34.py, exactiso.c}`, written independently of the authors' harnesses. Lean was not run. Sources read: GIQS (arXiv:2610.00874), IMQSZ, GQ IV (arXiv:2306.16317), Sun (arXiv:2303.15412), all from the scratchpad; Sun, arXiv:2611.05920, downloaded and read for this report.

## 0. Verdict table

| # | Claim | Verdict | Severity of anything found |
|---|---|---|---|
| 1 | Thm A (squares gadget) | **sound**, all $n$ by hand; exact tests pass | none; add "pass to a complement" for nonzero radical (already remarked) |
| 2 | Thm B (exact cubic reduction) | **sound for all $n$**, both directions checked by hand; a sharper form holds: solutions $S$ biject with $\mathrm{Iso}(f,g)$ | none |
| 3 | Thm C (radical elimination) | **sound** | none |
| 4 | Thm D and consequences (conditional) | **sound as conditional statements**; parameter accounting checks; second hypothesis available from arXiv:2611.05920 | the hypothesis is unrefereed; §3.4 item 1's repair is correct |
| 5 | Obstacle ($X^*X=E$, $\mathbb F_2^6$ instance) | **instance verified; sound but weaker than advertised.** It is not char-2-specific (as w35 itself admits). A char-2-specific instance is given in §5 | wording |
| 6 | Prior art | **search done.** Directly relevant new item: Sun, arXiv:2611.05920 (4 Nov 2026), Thm 2.1/A.1: alternating tuple isometry over $\mathbb Z/p^\tau$, including $\mathbb F_2$. No reduction of cubic Boolean equivalence to quadratic-form spaces found | affects novelty of E(i), not B |
| 7 | w34 one-round VC (Thm 2.1 of the doc) | **sound** | none |
| 8 | w34 multi-round VC on Turyn iterates | **sound**; needs $r\ge1$ | none |
| 9 | Thm 4.1, E1/E2, Prop 4.2 | **sound**; two notational slips in Prop 4.2 | minor |
| 10 | Latin squares of $\mathbb Z_2^k$ | **sound** and elementary | none |

**No break found in either memo.** The claims labelled [PROVEN] in the scope above are proven as far as I can check; the conditional ones are correctly stated as conditional.

## 1. Theorem A

Checked by hand. ($\Rightarrow$) $q_i\circ L+q_i'$ has zero polar so equals $(c_ix)^2$ for a row $c_i$ (over $\mathbb F_2$, a zero-polar form is the square of a linear form); $S(x,u)=(Lx,Cx+u)$ does it. ($\Leftarrow$) common radical of polars is $U$, so $S$ is block triangular; $u_i^2$ forces $P=I$ (tuple) or $P=M$ invertible (space). Space version forward direction: if the $A_i$ are dependent, the matrix $M$ with $L^TA_iL=\sum_jM_{ij}B_j$ can always be chosen invertible (two surjections $\mathbb F_2^m\to\langle B\rangle$ with equal kernels' dimensions). Worth one sentence in the memo, since the $Q_i$ are always independent; it does not affect correctness.

The zero-common-radical hypothesis is removable as the memo says: common radicals correspond under any isometry; restrict to complements.

Exact tests (§8): tuple $n=5,m=3$, 59 instances (30 congruent); space $n=4$, $m=2,3$, 46 instances (32 isometric); random lifts on both sides, exact search vs exact truth: 0 disagreements.

**Verdict: sound, for all $n$, both versions.**

## 2. Theorem B

The question posed was whether a span isometry can mix the $u$- and $x$-blocks in other ways. It cannot. The steps, verified line by line:

1. *Low-rank subspace.* Polars of $\langle Q_i\rangle$ have rank at most $n-1$; every element of $F+\langle Q_i\rangle$ has polar $\begin{psmallmatrix}*&I\\I&0\end{psmallmatrix}$ of rank $2n$. So $S$ carries $\langle Q^f\rangle$ onto $\langle Q^g\rangle$, and $F^f\circ S\in F^g+\langle Q^g\rangle$.
2. *Common radical.* With $\mathrm{Rad}\,\tau=0$ the common radical of $\langle Q^f\rangle$ is exactly $U$, so $S(U)=U$: no $u\to x$ mixing is possible. Form $S(x,u)=(Lx,Cx+Pu)$.
3. *$F$ part.* $F^f\circ S$ has no pure-$u$ monomials, so the coefficients of $Q^g$ vanish; the $x$-$u$ cross term forces $L^TP=I$.
4. *$Q$ part.* The $u$-squares give $R=P^T$, hence $R=L^{-1}$. Polars give $\tau_f\circ L=\tau_g$. The $x_j^2$ coefficient of the $x$-part gives $(a^TC)_j=\Gamma^f_a(Le_j)$ for all $a,j$, i.e. $L^TC=\mathbf N$ (uses that $\Gamma^g$ has zero diagonal).
5. *Conclusion.* The $x$-part of $F$ gives $(Q_f+\ell_f)(Lx)+x^T\mathbf Nx=(Q_g+\ell_g)(x)$, and by $(*)$, $g=f\circ L$.

Identities (I1), (I2), $(*)$: expanded by hand on one monomial (I1, I2); $(*)$ follows since a function of degree at most 2 with zero constant term is determined by its values on $e_j$ and its polar on $(e_j,e_k)$. The forward direction was re-derived with $C=L^{-T}\mathbf N$ and $b=L^{-1}a$.

**Strengthening worth recording.** The proof shows more: given $L$, the map $S$ is unique ($P=L^{-T}$, $C=L^{-T}\mathbf N$). So
$$S\ \mapsto\ L\quad\text{is a bijection from }\{S:\Phi(f)\circ S=\Phi(g)\}\text{ to }\mathrm{Iso}(f,g)$$
when $\mathrm{Rad}\,\tau_f=\mathrm{Rad}\,\tau_g=0$. This is a stronger prediction than the decision statement and it was tested: exhaustive enumeration of all span isometries at $n=3$ (all $64^2$ pairs, 10752 isometries in total) and on a sample at $n=5$ gives $\#S=\#\mathrm{Iso}(f,g)$ every time, and every witness has $S(U)=U$.

Exact tests: §8. $n=4$ has no $\mathrm{Rad}\,\tau=0$ instances (every 3-form on $\mathbb F_2^4$ has a nonzero radical, as w35 says), so the theorem is vacuous there; $n=5$ has one $\tau$-orbit with $\mathrm{Rad}=0$; tests there and at $n=6$ are in §8.

**Verdict: sound for all $n$.** The memo's test sizes were not the limit of what is true; the proof is complete and elementary.

## 3. Theorem C

$\mathrm{Rad}\,\tau_{f^+}=0$: for $(a,b,s)$ in the radical, testing against $(0,0,1)$ and $(a'',b'',0)$ gives $a=b=0$; then $s\,a'^Tb''$ gives $s=0$. Holds for $n\ge1$.

($\Leftarrow$) The slice at $(x,y,1)$ has rank at least $2n$; at $(x,y,0)$ at most $\mathrm{rk}\,\tau_f(x,\cdot,\cdot)+2\le n+1$. For $n\ge2$ these are disjoint, so $M$ preserves $H=\{t=0\}$. Restriction gives $f(Ax+By)=g(x)$; surjectivity of $(x,y)\mapsto Ax+By$ gives invariance of $f$ under $I=\mathrm{Im}\,B$; $A$ induces a surjection $V\to V/I$, and $L$ is built from a complement of its kernel. Checked each step; correct. The case distinction ($f$ with linear structures) is handled by the $L\equiv A$ mod $I$ construction, which is where a careless proof would fail.

**Verdict: sound.**

## 4. Theorem D and consequences (conditional)

**Parameter accounting.** $f\mapsto\Phi(f^+)$ with $n'=2n+1$: $2n'=4n+2$ variables and $n'+1=2n+2$ forms, so $m+N=6n+4$ and Thm 1.2 costs $2^{O(n^{1.5})}$. AGL: $2^n$ translation enumeration, absorbed. The memo's $\tilde O$ (from GIQS Thm 2.7) is the conservative reading; correct either way. Thm 1.2's statement is exactly what is used (GIQS PDF p.4: sequences of quadratic forms in $n$ variables over $\mathbb F_2$, span equality under invertible $S$, time $2^{O((m+n)^{1.5})}$), with no hypothesis the instances fail. $\Phi(f)$ has linearly independent forms, which GIQS's algorithm assumes.

**§3.4 item 1 (Thm 4.9 Step 3 overclaim).** Confirmed from the text: the algorithm enumerates all $S'\in M(d_f\times(\beta_0+\beta_1-d_f),\mathbb F_2)$, which is $2^{\Theta(n^2)}$ when $d_f=\Theta(n)$, not the claimed $2^{O((m-\alpha_0-\alpha_1)n)}$. The memo's repair is correct, and shorter than it says: by properties 1 and 3 of the proof, degenerate variables $x_j$ ($j\le d_f$) appear in no cross terms and have zero diagonal in the forms $i\le\alpha_0+\alpha_1$. So substituting $x_j\mapsto x_j+\sum_kS'[j,k]x_k$ changes the induced forms $f_i''$ only through the diagonal, by $\sum_jf_i[j,j]S'[j,k]$. Thus $S'$ matters only via the $n$ vectors $\sum_ja_jS'[j,k]\in\mathrm{span}(a_j)\le\mathbb F_2^{m-\alpha_0-\alpha_1}$, giving at most $2^{(m-\alpha_0-\alpha_1)n}$ cases. (Also an apparent typo in the paper's "Property 3": from the definition of a degenerate vector the index range should be $i\le\alpha_0+\alpha_1$, not $i\le m-\alpha_0-\alpha_1$.) This is a defect of GIQS, not of w35, and it does not change Thm 1.2's bound once repaired. I did not otherwise re-verify GIQS's proof.

**Consequences (E, G).**
- E(i), alternating tuple/space isometry: follows from A and Thms 1.3/1.2 with parameters $(n+m,m)$. Correct.
- E(ii), 3-TI: GQ IV Thm 2.1 gives an $(\ell+1)$-dimensional space of matrices of size at most $3n+2m+2$; the proof divides only by the nonzero entry $\sigma$, so it survives $\mathbb F_2$ (read; the rank-individualization Lemma 4.1 and Lemma 5.2 are field-independent as stated). Combined with A: $O(L)$ variables and forms. Correct, conditional on GIQS and GQ IV.
- E(iii), ATF: via Cor. 5.4 and Thm 5.3 (FGS19 Thm 4.1). Cor. 5.4's chain is a linear-size chain of gadget reductions; I read the statements, not the FGS19 proof. The memo's explicit hedge is the right one.
- G, T2 with cubic colourings: for $d\ge4$ the degree-$\le3$ extension of $\chi$ to $V$ is unique (the two extensions differ by $\delta_0$, of degree $d$), and $A\in\mathrm{GL}(V)$ fixes $0$, so $\chi'\circ A=\chi$ on $V\setminus0$ iff the extensions match; $n=2^{d+3}-1$; recovery by redteam-w30 §1.5. Correct. "Hard T2 instances need degree $\ge4$" is the correct reading.

**One more route to Theorem D.** Thm F's reduction (exact cubic GL-equivalence to isomorphism of 2-groups of Frattini class 2, order $2^{6n+4}$) composes with Sun's arXiv:2611.05920 Thm 1.1 (every $p$-group of class 2, $N^{O((\log N)^{25/26}\log\log N)}$) to give GL-equivalence of cubics in $2^{O(n^{51/26}\log n)}$ time. That is weaker than GIQS's exponent 1.5 but still $2^{o(n^2)}$ and rests on a different (also unrefereed) proof. So the headline "$2^{o(n^2)}$" no longer depends on GIQS alone.

**Verdict: sound as conditional statements.** The hypothesis remains a five-week-old unrefereed preprint with an acknowledged repairable running-time defect.

## 5. The obstacle

Read IMQSZ §4.3 directly: the decomposition $X^*X=E$ is stated for "finite fields of odd characteristics [IQ19]". IQ19 (arXiv:1708.03495) explicitly assumes characteristic not 2 and lists characteristic 2 as an open extension; GIQS PDF p.5 states that the lifting "inherently involves dividing by 2". The memo's location of the obstacle is correct.

Caveat on "the only step": IMQSZ Prop. 4.9 is also stated for odd $q$, but its proof (module isomorphism via [BL08, IKS10]) uses no division by 2, so the memo's "left-right step unproblematic" reading is right. The memo cites Prop. 4.9 in its table row O while its text treats that step as fine; align the two.

**The instance.** Verified: $A_iE=B_i$, $B$ alternating, $E^*=E$; $\dim\mathrm{Adj}(A)=4$ (equal to $I_3\otimes M_2$), so congruence would require $Y^TY=\mathrm{Swap}$, impossible by the parity argument; exhaustive search over $\mathrm{GL}(6,2)$ agrees, with a positive control.

**Weakness.** The instance fails for a semisimple-level reason (the transpose involution on $M_2(\mathbb F_2)$ cannot produce $\mathrm{Swap}$), and over $\mathbb F_3$ the same $E$ also fails, as w35 itself notes. It does not exhibit what GIQS says goes wrong, namely a solution of the quotient problem with no lift.

**A char-2-specific instance.** Let $R=\mathbb F_2[\varepsilon]/(\varepsilon^2)$ with basis $(1,\varepsilon)$, and let $C_1,C_2,C_3$ span the alternating $3\times3$ matrices. Take $A=(C_i\otimes\mathrm{Swap},\ C_i\otimes\mathrm{diag}(1,0))$ on $\mathbb F_2^6$ with $m=6$, and $B_i=A_i(I_3\otimes M_{1+\varepsilon})$. Here $\mathrm{Swap}$ and $\mathrm{diag}(1,0)$ are the Gram matrices of $\varphi(xy)$ and $\varphi(\varepsilon xy)$ for $\varphi(a+b\varepsilon)=b$. Then $\mathrm{Adj}(A)$ has dimension 2 (computed), equal to $I_3\otimes R$ with $\varepsilon^*=\varepsilon$, and $E=1+\varepsilon$ satisfies $E^*=E$. Modulo the radical $E\equiv1$, which has the solution $X=1$. But $(a+b\varepsilon)^2=a^2$ in characteristic 2, so $X^*X=E$ has no solution; exhaustive search over $\mathrm{GL}(6,2)$ confirms $A,B$ are not congruent. Over $\mathbb F_3$ the analogous instance *is* congruent, by the explicit $L=I_3\otimes(1+2\varepsilon)$ (checked), since $(1+2\varepsilon)^2=1+\varepsilon$. This is exactly the lifting failure. I suggest replacing or supplementing §1.2 with it.

**Verdict: instance correct, role overstated; sound with this addition.**

## 6. Prior art (search run for this report)

Searches on alternating/quadratic tuple reductions over $\mathbb F_2$, Grochow–Qiao and char 2, cubic Boolean equivalence algorithms, IP1S char 2, and classification work. Web tools were available and used; arXiv full text was fetched for the first item below.

- **Sun, "Faster Isomorphism for Groups of Class 2", arXiv:2611.05920 (4 Nov 2026, unrefereed).** Directly relevant, and post-dates w35's reading. Thm 1.1: $p$-groups of class 2 in $N^{O((\log N)^{25/26}\log\log N)}$ for every prime $p$. Thm 2.1/A.1: alternating matrix tuple isometry over $\mathbb Z/p^\tau$ in $p^{O(\tau n^{7/4}\log(\tau n))}\mathrm{poly}(m)$, with search and generators of the automorphism group; at $\tau=1$, $p=2$ this is alternating tuple isometry over $\mathbb F_2$. It says the result "mostly follows the framework of [17] for alternating matrix tuple isometry over $\mathbb F_2$", citing GIQS, and states that GIQS gives an "$n^{O(\sqrt n)}$-time algorithm over $\mathbb F_2$". That last figure does not match GIQS's stated bound $2^{O((m+n)^{1.5})}$ and looks like an error of statement. **Consequence for w35:** E(i)'s tuple conclusion is no longer new as a statement; the two bounds are incomparable (Sun better when $m\gg n$, A+GIQS better when $m=O(n)$). A text search of the paper finds no mention of cubic forms or Boolean functions, and quadratic forms appear only in the introduction's discussion of GIQS; its appendix works with alternating tuples directly. I read the introduction, the statements and the start of the appendix, not the proofs.
- **GIQS itself** says (PDF p.5) that the alternating tuple obstacle was overcome and that its algorithm is built around quadratic-form tuples, but it states no alternating-tuple theorem and no reduction from alternating to quadratic tuples. Theorem A supplies the missing formal bridge. Given that Sun treats the alternating case as done by the GIQS framework, treat Thm A as folklore-adjacent: true, one line, not found written.
- **Cubic Boolean equivalence.** Hou (1996) orbit classification of cubic forms and Brier–Langevin (2003), 9 variables (from search listings, not read); Khoruzhii–Gelß–Pokutta, arXiv:2606.28473 (June 2026), $\mathrm{GL}(10,2)$ orbits by rank-stratified enumeration, no complexity bound on its abstract page (full text not read). No reference found giving a sub-$2^{n^2}$ worst-case algorithm, or any reduction of cubic Boolean equivalence to quadratic-form spaces. Grochow–Qiao TI-completeness of cubic forms is stated for characteristic $\neq2,3$ (and GQ IV Cor. 1.11 for $>3$); char-2 cubic equivalence is outside it.
- **IQ19 (arXiv:1708.03495)**: extension to characteristic 2 listed as open. **Berthomieu–Faugère–Perret 2015**: regular case of quadratic IP1S only; GIQS footnote 3 says it fails for an even number of variables and that the general case is open there.

The search was limited (web tools only; no MathSciNet). "Not found" is what it means, nothing stronger. Theorem B and its composite with Theorem C appear to be new as far as I could determine.

## 7. w34

**Item 7 (Thm 2.1: $\lfloor\frac12\log_2n\rfloor-4\le\mathrm{VC}(\mathcal E^1)<2\log_2n$).** Checked every line. The averaging step ($\frac1n\sum_x\langle C_x,\mathbf1_Q\rangle^2\le|Q|$, choice of $x\notin D_i$ with sum at most $2\Psi_i$), the splitting bound $|Q^\pm|\ge\frac12(|Q|(1-\sqrt{2\Psi_i})-1)$ (the $-1$ accounts for $x\in Q$), the recursion for $t_i$, and the arithmetic $\sum_{i<d}2^{i+1}/\sqrt n\le1/8$ are all correct. The closure of the induction uses $t_i\le1$, which holds because cells partition a set of at most $n$ points. Run on $P(65537)$, $d=4$, every intermediate inequality held. The upper bound is $\log_2\binom n2$. **Sound.** (The user's numbering "Thm 3.2" here is the doc's Thm 2.1; the doc's Thm 3.2 is item 8.)

**Item 8 (Thm 3.2).** Prop 3.1 (product coarsening): the induction is correct; the count over a product cell is as stated, and passing from unsigned neighbour counts to signed sums uses that $x,x'$ lie in one round-$r$ cell. Iterating to $m$ coordinates is correct. One small repair in wording: at $r=0$ a singleton product cell need not be an $S$-vertex, but a singleton is trivially inside one cell. The shattering: at $i\in Y$, coordinates $j\ne i$ project to the single vertex $\alpha$, whose stable partition $\{\alpha\},N(\alpha),\bar N(\alpha)$ is equitable (immediate from $V^2=vI-J$, $V\mathbf1=0$), and $V(\alpha,s)=V(\alpha,t)$ keeps $s,t$ together; at $i\notin Y$ the product of signs at $a^{i,1}$ is $-1$. Correct for every symmetric conference-type base of order at least 5 and all $r\ge1$. **Fix:** say "$r\in\{1,2,\dots\}\cup\{\infty\}$"; at $r=0$ no separation occurs and the statement is empty. The spare-coordinate variant for $k>v-2$ is correct. Exact 1-WL on $W_2(P(5))$ ($n=625$): see §8. **Sound.**

**Item 9.**
*Thm 4.1.* The union bound over at most $n^2/2$ pairs gives failure at most $1/(2n)$; the $\varepsilon$-net at $\varepsilon=3/4$ needs $\max((4/\varepsilon)\log_2(2/\delta),(8d/\varepsilon)\log_2(13/\varepsilon))$ samples (BEHW 1989, confirmed in the paper); $(8d/\varepsilon)\log_2(13/\varepsilon)=43.898d\le44d$, and $(16/3)\log_2(2/\delta)\le11$ holds for $\delta\ge0.4788$; total failure is below 1. Two vertices per test gives $2T+2\max(11,44d)\le2T+88d+22$. Separation: if $x,y$ are split in round 1 there is nothing to do; if they are in one round-1 cell and $a,b$ are individualized, $T(a,b,x)\ne T(a,b,y)$ forces separation in round 2 (w32 Lemma 2.3: $C_aC_b$ is constant on cells, and extra individualized vertices only refine them). The constants are correct. **Sound.**
*E1, E2.* Correct, with the routine algorithm that tries all tuples of the bound's size. E2 should read $O(\sqrt{A\log n}+1)$ (for $A$ so small that $\sqrt{A\log n}<1$ the additive 22 remains) and assumes $\log_2(1/\tau)$ in range, i.e. $A\lesssim\log n$.
*Prop 4.2.* Verified the structure: the pair in $B(\tau)$ is witnessed by the all-$a$, all-$b$ test via Lemma 3.3 at base coordinates; the shattering tests collide at $B$-level by Prop 3.1 at $r=2$ and non-collide by sign. Two slips, neither affecting the statement: (i) "$P_B\ge\binom{|B|}2^{-1}$" conflates the ordered fraction $P$ of w32 with $p_2$; what is used is $P_B\ge2/|B|^2$, which yields exactly the stated $2C_0v^{-2^{\ell+1}}$, and $p_2\ge P$ handles the final comparison. (ii) "Equivalently $d(\tau)\ge\frac14\log_v(1/\tau)-O(1)$" holds only for $\tau$ in the range where $\ell\in[1,L]$ exists; outside it $d(\tau)$ is capped by $\ell=L$, which still suffices for the $\Theta(\sqrt{\log n})$ conclusion. Lemma 3.3's statement has a broken LaTeX line ("$W(a,x)\neq W(a,y)$"). **Sound with these fixes.**

**Item 10.** $|\mathrm{Aut}|\ge|\mathrm{GL}(k,2)|\cdot4^k$ from $(x,y)\mapsto(Ax+a,Ay+b)$, acting faithfully on cells; base size at least $\log_n|\mathrm{Aut}|\ge k/2=\frac14\log_2n$; depth is at least base size. **Sound, elementary.**

## 8. Experiments

Single process, nice 19, pure Python plus `exactiso.c` (gcc), nothing outside the worktree and scratchpad. `exactiso.c` searches all of $\mathrm{GL}(N,2)$ with pruning by quantities invariant under any span isometry, and each witness is re-verified by separate form arithmetic in `check_w35.py`. Truth for $f\sim g$ comes from an independent backtracking search over $\mathrm{GL}(n,2)$ on truth tables.

**w35** (`check_w35.py`)

| Section | What | Result |
|---|---|---|
| `identities` | (I1), (I2) for $n\le30$; $(*)$ for $n\le15$, random evaluation; forward map $\Phi(f)\circ S=\Phi(g)$ as exact forms, $n=3,\dots,9$ | 51600 checks, 0 failures; 210/210 |
| `b3` | Thm B, $n=3$, all $64^2$ pairs with $\mathrm{Rad}\,\tau=0$: **all** span isometries enumerated | $\#S=\#\mathrm{Iso}(f,g)$ on every pair (10752 isometries); every $S$ has $S(U)=U$ |
| `b5` | Thm B, $n=5$, the unique $\mathrm{Rad}=0$ orbit $x_0(x_1x_2+x_3x_4)$; $\lvert\mathrm{Stab}\rvert=11520$ (orbit size $9999360/11520=868$, matching the 868 rank-4 alternating forms); 47 orbits on the $2^{15}$ lower terms; 900 sampled ordered pairs of the $47^2$, $g$ randomly conjugated | 0 disagreements (20 equivalent, 880 not); $\#S=\#\mathrm{Iso}$ on 12/12 |
| `b6` | Thm B, $n=6$, 30 random $\mathrm{Rad}=0$ cubics: planted conjugate and one-term perturbation; truth exhaustive | 60 instances, 0 disagreements (31 equivalent, 29 not); up to 11253 search nodes |
| `degenerate` | $\Phi$ with the hypothesis $\mathrm{Rad}\,\tau=0$ removed; all pairs of GL-orbit representatives of functions with $f(0)=0$ | $n=3$: 100 pairs; $n=4$: 529 pairs (23 orbits); 0 disagreements. Necessity of the hypothesis remains open; Thm C makes it moot |
| `composite` | $f\mapsto\Phi(f^+)$, all orbit-representative pairs, $g$ conjugated | $n=2$ ($\mathbb F_2^{10}$, $m=6$): 16 pairs; $n=3$ ($\mathbb F_2^{14}$, $m=8$): 100 pairs; 0 disagreements |
| `thmc` | Thm C at $n=2,3$: $\mathrm{Rad}\,\tau_{f^+}=0$, and $f\sim g$ iff $f^+\sim g^+$ | 16 and 100 pairs, 0 disagreements |
| `squares` | Thm A, random lifts on both sides | tuple $n=5,m=3$: 59 instances (30 congruent); space $n=4,m=2,3$: 46 (32 isometric); 0 disagreements |
| `obstacle` | §1.2 of w35 | $\dim\mathrm{Adj}=4$; no congruence in $\mathrm{GL}(6,2)$; positive control found |
| `obstacle2` | §5 instance above | $\dim\mathrm{Adj}=2$; no congruence over $\mathbb F_2$; explicit congruence over $\mathbb F_3$ |

**w34** (`check_w34.py`)

| Section | What | Result |
|---|---|---|
| `arith` | $\varepsilon$-net constants; Prop 1.1 on $P(13),P(17),P(29),P(37)$ | $43.898\le44$; $\delta\ge0.4788$; bound holds |
| `greedy` | Thm 2.1's steps on $P(65537)$, $d=4$ | every inequality holds; all 16 patterns realized at least twice |
| `prop31` | Prop 3.1 on $W_1$ over $P(5),P(9),P(13)$ and $W_2$ over $P(5)$ | 300 and 36 cases, all hold |
| `thm32` | Exact 1-WL on $W_2(P(5))$, $n=625$: 3 pairs $(s,t)$, $k=1,2,3$, $i\in[3]$, all $Y$, $r=1,2,\infty$ | 648 of 648 match the shattering pattern |
| `lemma41` | w32 Lemma 4.1 on generic triples | 1200, 0 mismatches |
| `prop42` | On $W_2$ over $P(9)$ ($n=6561$): collision of the all-$a$, all-$b$ test for each $x^Y,y^Y$; tests $a^i$ collide iff $i\in Y$ | all hold |

**Limits of these runs.** Inequivalent verdicts come either from the invariant comparison in `exactiso.c` or from exhausting the search, and rest on that code being correct; hash collisions in the invariants can only weaken pruning, never produce a false "not isometric". Each "isometric" verdict is re-verified by separate form arithmetic. At $n=5$ the inequivalent pairs were all rejected within 17 nodes, so the backtracking is really exercised only at $n=6$ and in the positive cases. In `b5` the orbits were computed from 40 random stabilizer elements; they only select the pairs, and truth is a direct search. `thmc` uses an invariant-filtered truth search because the unfiltered one was too slow at 7 variables. `prop42` stops at $W_2$ (so $\ell=L=2$): the further lift by w32 Thm 4.2 is checked by hand only. Experiments support the proofs; the proofs are what certify all $n$.

## 9. What I would sign

1. **Theorem A, B, C and the composite** (for all $n$, both directions, as stated), plus the strengthening: solutions $S$ of Theorem B biject with $\mathrm{Iso}(f,g)$. Elementary, complete.
2. **Theorem D conditional on GIQS Thm 1.2**; parameter accounting correct; the same reduction gives $2^{O(n^{51/26}\log n)}$ conditional instead on arXiv:2611.05920 Thm 1.1 via Thm F.
3. **Consequences E(i)–(iii) and G** conditional on GIQS Thm 1.2, with E(ii)/(iii) additionally on GQ IV Thm 2.1/Cor. 5.4 (read, char-2 compatible for Thm 2.1; FGS19 not re-verified).
4. The obstacle is **correctly located**; the §1.2 instance is valid but not char-2-specific; the instance in §5 above is.
5. **w34**: Thm 2.1, Thm 3.2 ($r\ge1$), Thm 4.1, Prop 4.2 (with the two notational fixes), §7's Latin square bound, and the conditional E1/E2. All as stated after the small fixes listed.

**Not done:** GIQS's proofs beyond what §4 lists were not verified; FGS19 was not checked; no formal verification; novelty is a limited web search.
