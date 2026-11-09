# Red team: w49-pruned (Theorems T, P, Lemmas L′, Bil, Aut, B′, repair R1)

Adversarial referee report, branch `w51-redteam-pruned`, 2026-11-09. Target: `docs/w49-pruned.md` at commit `e6a8fb1`. HJ = arXiv:2611.01399, line numbers `L…` of the local LaTeX; Helfgott = arXiv:1710.04574 (`BDHv8.tex`). The Lean tree was read only, never run. Code: `docs/redteam-w49-code/`, written independently of `docs/w49-code/`.

**Bottom line.** Theorem T survives, and survives more than its author claimed: his untraced Lean colour rule, once traced, matches choice (b) automatically once choice (a) holds. The four group-theory lemmas are correct. Theorem P is **correct as an inequality for left-only pruning, but its gloss is false**: the memo's "any automorphism pruning", its "strongest possible" pruning and its §6 conclusion ("any improvement must change the path … and not the pruning") are refuted by *two-sided* pruning, which uses certified automorphisms of source and target, and leaves exactly the number of conjugacy classes of $\mathrm{GL}(d/2,2)$ children at this node, which is $2^{d/2+o(d)}=N^{(1/(4e))(1+o(1))}$. That is polynomial in $N$. The literal conjecture of w47 §5.3 is still falsified, because it is one-sided; but what the conjecture was meant to capture is not. Remaining items are statement slips.

## 0. Verdicts

| # | Claim | Verdict | Severity |
|---|---|---|---|
| L′ | $\mathrm{Aut}(B)=\mathrm{GL}(V)\times\mathrm{GL}(U)$, $d>e\ge3$ | **sound** | none |
| Bil | $\mathrm{Aut}(\mathrm{Bil})=N{:}(\mathrm{GL}\times\mathrm{GL})$, $d>e\ge3$ | **sound** | none |
| Aut | $\mathrm{Aut}(x)=N{:}(\mathrm{Sp}\times\mathrm{Sp})$, even $d>e\ge4$ | **sound** | none |
| B′ | unique block system on $W$ | **sound** | none |
| T | trace to a post-rectangle `Continue` node enumerating $P\cong\mathrm{GL}(d,2)$ | **sound** (given H0, HJ as written, (a)) | none |
| T, "the Lean tree leaves them open too" | | **statement error**: the Lean *program* fixes both choices by label order (§3) | low |
| T, "$n\ge2^{33152}$" | | **statement slip**: $d$ is even, so $d\ge260$, $n\ge2^{33280}$ | trivial |
| P, as an inequality for left-only pruning | | **sound** | none |
| P, "any automorphism pruning"; §4 "strongest possible", "genuinely inequivalent under every automorphism"; §6 "must change the path … not the pruning" | | **broken** (§4 here): two-sided pruning leaves $\lvert\mathrm{Cl}(\mathrm{GL}(d/2,2))\rvert=2^{d/2+o(d)}$ children | **high** (for the conclusion; the literal inequality stands) |
| w47 §5.3 falsified | | **sound as literal statement**; two-sided analogue is not refuted (§5) | medium (framing) |
| R, effect of R1 on this family | | **sound** | none |
| R1, soundness | | still **unverified** at inner nodes, as the memo says | open |
| §5.3 bullet, Kantor | | **sound with fix**: bounded exceptions exist (§6); conclusion OK for large $m$ | low |
| §7, polar row | | **sound with fix**: $\mathrm{U}(k,2)<\mathrm{O}^{(-1)^k}(2k,2)$, not always $\mathrm O^-$ | low |

No break found in: fullness of the tests, $F=F_{\rm tot}$, the Case 2b orbital, primitivity, the rank scheme, dominance, the exactness of the rectangle answer, the orbit-chain order, the top primitive quotient, the Small test, the index formula, or Lemma L′'s proof.

## 1. Method

Everything below was run with my own harness. nauty 2.9.1 and GAP 4.15.1 at the store paths in `common.py`.

| Script | Purpose | Result |
|---|---|---|
| `common.py` | $Q$ built from the polar form on the tensor basis, checked against the memo's sum of minors and against $Q|_{R_1}=0$ on $(2,2),(4,2),(4,4),(6,2)$ | agree |
| `lambda_full.c` | exact $\lambda(v)=\lvert S\cap(S+v)\rvert$ by Walsh transform, including the **in-range** $(6,4)$ ($2^{24}$ points) | formula exact on every class, $R_1$ separated from $H$ |
| `nauty_groups.py rect` | $\lvert\mathrm{Aut}(B)\rvert$; each nauty generator reconstructed as linear $(\alpha,\gamma)$ acting by $M\mapsto\alpha M\gamma^{*}$ | $(4,3)$, $(5,3)$: order exact; all 9 and 14 generators reconstructed |
| `nauty_groups.py rect d e b c` | other colour choices $(b,c)$ | $(4,3)$: $(2,1),(2,2)$ give the same order |
| `nauty_groups.py bil`, `x` | $\lvert\mathrm{Aut}(\mathrm{Bil})\rvert$, $\lvert\mathrm{Aut}(x)\rvert$ | $(4,3)$; $(4,2)$, $(6,2)$: exact |
| `closures.py` | coherent closure by Walsh convolution, for $R_1$, for every other $F_0$-orbital ($e=2$), and for R1 | §3.2 |
| `lean_rule.py` | Lean's `rcFind` on the rank scheme, random labellings with labels $0,1$ $R_1$-related | always $W$, $R_1$, edge colour $e$ or $e-1$ |
| `twosided.c`, `sp_gens.g` | orbits of $\mathrm{Sp}(d,2)$ on nondegenerate alternating forms = double cosets | §4 |
| `check_numbers.py` | index formula, exponents, scale, class counts | §7 |
| `spot_candidates.g`, `spot_polar.py` | two failed-candidates rows | §6 |

**What computation cannot reach.** $e\ge2\kappa=128$; HJ on any input in range; (H0). The trace below is by hand against the LaTeX and the Lean source. $\mathrm{Aut}(x)$ was not computed directly at $e\ge4$ ($(6,4)$ has $2^{24}$ vertices and degree about $2^{23}$): there I have only the exact $\lambda$ table plus the hand proof of §2.3 (Bil), which nauty confirms at $(4,3)$.

## 2. Group theory

I re-derived L′, Bil, Aut, B′ by hand. No error found. Points tested specifically.

* **L′.** The three codegrees; that the sets $\{a:(a,b)\in N_B(M)\}$ are exactly the $(e-1)$-flats missing $0$; the intersection step (it needs $d-e+1\ge2$, which holds); $f$ additive and $c=0$; $\gamma$ needs $e\ge3$ for planes to exist. No swap, since $\lvert W\rvert\ne\lvert R_1\rvert$; no kernel, since over $\mathbb F_2$ a pure tensor determines its factors. The action is faithful on $W$, as nauty's generators confirm.
* **Bil.** The statement "$\{(a,b):\mathrm{rk}(M+a\otimes b)=\rho-1\}$ is $N_B$ of $\mathrm{Row}(M)^*\to\mathrm{Col}(M)$" looks too strong at first, since $a$ in the column space alone seems enough when $b\notin\mathrm{Row}(M)$. It is not: for $b\notin\mathrm{Row}(M)$ the kernel does not grow and the rank does not drop. The claim is right.
* **Aut.** The formula for $\lambda$ was verified by exact transform on **all** classes at $(4,2),(6,2),(8,2),(6,4)$, including $\Delta(2)=0$ at $e=2$. At the in-range $(6,4)$: $\lambda_{R_1}=4192844$, $\lambda_H(\rho)-\lambda_{R_1}=540,406,342$ for $\rho=2,3,4$, exactly the memo's $\Delta$. **Non-affine automorphisms are excluded by §2.3 (Bil), not by this table**: $\lambda$ gives only that every automorphism preserves the edge set $\mathrm{Cay}(\Phi,R_1)$. So the $e\ge4$ result rests on Bil. Bil is independently Hua's theorem, and nauty confirms it at $(4,3)$; I did not find a counterexample path.
* **B′.** Re-derived. The same argument, with the stabilizer of a pair in place of a point, shows that **every** maximal overgroup of the stabilizer of $(M,M')$ in $A$ has the form $T_V\times\mathrm{GL}(U)$, for every hierarchy. So Step 7's "in every tower $P\cong\mathrm{GL}(d,2)$" needs no case split.
* **"Is $d$ even needed?"** Only to have $\omega$. L′, Bil, B′ hold for all $d>e\ge3$.

## 3. The trace (Theorem T)

### 3.1 Step-by-step, against the paper and Lean

| Step | Interception tried | Result |
|---|---|---|
| Root | $\Omega=[n]^2$, $\mathrm{Sym}(n)$ intransitive; $\Omega_1$ first (L623); Small fails; normalize to $\mathrm{Alt}(n)$ | as stated |
| `RowStep` | $q=n>\lambda=N^\alpha$, $\alpha<\tfrac12$ (L1098); two-label map | not taken |
| Tests | $T,T'$ of the memo; $F_0\le\mathrm{Alt}(n)$ since $e\ge6$ | Full; `Nonfull` impossible since $\mathrm{Aut}_{P_T}(x)\le A_i$ induces $\mathrm{Alt}(T)$ |
| $F$ | Helfgott L1913: generated by all $K(T)$, $T$ full; normal in $\mathrm{Aut}_{G_0}(x)=F_{\rm tot}$ | $F=F_{\rm tot}$. The minimal-normal and projection arguments are correct |
| Case | $\Phi=\Gamma$, not giant (L2798, Helfgott L1929–34) | Case 2b, $d_{\rm tr}=1$, no anchors |
| Orbital | $R_1$ is a single $F$-orbital; smallest for $d\ge e+2$ (confirmed $(4,2),(6,2)$) | choice (a) |
| Closure | binary colouring by $R_1$, then canonical refinement (L2807) | rank scheme; `closures.py` confirms $(4,2),(4,3)$; it is primitive |
| Balance | $\lvert W\rvert/n\ge1-2^{e-d}$ | dominant class $W$, no balanced partition |
| Rectangle | Helfgott Thm 5.3 proof (L1445–47); Lean `rcCond` | $B$ or its complement (§3.3) |
| **Answer** | **Is the query string just the matrix, or does it carry $H$?** L4445 ("Pull the matrix color"), Lean `AuxPairRect`: strings are matrix entries only | **No $H$-information reaches the query.** Permitted group full since $\lvert Y\rvert\ge2$ (L4480). Under H0 the answer is $\mathrm{Aut}(B)$, and $L=\mathrm{GL}\times\mathrm{GL}$ by L′ |
| Continuation | L1077 `LiftAndContinue`; $H=(L\times\mathrm{Sym}(\Gamma\setminus W))\cap\mathrm{Alt}$ | $H$ intransitive; $O_{\rm gen}$ first (L1181: largest orbit) |
| Dispatcher | L1154, L1766 | $P\cong\mathrm{GL}(d,2)$, primitive, not Cameron, Small holds; $\lvert P\rvert$ children |

This is the place the brief told me to look first. It does not break: the rectangle really does forget $H$, because HJ's Case 2b refines only the orbital membership (L2807) and the query is built from configuration colours alone. The larger group is exactly $\mathrm{Aut}(B)$.

### 3.2 Admissibility

The theorem's content is the choice (a). `closures.py` at $e=2$ (the only size where every $F_0$-orbital can be tried):

| $(d,e)$ | orbital | closure classes | largest class $/n$ |
|---|---|---|---|
| $(4,2)$ | $R_1$ | 3 (rank scheme) | 0.820 |
| $(4,2)$ | rank 2, $Q=0$ | 3 | 0.645 |
| $(4,2)$ | rank 2, $Q=1$ | 3 | 0.527 |
| $(6,2)$ | $R_1$ | 3 (rank scheme) | 0.954 |
| $(6,2)$ | rank 2, $Q=0$ | 3 | 0.538 |
| $(6,2)$ | rank 2, $Q=1$ | 3 | 0.508 |

With any other orbital, at these sizes, no class exceeds $\eta=\tfrac34$, so the step gives a balanced partition and no rectangle. So (a) is genuinely load-bearing and not a technicality. For $e\ge4$ I could not run the other orbitals ($F_0$ has many orbitals there and the closure is too expensive at $(6,4)$).

The memo is honest about this in the theorem statement ("under the admissible choices"), but "HJ as written" in §0 and §4 reads as if it were a statement about all runs. It is a statement about *one* resolution of a free choice.

### 3.3 Lean's colour rule (the untraced item)

Lean does **not** leave these open as the memo says; the program fixes them:

* `AggItemSrcP.itSrcOf` uses `stSrc2b`: the six smallest points of the dominant orbit. So at $d_{\rm tr}=1$ the source vertex is the smallest label and the orbital is the $F$-orbital of the pair of the two smallest labels. (`st_orbitalOut_good` says only that every such tuple is *valid*; `Algorithm/Aggregation.lean` also has a classical default, and the Impl layer replaces it by these scans.)
* `AggRectCertMath.rcFind` takes the first index $t=an^2+bn+u$ passing `rcCond`, over fiber positions in increasing label order.

Consequences, with labels the vertex labels up to the map $\pi$ of `GiantLabels` (the paper derives $\Gamma$ from the action; I did not trace Lean's construction of $\pi$, so "labels $0,1$" below means positions in $\Gamma=$ `Fin q`):

1. **Choice (a) holds iff labels $0,1$ are $R_1$-related**, so it is a property of the input labelling. It is available to an adversary, and has probability about $2^{d+e-de}$ on a random labelling.
2. **Given (a), choice (b) is forced**: $a=\min W$, $b=1$ (since position 0 is the source and position 1 is rank 1), $u=\min W$. So $R=R_1$ and the edge colour is the colour of $(u,1)$, namely rank $e-1$ or rank $e$. `lean_rule.py`: 23 random labellings at $(5,3),(6,3),(4,2),(6,2),(8,2)$, always $(W,R_1,\text{edge}\in\{e-1,e\})$. Rank $e$ is the common case: Lean usually gets the **bipartite complement** of $B$ (which Helfgott's cyan $\ne$ aqua would exclude, but Lean's `rcCond` does not). The automorphism group is the same, so L′ applies.

So the memo's "I did not trace" gap closes in its favour. Other colour pairs permitted by the paper give the same $\mathrm{Aut}$ at $(4,3)$ (`rect 4 3 2 1`, `rect 4 3 2 2`), so (b) may not be needed at all, but I have no proof of that in general.

**Corrected wording (T).** Replace "(a)–(b)" by: "for any resolution in which the Case 2b source orbital is $R_1$; in the Lean program this holds exactly when the two smallest $\Gamma$-labels are $R_1$-related, and then (b) holds automatically, with edge colour rank $e-1$ or rank $e$."

## 4. Theorem P: where the pruning claim breaks

**The inequality is correct.** Elements of $\mathrm{Aut}_H(x|_{O_{\rm gen}})$ act on $W$ as elements of $L$ that preserve $H\cap W$; the Reed–Muller step, which uses $\lvert W\rvert/n>\tfrac34$, is sound; $\rho(F_0)=\mathrm{Sp}(V)$. The left-orbit count $[\mathrm{GL}:\mathrm{Sp}]$ is exact, and the index formula and the exponent $\tfrac1{8e^2}$ are correct (§7).

**The claim about pruning is not.** §4 calls $C=\mathrm{Aut}_G(x)$ "the strongest possible version" of pruning, says the children "are genuinely inequivalent under every automorphism", and §6 concludes "any improvement must change the path … and not the pruning". All three are false. At a node with kernel $K$, the sets $\mathrm{Iso}_{K\tau}(x,y)$ are translated by certified automorphisms on **both** sides: $a\in\mathrm{Aut}_G(x)$ on the left and $b\in\mathrm{Aut}_G(y)$ on the right. One child per double coset of $\rho(C_x)\backslash P/\rho(C_y)$ suffices, and the full answer is recovered in the usual way, because every element of $\mathrm{Iso}$ lies in a translate of a pruned representative. $C_y=F_y\cap H$ is computed at the root exactly as $C_x$ is: local certificates are computed for both strings. On a live branch ($Y\cong x$, the rectangle aligned) $\rho(C_y)=\mathrm{Sp}(\omega')$ for a conjugate symplectic form, so:

$$\#\text{children}=\bigl|\mathrm{Sp}(\omega)\backslash\mathrm{GL}(d,2)/\mathrm{Sp}(\omega')\bigr|=\#\{\mathrm{Sp}(\omega)\text{-orbits on nondegenerate alternating forms on }V\}.$$

Pairs of alternating forms with $\omega$ nondegenerate are classified by similarity of $\omega^{-1}\beta$, with $V\cong M\oplus M$ as an $\mathbb F_2[T]$-module (Scharlau). So the count is the number $c(d/2)$ of conjugacy classes of $\mathrm{GL}(d/2,2)$. (Scharlau's classification is from memory; the exact orbit counts below confirm it for $d\le8$, where 14 was predicted before the $d=8$ run.) An invertible matrix's similarity class is a partition of $k$ together with monic invariant factors, so $c(k)\le p(k)2^k$ with $p$ the partition function, hence $c(d/2)=2^{d/2+o(d)}=N^{(1/(4e))(1+o(1))}$; numerically $c(k)\le2^k$ for all $k\le32$ (`check_numbers.py`).

| $d$ | nondegenerate forms $=[\mathrm{GL}:\mathrm{Sp}]$ | orbits of $\mathrm{Sp}$ (exact, `twosided.c`) | classes of $\mathrm{GL}(d/2,2)$ |
|---|---|---|---|
| 2 | 1 | 1 | 1 |
| 4 | 28 | 3 (sizes 1, 12, 15) | 3 |
| 6 | 13888 | 6 (sizes 1, 315, 2880, 2880, 3780, 4032) | 6 |
| 8 | 112881664 | 14 (largest 16450560) | 14 |

So the superpolynomial count is a property of one-sided pruning. **Corrected statement (P).** "PHJ with left pruning by any subgroup of $\mathrm{Aut}_H(x)$ creates at least $[\mathrm{GL}:\mathrm{Sp}]$ children at the node; with $C=F\cap H$ the count is exactly that. Two-sided pruning, using $F_y\cap H$ on the right as well, leaves exactly $\lvert\mathrm{Cl}(\mathrm{GL}(d/2,2))\rvert=2^{d/2+o(d)}$ children (on the live branch)." §4's "strongest possible", "genuinely inequivalent", and §6's "not the pruning" should be deleted. The statement that remains true is that one-sided automorphism pruning does not suffice.

## 5. The conjecture, and what survives

The conjecture of w47 §5.3, as written, reads "$\lvert P\rvert\le N^{O(1)}\cdot\lvert\text{image of }\mathrm{Aut}_H(x)\text{ in }P\rvert$". It is one-sided, and T + P refute it (for fixed $e$, $d\to\infty$), so the falsification is correct, conditional on (H0), HJ as written, and (a).

But the mechanism does not refute the natural two-sided form:
$$\lvert P\rvert\le N^{O(1)}\cdot\lvert\rho(\mathrm{Aut}_H(x))\rvert\cdot\lvert\rho(\mathrm{Aut}_H(y))\rvert,$$
which on this family reads $\lvert\mathrm{GL}\rvert\le N^{O(1)}\lvert\mathrm{Sp}\rvert^2$, and holds easily: $\lvert\mathrm{GL}(d,2)\rvert/\lvert\mathrm{Sp}(d,2)\rvert^2<1$ for $d\ge4$. Even this form only bounds below; the sharper count is the double-coset number. I recommend the memo restate its open problem in double-coset terms. This also changes §0's "What is new" and the conclusion that Lie-type enumeration on this family is untouched by automorphisms.

## 6. Case 2b, R1, and the failed-candidates table

* **Diagnosis.** Correct. Helfgott L1934 gives the Schurian configuration; at $(4,2),(6,2)$ the $F_0$-orbits refine $H$, so no class exceeds about $\tfrac12$ (a class of the Schurian configuration is contained in a value of $Q$ together with a rank). HJ's L2793–2813 replaces it by one orbital for the stated reason (orbital names are not canonical).
* **R1 effect.** Correct: `closures.py` gives maximal class fraction $0.469$ at $(4,2)$ and $0.492$ at $(6,2)$. The bound $(\tfrac12+o(1))q$ is immediate from the colours $H$ versus $\Phi\setminus S$. Soundness at inner nodes remains the memo's named gap.
* **Kantor row (§7).** The statement "line-transitive forces $F\ge\mathrm{SL}$" is false as an unrestricted statement. $\Gamma\mathrm L(1,32)$ is transitive, indeed regular, on the 155 lines of $\mathrm{PG}(4,2)$ (`spot_candidates.g`). $A_7<\mathrm{GL}(4,2)$ is **arc-transitive on meeting pairs** of $J_2(4,2)$ (630 ordered pairs, one orbit) with index $8$. Both are bounded exceptions, so the row's conclusion for large $m$ is unharmed, but the citation needs an "$m$ large enough" and a list of exceptions. I could not retrieve Kantor's paper text; a search returned only related Kantor papers, which confirm the $A_7$ exception.
* **Polar row.** $\mathrm U(k,2)<\mathrm O^{(-1)^k}(2k,2)$; the memo's $\mathrm O^-(2k,2)$ is right only for odd $k$ (`spot_polar.py`: $k\le6$, singular counts match exactly). The density-$\tfrac12$ conclusion is unaffected.

## 7. Parameters

* Index: `check_numbers.py` confirms the closed form for $d\le64$, and at $d=260,e=128$: $\log_2[\mathrm{GL}:\mathrm{Sp}]\approx33669$, against $(\log_2N)^2/(8e^2)=33800$.
* $\kappa=64$ (L1820). $e\ge128$, $d\ge2e+3=259$, but $d$ must be even, so $d\ge260$ and $n\ge2^{33280}$. The memo's $2^{33152}$ uses the odd $d=259$, which the theorem excludes. It remains true as a lower bound but should be corrected.
* $d_0$ is named but not computed, as in w47. It should be read as "at least".

## 8. What could not be checked

* All computation is at $e\le4$. Nothing reaches $e\ge2\kappa$. No HJ run exists here.
* (H0), and HJ's correctness.
* $\mathrm{Aut}(x)$ by direct search at $e\ge4$. Non-affine automorphisms are excluded only by the proof of Bil plus nauty at $(4,3)$.
* Other orbitals at $e\ge4$ (§3.2).
* The exact map from input vertices to `GiantLabels` in the Lean program.
* Soundness of R1 at inner nodes. Whole-tree statements for pruned HJ, which the memo also disclaims.
* Kantor's paper itself.

## 9. Fix list for the author

1. §4, §6: state the left-only scope of PHJ; delete "strongest possible", "genuinely inequivalent under every automorphism", "not the pruning"; add the double-coset count.
2. §5.3 and §6: restate the open question in two-sided form; note that T does not refute it.
3. §3: replace (b) and "the Lean tree leaves them open" by the Lean rule; state the labelling dependence.
4. §3: $n\ge2^{33280}$.
5. §7: bounded exceptions for Kantor; $\mathrm O^{(-1)^k}$.
6. §0: "HJ as written" should say "for an admissible resolution of the free choice in Case 2b".

Sources: arXiv:2611.01399 (local LaTeX) · [Helfgott, arXiv:1710.04574](https://arxiv.org/abs/1710.04574) (local) · Lean tree `Algorithm/OutOrbital.lean`, `AuxRectangle.lean`, `AuxPairRect.lean`, `Impl/AggStructMath.lean`, `AggItemSrcP.lean`, `AggRectCertMath.lean` (read only) · Kantor's 1972 paper was not retrieved; a search returned only related Kantor items that I did not read in full ([1](https://darkwing.uoregon.edu/~kantor/PAPERS/ClassJordanGps.pdf), [2](https://msp.org/pjm/1973/48-1/p13.xhtml), [3](https://www.arxiv.org/abs/1806.02203)), whose snippets support the $A_7$ exception.
