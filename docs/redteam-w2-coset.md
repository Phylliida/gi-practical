# Red-team report on `docs/w2-coset.md`

Branch `w3-redteam-coset`, 2026-11-05. Target: the claims of `docs/w2-coset.md` ("W" below; "W L…"
is a line of that file). Background: `w1-fpt.md` ("FPT"), `w1-structure.md` ("STR"),
`redteam-w1-fpt.md`, `redteam-w1-structure.md` ("RT-STR").

**Sources.**
* GNS: `r4-sources/arxiv-1802.04659/x/bounded-degree-polylog-d.tex` ("G…" = line).
* Babai: `r4-sources/arxiv-1512.03547/x/main.tex` (abstract and §1.1, L196–300).
* ADKT: `r4-sources/w1fpt-adkt/adkt.txt` (ECCC TR09-093), Thms 3, 5, 6.
* Schweitzer–Wiebking arXiv:1806.07466 and Wiebking arXiv:1904.10454 (already downloaded):
  introduction, the codes corollary, open questions.
* arXiv:2504.19777 (already downloaded), §"Twisted Code Equivalence over small domains", which
  restates BCQ12 Thm 5 = Codenotti Thm 4.2.1 with its proof.
* **New download:** Codenotti's PhD thesis (Chicago 2011),
  `people.cs.uchicago.edu/~laci/students/codenotti.pdf`, saved in the new directory
  `r4-sources/w3rc-bcq/`. It was fetched with `curl -k`, because the host's certificate chain did not
  verify in this sandbox; it is treated as untrusted data. It was converted to text by
  `scratchpad/w3rc-scripts/pdf2txt.py` (pypdf, `python3 -I`). I read §1.1.4 (results), Thm 2.3.10
  (CI bound), and Ch. 4 (Def. 4.1.3, Thm 4.2.1 with its proof, Cor. 4.2.2).
* **Web search was unavailable** (session rate limit). The novelty search in §2 therefore covers
  only the papers named above, plus what I remember.

**Executed** (all under `nice`, scripts in `scratchpad/w3rc-scripts/`, run with `python3 -I`):
1. `thmP_redteam.py`: an independent implementation of Theorem P's recurrence (sets in place of CI),
   checked against brute force. 72 instances: shapes $(b,k)\in\{(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)\}$;
   group kinds random, top-only, diagonal and cyclic-top-plus-base, with $\lvert G\rvert$ up to 3840;
   random, Hamming-weight and constant strings. Under a minute in total.
2. `tbox_check.py`: automorphism groups of coloured $T\,\square\,T$ by VF2 (networkx), compared with
   the predicted subgroup of $W\times W$. About two minutes.
3. `examplex_check.py`: Example X for $r=3$, $L=3$: explicit permutations of the 512 points, and
   sympy group orders on 64 points. Seconds.

Lean was not run.

**Severity scale.**
* *Break*: the claim is false and cannot be repaired.
* *Gap*: the claim is true, or true after a stated repair, but the argument misses or misstates a
  step.
* *Overstatement*: the claim as worded covers more than is proved.
* *Cosmetic*: wording, constants, citation.

---

## 0. Verdicts

| # | claim | verdict | defects |
|---|---|---|---|
| 1 | **Theorem P** (PA-SI in $b!\,N^{3.17+o(1)}$, any top group) | **sound** (correct, cost bound holds) | Gap (low): the base case and the $C_{j',\pi}$ are **setwise** transporters of partial transversals. They are not Schreier–Sims computations, and in general they are as hard as SI for the top group. One CI call on $V$ each repairs this, and the bound is unchanged (§1.2). The table is smaller than claimed: $(1+b^2)^k$ reachable states, so the exponent is $\log_b(1+b^2)\le2.32$, not 3.17 (§1.3). Cosmetic: a factor $\exp(O(\log^cb))$ is dropped (§1.4). |
| 2 | Novelty of Theorem P | **not new in substance** | The recurrence is BCQ12 Thm 5 = Codenotti Thm 4.2.1 almost verbatim. The "arbitrary top group" follows from the full-wreath case by **one** extra coset intersection on $V$. STR §4.5 row (c) already said this, labelled [SKETCH]. The only addition is the arithmetic showing that the CI cost on $b\log N$ points is $f(b)N^{o(1)}$ (§2). |
| 3 | Thm 2.1 equivalences TreeSI ≡ TreeCI ≡ PCI ≡ PCI$_{\rm diag}$ ≡ $T^2$ | **sound** as statements about the abstract problems | Gap (medium, interpretive): Cor. 2.2 reads PCI$_{\rm diag}$-completeness as saying that "the full-diagonal combine step of the block DP" is hard. Combine steps that the DP actually produces with a full-diagonal kernel are never genuine CIs. They are SI on one child with a tuple alphabet (W's own §4.4). The minimal hard shape the DP produces is a diagonal on a **direct factor** ($K=K_1\times\mathrm{diag}(G_2)$, as in $\mathcal T\otimes\mathcal T$) (§3.3). Cosmetic: node counts with unary nodes, and unequal depths in $T^2$ (§3.2). |
| 4 | Lemma 2.4 (almost $d$-ary ⇒ tree group of degree $d!/2$) | **sound** | It matches GNS's definition exactly (G960–966). Cosmetic: $d\ge3$ suffices. Depth padding is needed. The "Use" paragraph understates GNS's blow-up: it is $n^{O(\log^2d)}$, not $n^{O(\log d)}$ (§4). |
| 5 | Example X collapse for $r\ge3$ | **argument sound for levels $j\ge3$; conclusion "$\varepsilon=1$" overstated** | Verified with explicit permutations. Level 2 has only one node per level-1 subtree, so step 4 is unavailable there. If level 1 carries only translations, the level-2 pairing **survives**: computed $\lvert\mathrm{GL}(3,2)\rvert^{4}$ instead of $\lvert\mathrm{GL}(3,2)\rvert^{8}$, so $\varepsilon_{\rm root}=\lvert\mathrm{GL}(r,2)\rvert^{2^{r-1}}$. This is still $f(d)$, so the FPT conclusion (Theorem E) stands. With $\mathrm{GL}$ at the root, level 2 decouples too (§5). |
| 6 | Prop. 6.1: $\mathrm{Aut}$ of coloured $T\,\square\,T$ is $\{(\alpha,\beta)\in W\times W\}$, or the diagonal if marked | **sound** | Proof re-derived. VF2 confirms it on 22 cases, including $\lvert\mathrm{Aut}\rvert=\lvert W\rvert^2$ and $\lvert W\rvert$ on trivial colourings. Without the depth colours there are extra automorphisms (the factor swap: 128 vs 64). Cosmetic: "GI$_{\deg}(2b+2)$" means *coloured* GI (§6). |
| 7 | Theorem E′ [SKETCH] | **plausible; no counterexample** | Missing: (i) STR Prop. 2.2 (still a SKETCH, with RT-STR's two repairs); (ii) product-structure recognition [TRUST]; (iii) the fibre-product bookkeeping for diagonal and twisted types, where the children are a quotient of $T^k$, not $\Delta^k$; (iv) the setwise-transporter repair of item 1, which carries over to the base case. Steps 1 and 2 themselves check out (§7). |

**No break found.** Every [PROVEN] item is true, after at most a one-line repair. The real issues
are: Theorem P is a corollary of BCQ/Codenotti rather than a new algorithm; Cor. 2.2 over-reads
PCI$_{\rm diag}$; and the Example X conclusion ignores level 2.

---

## 1. Theorem P (W L241–320)

### 1.1 What I checked

* The DP state space and the recurrence, line by line.
* Correctness, in an independent implementation (script 1) on shapes other than the agent's $k=b=3$.
* That every table entry is empty or a right coset.
* That the transporter $C_{j',\pi}$ is redundant.
* The cost of each primitive operation.
* The asymptotics of Babai's bound on $bk$ points.

### 1.2 Correctness: sound, with one misattributed primitive

**Recurrence.** Fix a branch $(j',\pi)$. Every $z\in\Delta^{[k]\setminus J}$ has a unique $a=z_j$,
and then $(u+(j,a))^g=u'+(j',\pi a)$. So $g\in I(J,u;J',u')$ with $(j,a)^g=(j',\pi a)$ iff
$g\in\bigcap_aI(J{+}j,u{+}(j,a);J'{+}j',u'{+}(j',\pi a))$.
* *Coset structure.* $I(J,u;J,u)$ is a group, the setwise stabiliser of $u$ intersected with the
  link-string stabiliser. $I(J,u;J',u')$ is a right coset of it.
* *Union step.* The generators "branch groups plus $r_\beta r_{\beta_0}^{-1}$" are correct.
* *$C$ is redundant for $b\ge2$.* Intersecting the conditions for two values $a\ne a'$ gives
  $u^g=u'$, and then $(j,a)^g=(j',\pi a)$.

Script 1 confirms all of this. Over 72 instances, the recurrence agrees with brute force both with
and without $C$, and every memoised entry is empty or a coset (`cosetfail=0` throughout). Cases with
large isomorphism cosets are included: $\lvert G\rvert=1296$, $\lvert\mathrm{Iso}\rvert=48$; constant
strings with $\mathrm{Iso}=G$; $\lvert G\rvert=3840$.

**The flaw tiny instances cannot see.** W L280–281 says the base case is "a point transporter,
computed by Schreier–Sims on $V$". It is not. A full point $u\in\Delta^k$ is a *set* of $k$ points of
$V$, and $\{g:u^g=u'\}$ is a **setwise** transporter. (The same applies to $C_{j',\pi}$, whose
condition on $u$ is setwise.) In general that is not a Schreier–Sims computation:
* Take $G=K\le S_k$ acting by pure coordinate permutations, $(j,a)^\sigma=(\sigma j,a)$, with $b=2$.
  Then $u\leftrightarrow S=\{j:u_j=1\}$, and $\{g:u^g=u'\}$ is the set transporter $S\mapsto S'$ in
  $K$ on $[k]$.
* That set transporter is SI for an arbitrary $K$ with binary strings, which is GI-hard.

The brute-force scripts (W's and mine) filter $G$ explicitly, so they cannot detect this.

*Repair.* $\{g\in G:u^g=u'\}=G\cap\Sigma_{u\to u'}$, where $\Sigma_{u\to u'}$ is the explicit coset
of $\mathrm{Stab}_{\mathrm{Sym}(\Delta)\wr S_k}(u)\cong S_{b-1}\wr S_k$ that maps $u$ to $u'$. That is
one CI on $V$. There are $\le N^2\le(1+b^2)^k$ base entries, so the claimed time bound is unchanged.
(Alternatively, drop $C$ entirely and pay one CI per base entry.)

**Arbitrary top group.** The top group is genuinely never enumerated. Branching is over
$j'\in[k]\setminus J'$ and $\pi\in S_b$ only, and $K$ enters only through the cosets. Script 1's
"top-only" and "cyclic-top+base" kinds exercise exactly this case.

### 1.3 State space: smaller than claimed

$j=\min([k]\setminus J)$ and the start is $J=\varnothing$, so **$J$ is always an initial segment
$\{1..s\}$**. Only $J'$ is free. The reachable states are therefore
$$\sum_s b^s\binom ks b^s=(1+b^2)^k=N^{\log_b(1+b^2)},$$
not $\sum_s\binom ks^2b^{2s}\le(1+b)^{2k}$. Script 1 reaches exactly 100 $=(1+3^2)^2$ states on a
$b=3,k=2$ constant-string instance and never more than $(1+b^2)^k$. The exponent is
$\log_2 5=2.32$ at $b=2$ (and $2.10$ at $b=3$), not 3.17. Per state there are $k\cdot b!$ branches
of $b$ CIs, so

$$T\le(1+b^2)^k\cdot k\,b!\,b\cdot\mathrm{CI}(bk)\ \le\ b!\,N^{2.33}\cdot\mathrm{CI}(b\log_2N)\cdot\mathrm{poly}.$$

Codenotti's sparse-table accounting (§2) gives $k\,2^kN^2$ entries, which is weaker here.

### 1.4 The CI cost

* Babai's abstract and §1.1 (L196–300) state CI in $\exp((\log n)^{O(1)})$, with $n$ the domain size.
* Write $(\log(bk))^c\le2^{c-1}\bigl((\log b)^c+(\log k)^c\bigr)$ (convexity, $c\ge1$) with
  $k\le\log_2N$. Then
  $$\mathrm{CI}(bk)\le e^{2^{c-1}\log^cb}\cdot N^{2^{c-1}(\log\log N)^c/\log N}=f(b)\,N^{o(1)}.$$
  The $o(1)$ depends on $N$ only. **Correct.**
* W then writes "$b!\cdot N^{3.17+o(1)}$", which drops $f(b)=b^{O(\log^{c-1}b)}$. Since
  $f(b)=(b!)^{o(1)}$, the honest form is $(b!)^{1+o(1)}N^{\log_b(1+b^2)+o(1)}$. *Cosmetic.*
* Babai 1983 / BKL83 give $\exp(\tilde O(\sqrt n))$ (also Codenotti Thm 2.3.10). W's split at
  $b\approx\log N/\log^4\log N$ is right and gives $2^{O(b\log^4b)}N^{O(1)}$. **Correct.** So
  quasipolynomial CI is **not needed** for FPT. Babai 1983 suffices.

**Verdict on claim 1: sound.** Correctness was checked independently. The cost bound holds after
the base-case repair, and the exponent improves to $\log_b(1+b^2)$.

---

## 2. Novelty of Theorem P

**BCQ12 Thm 5 = Codenotti Thm 4.2.1** (thesis Ch. 4, pp. 70–74; restated in arXiv:2504.19777).
* *Problem.* Twisted code equivalence of $\mathcal A\subseteq\prod_i\Gamma_i^{A_i}$ under
  $\prod_iG_i\wr\mathrm{Sym}(A_i)$.
* *Algorithm.* The table is indexed by pairs of partial strings. The domain of $y$ is extended at a
  fixed index $r$, and the algorithm branches over $s\in B_i$ and $g\in G_i$:
  $$I(y,z)=\bigcup_{s}\bigcup_{g}\bigcap_{\gamma}I(y(r,\gamma),z(s,\gamma^{g^{-1}})).$$
  The CIs run in $\prod G_i\wr\mathrm{Sym}(A_i)$, on $d=\sum\lvert A_i\rvert d_i$ points. This is
  W's recurrence, with $(j',\pi)\leftrightarrow(s,g)$.
* *Colours.* A string $x:\Delta^k\to\Sigma$ is the code $\{(z,x(z))\}$ over two alphabets: $(\Delta,k)$
  with $G_1=\mathrm{Sym}(\Delta)$, and $(\Sigma,1)$ with $G_2=1$. So
  $\mathrm{EQ}=\mathrm{Iso}_{\mathrm{Sym}(\Delta)\wr S_k}(x,y)$.
* **Arbitrary $G$:** $\mathrm{Iso}_G(x,y)=\mathrm{Iso}_{\mathrm{Sym}(\Delta)\wr S_k}(x,y)\cap G$, which is one
  more CI on $V$. STR §4.5 row (c) already noted "a subgroup $K<S_k$ needs a final coset
  intersection on $k\lvert M\rvert$ points [SKETCH]". (RT-STR §7's remark that "a top group $K$ …
  must still be enumerated" overlooked this.)
* *Cost as stated by Codenotti:* $O(n^2\,2^{n+d}\lvert G_{\max}\rvert\lvert\Gamma_{\max}\rvert\lvert\mathcal A\rvert^2\log\lvert\mathcal A\rvert)$.
  The proof bounds CI by "$2^{\sqrt d\log^2d}=O(2^d)$". With $d=bk$, $2^d=N^{b/\log_2b}$, which is
  XP. Keeping $2^{\sqrt d\log^2d}$, i.e. his own Thm 2.3.10, gives $f(b)N^{O(1)}$ by the split
  of §1.4.

**Other candidates.**
* *ADKT* (Thms 5, 6): colour classes of size $b$ are fixed setwise. A top group that permutes
  coordinates is outside its scope, or costs $2^{O(bk)}$.
* *S-W 2019*: codes and objects in $2^{O(\lvert V\rvert)}\mathrm{poly}$, which is
  $2^{O(bk)}$ here (XP).
* *Luks 1999*: $c^{\lvert V\rvert}$ (XP).
* *Wiebking 2019*: simply exponential in the degree (XP).
* *Babai's Cameron-case handling*: from memory, Babai treats product actions of
  giants by reduction to the socle factors inside his recursion, which is not an FPT statement in
  $b$. I could not re-check it this session.

**Assessment.** Theorem P is BCQ/Codenotti's algorithm, plus one coset intersection, plus an
accounting of the CI cost that the original analysis discarded. W's own Remark 3 ("experts may
regard it as folklore") is accurate. I found no paper that states "SI for subgroups of
$\mathrm{Sym}(\Delta)\wr S_k$ in product action is FPT in $\lvert\Delta\rvert$" explicitly. Without web
search I cannot certify that none exists. **Recommendation:** relabel it "Corollary (of BCQ12 Thm 5 /
Codenotti Thm 4.2.1 and CI)", and cite the thesis.

---

## 3. Theorem 2.1 (W L120–163) and Cor. 2.2 (L165–177)

### 3.1 Reductions checked

| reduction | type | parameter | instance size | check |
|---|---|---|---|---|
| (a) TreeSI ≤ TreeCI | Turing | $b\mapsto b$ | $\le(\#\text{nodes})^2\,b!$ calls on $\le N$ leaves | FPT Prop. 4.1 re-derived. $K_Bh_\sigma\cap\Pi_\sigma$ translated by $h_\sigma^{-1}$ is CI of $K_B$ and a coset of $\prod_i\mathrm{Aut}(C_i)$; both lie in $W(\mathcal T_B)$, and so does the representative (a product of restrictions of tree automorphisms). **OK.** |
| (b) TreeCI ≤ $T^2$ | many-one | $b\mapsto b$ | $N\mapsto N^2$ | $\mathcal T\otimes\mathcal T$ has degree $\le b$ and $G_1\times G_2$ preserves it. Since $\delta^{(h_1,h_2)}=\delta$ iff $h_1=h_2$, translating by $(a,c)$ gives a group instance with $y=\delta^{(a,c)^{-1}}$. **OK.** |
| $T^2$ ≤ TreeSI | identity | $b$ | $N^2$ | **OK**, if the two trees have equal depth; otherwise pad with unary levels. |
| (c) TreeCI ≤ PCI$_{\rm diag}$ | many-one | $b$ | $2N$ | **OK.** |
| (d) PCI ≤ TreeCI | many-one | $b$ | same | $K\cdot1\cap(\prod A_i)(z_i)_i$ on $\mathcal T_B$. **OK.** |

### 3.2 Cosmetic

* "$(2N)^2$ node pairs" assumes every internal node has $\ge2$ children. §1 allows unary nodes, and
  Lemma 2.4's padding creates them. Contract them, or count $(HN)^2$.
* (b) as stated needs $T_1,T_2$ of equal depth (pad).

### 3.3 Interpretive gap in Cor. 2.2 (medium)

Cor. 2.2 says that because PCI$_{\rm diag}$ is TreeCI-complete, "the simplest possible coupling …
is already as hard as all of TreeCI", and that the hard information lies in the "memoised
automorphism cosets of the children. These are arbitrary tree groups."

This is true of the **abstract** problem PCI$_{\rm diag}$, whose child cosets $A_i$ are arbitrary
inputs. It is false of the combine steps that the block DP actually produces with a full-diagonal
kernel:
* If $K_B=\{(r,r^{\varphi_2},\dots):r\in R\}$, then $R\trianglelefteq H_{C_i}$.
* The DP's child cosets are string-isomorphism cosets under $H_{C_i}$. So
  $A_iz_i\cap R=\mathrm{Iso}_R(x_i,y_i)$, by intersection with a normal subgroup (polynomial).
* The combine step for each child bijection $\sigma$ (at most $b!$ of them) is therefore
  $\bigcap_i\mathrm{Iso}_R(x_i^{\varphi_i^{-1}},y_{\sigma i}^{\cdots})=\mathrm{Iso}_R(\text{tuple strings})$.
  That is SI for $R$ on **one child** with a tuple alphabet, not a CI. This is W's own §4.4
  observation ("exact when the child cosets are themselves stabilisers of strings").
* For $R=W$ it is even polynomial (canonical forms under full $W$).

The hard combine steps that TreeSI instances do produce look like the root of $\mathcal T_1\otimes\mathcal T_2$:
* $K=K_1\times\mathrm{diag}(G_2)$, a diagonal on a **direct factor** of $H_{C_i}=(G_1)_{u_i}\times G_2$;
* the child cosets are not products, and the CI in $G_2$ is between *projections*.

So the correct reading is: the coupling *pattern* can be laminar (one diagonal) and the class is still
complete; but the diagonal must sit on a full-depth direct factor, not on the whole child. W's main
conclusion ("coupling depth, not pattern") survives with this correction. Theorem 2.1 itself is
unaffected.

**Verdict on claim 3: sound**, with Cor. 2.2 reworded.

---

## 4. Lemma 2.4 (W L186–219)

**GNS's definition** (G960–966): a $G$-invariant sequence
$\{\Omega\}=\mathfrak B_0\succ\cdots\succ\mathfrak B_k$ (singletons) is almost $d$-ary if for every
$i$ and every $B\in\mathfrak B_{i-1}$, either $G_B^{\mathfrak B_i[B]}$ is semi-regular, or
$\lvert\mathfrak B_i[B]\rvert\le d$. $\hat\Gamma_d$: every composition factor is isomorphic to a
subgroup of $S_d$ (G392), closed under subgroups and quotients (Luks, G400–407). W uses exactly this.

**Proof check.**
* *Orbits.* The parts are unions of $P$-orbits. $G_B$ fixes each part, so the action on parts is
  trivial, and any binary tree over them is invariant. Transport to $B^g$ is well defined because
  $G_B$ fixes everything inserted.
* *Regular orbits.* On one orbit $O$, the semiregular $P$ acts regularly. The right-coset partitions
  $\{o^{H_jx}\}$ are invariant under right multiplication and nested. A block has
  $\lvert H_j:H_{j-1}\rvert$ sub-blocks, and $H_j/H_{j-1}$ is a composition factor of a section of
  $G$, hence embeds in $S_d$, hence has order $\le d!/2$ (non-abelian factors lie in $A_d$) or is
  $C_p$ with $p\le d$.
* So every new step has $\le\max(2,d!/2)$ children. The result is a $G$-invariant
  $s(d)$-ary sequence on the same $\Omega$, i.e. $G\le W(\mathcal T)$. **Sound.**

**Cosmetic.**
1. $d\ge3$ suffices for $d!/2\ge d$.
2. Different blocks get different numbers of inserted levels; pad with unary levels (see §3.2).
3. "GNS reduce SI$(\hat\Gamma_d)$ to this class at domain cost $n^{O(\log d)}$" (L216): GNS Thm
   `reduction-two` (G1281–1290) gives $\lvert\Omega^*\rvert\le n^{(c_1\log d+c_2+1)\log d}=n^{O(\log^2d)}$.

**Verdict on claim 4: sound.**

---

## 5. Example X collapse (W L432–460)

**Steps 1–5 re-derived.**
* Conjugating "$A$ at $n$" by a local translation at a level $<j$ gives "$A$ at $n^\tau$", because
  translations do not touch coordinate $j$.
* The quotient and commutator identities hold: operations at distinct nodes of one level commute.
* $[\mathrm{GL}(r,2),\mathrm{GL}(r,2)]=\mathrm{GL}(r,2)$ for $r\ge3$.

**Script 3** ($r=3$, $L=3$, 512 points) builds each element *only* from the generators by
products, inverses and conjugation, and confirms:
* step 2 gives "$A$ at $(p_1,w_0)$ and $A$ at $(p_1+e_3,w')$";
* step 3 gives "$A$ at $n_1$, $A^{-1}$ at $n_2$";
* step 4 gives exactly "$[A,B]$ at $n_1$", which moves 6 points;
* $\lvert[\mathrm{GL}(3,2),\mathrm{GL}(3,2)]\rvert=168$.

The argument is **correct for levels $j\ge3$**.

**Level 2 is not covered.** Step 4 needs three level-$(j-1)$ nodes below $p_1+e_j$, but at $j=2$
there is one. So the conclusion "it is the uncoupled affine tower: $\varepsilon=1$" (L440) does not
follow. Script 3 computes the action of $\langle R,S\rangle$ on length-2 prefixes (64 points). Write
$\lvert G\rvert=(\text{top})\cdot8^8\cdot Q$, where $Q$ is the order of the level-2 $\mathrm{GL}$ part:

| level 1 carries | $Q$ | meaning |
|---|---|---|
| translations only | $168^4=\lvert\mathrm{GL}(3,2)\rvert^{2^{r-1}}$ | one $\mathrm{GL}$ per pair $\{p,p+e_2\}$: still coupled |
| translations and $\mathrm{GL}(3,2)$ | $168^8$ | fully decoupled |

STR's definition does not say what level 1 carries (the pairing "$p+(e_1,0,\dots)$" is vacuous at
the root). With $\mathrm{GL}$ at the root, conjugation turns the pair $\{p,p+e_2\}$ into
$\{Ap,Ap+Ae_2\}$, all differences occur, and W's argument then also works at level 2. Without it,
$\varepsilon_{\rm root}=\lvert\mathrm{GL}(r,2)\rvert^{2^{r-1}}=2^{O(d\log^2d)}$ (with $d=2^r-1$), and
$\varepsilon=1$ at all deeper nodes.

Either way Theorem E applies with $\varepsilon\le f(d)$, so the FPT conclusion stands, at cost
$\lvert\mathrm{AGL}(r,2)\rvert\cdot\lvert\mathrm{GL}(r,2)\rvert^{2^{r-1}}\mathrm{poly}(N)$ in the
worse case.

**Verdict on claim 5: argument sound; conclusion overstated (low).** Fix: "$\varepsilon_B=1$ below
level 2, and $\varepsilon_{\rm root}\le\lvert\mathrm{GL}(r,2)\rvert^{2^{r-1}}$."

---

## 6. Prop. 6.1: coloured $T\,\square\,T$ (W L598–629)

**Proof check.**
* Colour preservation fixes depth pairs, hence the two edge classes.
* The components of the row-edge graph are the copies $T\times\{v\}$ ($T$ is connected), and
  likewise for columns. A row and a column meet in exactly one vertex.
* So $\varphi=(\alpha,\beta)$, with $\alpha,\beta$ adjacency- and depth-preserving, i.e. in $W$.
* With the diagonal marked, $\alpha(u)=\beta(u)$ for all $u$.

There is no room for exotic automorphisms. (By Imrich's theorem, $\mathrm{Aut}(T\square T)$ for the
prime factor $T$ is $\mathrm{Aut}(T)\wr S_2$. The depth colouring kills the swap, and its root and
depth data force rooted automorphisms.)

**Script 2** compares $\lvert\mathrm{Aut}\rvert$ (VF2) with the number of predicted pairs, for
$(b,h)\in\{(2,1),(3,1),(2,2),(4,1),(2,3),(3,2)\}$, trivial or random $x$, and diagonal marked or not.
* **22/22 agree**, e.g. $\lvert\mathrm{Aut}\rvert=576=24^2$ for $b=4,h=1$, and $1296=\lvert W\rvert$ for
  $b=3,h=2$ with the diagonal marked.
* The maximum degree is $2b+2$ when $h\ge2$.
* Without the depth colours, $b=2,h=2$ gives 128 $=2\lvert W\rvert^2$: the factor swap appears. The
  depth colours are essential.

**Cosmetic.**
* "$P_{\rm graph}(b)\le\mathrm{GI}_{\deg}(2b+2)$" is coloured GI. Uncoloured needs colour gadgets,
  at $+O(1)$ degree.
* $P_{\rm graph}$ is defined on equal-depth pairs, while Prop. 6.1 colours all pairs. This is
  harmless.

**Verdict on claim 6: sound.**

---

## 7. Theorem E′ (W L342–380) [SKETCH]

**Step 1 ($\varepsilon_B=1$).**
* $K_B=\prod_uR_u$. (W writes $K_u$; Krasner–Kaloujnine is not needed, this is the definition of
  $\varepsilon=1$.)
* A lift of $\bar g\in P_B$ exists iff, for every child, $\hat g|_{C_u}\in\mathrm{Iso}(C_u,C'_{u^{\bar g}})R_u$.
  The conditions decouple because $K_B$ is a full product.
* So the projection of $\mathrm{Iso}_{G_B}$ is the set that Theorem P's recurrence computes with
  these base cosets.
* Each base set is the preimage of a coset of $\mathrm{Aut}(C_u)R_u$ ($R_u\trianglelefteq H_{C_u}$)
  under a map defined on the transporter, intersected with the setwise transporter of $u$. That
  makes it a coset (CI on $V$, §1.2).
* The partial entries are projections of isomorphism cosets of $G_B$ on unions of children, hence
  cosets, so the union step is valid. **OK.**

**Step 2.**
* $\prod_uR_u$ is normalised by $G_B$ ($g^{-1}R_ug=R_{u^g}$). So $\tilde G_B=G_B\prod R_u$ is a
  group with kernel $\prod R_u$.
* $\lvert\tilde G_B:G_B\rvert=\lvert\prod R_u:K_B\rvert=\varepsilon_B$, and the child groups are
  unchanged.
* Sieving back to $G_B$ costs $\varepsilon_B\,\mathrm{poly}$. **OK.**

**What is missing.**
1. **STR Prop. 2.2**, still a SKETCH. RT-STR §1.5 flagged the unstated classification of large
   irreducible linear groups. For products of diagonal groups with large top groups the components
   are unbounded. The fix uses the $jk$ socle factors as coordinates, pulled back along
   $T^{jk}\to(D\backslash T^j)^k$, with a blow-up $\lvert T\rvert^k\le d'^{1/(j-1)}$, so it stays
   polynomial.
2. **Recognising the product structure** of $P_B$ (socle and coordinate decomposition):
   standard, [TRUST].
3. **Bookkeeping for diagonal and twisted types.** The children are indexed by a quotient
   $D\backslash T^k$, not by $\Delta^k$. The DP must run in the fibre product of $G_B\to P_B\leftarrow\hat G$,
   where $\hat G\le\mathrm{Sym}(T)\wr S_k$ is the lift used in Cor. 3.1. This is written nowhere.
4. The **setwise-transporter repair** of §1.2, which carries over to the base case.

None of these looks like a hidden obstruction. **Verdict on claim 7: plausible SKETCH, correctly
labelled.** The Consequence paragraph (L376–380) is fine as conditional on E′.

---

## 8. Overall verdict

**No break.** Every [PROVEN] claim survives:
* Theorem P needs a one-line repair of its primitive operations.
* Cor. 2.2 needs rewording.
* The Example X conclusion needs its level-2 caveat.

The main correction is attribution. Theorem P is BCQ12/Codenotti's twisted-code-equivalence DP plus
one coset intersection, and the campaign's own STR §4.5 had already sketched it.

**Statements I would sign.**
1. *(Corollary of BCQ12 Thm 5 / Codenotti Thm 4.2.1 and Babai.)* For any $G\le\mathrm{Sym}(\Delta)\wr S_k$
   given on $V=[k]\times\Delta$, $\lvert\Delta\rvert=b$, and strings on $\Delta^k$ ($N=b^k$),
   $\mathrm{Iso}_G(x,y)$ is computable in
   $$(1+b^2)^k\,k\,b!\,b\cdot\mathrm{CI}(bk)\ \le\ (b!)^{1+o(1)}N^{\log_b(1+b^2)+o(1)}\ \le\ (b!)^{1+o(1)}N^{2.33}.$$
   With Babai 1983 alone it is $2^{O(b\log^4b)}N^{O(1)}$.
2. Theorem 2.1, as stated, for the abstract problems. Cor. 2.2 holds in the form: "a laminar
   diagonal on a full-depth direct factor ($\mathcal T_1\otimes\mathcal T_2$) is complete; DP
   combine steps with a full-diagonal kernel reduce to SI on one child".
3. Lemma 2.4, exactly as stated.
4. Prop. 6.1, exactly as stated, for vertex-coloured graphs.
5. Example X: for $r\ge3$, $\langle R,S\rangle$ contains $\mathrm{GL}(r,2)$ at every node of every
   level $\ge3$; $\varepsilon\le\lvert\mathrm{GL}(r,2)\rvert^{2^{r-1}}$; FPT by Theorem E.
6. Theorem E′ only as a SKETCH, with the four gaps of §7.

**Novelty.**
* *Theorem P:* low. The algorithm is published (BCQ12 / Codenotti 2011). Arbitrary subgroups are a
  one-CI extension, and FPT in $b$ is a re-accounting of the CI cost. The explicit parameterized
  statement may be unpublished; I could not run a web search to check.
* *Theorem 2.1 and Lemma 2.4:* new as packaging, elementary in content.
* *Prop. 6.1:* elementary.
* *Theorem E′:* the most interesting new claim, still a sketch.
