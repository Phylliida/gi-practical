# w2-coset: the core problem, coset intersection for coupled tree groups

Branch `w2-coset`, 2026-11-05. Wave 2 of the overnight campaign (`overnight-log.md`). Input:
`w1-fpt.md` (FPT below), `w1-structure.md` (STR below), `verify-theorem-R.md`, `redteam-theorem-R.md`.
FPT and STR are being red-teamed in parallel. I use their results only where I re-derived them,
and I say so.

**Task.** Both wave-1 theory agents reduced the branching question to one core problem: string
isomorphism, or coset intersection, for tree groups whose kernels are coupled across blocks.
1. Pin the core down and prove equivalences.
2. Look for algorithms: aligned DP, canonical forms, simply exponential machinery, Goursat
   decomposition of the coupling.
3. Look for hardness.
4. Decide what survives for bounded-degree graphs.

**Labels.**
* **[PROVEN]**: complete argument here, using only cited published results and the standard
  polynomial-time permutation-group toolkit (Schreier–Sims, pointwise and setwise stabilisers of
  points, restriction homomorphisms and preimages, intersection with a normal subgroup).
* **[PROVEN mod X]**: complete, except that the published result X is used as a black box.
* **[SKETCH]**: argument given, gaps named.
* **[CONDITIONAL: H]**: holds under hypothesis H.
* **[SPECULATION]**: opinion or conjecture.

**Computation.** One brute-force script (`scratchpad/w2coset/thmP_check.py`, about 90 lines) checks
the recurrence of Theorem P on tiny instances against exhaustive search (§3.2). Nothing else was run.

**Sources.** Read for this memo: GNS (arXiv:1802.04659) §5 on almost $d$-ary sequences; Neuen
(arXiv:2002.06997) §7 on $t$-CR-bounded graphs; the Neuen 2026 survey §4; Babai (arXiv:1512.03547)
abstract and introduction, which give CI in quasipolynomial time. Web searches (2026-11-05) covered:
product actions and coset intersection with FPT; coset intersection for iterated wreath products
or tree groups; coset CSPs and Mal'tsev polymorphisms. They turned up Miyazaki's note that CI is not
known to reduce to GI, Feder's ECCC TR05-005, Bulatov's ECCC TR02-034, Lasota arXiv:1412.4020, and
Lichter–Pago arXiv:2407.09097. None addresses the problems below. Sources are listed in §8.

---

## 0. Summary

| # | question | answer | label |
|---|---|---|---|
| 1 | Precise core | $P_{\rm core}(b)$ = **TreeCI$(b)$**: coset intersection for subgroups of $\mathrm{Aut}(\mathcal T)$, where $\mathcal T$ is a rooted tree with node degree $\le b$, with parameter $b$. Under fpt-reductions it is equivalent to TreeSI$(b)$; to tree-group PCI (the combine step); to $T^{\,2}$ (string isomorphism under $G_1\times G_2$ on $\Lambda_1\times\Lambda_2$, "matrices with tree-structured rows and columns"); and to SI for GNS's class of $\hat\Gamma_d$-groups with an almost $d$-ary sequence of invariant partitions ($b=d!/2$). | **[PROVEN]** (§2.1–2.3) |
| 2 | Does the *coupling pattern* matter? | **No.** PCI whose kernel is the **full diagonal of two children** (the simplest, laminar coupling) is already TreeCI-complete. All the difficulty is carried by the child cosets, i.e. by the **depth of the coupled section**. Bounded coupling depth $s$ gives FPT in $(b,s)$ (from Theorem E). At a primitive node, every coupling of non-abelian simple sections is all-or-nothing. Goursat pieces are bounded in $d$ exactly in the Theorem E regime. | **[PROVEN]** (§2.2, §4.1) |
| 3 | Is the core all of $\hat\Gamma_d$? | Not known. GNS-style unfolding of product-type components costs $\approx\lvert K\rvert$ (top group), up to $N^{\Theta(\log d)}$. I found no cheaper tree unfolding and no proof that none exists. (A draft claim of a representation-theoretic obstruction was false and is retracted, §2.4.) But that channel is FPT by a different route (row 4). | observation (§2.4) |
| 4 | New algorithm: product actions | **Theorem P.** SI for *any* $G\le\mathrm{Sym}(\Delta)\wr S_k$ in product action on $\Delta^k$ ($\lvert\Delta\rvert=b$, $N=b^k$) runs in $b!\cdot N^{3.2}\cdot\mathrm{CI}(bk)$. That is $b!\,N^{3.2+o(1)}$ with Babai's quasipolynomial CI, or $2^{O(b\log^cb)}N^{O(1)}$ with Babai 1983. The top group is arbitrary and is never enumerated. This covers every O'Nan–Scott coordinate type (product, affine imprimitive, diagonal, twisted wreath). | **[PROVEN mod Babai's CI bound]**; brute-force checked (§3) |
| 5 | Consequence for $\hat\Gamma_d$ | **Theorem E′.** SI over $\hat\Gamma_d$ is FPT for groups whose block kernels all have entanglement index $\le f(d)$, *with no bound on the primitive components*. So the whole enumeration channel (FPT row 2, STR rows 1–4) is FPT inside the block DP. Only entanglement remains. | **[SKETCH]**: STR Prop. 2.2 (a sketch) + integration (§3.4) |
| 6 | Where the $\hat\Gamma_d$ question now lives | SI$(\hat\Gamma_d)$ FPT $\Rightarrow$ TreeCI FPT (trivial). Exactly: SI$(\hat\Gamma_d)\equiv$ CI for *coordinate trees* (block trees whose nodes are of bounded degree, of small order, or of product type). TreeCI is the pure-tree sub-case. Residual gap: entangled kernels under, or inside, product-type nodes. | **[PROVEN]** / **[SKETCH]** (§3.5) |
| 7 | Algorithms for TreeCI itself | No FPT algorithm. Every method of the brief fails on $T^{\,2}$, each for a named reason (§4.6). Corrected Example X′ (Cayley-coupled node): the combine step is a **coset CSP on a Cayley graph**, FPT when the shared groups are small, TreeCI-hard when they are deep. STR's Example X, as written, **collapses**: equivariance under local translations forces $\mathrm{GL}$ at every single node, so it is the uncoupled tower with $\varepsilon=1$ (§4.2). | **[PROVEN]** / analysis |
| 8 | Hardness | No reduction from a problem believed not FPT. W[1]-hardness would need parameter blow-up $2^{k^{\Omega(1)}}$ (under ETH), and none of the natural XP sources (code equivalence by dimension or hull, group isomorphism by number of generators, SSI) encodes into tree groups (§5). | negative |
| 9 | Graphs | GI of vertex-coloured Cartesian products $T\,\square\,T$ of two $b$-ary trees (max degree $2b+2$) is equivalent to SI under $W\times W$, the **full-group** form of $T^{\,2}$, and reduces to $P_{\rm core}$. The converse would realise arbitrary tree groups at bounded degree. It is open, and would imply CI$\le$GI for tree groups, which is not known even without parameters (Miyazaki). Graph-derived instances only ever intersect automorphism groups of local structures. So **degree-$d$ GI may be strictly easier than TreeCI**. The precise form is in §6. | **[PROVEN]** / **[SPECULATION]** (§6) |

**Verdict.**
* *Enumeration channel.* The campaign's second $\log d$ channel, enumeration of large primitive
  quotients, is not an obstruction to FPT. Theorem P solves every product-type primitive group in
  $b!\,N^{O(1)}$ by DP over partial coordinate assignments, using cheap coset intersection on a
  domain of size $O(b\log N)$. Inside the block DP the same holds for any $\hat\Gamma_d$-group with
  boundedly entangled kernels.
* *What remains.* Everything left is **coset intersection for tree groups**, already in its
  simplest coupling form: rows and columns, $G_1\times G_2$ on $\Lambda_1\times\Lambda_2$.
* *Goursat idea.* The hoped-for decomposition fails for a precise reason. The coupled pieces are
  quotients $R_c/N_c$ of deep tree groups, not groups of size $f(d)$.
* *Status.* I found neither an algorithm nor a hardness reduction for TreeCI. Both look like they
  need a genuinely new idea: an FPT coset intersection for tree groups, or a lower bound for the
  coset-splitting model.

---
## 1. Definitions

**Trees and tree groups.** $\mathcal T$ is a rooted tree, all leaves at depth $H$, every node with
at most $b$ children. $\Lambda$ is the leaf set and $N=\lvert\Lambda\rvert$. $W(\mathcal T)=\mathrm{Aut}(\mathcal T)$
is the iterated wreath product. A **tree group** is a subgroup $G\le W(\mathcal T)$, given by
generators and acting faithfully on $\Lambda$. Equivalently, it is a group $G\le\mathrm{Sym}(\Lambda)$
with a $G$-invariant **$b$-ary sequence of partitions** in the sense of GNS (Def. in GNS §5): the
partitions of $\Lambda$ by depth-$i$ ancestors. Tree groups of node degree $b$ lie in $\hat\Gamma_b$.

**Block data** at a node $B$ with children $C_1,\dots,C_r$ ($r\le b$), as in FPT §4.1:
* $H_B=G_B|_B$;
* $P_B\le S_r$, the action on the children;
* $K_B\trianglelefteq H_B$, the kernel of that action;
* $\pi_i$, restriction to $C_i$;
* $R_i=\pi_i(K_B)$.

The **Goursat data** of $K_B$ are:
* the inner parts $N_i=\{k\in K_B:\pi_j(k)=1\ \forall j\ne i\}$, viewed in $R_i$, with $N_i\trianglelefteq R_i$;
* the **coupled sections** $Q_i=R_i/N_i$;
* the **coupling** $D_B=K_B/\prod_iN_i$, a subdirect product of $\prod_iQ_i$ in which no coordinate
  has a nontrivial kernel.

The entanglement index of FPT is
$$\varepsilon_B=\lvert\textstyle\prod R_i:K_B\rvert=\prod_i\lvert Q_i\rvert/\lvert D_B\rvert.$$
For $r=2$ this is exactly Goursat's lemma: $K_B$ is the fibre product of $R_1$ and $R_2$ over the
isomorphism $Q_1\cong Q_2$ that $D_B$ induces.

**Coupling depth.** $\delta_B$ is the least $s$ such that, for every $i$, $N_i$ contains the kernel
of $R_i$ acting on the top $s$ levels of $\mathcal T_{C_i}$. Then the coupled section $Q_i$ is a
quotient of a subgroup of $W_s$, the $s$-level wreath product.

**Problems** (parameter $b$ throughout; outputs are cosets given by generators plus one
representative, or $\varnothing$):

| name | input | output |
|---|---|---|
| TreeSI$(b)$ | $G\le W(\mathcal T)$; $x,y:\Lambda\to\Sigma$ | $\mathrm{Iso}_G(x,y)$ |
| TreeCI$(b)$ | $G_1,G_2\le W(\mathcal T)$; $a,c\in W(\mathcal T)$ | $G_1a\cap G_2c$ |
| PCI$(b)$ | node $B$; $K\le\prod_iR_i$ with $R_i\le W(\mathcal T_{C_i})$; cosets $A_iz_i\subseteq W(\mathcal T_{C_i})$ | $K\cap\prod_iA_iz_i$ |
| $T^{\,2}(b)$ | $G_j\le W(\mathcal T_j)$ ($j=1,2$); $x,y:\Lambda_1\times\Lambda_2\to\Sigma$ | $\mathrm{Iso}_{G_1\times G_2}(x,y)$ |
| $P_{\rm graph}(b)$ | $\mathcal T$; colourings $x,y$ of pairs of equal-depth nodes | $\mathrm{Iso}_{W(\mathcal T)}(x,y)$, with $W$ acting diagonally |
| PA-SI$(b)$ | $G\le\mathrm{Sym}(\Delta)\wr S_k$ with $\lvert\Delta\rvert=b$, in product action on $\Delta^k$; strings on $\Delta^k$ | $\mathrm{Iso}_G(x,y)$ |

**The brief's $P_{\rm core}(b,h,L,\text{coupling})$** is the family of TreeSI instances under
$G^L$ in product action on $\mathrm{Leaves}^L$, with $G$ a depth-$h$ tree group (FPT's
$T^{\,L}_{b,h}$), or with prescribed Goursat data. §2 shows that $L$ and the coupling pattern can be
removed from the definition: already $L=2$ with the simplest pattern is complete. So I take
$$P_{\rm core}(b):=\text{TreeCI}(b).$$

---

## 2. The core and its equivalences

### 2.1 Theorem 2.1 (equivalences) **[PROVEN]**

Under fpt-reductions (Turing reductions for (a); many-one for the others):
$$\text{TreeSI}(b)\ \equiv\ \text{TreeCI}(b)\ \equiv\ \text{PCI}(b)\ \equiv\ \text{PCI}_{\rm diag}(b)\ \equiv\ T^{\,2}(b).$$
Here $\text{PCI}_{\rm diag}$ is PCI restricted to two children and kernel the **full diagonal**
$K=\{(w,w^\varphi):w\in W(\mathcal T_{C_1})\}$, where $\varphi$ is a fixed isomorphism
$\mathcal T_{C_1}\to\mathcal T_{C_2}$. In sizes:
1. $\mathrm{TreeSI}(b,N)\le4N^2b!\cdot\mathrm{TreeCI}(b,N)+\mathrm{poly}(N)$;
2. $\mathrm{TreeCI}(b,N)\le T^{\,2}(b,N^2)\le\mathrm{TreeSI}(b,N^2)$;
3. $\mathrm{TreeCI}(b,N)\le\mathrm{PCI}_{\rm diag}(b,2N)$.

*Proof.*

(a) **TreeSI $\le$ TreeCI.** This is FPT Prop. 4.1, re-derived.
* Tabulate $\mathrm{Iso}(B,B')=\{g|_B:g\in G,\ B^g=B',\ x=y\circ g\text{ on }B\}$ over pairs of
  same-depth nodes. There are at most $(2N)^2$ pairs.
* Grouping by the bijection of children that $g$ induces gives
  $\mathrm{Iso}(B,B')=\bigcup_\sigma(K_Bh_\sigma\cap\Pi_\sigma)$, with at most $\lvert P_B\rvert\le b!$
  terms and $\Pi_\sigma=\prod_i\mathrm{Iso}(C_i,C'_{\sigma i})$.
* After right translation by $h_\sigma^{-1}$, each term is a coset intersection of two tree groups on
  $\mathcal T_B$: $K_B$, and $\prod_i\mathrm{Aut}(C_i)$. The latter fixes every child and is a tree
  group.
* The union of the terms is an isomorphism set, hence a coset. Its generators are the generators
  of the terms together with quotients of their representatives.
* $H_B$, $K_B$ and $P_B$ are polynomial-time computable.

(b) **TreeCI $\le T^{\,2}$.** Let $\mathcal T\otimes\mathcal T$ be the interleaved product tree.
* Its nodes are pairs $(u,v)$ with $\mathrm{depth}(u)-\mathrm{depth}(v)\in\{0,1\}$. The children
  of $(u,v)$ are $(u_i,v)$ when the depths are equal, and $(u,v_j)$ otherwise.
* It has node degree $\le b$ and leaves $\Lambda\times\Lambda$, and $G_1\times G_2$ preserves it.
* Let $\delta(\omega,\omega')=[\omega=\omega']$. Since the action on $\Lambda$ is faithful,
  $(g_1a,g_2c)$ maps $\delta$ to $\delta$ iff $g_1a=g_2c$.
* So $G_1a\cap G_2c$ is the projection of $\mathrm{Iso}_{(G_1\times G_2)(a,c)}(\delta,\delta)$, and
  $\mathrm{Iso}_{H\tau}(x,y)=\mathrm{Iso}_H(x,y^{\tau^{-1}})\tau$ turns this into a group instance.
* $T^{\,2}\le$ TreeSI holds because $G_1\times G_2\le W(\mathcal T\otimes\mathcal T)$.

(c) **TreeCI $\le\mathrm{PCI}_{\rm diag}$.** Hang two copies of $\mathcal T$ under a new root and put:
* $K=\{(w,w):w\in W(\mathcal T)\}$;
* $A_1z_1=G_1a$ and $A_2z_2=G_2c$.

Then $K\cap(A_1z_1\times A_2z_2)=\{(g,g):g\in G_1a\cap G_2c\}$.

(d) **PCI $\le$ TreeCI.** A PCI instance is the coset intersection of the tree groups $K$ and
$\prod_iA_i$ on $\mathcal T_B$, after translation. ∎

### 2.2 Corollary 2.2: the coupling pattern is not where the difficulty lies **[PROVEN]**

By (c), PCI whose kernel is a **full diagonal of two children** is already as hard as all of
TreeCI. This is the simplest possible coupling: laminar, all-or-nothing, with one shared section.

The hard information sits elsewhere:
* *In PCI form*, it is in the child cosets $A_iz_i$, i.e. the memoised automorphism cosets of the
  children. These are arbitrary tree groups.
* *In Goursat terms*, it is in the coupled section $Q_i=R_i$ (the full child group) and its depth
  $\delta_B=$ the full child depth.

The coupling patterns studied in wave 1 (Cayley graphs, non-laminar classes) can only make
individual instances harder. They cannot raise the complexity of the class.

**Corollary 2.3 (bounded coupling depth).** **[PROVEN, from FPT Theorem E]**
* If every node has coupling depth $\delta_B\le s$, then
  $\varepsilon_B\le\prod_i\lvert Q_i\rvert\le\lvert W_s\rvert^b\le(b!)^{b^{s+1}}$, so TreeSI runs in
  $b!\,(b!)^{b^{s+1}}\mathrm{poly}(N)$. This is FPT in $(b,s)$.
* $T^{\,2}$ and $\mathrm{PCI}_{\rm diag}$ have $\delta_B=$ (full depth).
* The open window is unbounded coupling depth.

### 2.3 Lemma 2.4: GNS's almost $d$-ary class is tree groups **[PROVEN]**

*Notation.* For $d\ge5$ let $s(d)=d!/2$. This bounds the order of every simple group embeddable in
$S_d$, including $C_p$ for $p\le d$.

**Lemma 2.4.** Let $G\in\hat\Gamma_d$ carry a $G$-invariant almost $d$-ary sequence
$\{\Omega\}=\mathfrak B_0\succ\cdots\succ\mathfrak B_m$ (GNS §5): at each step the induced action
on the children of a block has at most $d$ children, or is semiregular. Then the sequence can be
refined, in polynomial time and **without changing $\Omega$**, to a $G$-invariant $s(d)$-ary
sequence. Hence SI for that class $\le$ TreeSI$(s(d))$ by the identity map on instances.

*Proof.* Fix a step and a block $B\in\mathfrak B_{i-1}$ whose induced group
$P=G_B^{\mathfrak B_i[B]}$ is semiregular. Work at one representative $B$ of each $G$-orbit on
$\mathfrak B_{i-1}$, and transport each inserted partition to $B^g$ by $g$. This is well defined
because $G_B$ preserves everything inserted.
1. *Orbits.* Insert the partition of $B$ into unions of $P$-orbits on its children. $G_B$ fixes each
   part, so this node has trivial action; binarise it by any fixed binary tree (degree 2, trivial
   action).
2. *Regular orbits.* On one $P$-orbit $O$ the action is regular, so $P^O\cong P$ is a section of
   $G$, and its composition factors embed in $S_d$. Choose a composition series
   $1=H_0\triangleleft\cdots\triangleleft H_s=P^O$ and a point $o\in O$, and insert the partitions
   $\mathcal Q_j=\{o^{H_jx}:x\in P^O\}$ (right cosets).
   * $o^{H_jx}g=o^{H_jxg}$, so each $\mathcal Q_j$ is $G_B$-invariant.
   * The partitions are nested, and a block of $\mathcal Q_j$ has $\lvert H_j:H_{j-1}\rvert\le s(d)$
     sub-blocks.
   * The stabiliser of a block acts on its sub-blocks through the simple group $H_j/H_{j-1}$,
     regularly.

Steps with at most $d$ children are left unchanged. Composition series are polynomial-time (Luks). ∎

*Use.* GNS reduce SI$(\hat\Gamma_d)$ to this class at domain cost $n^{O(\log d)}$, which is not an
fpt reduction. Lemma 2.4 shows that the *target* of their reduction is exactly TreeSI$(f(d))$. So
the GNS route makes the whole $\hat\Gamma_d$ question "TreeCI plus an $n^{O(\log d)}$ unfolding"; §3
removes the unfolding by a different route.

### 2.4 Is the core all of $\hat\Gamma_d$? (observation)

A primitive component of large degree and large order is, by STR Prop. 2.2 **[SKETCH there]**, of
coordinate type: it embeds in $\mathrm{Sym}(\Delta)\wr K$ in product action, with $\lvert\Delta\rvert\le f(d)$.
* *GNS's unfolding.* It turns such a component into a tree by making the top part semiregular
  ($\Omega^*=G/\mathrm{Soc}\times\Omega$) and reading the socle $T^k$ along a prefix tree. That
  costs about $\lvert K\rvert$, which is up to $d^{k}=N^{\Theta(\log d/\log\lvert\Delta\rvert)}$ when
  the base is small and $K$ is a deep tree group on the $k=\log_{\lvert\Delta\rvert}N$ coordinates.
* *Small top groups* unfold cheaply. Example: $A_5\wr C_{2^s}$, through the chain
  $A_5^m{:}C_m\supset A_5^m{:}C_{m/2}\supset\cdots\supset A_5^m\supset A_4\times A_5^{m-1}\supset\cdots\supset A_4^m$,
  all of whose indices are $\le5$, at domain cost $m$.
* *Large top groups.* I found no cheaper tree unfolding, and **no proof that none exists**.
  (An earlier claim in my notes, "no faithful tree representation of degree $<m$", is false:
  $A_5\wr C_m$ is a tree group of degree 5 in its imprimitive action. The right question is about
  unfoldings $\Omega^*\to\Omega$ that preserve strings, and it is open.)

Theorem P (§3) sidesteps the question: product-type components are FPT directly, by memoisation,
without being turned into trees.

---
## 3. A new FPT ingredient: product actions with arbitrary top group

### 3.1 Statement

Let $\Delta$ be a set with $\lvert\Delta\rvert=b\ge2$, let $k\ge1$, and let
$V=[k]\times\Delta$ (so $\lvert V\rvert=bk$). A group $G\le\mathrm{Sym}(\Delta)\wr S_k$ acts:
* on $V$ imprimitively, preserving the partition into the "coordinates" $\{j\}\times\Delta$;
* on $\Omega=\Delta^k$ in product action: a point $z$ is the transversal
  $\{(j,z_j):j\in[k]\}\subseteq V$.

$N=b^k$, and $k\le\log_2N$. Write $\mathrm{CI}(n)$ for the cost of coset intersection on $n$ points.

**Theorem P.** **[PROVEN mod the CI bound used]** Given $G$ by generators on $V$ (if only the
action on $\Omega$ is given, the product structure must first be computed, which is standard for
primitive groups via the socle **[TRUST]**), and strings
$x,y:\Omega\to\Sigma$, $\mathrm{Iso}_G(x,y)$ can be computed in time
$$(b+1)^{2k}\cdot k\,b!\,(b+1)\cdot\bigl(\mathrm{CI}(bk)+\mathrm{poly}(bk)\bigr)\ \le\ b!\cdot N^{2\log(b+1)/\log b}\cdot\mathrm{CI}(b\log_2N)\cdot\mathrm{poly}.$$
* With Babai's quasipolynomial CI (arXiv:1512.03547, the corollary in §1:
  $\mathrm{CI}(n)=\exp((\log n)^{O(1)})$) this is $b!\cdot N^{3.17+o(1)}$, because
  $\exp((\log(b\log N))^{c})\le\exp(2^c(\log b)^c)\cdot N^{o(1)}$.
* With only Babai 1983 ($\mathrm{CI}(n)=\exp(\tilde O(\sqrt n))$) it is
  $2^{O(b\log^cb)}N^{O(1)}$. Split on whether $b\ge\log N/\log^4\log N$:
  $\sqrt{b\log N}\log^2(b\log N)\le O(\log N)+O(b\log^{c}b)$.

Either way **PA-SI is FPT in $b$, for every top group $K\le S_k$**. The exponent $2\log(b+1)/\log b$
is $3.17$ at $b=2$ and tends to 2.

### 3.2 Proof

For $J\subseteq[k]$ and a partial assignment $u\in\Delta^J$ (a set of $\lvert J\rvert$ points of
$V$, one in each coordinate of $J$), define the link $x_{J,u}(z)=x(u\cup z)$ for
$z\in\Delta^{[k]\setminus J}$. Define $I(J,u;J',u')$ as the set of $g\in G$ with:
* $u^g=u'$ as a point set in $V$;
* $y(u'\cup z^g)=x(u\cup z)$ for all $z\in\Delta^{[k]\setminus J}$.

Since $G$ preserves coordinates and maps $u$ to $u'$, it maps $J$ to $J'$ and
$\Delta^{[k]\setminus J}$ to $\Delta^{[k]\setminus J'}$. $I$ is an isomorphism set, so it is empty
or a right coset of $I(J,u;J,u)\le G$. The answer is $I(\varnothing,\varnothing;\varnothing,\varnothing)$.

*Base* ($J=[k]$). $I=\{g:u^g=u'\}$ if $x(u)=y(u')$, and $\varnothing$ otherwise. This is a point
transporter, computed by Schreier–Sims on $V$.

*Recurrence.* Let $j=\min([k]\setminus J)$. Every $g$ sends coordinate $j$ to some
$j'\in[k]\setminus J'$ and acts on it by a bijection $\pi:\Delta\to\Delta$, so $(j,a)^g=(j',\pi a)$.
Let $C_{j',\pi}$ be the transporter of the point sequence
$\bigl(u,\ (j,a)_{a\in\Delta}\bigr)\mapsto\bigl(u',\ (j',\pi a)_{a\in\Delta}\bigr)$ in $G$ on $V$.
Every $z$ has exactly one value $a=z_j$, so
$$I(J,u;J',u')=\bigcup_{j'\notin J',\ \pi}\ \Bigl(C_{j',\pi}\ \cap\ \bigcap_{a\in\Delta}I\bigl(J{+}j,\ u{+}(j,a);\ J'{+}j',\ u'{+}(j',\pi a)\bigr)\Bigr).$$
* Within a branch $(j',\pi)$ the targets are fixed, so each branch is an intersection of $b+1$
  cosets of subgroups of $G\le\mathrm{Sym}(V)$: $b$ calls to CI on $bk$ points.
* There are at most $k\cdot b!$ branches.
* The union is an isomorphism set, hence a coset. Its generators are those of the branch groups
  together with $r_\beta r_{\beta_0}^{-1}$ over the branch representatives $r_\beta$.

*Table size.* There are $\sum_s\binom ks^2b^{2s}\le(1+b)^{2k}$ entries. ∎

**Remarks.**
1. *Why it works.* The DP branches on the image of a whole coordinate $\{j\}\times\Delta$ at once.
   After that, all $b$ child conditions have determined targets, so the universal quantifier over
   $a$ becomes a coset intersection rather than an intersection of unions. For general
   down-closed hypergraphs, branching on single points does not have this property.
2. *Domain.* All coset intersections take place on $V$, which has $O(b\log N)$ points, and never
   on $\Omega$. This is FPT §3.2's insight ("intersect on the small faithful domain"). The new
   points are:
   * enumeration of the top group $K$ is replaced by DP over unordered coordinate sets $J$;
   * ADKT's bounded-orbit CI ($2^{O(\text{orbit})}$, which is $2^{O(bk)}$ here because $K$ merges
     the coordinates) is replaced by Babai's general CI on the small domain.
3. *Prior art.* FPT Prop. 3.3 enumerates $K$, giving $\lvert K\rvert$, which is up to
   $N^{\Theta(\log d)}$. BCQ / Codenotti Thm 4.2.1 (twisted code equivalence) handle $Q\wr S_k$,
   the full symmetric top. Luks 1999 and the small-faithful-degree remark (FPT §3.2) give
   $2^{O(bk)}=N^{O(b/\log b)}$, which is XP. I found no statement of FPT in $b$ for arbitrary
   subgroups of $\mathrm{Sym}(\Delta)\wr S_k$ (searches in §8). **The DP is an easy combination of
   known pieces, and experts may regard it as folklore.**

*Computation check.* `scratchpad/w2coset/thmP_check.py` takes $k=b=3$, random subgroups
$G\le S_3\wr S_3$ (orders 2 to 648, enumerated explicitly), and random or symmetric strings with
$y=x^{g_0}$ in 60% of cases. It computes $I(\varnothing,\varnothing;\varnothing,\varnothing)$ by the
recurrence, with set intersections in place of CI, and compares the result with exhaustive search.
All 14 instances agree, including non-trivial isomorphism cosets (e.g. $\lvert G\rvert=324$,
$\lvert\mathrm{Iso}\rvert=6$). Run time is a few seconds.

### 3.3 Corollary 3.1: primitive $\hat\Gamma_d$-groups **[SKETCH]**

SI for primitive $G\in\hat\Gamma_d$ of degree $d'$ is FPT in $d$. The argument relies on STR
Prop. 2.2 **[SKETCH]** together with polynomial-time computation of the O'Nan–Scott structure
**[TRUST]**. By STR Prop. 2.2, either $\lvert G\rvert\le f(d)\,d'^{\,C}$ (enumerate), or $G$ is of
coordinate type with components of size $\le f(d)$. Each coordinate type embeds in a product action
with base of size $\le f(d)$:
* *product type:* $G\le Q\wr K$ on $\Delta^k$, directly;
* *affine imprimitive linear:* $V=W^\ell$ and $V{\rtimes}H\le\mathrm{AGL}(W)\wr K$ on $W^\ell$;
* *diagonal type* $T^k.(\mathrm{Out}\,T\times K)$ on $\Omega=D\backslash T^k$: pull strings back
  along the equivariant surjection $T^k\to\Omega$ ($D$ is normalised by $G$, and there is an
  $\lvert T\rvert$-fold blow-up). On $T^k$, $G$ acts by coordinatewise bijections of $T$ (right
  translations, diagonal automorphisms) and coordinate permutations, so
  $G\le\mathrm{Sym}(T)\wr S_k$, with $b=\lvert T\rvert\le d!$;
* *twisted wreath:* $\Omega=T^k$ is regular for the socle. The point stabiliser acts by
  automorphisms permuting the coordinates, so again $G\le\mathrm{Sym}(T)\wr S_k$.

Then apply Theorem P. *Gaps:* STR Prop. 2.2 is a sketch, and the claim that its "$d'>2^{C_1d\log d}$"
case analysis covers every large-order case is inherited from it.

### 3.4 Theorem E′: inside the block DP, only entanglement matters **[SKETCH]**

**Claim.** Let $G\in\hat\Gamma_d$ and take a maximal chain of block systems, as in FPT Prop. 4.1.
Suppose every node $B$ has entanglement $\varepsilon_B\le\varepsilon$. Then SI under $G$ runs in
$\varepsilon\cdot f(d)\cdot\mathrm{poly}(N)$. **There is no bound on the order or degree of the
primitive components.**

This extends FPT Theorem E, which needed $\lvert P_B\rvert\le\pi_0$.

*Sketch.* Run the block-pair DP. Nodes whose $P_B$ has order $\le f(d)\,d'^{\,C}$ are handled as in
Theorem E. A node of coordinate type has its children indexed by $\Delta^k$; there:

1. *$\varepsilon_B=1$.* By Krasner–Kaloujnine, $K_B=\prod_uK_u$.
   * Run Theorem P's DP for the group $\bar G=P_B$ on $V$.
   * At a full point $u\mapsto u'$, replace the test "$x(u)=y(u')$" by
     $\{\bar g:u^{\bar g}=u',\ \hat g|_{C_u}\in\mathrm{Iso}(C_u,C'_{u'})\cdot K_u|_{C_u}\}$. This is
     the preimage, under $\bar g\mapsto\hat g|_{C_u}K_u$, of a coset of $\mathrm{Aut}(C_u)K_u$, so it
     is a coset of $\bar G$ and computable by restriction and preimage.
   * All coset intersections stay on $V$.
   * Lift: for each generator of the resulting coset of $\bar G$, choose in each child an element
     of the (nonempty) $\mathrm{Iso}(C_u,C'_{u^{\bar g}})\cap\hat gK_u$, and add generators of
     $\prod_u(\mathrm{Aut}(C_u)\cap K_u)$.
2. *$\varepsilon_B\le\varepsilon$.* Put $\tilde G_B=G_B\prod_uR_u$. This has the same child
   groups, $\varepsilon=1$, and index $\lvert\tilde G_B:G_B\rvert=\varepsilon_B$.
   * Compute $\mathrm{Iso}_{\tilde G_B}$ by step 1.
   * Intersect with $G_B$ using $\varepsilon_B$ coset representatives and membership tests
     (Schreier's lemma, ADKT Thm 1).

*Gaps.*
* Step 1's preimage and lift need the action of $G_B$ on $V\cup B$ simultaneously. That is fine
  for Schreier–Sims, but I did not write out the bookkeeping.
* The coordinate structure of $P_B$ must be computed **[TRUST]**.
* STR Prop. 2.2 is a sketch. ∎

**Consequence.** The enumeration channel of R\* (FPT §3.1; STR rows (E1), (E2), (PR)) is FPT in the
memoising framework. This includes the families on which HJ+(M′) provably pays $N^{\log_2D-0.45}$
(FPT Prop. 3.1) and $N^{\log_2(d+1)+1-o(1)}$ (STR Prop. 4.2, $\mathrm{AGL}^L$ in product action);
FPT Prop. 3.3 and STR Theorem L were family-specific. *Not* covered: STR's $G_{r,L}$ has
$\varepsilon$ unbounded; Theorem L still handles it.

### 3.5 Where the $\hat\Gamma_d$ question now lives

**Proposition 3.2.**
1. SI$(\hat\Gamma_d)$ FPT $\Rightarrow$ TreeCI$(d)$ FPT. **[PROVEN]** Tree groups of degree $d$
   lie in $\hat\Gamma_d$, and CI reduces to SI on $n^2$ points (Theorem 2.1(b)).
2. PCI FPT *for $\hat\Gamma_d$-groups* $\Rightarrow$ SI FPT for every $\hat\Gamma_d$-group whose
   coordinate-type nodes have $\varepsilon_B\le f(d)$. **[SKETCH]**
   * Run the block DP.
   * Nodes whose primitive component has degree $\le f(d)$, or small order relative to degree,
     are enumerated and use PCI.
   * Coordinate-type nodes use §3.4.

   *Caveat (a correction to my first draft).* The PCI groups at a tree node, namely $K_B$ and
   $\prod\mathrm{Aut}(C_i)$, live on $\mathcal T_B$. They may contain coordinate-type nodes further
   down, so they are **not tree groups** in general.
3. So the exact core for $\hat\Gamma_d$ is **CI for "coordinate trees"**: groups with a block tree
   all of whose nodes are of degree $\le f(d)$, of order $\le f(d)\,d'^{\,C}$, or of product type
   with base $\le f(d)$. TreeCI is the sub-case without product-type nodes, and is complete for
   GNS's almost $d$-ary class (Lemma 2.4). SI$(\hat\Gamma_d)\equiv_{\rm fpt}$CI(coordinate trees)
   modulo STR Prop. 2.2 (Luks's SI $\equiv$ CI preserves the class).

**The residual gap** is a coordinate-type quotient (large primitive component) sitting over an
*entangled* kernel. The DP then needs a PCI "twisted" by Theorem P's coordinate DP. I did not find
an instance where this is harder than TreeCI, nor a reduction to TreeCI. **[open]**

---
## 4. Algorithms for TreeCI itself

### 4.1 Goursat structure at a primitive node **[PROVEN mod Scott's lemma]**

**Lemma 4.1.** Let $P_B$ be primitive on the children, and suppose every $R_i\cong T$ for one
non-abelian simple $T$. Then $K_B=\prod_iR_i$, or $K_B$ is a full (twisted) diagonal
$\{(t^{\alpha_1},\dots,t^{\alpha_r})\}$.

*Proof.*
* A subdirect product of non-abelian simple groups is a product of diagonals over a partition of
  the coordinates (Scott's lemma).
* $G_B$ normalises $K_B$ and permutes the $R_i$ as $P_B$ does, so it preserves that partition.
* A primitive $P_B$ preserves only the two trivial partitions. ∎

So a *non-laminar* coupling needs several simple factors per child, labelled by a $P_B$-set
(Example X′ below), or non-simple sections. Together with Cor. 2.2 this answers the brief's Goursat
question:
* The fibred-product decomposition always exists, but its pieces $Q_i=R_i/N_i$ are quotients of
  deep tree groups.
* They are bounded in $d$ exactly when the coupling depth is bounded, which is Theorem E's regime
  (Cor. 2.3).
* **An FPT algorithm "by decomposing the coupling into pieces of size $f(d)$" therefore exists only
  where FPT was already known.**

### 4.2 Example X: as defined in STR §4.8 it is not entangled **[PROVEN]**

STR's Example X:
* $C_j=X=\mathbb F_2^r$;
* local translations $R_j=X$ at every node, as in Example C;
* $\mathrm{GL}(r,2)$ at level $j$ synchronised only between nodes $p$ and $p+(e_j,0,\dots,0)$.

*Claim.* For $r\ge3$ and levels $j\ge3$, the group $\langle R,S\rangle$ contains $\mathrm{GL}(r,2)$
acting at **every single node** of level $j$. So it is the uncoupled affine tower: $\varepsilon=1$,
and it is solved by FPT Theorem E in $\lvert\mathrm{AGL}(r,2)\rvert\cdot\mathrm{poly}(N)$.

*Proof.*
1. Let $s$ apply $A$ at the pair $\{(p_1,w_0),(p_1+e_j,w_0)\}$ and the identity elsewhere. This is
   an element of $S$.
2. Local translations below $p_1+e_j$ act transitively on the depth-$(j-1)$ nodes below
   $p_1+e_j$, and conjugating "$A$ at node $n$" by a translation that moves $n$ to $n'$ gives "$A$
   at $n'$". Hence $\langle R,S\rangle$ contains "$A$ at $(p_1,w_0)$ and $A$ at $(p_1+e_j,w')$" for
   every $w'$.
3. Quotients of two such elements give $\alpha_A=$ ($A$ at $n_1$, $A^{-1}$ at $n_2$), with
   $n_1,n_2$ both below $p_1+e_j$.
4. With a third node $n_3$ (level $j\ge3$ gives $\ge4$ nodes),
   $[\alpha_A,\alpha'_B]=([A,B]\text{ at }n_1)$, where $\alpha'_B=$ ($B$ at $n_1$, $B^{-1}$ at $n_3$).
5. These generate $[\mathrm{GL},\mathrm{GL}]=\mathrm{GL}(r,2)$ at $n_1$, because $\mathrm{GL}(r,2)$
   is simple for $r\ge3$. ∎

The mechanism: a pairing between nodes is $G$-invariant only if the groups that move nodes respect
it. Local translations move the two partners independently, so equivariance kills the coupling.
This is STR's remark that equivariance forces "Cayley-like" patterns, and it bites harder than
STR assumed.

### 4.3 Example X′: a genuinely Cayley-coupled node, and why it reduces to a coset CSP

*Definition.*
* Children of $B$ are indexed by $X=\mathbb F_2^r$.
* Fix a spanning set $E\subseteq X\setminus0$ and $H\le\mathrm{GL}(X)$ with $HE=E$.
* Child $c$ has $\lvert E\rvert$ sub-blocks $S_{c,e}$, each carrying a copy of a tree group $T$.
* $K_B=\{(t_{c,e}):t_{c,e}=t_{c+e,e}\ \forall c,e\}\cong T^{\lvert X\rvert\lvert E\rvert/2}$.
* $G_B=K_B\rtimes(X\rtimes H)$, with $X$ translating children and $H$ acting by $c\mapsto hc$,
  $e\mapsto he$. Both preserve the pairing $\{(c,e),(c+e,e)\}$, so this is a group.

*Properties.*
* The coupling graph is $\mathrm{Cay}(X,E)$, with edge labels, and is non-laminar.
* $\varepsilon_B=\lvert T\rvert^{\lvert X\rvert\lvert E\rvert/2}$.
* $P_B=X\rtimes H$ is primitive if $H$ is irreducible.

*Combine step.* There is one unknown $t_{\{c,c+e\}}\in T$ per edge. At each vertex $c$ the child
coset gives a constraint $(t_{c,e})_{e\in E}\in\Gamma_c$, a coset in $T^E$ (the projection of
$A_cz_c\cap R_c$-coset). So PCI is a **coset CSP on a Cayley graph with domain $T$**.
* *$T$ of bounded degree $f(b)$.* $K_B$ has orbits of size $\le\deg T$, so ADKT's CI gives
  $2^{O(f(b))}\mathrm{poly}$ **[PROVEN mod ADKT Thm 5]**. For fixed $T$ this is the Feder–Vardi /
  Bulatov–Dalmau Mal'tsev CSP.
* *$T$ deep.* The edge variables are coupled CI problems in $T$, and $\lvert X\rvert=2$ already
  contains $\mathrm{PCI}_{\rm diag}$. So it is TreeCI-hard.
* *Iterated X′* (each $T$ is itself an X′ tower) defeats Theorem E (unbounded $\varepsilon$),
  Theorem L (not level-synchronised) and ADKT (deep orbits). It is a reasonable test family, but
  by Cor. 2.2 it is no harder than $T^{\,2}$.

### 4.4 Aligned-position DP

In X′, and in every diagonal coupling, partners occupy aligned positions. The aligned DP descends
into all synchronised copies in lockstep, so a diagonal coupling becomes one child with a tuple
alphabet (FPT §4.5).
* *Where it works.* It is exact when the child cosets are themselves stabilisers of strings. In
  the SI-DP, $\mathrm{diag}\cap(\mathrm{Iso}(x_1,y_1)\times\mathrm{Iso}(x_2,y_2))=\mathrm{Iso}_R((x_1,x_2),(y_1,y_2))$.
* *Where it breaks.* There are two failure points.
  * With a non-trivial $P_B$ on top, each child bijection $\sigma$ gives a different tuple string.
    That is set-of-strings isomorphism (FPT §4.5), and SSI $\le_{\rm fpt}$ SI is open (Neuen
    survey §4.1).
  * When the child constraints $\Gamma_c$ couple *different* positions (any non-product
    $\mathrm{Aut}(C_c)$), lockstep descent is not a product over positions. The DP then needs CI in
    $R$ with arbitrary groups, which is TreeCI one level down and is *not* a memoised entry.
* *Cost.* Per level this costs $b!\cdot b$, compounded over $\log_bN$ levels: $N^{O(b)}$, i.e.
  Luks.

**[PROVEN]** as an analysis: aligned DP equals FPT Prop. 4.1 plus the product-alphabet trick, and it
reproduces exactly the known regimes.

### 4.5 Canonical forms, simply exponential machinery

* *DP with canonical forms at nodes* (Theorem L style). The parent form must be a function of the
  children's forms.
  * True for $\varepsilon=1$.
  * For Goursat data $(N_i,Q_i,D_B)$ one would need **quotient-relative canonisation**: a canonical
    form of $x_i$ modulo $N_i$, together with the action of $Q_i$ on such forms, and then
    canonisation under $D_B\le\prod Q_i$.
  * Theorem L does this when $D_B$ is coordinatewise with small orbits on a ground set.
  * In $T^{\,2}$, $N_i=1$ and $Q_i=R_i$ is a full child group, so the requirement is exactly
    canonisation under the child group with a tuple alphabet, plus SSI for the top. That is no
    reduction at all.
* *S-W, BCQ, ADKT.* All need a faithful domain with small orbits ($2^{O(k)}$). Theorem P succeeds
  because product actions have one, $V$ with $\lvert V\rvert=O(b\log N)$. Tree groups have none:
  the full $W(\mathcal T)$ acts faithfully only with an orbit of length about $N$. (This is
  standard for iterated wreath products of $S_b$, $b\ge3$; I did not re-prove the exact minimal
  degree.) So simply exponential CI on a small domain is unavailable for TreeCI, and this is
  precisely the difference between the solved product channel and the open tree channel.

### 4.6 Every method against $T^{\,2}$

| method | needed | on $T^{\,2}$ ($G_1\times G_2$ on $\Lambda_1\times\Lambda_2$) breaks because |
|---|---|---|
| Theorem E | $\varepsilon\le f(b)$ | $\varepsilon_B=\lvert G_2\rvert^{b-1}$ at first-coordinate nodes |
| Theorem L | synchronised part with small orbits on some $U$ | the synchronised part is $G_2$, a deep tree group with no small faithful domain |
| ADKT / S-W | small orbits | orbits of size $N$ |
| Theorem P | small faithful domain $V$ | none exists (§4.5) |
| Goursat decomposition | pieces of size $f(b)$ | piece $=G_2$ (§4.1) |
| aligned DP | product child cosets | the child cosets are arbitrary tree groups (§4.4) |
| block DP (Prop. 4.1) | cheap PCI | PCI $=$ CI in $G_2$ of projections of matrix automorphism groups |
| HJ+(M′), GNS | — | $N^{O(\log b)}$, $N^{\mathrm{polylog}\,b}$ (both are XP) |

*One more observation.* If $G_1=W(\mathcal T_1)$ is the full group, then SI under $W\times G_2$
amounts to **hierarchical set-of-strings isomorphism**: the rows of $x$, indexed by the leaves of
$\mathcal T_1$, are strings on $\Lambda_2$, unordered up to $W(\mathcal T_1)$, and $G_2$ acts on the
columns. The block DP's combine step is then CI in $G_2$ of the column projections of row-block
automorphism groups. **[PROVEN, by unwinding Prop. 4.1]** For depth-1 $\mathcal T_1$ this is SSI
with $b$ strings, which is FPT by enumerating $S_b$. In general it sits between SI and SSI for $G_2$.

---
## 5. Hardness

### 5.1 What a hardness proof would have to look like

* **ETH barrier.** **[PROVEN under ETH, mod GNS]** TreeCI$(b)$ is solvable in $N^{\mathrm{polylog}\,b}$.
  Tree groups carry a $b$-ary sequence of invariant partitions, so GNS's almost-$d$-ary algorithm
  applies, and CI reduces to SI on $N^2$ points.
  * Suppose there were an fpt-reduction from $k$-Clique to TreeCI with $b\le g(k)$. Then $k$-Clique
    would be solvable in $f(k)\,n^{\mathrm{polylog}\,g(k)}$. ETH forbids $f(k)n^{o(k)}$, so
    $g(k)\ge2^{k^{\Omega(1)}}$.
  * Conditionally on R\* ($N^{O(\log b)}$), $g(k)\ge2^{\Omega(k)}$.
  * So any W[1]-hardness proof must blow the parameter up exponentially, as FPT §1.3 noted for GI.
* **Fixed $b$ is easy.** TreeCI$(b)\in$ P for each fixed $b$ (Luks). Any source problem must
  therefore be XP and not known to be FPT, and its parameter must map to the node degree.

### 5.2 Candidate sources, and why none encodes

| source (parameter) | status | why it does not reduce to TreeCI |
|---|---|---|
| linear code equivalence (dimension $k$) | FPT: columns are points of $\mathbb F_q^k$, enumerate $\mathrm{GL}(k,q)$ | not hard |
| permutation code equivalence (hull dimension $h$) | algorithms exponential in $h$ (Sendrier; Bardet–Otmani–Saeed-Taha), cited from memory; FPT status unknown to me | the symmetry group is $S_n$ on coordinates, with composition width $n$; a tree group of degree $f(h)$ cannot simulate it |
| group isomorphism ($d$ generators) | $n^{d+O(1)}$ by generator enumeration; FPT open | Cayley-table input; no small-width permutation-group formulation |
| set-of-strings isomorphism for tree groups (none) | SSI $\le$ SI in poly time; fpt open (Neuen) | it appears *inside* $T^{\,2}$ (§4.6) and has the same open status, so it cannot serve as a source |
| GI parameterized by degree | open (the target question) | GI$_{\deg}\le$ SI$(\hat\Gamma_{d-1})$, but not known $\le$ TreeCI (§6) |
| coset CSP over a group domain (domain size) | P for fixed domain (Mal'tsev); succinct domain = CI | that *is* the problem (§4.3) |

### 5.3 The lower-bound program, sharpened

FPT §3.4 proposed a lower bound for "coset-splitting without memoisation". §2.2 picks the instance
family: **$\mathrm{PCI}_{\rm diag}$ iterated**, i.e. $T^{\,2}$ with $G_1=G_2$ given by generators.
The coupling is the simplest possible and the instances are complete, so a lower bound there is a
lower bound for the core.

The target statement is: every coset-splitting tree on these instances has $N^{\Omega(\log b)}$
leaves, where the moves are (i) split along a subgroup chain, (ii) prune by local string checks,
(iii) recurse into orbits. That would be the first lower bound for a group-theoretic model that
contains Luks. I did not prove it. **[open]**

### 5.4 Conditional implications that do hold

| implication | label |
|---|---|
| TreeCI FPT $\Leftrightarrow$ TreeSI FPT $\Leftrightarrow$ $T^{\,2}$ FPT $\Leftrightarrow$ PCI$_{\rm diag}$ FPT | **[PROVEN]** Thm 2.1 |
| TreeCI$(d!/2)$ FPT $\Rightarrow$ SI FPT for GNS's almost-$d$-ary $\hat\Gamma_d$ class | **[PROVEN]** Lemma 2.4 |
| SI$(\hat\Gamma_d)$ FPT $\Rightarrow$ TreeCI$(d)$ FPT; GI$_{\deg}$ FPT $\Rightarrow$ $P_{\rm graph}$ FPT | **[PROVEN]** (§3.5, §6) |
| SI FPT for all $\hat\Gamma_d$-groups with boundedly entangled kernels, primitive components unrestricted | **[SKETCH]** Thm E′ |

---

## 6. Graphs

### 6.1 A bounded-degree graph problem inside the core

**Proposition 6.1.** **[PROVEN, elementary]** Let $\mathcal T$ be a complete $b$-ary tree and let
$T\,\square\,T$ be the Cartesian product on all pairs of nodes. Its maximum degree is $2b+2$ and it
has at most $4N^2$ vertices.
1. Colour each vertex $(u,v)$ by $(\mathrm{depth}\,u,\mathrm{depth}\,v,x(u,v))$. Then the
   colour-preserving automorphisms are exactly the pairs $(\alpha,\beta)\in W\times W$ that
   preserve $x$.
2. If moreover the diagonal $\{(u,u)\}$ gets an extra colour, they are exactly the
   $\alpha\in W$ (diagonal) preserving $x$.

*Proof.*
* An automorphism $\varphi$ preserves depth pairs. It therefore preserves the two edge classes:
  edges that change the first depth ("row edges") and edges that change the second ("column
  edges").
* The components of the row-edge graph are the rows $T\times\{v\}$, and similarly for columns. So
  $\varphi$ permutes rows and permutes columns, and $(u,v)$ is the unique common vertex of its row
  and its column.
* So $\varphi(u,v)=(\alpha(u),\beta(v))$, where $\alpha$, the action on the column index, preserves
  tree adjacency and the root, and likewise $\beta$.
* For (2): $(\alpha(u),\beta(u))$ is diagonal for all $u$ iff $\alpha=\beta$. ∎

**Consequences.**
* GI on such coloured graphs (degree $2b+2$) is equivalent to SI under $W\times W$ on node pairs,
  the **full-group** form of $T^{\,2}$, and so reduces to $P_{\rm core}$. Internal-node colours
  are pushed down to leaf pairs as tuples of ancestor colours.
* With a marked diagonal, $P_{\rm graph}(b)$ ($W$ acting diagonally on a binary structure on
  $\mathcal T$) satisfies $P_{\rm graph}(b)\le$ GI$_{\deg}(2b+2)$ and $P_{\rm graph}(b)\le$ TreeSI$(b)$.
  The second holds because diagonal $W\le W\times W$ preserves $\mathcal T\otimes\mathcal T$.
* So **GI$_{\deg}$ FPT $\Rightarrow$ $P_{\rm graph}$ FPT**.

### 6.2 What bounded-degree GI actually produces

* *Luks (Neuen survey Lemma 4.5).* GI$_{\deg}(d)\le$ SI$(\hat\Gamma_{d-1})$. The groups are
  restrictions of automorphism groups of partial graphs. They are **not** tree groups in general:
  a vertex with several parents in the BFS layering breaks nestedness, and only the universal cover,
  of exponential size, is a tree.
* *Neuen 2020 (arXiv:2002.06997, §7, read).* $t$-CR-bounded GI $\le$ hypergraph isomorphism / SSI
  for $\hat\Gamma_t$-groups, and connected degree-$(t+1)$ graphs with one vertex individualised are
  $t$-CR-bounded. In that proof the groups act on successive colour-class partitions. Splitting
  steps are $t$-ary. Colour-refinement steps refine arbitrarily but are *kernel-free*: the group on
  the finer partition is isomorphic to the group on the coarser one. This is a different relaxation
  from GNS's semiregular steps, and I did not determine how kernel-free steps interact with the
  block DP. **[open]**
* *Product-type pieces.* The barrier families (FPT Prop. 3.1, STR Prop. 4.2) are product actions,
  so by Theorem P they are FPT whether or not they arise from graphs. The "transfer to graphs"
  question (FPT lead 4, STR lead 6) still matters as an HJ lower bound, but **no longer as an FPT
  obstruction**.

### 6.3 Is degree-$d$ GI strictly easier than the core? Precise form

* **Graph instances only intersect definable groups.** In the block DP for a graph-derived group,
  the PCI groups are restrictions, to a block, of automorphism groups of coloured bounded-degree
  structures (individualise the children). The intersection of two automorphism groups of
  structures on the same domain is the automorphism group of the union structure.
* **Hardness, if any, enters through restriction (projection).** That is how hierarchical SSI
  arises in §4.6, and how SSI arises from SI.
* **TreeCI allows arbitrary generator-given groups.** Even unparameterized, CI is not known to
  reduce to GI (Miyazaki; GI $\le$ CI is the known direction). So an fpt-reduction TreeCI
  $\to$ GI$_{\deg}$ would in particular give CI $\le$ GI for tree groups, which is new.

**Question 6.2.** Is $P_{\rm graph}(b)$ (full-group, 2-closed) fpt-equivalent to TreeCI$(b)$?
* If not, degree-$d$ GI may be strictly easier than TreeCI: the sandwich
  $P_{\rm graph}\le$ GI$_{\deg}\le$ SI$(\hat\Gamma)$ would then have TreeCI-hard instances only
  above GI$_{\deg}$.
* If yes, TreeCI FPT would be *necessary* for GI$_{\deg}$ FPT, a partial converse to Neuen's Q4.8.

**[SPECULATION]** I lean towards "strictly easier, but unprovable with current tools". All known
GI-to-group reductions produce restrictions of definable groups, and nothing forces arbitrary
generator-given entanglement.

---

## 7. Leads for the next agent (ranked)

1. **$T^{\,2}$ / iterated PCI$_{\rm diag}$.** This is the single clean target: matrices with
   tree-structured rows and columns, under $G_1\times G_2$.
   * Start with the full-group case, SI under $W\times W$ (= coloured $T\,\square\,T$ GI, §6.1).
     It is a natural bounded-degree graph family on which no FPT algorithm is known. Its block-DP
     combine step is hierarchical SSI (§4.6).
   * An FPT algorithm here would be the "genuine new idea". It would need something like
     quotient-relative canonisation (§4.5).
2. **Lower bound for coset-splitting on PCI$_{\rm diag}$** (§5.3). The instance family is now
   canonical.
3. **The residual $\hat\Gamma_d$ gap** (§3.5): entangled kernels under product-type nodes. Try to
   reduce "coordinate-tree CI" to TreeCI by running Theorem P's coordinate DP *as* extra tree
   levels over the $(J,u)$ lattice.
4. **Implement Theorem P** in `gi-practical` as a dispatcher case. It needs product-action
   recognition and a $(J,u)$-DP, with ADKT-style CI or plain Schreier–Sims on $V$; Babai's CI is
   overkill in practice. This removes the enumeration channel that FPT and STR proved costs HJ+(M′)
   $N^{\log d}$.
5. **Red-team targets.**
   * Theorem P: check BCQ (ICALP'12), Codenotti's thesis and Wiebking (SODA'20) for a prior
     statement.
   * Lemma 2.4: confirm against GNS's almost-$d$-ary definition.
   * STR Prop. 2.2: needed rigorously by Cor. 3.1 and Theorem E′.
   * Example X collapse (§4.2): independent check.
6. **Kernel-free steps** (§6.2). Does Neuen's $t$-CR route give an fpt reduction of GI$_{\deg}$ to
   TreeSI plus kernel-free levels? If kernel-free levels are harmless in the block DP, then GI$_{\deg}$
   would reduce to (a variant of) the core.

---

## 8. Sources and ledger

**Read:**
* GNS arXiv:1802.04659 source, §5 (almost $d$-ary sequences, Thm `reduction-one`).
* Neuen arXiv:2002.06997 source, §7 ($t$-CR-bounded graphs, Lemma `extend-gamma-d-group-t-cr`).
* Neuen 2026 survey §4 (Lemma 4.5, Q4.8, SSI, Lemma 4.11).
* Babai arXiv:1512.03547 abstract and §1 (SI and CI in quasipolynomial time; CI $\equiv$ SI, Luks).
* FPT, STR in full.

**Web searches (2026-11-05):**
* (i) product action / SI / FPT / CI on a small domain: nothing relevant.
* (ii) CI for iterated wreath products or tree groups: nothing algorithmic. Miyazaki's
  `beijing.pdf` (CI vs GI reducibility) appeared.
* (iii) coset CSP / Mal'tsev: Feder ECCC TR05-005, Bulatov ECCC TR02-034, Lasota arXiv:1412.4020,
  Lichter–Pago arXiv:2407.09097.

All are abstracts or snippets only.

**Cited from memory:** Scott's lemma on subdirect products of simple groups; Krasner–Kaloujnine;
Babai 1983 (CI in $\exp(\tilde O(\sqrt n))$, restated in Babai's §1); ADKT Thms 1, 5; Sendrier and
Bardet–Otmani–Saeed-Taha on hull dimension; simplicity of $\mathrm{GL}(r,2)$ for $r\ge3$.

| item | status |
|---|---|
| Thm 2.1 (TreeSI $\equiv$ TreeCI $\equiv$ PCI $\equiv$ PCI$_{\rm diag}$ $\equiv T^{\,2}$) | **[PROVEN]** |
| Cor. 2.2 (coupling pattern irrelevant), Cor. 2.3 (bounded coupling depth FPT) | **[PROVEN]** (2.3 via FPT Thm E) |
| Lemma 2.4 (almost $d$-ary $\hat\Gamma_d$ = tree groups of degree $d!/2$) | **[PROVEN]** |
| §2.4 (unfolding product types costs $\approx\lvert K\rvert$; draft obstruction retracted) | observation |
| **Theorem P** (PA-SI in $b!\,N^{3.17+o(1)}$, any top group) | **[PROVEN mod Babai CI]**; $2^{O(b\log^cb)}N^{O(1)}$ mod Babai 1983; brute-force checked on 14 instances |
| Cor. 3.1 (primitive $\hat\Gamma_d$ FPT) | **[SKETCH]** (STR Prop. 2.2, O'Nan–Scott structure [TRUST]) |
| Theorem E′ (bounded entanglement suffices for $\hat\Gamma_d$) | **[SKETCH]** |
| Prop. 3.2 (core for $\hat\Gamma_d$ = coordinate-tree CI) | (1) **[PROVEN]**, (2)–(3) **[SKETCH]** |
| Lemma 4.1 (primitive node: simple couplings all-or-nothing) | **[PROVEN mod Scott]** |
| §4.2 (Example X collapses to the uncoupled tower, $r\ge3$) | **[PROVEN]** |
| §4.3 (X′ combine = coset CSP; FPT iff shared section shallow) | **[PROVEN mod ADKT]** / analysis |
| §4.4–4.6 (aligned DP, canonisation, method table) | analysis |
| §5.1 ETH barrier | **[PROVEN under ETH, mod GNS]** |
| Prop. 6.1 ($T\,\square\,T$, $P_{\rm graph}\le$ GI$_{\deg}$, TreeSI) | **[PROVEN]** |
| FPT for TreeCI, for $\hat\Gamma_d$, or for degree-$d$ GI | **not achieved** |
| hardness reduction for TreeCI | **not achieved** |
