# w49-pruned: is the Lie-type enumeration of HJ covered by automorphisms on graphs?

Moonshot memo, branch `w49-pruned`, 2026-11-09. HJ = Hajiaghayi–JafariRaviz, arXiv:2611.01399 (local LaTeX, line numbers `L…`). Helfgott = arXiv:1710.04574 (`BDHv8.tex`). w47 = `docs/w47-mu.md`, read with `docs/redteam-w47-mu.md`. Every statement about "HJ" is about the algorithm **as written** and assumes (H0): each recursive call returns the exact coset it is specified to return. HJ is unrefereed. Nothing here is machine-checked. The Lean tree was only read. Labels: **[PROVEN]** (full argument here), **[SKETCH]** (named gaps), **[CONDITIONAL: …]**, **[SPECULATION]**. Code: `docs/w49-code/`.

## 0. Summary

**Outcome: counterexample to the conjecture of w47 §5.3, as stated. It does not show what the conjecture was meant to probe.** The conjecture fails for a simple reason specific to HJ: HJ's Case 2b gives the configuration step *one* orbital of $F$ (L2798–2813), where Helfgott gives it the whole Schurian configuration. One orbital can have a far larger automorphism group than $F$. The family below exploits exactly this. A cheap repair removes this node (§5). Whether the conjecture holds for the repaired algorithm is open.

Let $V=\mathbb F_2^d$, $U=\mathbb F_2^e$ with $d>e$ even, $\omega,\omega'$ symplectic forms, and $\Phi=V\otimes U$ ($d\times e$ matrices), $n=2^{de}$. Let $R_1$ be the pure tensors (rank-one matrices), $Q$ the quadratic form on $\Phi$ with polar form $\omega\otimes\omega'$ and $Q|_{R_1}=0$, and $H=Q^{-1}(1)$. The graph is $x=\mathrm{Cay}(\Phi,\,R_1\cup H)$.

| # | Statement | Status |
|---|---|---|
| L′ | Rectangle $B=(W,R_1;\ \mathrm{rk}(w-r)=e-1)$, $W$ the rank-$e$ matrices: $\mathrm{Aut}(B)=\mathrm{GL}(V)\times\mathrm{GL}(U)$, for $d>e\ge3$ | **[PROVEN]** §2.2; nauty $(4,3),(5,3),(6,3)$ |
| Bil | $\mathrm{Aut}(\mathrm{Cay}(\Phi,R_1))=\Phi{:}(\mathrm{GL}(V)\times\mathrm{GL}(U))$, for $d>e\ge3$ | **[PROVEN]** §2.3 |
| Aut | $\mathrm{Aut}(x)=\Phi{:}(\mathrm{Sp}(V)\times\mathrm{Sp}(U))$, for even $d>e\ge4$ | **[PROVEN]** §2.4; nauty $(4,2),(6,2)$ (outside the proof's range) |
| B′ | $\mathrm{GL}(V)\times\mathrm{GL}(U)$ on $W$ has exactly one nontrivial block system, with primitive quotient $\mathrm{GL}(V)$ on $G_e(V)$, for $d>e\ge3$ | **[PROVEN]** §2.5; GAP $(4,3)$ |
| T | For even $e\ge\max(2\kappa,6)$ and even $d\ge\max(2e+3,d_0)$, $Y\cong x$: an admissible run of HJ has a `Continue` node after a rectangle continuation that enumerates $P\cong\mathrm{GL}(d,2)$, creating $\lvert P\rvert\ge0.288\cdot2^{d^2}$ children | **[PROVEN, given (H0) and HJ as written]** §3, admissible choices listed there |
| P | At that node, $\rho(\mathrm{Aut}_H(x))\le\mathrm{Sp}(d,2)$. So any automorphism pruning leaves at least $[\mathrm{GL}(d,2):\mathrm{Sp}(d,2)]=2^{d^2/2-d/2-O(1)}=N^{\frac{1}{8e^2}\log_2N-O(1)}$ children | **[PROVEN, given T]** §4 |
| R | With Case 2b refined by the input coloring (repair R1), this node does not arise: every class at the source has size at most $(\tfrac12+o(1))q$ | **[PROVEN]** for that step §5; soundness of R1 **[SKETCH]** |
| C | Conjecture for repaired HJ | **open** §5.3 |

**What is new relative to w47.** Prop D (pruning removes the enumeration on $X_m$) does not extend: there is a graph on which the enumerated quotient has superpolynomial index over the entire node automorphism group. The rectangle has symmetry $\mathrm{GL}(V)\times\mathrm{GL}(U)$ that is not global, as the brief asked. But the input is highly symmetric, the mechanism is not CFI or local-to-global failure, and I regard the result as a defect of one step of HJ, not as evidence that Lie-type enumeration is a real obstacle for GI (§6).

---

## 1. Construction

Matrices $M\in\Phi$; $\mathrm{rk}$ is matrix rank, equal to the distance from $0$ in the bilinear forms graph $\mathrm{Bil}=\mathrm{Cay}(\Phi,R_1)$. Take hyperbolic pairs of coordinates and set
$$Q(M)=\sum_{t,s}\det M[\text{$t$-th pair of rows},\ \text{$s$-th pair of columns}]\pmod2 .$$
Polar form $\beta=\omega\otimes\omega'$, nondegenerate. $Q$ vanishes on pure tensors (each minor of a rank-one matrix is $0$). $Q$ is hyperbolic of dimension $2m=de$, since $Q$ vanishes on $V_0\otimes U$ for a Lagrangian $V_0$ (polar form zero there, and $Q=0$ on a spanning set of pure tensors). So $R_1\cap H=\emptyset$.

Let $N$ be the translation group, $F_0=\mathrm{Sp}(V)\times\mathrm{Sp}(U)$ acting by $M\mapsto gMh^{\mathsf T}$, and $F_{\rm tot}=N{:}F_0$. $F_0$ preserves $R_1$. It preserves $Q$: $Q\circ(g\otimes h)$ has the same polar form as $Q$, so it differs from $Q$ by a linear functional, which vanishes on the spanning set $R_1$. Hence $F_{\rm tot}\le\mathrm{Aut}(x)$. $F_0$ is transitive on $R_1$ because $\mathrm{Sp}$ is transitive on nonzero vectors.

---

## 2. Group theory

### 2.1 Notation for the rectangle

$W$ is the set of rank-$e$ matrices, viewed as injective maps $M:U^*\to V$. $R_1=(V\setminus0)\times(U\setminus0)$ via $(a,b)\mapsto a\otimes b$; over $\mathbb F_2$ this is a bijection. For $M\in W$:
$$\mathrm{rk}(M+a\otimes b)=e-1\iff\exists\varphi\in U^*:\ \varphi(b)=1,\ M\varphi=a .$$
So $N_B(M)=\{(M\varphi,b):\varphi(b)=1\}$, of size $(2^e-1)2^{e-1}$.

### 2.2 Lemma L′. [PROVEN]

For $d>e\ge3$, restriction gives $\mathrm{Aut}(B)\cong\mathrm{GL}(V)\times\mathrm{GL}(U)$, acting by $M\mapsto gMh^{-1}$, faithfully on $W$.

*Codegrees on $R_1$.* Let $E_2=\prod_{i=2}^{e-1}(2^d-2^i)$. Count $M\in W$ adjacent to both $(a,b)$ and $(a',b')$, by the preimages $\varphi,\varphi'$:

* $a=a'$, $b\ne b'$: $\varphi$ is one functional with $\varphi(b)=\varphi(b')=1$, giving $\mu_{\rm i}=2^{e-2}(2^d-2)E_2$.
* $a\ne a'$, $b=b'$: $\mu_{\rm ii}=2^{e-1}(2^{e-1}-1)E_2$.
* $a\ne a'$, $b\ne b'$: $\mu_{\rm iii}=(2^{2e-2}-2^{e-2})E_2$.

Distinct nonzero vectors over $\mathbb F_2$ are independent, which is used throughout. The three values are pairwise different for $d\ne e$: $\mu_{\rm ii}\neq\mu_{\rm iii}$ always, $\mu_{\rm i}=\mu_{\rm ii}$ iff $d=e$, and $\mu_{\rm i}=\mu_{\rm iii}$ would need $2^d-2=2^e-1$, impossible by parity. So every $\tau\in\mathrm{Aut}(B)$ preserves the equivalences "same $a$" and "same $b$", and $\tau(a,b)=(\alpha a,\gamma b)$ for permutations $\alpha$ of $V\setminus0$, $\gamma$ of $U\setminus0$.

*$\alpha$ is linear.* For fixed $b$, $\{a:(a,b)\in N_B(M)\}=M(\{\varphi:\varphi(b)=1\})$. These sets are exactly the $(e-1)$-dimensional affine subspaces of $V$ not containing $0$: given such a flat $a_0+L$ and $b$, take $M$ sending $b^\perp$ onto $L$ and a functional with value $1$ at $b$ to $a_0$. So $\alpha$ permutes these flats. Every affine plane avoiding $0$ is an intersection of such flats, for $d\ge e+1$: for $\pi=a+L$, $k=e-1$ and a point $p\notin\pi$, pick $\bar T\le V/L$ of dimension $k-2$ avoiding the nonzero vectors $\bar a$ and $\bar p+\bar a$, which exists since $d-2-(k-2)\ge2$. So $\alpha$ maps planes avoiding $0$ to planes avoiding $0$, that is, it preserves "four distinct nonzero vectors with sum $0$".

Then for $s\ne0$, $f(s)=\alpha(x)+\alpha(y)$ does not depend on the pair $x+y=s$ with $x\neq y$ both nonzero: two such pairs are disjoint and form a 4-set with sum $0$. Taking $x=u+y$, $z=v+y$ with $y\notin\{0,u,v,u+v\}$ gives $f(u)+f(v)=f(u+v)$, so $f$ extends to a linear map. From $\alpha(x)+\alpha(y)=f(x)+f(y)$, $\alpha=f+c$ on $V\setminus0$. Injectivity of $\alpha$ forces $f\in\mathrm{GL}(V)$, and $\alpha(V\setminus0)=V\setminus0$ forces $c=0$.

*$\gamma$ is linear.* For $a\in\mathrm{Im}\,M$, $\{b:(a,b)\in N_B(M)\}=\{b:\varphi(b)=1\}$ with $\varphi=M^{-1}a$: exactly the affine hyperplanes of $U$ avoiding $0$. Planes avoiding $0$ are intersections of these, for $e\ge3$. The argument for $\alpha$ applies.

*Conclusion.* $N_B$ is injective on $W$: $\mathrm{Im}\,M$ is the set of first coordinates, and $\{b:(a,b)\in N_B(M)\}$ determines $M^{-1}a$. So $\sigma$ on $W$ is determined by $\tau$, namely $M\mapsto\alpha M\gamma^{*}$. The converse is immediate. ∎

Machine check (`rect_check.py`): nauty gives $|\mathrm{Aut}(B)|=|\mathrm{GL}(d,2)||\mathrm{GL}(e,2)|$ exactly at $(4,3)$, $(5,3)$ and $(6,3)$. It also holds at $(4,2)$ and $(6,2)$, outside the proof's range.

### 2.3 Automorphisms of the bilinear forms graph. [PROVEN]

For $d>e\ge3$, $\mathrm{Aut}(\mathrm{Bil})=N{:}(\mathrm{GL}(V)\times\mathrm{GL}(U))$.

Let $\sigma$ fix $0$. It preserves distance, hence rank. So $(\sigma|_W,\sigma|_{R_1})\in\mathrm{Aut}(B)$, and by L′ we may compose so that $\sigma$ fixes $R_1$ pointwise. For $M$ of rank $\rho$, $\{(a,b):\mathrm{rk}(M+a\otimes b)=\rho-1\}$ is $N_B$ computed for the injective map $\mathrm{Row}(M)^*\to\mathrm{Col}(M)$, and it determines $M$, as in L′. Since $\sigma$ preserves distances to the fixed points of $R_1$, $\sigma(M)=M$. ∎

This is Hua's fundamental theorem of the geometry of rectangular matrices in this case. I proved it directly because one modern formulation found in my search requires $|D|\ne2$, and I did not confirm the $\mathbb F_2$ case in the literature.

### 2.4 Theorem Aut. [PROVEN]

For even $d>e\ge4$: $\mathrm{Aut}(x)=F_{\rm tot}$.

*Codegrees.* Common neighbours of an edge $\{u,u+v\}$ number $\lambda(v)=|S\cap(S+v)|$, with $S=R_1\cup H$. Let $\rho=\mathrm{rk}\,v$, $r=|R_1|=(2^d-1)(2^e-1)$, and $\tau_\rho=(2^d-2^{d-\rho})2^{e-1}$. Then:

* $\tau_\rho$ is the number of pure tensors $p$ with $\beta(p,v)=1$: the bilinear form $(a,b)\mapsto a^{\mathsf T}JvJ'b$ has rank $\rho$.
* $c_\rho:=|R_1\cap(R_1+v)|$ equals $2^d+2^e-4$ for $\rho=1$, $6$ for $\rho=2$, and $0$ for $\rho\ge3$. For $\rho=2$: both tensors lie in $\mathrm{Col}(v)\otimes\mathrm{Row}(v)$, normalize $v=I_2$, and count $xy^{\mathsf T}$ with $y^{\mathsf T}x=1$.
* $C:=|H\cap(H+v)|=2^{2m-2}-2^{m-1}$ for every $v\ne0$. For $Q(v)=0$ count $Q=1$ on $v^\perp$ through the hyperbolic quotient $v^\perp/v$. For $Q(v)=1$ the involution $w\mapsto w+v$ on $v^\perp$ swaps the values of $Q$, so $C=|H|-2^{2m-2}$.

Hence $\lambda(v)=c_1+2\tau_1+C$ for $v\in R_1$, and $\lambda(v)=c_\rho+2(r-\tau_\rho)+C$ for $v\in H$. The difference $\Delta(\rho)=\lambda_H(\rho)-\lambda_{R_1}$ is
$$\Delta(2)=3\cdot2^{d+e-2}-3(2^d+2^e)+12,\qquad\Delta(\rho\ge3)=2^{d+e-1}+2^{d+e-\rho}-3(2^d+2^e)+6,$$
both positive for $d>e\ge4$. So every automorphism preserves the edge set $\mathrm{Cay}(\Phi,R_1)$ and the edge set $\mathrm{Cay}(\Phi,H)$. By §2.3, a $0$-fixing automorphism is $g\otimes h$. It preserves $H$, so $Q\circ(g\otimes h)=Q$, so $\omega(g\cdot,g\cdot)\otimes\omega'(h\cdot,h\cdot)=\omega\otimes\omega'$, and over $\mathbb F_2$ this gives $g\in\mathrm{Sp}(V)$, $h\in\mathrm{Sp}(U)$. ∎

Machine checks: `check_formula.py` confirms the formula for $\lambda$ on every class at $(4,2),(6,2),(4,4)$. At $e=2$, $\Delta(2)=0$: the two edge classes are *not* separated by $\lambda$, so the proof genuinely needs $e\ge3$. `construct.py` (nauty): $|\mathrm{Aut}(x)|=2^{de}|\mathrm{Sp}(d,2)||\mathrm{Sp}(e,2)|$ exactly at $(4,2)$ ($1105920$) and $(6,2)$ ($35672555520$).

### 2.5 Lemma B′. [PROVEN]

For $d>e\ge3$, $A=\mathrm{GL}(V)\times\mathrm{GL}(U)$ on $W$ has exactly one nontrivial block system, the fibres of $M\mapsto\mathrm{Im}\,M$. The block action is $\mathrm{GL}(V)$ on $G_e(V)$, primitive and faithful.

*Proof.* $A_M=\{(g,\psi(g)):g\in P_S\}$, where $S=\mathrm{Im}\,M$ and $\psi:P_S\to\mathrm{GL}(U)$ is onto. Let $A_M\le T\le A$, and $T\cap(1\times\mathrm{GL}(U))=1\times C$. Then $C\trianglelefteq\mathrm{GL}(U)$, which is simple, because $A_M$ projects onto $\mathrm{GL}(U)$. Let $T_1$ be the projection of $T$ to $\mathrm{GL}(V)$; $P_S$ is maximal, so $T_1\in\{P_S,\mathrm{GL}(V)\}$. If $C=\mathrm{GL}(U)$ then $T=T_1\times\mathrm{GL}(U)$. If $C=1$ then $T$ is the graph of a homomorphism $\theta:T_1\to\mathrm{GL}(U)$ extending $\psi$. $T_1=\mathrm{GL}(V)$ is impossible: $\mathrm{GL}(V)$ is simple and larger than $\mathrm{GL}(U)$, so $\theta$ would be trivial, against $\psi$ onto. So $T=A_M$. ∎

GAP (`blocks.g`): at $(4,3)$, degree 2520, the only nontrivial block size at a point is $168$.

---

## 3. Theorem T: the trace through HJ

**Theorem T. [PROVEN, given (H0) and HJ as written]** Let $\kappa$ be HJ's certificate size. Let $e\ge\max(2\kappa,6)$ be even and $d\ge\max(2e+3,d_0)$ be even, where $d_0$ depends only on $e$ and HJ's constants. For $Y\cong x$, the recursion tree of HJ on $(x,Y)$, under the admissible choices (a)–(b) below, contains a `Continue` node whose group acts as $L=\mathrm{GL}(V)\times\mathrm{GL}(U)$ on the orbit $O_{\rm gen}$ of generic pairs in $W^2$, whose dispatcher enumerates $P\cong\mathrm{GL}(d,2)$, creating $|P|$ children.

With $\kappa=64$ this needs $e\ge128$ and $d\ge259$, so $n\ge2^{33152}$. It says nothing about feasible inputs.

Admissible choices. HJ leaves these open, and the Lean tree leaves them open too:

* **(a)** the source orbital in Case 2b is $R_1$ (L2804: "Choose one proper non-diagonal source orbital"; Lean `OutOrbital`: the orbital of $(t_{d-1},t_d)$, where `st_orbitalOut_good` accepts every source tuple of distinct points of $\Phi$). Moreover $R_1$ is the unique smallest non-diagonal orbital of $F$ for $d\ge e+2$: an orbit of rank $\ge2$ has size at least $(2^d-1)(2^{d-1}-2)$ by Witt, which exceeds $|R_1|$. So a smallest-orbital rule picks it.
* **(b)** the rectangle colors are beige $=$ rank $1$, cyan $=$ rank $e-1$ (L4524 allows a canonical palette choice or branching over all choices; under branching this branch exists in every run). I did not trace which color rule Lean's `sojItem` uses.

Steps (numbering as w47 §3.2):

**Steps 0–1.** Root as in w47: $\Omega_1$ first; $\mathrm{Sym}(n)$ is not small and is a giant; `GiantStep` with $\Gamma=[n]$, $q=n>\lambda$, two-label map, no `RowStep`. Tests: $T=\{a_i\otimes b_0\}_{i\le\kappa}$ with $a_i$ independent and pairwise orthogonal, and $T'=\{a_0\otimes b_i\}_{i\le\kappa}$ likewise in $U$. By Witt, $\mathrm{Sp}$ induces $\mathrm{Sym}(T)$, $\mathrm{Sym}(T')$. So $\phi_T(A_i)=\mathrm{Alt}(T)$ at every window, the loop can only end `Full`, and $K(T),K(T')\neq1$.

**Step 2: $F=F_{\rm tot}$.** $F\trianglelefteq\mathrm{Aut}_{G_0}(x)=\mathrm{Aut}(x)=F_{\rm tot}$ (it lies in $\mathrm{Alt}(n)$: translations are even for $de\ge2$, and $F_0$ is perfect). $N$ is minimal normal and self-centralizing, because $V\otimes U$ is an irreducible $F_0$-module. So $F\ge N$. Let $\bar F=F/N\trianglelefteq F_0$. If an element of $K(T)$ had trivial $\mathrm{Sp}(V)$-part, then comparing differences $a_i\otimes hb_0+n=a_{\sigma i}\otimes b_0$ forces $\sigma=\mathrm{id}$, using independence of the $a_i$. So $\bar F$ projects nontrivially to $\mathrm{Sp}(V)$, and symmetrically (with $T'$) to $\mathrm{Sp}(U)$. Normal subgroups of a product of two nonabelian simple groups are the four obvious ones, so $\bar F=F_0$.

**Step 3: Case 2b.** $F$ is transitive on $\Gamma=\Phi$. It is not a giant and not $2$-transitive ($F_0$ has several orbits on $\Phi\setminus0$), so $d_{\rm tr}=1$, no anchors. $R_1$ is a single non-diagonal orbital. HJ colors by membership in $R_1$ and applies coherent refinement. The closure of a distance-regular graph is its metric scheme, so the configuration is the rank scheme of $\mathrm{Bil}$ (rank $e+1$). It is primitive: a block is a nonzero $\mathrm{GL}\times\mathrm{GL}$-invariant subgroup of $\Phi$, hence $\Phi$.

**Step 4: first rectangle.** $q>\lambda$. Source $0$; classes are rank classes. The rank-$e$ class has fraction $\prod_{i<e}(1-2^{i-d})>3/4=\eta$. Choice (b) gives $W$, $R=R_1$ and $B$; $\mathrm{rk}(z-y)=e-1$ with $y$ pure occurs, so $B$ is nonempty. Rectangle sizes: $|W||R_1|\ll q^2$.

**Step 5.** $Y'=\Gamma\setminus(W\cup R_1)$ has at least $2$ points (ranks $0,2,\dots,e-1$), so the permitted group is full $\mathrm{Sym}(W)\times\mathrm{Sym}(R_1)$ (L4480). The answer is exact by (H0), and $L=\mathrm{GL}(V)\times\mathrm{GL}(U)$ by L′.

**Step 6.** `LiftAndContinue` runs under $H=(L\times\mathrm{Sym}(\Gamma\setminus W))\cap\mathrm{Alt}(n)$. The generic orbit $O_{\rm gen}=\{(M,M'):\mathrm{rk}[M\,M']=2e\}$ is one $L$-orbit ($\mathrm{GL}(V)$ is transitive on rank-$2e$ matrices), with $|O_{\rm gen}|/n^2\ge1-2^{2e-d}$. It is the unique largest orbit of $H$ on $\Omega_1$ for $d\ge2e+3$ (`path_numbers.py`): $W\times(\Gamma\setminus W)$ and $(\Gamma\setminus W)^2$ together have fraction at most $3\cdot2^{e-d}$ of $n^2$. Orbit-chain processes it first.

**Step 7: the dispatcher.** Top partition first or second coordinate: quotient $L$ on $W$, whose primitive quotient is $\mathrm{GL}(V)$ on $G_e(V)$ by B′. Unordered-pair tower: a maximal overgroup $T$ of $A_{\{M,M'\}}$ in $A$ is $T_V\times\mathrm{GL}(U)$, since $A_{\{M,M'\}}$ projects onto $\mathrm{GL}(U)$. So the primitive quotient is $\mathrm{GL}(V)$ acting primitively on the cosets of $T_V$. In every tower, $P\cong\mathrm{GL}(d,2)$, $\ker\rho\supseteq1\times\mathrm{GL}(U)$, $\log|P|\le d^2$, and the degree is at least $2^d-1$ (explicit in the coordinate towers; in the unordered tower this is the minimal degree of $\mathrm{GL}(d,2)$ for large $d$, cited from memory as in w47 §3.4). Hence $P$ is not Cameron-large, the Small test holds for HJ's $a$, and enumeration fires (L1154, L1766). ∎

**What $d_0$ absorbs:** $N_0$, $q_0$, the thresholds of Cor. physical-support, $\mathrm{Sym}(n)$ failing Small, $|O_{\rm gen}|>N^\gamma$, and $W$ dominant. $N=n^2$.

**Where the trace uses HJ specifics.** Only Step 3 differs in kind from w47's: the configuration is the closure of *one* orbital. In Helfgott's Case 2b it is the Schurian configuration of $F$, whose colors see $Q$. HJ changed this because orbital names are not canonical (L2793–2797).

---

## 4. Pruning

**Definition (PHJ).** At an enumeration node with group $G$, string $x$, $\rho:G\to P$, and a known subgroup $C\le\mathrm{Aut}_G(x)$: create one child per orbit of $\rho(C)$ acting by left multiplication on $P$. What is known at the node: the ancestors' certificate groups $F$ intersected with $G$, which are certified automorphisms of the full string at the ancestor and therefore of its restrictions. The strongest possible version takes $C=\mathrm{Aut}_G(x)$ for the node's string.

Soundness: children in one orbit have translated answers (standard; w28 P1, w47 Prop D).

**Theorem P. [PROVEN, given T]** At the node of Theorem T, $\rho(\mathrm{Aut}_H(x|_{O_{\rm gen}}))\le\mathrm{Sp}(d,2)$. So PHJ, even with an oracle for the full node automorphism group, creates at least
$$[\mathrm{GL}(d,2):\mathrm{Sp}(d,2)]=2^{d^2/4-d/2}\prod_{j=1}^{d/2}(2^{2j-1}-1)=2^{d^2/2-d/2-O(1)}$$
children at this node, which is $n^{\frac1{2e^2}\log_2n-O(1)}=N^{\frac1{8e^2}\log_2N-O(1)}$. With the certified group $C=F\cap H\supseteq F_0$ this count is attained exactly.

*Proof.* An element of $H$ preserving $x|_{O_{\rm gen}}$ acts on $W$ as some $(g,h)\in L$. For $N_0\in W$ there is $(M,M')\in O_{\rm gen}$ with $M+M'=N_0$ (choose $M$ with image independent of $\mathrm{Im}\,N_0$, possible since $d\ge2e$). Also $R_1\cap W=\emptyset$ for $e\ge2$. So $(g,h)$ preserves $H\cap W$, i.e. $Q\circ(g\otimes h)$ agrees with $Q$ on $W$. Since $|W|/n>3/4$ and two distinct quadratic functions on $\mathbb F_2^{de}$ differ on at least a quarter of the points (Reed–Muller minimum distance), the two are equal as quadratic forms. So $g\in\mathrm{Sp}(V)$, $h\in\mathrm{Sp}(U)$ as in §2.4. In particular the bound also holds for $\mathrm{Aut}_H$ of the full string. ∎

`stab_check.py`: at $(4,2)$, exhaustive enumeration of $\mathrm{GL}(4,2)\times\mathrm{GL}(2,2)$ finds exactly $4320=720\cdot6$ pairs preserving $Q$ on $W$, with $720$ distinct $g$.

**Does pruning move the cost?** At this node the cost is not moved, because the children are genuinely inequivalent under every automorphism. The children are not necessarily expensive (each is a `Continue` on kernel orbits under a group containing $1\times\mathrm{GL}(U)$), and a Prop-2-style count of *created* children is the only claim. I did not bound the whole tree of PHJ on this family.

**Status of the conjecture of w47 §5.3.** False as stated, for HJ as written under the admissible choices, for both readings of "$\mathrm{Aut}_H(x)$" (node string or full string), since $|P|/|\rho(\mathrm{Aut})|$ is superpolynomial in $N$.

---

## 5. Repair, and what remains open

### 5.1 Where the gap comes from

$F$ preserves $x$ but $\mathrm{Aut}(\mathrm{closure}(O))$ need not. HJ's $O$ is an $F$-orbital, chosen with no reference to $x$. An arc-transitive subgroup with superpolynomial index is exactly what the tensor family provides: $\mathrm{Sp}$ is transitive on points, which is all that pure tensors need.

### 5.2 Repair R1. [SKETCH for soundness; PROVEN for the effect on this family]

**R1:** in Case 2b, color pairs of $C$ by the pair (membership in $O$, value of the input string on that pair), and refine. When the string is not a function of the pair (later nodes), use the $G$-orbit-compressed string; I have not specified this in general, which is the gap.

Soundness sketch: $F\le\mathrm{Aut}(x)$ preserves the coloring, so homogeneity survives; $x$ and $y$ colors are canonical, so target branches cover parent isomorphisms as before.

Effect here: the color of $(0,M)$ separates $H$ from its complement. $|H|=(\tfrac12+o(1))n$ and $|\Phi\setminus H|=(\tfrac12+o(1))n$, so every class at the source has size at most $(\tfrac12+o(1))q<\tfrac34q$. HJ therefore takes the balanced colored-partition branch at this step, and no rectangle arises.

A sparse variant $S=R_1\cup Z$ with $Z$ a thin $F_0$-invariant part of rank $e$ does not obviously evade R1 either: the source class $W\setminus Z$ is then the left side and, if Lemma L′ survives deleting $Z$ from the left side, the rectangle group must stabilize $Z$. **[SPECULATION]**

### 5.3 Open question

**Conjecture for HJ+R1. [SPECULATION]** At every node of HJ+R1 on a graph input where a Cameron-small quotient is enumerated after a rectangle continuation, $|P|\le N^{O(1)}|\rho(\mathrm{Aut}_H(x))|$.

The conjecture's original evidence was w47 §5.3's two bullets. Both now need restating. The Case 2b bullet ("$F$ must be transitive on an orbital of a classical scheme, so $F\ge\mathrm{SL}$") holds for the Grassmann scheme **[CONDITIONAL: Kantor's line-transitivity theorem, from memory]** and is false for bilinear forms schemes, where point-transitive $\Gamma$ on each side suffices. I have not resolved the Case 3 bullet.

---

## 6. What this means

**For HJ as written** (given (H0), and choices (a)–(b)): the enumeration channel at this node is not covered by automorphisms, so Prop D has no general form. The defect is local to Case 2b's single-orbital rule.

**For pruned HJ.** PHJ, as defined in §4, still creates $N^{\Omega(\log N)}$ children at this node with $e$ fixed. Any improvement must change the path, for example by R1, and not the pruning. I have no whole-tree statement for PHJ.

**For GI.** Nothing. The family is easy by other means: $\lambda$ recovers $R_1$ in polynomial time, and then both inputs carry a bilinear forms structure with a quadratic form, whose comparison is linear algebra **[SKETCH: I did not write out the recovery of $V$, $U$ and the comparison of $Q$]**. The result gives no evidence that graphs are as hard as strings, and it does not address Neuen's Q4.8 (the family has unbounded degree and composition width).

**Relation to the "graphs are easier" hope.** A theorem of the form "enumerated Lie quotients on graphs are automorphism-covered" cannot hold for HJ as written. It is not refuted for HJ+R1.

---

## 7. Other candidates, and why they did not work

Each is a reasoning note, not a trace to HJ's level of detail; none is claimed beyond its label.

| Candidate | Result | Status |
|---|---|---|
| Arc-transitive $F\ll\mathrm{Aut}(O)$ on Grassmann $J_2(m,2)$ | $F$ line-transitive forces $F\ge\mathrm{SL}$ (Kantor 1972, from memory); no gap | **[CONDITIONAL: Kantor]** |
| Polar spaces, $F=\Gamma\mathrm U(k,2)<\mathrm O^-(2k,2)$ on singular points | $F$ is arc-transitive on non-perp pairs, a real superpolynomial gap, but the non-perp class has density $\tfrac12$: balanced, no rectangle | **[SKETCH]** |
| Same, $q\ge4$ for dominance | non-perp pairs split into $q$ classes under $\mathrm{GU}$; field automorphisms do not merge them | **[SKETCH]** |
| Hamming $H(d,q)$ with $F=T\wr C_d$ | dominant class needs $q\gtrsim 2.5d$, then the top is $\mathrm{Alt}(q)^d$: product refinement, not Cameron-small | **[SKETCH]** |
| Rank-metric/forms graphs on $\mathrm{Alt}$, $\mathrm{Her}$ | $\log n\sim d^2$, so $|\mathrm{GL}(d)|$ is polynomial in $n$ | **[PROVEN arithmetic]** |
| Solvable transitive $\Gamma$ (Singer) in place of $\mathrm{Sp}$ | gives larger index, but a solvable-by-bounded point stabilizer has no $\mathrm{Alt}(\kappa)$ section for $\kappa$ large, so no Full test and $F=1$ | **[PROVEN]** |
| CFI covers of $X_m$, T2 with intermediate $\chi$, Case 3 generally | Not completed. Windows stop only at asymmetry or fullness: if no local asymmetry stops a test, the Step 4 chain reaches the global asymmetry and the tuple color is fine (w47 §5.3). Coarse Case 3 colors need exact design-like statistics on $\kappa$-tuples. I could not build a rigid example | **[SKETCH]**, documented failure |
| Finite quotients of affine buildings (locally $\mathrm{PG}$) | link size forces $n\ge q^{d^2/4}$, so $|\mathrm{GL}(d,q)|=n^{O(1)}$: no superpolynomial enumeration from the link | **[SKETCH]** |

**Lead worth keeping [SPECULATION].** Theorem P's index grows if $\mathrm{Sp}(V)$ is replaced by a smaller transitive group with an $\mathrm{Alt}(\kappa)$ section, for example $\mathrm{SL}(\kappa,2^{d/\kappa})$, whose order is $n^{O(1)}$. That would give a graph with polynomially bounded $\mathrm{Aut}$ and the same $|P|$. It needs a connection set with exactly that stabilizer, and the natural $\mathbb F_{2^s}$-rank sets have larger groups. I did not find one.

---

## 8. Experiments and what they do not show

| Script | Check | Result |
|---|---|---|
| `construct.py d e` | $|\mathrm{Aut}(x)|$ (nauty); $\lambda$ by class | $(4,2)$: $1105920$; $(6,2)$: $35672555520$; both equal $2^{de}|\mathrm{Sp}(d,2)||\mathrm{Sp}(e,2)|$ |
| `check_formula.py` | $\lambda$ formula of §2.4 | agrees on all classes at $(4,2),(6,2),(4,4)$ |
| `rect_check.py d e` | $|\mathrm{Aut}(B)|$ (nauty; sparse mode for $(6,3)$) | $(4,2),(6,2),(4,3),(5,3),(6,3)$: equals $|\mathrm{GL}(d,2)||\mathrm{GL}(e,2)|$ |
| `blocks.g` | block systems (GAP) | $(4,3)$: only size $168$ |
| `stab_check.py` | pairs preserving $Q$ on $W$ | $(4,2)$: $4320$ |
| `path_numbers.py` | sizes along the trace | $|W|/n$, $|O_{\rm gen}|/n^2$, index exponents; needs $d\ge2e+3$ for $O_{\rm gen}$ to dominate (e.g. it fails at $(200,128)$) |

**What does not transfer.** The theorem needs $e\ge2\kappa$ and $d\ge2e+3$. All computation is at $e\le4$; the group facts checked are the ones proved in §2. No experiment runs HJ's path, and the Python solver in `gi/` does not implement Case 2b orbital refinement or the first rectangle. Note $e=2$ is outside Theorem Aut's proof ($\Delta(2)=0$), although nauty confirms the conclusion there.

---

## 9. Novelty and sources

Searches (2026-11-09): nothing found on HJ's Case 2b rule or on automorphism pruning at enumeration nodes; the HJ paper itself did not surface. I claim "not found", not "new". The ingredients are classical: bilinear forms graphs and Hua's theorem, $\mathrm{Sp}\otimes\mathrm{Sp}<\mathrm O^+$, Witt's theorem, and $\mathrm{RM}(2,m)$ minimum distance. The observation that one orbital of a group can have a much larger automorphism group is standard (arc-transitive subgroups); its use against HJ's Case 2b is the only content here that I could not find stated.

**Leads.** (1) Decide the conjecture for HJ+R1, first on Case 2b inputs. (2) Specify R1 at inner nodes and verify it inside the potential. (3) Find a connection set whose stabilizer is $\mathrm{SL}(\kappa,2^s)\times\mathrm{GL}(U)$ (§7). (4) Whole-tree bound for PHJ on this family, including other orbital choices. (5) Case 3 remains the unresolved direction: construct a rigid graph with coarse tuple colors at HJ's actual window depth, or prove none exists.

**Reproduction.** From `docs/w49-code/` with `python3`, nauty 2.9.1 and GAP 4.15.1 at the store paths in the scripts: `python3 construct.py 4 2`; `python3 construct.py 6 2`; `python3 check_formula.py`; `python3 rect_check.py 5 3`; `python3 stab_check.py`; `python3 path_numbers.py`; `gap -q -b blocks.g`.

Sources: arXiv:2611.01399 (local LaTeX, read at L700–1090, L1092–1236, L2593–3028, L4400–4560) · [Helfgott, arXiv:1710.04574](https://arxiv.org/abs/1710.04574) §5.2, §6.2 (local) · Lean tree `Algorithm/OutOrbital.lean`, `Impl/AggStructMath.lean`, `Algorithm/AuxRectangle.lean` (read only) · [Huang–Zhao, graph homomorphisms on rectangular matrices](https://ar5iv.labs.arxiv.org/html/1701.07324) and [Huang–Wan, adjacency preserving maps](https://emis.univie.ac.at/journals/BAG/vol.45/no.2/b45h2hua.pdf) (search results only, full text not read) · Kantor, *Line-transitive collineation groups of finite projective spaces*, Math. Z. (1972), from memory, not re-read.
