# Group isomorphism: working notes for a direct attack

Started 2026-11-09, as of master `2dbaade`, by one AI session, at the user's request to "try for the general problem just for fun". It continues [groupiso-scoping](groupiso-scoping.md). **Nothing here is a result.** Every statement is tagged; nothing has had a red-team pass unless its tag says so, and novelty against the literature is unchecked unless stated. The target is group isomorphism from Cayley tables in N^{o(log N)}; the core case is p-groups.

## 0. Notation

G is a p-group of order N = p^ℓ. The lower exponent-p central series is P₁ = G, P_{i+1} = [P_i, G]·P_i^p, so P₂ = Φ(G). L_i = P_i/P_{i+1} has dimension d_i; V = L₁, d = d₁, m = ℓ − d. Q_i = G/P_{i+1} is the quotient of p-class i. M(Q) is the p-multiplicator of Q; for a minimal presentation Q = F/R it is R/[R,F]R^p, and M(Q)^* ≅ H²(Q, F_p) compatibly with Aut(Q) (five-term sequence, because H¹(Q) → H¹(F) is an isomorphism). dim M(Q) ≤ O(log² |Q|).

Standard fact used throughout: Q_{i+1} is a central extension of Q_i by L_{i+1} with L_{i+1} ≤ Φ, so it corresponds to a surjection λ: M(Q_i) → L_{i+1}, equivalently to the subspace S_{i+1} = λ^*(L_{i+1}^*) ≤ H²(Q_i, F_p) of dimension d_{i+1}. Two such extensions of Q_i are isomorphic as groups iff their subspaces lie in one Aut(Q_i)-orbit. The kernel of Aut(Q_{i+1}) → Aut(Q_i) is Hom(V, L_{i+1}). This is the framework of the p-group generation algorithm (O'Brien 1990) and of Eick–Leedham-Green–O'Brien 2002.

## 1. L1: lifting a fixed map on the Frattini quotient [SKETCH; believed known in computational group theory]

**Statement.** Let U be a p-subgroup of GL(V_G) (for example the trivial group, or the unipotent radical of the stabilizer of a complete flag) and ψ₀: V_G → V_H an isomorphism. The set of isomorphisms G → H that induce an element of ψ₀U on the Frattini quotients is empty or a coset of a p-group, and can be computed (generators plus one element) in time poly(N).

**Sketch.** Induct on i, holding the answer for Q_i as a coset φ_i·K_i with K_i ≤ Aut(Q_i(G)) a p-group; K_i is a permutation group of degree ≤ N, so its order, a polycyclic generating sequence and kernels of homomorphisms to F_p are polynomial time. Transport S_{i+1}(H) to H²(Q_i(G), F_p) by φ_i. The step is the transporter of one subspace to another in the module W = H²(Q_i(G), F_p) under the p-group K_i. W has dimension O(ℓ²) and is computed by linear algebra on cochains (N² coordinates).

* A p-group acts unipotently. A K-invariant complete flag comes from iterated fixed-point spaces.
* Vector case: with W₁ the bottom of the flag (fixed pointwise), and S̄ the stabilizer of v + W₁ in W/W₁ (recursion), s ↦ s·v − v is a homomorphism S̄ → W₁ ≅ F_p. The stabilizer of v is its kernel; the orbit is v + image. Transporter and canonical representative follow.
* Subspace case: if W₁ ≤ S pass to W/W₁. Otherwise handle (S + W₁)/W₁ first; then S is a complement to W₁ in T = S + W₁, complements correspond to functionals θ on T with θ|W₁ = id, and the group acts on these through the dual action on T^*, which is a vector problem.

Each of the O(ℓ²) steps takes a kernel of a homomorphism to F_p inside a permutation group of degree N. The same recursion gives a canonical form of (G, ψ₀U-class of bases), needed for collision arguments; that part needs the canonical choices written out.

**Literature.** Stabilisers under the p-part are computed this way in practice (Schwingel's algorithm, cited in ELO 2002). A statement in the Cayley-table complexity model was not looked for yet.

## 2. T1: the Frattini-flag bound [SKETCH; novelty unchecked]

The stabilizer in GL(d,p) of a complete flag is U ⋊ T with U a p-group and T a torus of order (p−1)^d ≤ N. Fix a complete flag of V_G. Enumerate the complete flags of V_H (at most 2^d·p^{d(d−1)/2}) and the torus elements, and apply L1 to each. This decides isomorphism in p^{d²/2 + O(d)}·poly(N).

With bidirectional collision (canonical forms of (G, framed flag); half-flags on each side) the count is the square root: **p^{d²/4 + O(d)}·poly(N)**.

Comparison: the best general bound is p^{ℓ²/4 + O(ℓ)} (Le Gall–Rosenbaum). T1 replaces ℓ by d = d(G). It gains nothing when m = ℓ − d is O(1), and it gives exponent constant (d/ℓ)²/4 in general, for example 1/9 at d = 2ℓ/3.

## 3. T2: reduction to quotients with large p′-symmetry [SKETCH; conditional on a property of the class-2 algorithms]

Let A₂ be the image of Aut(Q₂(G)) in GL(V), and suppose Iso(Q₂(G), Q₂(H)) is available as a coset with generators (Q₂ has p-class 2; that is the case treated by Ivanyos–Mendoza–Qiao–Sun–Zhang and by Sun 2611.05920, **if** those algorithms output cosets, which is to be checked). A₂ is a permutation group on V of degree p^d ≤ N, so a Sylow p-subgroup P and a transversal are polynomial time. For each of the |A₂|_{p′}-many cosets apply L1 with U = P. Total: (cost of the class-2 algorithm) + |A₂|_{p′}·poly(N).

So p-groups are in N^{o(log N)} **unless** |A₂|_{p′} ≥ p^{εℓ²}. That forces d = Θ(ℓ) and a section of A₂ that is a classical group of rank Θ(ℓ) in characteristic p (to be made precise). The remaining problem is the relative one of §6.

Observation on those hard cases: all modules of such a classical group Γ that fit in dimension O(ℓ²) are of degree at most 2 in the natural module X. So the whole of G is described by data of degree ≤ 2 in X, with multiplicity spaces of dimension O(1)·(ℓ/dim X).

## 4. T3: exponent p and class ≤ p reduce to Lie algebras, without Lazard [SKETCH for p = 3 and class 3; SPECULATION beyond]

**Exponent 3.** Let B = B(d,3) be the free exponent-3 group of rank d and 𝔏 = V ⊕ Λ²V ⊕ Λ³V the free 2-Engel Lie algebra over F₃. γ₂(B) is elementary abelian, with basis the basic commutators [x_i,x_j] (i<j) and [x_i,x_j,x_k] (i<j<k); identify it with 𝔏² = Λ²V ⊕ Λ³V by this basis.

* A subgroup R ≤ γ₂(B) is normal iff [R, B] ≤ R, and [c, x] for c ∈ γ₂(B) is the Lie bracket of the classes. So normal subgroups of B inside γ₂(B) are exactly the ideals of 𝔏 inside 𝔏².
* d-generated groups of exponent 3 up to isomorphism are the Aut(B)-orbits on such R; d-generated 2-Engel Lie algebras over F₃ are the Aut(𝔏)-orbits on such ideals.
* Claim: Aut(B) and Aut(𝔏) have the same image in GL(γ₂(B)) = GL(𝔏²). Both images are block triangular with diagonal (Λ²A, Λ³A). The off-diagonal blocks are D(f)·Λ²A, f ∈ Hom(V, Λ²V), D(f)(x∧y) = [x,f(y)] + [f(x),y], for 𝔏; for B there is an additional correction E_A from [xy,z] = [x,z][x,z,y][y,z]. E_A is of the form D(f_A)·Λ²A: the automorphism σ that inverts each x_i fixes each [x_i,x_j] (2-Engel), so span{[x_i,x_j]} is the (+1)-eigenspace of σ on γ₂(B); another basis gives another lift of −1, which differs from σ by an IA-automorphism, and IA-automorphisms move the eigenspace by D(f). Checked by hand on y₁ = x₁x₂: E = D(f) with f(y₁) = −y₁∧y₂.

Consequence: **G = B/R ↦ 𝔏/R is a bijection between isomorphism classes of groups of exponent 3 and of finite 2-Engel Lie algebras over F₃.** Concretely, for G with generators g₁..g_d: the Lie algebra has the graded pieces of G, and for a weight-2 relator k = Σ a_ij x_i∧x_j (in the kernel of Λ²V → γ₂/γ₃) the deformation is c(k) = Π [g_i,g_j]^{a_ij} ∈ γ₃(G). Computable in poly(N).

With a linear-length reduction from Lie algebra isomorphism to 3-tensor isomorphism (Grochow–Qiao IV, to be checked that it covers this) and the N^{Õ((log N)^{1/2})} algorithm, this would put **all groups of exponent 3** in N^{Õ((log N)^{1/2})}. Lazard only covers class < p, that is class ≤ 2 for p = 3.

**General form (torus linearization).** For p odd, exponent p, class 3: groups with graded Lie algebra L form a torsor under H(L) = Hom(K₂, L₃)/D(Hom(V, L₂)); Aut_gr(L) acts affinely; the central element z_λ = (λ, λ², λ³) has linear part λ ≠ 1 on H(L), so it has a unique fixed point, which is fixed by all of Aut_gr(L). That gives a canonical base point and an equivariant identification with the Lie side. For class c the deformation degrees are 1..c−2 and λ^j ≠ 1 needs j ≤ p−2, so the expected range is **exponent p, class ≤ p** [SPECULATION: needs an induction, not a one-step torsor].

**Where it stops.** With p-th powers, weights mix (x^p has weight 1, [x,y] weight 2), z_λ is not an automorphism of the graded object and there is no canonical base point: the affine action can be non-split. For p = 2 there is no torus.

**To check:** the literature on exponent-3 groups and on "Lazard for class p"; a machine check on small cases (count exponent-3 groups against 2-Engel Lie algebras of order 3⁷..3⁹ is not possible without GAP; a direct check of the eigenspace claim in B(4,3) is).

## 5. T4: fixing the bottom [SPECULATION]

Enumerate ψ: Φ(G) → Φ(H) (at most p^{m²}). Then φ is determined modulo C = C_G(Φ(G)); [C, G] ≤ Z(Φ(G)), C has class ≤ 2, C/Z(Φ) embeds in V. The residue is an isometry problem with fixed target for the commutator form on C (polynomial time for odd p by Ivanyos–Qiao / Brooksbank–Wilson in the pure case) coupled to crossed homomorphisms κ(c): V → Z(Φ) and to the relations among coset representatives. Whether the coupled problem is polynomial time is open here. If it is: all p-groups in min(p^{d²/4}, p^{m²})·N^{O(1)}, balanced at d = 2ℓ/3: exponent constant 1/9; about 0.086 with a collision at the bottom as well.

## 6. The crux: the central relative problem [SPECULATION]

**CRP.** Given Q of order p^n, Aut(Q) by generators, and subspaces S, S′ ≤ H²(Q, F_p) of dimension z, find α ∈ Aut(Q) with α·S = S′, in time p^{o((n+z)²)}.

For Q elementary abelian and p odd this is isomorphism of p-class-2 groups (S ≤ Λ²V^* ⊕ V^*). Solving CRP for Q of p-class i, with output as a coset, gives p-class i+1, so CRP in general is equivalent to the whole p-group problem.

What is special about H²(Q) as a module:

* Aut(Q) = K ⋊-like extension with K a p-group (handled by L1) and the image A in GL(V).
* S projects isomorphically to the "graded" part (the structure maps L₂ × V → L₃ and the p-map L₂ → L₃), and is the graph of a map c from that part to the weight-2 relators' dual: a 3-tensor with all sides O(ℓ), defined up to an affine gauge.
* The gauge f ∈ Hom(V, L₂) acts on c by translation by D(f), which is linear in f. When a graded base point exists (T3) the pair (graded algebra, c) is one filtered algebra and CRP is an algebra isomorphism. In general the translation part of the action of A is a polynomial (degree 2 or 3) cocycle and there may be no base point; this is the same phenomenon as quadratic forms against alternating forms in characteristic 2 (D₈ against Q₈), which Sun 2611.05920 and arXiv:2610.00874 handle for class 2.

**Question to settle by reading:** how the class-2 algorithms treat the characteristic-2 quadratic refinement, and whether that treatment extends to the affine gauge above. If it does, p-class 3 follows, and the same step iterates.

## 7. What the class-2 algorithms do (read from the papers, 2026-11-09)

Read directly from extracted PDF text: IMQSZ §1–§3 and the start of §4.1; Sun 2611.05920 abstract, introduction, §1.3, §2.1 and a keyword search of Appendix A; Grochow–Qiao IV by keyword search only (Cor 1.4, Thm 1.10, Thm 7.3, Prop 7.5). Not read: IMQSZ §4.3 (proof for Cond-Alt-MTC) and §5; Sun §3 onward; Sun 2303.15412; arXiv:2610.00874.

**IMQSZ (alternating matrix space congruence of length n over F_q in q^{Õ(n^{1.5})}).**

1. Reduce to equivalence of matrix spaces for an n×n×n tensor (Grochow–Qiao, linear length).
2. Individualize L ∈ M(s×n, q) and R ∈ M(n×s, q), s = ⌈3·max(n/r, r)⌉, r = ⌈√n⌉. Lemma 3.4: for random L, R the kernel K = {A : LAR = 0} has maximal rank ≤ r with probability ≥ 1 − q^{−r}. On the other side all L′, R′ are enumerated: q^{O(sn)}.
3. A canonical basis of the image labels the quotient 𝒜/K. Lemma 3.6: mrk(K) = r implies ncrk(K) ≤ O(r log r). The canonical shrunk subspace (Ivanyos–Qiao–Subrahmanyam) gives a block shape (a,b,c,d,e,f) with d + f = ncrk(K).
4. The equivalence matrices are then block triangular; the small blocks are enumerated (q^{(d+f)n}); the rest splits into three sub-arrays in each of which one of the three acting matrices is already trivial. These are three correlated matrix-*tuple* problems, assembled into one "conditional alternating matrix tuple congruence" instance, polynomial time (Lemma 3.9, through the *-algebra method of Ivanyos–Qiao).

Own reading of step 4 [not a statement of the paper]: the tensor vanishes on unknown × unknown × unknown, so every residual constraint has a frozen direction and is of module-isomorphism type. In group language: after individualizing Õ(√ℓ) elements there are subspaces U, U′ ≤ V of total codimension Õ(√ℓ) with [U, U′] inside the span of commutators with the individualized elements.

**Sun 2611.05920 (all p-groups of class 2).**

* Tensor-isomorphism structure is used to *restrict* the search: a chain Z(G) ≤ C ≤ B ≤ G, an additive labelling ρ on B vanishing on C, and a small exceptional central subgroup Z with [x, F] ≤ Z when ρ(x) = 0.
* The linear part is "matching": alternating matrix tuple isometry over R = Z/p^τ (its Theorem 2.1: p^{O(τ n^{7/4} log(τn))}·poly, **returning a generating set of the automorphism group**).
* The non-linear remainder (top base-p digits of power coefficients, from (xy)^q = x^q y^q [y,x]^{C(q,2)}) is confined to a small part and recovered by explicit orbit computation.
* Appendix A uses transporters under unipotent groups with Schreier's lemma and computes automorphism groups (A.6). So L1-type machinery is standard in this literature, and cosets with generators are available from the class-2 algorithms in principle (T2's assumption; the exact statement for Aut(Q₂) is still to be pinned down).

**Grochow–Qiao IV 2306.16317.** Cor 1.4 covers class c < p **and exponent p**. Thm 7.3 is the Lazard correspondence between groups of order p^n and class c < p (any exponent) and Lie rings of the same order and class; the Cayley-table realisation (Prop 7.5) is stated for exponent p. Thm 1.10: associative and Lie algebra isomorphism reduce to 3-tensor isomorphism with linear blow-up in length. Cubic forms need p > 3.

**Answer to the question of §6.** The class-2 treatments of non-linearity are "confine it to a small exceptional part and enumerate". Neither paper treats an affine gauge acting on a big part. So the extension to p-class 3 is not a matter of quoting them.

## 8. Architecture sketch for general p-groups [SPECULATION]

1. Form the graded object gr(G) = ⊕ L_i with brackets L_i × L_j → L_{i+j} and p-maps L_i → L_{i+1} (L_i → L_{pi} is the restricted structure; the lower exponent-p series also gives the shift-by-one p-map). It is an algebra of dimension ℓ computable in poly(N), and G ≅ H implies gr(G) ≅ gr(H).
2. With linear-length reductions and the class-2 machinery applied to gr (if the p-maps can be encoded; for p odd they are semilinear-free, linear on L_i for i ≥ 2 and "linear plus bracket correction" on L₁), obtain Iso_gr as p^{Õ(ℓ^{1.5})} cosets of a group Λ of *-algebra type: a p-group radical extended by a product of classical groups.
3. Decide which elements of those cosets lift to G → H: a tower of affine spaces H_i (deformations at p-class i+1), with Λ acting affinely.
4. Small classical factors are enumerated. For large ones the lifting condition has to be solved as a tuple-of-forms problem; the obstacles are the unipotent gauge and the non-linear translation cocycle of §6. Sun's pattern (confine the non-linearity to a small exceptional part, enumerate its orbit) is the only template found so far.

## 9. T6: class < p with arbitrary exponent [SPECULATION; novelty unchecked]

Lazard holds for class c < p at any exponent and gives a Lie ring of order p^ℓ, a module over Z/p^k. Grochow–Qiao IV stops at exponent p. Candidate route: realise the correspondence in the Cayley-table model for exponent p^k (BCH formulas have denominators prime to p for c < p, so this should be routine), then reduce Lie ring isomorphism over Z/p^k to tensor problems over Z/p^k and use the commutative-ring results (Grochow–Qiao–Sun et al., STOC 2025, matrix tuple isometry over Z/p^τ for odd p; Sun 2611.05920 Thm 2.1). Open points: the modules are not free over Z/p^k; whether the linear-length gadgets and the individualization lemmas work over such rings; whether this is already known.

## 10. Cochain view [SPECULATION]

p-class-3 extension data over V are defining systems for triple Massey products in C^*(V, F_p). C^*(B(Z/p)) is not formal for odd p (the p-fold Massey power of a degree-1 class is minus the Bockstein), which is the source of the p = 3 anomaly in T3: an alternating trilinear form is a 3-coboundary on V in characteristic 3 since 3! ≡ 0. An A_∞ model on (H¹, H²) is not of linear size, since H² has dimension Θ(d²). No algorithmic use found.

## 12. RP: extending a fixed isomorphism of the Frattini subgroups [SKETCH; odd p; this replaces the vague §5]

**Problem RP.** G, H p-groups of order N, ψ: Φ(G) → Φ(H) an isomorphism. Find all isomorphisms φ: G → H with φ|Φ(G) = ψ. Claim: polynomial time for odd p.

Identify Φ(H) with Φ = Φ(G) through ψ. Z = Z(Φ). ρ_G: G → Aut(Φ) is conjugation, C_G = ker ρ_G. Conventions: [a,b] = a⁻¹b⁻¹ab, x^y = y⁻¹xy.

* Necessary: ρ_G(G) = ρ_H(H), because φ|Φ = id forces ρ_H∘φ = ρ_G.
* Lemma 1. [C_G, G] ≤ Z; C_G ∩ Φ = Z ≤ Z(C_G); C_G/Z ≅ C_GΦ/Φ =: Ū is elementary abelian; C_G has class ≤ 2; for every g ∈ G the map κ_g(c) = [c, g] is a homomorphism C_G → Z.
* Choose t₁..t_k ∈ G mapping to a basis of G/C_GΦ, and t′_j ∈ H with ρ_H(t′_j) = ρ_G(t_j). Write κ_j = κ_{t_j}, κ′_j = κ_{t′_j}.
* Lemma 2. The isomorphisms φ extending ψ correspond to pairs (φ_C, (c_j)) with φ_C: C_G → C_H an isomorphism that is the identity on Z, and c_j ∈ C_H (φ(t_j) = t′_j c_j), such that, written additively in Z:
  1. κ_j = (κ′_j + [·, c_j])∘φ_C in Hom(C_G, Z);
  2. ν′_j(c_j) = z_j, where ν′_j(c) = c^p·∏_{i=1}^{p−1}[c, t′_j^i] and z_j = t′_j^{−p}·t_j^p ∈ Z;
  3. κ′_j(c_i) − κ′_i(c_j) + [c_i, c_j] = z_ij, where z_ij = [t′_i, t′_j]⁻¹[t_i, t_j] ∈ Z.
  (Presentation of G relative to N = C_GΦ = C_G ∘_Z Φ; the conjugation relations on Φ hold automatically.)
* For odd p, ν′_j is a homomorphism C_H → Z, and by the Baer trick C_G is an abelian group C⁺ ⊇ Z with an alternating map b: Ū × Ū → Ω₁(Z).
* Put W = C⁺ ⊕ (free module on t₁..t_k) and the alternating Z-valued form 𝔸(c + Σa_j t_j, c′ + Σa′_j t_j) = b(c,c′) + Σ a′_j κ_j(c) − Σ a_j κ_j(c′) + Σ a_i a′_j ω_ij, with ω_G(t_i,t_j) = z_ij and ω_H = 0. Then (φ_C satisfies 0) ∧ (1) ∧ (3) ⟺ g = [[φ_C, c],[0, 1]] is an isometry (W_G, 𝔸_G) → (W_H, 𝔸_H) with g|Z = id, g(C_G) = C_H, g ≡ id on W/C. This is a **fixed-target** isometry problem with block constraints.
* (2) is then a homomorphism condition: on the solution group of (0),(1),(3) the map g ↦ (ν_j(c_j(g)))_j is a homomorphism to Z^k (uses ν′_j∘φ_C = ν_j, which follows from (1)). Its kernel is found by permutation-group methods (act by translation on the cyclic factors of Z^k).

**Principle Q** (the engine) [SKETCH]. The set of g ∈ Aut(W) that preserve a system of bi-additive forms with frozen values, lie in a given unital subring 𝔭 of End(W), and are ≡ 1 modulo a two-sided ideal of 𝔭, is the unitary group of a finite ring with involution (pairs (X, Y) with 𝔸(Xw, w′) = 𝔸(w, Yw′), involution (X,Y) ↦ (Y,X)). For odd p its generators are polynomial time: semisimple quotient by Wedderburn (classical groups), lifting unitaries by u ↦ u(1 − s/2) with s = u^*u − 1, the kernel by Cayley transforms of skew elements. Over F_p this is Brooksbank–Wilson 2012 and Ivanyos–Qiao 2019; over Z/p^e the same lifting should work (to be written; compare the STOC 2025 paper on commutative rings). Transporter version: the same with W_G ⊕ W_H.

**Consequence T4′** [SKETCH, odd p]: isomorphism of p-groups in p^{m·d(Φ)}·poly(N), by enumerating Iso(Φ(G), Φ(H)) by generator images (m = log_p |Φ(G)|). More generally in p^{ℓ·s}·poly(N), where s is the least number of elements generating a subgroup that contains Φ(G).

**Consequence T5: the constant** [SKETCH, odd p]. min(T1, T4′): exponent min(d²/4, m²) ≤ ℓ²/9 with collision at the top (d = 2ℓ/3), or min(d²/2, m²) ≤ ℓ²/(1+√2)² ≈ 0.172·ℓ² without any collision argument. Either is below the known ℓ²/4. So: **p-groups of odd order in N^{(1/9)·log_p N + O(1)}**, if L1 (with canonical forms), RP and Principle Q hold. The class-2 case with ψ fixed on the centre is the known p^{O(w²)} algorithm; RP is its generalisation to every p-group.

p = 2: needs fixed-target isometry for quadratic maps in characteristic 2 (no Baer trick, ν is not a homomorphism). Not attempted.

## 13. Slots [SPECULATION; a way to organise the general problem]

A constraint is cheap when at most two of its arguments are unknown and its target is frozen (Principle Q). The class-2 problem V × V → L₂ has three unknown slots; IMQSZ individualize Õ(√ℓ) vectors to reach "unknown × unknown × unknown = 0". RP is the statement that freezing Φ(G) leaves only two-slot constraints, in every p-group. Top-fixing (L1) is the other polynomial regime: everything is a p-group and Luks-type set stabilisers apply (L1 follows from Luks 1982 once a flag-stabilising ambient p-group in Sym(G) is written down).

What a general algorithm needs: an individualisation of cost p^{o(ℓ²)} after which all constraints are two-slot or unipotent. Beyond class 2 the group law itself is not bilinear ([uu′, x] = [u,x][u,x,u′][u′,x]), which is the non-linear cocycle of §6.

## 14. Symmetry dichotomy [SPECULATION]

Suppose Iso(Q_i(G), Q_i(H)) is known as p^{o(ℓ²)} cosets of a group Λ with a p-radical R and classical sections Γ_j = GL/Sp/O/U(X_j). Since the natural modules X_j occur in V, Σ dim X_j ≤ ℓ, so Σ (dim X_j)² ≤ ℓ·max dim X_j. All sections with dim X_j ≤ εℓ can be enumerated at total cost p^{εℓ²}. A section with dim X_j ≥ εℓ can act on H²(Q_i, F_p) (dimension O(ℓ²)) only through composition factors of degree ≤ 2 in X_j (degree 3 has dimension Θ(ℓ³)). Stabilising a **vector** in a degree-≤2 module is a tuple-of-forms problem (Principle Q); stabilising a **subspace** is a matrix-space problem (IMQSZ type). What is missing: the p-radical R (gauge) and non-split extensions (the cocycle). The program for N^{o(log N)} would be: subspace transporter for (R ⋊ big classical) on degree-≤2 modules.

Example: extraspecial Q₂ of rank ≥ 4 has no descendants with [L₂, V] ≠ 0 (Hall–Witt forces t₃ = 0). High symmetry of Q₂ restricts the descendants; whether this can be turned into a bound is open.

## 11. Log

* 2026-11-09. Notes T1–T4 and CRP written from one session's reasoning; nothing verified. Papers downloaded to the session scratchpad: Sun 2611.05920, Sun 2303.15412, Grochow–Qiao IV 2306.16317, IMQSZ (SZTAKI eprint), arXiv:2610.00874.
* 2026-11-09, later. §7 written from direct reading (scope stated there); §8–§10 added. Still nothing verified or red-teamed. A running journal of the session is in [groupiso-journal](groupiso-journal.md).

## Sources

* https://arxiv.org/abs/2611.05920
* https://arxiv.org/abs/2303.15412
* https://arxiv.org/abs/2306.16317
* https://arxiv.org/abs/2610.00874
* https://eprints.sztaki.hu/10827/
* https://arxiv.org/abs/1609.08253
* https://arxiv.org/abs/1304.3935
* https://arxiv.org/abs/1708.03495
* https://arxiv.org/abs/1907.00309
