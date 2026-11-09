# Glossary of notation

[Home](Home.md)

## Symbols

| Symbol | Meaning | Notes |
|---|---|---|
| n, N | number of vertices of a graph; number of positions (domain size) of a string instance | for GI through pairs, N = n²; in GNS-exponent memos n is a domain size |
| Ω | domain (positions) of a string instance | |
| Γ | the ideal domain of labels in HJ and in GNS's giant representation; also a group in Neuen's notation (Γ ∈ Γ̂_d) | depends on the memo |
| **Γ_d** | the Babai–Cameron–Pálfy class that Luks-style recursions use; larger than Γ̂_d, and contains AGL(d,p) (GNS Rem. 3.14) | see the sources for its exact definition |
| **Γ̂_d** | groups all of whose composition factors embed in S_d; composition width at most d | closed under subgroups, quotients, extensions |
| Sym(Ω), Alt(Ω) | full symmetric and alternating groups | S_n, A_n |
| Iso_G(x, y), Aut_G(x) | isomorphisms, automorphisms of strings under G | coset or empty |
| **κ** | HJ's test-set size (64) | the solver uses κ = 3 by default |
| **t** | test-set size in Babai/GNS: t = max(9, 3 + log₂ d) in GNS; in BC about 2 log₂ n | also a Johnson parameter (k-sets), see below |
| q | label-set size of a giant, or the size of a finite field | context |
| **k** | degree of GNS's giant representation; also a Johnson set size; also dim in AGL(k,2); also the clique parameter; also treewidth | **k means different things**; see collisions |
| **d** | maximum degree of a graph, or class parameter of Γ̂_d; in HJ, d′ or d_i is a hierarchy ratio or quotient degree | **d is overloaded**, check the memo |
| D | in w1-fpt, the odd degree parameter D = d + 1; in HJ, the exponent in W = (s+2)^D e^Φ | |
| b | node degree of a tree group; also a block size | |
| s | current domain size of a call | |
| **σ** | HJ's hereditary budget; also a permutation (an isomorphism) | **σ is overloaded** |
| **ρ** | HJ's hierarchy rank; also a label permutation or a homomorphism | **ρ is overloaded**; in GNS-type work ρ is a coset representative |
| **Q** | HJ's cap moment Σ log d_i log max(c_i, 2); also a quotient group in w1-structure and Goursat data Q_i | |
| Q_d | Q with caps initialized at min(d_i, d) | |
| **Λ** | canonical labelling coset (Λ_H(x)) in canonization memos; **also** the logarithmic multiplier in Φ_Λ (= log 8d̃) | **two unrelated meanings** |
| Φ, W | HJ's potential and weight | Φ = A(x² + ρx + σx + Q) + Bh, x = log(s+2), W = (s+2)^D e^Φ |
| Φ_Λ | Theorem R\*'s potential A(Λx + Λρ + Λσ + Q_d) + Bh | |
| **μ** | order exponent log\|P\|/log d′ of a primitive P; in w8-poset, a poset parameter | **μ is overloaded** |
| λ | largest classical section dimension; also N^α in HJ; also a Young parameter in w8-poset | |
| τ | largest Goursat quotient of the instance's row strips (Prop T) | |
| ε, ε_B | entanglement index | |
| δ_B | non-abelian descent number, or coupling depth | |
| ν | non-solvable depth (w6 Prop L) | |
| w | alternating width; or a group element | |
| L | log₂(d+2) in exponent memos; number of levels in Theorem L | |
| x (exponent memos) | log n = L^x | not HJ's x = log(s+2) |
| c | exponent in n^{O(log^c d)} | |
| option 1, option 2 | the two cases of GNS Theorem 3.13 (order bound; structured socle) | |
| H0 | assumption that HJ is correct as written | |
| H1, H2 | recognition and call grouping (both discharged) | |
| (M), (M′) | dispatcher modification; structural rule | |
| TreeCI, TreeSI, PCI, T², T²_full | see [Core problem](Math-Core-Problem.md#definitions) | |
| R1, R1_c, R2 | tanglegram isomorphism; complete-tree version; definability | not to be confused with Theorems R, R\* |
| HCGI, FullCI, Def-CI, HS(b,r) | graph-side equivalents | [w4-t2](../docs/w4-t2.md) |
| CF, CP | canonical form, canonical placement | |
| BC, BL83, GNS, HBD, B–H | Babai 2019, Babai–Luks 1983, Grohe–Neuen–Schweitzer, Helfgott–Bajpai–Dona, Babai with Helfgott's analysis | see [Bibliography](Bibliography.md) |
| WL, CR, IR, SI, CI | Weisfeiler–Leman, colour refinement, individualization-refinement, string isomorphism, coset intersection | |
| CLIQUE-LB | k-Clique has no f(k)n^{o(k)} algorithm | |

## Names that are reused

Memo names disambiguate; the [ledger](Results-Ledger.md) gives the memo for each row.

| Name | Meanings |
|---|---|
| Theorem A | canonical strings under Γ̂_d (canonization); T²_full equivalences (w4-t2); AGL canonical form (w17) |
| Theorem B / Corollary B | canonical graphs (Corollary B); WL lower bound on tanglegrams (w4-t2, Theorem B); bidirectional AGL (w17, Theorem B) |
| Theorem C | HJ-canon (w3); GNS main recursion (w8); tensor reduction (w17) |
| Theorem D, Prop D | Corollary D (labelling cosets); Prop D diagonal shape (w4-t2); Prop D prime decomposition (w6); Prop D random bound (w17) |
| Theorem E | bounded entanglement (w1-fpt); weak hereditary budget (w8); Prop E vectorial quadratics (w17) |
| Theorem G | no t-ary black box (w12); Prop G Sylow (w17) |
| Theorem H | canonical Neuen (w8); frontier hybrid (w3); Prop H width-2 (w8-poset) |
| Theorem L | level-synchronised towers (w1-structure); Prop L one-sided polynomial (w6) |
| Lemma A | composition factors (w8); Lemma S canonical subcoset (w4) |
| Prop A′, A″ | w4-t2 |
| Prop B | multiplicative giant (w8-gnsexp); recognition of coordinate structure (w8-poset); Prop B′ oracle bound (w17) |
| Prop C | coordinate tanglegrams (w6), known prior work |
| Prop S | sign group definability (w4-t2); straddling (w6) |
| Theorem P, P-canon | product actions (w2), its canonical version (w3) |
| Theorem R, R\*, R\*\* | degree-d conditional bounds; not the same as R1 |
| Theorem A1, A2, B1 | w18: quasigroups (A1, A2); HJ on PG incidence graphs (B1); not Theorems A, B |
| Theorem X | black box (w10) |
| "Theorem 1" | exponents (w8-gnsexp); poset DP (w8-poset) |
| Example X, X′ | Cayley-coupled towers (w1-structure, w2-coset) |
| E1–E6 | experiments in several memos; **E** rows of the redteam-theoremg report are edits |

## Terms in English

* **Giant**: a large alternating-group quotient (or a representation onto one).
* **Johnson action**: Sym(m) on t-subsets.
* **Cameron group**: product of Johnson-type groups in product action; **GNS option 2** is the structural condition used in Theorem R\*.
* **Primitive quotient**: a quotient of a transitive group acting on blocks with no nontrivial block system.
* **Local certificate**: Babai's test of whether a small set of labels can be symmetric under a window.
* **Reference tuple**: Lemma T's group-chosen ordered tuple.
* **First rectangle**: HJ's replacement for Split-or-Johnson.
* **Twisting**: non-trivial Goursat coupling between rows and columns.
* **Multipede**: Gurevich–Shelah-type graphs; used by Neuen–Schweitzer as hard IR instances.
