<!-- Draft for the user. Not sent. Fill in the recipient and signature. -->

**Subject:** Request to check a claimed answer to Question 9.6 (canonical labelings in n^polylog(d))

Dear [Name],

Would you be willing to look at the attached draft? It claims to answer Question 9.6 of Daniel Wiebking's dissertation.

**Claim.** For every G ≤ Sym(Ω) whose composition factors all embed in S_d, canonical labelings of strings under G, or under a coset of G, can be computed in time n^{O((log d)^c)}, where n = |Ω|. With a canonical Luks reduction following Babai–Luks (1983), this gives canonical forms of n-vertex graphs of maximum degree d in the same time. The one essentially pairwise step of GNS (the joint comparison classes in Lemma 6.6) is replaced by canonizing under the stabilizer of a reference tuple chosen from the group: Wiebking's canonical test set (dissertation, Lemma 5.34), used in a new role.

**Assumed.** The published GNS results (Thms 3.13, 4.3, 4.6, 5.8, 5.9, Lemma 6.2, Cor 6.5, Lemma 7.1), with all auxiliary constructions run deterministically on canonical generating sets. Also Babai's STOC 2019 canonical form, used only on d^{O(log d)} points.

**A question.** In the proof of GNS Lemma 7.2 (arXiv v3), the step H′_(𝒞′) ≤ ker φ′ seems to need the next block system to lie above 𝒞′. As written, any block system above 𝔅₁ may be chosen. For S_m ≀ S₂ in product action, the column system then gives k′ = k. Is "choose the next block system above 𝒞′" the intended reading? Is it addressed in the SICOMP version?

Canonical versions of Neuen's hypergraph test and of the treewidth algorithm are included, marked as sketches.

The work is unrefereed and was prepared with substantial AI assistance. I would be grateful for any comments, including that it is wrong or already known.

With thanks and best regards,
[Name]
