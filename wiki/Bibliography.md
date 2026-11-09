# Bibliography

What the project relied on, and how each source was used. The BibTeX for the paper is [refs.bib](../paper/refs.bib). "Read" means an agent read the source, not that it is assessed for correctness.

[Home](Home.md)

## Read substantially (source or full text)

| Reference | What was read | Used for |
|---|---|---|
| Hajiaghayi, JafariRaviz, *Deterministic n^{O(log n)} Graph Isomorphism Algorithm via Inherited Decompositions*, arXiv:2611.01399v1 (2026) | LaTeX source and the Lean development, repeatedly | [HJ](Math-HJ-Algorithm.md), everything conditional |
| Grohe, Neuen, Schweitzer, *A faster isomorphism test for graphs of small degree*, FOCS 2018, arXiv:1802.04659 v1–v3 (SICOMP 52(6), 2023) | full arXiv v3 source; v1, v2 compared | canonization, exponent, R\* |
| Babai, *Canonical form for graphs in quasipolynomial time: preliminary report*, STOC 2019 | NSF copy, full text | Theorem A |
| Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547v2 | relevant source sections | throughout |
| Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*, arXiv:1710.04574 | full source | Theorem X, Theorem G, video |
| Neuen, *Hypergraph isomorphism for groups with restricted composition factors*, arXiv:2002.06997 v1, v2 (ICALP 2020 / TALG 2022) | whole paper (v2 source) | Theorem H |
| Wiebking, *A Decomposition-Compatible Canonization Framework for the Graph Isomorphism Problem*, RWTH 2021, DOI 10.18154/RWTH-2021-06242 | relevant chapters; obtained as described in [Disclosures](Disclosures.md) | Q 9.6, Lemma 5.34 |
| Wiebking, arXiv:1911.11257 (ICALP 2020) | source, in full for treewidth | TW |
| Schweitzer, Wiebking, arXiv:1806.07466 (STOC 2019) | source sections | Theorem L, framework |
| Grohe, Neuen, Schweitzer, Wiebking, arXiv:1803.06858 v1 | relevant files | TW |
| Grohe, Neuen, Wiebking, arXiv:2004.07671 | main proof | H4 |
| Neuen, arXiv:2011.14730 | main proof | H4 |
| Neuen, *Parameterized complexity of graph isomorphism testing*, Comput. Sci. Rev. 60 (2026) | full text | status of the field |
| Grohe, Neuen, *Recent advances on the graph isomorphism problem*, arXiv:2011.01366 | §4.4, open questions | Thm 4.16, obstruction |
| Babai, Luks, *Canonical labeling of graphs*, STOC 1983 | §4.2–4.3 (OCR from Luks's homepage) | Corollary B |
| Arvind, Das, Köbler, Toda, ECCC TR09-093 | full text | Prop 3.3, Theorem E |
| Codenotti, PhD thesis, Chicago 2011 | Ch. 4 (Thm 4.2.1) | Theorem P (known) |
| Luks, *Permutation groups and polynomial-time computation*, DIMACS 1993 | relevant parts | Prop L |
| Pago, arXiv:2302.05426 | Lemmas `G_groupInduction`, `G_fixingTheRestPointwise` | Lemma A credit |
| Grochow, Ivanyos, Qiao, Sun, arXiv:2610.00874 (unrefereed) | statements | w17 |
| Rosenbaum, arXiv:1304.3935 | §1, §2, §5–6 | w17 Theorem B |
| "The Exponential Time Hypothesis is False" (OpenAI math release, Oct 2026; unrefereed) | core sections, appendices partially | [w21-eth](../docs/w21-eth.md) |
| Anagnostopoulou-Merkouri, Bailey, Cameron, Forum Math. Sigma 2025 (arXiv:2409.10461) | full text | w8-poset |
| Neuen, Schweitzer, arXiv:1705.03283 and 1705.03686 | source and constructions | multipedes |
| Lichter, arXiv:2104.12999 | abstract, intro, CFI section | w4-t2 |

## Read in part, or only as restated by another source

| Reference | How |
|---|---|
| Babai, Cameron, Pálfy 1982 | paywalled; through GNS, Maróti's thesis, Burness–Shalev |
| Maróti, J. Algebra 2002 / doctoral thesis | thesis read; journal numbering not confirmed |
| Burness, Shalev, arXiv:2012.12818 | selected statements |
| Babai, Codenotti, Qiao, ICALP 2012 | via arXiv:2504.19777 and Codenotti's thesis |
| Luks, STOC 1999 | not obtained; via ADKT, Schweitzer–Wiebking, Neuen 2020 |
| Luks 1982; Babai–Kantor–Luks 1983; Babai–Luks–Seress 1987; Kantor–Luks 1990 | cited or as quoted by GNS |
| Sun STOC 2023 (arXiv:2303.15412); IMQSZ FOCS 2024; Grochow–Qiao; Dietrich–Wilson; Le Gall–Rosenbaum (arXiv:1609.08253) | abstracts or statements |
| Levet 2023; Gill 2025; Miller 1978–79 | as cited, some from memory |
| Liebeck–Shalev, Liebeck 1984, GSS98, Cooperstein, Kleidman–Liebeck, Pálfy, Wolf | through GNS |
| Matsen et al., Konvalinka–Wagner, Billey et al., Diaconis et al. (tanglegrams) | verified from sources by a search agent |
| Lokshtanov, Pilipczuk, Pilipczuk, Saurabh STOC 2022 (arXiv:2210.14638); Grohe 2010, 2017 | statements via red-team |
| Cardona et al., arXiv:0902.4640 | read through a fetch summary |
| Otachi–Schweitzer arXiv:1403.7238 | from downloaded text |
| Dixon, Mortimer, *Permutation Groups*; Seress | from memory for specific lemmas |

## Unread (blocked or not obtained)

* SICOMP 2023 text of GNS (403).
* Neuen's dissertation, RWTH 2019/2020 (bot wall, 503).
* TALG versions of Neuen 2020 and GNSW18.
* ScienceDirect originals (403).

See [Disclosures](Disclosures.md#literature-that-was-not-read). Items above may be incomplete where a memo uses a citation only in passing; each memo's own Sources section is authoritative for what that memo read.

## Repository memos as sources

| File | Topic |
|---|---|
| [moonshot-theory](../docs/moonshot-theory.md) | dissection of the bound |
| [hardness](../docs/hardness.md) | empirical growth |
| [overnight-log](../docs/overnight-log.md) | running log |
| [paper/cover-note](../paper/cover-note.md) | draft note to an expert |
