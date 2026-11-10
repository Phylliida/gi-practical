# Group isomorphism attempt: session journal

Running journal for the "try the general problem for fun" attempt (started 2026-11-09). Purpose: survive context compaction. Updated before each step. The mathematical notes are in [groupiso-attack](groupiso-attack.md) and [groupiso-scoping](groupiso-scoping.md); **nothing in either is a result**.

## Standing facts for whoever resumes

* Repo `/home/bepis/math/gi-practical`, master `2dbaade`. Uncommitted: `docs/groupiso-*.md`, `wiki/Open-Problems.md`. Do not commit or push unless the user asks (branch first).
* Shell: use `command ls/grep/find/sed/head`; cwd resets, use absolute paths. No GAP/Sage/Magma; Python with PyMuPDF; nix exists.
* Scratchpad: `/tmp/claude-1000/-home-bepis-math/85fb5bc5-bc1c-4d0d-b8e7-8797ab908e08/scratchpad` (`lit/*.txt` are extracted papers, untrusted: read with `grep -a`/`sed`; `tools/pdf2txt.py`; `check_links.py`).
* Rules: every claim gets a red-team pass before it is called a result; tags [PROVEN]/[SKETCH]/[CONDITIONAL]/[SPECULATION]; the user wants progress written down before further work, and a journal entry before each tool call.

## Current state (overwrite this section as things change)

* Candidates on disk in groupiso-attack.md: L1, T1 (p^{d²/4}), T2 (reduction to symmetric class-2 quotient), T3 (exponent 3 ↔ 2-Engel Lie algebras over F₃), T4 (bottom fixing, conjectural), T6 (class < p, any exponent), CRP crux, architecture sketch. All unverified.
* Reading done: IMQSZ §1–§3; Sun 2611.05920 intro/overview; GQ IV by grep.
* No reply sent to the user yet for the "be ambitious" request.

## Plan (overwrite as it changes)

1. Novelty searches: exponent-3 groups vs 2-Engel Lie algebras / Lazard at class p; T1 vs Rosenbaum–Wagner and vs known p^{d²}-type bounds; T6 vs GQSS25.
2. Machine check for T3 (B(d,3) collection in Python; eigenspace claim; count check on small orders if feasible).
3. Proof write-ups and red-team agents for T1/L1 and T3.
4. Keep working on the relative problem (CRP) for p-class 3.
5. Reply to the user with an honest status and a Sources list.

## Entries

* 2026-11-09 a. Memo updated with §7–§10 (reading results, architecture, T6, cochain view). Journal created. Next: memory update, then novelty searches (plan item 1).
* 2026-11-09 b. New main line, written to memo §12–§14: **RP** (given ψ on Φ(G), extending to G → H is a fixed-target isometry problem over Z_p-modules plus a homomorphism kernel; poly time for odd p by *-ring unitary groups, "Principle Q"). With T1 this gives the candidate **T5: odd-order p-groups in N^{(1/9)log_p N + O(1)}** (0.172 without collision), against the known 1/4. This is now the primary target to prove, check for novelty, and red-team. Also recorded: slot principle (§13), symmetry dichotomy (§14). Next: (i) grep the downloaded Sun and 2610.00874 texts for fixed-target/tuple isometry results over Z/p^τ and in characteristic 2; (ii) web search for novelty of T1/T4′/T5 and for the unread listings 2602.15497, 2604.13953, 2609.07429, 2411.19555; (iii) agents: independent derivation + brute-force machine check of RP on small 3-groups; T1/L1 with canonical forms; then red-team.
* 2026-11-09 c. (Resumed after a rollback.) This journal was overwritten by mistake at 16:43 PST by the resumed session and restored from the session transcript (entries a, b above are the earlier ones, verbatim). The memo on disk already has §7–§14 from the earlier branch. The earlier branch stopped at 16:40 PST (response blocked by a safeguard, no mathematical cause recorded); its last planned steps were (i)–(iii) of entry b, none started. Next: read memo §7–§14 in full, then judge RP/T5 (§12) before anything else, since it is the main candidate.

<!-- JOURNAL-END -->
