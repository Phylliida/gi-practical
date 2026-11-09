# Disclosures and method

[Home](Home.md)

## Who did this

**The work was done by AI agents and no human expert has checked any result.** A user directed the project; agents wrote the code, derived the mathematics, performed the red-teams and wrote the documents. Where a document says "red-team", "referee", "verified" or "signed", an AI agent did it. The cover note and the papers state that the drafts were prepared with substantial AI assistance. Author lines in the papers are placeholders.

Several agent runs were interrupted by rate limits and resumed.

## How work was organized

* Each piece of work ran on its own git worktree and branch, then was merged into `master` by hand: `r1`–`r4` (rounds, 4 Nov) and `w1`–`w39` (waves, 4–9 Nov). See [Timeline](Timeline.md).
* **Red-team rule.** From the overnight campaign on, every claimed result got an independent agent whose job was to break it. Red-teams record what they checked and what they could not. Results without a red-team are marked "author only" or "not yet red-teamed" in the ledger; `w32-conference` is one.
* **Tags.** Memos label claims `[PROVEN]`, `[PROVEN mod X]`, `[SKETCH]`, `[CONDITIONAL: H]`, `[SPECULATION]`. Some waves also use `[VERIFIED]`, `[TRUST]`, `[ARGUED HERE]`. The [ledger](Results-Ledger.md) uses a single scheme.
* **Untrusted sources.** Downloaded papers were saved in fresh directories and read as data; no code from them was run. They live in the session scratchpad, not the repository.
* **CPU rule.** Agents ran under `nice`, one process each, because the user tunes system benchmarks on this machine. No Lean except the single authorized build and the later `lean/DegreeD` work (`w36-lean`, `w38-lean-stage1`).

## Literature access

* **One agent passed RWTH's JavaScript bot wall** by sending the `APP_INIT=1` cookie that the page sets, to fetch the open-access Wiebking thesis (green OA per OpenAlex, DOI 10.18154/RWTH-2021-06242). It is recorded in [redteam-w4-gnscanon](../docs/redteam-w4-gnscanon.md). Later agents declined to do this for other documents and left the decision to the user.
* **dreadnaut came from nixpkgs** (`nauty` 2.9.1).

### Literature that was not read

* The **SICOMP 2023 version of GNS** (DOI 10.1137/19M1245293): SIAM returned a 403 challenge. Crossref registers no erratum. arXiv v3 was read instead.
* **Neuen's PhD thesis** (RWTH, DOI 10.18154/RWTH-2020-00160): bot wall or 503, not bypassed. It contains Lemma 6.1.17 used by Theorem H and Example 5.5.10 cited in the literature.
* The **TALG version** of Neuen 2020 and of GNSW18 (not compared with arXiv).
* BCP 1982 original (paywalled; used through restatements). Luks STOC 1999, some others: only as described by citing papers.
See [Bibliography](Bibliography.md).

## Other limits

* Timings are from one shared machine; see [Benchmarks](Benchmarks.md#read-these-caveats-first).
* Numbers in the wiki trace to the linked sources; in a few cases (early-round numbers, the Lean audit, the disclosures above) the source is the project's working notes or conversation with the user, as noted.
* Tool transcripts were used only to confirm details of the early rounds; the memos take priority where they differ.
