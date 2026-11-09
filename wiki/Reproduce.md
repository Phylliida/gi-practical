# How to reproduce

Exact commands for everything the project ran. Paths assume the repository root. Be careful on this machine: the disk under `/home/bepis/math` had under 10 GB free when this was written.

[Home](Home.md) · [Software](Software.md) · [Benchmarks](Benchmarks.md)

## Setup

* Python 3.12 with `pytest`, `sympy`, `networkx`. Only the standard library is needed by the solver. numpy is not used.
* For `pynauty`, use a project-local virtualenv: `python3 -m venv .venv && .venv/bin/pip install pynauty networkx sympy` (or the existing one at `../r2-hybrid/.venv/`).
* Run long benchmarks under `nice -n 19`, one process at a time. The machine is shared.

## Tests

```sh
python3 -m pytest -q tests                  # with the kernel if it is built
GI_NO_CKERNEL=1 python3 -m pytest -q tests  # pure Python; extra skips
GI_REQUIRE_CKERNEL=1 python3 -m pytest -q tests/test_ckernel.py
```

At `b1a2d03`, 1039 tests are collected. Tests compare against brute force on small graphs, VF2 and known orders, in both kernel modes.

## The compiled kernel

```sh
python3 build_ckernel.py            # needs only gcc on PATH (or $CC); writes gi/_ckernel*.so
python3 build_ckernel.py --asan     # sanitizer build, see the docstring
python3 build_ckernel.py --clean    # remove it
GI_NO_CKERNEL=1 python3 ...         # run without it
```

If `gcc` is not on PATH: `nix shell nixpkgs#gcc -c python3 build_ckernel.py`. Headers come from the interpreter running the script, not from `python3-config` on PATH. Details: [w16-ckernel](../docs/w16-ckernel.md).

## Benchmarks

```sh
python3 bench/run.py --tiers tiny,small --timeout 60 --label NAME
python3 bench/run.py --tiers large,xl --only "J(8,3)|PG(2,5)"     # names may contain commas
python3 bench/run.py --tiers medium --timeout 120 --label NAME --solver-args '{"certificates": false}'
python3 bench/run.py --tiers large --graph-args '{"ir": 0}'       # the recursion alone
```

Other runners (see each memo's "Reproduce" section):

| Script | Purpose | Memo |
|---|---|---|
| [bench/run.py](../bench/run.py) | correctness-checked tiers | [README](../README.md) |
| [bench/irhard.py](../bench/irhard.py) | Neuen–Schweitzer multipedes, CFI, Miyazaki, audit, node counts | [w1-scale](../docs/w1-scale.md) §6 |
| [bench/canon.py](../bench/canon.py) | canonical-labeling benchmark against pynauty and dreadnaut | [w9-canontool](../docs/w9-canontool.md) §5 |
| [bench/bounded.py](../bench/bounded.py) | Luks pipeline against `graph_iso` and nauty | [bounded-degree](../docs/bounded-degree.md) |
| [bench/hardness.py](../bench/hardness.py) | growth tables and fits; `list`, `run`, `table`, `fit` | [hardness](../docs/hardness.md) |
| [bench/ckernel.py](../bench/ckernel.py) | paired kernel on/off timings | [w16-ckernel](../docs/w16-ckernel.md) |
| [bench/reference.py](../bench/reference.py), [bench/nauty_check.py](../bench/nauty_check.py) | VF2 and pynauty reference; cross-check of `graph_iso` | [README](../README.md) |

Example, the multipede headline:

```sh
PY=../r2-hybrid/.venv/bin/python
nice $PY bench/irhard.py run --family ns --sizes 16,32,48,64,80,96,112,128,144 --modes new,dnd,dns,dnt --timeout 600 --label w1-ns
$PY bench/irhard.py table --label w1-ns
nice $PY bench/irhard.py audit --size 112
```

`bench/run.py` writes `bench/results/NAME.json`. Avoid overwriting committed results; use a fresh `--label`.

## nauty and Traces (dreadnaut)

nauty 2.9.1 from nixpkgs (`nix shell nixpkgs#nauty`). `bench/irhard.py` finds the binary from the `DREADNAUT` environment variable, then PATH, then the Nix store. The runs in the project used dreadnaut in modes dense `Ad`, sparse `As`, Traces `At`, with canonical labeling on for canonical-form comparisons.
Check disk before fetching anything through Nix. pynauty is 2.8.8.1 in the r2-hybrid venv.

## The Lean build and comparator

**Do not run this casually.** It takes about 14 GB of disk and an hour or more of CPU, and the project's rule on this machine is never to run Lean unless asked. The project has already done this; see [Lean audit](Lean-Audit.md).

```sh
cd ~/math/GraphIsomorphismLog2
nix shell nixpkgs#elan   # provides elan; install leanprover/lean4:v4.30.0-rc2
lake exe cache get       # about 76 s
lake build               # 44.5 min here
```

To check the axioms: `#print axioms main_theorem` (via a small Lean file importing the build). Expect `propext`, `Classical.choice`, `Quot.sound` and the 10 `GI.Axioms.*` listed on the [Lean audit](Lean-Audit.md) page.

**Comparator** (`comparator.json` in the repository sets it up): build comparator and lean4export from their `v4.30.0-rc2` tags and landrun from commit `5ed4a3d`, then `lake env /path/to/comparator comparator.json`. **On NixOS**, comparator needs `--rox /nix/store` added to its landrun arguments, so the toolchain wrappers can execute. Kernel replay took 46 min 22 s.

## The paper PDFs

`pdflatex` is not on PATH. Build through Nix:

```sh
cd paper
nix shell nixpkgs#texlive.combined.scheme-medium -c bash -c \
  'pdflatex -interaction=nonstopmode canon && bibtex canon && pdflatex -interaction=nonstopmode canon && pdflatex -interaction=nonstopmode canon'
```

Likewise for `exponent`. `paper/canon.pdf` was last built in `d6db110` and `paper/exponent.pdf` in `9cd1433`. Both are current with their `.tex` at master `b1a2d03`. Texlive is a large download; check `df -h` first.

## The video

*The Third Logarithm* is plain HTML, CSS and JavaScript and runs offline: open [video/index.html](../video/index.html) in a browser (`file://` works). It has chapters, captions, and optional speech.

* Data shown on screen is generated: `python3 video/tools/gen_data.py` writes `video/js/data.js` from the repository's `gi` package.
* Headless checks use Firefox over Marionette: `video/tools/shoot.py` and `video/tools/ui_test.py`. Paths in `ui_test.py` assume the original worktree; adjust before running.
* Claims and their sources: [CLAIMS.md](../video/CLAIMS.md). Script and teaching notes: [STORYBOARD.md](../video/STORYBOARD.md), [TEACHING-NOTES.md](../video/TEACHING-NOTES.md).

**In progress:** branch `w24-video-review` at commit `08fd28a` (no `REVIEW.md` yet) is an independent fact-check of the script. Until it lands, treat the video as unreviewed by a second reader. Spoken narration was toggled in testing but never listened to.

## Check scripts

Several memos have an executable check, listed here with what each exercises. Each is standard library or sympy unless noted, runs in seconds to a few minutes (the affine check about 15 minutes), and is run from the repository root with `nice python3 -I`.

| Script | Exercises |
|---|---|
| [redteam-gns-lemma72-check.py](../docs/redteam-gns-lemma72-check.py) | the GNS Lemma 7.2 example for small m (sympy) |
| [redteam-canonization-writeup-check.py](../docs/redteam-canonization-writeup-check.py) | §8 canonical Luks reduction by brute force; §7.3 arithmetic |
| [redteam-w8-gnsexp-check.py](../docs/redteam-w8-gnsexp-check.py) | Bochert and Praeger–Saxl tables for Lemma A, exponent arithmetic |
| [redteam-w8-hypercanon-check.py](../docs/redteam-w8-hypercanon-check.py) | toy Theorem H canonicity, mutants |
| [redteam-canhyp-check.py](../docs/redteam-canhyp-check.py) | CanHyp-lite on small groups, mutants, §2.1 counterexample |
| [verify-neu417-check.py](../docs/verify-neu417-check.py) | Thm 4.17(G) counterexample |
| [w10-blackbox-check.py](../docs/w10-blackbox-check.py), [redteam-w10-blackbox-check.py](../docs/redteam-w10-blackbox-check.py) | exponent arithmetic, Prop 1.3 instance |
| [w12-theoremg-check.py](../docs/w12-theoremg-check.py), [redteam-theoremg-check.py](../docs/redteam-theoremg-check.py) | Theorem G combinatorics, recurrence |
| [redteam-w17-affine-check.py](../docs/redteam-w17-affine-check.py) | Theorem A, B, C on small k |

The directories [docs/w8-poset-code](../docs/w8-poset-code/), [docs/w17-affine-code](../docs/w17-affine-code/), [docs/w21-eth-code](../docs/w21-eth-code/) hold experiment code.
