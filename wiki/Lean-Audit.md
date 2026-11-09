# The Lean audit of HJ

Formalization: `~/math/GraphIsomorphismLog2`, Lean v4.30.0-rc2, mathlib 2f9133a, about 420k lines in 2233 files.
Audited by AI agents; **no human has checked the result**. Most facts on this page come from the audit itself, recorded in the project's working notes and the
[overnight log](../docs/overnight-log.md), and not in a repository memo. Steps to redo it are on [Reproduce](Reproduce.md#the-lean-build-and-comparator).

[Home](Home.md) · Related: [HJ algorithm](Math-HJ-Algorithm.md)

## The result

On 5 Nov 2026:

* Toolchain obtained through `nix shell nixpkgs#elan`; `lake exe cache get` then `lake build` exited 0 in 44.5 min (mathlib cache download 76 s; about 14 GB of disk).
* `#print axioms main_theorem` lists exactly the 3 standard axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the 10 literature axioms below. No `sorryAx`, no `ofReduceBool`.
* Dependency cone of `main_theorem`: 115,555 constants, including `GI.Paper.thm_hereditary_budget` (HJ Theorem A.9).
* Comparator accepted: `Solution.lean` proves exactly `Challenge.lean`'s statement, built in a landrun sandbox, exported with lean4export, and replayed in a
  fresh kernel in 46 min 22 s ("Lean default kernel accepts the solution").
* One local deviation: `--rox /nix/store` was added to comparator's landrun arguments so the NixOS toolchain wrappers can execute. Writes stay confined to `.lake`.

Comparator and lean4export were at v4.30.0-rc2, landrun at commit 5ed4a3d.

## What is trusted

The trusted base is 17 files, about 1350 lines: `Statement/Machine.lean`, `Statement/Main.lean`, `Cited/*`, `Axioms/*`. All were read by hand (by an agent).
A grep found no `sorry`, `native_decide` or unsafe construct outside `Challenge.lean`.

**The statement.** There is one program p and one real constant C such that for all n and all graphs G, H on Fin n, the run on the adjacency-matrix memory halts
with a correct output (yes/no; on yes, an isomorphism and generators of Aut(G)) at cost ≤ exp(C·log(n+2)²).

**The machine.** A log-cost RAM with procedures: each operation costs one plus the bit lengths of the numbers involved. Multiplication is at linear bit cost,
which stays polynomially equivalent to Turing machines.

**The 10 axioms** (all CFSG-era). Each was compared with its source and looked correct as stated, including edge cases. Input encodings keep every number ≤ n, so no task is secretly impossible.

| Axiom | Content |
|---|---|
| `transitiveAffected` | Babai's affected-points lemma |
| `marotiPrimitive` | Maróti's bound on orders of primitive groups, for degree n ≥ 25 |
| `sixTransitiveContainsAlt` | 6-transitive implies containing Alt(n) |
| `gmpOutBound`, `gmpTransitiveNonabelian` | two Guralnick–Maróti–Pyber bounds |
| `simpleValuationDegree` | a bound on the 3-adic or 5-adic valuation of a simple group's automorphism group |
| `chiefSeriesAlgo`, `quotientCentralizer`, `sylowAlgo`, `sylowConjugate` | polynomial-time algorithms: chief series, centralizers in quotients, Kantor's Sylow and conjugation |

Six are structural and four algorithmic. A false algorithmic axiom would let the proof derive anything, which is why the encodings were checked.

## What is not established by this

* Whether the Lean model matches the paper's informal argument.
* HJ's string-isomorphism theorem (Theorem 1.2) at machine level: the Lean states only GI. `GI.Paper.thm_main_string_stage1` covers an abstract recursion with hypotheses `Supply`, `NodeBound`, `RootsOK`, which only the graph pair state discharges ([w10-blackbox](../docs/w10-blackbox.md) §2.1).
* The project's own Theorem R\* and its Λ accounting: not machine-checked ([redteam-theorem-R](../docs/redteam-theorem-R.md) §9(e)).
* The theorems behind the 10 axioms: each statement was compared with its source by reading, but the sources' proofs were not re-derived.

Stale docstrings exist in the Lean, which said parts were not formalized. The final proof supersedes them; see [Corrections](Corrections.md#status-of-the-lean-formalization).

## The constant C

Traced by reading only. C is non-explicit: it depends on the unnamed constant of `simpleValuationDegree`, the exponents of 21 polynomial-time primitives chosen by `Classical.choose`,
`cc₀` parameters, and a sum of worst-case costs over all n below about 4²⁰. The explicit parts force C ≳ 4·10¹⁴, realistically ≳ 10¹⁶.

**Do not confuse this with the video's 2.5×10⁶.** [video/CLAIMS.md](../video/CLAIMS.md) lists a root exponent "≥ 2.5×10⁶ log² N": a lower bound on the constants the *paper's potential* needs, computed from a ≈ 2453, A ≈ 19,152, C ≥ 128.
It is not the constant of the Lean theorem.

Paper parameters are on the [HJ page](Math-HJ-Algorithm.md#3-the-running-time-analysis).

## Disclosure

The audit and build were carried out by AI agents; several runs were interrupted by rate limits and resumed. See [Disclosures](Disclosures.md).
