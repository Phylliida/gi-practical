# Overnight campaign: improving n^{O(log d)} (started 2026-11-04)

Goal set by the user: push the conditional n^{O(log d)} bound for graph isomorphism of maximum degree d
(Theorem R*, see verify-theorem-R.md and redteam-theorem-R.md) further, ideally toward polynomial,
with 2-3 agents at a time. Framing: polynomial for all d would put GI in P; f(d)·poly(n) (FPT in the
degree) is a recognized open problem. Every claim is labeled proven / sketched / speculative, and
claimed results get an independent red-team pass.

## Wave 1
* w1-fpt: source of the log d factor; amortization attempts; lower bounds for the algorithm class.
* w1-structure: replace enumeration of non-Cameron primitive quotients (affine groups etc.) by
  structure; polynomial time for d = O(log n)?
* w1-scale: bounded-degree pipeline at n in the thousands; instances hard for nauty.

### w1-fpt (done, commit 4eb2ccc; docs/w1-fpt.md)
* Literature: FPT by maximum degree is open (Downey–Fellows; GNS; Grohe–Neuen 2021 Q4; Neuen 2026 survey
  "wide open", Q4.8). No W-hardness known; known lower bounds (CFI/WL, Neuen–Schweitzer for IR, proof
  systems) do not apply to group-theoretic recursion.
* [PROVEN, pending red-team] Barrier: on string isomorphism under G = (F_2^d ⋊ S_{d+1}) wr C_m (primitive,
  in Γ̂_{d+1}), HJ+(M') enumerates ≥ |G| ≥ N^{log2(d+1) − 0.443} cosets. So R*'s exponent is tight for the
  algorithm; FPT needs a different algorithm, not a better analysis. (Not claimed for graphs.)
* [PROVEN, pending red-team] That family is FPT by a DP over coordinate prefixes with ADKT coset
  intersection. Memoization over O(N^2) block-pair subinstances makes giant branching additive; the
  difficulty concentrates in kernel-coset ∩ product-of-child-cosets. Theorem E: if primitive components
  have order ≤ π0 and every kernel has entanglement index ≤ ε, string isomorphism is π0·ε·poly(N).
  Prop 4.2: for tree groups, string isomorphism is FPT iff coset intersection is FPT.
* Leads: coset intersection for tree groups (test family T_{b,h}^L); prefix-DP for product-action
  quotients in the dispatcher; measure the entanglement index on real Luks towers; does the barrier
  transfer to graphs?
