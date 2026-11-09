# w42-lean-supply: `Supply` for all `d`, and Luks's reduction in Lean

Branch `w42-lean-supply`. New Lean under `lean/DegreeD/Luks/` and `lean/DegreeD/M/{Supply,NodeBoundOne}.lean`
(imports the built development at `~/math/GraphIsomorphismLog2`, not modified). Continues
`docs/w38-lean-stage1.md` and closes items 3 and 4 of `docs/redteam-lean-stage1.md`.

**Status.** Both items are closed at the abstract level, no `sorry`:

* `Supply P D` is built for all `D ≥ 6` from HJ's own giant-step data; runs of `M.Run` exist for every `d`
  (modulo the cited results HJ already takes). The red-team's `cls` lemma is proved: an aggregation
  round's only fresh `Solve` query is `cfgQuery` on `Sym(C)`, `|C| ≤ q`.
* Luks's reduction is formalized: a graph of maximum degree `d` yields, layer by layer from a fixed edge,
  a script of `Solve` calls whose groups are in `Γ̂_d` on at most `3 n⁴` positions, with an exact correspondence between each
  layer's answer and the isomorphisms of the next ball. The theorem (`graphIso_final`) covers
  all graphs on `Fin n` (components included), with `C` absolute and total weight
  `exp(C log(d+2) log(n+2))`. Axioms: the three standard ones and `bcp`, `gnsPrimitive` (the two already in
  `M/Axioms.lean`). No new axiom or cited result was added.

**Three things to read before citing this.**
1. The theorem is about an `M.Exec` of an abstract `Script` of calls. There is no program; the bound is on `Σ_nodes w`. It says nothing
   about the bookkeeping cost of the script between calls (reading the cosets, building the
   instances), which a program pays polynomially per layer.
2. `graphIso_general` takes the Stage-1 conclusion for any weight `w`; `graphIso_final` is the `w ≡ 1`
   (node-count) instance, with HJ's cited results as hypotheses (the six listed below).
3. The groups are in `Γ̂_d`, not `Γ̂_{d−1}` (end of §2). This costs a constant factor only.

## 1. `Supply` for all `D` (`M/Supply.lean`, 293 lines)

* `Aggregation.calls_class (I : Aggregation P S L) (hq : L.q ≤ D) :
  I.script.CallsExact fun {_ _} m T => m = .solve → GammaHat D T.G`. The certificate and comparison phases are
  `.cont` (`certPhase_cont`, `comparePhase_cont`). The items of `plan`: `caseOneItem` (overcoset), `halvingItem`
  (`.cont` calls), and `cfg`/`cfgOutItem`: `objItem` (overcoset), `cfgItem` (the fresh `pairState` call on
  `Sym(C)`, `C ⊆ [q]`, in `Γ̂_D` by `pairState_class` since `|C| ≤ q ≤ D`), `sojItem`/`rectItem` (queries of
  `RectOracle.ofReps`, all `.cont`, `ofReps_cont`).
* `Supply.ofGiant (hP) (hγ) (Gs : GiantSupply P) (hD : 6 ≤ D) : Supply P D`. The giant field is HJ's
  `GiantSupply`, with `cls` from `calls_class` and `q ≤ D` from `labels_q_le` (`q ≤ max D 6 = D`).
* `degreeD_stage1_of_giant`, `degreeD_stage1_cited`: the conclusion of `degreeD_stage1_full` for `∀ d`, with
  `Su` discharged. `degreeD_stage1_cited` takes HJ's cited results (`TransitiveAffected`, `KaryCoherentRefinement`,
  `SixTransitiveContainsAlt`, `DesignLemma`, `AutCardLeSq`, `SimpleValuationDegree`) and the parameter conditions.
* `params_full (hcite) (c₁ c₂)`: there are `P, cc` satisfying every numeric hypothesis of `degreeD_stage1` (for the given GNS constants),
  `Params.Aggregates`, `Params.RowThreshold` (from the cited `TransitiveAffected`), with `P.a = cc.a − 1`, `198 ≤ cc.a`.
  (`params_exist_ge` in `ParamsExample.lean`: `params_exist` with `N₀` above any given value, and the values of `α, γ, κ, θ, β, q₀`, `P.a`.)
* `M/NodeBoundOne.lean` (92 lines): `nodeBoundD_one (ha : 5 ≤ P.a) : NodeBoundD (fun _ => 1) 0 P.a` (the red-team's
  scratch check, kept).

## 2. Luks's reduction (`lean/DegreeD/Luks/`, 2524 lines)

| file | lines | content |
|---|---|---|
| `Wreath.lean` | 234 | `Om V q = V ⊔ (V×[q]) ⊔ (V×[q])²`, `act a s`, `wreath A`, `gammaHat_wreath`, `gammaHat_piDep` |
| `Step.lean` | 986 | `LG` (graph with levels and slots), `IsIso`, `LG.aut`, `layerState`, `extf`, `extf_isIso`, `extf_surj`, `readStep`, `LG.gammaHat_aut` |
| `Reduction.lean` | 221 | `layersScript`, `rootedScript`, `exec_of_calls`, `exec_total_le` |
| `Graph.lean` | 393 | `edgeLvl`, `mkLG`, `rooted_iff`, `connScript` |
| `Final.lean` | 285 | `Stage1Conclusion`, `graphIso_connected`, `graphIso_connected_final`, numerics |
| `Components.lean` | 405 | `anyScript`, `graphScript`, `iso_iff_restr`, `graphIso_general`, `graphIso_final` |

**One layer.** `LG V q` bundles a graph, levels `lvl` (adjacent vertices differ by at most one level, every
vertex above level 0 has a neighbour one level below) and slots `nb : V → Fin q → Option V` of the down-neighbours.
`IsIso X Y f₀ r f`: `f` restricted to `{lvl ≤ r}` is a level-preserving isomorphism `X_r → Y_r` agreeing with
`f₀` at level 0 (values outside the ball are irrelevant). `X.aut r ≤ Perm V`: automorphisms of `X_r` as permutations
fixing everything outside the ball.

The instance at level `r` from data `(A, τ)` is `layerState X Y A τ r`, the group `wreath A = S_q ≀_V A`
on `Om V q`, strings `str X X id r` and `str X Y τ r` (occupancy of the slots at level `r`, and for pairs of slots the
value `equal/adjacent/other` of their occupants). Then:

* `extf_isIso`: every `h = act a s` in the answer (`a ∈ aut r`, `τ ∈ Iso r`) induces, by `extf` (on the ball `τ ∘ a`,
  on level `r+1` the occupant of the image of a chosen up-slot), an isomorphism of the next ball;
* `extf_surj`: every isomorphism of the next ball arises this way (from `exists_slotPerm`, padding the
  slot permutations).
* `readStep_none/some`: the next data `(A', τ')` read off the answer (an element `h₀` gives `τ'`; `A'` is generated by the
  `b` fixing the outside with `extf g = τ' ∘ b` on the ball for some `g` in the answer) satisfies `A' = aut (r+1)` and `τ' ∈ Iso (r+1)`; an empty answer means no
  isomorphism.
* `gammaHat_wreath`, `LG.gammaHat_aut` (Luks): `S_q ≀_V A` and `Aut(X_r)` are in `Γ̂_q` (kernel into the product of
  symmetric groups on down-neighbour sets, restriction to the smaller ball).

**The script.** `layersScript X Y f r A τ` is a `Script` (HJ's script language, asks `Solve` and continues on the answer),
`rootedScript` runs it from `(⊥, f₀)` and returns the set of `f`. `rootedScript_spec`: if `f₀` is an iso of level 0 and all levels
are at most `R`, the script's exact value is `{f | IsIso X Y f₀ R f}`, its calls are `CallOK q`: `Solve`, finite, `Γ̂_q`, on `|Om V q|` positions, at most `R` calls.
`connScript` loops over the ordered pairs `(u', v')` of `Y` with `Y.Adj u' v'`; `connScript_spec`: value is the isomorphism set of `X, Y`.

**Graphs.** `edgeLvl G u v w = min (dist u w) (dist v w)`, `mkLG G hG u v q hd`, for `G` connected (slots from the degree bound). `rooted_iff`:
`IsIso … R f ↔ ∃ e : X ≃g Y, ⇑e = f ∧ e u = p.1 ∧ e v = p.2` (uses `dist_eq_of_iso`).

Connected graphs on arbitrary finite types; for general graphs `graphScript` asks, for each pair of components, the connected
reduction (with the singleton components directly, `anyScript`) and returns `{g | ∀ c, restr g c ∈ ⋃ answers}`;
`iso_iff_restr` (`restr g c` is the restriction to the component, as a partial map).

**Main statements** (`Luks/Components.lean`):

```lean
theorem graphIso_general {P : Params} {w : M.Node P → ℝ} (h : Stage1Conclusion P w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      (∀ v, Nat.card (X.neighborSet v) ≤ d) → (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
      ∃ (s : Script (Set (Perm (Fin n)))) (e : M.Exec P s s.evalExact),
        s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} ∧
        s.CallsExact (fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4) ∧
        e.total w ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2)))

theorem graphIso_final (hcite : GI.Cited.TransitiveAffected)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDL : GI.Cited.DesignLemma) (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ (P : Params) (C : ℝ), 0 ≤ C ∧ ∀ (n d : ℕ) (X Y : SimpleGraph (Fin n)),
      (∀ v, Nat.card (X.neighborSet v) ≤ d) → (∀ v, Nat.card (Y.neighborSet v) ≤ d) →
      ∃ (s : Script (Set (Perm (Fin n)))) (e : M.Exec P s s.evalExact),
        s.evalExact = {g | ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)} ∧
        s.CallsExact (fun {_ _} m T => m = .solve ∧ GammaHat d T.G ∧ (T.size : ℝ) ≤ 3 * (n : ℝ) ^ 4) ∧
        e.total (fun _ => (1 : ℝ)) ≤ Real.exp (C * (Real.log ((d : ℝ) + 2) * Real.log ((n : ℝ) + 2)))
```

`Stage1Conclusion P w` is the conclusion of `degreeD_stage1_cited` (`M.Run` exists on every `Γ̂_d` state with exact
answer; every run with root bounds costs `≤ exp(C'·lam d·log(s+2))`). Connected case: `graphIso_connected`, `graphIso_connected_final` (`Luks/Final.lean`).

The degree hypothesis is `Nat.card (X.neighborSet v) ≤ d`; `card_neighborSet_le_of_degree` converts `X.degree v ≤ d`.

Luks's standard statement has the groups in `Γ̂_{d−1}` (rooted at an edge, each vertex has at most
`d−1` down-neighbours). Here the slot count is `q = min d n` with `q ≥` the maximum degree, so the groups are in `Γ̂_d`; rooting at an edge is used only to start the layers (`n ≥ 2`). The theorem's bound and class are as the task allows.

## Axioms

```
#print axioms graphIso_final          : propext, Classical.choice, Quot.sound, GI.DegreeD.M.bcp, GI.DegreeD.M.gnsPrimitive
#print axioms graphIso_general        : propext, Classical.choice, Quot.sound
#print axioms Supply.ofGiant          : propext, Classical.choice, Quot.sound
#print axioms degreeD_stage1_cited    : propext, Classical.choice, Quot.sound
#print axioms LG.gammaHat_aut         : propext, Classical.choice, Quot.sound
```

The hypotheses of `graphIso_final` are the six statements HJ's Stage-1 theorem cites (hypotheses in HJ, not axioms in
this development, as in `degreeD_stage1_full`): `GI.Cited.TransitiveAffected`, `KaryCoherentRefinement`, `SixTransitiveContainsAlt`, `DesignLemma`,
`AutCardLeSq`, `SimpleValuationDegree`. The GNS constants `c₁, c₂` of `gnsPrimitive` are absorbed in the choice of `P`, `cc`. **No new
axiom and no new cited statement was introduced.**

## Non-vacuity

* `params_full` (kernel-checked): the numeric and aggregation hypotheses are simultaneously satisfiable for the
  constants of `gnsPrimitive` (given `hcite`).
* `graphIso_final` has no hypotheses other than the cited results: `nodeBoundD_one` supplies `w ≡ 1`, `degreeD_stage1_cited` supplies runs on all `Γ̂_d` states, and
  `Supply.ofGiant` is the `M.Supply`; the `∃ P, C` is witnessed by `params_full`.
* `layerState` etc. are concrete definitions; `rootedScript_spec` is unconditional. `Script` is HJ's `Script`, so `s` is a
  genuine object of the existing script language.

## What remains between this and "GI of max degree `d` in `n^{O(log d)}` time"

1. **Traces, not a program.** `M.Exec`/`M.Run` are trees with their choices supplied. The script's read-off of `A', τ'` (`readStep`) and the
   slot assignments are classical functions, not computed. The red-team's `Structural`
   recognition gap is unchanged.
2. **`w` is not time.** `graphIso_final` counts nodes (`w ≡ 1`). `NodeBoundD` for real per-node work is Stage-2, and the script's own work
   per layer (building the instance of size `O(n⁴)`, reading cosets) is not counted in `e.total`; it is polynomial per call, with `≤ n⁵` calls in total.
3. **Trusted inputs**: `bcp`, `gnsPrimitive`, the six HJ cited statements, all HJ correctness (H0). No change.

## Layout and compile order

`Induction TableLambda RStarColumns ListFam ScriptFamilies GammaHat M.Dispatch M.Cited M.Run M.Correctness M.Tree M.PhaseTree M.ScriptFam M.Bounds M.RealRuns M.Closure M.QClip M.TotalCost M.PhaseCost M.Main M.Existence M.Axioms M.ParamsExample M.Final M.Supply M.NodeBoundOne Luks.Wreath Luks.Step Luks.Reduction Luks.Graph Luks.Final Luks.Components`, each with `lake env lean --root=lean -o $OL/...` as in `docs/w36-lean.md`.
New Lean: 2524 lines in `Luks/`, 293 + 92 in `M/` (`M/ParamsExample.lean` got a generalized `params_exist_ge`). Total new: about 2900 lines.
