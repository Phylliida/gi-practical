# w54-lean-t2: machine check of T2 (Steiner triple system reduction)

Branch `w54-lean-t2`, 2026-11-09. Target: T2 of `docs/w30-sts.md` §6, as re-derived in `docs/redteam-w30-sts.md` §1.
Code: `lean/STS/` (Lean 4 v4.30.0-rc2, mathlib `2f9133a`, imports only `Mathlib.*` and `STS.*`).

## Verdict

**Full.** Both parts of T2 are machine-checked as the memo states them, with no extra hypothesis:

1. for every `d` and every colouring `χ`, `X_χ` is a Steiner triple system on `2^(d+3) − 1` points;
2. for non-constant `χ, χ'`, `X_χ ≅ X_χ'` iff `χ' ∘ A = χ` on `V ∖ 0` for some `A ∈ GL(V)`, including the hard direction.

There is no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`. Nothing in the memo's T2 statement or proof turned out wrong. The memo's `d ≥ 2` is implied by non-constancy, so it is not a hypothesis. The rank bound and the complexity reading of T2 are not covered (see the last section).

## The statement (`lean/STS/Statement.lean`, 102 lines, imports only Mathlib)

The definitions, copied from the file without their doc comments:

```lean
def IsSTS {P : Type*} (blocks : Set (Finset P)) : Prop :=
  (∀ B ∈ blocks, B.card = 3) ∧
  ∀ x y : P, x ≠ y → ∃! B : Finset P, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

def Isomorphic {P P' : Type*} [DecidableEq P'] (blocks : Set (Finset P))
    (blocks' : Set (Finset P')) : Prop :=
  ∃ e : P ≃ P', ∀ B : Finset P, B ∈ blocks ↔ B.image e ∈ blocks'

abbrev V (d : ℕ) := Fin d → ZMod 2

def LinearlyEquivalent {d : ℕ} (χ χ' : V d → Bool) : Prop :=
  ∃ A : V d ≃ₗ[ZMod 2] V d, ∀ c : V d, c ≠ 0 → χ' (A c) = χ c

def NonConstant {d : ℕ} (χ : V d → Bool) : Prop :=
  ∃ c₀ c₁ : V d, c₀ ≠ 0 ∧ c₁ ≠ 0 ∧ χ c₀ ≠ χ c₁

abbrev Z := Fin 8          -- 𝔽₂³ in binary, addition = xor ^^^

def F1 (z : Z) : List (Z × Z) :=          -- the memo's table, verbatim
  match z.val with
  | 1 => [(0, 5), (1, 2), (3, 4), (6, 7)]
  | 2 => [(0, 2), (1, 6), (3, 7), (4, 5)]
  | 3 => [(0, 7), (1, 5), (2, 4), (3, 6)]
  | 4 => [(0, 4), (1, 7), (2, 3), (5, 6)]
  | 5 => [(0, 1), (2, 7), (3, 5), (4, 6)]
  | 6 => [(0, 6), (1, 3), (2, 5), (4, 7)]
  | 7 => [(0, 3), (1, 4), (2, 6), (5, 7)]
  | _ => []

def InFactor : Bool → Z → Z → Z → Prop          -- {a,b} ∈ F^col_z
  | false, z, a, b => b = a ^^^ z
  | true,  z, a, b => (a, b) ∈ F1 z ∨ (b, a) ∈ F1 z

abbrev Point (d : ℕ) := {z : Z // z ≠ 0} ⊕ ({c : V d // c ≠ 0} × Z)

def X {d : ℕ} (χ : V d → Bool) : Set (Finset (Point d)) :=
  { B | (∃ z₁ z₂ z₃ : {z : Z // z ≠ 0}, z₁.1 ^^^ z₂.1 ^^^ z₃.1 = 0 ∧
            B = {.inl z₁, .inl z₂, .inl z₃}) ∨
        (∃ (z : {z : Z // z ≠ 0}) (c : {c : V d // c ≠ 0}) (a b : Z), InFactor (χ c) z a b ∧
            B = {.inl z, .inr (c, a), .inr (c, b)}) ∨
        (∃ (c₁ c₂ c₃ : {c : V d // c ≠ 0}) (a b : Z), c₁.1 + c₂.1 + c₃.1 = 0 ∧
            B = {.inr (c₁, a), .inr (c₂, b), .inr (c₃, a ^^^ b)}) }

def T2_sts : Prop :=
  ∀ (d : ℕ) (χ : V d → Bool), IsSTS (X χ) ∧ Fintype.card (Point d) = 2 ^ (d + 3) - 1

def T2_iso : Prop :=
  ∀ (d : ℕ) (χ χ' : V d → Bool), NonConstant χ → NonConstant χ' →
    (Isomorphic (X χ) (X χ') ↔ LinearlyEquivalent χ χ')
```

`lean/STS/Main.lean` proves `theorem STS.t2_sts : T2_sts` and `theorem STS.t2_iso : T2_iso`.

The claims are written as `Prop` definitions so that Statement.lean needs no proof imports and holds everything a reader must check. A reader can see that:
- `X χ` is a set-builder over the memo's three kinds of block, with no choice and no `∃` over the construction;
- STS, isomorphism and GL-equivalence are the textbook notions.

Proof devices (`third`, `partner`, `label`) appear only in proof files. The partners and labels inside the fixed 8-point gadget use `Classical.choose`, which `X` never touches.

The Lean tail of `Main.lean` prints:

```
'STS.t2_sts' depends on axioms: [propext, Classical.choice, Quot.sound]
'STS.t2_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
'STS.induced_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparison with the memo's T2, item by item

| memo (w30 §6, red-team §7.1) | Lean | effect |
|---|---|---|
| $V=\mathbb F_2^d$, $d\ge2$ | `V d = Fin d → ZMod 2`, any `d` | Part 1 holds for every `d ≥ 0` (`d = 0` is the Fano plane, `d = 1` has 15 points). In part 2, `NonConstant` already forces two distinct nonzero vectors, so `d ≥ 2` follows. |
| $\chi:V\setminus0\to\{0,1\}$ | `χ : V d → Bool`, the value at `0` is never read (`X`, `NonConstant` and `LinearlyEquivalent` look only at `c ≠ 0`) | Equivalent; `false` is colour 0. |
| $Z=\mathbb F_2^3$, table entries `0..7` | `Z = Fin 8` with xor | Same encoding as the memo's code (`x_fib` in `docs/w30-sts-code/sts.py`: `a ^ z`, `a ^ b`). |
| $F^1$ with properties (a), (b) | the memo's table, copied verbatim | The theorem is for **this** table, not for any gadget with (a), (b). (a) and (b) are not hypotheses: they are proved by `decide` in the form the proof uses (next section). |
| $F^0_z=\{\{a,a+z\}\}$ | `InFactor false z a b ↔ b = a ^^^ z` | Same. |
| blocks (i), (ii), (iii) | the three clauses of `X` | Same. A line `{c₁,c₂,c₃}` of `PG(V)` is written as three nonzero vectors with sum 0, which forces them to be distinct. Likewise in (i). |
| "STS of order $n=8\cdot2^d-1$" | `IsSTS (X χ) ∧ Fintype.card (Point d) = 2^(d+3) − 1` | Same. |
| $X_\chi\cong X_{\chi'}\iff\exists A\in\mathrm{GL}(V),\ \chi'\circ A=\chi$ | `Isomorphic (X χ) (X χ') ↔ ∃ A : V d ≃ₗ[ZMod 2] V d, ∀ c ≠ 0, χ' (A c) = χ c` | Same orientation as the memo. |
| red-team: "every isomorphism induces $A$ … every such $A$ lifts" | `induced_linear` (Backward.lean): every isomorphism maps `Z∖0` to itself and the fibre over `c` into the fibre over `A c`, with `χ'∘A = χ`. `liftEquiv` (Forward.lean) is the lift `z ↦ z`, `(c,a) ↦ (A c, a)`. | Proved: isomorphisms surject onto linear equivalences. The gauge kernel `K` is not formalized. |
| rank $\ge\log_2(n+1)-3$; poly-time reduction; consequence for $n^{o(\log n)}$ | not formalized | See the last section. |

## Proof structure (files under `lean/STS/`)

| file | lines | content |
|---|---|---|
| `Statement.lean` | 102 | definitions and the two claims |
| `Gadget.lean` | 137 | facts about xor and the table on `Fin 8`, by `decide`: each `F^col` is a 1-factorization; (b) as `F1_span`; (a) as `F1_not_PG` |
| `Steiner.lean` | 118 | generic layer. A "third point" operation with the Steiner-quasigroup laws gives an STS `{{x,y,t x y}}`. A bijection is a block isomorphism iff it commutes with `t`. |
| `Third.lean` | 238 | the explicit `third χ`, its laws, and `X χ = blocksOf (third χ)` |
| `Chars.lean` | 132 | character classification (below) and the coordinate characters `c ↦ c_i` |
| `Forward.lean` | 55 | (⇐) |
| `Backward.lean` | 258 | (⇒) |
| `Main.lean` | 38 | the two theorems, the point count, `#print axioms` |
| `Sanity.lean` | 172 | non-vacuity checks |
| total | 1250 | |

(⇒) follows the memo:
- **Characters.** If `f : Point → 𝔽₂` sums to 0 on every block and `χ` is non-constant, then `f = 0` on `Z∖0` and `f` is constant on each fibre (`char_classify`). A colour-0 fibre gives `λ = μ`, and a colour-1 fibre together with (b) gives `μ = 0`.
- **Fibres.** Pulling back the coordinate characters along an isomorphism shows that it fixes `Z∖0` setwise and maps fibres to fibres. The induced map on `V` is additive, because lines of `PG(V)` go to lines, and bijective.
- **Colours.** In a colour-0 fibre the matchings compose additively: `F⁰_{w₁} ∘ F⁰_{w₂} = F⁰_{w₁+w₂}`. In the colour-1 fibre they do not, by (a). Since the isomorphism maps `Z∖0` to itself and fibre to fibre, colours are preserved.

## What the formalization forced or exposed

- **The memo's statement and proof are correct as written.** No step needed repair.
- **(b) is used only through 3 of the 28 table pairs:** `(z;a,b) = (1;0,5), (1;1,2), (2;1,6)`, with additivity of `μ` (`F1_span`).
- **(a) is used in a concrete form rather than as "T¹ ≇ PG(3,2)":** one explicit path `a → b → c` through `F¹_{w₂}` then `F¹_{w₁}`, with `{a,c} ∉ F¹_{w₁+w₂}` (`F1_not_PG`, found by `decide`).

  The memo's last step ("`S ∪ C_c` is PG(3,2) iff the colour is 0") never needs PG(3,2) to be recognized abstractly. The isomorphism is already known to fix `S = Z∖0` and to map fibres to fibres, so it suffices that colour-0 matchings compose like addition in `Z` and colour-1 matchings do not.
- **Where non-constancy enters.** It is used only in the character step: two distinct nonzero fibre indices make `μ` independent of the fibre and additive; a colour-0 fibre gives `λ = μ`; a colour-1 fibre gives `μ = 0`.

  A hand remark, **not machine-checked**: for this table the colour-1 equations alone already force `μ = λ = 0`. I checked this exhaustively over all 8 additive `μ` and 128 `λ`. So for `d ≥ 2` the hypothesis could probably be weakened to "χ ≢ 0", plus a separate argument for `χ ≡ 0`, where `X_0 = PG(d+2,2)` and its characters separate points. This matches the red-team's exact finding that iso ⟺ same GL-orbit with constants included at `d ≤ 3`. It is not part of the memo's claim and is not formalized.
- **Points of detail the Lean statement makes explicit:**
  - the value of `χ` at 0 is irrelevant;
  - "lines" means nonzero triples with sum 0;
  - part 1 holds for all `d`.

## Non-vacuity checks (`lean/STS/Sanity.lean`)

All of these are proved without `sorry`. The `#print axioms` output for the four key lemmas is again `propext, Classical.choice, Quot.sound`.

- **`d = 2`:** `χ₁ = 1_{e₀}`, `χ₂ = 1_{e₁}`, `χ₃ = 1_{\{e₁, e₀+e₁\}}`, all `NonConstant`.
  - `Fintype.card (Point 2) = 31` by `decide`, independently of the general count.
  - `IsSTS (X χ₁)` holds.
  - There are explicit blocks of kinds (i), (ii) (one colour-1 block and one colour-0 block) and (iii).
  - The colour-0 triple `{1, (e₀,0), (e₀,1)}` is **not** a block of `X χ₁`, so the colouring really changes the blocks.
- **Both sides true:** `χ₁, χ₂`, via the coordinate swap. `LinearlyEquivalent` is proved directly by `decide`, and `Isomorphic` follows from the theorem.
- **Both sides false:** `χ₁, χ₃` (weights 1 and 2). `¬ LinearlyEquivalent` is proved directly, and `¬ Isomorphic` follows from the theorem.
- **`d = 3`, equal weights:**
  - The line indicator `1_{\{f₀,f₁,f₀+f₁\}}` and the basis indicator `1_{\{f₀,f₁,f₂\}}` make **both sides false**. Both have weight 3, so the two STS have the same number of colour-1 fibres, and non-isomorphism comes only from the linear structure. `¬ LinearlyEquivalent` is proved directly: the sum of two distinct basis vectors is not a basis vector.
  - The basis indicator against `1_{\{f₀, f₀+f₁, f₀+f₁+f₂\}}` makes **both sides true**, via a non-permutation matrix.

So the hypotheses are satisfiable, and both sides of the biconditional take both truth values.

## Compile recipe and time

Do not run `lake build` or `lake update`. Each file is compiled by itself against the existing mathlib build, writing oleans to a scratch directory, in dependency order (`Statement Gadget Steiner Third Chars Forward Backward Main Sanity`):

```sh
S=<scratch dir>; mkdir -p $S/out; R=<worktree>/lean
cd ~/math/GraphIsomorphismLog2 && nix shell nixpkgs#elan -c bash -c 'B=$(lake env printenv LEAN_PATH); export LEAN_PATH=$B:'$S'/out; mkdir -p '$S'/out/STS; for f in Statement Gadget Steiner Third Chars Forward Backward Main Sanity; do nice lean --root='$R' -o '$S'/out/STS/$f.olean '$R'/STS/$f.lean || break; done'
```

The loop above, run from an empty output directory, takes **28 s wall-clock** and prints only the `#print axioms` lines: no warnings, no errors. Compiling each file in its own `nix shell` takes 3–8 s per file (Gadget is the slowest at 8 s) and about 41 s in all.

## Not covered

- **The rank bound** `rk(X_χ) ≥ log₂(n+1) − 3`, part of the memo's T2 (via Prop. 1). Not formalized.
- **The complexity reading.** "Polynomial-time reduction" is represented only by `X` being an explicit construction. Running time is not formalized. The arithmetic consequence `n^{o(log n)} ⇒ 2^{o(d²)}` (with `n = 2^{d+3} − 1`) is not formalized.
- **Constant colourings and the value at 0.** The memo's reduction for arbitrary Boolean functions handles these "directly". Only the non-constant biconditional is proved; see the hand remark above.
- **The gauge kernel** `K = Hom(V/⟨supp χ⟩, Z)` and the count `|Aut X_χ| = |Stab_GL(χ)|·|K|` (red-team §1.4). Proved: every isomorphism induces some `A` with `χ'∘A = χ`, and every such `A` lifts. The fibres of this surjection are not described.
- **Other gadgets.** The theorem is for the memo's table only, not for every `F¹` satisfying (a), (b).
- **The rest of w30** (T1, T3, T5, Latin-square isotopy, Prop. 2): not attempted.
