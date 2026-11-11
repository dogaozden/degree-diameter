# VERIFY: omega2 (Theorem 2 of research/squads/cells/d12D8_table.md, Lean files `lean/BipartiteDD/LeanMaxx/Omega2/`)

Job leanmaxx-verify-omega2 (independent verifier, Sonnet). Verifier branch `claude/leanmaxx-verify-omega2-lms0i1`, made from
origin/master (ab2f6fb), with `origin/claude/omega2-theorem-2-formalization-61iulq` (e623fc9) merged. I did not use the
worker's logs or its `Axioms.out.txt` as evidence, and I changed no proof.

## Verdict

**The proof is accepted.** Every module builds from a clean checkout with Lean 4.34.1 and Mathlib, with no sorry. The
regenerated axiom list is byte-identical to the committed one and shows only `propext`, `Classical.choice`, `Quot.sound`.
The statements say what the note's Theorem 2 says, with the limits listed in §5 (none of them a weakening for q ≥ 7 and
the thesis's ΩH_q). One gap to know about: q = 8 is not wired in the committed files. I checked that a 10-line wrapper
closes it (§5.5).

## 1. Merge

`git merge origin/claude/omega2-theorem-2-formalization-61iulq` into the branch at origin/master: fast-forward, **no
conflicts**. The branch adds 11 files (10 Lean files under `lean/BipartiteDD/LeanMaxx/Omega2/` and
`research/lean-maxx/STATUS-omega2.md`) and touches nothing else (`git diff --stat origin/master HEAD`).

## 2. Build, one module at a time, foreground

Fresh container: no `.lake`, no Lean. I installed elan, toolchain `leanprover/lean4:v4.34.1` (the repo's `lean-toolchain`),
ran `lake exe cache get` (8,908 Mathlib files), then `lake build <module>` in dependency order:

| module | result |
|---|---|
| `Omega2.Sphere` (also built `Doubling.Hat`) | OK, 1 linter warning (`haveI` vs `have`) |
| `Omega2.Count` | OK |
| `Omega2.Trace` | OK |
| `Omega2.Reach` | OK, 1 warning (`push_neg` deprecated) |
| `Omega2.Main` | OK |
| `Omega2.Polygon` (also built `Hexagon.*`, 1m22s) | OK |
| `Omega2.HexQ` | OK, `Try this` linter warnings |
| `Omega2.Toy` | OK |
| `Omega2.Axioms` | OK |

Every build exited 0. No warning or error mentions `sorry`; the only warnings are style linters (`haveI`, unused simp
args and section variables in the older `Hexagon` files, `push_neg` deprecation).

## 3. Axioms, regenerated

`lake env lean BipartiteDD/LeanMaxx/Omega2/Axioms.lean` → `verify-omega2/Axioms.regen.txt`;
`diff` with the committed `Axioms.out.txt`: **identical**. 15 theorems printed: `pred_unique`, `q_pow_five_le_card_sph_six`,
`card_sph_five`, `HexData.card_sph_eq`, `count_lt`, `exists_trace`, `HexData.reach_bad`, `HexData.exists_far`,
`omega2_far`, `omega2_ediam`, `omega2_ediam_polygon`, `omega2_ediam_inc`, `exists_sigma`, `omega2_ediam_hexagon`,
`omega2_toy`. All depend on `[propext, Classical.choice, Quot.sound]` (`exists_trace` on `[propext, Quot.sound]`).
Nothing else, so no `sorryAx`, no `Lean.ofReduceBool`.

## 4. Grep over the new files

`grep -nwE "sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|ofReduceBool|opaque|set_option|macro|elab|syntax|notation|local|attribute|initialize|run_cmd|partial|noncomputable"`
and `grep -nE "instance|deriving|class |structure "`, case-insensitive grep for `sorry|admit`:

- `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, `opaque`, `macro`, `elab`,
  `syntax`, `notation`, `attribute`, `initialize`, `partial`: **no hits**.
- `instance`: no declaration (the two textual hits are the words "instance" in comments: `Main.lean:74`, `Polygon.lean:88`;
  nothing is declared as an instance, so no instance can change the meaning of a statement).
- `set_option`: five hits, all `set_option linter.unusedSectionVars false` (Main 27, Polygon 14, Reach 16, Sphere 17,
  Toy 12). A linter switch; changes no elaboration.
- `noncomputable def`: `W2`, `W3`, `X1`, `X2` (Reach), `sph` (Sphere). Plain definitions that use classical choice for
  `Finset.filter`/`biUnion`; this is the reason `Classical.choice` is in the axiom list.
- `structure HexData … : Prop` (Reach 23): a `Prop` structure with fields `egirth`, `reach`, `deg`, `col`. Not an axiom.
- `local`/`open scoped`: none in these files.

Also: no file of the branch touches `lakefile.toml`, `BipartiteDD.lean` or any existing file.

## 5. Statement fidelity

Statements as printed by Lean (`#check`):

`omega2_far`: for `HexData B q κ` (B finite, girth 12, connected, (q+1)-regular, 2-coloured by κ), `7 ≤ q`, an involution
`π` with `κ (π a) = κ a + 1`, a graph `G` with proper 2-colouring `K`, label map `f : V → β`, copy map `c : V → Option ι`:

- `h1`: a G-edge between two copy vertices lies in one copy (`i = j`) and `B.Adj (f u) (f w)`;
- `h2`: for every new vertex `x` (`c x = none`) every neighbour `w` is a copy vertex with `f w = f x ∨ f w = π (f x)`;
- `hsurj`: every copy has a vertex of every label;
- `hconn`: any two vertices of a copy are joined by a walk all of whose vertices are copy vertices;
- a new vertex `x` with no neighbour in copy `j`,

then `∃ v, c v = some j ∧ 9 ≤ G.edist x v`. `omega2_ediam` concludes `9 ≤ G.ediam`; `omega2_ediam_polygon` takes
`GenPolygonGraph B 6` plus degrees; `omega2_ediam_inc` is the incidence-structure form with `σ : P ≃ L`, `partner σ`
(point t ↦ line σ t, line l ↦ point σ⁻¹ l); `omega2_ediam_hexagon` is `H(q)` over `F` (`Fintype`, `NeZero 2`, `|F| ≥ 7`)
with any `σ : SPt F ≃ HLine F`.

### 5.1 Is this Theorem 2 of the note?

Note's Theorem 2: q ≥ 7; every K₁-vertex joined only to point t and line σ(t); any bijection σ, any mix of blocks, any
colour convention per copy; conclusion: some pair at distance ≥ 9. Item by item:

- **any σ**: `σ : P ≃ L` is a free argument (`omega2_ediam_inc`, `_hexagon`); `π` is any involution flipping classes
  in `omega2_far`.
- **any mix of blocks**: the block structure does not occur; copies are indexed by an arbitrary type `ι`, and only `h1`,
  `h2`, `hsurj`, `hconn` and "x misses copy j" are used. Which copies a hub meets is unconstrained.
- **any colour convention per copy**: `K` is only required to be a proper 2-colouring of `G`. The proof derives, per
  copy, that `K + κ∘f` is constant (`eps_walk`, from `hconn`, `h1`, `hK`), so a copy may be coloured either way round
  relative to its labels; copies may differ.
- **x meeting one label or two**: `h2` allows `f w = f x` or `f w = π (f x)`; neither has to occur, and which of the two
  a hub meets may change from copy to copy. So reading 1 and reading 2 of the note (§1.3) are both instances.
- **q ≥ 7**: `7 ≤ q` is a hypothesis (`HexData` with `q+1` regularity).
- **conclusion**: `omega2_far` gives an explicit `x`, `v` with `G.edist x v ≥ 9` (ℕ∞-valued, so `⊤` for different
  components also counts, and for ΩH_q the graph is connected anyway). `omega2_ediam*` give `9 ≤ G.ediam`, equivalent to
  a pair at distance ≥ 9 for a graph of finite diameter and a violation of "diameter ≤ 8" in every case.

The proof's route matches the note (§2 and STATUS): class parity, the cases s = 0, 1, 2, 3 switches, the numbers
`sumA q`, `sumB q` (checked: `Count.lean` equals the note's A and B formulas; A + B + 1 = 15,459 / 25,482 / 39,763 at
q = 7 / 8 / 9, below q⁵ = 16,807 / 32,768 / 59,049).

### 5.2 Are h1, h2, hsurj, hconn satisfied by Gómez's ΩH_q?

I downloaded the thesis (F. Comellas' site, PDF pp. 49–52 = thesis pp. 43–46, and pp. 45–47 = thesis pp. 39–41) and read
§2.9.3 and §2.8.9 myself. Findings:

- **Copies**: "5α copies of B₁" (Figs 2.21a and 2.21b, 5 each when α = 2); B₁ is the incidence graph of H(q) (the thesis
  says B₁ is bipartite of even diameter; the table lists ΩH_q from H(q)). The only edges among copy vertices are the
  copies' own edges: the figures add edges only to the K₁-vertices. So **h1** holds (with `f` = the label in B₁: §2.8.9
  p. 41 writes the vertices of a copy as (t, 1, j, k, h) with the same t, j in every copy).
- **hsurj, hconn**: each copy is a whole copy of B₁ (connected, every label present). Hold.
- **h2**: §2.8.9 (p. 39 text, Fig. 2.18, p. 41) joins the K₁-vertex (t, i) to vertices of the copies carrying the same
  label t (the figure writes "~(t, ·)" at both dots of a copy, i.e. class 0 and class 1 with label t). §2.9.3 reuses the
  construction ("también se toman, como en los Apartados 2.8.4 y 2.8.9, copias de K₁"). In Figs 2.21a/b each K₁-vertex
  k, k̄ sits on one edge (star or arc) with two dots, and each dot is one class of one copy. Which class the inner/outer
  dot is is not stated, but whichever it is, (t,k) meets only labels t of class 0 or class 1, i.e. point t or line σ(t)
  where σ pairs the label t of the two classes. `h2` allows exactly that set. Also no K₁–K₁ edges: the degree count
  closes with copy edges alone (K₁-vertex degree 2α = 2 per block × α blocks; p. 45 "el grado … se incrementa hasta
  2α"), so `c w ≠ none` holds.
- **Count check of the reading** (p. 44–45): N = 10·N₁/2 + 5αN₁ = 5(α+1)N₁: 10 sets of N₁/2 K₁-vertices plus 5α copies.
  The first formula on p. 44 reads "10·N₁/2 + 10N₁ = 15N₁" (α = 2), so the "10 sets of N₁ vertices" in the sentence above
  it is the slip the note says (N₁/2). Fine.
- **hK**: the thesis says the construction gives bipartite graphs ("grafos bipartitos"); the note checked bipartiteness
  by computation at q = 3, 5, 9 (`apsp_auto` checks bipartite). `hK` is a hypothesis, not proved in Lean.
- **hmiss (x misses a copy)**: not formalised, but the count is immediate: a K₁-vertex has degree 2α, and there are 5α
  copies, so it meets at most 2α < 5α copies. ΩH₉: 12 < 30.

So ΩH_q (any of the readings of the figures) is an instance. What Lean does **not** contain is a definition of ΩH_q
itself; the step "ΩH_q satisfies the hypotheses" rests on the reading of the thesis above and in §1 of the note.

### 5.3 Does `omega2_toy` show the hypotheses are satisfiable?

Yes, for any `HexData`. `toyGraph`: three copies `Fin 3 × β` of `B` plus two layers of new vertices `(r, t)` joined to
label t in copy r and label π t in copy r+1, so each hub meets two different labels and misses one copy. `omega2_toy`
proves, by applying `omega2_ediam`, that all of `hK, h1, h2, hsurj, hconn, hx, hmiss` hold for it. Two limits of the
worker's example: it is stated for an abstract `HexData` (no concrete `H(q)` plugged in), and `omega2_toy` itself only
shows the conclusion on its own graph, which is not a ΩH_q-like graph.

I closed the first: `verify-omega2/VerifyConcrete.lean` builds `HexData` from `genPolygonGraph_hexagon` for `H(p)`,
`p` any prime ≥ 7 (`ZMod p`, any `σ : SPt ≃ HLine`), and applies `omega2_toy` to the incidence graph of `H(p)` with
`partner σ`. It compiles, axioms `[propext, Classical.choice, Quot.sound]`. So the hypotheses are jointly satisfiable at a
real hexagon, and `HexData`, `7 ≤ q`, `hπ`, `hκπ` are consistent.

### 5.4 Weakenings, limits, extras (all named)

1. **No weakening of the claim** that I can find for q ≥ 7. The Lean hypotheses are at most as strong as the note's;
   they are more general in two places: `h1` only asks that copy edges project to B-edges (copies need not be full copies
   of B), and `hsurj` + `hconn` replace "copy of B₁".
2. **One global σ.** `h2` uses one `π` for all new vertices. In the thesis the labelling of B₁ is single (t for both
   classes), so one σ; a graph in which different hubs used different pairings is not covered. Not what Gómez defines.
3. **`hK` (bipartite) and `hmiss` are hypotheses**, not derived; see 5.2.
4. **Labels preserved by copies.** `f` is a single map `V → β`. Copies that are glued by relabelling (an automorphism
   of B₁ per copy) are included, because `f` may be transported per copy; the thesis uses the identity relabelling
   anyway. A relabelling that is not an automorphism would violate `h1`; not Gómez's construction.
5. **q = 8 and even characteristic.** `omega2_ediam_hexagon` needs `NeZero (2 : F)`. ΩH₈ (11,8) has q = 8, so it is not
   covered by the committed `HexQ.lean`. `omega2_ediam_inc` takes any `GenPolygonGraph`, and `BipartiteDD.HexagonEven`
   (on master) proves `genPolygonGraph_hexagon_even`, `card_lines_through_even`, `finite_hline_even`. I wrote the wrapper
   in `verify-omega2/VerifyEven.lean` (`omega2_even`, every finite field with `|F| ≥ 7`): compiles after
   `lake build BipartiteDD.HexagonEven.Main`, axioms standard. The worker should add it; it is not in the branch.
   q = 5 (ΩH₅) is outside the theorem (`7 ≤ q`), as in the note (the note covers q = 3, 5 by computation).
6. The Lean `Hexagon` library (the model of H(q) as the quadric Q(6,q) with Tits' equations, `genPolygonGraph_hexagon`
   via a Moore-type counting theorem) is older code on master; this job did not re-audit it. The Omega2 files use it only
   through `GenPolygonGraph B 6` (girth 12, diameter 6, bipartite), which is the standard characterisation, plus the
   degrees `q + 1`. `Doubling/Hat.lean:203` defines `GenPolygonGraph` as written in the note's usage.

## 6. What the theorem gives for the thesis's D = 8 values

Applicable in Lean as committed (odd q, |F| ≥ 7): ΩH₇ (10,8), ΩH₉ (12,8), ΩH₁₁ (14,8)/(15,8), ΩH₁₃ (16,8): each has more
copies (25, 30, 35, 40) than the hub degree (10, 12, 14, 16), so `hmiss` holds, and each has diameter ≥ 9, so none is a
graph of diameter 8. ΩH₈ (11,8) follows with `VerifyEven.lean`. ΩH₅ (8,8) is outside q ≥ 7. So the note's verdict on the
(12,8) value 4,650,100 is now a machine-checked theorem on top of the stated reading of the thesis.

## 7. Files in `research/lean-maxx/verify-omega2/`

- `Axioms.regen.txt`: my regenerated `#print axioms` output (identical to the committed file).
- `VerifyConcrete.lean`: `omega2_toy` at `H(p)`, `p` prime ≥ 7, any σ.
- `VerifyEven.lean`: `omega2_even`, Theorem 2 for every finite field with `|F| ≥ 7` (even characteristic included).

Run (from `lean/`, after `lake exe cache get`, the Omega2 build and `lake build BipartiteDD.HexagonEven.Main`):
`lake env lean ../research/lean-maxx/verify-omega2/VerifyConcrete.lean` and the same for `VerifyEven.lean`.
Not part of the Lean library, so the checked-in build is unchanged.

Environment: elan installed from elan.lean-lang.org, Lean 4.34.1 (commit 5045d00), Mathlib cache from cache.mathlib.org,
container with no prior `.lake`. Thesis PDF downloaded to the scratchpad only, not committed.
