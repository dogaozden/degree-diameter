# STATUS: omega3 (Theorem 3.3 of research/theorems/OMEGA_REPAIR.md)

**Verdict: done.** Theorem 3.3 is formalised and builds, with no sorry, admit or native_decide and no axiom of
our own. `Axioms.out.txt` shows only `propext`, `Classical.choice`, `Quot.sound` for every headline theorem.
All files are new, under `lean/BipartiteDD/LeanMaxx/Omega3/`. The branch also carries the verified files of
`LeanMaxx/Projection/` and `LeanMaxx/Omega2/` (copied unchanged from their branches; `Omega2/Sphere.lean` and
`Omega2/Polygon.lean` are used, `Projection` is not).

## Statement (what is proved)

`omega3_hexagon_geometric_shared` (`Concrete.lean`). Let `F` be a finite field with `q = |F| ≥ 8` (any
characteristic: q = 8, 9, 11, 13, 16, …), `α ≥ 1` blocks of five copies with `2 α ≤ q + 3` (Gómez: `α = ⌊(q+3)/2⌋`),
any block types `typ : Fin α → Bool` (false = type a, true = type b), `ε₀ : ZMod 2` the colour of the unbarred hubs
(`ε₀ = 0` is reading 2, unbarred hubs on points and barred hubs on lines; `ε₀ = 1` is its point/line dual). A
*labelling* gives each copy `c` a colour-preserving bijection `μ c` of the vertices of the incidence graph of `H(q)`
(the map row ↦ vertex of copy `c`; one bijection per copy serves its points and its lines). It is *geometric*
(`GeometricShared`) if, for every hub class `(bar, k)` meeting copies `c` and `d`, the transfer map
(mark of a row in `c` ↦ mark of the same row in `d`) is the restriction of an automorphism of the incidence graph.
Then the graph `omega … (labMk μ)` (the wiring of Figs. 2.21a/b: copies of `H(q)` and hubs `(bar, k, row)` joined
to the mark of the row in every copy met by the class) satisfies `9 ≤ ediam`.

This is the wording of the note and of the referee (`research/referee/omega-repair.md`: the per-copy model, the
transfers along shared classes). Not covered, as in the note: non-geometric labellings, labellings chosen per
(hub class, copy), other wirings, reading 1 with mixed inner classes, and q ≤ 7 (q = 7 needs the character-sum
argument of §4 of the note, which is not formalised).

Other forms: `omega3_hexagon` (normal form `mk false c = 1`, `mk true c = λ_c`), `omega3_ediam` / `omega3_far`
(any `Hex` graph; `omega3_far` gives the far pair: a hub and a vertex of a copy it misses),
`omega3_geometric` (all-pairs `Geometric`), `omega3_hexagon_thesis` (sanity: the thesis labelling `μ c = 1` has
diameter ≥ 9 for q ≥ 8, consistent with Theorem 1 of `d12D8_table.md`).

## Files

| file | content |
|---|---|
| `Balls.lean` | `Hex B κ q` (bipartite, `(q+1)`-regular, girth 12, diameter 6). **Lemma 3.1** upper bounds: `card_ballOpp_two_le` (`≤ q²`) and `card_ballOpp_four_le` (`≤ q⁴ + 2q²`) for the vertices opposite `t` within distance 2, 4 of a centre of the colour of `t`. Key identity `X4_add`: `|X4| + q |X2| = q |T3|` (double count). |
| `Wiring.lean` | `Copy α = Fin α × ZMod 5`, `metPos`/`meets` (which positions a hub class meets), `share`, `CuK`, the families `F0 … F3`, `m2`, `cstar` (the missed copy). **Lemma 3.2**: `cstar_not_mem`, `card_F0_le` (`≤ α`, one copy per block, via `unique_star`). Crude counts `card_F1_le`, `card_F2_le`, `card_F3_sdiff`, `m2_add_le`, `crude_ineq`, `star_crude` (q ≥ 10). |
| `Tables.lean` | `star_small`: the cases q = 8, 9 by kernel evaluation (`decide +kernel`) for every pattern `Fin α → Bool`, α ≤ 5 resp. 6. `star_exists`: the counting hypothesis for every q ≥ 8. About 4 minutes. |
| `Graph.lean` | `autSub`, `Hub`, `Vtx`, `omega B κ typ ε₀ mk` (via `SimpleGraph.fromRel`), adjacency lemmas, `Kcol` and `Kcol_proper`. |
| `Route.lean` | `pT`, `Route`, `ev`; **Lemma 2.1** as `walk_route`: a walk of length `n` between copy vertices gives a route with `a + 2 |fn| ≤ n` and a `B`-walk of length `≤ a` from the transformed start. Works for any hexagon, any transfer maps that are colour-preserving automorphisms. |
| `Shape.lean` | `nfmk`, `cen`, `CovP`; `shape`: a route of cost `≤ 6` from `CuK 0` to the missed copy ends in a ball around a centre indexed by `F0 … F3` (the case analysis p = 1, 2, 3 passes of Lemma 2.1; p = 3 forces three unbarred passes by colour). |
| `Main.lean` | `covSet`, `card_covSet_le`, **Theorem 3.3 (normal form)** `omega3_far`, `omega3_ediam`. |
| `Geometric.lean` | `labMk`, `Geometric`, `aut_col`, `Phi`/`Psi`/`Phi_adj`: **Lemma 1.1** as a graph homomorphism from the graph of a geometric labelling to the normal form (apply `a_c⁻¹` to copy `c`); `omega3_geometric`. |
| `Shared.lean` | `GeometricShared` (the note's definition) ⇒ `Geometric` (`geometric_of_shared`: connectivity of the sharing graph, `copy_connected`, and composition of transfers). |
| `Concrete.lean` | `H(q)` for every finite field: `hex_hexagon` (via `genPolygonGraph_hexagon_even`), `omega3_hexagon`, `omega3_hexagon_geometric(_shared)`, `omega3_hexagon_thesis`. |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` for the headline theorems. |

## Proof as formalised (differences from the note)

1. `walk_route` is proved by strong induction on the walk length. The note's families A, B of Lemma 2.1 appear as
   the cases `shape` distinguishes: one pass (`F0`, radius 4), two passes (`F1`, `F2`, `F3`, radius 2) and three
   passes (all unbarred, radius 0). Colour parity enters only in the three-pass case (the route carries the
   colour of the current vertex).
2. Counting: the note bounds `m₂ ≤ 8α² − 1`; for q ≥ 10 the file uses the cruder `m2 + |F0| ≤ 8α² + 6α` (each copy
   shares a barred class with at most `4α` copies), which still suffices (`crude_ineq`; q = 10 uses α ≤ 6, q ≥ 11 an
   `nlinarith` inequality). For q = 8, 9 the exact families `F1, F2, F3 ∖ F0` are counted by kernel evaluation, for
   all 2^α block patterns (the worst values of `m2` are 5, 25, 55, 95, 145, 207 for α = 1…6; the largest values
   allowed are 181 at q = 8, α = 5 and 230 at q = 9, α = 6). The families agree with the note: a Python script
   with the same definitions gives 140 distinct radius-2 centres for the pattern aabbb at q = 7, the value in the
   referee's table of starved pairs (`research/referee/omega-repair.md`, §2).
3. **Lemma 3.1 is proved with the weaker bound `q⁴ + 2q²`** (the exact value is `q⁴`). This is enough: the margin
   at q = 8, 9 is a few thousand. The proof needs only the layer lemmas of `Omega2/Sphere.lean` (no
   distance-regularity, no odd radii) and the identity `X4_add`.
4. The note's `α` radius-4 centres are `|F0| ≤ α` (Lemma 3.2 needs only the upper bound).
5. The note's Theorem 3.5 (all readings, dualities) is not formalised; reading 2 and its dual are `ε₀ = 0, 1`.
   Dualities are allowed in `Geometric` (any automorphism of the incidence graph); `aut_col` shows that an
   automorphism that restricts to a colour-preserving transfer preserves colours.

## Build and check (reproduce)

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Omega3.Axioms      # about 6 minutes, most of it Tables.lean
    lake env lean BipartiteDD/LeanMaxx/Omega3/Axioms.lean

`grep -nE "sorry|admit|native_decide|implemented_by|unsafe" lean/BipartiteDD/LeanMaxx/Omega3/*.lean` has no hits.
`Tables.lean` uses `decide +kernel` (kernel evaluation of a decidable proposition; no extra axiom, as the output of
`#print axioms star_exists` shows).

## Remaining / notes

- q = 7 (Theorem 4.5: Bonferroni on 17 configuration types, character-sum bound on `Perp(h)`) and Theorem 3.5 are
  not formalised.
- Lemma 3.1 with the exact values `q⁴`, `q²` and the odd radii is not needed and not proved.
- The graph `omega` has vertex set `(Copy α × β) ⊕ Hub`: copies of the incidence graph and hubs, as in the note
  (hub degree `2α`, copy vertices of degree `q + 3`). Nothing is assumed about degrees in the Lean statement
  beyond `2 α ≤ q + 3`.
