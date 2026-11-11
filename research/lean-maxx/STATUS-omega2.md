# STATUS: omega2 (Gómez ΩH_q, Theorem 2 of research/squads/cells/d12D8_table.md §2)

**Verdict: done.** All files under `lean/BipartiteDD/LeanMaxx/Omega2/` build, with no sorry, admit, native_decide or
axiom. `Axioms.out.txt` shows only `propext`, `Classical.choice`, `Quot.sound` (one theorem uses only `propext`,
`Quot.sound`). The files do not import the Projection files; they only use `BipartiteDD.Doubling.Hat`
(`GenPolygonGraph`) and, for `HexQ.lean`, `BipartiteDD.Hexagon.Main`.

## Statement (what is proved)

`omega2_ediam_inc` (`Polygon.lean`), the form of the note: `Hexagon.incGraph inc` on `P ⊕ L` is a generalized
hexagon (`GenPolygonGraph … 6`) with every point and line of degree `q + 1`, `q ≥ 7`; `σ : P ≃ L`.
`G` is any bipartite graph (colouring `K`) with label map `f : V → P ⊕ L`, copy map `c : V → Option ι`, and

- `h1`: a `G`-edge between two copy vertices stays in one copy and projects to an incidence-graph edge;
- `h2` (the switch rule): a new vertex `x` is adjacent only to copy vertices whose label is `f x` or
  `partner σ (f x)` (point `t` and line `σ t`; line `l` and point `σ⁻¹ l`);
- `hsurj`: every copy has every label; `hconn`: two vertices of one copy are joined by a walk through copy vertices.

Then, if some new vertex `x` misses some copy `j`, `9 ≤ G.ediam`. Stronger form `omega2_far` (`Main.lean`): some vertex of
copy `j` is at `G.edist ≥ 9` from `x`. Nothing is assumed about how many of the two labels `x` meets, about which
blocks are used, or about the colour convention per copy.

Further forms: `omega2_ediam` (abstract `HexData`), `omega2_ediam_polygon` (any `GenPolygonGraph B 6`, any
involution `π` flipping a 2-colouring), `omega2_ediam_hexagon` (`HexQ.lean`: the split Cayley hexagon `H(q)`, `F`
finite of odd characteristic, `|F| ≥ 7`, every bijection `σ`; `exists_sigma` shows a bijection exists),
`omega2_toy` (`Toy.lean`: an explicit graph satisfying all the hypotheses, three copies and two layers of new
vertices that each meet two labels and miss one copy, so the theorem is not vacuous).

## Files

- `Sphere.lean`: girth ⇒ at most one neighbour at distance d from a vertex at distance d+1 (d ≤ 4; the cycle
  comes from `Walk.bypass`, `pred_unique`); layer counts; `card_sph_zero`, `card_sph_one`,
  `card_sph_succ`, `card_sph_five` = (q+1)q⁴, `q_pow_five_le_card_sph_six` (`q⁵ ≤ |S₆|`).
- `Count.lean`: `sumA q`, `sumB q` (the A and B of the note, as sums over pairs / triples of sphere sizes) and
  `count_lt : 7 ≤ q → sumA q + sumB q + 1 < q⁵`.
- `Trace.lean`: `Tr B π m s a b` (m edges, s switches), `Tr.walk0`, `Tr.decomp` (split at first switch),
  `Tr.col` (colour parity), `exists_trace` (a G-walk of length m + 2k between copy vertices gives a trace with
  s ≤ k switches), `copy_index_const`, `walk_col`.
- `Reach.lean`: `HexData`, sets `X1`, `X2` with `card_X1 ≤ sumA`, `card_X2 ≤ sumB`; `reach_bad` (the case split
  s = 0, 1, 2, 3 of the proof of Theorem 2); `exists_far`.
- `Main.lean`: `omega2_far`, `omega2_ediam`. `Polygon.lean`, `HexQ.lean`, `Toy.lean`: as above.
- `Axioms.lean`, `Axioms.out.txt`.

## Proof as formalised

Pick a copy-`j` invariant ε (K + κ∘f is constant on a copy). Among `f x`, `π (f x)` take `a` of class `K x + 1 + ε`;
by the counting bound there is `w` at distance 6 from `a` outside `X1 (π a) ∪ X2 a` (`exists_far`); let `v` be the
vertex of copy `j` labelled `w`. Then `K v = K x + 1`, so every `x`–`v` walk has odd length. If it has length ≤ 7,
it is `1 + m + 2k` with `m` even, `k ≥ 1` (otherwise `x`'s first neighbour is in copy `j`), a trace with `s ≤ k`
switches, `m + 2k ≤ 6`. Parity of `s` is forced by the classes (`m` even): s = 0 gives `dist(a,w) ≤ 4`; s = 1 starts
at `π a` and gives `w ∈ X1`; s = 2 starts at `a` and gives `w ∈ X2`; s = 3 forces `m = 0` and `w = a`. All
contradict the choice of `w`. Note the roles: the note's "A" is the s = 1 count, "B" the s = 2 count, "+1" the s = 3 case.

## Build and check

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Omega2.Axioms
    lake env lean BipartiteDD/LeanMaxx/Omega2/Axioms.lean

Grep check: `grep -nE "sorry|admit|native_decide|implemented_by|unsafe" lean/BipartiteDD/LeanMaxx/Omega2/*.lean`
has no hits.

## Remaining / notes

- Even characteristic (q = 8, 16, …): `omega2_ediam_polygon`/`_inc` apply as soon as the hexagon is a `GenPolygonGraph`
  with degrees `q + 1`; `HexQ.lean` covers odd characteristic only (the Hexagon library's `genPolygonGraph_hexagon`).
  `BipartiteDD/HexagonEven` has the even case; not wired.
- The full ΩH_q graph (with its blocks of Figs 2.21a/b) is not built in Lean; the theorem is stated for any graph
  satisfying the switch rule, as the note's Theorem 2 is.
- For q = 3, 5 the counting does not suffice (as in the note); not covered.
