# STATUS: leanmaxx-moore (the bipartite Moore bound, in general)

## Done

Both main theorems build with no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
`unsafe` in the new files. `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for each
(`lean/BipartiteDD/LeanMaxx/Moore/Axioms.out.txt`).

Files (all new, under `lean/BipartiteDD/LeanMaxx/Moore/`; no existing file was edited):

- `Layers.lean`: the counting. Layers `L_i(u,v) = {w : dist u w = i ≤ dist v w}`, the bound
  `|L_i| ≤ (d-1)^i` (`card_layer_le`), and the covering argument `card_le_of_edge`.
- `Main.lean`: the main theorem `BipartiteDD.LeanMaxx.Moore.card_le_moore` and the regular corollary
  `card_le_moore_of_regular`.
- `Axioms.lean` and `Axioms.out.txt`.

Statement, as on the card:

```
theorem card_le_moore {V : Type*} [Fintype V] (G : SimpleGraph V) {d D : ℕ} (hd : 2 ≤ d)
    (hD : 1 ≤ D) (h : BipartiteDD.IsBipartiteDegDiam G d D) :
    Fintype.card V ≤ 2 * ∑ j ∈ Finset.range D, (d - 1) ^ j
```

## Proof, and how it differs from the card's sketch

The card's sketch ("count vertices by layers of the two trees grown from u and v") is what the proof does,
made precise as follows.

1. No edge: a connected graph with no edge has at most one vertex. Two distinct vertices would be joined
   by a walk, and its first step is an edge.
2. Edge `uv`: `dist u w ≠ dist v w` for every `w`. This is bipartiteness, via Mathlib's
   `Coloring.even_length_iff_congr` on a `Bool`-colouring built from the `Fin 2` colouring.
3. Each `w` lies in `L_i(u,v)` or `L_i(v,u)` for some `i < D`. Here `i ≤ dist u w < dist v w ≤ D`, using
   the parity fact to get the strict inequality. So `|V| ≤ ∑_{i<D} |L_i(u,v)| + ∑_{i<D} |L_i(v,u)|`.
4. `|L_i| ≤ (d-1)^i`, by induction on `i`. `L_0 ⊆ {u}`. A vertex of `L_{i+1}` has a neighbour `p` with
   `dist u p = i`, and `p ∈ L_i`. Each `x ∈ L_i` misses one neighbour in `L_{i+1}` (`v` if `i = 0`, its
   predecessor otherwise), so it has at most `d-1` neighbours in `L_{i+1}`.

`d ≥ 2` is not used in the proof; the bound holds for all `d`. The hypothesis is kept because the card
states it. `D ≥ 1` is used only in the no-edge case.

The regular corollary takes `(G.neighborSet v).ncard = d` for every `v`, and is `card_le_moore` applied
to `≤ d`. It is free, as the card allowed. It adds no content beyond the main theorem.

## Verification

- `lake build BipartiteDD.LeanMaxx.Moore.Main` succeeds. One lint warning: `hd` is unused (see above).
- `Axioms.out.txt`: both theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
- The `Layers.lean` build also succeeds, with one unused-section-variable lint, which I fixed with `omit`.

## Toolchain note

`lean/` had no `.lake` directory and no elan. I installed elan (`elan-init.sh -y --default-toolchain none`),
then Lean 4.34.1 from `lean-toolchain`, then `lake exe cache get` (8908 Mathlib cache files). After that,
single-module builds take seconds.

## Blocked

Nothing.

## Partial / remaining

Nothing. Equality cases (Moore graphs, generalized polygons) were not attempted; the card does not ask for them.
