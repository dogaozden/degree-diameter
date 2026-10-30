# STATUS d5-384: the (5,5) record on 384 vertices

**Status: done.** The theorem is kernel-checked, with the standard axioms only.

    theorem nb_5_5_n384 : ∃ G : SimpleGraph (Fin 384), BipartiteDD.IsBipartiteDegDiam G 5 5

Axioms (`lean/BipartiteDD/D5New/Axioms384.out.txt`): `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`,
`axiom` or `native_decide` in the new files, and no `sorryAx` or `Lean.ofReduceBool` in the dependency chain.

## Source
- Edge list: `research/beyond-haar-d5b/records/d5D5_n384_a1_g96_31.edges` (header `384`, then 960 edges). It is the
  384-vertex regular lift of the 4-vertex base `[[2,3],[3,2]]` by a group of order 96 (`g96_31.txt`, `g96_31.info`), with
  voltages in `d5D5_n384_a1_g96_31.sol`. Its recorded checks are in `d5D5_n384_checks.txt`.
- Independent checks before building:
  - `research/beyond-haar-d5b/records/check_bfs.py` on the edge file, with `d=5 D=5`: `n=384 edges=960 degrees=[5]
    bipartite=True connected=True diameter=5 -> VALID`.
  - The Lean adjacency lists in `lean/BipartiteDD/Graphs/G384.lean`, parsed back out of the file, give the same 960
    undirected edges as the edge file. They are symmetric and 5-regular, and the claimed colouring `colL` is a proper
    2-colouring of every edge.
  - `coordinator_lift_check.py` was not used to regenerate the edges. Its sol parser expects the `x/y/z/w` voltage
    layout, and `d5D5_n384_a1_g96_31.sol` has a `g/d/c` layout, so it errors. The brief's check is on the edge file,
    and that file passes the BFS check above.

## Files (all additive; no existing file was changed)
- `lean/gen_d5new384.py`: reads the edge file and writes `lean/BipartiteDD/Graphs/G384.lean` through `lean/gen.py`
  (same layout as G360, with `write_graph` and `two_colour` unchanged). It asserts 384 vertices, 960 edges and
  5-regularity. Run from `lean/`: `python3 gen_d5new384.py`.
- `lean/BipartiteDD/Graphs/G384.lean`: the adjacency lists and colouring.
- `lean/BipartiteDD/D5New/Record384.lean`: `nb_5_5_n384`, via `Fast.check_of_fast 9 5 5` (`384 ≤ 2^9`) and `check_sound`.
- `lean/BipartiteDD/D5New/Axioms384.lean` and `Axioms384.out.txt`: `#print axioms`. The brief names these
  `Axioms.lean` and `Axioms.out.txt`, but those files already exist for the 360 record and must not change, so the
  new ones are named with the suffix `384`.

## Build
- `lake build BipartiteDD.Graphs.G384`: 5 s.
- `lake build BipartiteDD.D5New.Record384`: 25 s (16 s for the record module itself).
- `lake build BipartiteDD.D5New.Axioms384`: 1.4 s, output as in `Axioms384.out.txt`.
- Toolchain `leanprover/lean4:v4.34.1` (elan), mathlib from `lake exe cache get`.
