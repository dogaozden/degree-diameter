# STATUS lift38: Δ3·D8 record on 288 vertices

**Status: done.** `nb_3_8_288` is kernel-checked.

    theorem nb_3_8_288 : ∃ G : SimpleGraph (Fin 288), BipartiteDD.IsBipartiteDegDiam G 3 8

Axioms (`lean/BipartiteDD/Haar/LiftD/Axioms.out.txt`): `'nb_3_8_288' depends on axioms: [propext, Classical.choice, Quot.sound]`.
A scan of `lean/BipartiteDD/Haar/LiftD/*.lean` for `sorry`, `admit`, `native_decide` and `axiom` is empty.

## The record
- Voltage lift of the 4-vertex cubic base graph (edges 0–2 twice, 0–3, 1–2, 1–3 twice) over `G = Z3^2 ⋊_M Z8`,
  `M = [[0,2],[1,0]]`, product `(v,j)(w,l) = (v + M^j w, j + l)`. Voltages from
  `research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt`.
- Vertices `72·u + x + 3y + 9j` for base vertex `u < 4`, `(x,y,j) ∈ G`. Edge `(u,g) ~ (w, gα)` for each base edge with voltage `α`;
  the backward direction uses `α⁻¹`, listed next to `α` in `baseEdges`.
- Simple, 3-regular, 432 edges, bipartite (colour = base side `{0,1}` / `{2,3}`), diameter exactly 8.

## Route
- Same route as the small October 10 records: `Basic.check_sound` with `Fast.check_of_fast` (the kernel-friendly check of
  `Fast.lean`). `Fast.checkFast 9 3 8 adjL colL` is evaluated by `decide +kernel`; `2^9 = 512 ≥ 288`.
- The graph is defined from the formula (`LiftD/Formula288.lean`), with no generated table. The record is about that
  definition, so the voltage rule is what the kernel checks.

## Modules (`lean/BipartiteDD/Haar/LiftD/`)
- `Formula288.lean`: `mpow`, `gmul`, `gdec`/`genc`, `baseEdges` (with inverse voltages), `nbrNat`, `adjL`, `colL`.
- `Record288.lean`: `nb_3_8_288`.
- `Sanity.lean`: `checkFast` rejects the broken variants (diameter 7, degree 2, constant colouring); each `decide +kernel` proves a `= false`.
- `Axioms.lean`, `Axioms.out.txt`: the axiom check.

## Cross-checks
- `research/lean-haarD/lift38/lift38_check.py` builds the lift independently in Python and checks it: 288 vertices, 432 edges,
  simple, 3-regular, bipartite, eccentricity ≤ 8 from every vertex (max = 8). It also checks the inverse voltages.
- `#eval` of `Formula288.adjL` and `python3 lift38_check.py dump` give the same sorted neighbour list for all 288 vertices.

## Build
- `lake exe cache get`: ok (8908 files). Elan 4.x installed into `~/.elan` (not preinstalled here); toolchain v4.34.1.
- Modules built one at a time: `Table288` was built and then dropped; `Formula288`, `Record288` (34 s), `Sanity` (11 s); then `lake env lean` on `Axioms.lean`. All exit 0.

## Deviations from the brief
- **Branch.** The brief said `lean-haarD-lift38`. The session's designated branch is `claude/nb-3-8-288-lift-xzwgs1`, and that is where this was pushed.
- **No stage modules.** The brief expected a stage split. The whole check is one `decide +kernel` taking about 30 s, so nothing was split.
- **No generated table.** An earlier version used a Python-generated neighbour table. It was replaced by the formula, so the record does not depend on a generator.
- **Axioms.** `lean/Axioms.lean` was not extended, because it imports every record (see D9D8c). The check lives in `LiftD/Axioms.lean`.
- **Attribution.** The `Co-Authored-By` line naming the model is left out of the commits, because the system instructions bar model identifiers in commits. The `Claude-Session` trailer is included.

## Largest stage that built
Single module: `Record288` (the whole `decide +kernel` check).
