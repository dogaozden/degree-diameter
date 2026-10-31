# Status: lean-lifts (orbit reduction for the staged lift records)

Branch `claude/lean-diameter-5-lifts-oh46ul`. Every file here is new; no existing file is changed.

## The method

The records (12,5) 9,840, (13,5) 11,700, … are fibre-transitive cyclic lifts: vertex `m x + h` is in fibre `x`,
and `τ(m x + h) = m x + (h + 1) mod m` is an automorphism. The staged method stored ball masks of all `n` vertices,
which is `n²` bits per radius. The orbit reduction (`lean/BipartiteDD/Orbit.lean`) needs only the `k = n / m`
representatives `m x`:

* Orbit lemma (`ediam_le_of_orbits`): if `τ` preserves adjacency, `τ^[m] = id`, every vertex is `τ^[j] (rep i)`
  with `j < m`, and every representative is within `D` of every vertex, then the diameter is at most `D`.
  (`τ^[j]` preserves distances, so `dist(τ^[j] r, v) = dist(r, τ^[m-j] v)`.)
* Masks: bit `i` of the level-`r` mask at `v` says that representative `m i` is within `r` of `v`. A step is the
  ordinary `Fast.step`, so the staged machinery is reused. Masks are `k` bits wide instead of `n`, a factor `m` less data.
* `homOK` (Bool, Tree lookups): the shift maps each neighbour list into the list of the image. `tauF_isHom` turns
  it into adjacency preservation of `gOf adj`, using `τ^[m-1]` as inverse for injectivity.
* `lift_sound` assembles: local test (`checkLocal`, bridged by `local_spec`), shift check, staged chain, orbit lemma.

Generator: `research/lean-haarD/gen_orbit_lift.py EDGES M D FOLDER THEOREM`. It checks in Python that the
degrees are regular, the graph is bipartite, `τ` is an automorphism, and the radius-`D` masks are full; then it
writes the folder and reads the Lean adjacency lists back against the edge file.

## Records

### (12,5) 9,840, folder `D12D5GQ9Z6`, theorem `nb_12_5_n9840`

Edge file `research/d10D7/graphs/d12D5_n9840_gqdm_q9.edges.gz` (copied into the folder).
`m = 6`, `k = 1640`, `K = 14` (`2^14 ≥ 9840`), `d = 12`, `D = 5`.

Python checks (`gen_orbit_lift.py`, run 2026-10-31):
* 9,840 vertices, 59,040 edges, all degrees 12, no repeated neighbour, bipartite;
* `τ` maps every arc to an arc;
* radius-`r` masks full at 0 of 9,840 vertices for `r = 1..4`, and at all 9,840 for `r = 5`.
* Read back: the Lean adjacency lists give exactly the 59,040 edges of the edge file; the four levels read back
  equal the computed masks.

Data size: `Levels.lean` is 13 MB (four levels of 9,840 hex literals of 1,640 bits). The staged method's data for
this record was about 97 MB (`n²` bits per radius, see `STATUS-lean-gaps2.md`).

Build measurements: see the table below (filled in as each module builds).

| Module | Wall time | Peak RSS | Result |
|---|---:|---:|---|
| `Orbit` (generic, reusable) | 20 s (incremental) | — | builds, no sorry |
