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

Build measurements (each module built with its own `lake build`, one at a time; wall time and the peak RSS of the
largest child, from `scratchpad/memrun.py`, since `/usr/bin/time` is not installed here; 4 cores, 15 GB):

| Module | Wall time | Peak RSS | Result |
|---|---:|---:|---|
| `Orbit` (generic, reusable; incremental rebuilds after each change) | ~20 s | — | builds, no `sorry` |
| `Graph` (adjacency and colour literals, 9,840 vertices) | 482 s | 4.23 GB | ok |
| `Levels` (4 levels, 13 MB; final build) | 236 s | 3.10 GB | ok |
| `Local` (checkLocal in 4 quarters + 2 joins; final build) | 514 s | 10.20 GB | ok |
| `Hom` (shift check, 8 pieces + 7 joins) | 210 s | 3.83 GB | ok |
| `Stage0` | 191 s | 12.56 GB | ok (its wrapper also rebuilt `Levels`, 215 s, after the `Orbit` change) |
| `Stage1` | 254 s | 12.45 GB | ok |
| `Stage2` | 188 s | 12.46 GB | ok |
| `Stage3` | 161 s | 12.47 GB | ok |
| `Stage4` | 176 s | 12.51 GB | ok |
| `Record` (elaboration only) | 5 s | 1.74 GB | ok |
| `Axioms` (`lake env lean`) | — | — | `propext, Classical.choice, Quot.sound` |

The stage modules peak near 12.5 GB, close to the 15 GB of this sandbox. That is the kernel's cost of one `decide`
step over 9,840 vertices with 1,640-bit masks; it is the limit to watch for the larger records.

### Failures on the way (kept here, not in the code)

* `Levels`: the first build failed on the default heartbeat budget and recursion depth in the big list literals
  (`maximum recursion depth`, `isDefEq` timeouts). Fixed by `maxHeartbeats 0` and `maxRecDepth 1000000` before each
  level definition.
* `Local`: the two-half check (one `decide +kernel` per half) peaked at 12.85 GB. Quarters peaked at 10.20 GB. The
  join was first written with literal ranges, `checkLocalRange … 0 4920`, and the defeq check of `2460 + 2460 =?= 4920`
  inside `checkLocalRange` hit the recursion limit. Fixed by `checkLocalRange_join`, which takes the offsets and
  totals as equations proved by `decide`, and the chain was first tested in a scratch file.
* `Hom`: the one-shot `homOK` over 9,840 vertices was killed at 13.13 GB (exit −9). Fixed by the range form
  `homOKRange` and eight pieces with `homOKRange_join`.
* `Local`, `Record`: `by norm_num` is not available in these modules (`unknown tactic`); replaced by `by decide`.
* `Record`: the generator's loop variable overwrote `k` (it set `k = 7`) in the new `Hom` section. Caught by the diff
  before any build, fixed, and regenerated.
* `Axioms`: `#print axioms` needs the qualified name `BipartiteDD.Haar.D12D5GQ9Z6.nb_12_5_n9840`.

### (13,5) 11,700, folder `D13D5W8Z10`, theorem `nb_13_5_n11700`

Edge file `research/frontier/beyond/graphs/d13D5_n11700_W8_2dm_Z10.edges.gz` (Z10 lift of W(8), 13-regular, 76,050 edges).
`m = 10`, `k = 1170`, `K = 14`, `d = 13`, `D = 5`. The generator checked: shift automorphism, radius-5 masks full at
all 11,700 vertices, Lean adjacency lists equal to the edge file.

| Module | Wall time | Peak RSS | Result |
|---|---:|---:|---|
| `Graph` | 686 s | 5.05 GB | ok |
| `Levels` | 202 s | 3.27 GB | ok |
| `Local` (4 quarters) | 634 s | 11.90 GB | ok |
| `Hom` (10 pieces) | 255 s | 3.88 GB | ok |
| `Stage0` | 212 s | 13.08 GB | ok |
| `Stage1` | 267 s | 13.08 GB | ok |
| `Stage2` | 224 s | 13.08 GB | ok |
| `Stage3` | 216 s | 13.08 GB | ok |
| `Stage4` | 225 s | 13.08 GB | ok |
| `Record` | 8 s | 1.73 GB | ok |

Axioms (`D13D5W8Z10/Axioms.out.txt`): `propext, Classical.choice, Quot.sound`.

The stage peak is 13.08 GB, up from 12.5 GB at n = 9,840. It grows with n, so the next record (n = 17,568) needs the
stage step split into vertex ranges before it can be checked in this sandbox.

### (14,5) 17,568, folder `D14D5GQ11Z6` (attempted, NOT proved)

Edge file `research/d10D7/graphs/d14D5_n17568_gqdm_q11.edges.gz`. The lift is Z6 (`lift vertex (x, h) = 6x + h`, from its
CHECK note), not Z12: `m = 6`, `k = 2928`, `K = 15`, `d = 14`, `D = 5`. The generator's checks pass (shift automorphism,
radius-5 masks full, Lean lists equal the edge file). `Levels.lean` is 42 MB.

| Module | Wall time | Peak RSS | Result |
|---|---:|---:|---|
| `Graph` | 1,766 s | 8.37 GB | ok |
| `Levels` | 1,098 s | 4.07 GB | ok |
| `Stage0` | 210 s | 13.05 GB | **killed by the kernel (exit 137, out of memory)** |

The stage check on the whole vertex set does not fit in this sandbox at n = 17,568 with 2,928-bit masks. Next step:
split each radius step by vertex ranges (`step` restricted to `lo ≤ v < lo + cnt`, with an append lemma, as `checkLocalRange`
and `homOKRange` already do for the local and shift checks), so that each kernel check holds a fraction of the list.
The `Graph`, `Levels`, `Local` and `Hom` parts are not affected by this. The generated `Stage*.lean` files and `Record.lean`
in this folder are not verified and must not be cited.

### Status

* (12,5) 9,840: **proved**. `BipartiteDD.Haar.D12D5GQ9Z6.nb_12_5_n9840 : ∃ G : SimpleGraph (Fin 9840), IsBipartiteDegDiam G 12 5`,
  axioms `propext, Classical.choice, Quot.sound` (`D12D5GQ9Z6/Axioms.out.txt`).
* Data: `Levels.lean` is 13 MB (four levels of 9,840 hex literals of 1,640 bits), against about 97 MB for the staged
  method on the same record.
* (13,5) 11,700: **proved** (`BipartiteDD.Haar.D13D5W8Z10.nb_13_5_n11700`, same axioms).
* (14,5) 17,568: attempted; `Stage0` ran out of memory (see above). Not proved.
* Not done: (15,5), (16,5), (18,5). Each needs its own generator run and builds. The same method
  applies to the fibre-transitive ones; (15,5) and (16,5) are route-chart lifts and may need a different
  numbering. The data is about n²/m bits per radius, so the larger records are heavier in data and in the
  stage memory (which grows with n).
