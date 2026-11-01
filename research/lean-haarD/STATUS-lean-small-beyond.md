# STATUS lean-small-beyond: (3,13), (3,14) and the degree-4 records at D = 11–14 in Lean

**Status: done.** All six graphs of the brief are kernel-checked, with the record statement and, in addition, the exact
degree and the exact diameter. Branch `claude/lean-graph-proofs-l7h72e`.

| Cell | Vertices | Graph | Edge list | Record theorem | Exact theorem | Build |
|---|---:|---|---|---|---|---:|
| (3,13) | 3,400 | `Z_170` lift of a 20-vertex cubic base | `research/frontier/beyond/graphs/d3D13_n3400_lift_gp10_Z170.edges.gz` | `nb_3_13_3400` | `CycLift.G3400_exact` | 13 s |
| (3,14) | 5,706 | `Z_317` lift of the Pappus graph | `research/frontier/beyond/graphs/d3D14_n5706_lift_pappus_Z317.edges.gz` | `nb_3_14_5706` | `CycLift.G5706_exact` | 10 s |
| (4,11) | 30,334 | Haar graph of `Z_523 ⋊_9 Z_29` | `research/lean-haarD/cyclift/d4D11_n30334_meta523_29_9.edges.gz` (rebuilt from the sol file) | `nb_4_11_30334` | `CycLift.G30334_exact` | 10 s |
| (4,12) | 74,066 | Haar graph of `Z_1277 ⋊_964 Z_29` | `research/frontier/beyond/graphs/d4D12_n74066_meta1277_29_964.edges.gz` | `nb_4_12_74066` | `CycLift.G74066_exact` | 11 s |
| (4,13) | 192,382 | Haar graph of `Z_2237 ⋊_1984 Z_43` | `research/frontier/beyond/graphs/d4D13_n192382_meta2237_43_1984.edges.gz` | `nb_4_13_192382` | `CycLift.G192382_exact` | 25 s |
| (4,14) | 497,042 | Haar graph of `Z_2731 ⋊_2400 Z_91` | `research/frontier/beyond/graphs/d4D14_n497042_meta2731_91_2400.edges.gz` | `nb_4_14_497042` | `CycLift.G497042_exact` | 100 s |

Statements (one per row):

    theorem nb_3_13_3400 : ∃ G : SimpleGraph (Fin 3400), IsBipartiteDegDiam G 3 13
    theorem CycLift.G3400_exact : (∀ v, (G3400.neighborSet v).ncard = 3) ∧ G3400.ediam = 13

`lean/BipartiteDD/Haar/CycLift/Axioms.out.txt`: all twelve theorems depend on `[propext, Classical.choice, Quot.sound]`.
A scan of `CycLift/*.lean` for `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, `maxHeartbeats`,
`maxRecDepth` is empty. Every certificate is `decide +kernel`.

The (4,12) record in `research/RESULTS.md` is 70,176; the 74,066 graph is the later beyond-d13 one in
`research/frontier/beyond/graphs` (checked by the coordinator on Nov 1). For (4,13) and (4,14) the proofs are for the
largest graphs there (192,382 and 497,042), not for the superseded 186,314, 490,070 and 491,294.

## Method: one search per base vertex, no tables

No all-pairs data and no word certificates. Everything runs on the base graph.

- `CycLift/Lift.lean`. A regular `Z_m`-lift is given by arc lists `outA` (`(u, β)` in row `w` means
  `(w, x) ~ (u, x + β)`); vertex `(w, x)` is `w * m + x`. The fibre rotation is an automorphism, so the distance from
  `(u₀, x)` to `(w, y)` depends only on `y - x`. The search from base vertex `u₀` keeps one `m`-bit mask per base
  vertex; a step ORs into the mask of `w` the mask of each out-neighbour rotated back by the voltage (`rotR`, three
  shifts and masks on `Nat`, which the kernel does with GMP). `bfs_sound`: bit `y - x` of the mask of `w` at radius
  `r` gives `edist (u₀, x) (w, y) ≤ r` for every `x` at once. With four base checks (arcs in range, reverse arcs,
  degree, base 2-colouring) this gives `IsBipartiteDegDiam`. Cost: `b` searches of `D` steps on `b` masks.
- `CycLift/Aut.lean`. A Haar graph of `Z_M ⋊_R Z_K` is a `Z_M`-lift of a base on the `2K` cosets: element `(a, j)`
  on side A or B goes to fibre coordinate `R^(-j) a` over `A_j` or `B_j`, and `s = (c, l)` gives the arc
  `A_j → B_(j+l)` with voltage `R^(-(j+l)) c`. Right multiplication by `(0, 1)` is the lift automorphism
  `(w, y) ↦ (π w, R⁻¹ y)` with `π` the coset shift. `autOK` checks it on the base arcs, `invOK` its inverse, `orbOK`
  that the `π`-orbits of `A_0` and `B_0` cover the base; then two searches suffice (`isBipartiteDegDiam_of_srcs`).
  For (4,14) that is 2 searches of 14 steps on 182 masks of 2,731 bits.
- `CycLift/Exact.lean`. `bfs_complete`: a walk of length `r` sets the bit at radius `r` (induction on walks), so a
  search from base vertex 0 that is not full at `D - 1` (`eccFailOK`, kernel-checked) gives a pair at distance `D`,
  and `ediam = D`. `regOK` (exactly `d` arcs per base vertex, no repeats) with the colouring gives exactly `d`
  neighbours at every vertex.

## How the Lean data is tied to the edge lists

- `research/lean-haarD/gen_cyclift.py` (the two lifts): decodes the voltages from the edge list (vertex `v` is
  `(v // m, v % m)`; every base edge carries a whole fibre), rebuilds the lift by the Lean formula and checks the edge
  set equals the file, checks simple, regular, bipartite, runs an all-pairs BFS (diameter exactly `D`), and runs the
  Python mirror of the search (full at `D`, not at `D - 1`).
- `research/lean-haarD/gen_cychaar.py` (the four Haar graphs): reads `S` from the neighbours of vertex 0, rebuilds the
  Haar graph from `S` under `(a,j)(b,l) = (a + R^j b, j + l)` and checks it equals the file (so the numbering is that of
  `build_haar2.py`), maps every file edge through the coordinate change above and checks the image is exactly the
  lift's edge set (the map is a bijection), checks `π`, `R⁻¹` and the orbits, and runs BFS from `(e, A)` and `(e, B)`.
- sha256 of the three degree-4 files in `beyond/graphs` and of the two lift files match
  `research/coordinator_check/check_2026-11-01.txt`. The (4,11) edge list was written by
  `python3 research/frontier/build_haar2.py research/frontier/sols/d4D11_meta_523_29_9_b2h01.txt OUT`
  (VALID, eccentricities 11 and 11, sha256 `13ca7af2d26ca444bc6a2bcd1dba030ceaa663269e6ec8c7074d0d71c51e542e`) and is committed gzipped in `research/lean-haarD/cyclift/`.

Commands (from the repo root):

    G=research/frontier/beyond/graphs; L=lean/BipartiteDD/Haar/CycLift
    python3 research/lean-haarD/gen_cyclift.py $G/d3D13_n3400_lift_gp10_Z170.edges.gz 170 13 3 G3400 $L/N3400.lean
    python3 research/lean-haarD/gen_cyclift.py $G/d3D14_n5706_lift_pappus_Z317.edges.gz 317 14 3 G5706 $L/N5706.lean
    python3 research/lean-haarD/gen_cychaar.py research/lean-haarD/cyclift/d4D11_n30334_meta523_29_9.edges.gz 523 29 9 11 G30334 $L/N30334.lean
    python3 research/lean-haarD/gen_cychaar.py $G/d4D12_n74066_meta1277_29_964.edges.gz 1277 29 964 12 G74066 $L/N74066.lean
    python3 research/lean-haarD/gen_cychaar.py $G/d4D13_n192382_meta2237_43_1984.edges.gz 2237 43 1984 13 G192382 $L/N192382.lean
    python3 research/lean-haarD/gen_cychaar.py $G/d4D14_n497042_meta2731_91_2400.edges.gz 2731 91 2400 14 G497042 $L/N497042.lean

## Independent checks (haiku-squad round lean-cyc-r1)

Eight Haiku cards, `research/squads/lean-cyc-r1/` (spec, code, scoreboard). They were told not to read the two
generators. c1–c6: one graph each, own parser of the `.lean` literal, own lift, edge-file comparison (Haar map for
c3–c6), BFS diameter: all six pass (all-pairs for 3,400, 5,706 and 30,334; `(e, A)`, `(e, B)` and 50 random sources for
the others). c7: line-by-line Python port of every Boolean check in `Lift.lean`/`Aut.lean`: true at `D`, false at
`D - 1`, on all six. c8: soundness attack on 7,070 mutants of the 3,400 data that keep `arcsOK` and `symOK`: 27 pass the
search at 13, all have true diameter 13 (C all-pairs BFS); no counterexample. I re-ran c1, c4, c6 and c7: same output.

## Modules (`lean/BipartiteDD/Haar/CycLift/`, all new)

| Module | Content |
|---|---|
| `Lift.lean` | `rotR`, `stepM`, `levM`, the base checks, `nbrs`, `liftGraph`, `bfs_sound`, `isBipartiteDegDiam_of_checks` |
| `Aut.lean` | `autMap`, `autOK`, `invOK`, `orbL`, `orbOK`, `eccSrcOK`, `isBipartiteDegDiam_of_srcs` |
| `Exact.lean` | `bfs_complete`, `ediam_eq_of`, `ncard_neighborSet_eq`, `exact_of` |
| `N3400.lean` … `N497042.lean` | data (`outA`, `side`, for Haar also `pi`, `piInv`) and the two theorems per graph (generated) |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` for the twelve theorems |

## Build

Elan installed from `elan-init.sh` (not preinstalled), toolchain v4.34.1, `lake exe cache get` (8,908 files, 2.5 min).
One module per `lake build`, in the foreground: `Lift` 3 s, `Aut` 2 s, `Exact` 2 s, then the six records (times in the
table; the record build includes both theorems), then `lake env lean` on `Axioms.lean`. Nothing was split or staged.

## Deviations

- Branch: the session's designated branch `claude/lean-graph-proofs-l7h72e`, not `lean-haarD-<job>`.
- `lean/Axioms.lean` is not extended (it imports every record; regenerating it means building all of them). The
  job's own `CycLift/Axioms.lean` covers the full dependency closure of the twelve theorems, as in LiftA–LiftD.
- Nothing imports `CycLift`, so the default `lake build` target is unchanged.

## Follow-up the tool makes cheap

`gen_cychaar.py` works for any Haar graph of `Z_M ⋊_R Z_K`, with kernel cost `2 · D · 2K · |S|` rotations of
`M`-bit masks. The metacyclic records of degree 5 and 6 at D = 11 and 12 in `research/RESULTS.md` (for example (5,11)
311,426 `meta 5023 31 2886`, (5,12) 1,058,342 `meta 8969 59 205`, (6,11) 2,122,518 `meta 20809 51 12972`) should go
through unchanged once their edge lists are rebuilt from the sol files. `gen_cyclift.py` handles any regular cyclic lift
with fibre-major numbering, but costs `b²` per radius, so it does not suit lifts with a large base and a small group
such as the GQ `Z_6`/`Z_10` lifts at D = 5.
