# Round lean-cyc-r1: independent checks of the CycLift Lean data

Goal: confirm, with code you write yourself, that each Lean data file in `lean/BipartiteDD/Haar/CycLift/N<n>.lean`
defines exactly the graph of its edge list, with the stated degree and diameter. Do NOT read or run
`research/lean-haarD/gen_cyclift.py` or `gen_cychaar.py` (they wrote the files; the point is an independent check).

## What the Lean file says (the semantics to implement)
- `def outA<n> : List (List (ℕ × ℕ)) := [ [(u, β), ...], ... ]` — line w of the literal is the arc list of base vertex
  w (0-based). Parse it from the .lean text (regex on `(\d+), (\d+)` inside each `[...]` row).
- `liftGraph n m outA`: vertices 0..n-1, n = b*m (b = number of rows, m = the modulus in `liftGraph <n> <m> outA<n>`).
  Vertex v has base vertex w = v // m and fibre x = v % m; its neighbours are `(u*m + (x + β) % m) % n` for each
  (u, β) in row w. The graph is the symmetric closure without loops.
- Edge files: gzip text, first line n, then "a b" per edge.

## Graphs
| card | Lean file | edge file | m | stated degree, diameter | numbering of the edge file |
|---|---|---|---|---|---|
| c1 | N3400.lean | research/frontier/beyond/graphs/d3D13_n3400_lift_gp10_Z170.edges.gz | 170 | 3, 13 | same as the lift |
| c2 | N5706.lean | research/frontier/beyond/graphs/d3D14_n5706_lift_pappus_Z317.edges.gz | 317 | 3, 14 | same as the lift |
| c3 | N30334.lean | research/lean-haarD/cyclift/d4D11_n30334_meta523_29_9.edges.gz | 523 | 4, 11 | Haar, M=523 K=29 R=9 |
| c4 | N74066.lean | research/frontier/beyond/graphs/d4D12_n74066_meta1277_29_964.edges.gz | 1277 | 4, 12 | Haar, M=1277 K=29 R=964 |
| c5 | N192382.lean | research/frontier/beyond/graphs/d4D13_n192382_meta2237_43_1984.edges.gz | 2237 | 4, 13 | Haar, M=2237 K=43 R=1984 |
| c6 | N497042.lean | research/frontier/beyond/graphs/d4D14_n497042_meta2731_91_2400.edges.gz | 2731 | 4, 14 | Haar, M=2731 K=91 R=2400 |

Haar numbering (research/frontier/build_haar2.py): N = M*K; group element (a, j), a < M, j < K, has index a*K + j;
(g, A) is vertex idx(g), (g, B) is vertex N + idx(g). The claimed map to the lift: (a, j) on side A goes to
lift vertex j*M + (R^(-j) * a mod M); on side B to (K + j)*M + (R^(-j) * a mod M). (R^(-j) is the inverse of R^j mod M.)

## Checks for c1–c6 (one graph each)
1. Parse outA; build the lift's edge set; check n, simple, no loops, every vertex has exactly the stated degree.
2. Lifts (c1, c2): lift edge set == edge-file edge set. Haar (c3–c6): apply the map above to every edge of the file
   and check the mapped set == lift edge set, and that the map is a bijection on vertices.
3. Bipartite (BFS 2-colouring).
4. Diameter. c1, c2: BFS from every vertex; the maximum eccentricity must be exactly the stated D. c3–c6: BFS in the
   edge-file graph from vertex 0 and from vertex N (the group acts transitively on each side, so these two give the
   diameter); the max must be exactly D. Also BFS from 50 random other vertices as a sanity check (all ≤ D).
Score = 1 if every check passes, else 0 (say which failed).

## c7: port the Lean checks literally
Read `lean/BipartiteDD/Haar/CycLift/Lift.lean` and `Aut.lean` and port `rotR`, `stepM`, `levM`, `eccOK`, `arcsOK`,
`symOK`, `degOK`, `colOK`, `autOK`, `invOK`, `orbL`, `orbOK`, `eccSrcOK` to Python line by line (Nat semantics:
`a - b` truncates at 0; `&&&`, `|||`, `>>>`, `<<<` are bitwise). Evaluate them on all six data files with the exact
arguments of each file's theorem (N3400/N5706 use `isBipartiteDegDiam_of_checks`; the Haar ones use
`isBipartiteDegDiam_of_srcs` with pi/piInv/μ/μ'/K/srcs from the file). All must be true; then evaluate `eccOK` /
`eccSrcOK` at D−1: must be false. Score = number of the six files where all checks behave as stated.

## c8: try to break it (soundness attack)
Using your own Python port of `eccOK`, `arcsOK`, `symOK` from Lift.lean (write it yourself), take N3400's outA
and try ≥ 2000 random mutations (change one voltage, swap two arcs, change an arc target, while keeping arcsOK and
symOK true by mutating an arc and its reverse together). For each mutant where your port of eccOK at D=13 is true,
compute the real diameter of the mutant lift by BFS from every vertex (3400 vertices). A counterexample is a mutant
with eccOK true but real diameter > 13. Score = number of counterexamples (expected 0); also report how many
mutants passed eccOK at all.

## Machine rules
About 4 cores and 15 GB are shared: one thread; `timeout 900 nice -n 10 python3 ...`; at most about 1.5 GB of memory;
no git commits; write only inside `research/squads/lean-cyc-r1/<card>/`. Time box about 15 minutes.

## Scoreboard
Append ONE line of JSON to `research/squads/lean-cyc-r1/scoreboard.jsonl`:
`{"card": "c5", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false,
"next": "<one line>"}` and reply in at most 5 lines.
