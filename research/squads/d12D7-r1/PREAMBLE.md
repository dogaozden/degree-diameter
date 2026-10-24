# Squad round d12D7-r1: shared preamble (read this first)

Job "cell-12-7" (Opus director, 2026-10-24). Goal of the whole job: a **bipartite graph of maximum degree 12 and diameter 7
on more than 664,300 vertices**. Bipartite Moore bound: 3,897,434.

## What the record is (worked out by Opus before this round)

664,300 = 5 · 132,860, where 132,860 = 2·66,430 is the incidence graph of the split Cayley hexagon H(9)
(10-regular, diameter 6, girth 12). The record is the **(2j+1)-fold polygon cover**: take H(9) + j = 2 perfect matchings
σ1, σ2 (points → lines) and lift by Z_5 with voltage 0 on hexagon edges and t on σ_t (t = 1, 2). Degree 10 + 2 = 12.
Any matchings work: a copy at Z_5-distance ±t is reached with one "hop" along σ_t, taken at whichever end of the pair is
on the right side, and then ≤ 5 or ≤ 6 hexagon steps finish. Every D = 7 table value with Δ ≥ 9 has this form
(2j+1)·|H(q)| with Δ = q+1+j, e.g. (7,7) = 3·|H(5)| = 23,436, (9,7) = 3·|H(7)| = 117,648, (11,7) = 3·|H(9)| = 398,580.

## What is already known NOT to work (do not spend your card on these)

- **Random or orbit-symmetric Haar graphs**: the coupon-collector ceiling at (12,7) is 2N ≈ 522,000 (research/frontier/SIZE_LAW.md);
  the table is 1.27× above it.
- **More than 2j+1 copies of H(q)** with zero hexagon voltages: copies outside {0, ±t} need two hops, which leave ≤ 4
  hexagon steps; with isometric matchings each two-hop route covers one radius-4 ball (≈ 1/q of a copy).
  Calibration with tools/pcover (random matchings, D = 7, T = {1,2}): H(2) over Z_6 cost 0; H(3) over Z_6 cost 69;
  H(4) over Z_6 cost 14,645. It gets worse with q; at q = 9 it is hopeless.
- **Lifts of the record** by any group ≠ 1 (Opus lemma): a generic same-side pair in different copies is joined by
  exactly 3 walks of length ≤ 6 (one hop at one of the 3 points of a hexagon geodesic). Two-colouring every line's
  q+1 points then forces ≥ q−1 "repeated" points per line against ≤ 1 per point, impossible for q ≥ 3.
- **Route-chart lifts** (controller × fibre F_q^6, research/theorems/BEAT_16_5_SQUAD.md on branch claude/beat-16-5-squad-jiiwg2):
  at Δ = 12 = 3·4 the cubic controller needs ≥ 82 vertices per side with a 6-cycle through every vertex; the only cubic
  D = 7 graph that big is Conder's 168-vertex graph, which has girth 12.
- **Weyl-distance graphs of buildings** (every type to rank 7, q ≤ 11, every residue pair and union of double cosets):
  none with Δ ≤ 12, D ≤ 7 above 300,000 vertices except H(11) itself (354,312, D = 6).
- **Doubling a general graph**: 2·n(11,6) = 2·186,033 = 372,066.

The counting rule behind all of this: from any vertex there are at most 1,948,717 nonbacktracking walks of length ≤ 6,
and every same-side vertex (more than 332,150 of them) must be the end of one. The record covers 17 % of the walks'
ends; random-like constructions manage about 11–13 %. **Anything that beats the record must be structured.**

## Tools (in research/squads/d12D7-r1/tools/, built; bases in ../bases/)

- `gh_fast.py q OUT [check]`: H(q) incidence structure, q ≤ 9 (polygons.py format: first line P, then one line per
  hexagon line with its q+1 point ids). Ready: `bases/gh{2,3,4,5,7,8,9}.txt`.
- `polygons.py`: also `pg q` (projective plane) and `gq q` (W(q)).
- `pcover BASE D M seed iters T1 .. Tj` (env OUT=file to save matchings, TEMP0/TEMP1): anneals the j matchings of a
  polygon cover over Z_M; prints `RESULT best <cost>` (cost = uncovered lifted pairs over all base sources).
- `apsp EDGES d D`: independent all-pairs check of an edge list (first line n, then "a b" per edge): degree, bipartite,
  exact diameter. Use it on every graph you claim. `bfs_all EDGES` also exists.
- `mlift`: voltage annealer for 4-regular bases (see its header) – mostly for reading.
- Python 3 with numpy; gcc. No networkx unless you check it is installed.

## Rules (shared machine: 4 cores, 15 GB, shared with 7 other cards and Opus)

- THREADS=1, `timeout 900 nice -n 10 <cmd>` for anything heavy, at most about 1.5 GB of memory.
- Work only inside your card folder `research/squads/d12D7-r1/<card>/` (you may read anything). No git commands.
- Time box: about 15 minutes of compute.
- **Scoreboard**: append exactly ONE line of JSON to `research/squads/d12D7-r1/scoreboard.jsonl`:
  `{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false, "next": "<one line>"}`
  Use `>>` (append) from a single `echo` or `printf`, never rewrite the file.
- Then reply to Opus in at most 5 lines: the score, whether it was checked with apsp, and the one thing you learned.
- A "valid" claim needs an apsp (or equivalent independent BFS) check of the actual graph. Say so if you did not.
