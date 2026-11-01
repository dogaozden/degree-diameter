# Job beyond-small, squad round 2 — common header (read this first, then your card)

Director: Opus cloud session, branch claude/beyond-small-cells-fwb6si, 2026-11-01. Round 1: research/squads/beyond-small/r1/
(HEADER.md there has the machine rules, scorer and scoreboard format: they are unchanged; read its "Machine rules",
"Scorer" and "Scoreboard" sections). Your folder: research/squads/beyond-small/r2/<card>/, scoreboard
research/squads/beyond-small/r2/scoreboard.jsonl. The box is loaded (director checks of 3–5M-vertex graphs run in the
background): keep every command under 100 s, one thread, `timeout 100 nice -n 10`.

## Goal: (17,5) — more hubs on the (16,5) graph G (33,792 vertices, 16-regular, diameter 5)

Best so far: **33,983** = G + 191 hubs on side A (director, apsp VALID). Round 1 found the method:
- A **hub** on side A is a new vertex joined to a set N ⊆ B of old vertices (|N| ≤ 17; each old vertex is in at most one
  hub's N, so old degrees stay ≤ 17). Diameter stays 5 iff (1) every A-vertex is within distance 3 of N, (2) any two
  A-hubs h, h' have x ∈ N(h), x' ∈ N(h') with d(x,x') ≤ 2 (no shared vertex), (3) A-hubs and B-hubs are within 5 (in
  practice always true; apsp decides). Side B is symmetric (N ⊆ A covering B).
- c03's discovery: N = 4 affine fibre lines {(v, y + λc) : λ ∈ F4} (16 vertices) easily covers a whole side.
  G's numbering: A-vertex ((a_i, g), x) → (22i+g)·256 + id(x); B-vertex → 16896 + (22j+h)·256 + id(y),
  id(x) = x0 + 4x1 + 16x2 + 64x3, F4 = {0,1,w,w²} coded 0..3, addition XOR (research/theorems/graphs/build_d16D5_n33792.py).
- Director's packer `research/squads/beyond-small/director/hubpack.c` (read it; copy it into your folder to modify):
  distance-3 balls and distance-2 sets as bitsets, candidate hubs = greedy 4-line covers (6 best directions per
  controller vertex), compatibility graph (condition (2) + disjointness, density ≈ 0.937), max clique by greedy +
  1-swaps. `hubpack EDGES SIDE NCAND SECS SEED OUT` (SIDE 0 = A-hubs, 1 = B-hubs; OUT = one hub per line, global ids).
  6,000 candidates → 191 A-hubs. `director/merge_hubs.py BASE OUT HUBFILES...` appends hubs; then apsp.
- Files: G = research/squads/beyond-small/data/d16D5_n33792.edges (read-only); the 191 A-hubs:
  research/squads/beyond-small/r2/hubsA_191.txt.
- Upper limit: 16,896/16 = 1,056 hubs per side (2,112 total → 35,904). The binding constraint is (2): a random new hub
  is compatible with a given hub with probability ≈ 0.94, so random candidates stall near 200 per side.

Score = largest n with `research/squads/beyond-small/bin/apsp EDGES 17 5` → RESULT VALID. Report a hub file too.

## Ruled out in round 1 (do not repeat)
Route charts with an extra translation vector (c04–c07; c07: an extra vector cannot repair a singular pattern that uses
the extended letter once), F5 chart with deleted scalars (c08), Haar graphs (best 20,200), hexagon quotients, lifts of
W(16) (a girth argument), Z8 lifts of W(q), Theorem-D hubs at D = 6, deleting a 1-factor from (18,5), random 17-sets
for hubs (c01: 240 uncovered; lines do much better).
