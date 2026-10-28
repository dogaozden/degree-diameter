# Squad polylev r1 (director: Opus, job thm-polygon-levels, 2026-10-28)

Read this header, then your card. Work ONLY in `research/squads/polylev/r1/<card>/` (create it). No git commits, no
edits outside your folder. Machine: 4 cores shared with the director and 15 other cards, so: one thread, every heavy
command as `timeout 1200 nice -n 10 <cmd>`, at most 1.5 GB of memory. Time box: about 25 minutes of work.

## The construction (proved by the director; do not re-prove it)

H(q) = split Cayley hexagon, N = (q^6-1)/(q-1) points and N lines, incidence graph I (bipartite, (q+1)-regular,
diameter 6, point-line distances <= 5). The **2-ball** of a point p is the set of q^2+q+1 points equal or collinear to p
(the plane pi_p); the 2-ball of a line l is l plus the q^2+q lines meeting it.

**D = 9 ball lift.** Colour the points by k colours so that every point 2-ball sees all k colours (each colour class is a
dominating set of the collinearity graph), and the lines by the same k colours so that every line 2-ball sees all k
colours, with **equal class sizes** on both sides (|point class i| = |line class i|; elements may also stay uncoloured,
-1, as long as sum_i max(|A_i|, |B_i|) <= N). Then for every r >= 1 there is a bipartite (q+1+r)-regular graph of
diameter <= 9 with 2N(2rk+1) vertices. So the whole game is: **large k, on both sides, with equal class sizes.**
k <= q^2+q+1 (equality = partition into ovoids and spreads, impossible at q = 3).

**D = 11 ball lift.** Same with 4-balls (elements at distance <= 4 of the same type). Every hexagon line's point set
meets every point 4-ball, and every pencil (the q+1 lines through a point) meets every line 4-ball. So K pairwise
disjoint lines (a partial distance-2 spread) plus K pairwise non-collinear points (a partial distance-2 ovoid) give K
balanced classes of size q+1, and 2N(2rK+1) vertices, degree q+1+r, diameter <= 11. K <= q^4+q^2+1.

## Record thresholds (lab's current values; beat them)

D = 9, k needed: q=8: Delta 10 k>=53, Delta 11 k>=56. q=9: Delta 11 k>=63, Delta 12 k>=64, Delta 13 k>=85.
q=11: Delta 13 k>=96, Delta 14 k>=82, Delta 15 k>=98. q=13: Delta 15 k>=129, Delta 16 k>=105, Delta 17 k>=104,
Delta 18 k>=123, Delta 19 k>=152. q=16: Delta 18 k>=177, Delta 19 k>=136, Delta 20 k>=136.
D = 11, K needed (r = 1): q=7 (Delta 9) K>=1852 of 2451; q=8 (Delta 10) K>=2975 of 4161.

## Tools (all in research/theorems/polylev/, binaries in bin/, hexagons in hex/hex_q{2,3,4,5,7,8,9,11,13}.bin)

- `hexlib.py` (Python loader: H.lines (N x (q+1) point ids), H.PL (lines through each point), H.coord, field tables).
- `bin/domlocal HEX lines|points k s SEED SECONDS OUT [bal]`: local search for k dominating classes (s = 2 or 4);
  writes an int32 colour per element (-1 free) when it reaches cost 0.
- `bin/translocal HEX PERM lines|points SEED SECONDS OUT [A] [fixed]`: colourings equivariant under a semiregular
  group T = <h> of order d given by the permutation file PERM (.pperm for points, .lperm for lines); k = A*d colours;
  `fixed` keeps the same number of orbits in each block, so a point run and a line run with the same A have EQUAL class
  sizes (that is the balance the lift needs). Groups available in grp/: T_q{3,4,7,9} (order q^2-q+1), S13_q9, S7_q9,
  S7_q11, S19_q11, S61_q13 (Singer subgroups; may still be generating when you start: wait for the .pperm file).
- `bin/orblocal HEX PERM lines|points k SEED SECONDS OUT`: colourings constant on the T-orbits.
- `singer_perms.py HEX e OUT` (Singer element g of SL(3,q), writes perms of g^e), `g2.py` (finds a semiregular cyclic
  group of order q^2-q+1 in G2(q)), `domsat.py`, `transsat.py` (SAT versions; slow beyond q = 4).
- `lift9.py HEX POINTCOL LINECOL k r seed OUT.edges` builds the lift; `bin/apsp OUT.edges Delta D` checks it all-pairs.
- `perfcodes.c` / `bin/perfcodes` (spreads/ovoids), `packing.py`, `spreadT.py`.
- research/gh6/ils_mis.c: iterated local search for a maximum independent set (`ils_mis graph.txt seconds seed`).

## Scorer

`python3 research/theorems/polylev/domcheck.py HEX POINTCOL LINECOL s` (s = 2 for D = 9, 4 for D = 11) prints k, the
balance check and the orders. A colouring of only one side: give the same file twice to see that side's count.

## Already found / already ruled out (do not repeat)

- Found: q=3 k=10 (one side, domlocal); q=3 k=7 and q=4 k=13 both sides via T (q^2-q+1); q=3 D=9 lift checked
  all-pairs (diameter 9, r = 1, 2); the duality of H(9) (parts/dual_q9.phi) maps point classes to line classes, so at
  q = 9 only the POINT side is needed.
- Ruled out: perfect partitions at q=3 (H(3) has 6,318 spreads, no partition; at most 2 pairwise disjoint);
  Hermitian spreads of H(9) are never disjoint from their T73-translates (overlap 10); T-equivariant k = q^2-q+1 at
  q=7 (points, cost >= 2,240) and q=9 (cost about 11,000); T73-orbit-invariant k=60 at q=9 (cost 3,378).
- Director is running: q=9 points with S13 (A=5, k=65) and S7 (A=9, k=63) block colourings, and free domlocal k=64.

## Report

Append ONE line of JSON to `research/squads/polylev/r1/scoreboard.jsonl`:
`{"card": "cNN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <k or K reached at cost 0, or
best cost if none>, "valid": true|false, "next": "<one line>"}` and reply in at most 5 lines.
