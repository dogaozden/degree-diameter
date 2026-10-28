# Explicit hub graphs for every size in a range (squad gqd5-r2, card c9)

Hub graph HG5(K_B, K_A; delta): bipartite, classes A (colour 0) and B (colour 1) of sizes K_A and K_B, max degree
<= delta, any two same-colour vertices at distance <= 4. Every graph below was checked by `hub4`
(research/squads/gqd5-r2/c9/hub4.c, copy of the r1/c10 checker): simple, bipartite, connected, all same-colour
pairs within distance 4, max degree and class sizes reported. The `hub4` run is the validity check for each member.

Generator: `research/squads/gqd5-r2/c9/gen_hubs.py` (`python3 gen_hubs.py KA KB DELTA out.edges`).
Helpers: `hubgen.py` (PG(2,s), W(q), finite fields, pendant windows), `clique.py` (clique of PG cores),
`cliques_d8.json` (table: balanced K -> core orders and search seed), `check.py` (calls hub4).

## 1. Building blocks

Notation: N_s = s^2+s+1 for PG(2,s); points are A, lines are B. A pendant on an A-vertex is a new B-vertex, and vice versa.

**Lemma 1 (PG(2,s) + pendants).** Any two points of PG(2,s) are at distance 2, any two lines too, and a point and a
line are at distance <= 3. Attach to every point (resp. line) up to delta-s-1 pendants. Then a pendant of a point
is at distance 4 from every other pendant of a point (2 + 2) and at distance <= 4 from every line (1 + 3); the
symmetric statements hold for line pendants. Hence every K_A and every K_B with N_s <= K <= N_s(delta-s) is realized,
independently on the two sides (unbalanced squares), so balanced K in [N_s, N_s(delta-s)].

**Lemma 2 (W(q) + pendants).** W(q) (symplectic GQ of order (q,q)) has (q+1)(q^2+1) points and lines; incidence graph
has girth 8, point-point and line-line distance <= 4, point-line distance <= 3. Non-collinear points are at distance 4,
so pendants on arbitrary points would be at distance 6. Restrict to the q+1 points L of one line (pairwise collinear,
distance 2) for B-pendants, and to the q+1 lines through one point x for A-pendants. Each carries up to delta-q-1
pendants. Realized: balanced K in [(q+1)(q^2+1), (q+1)(q^2+1) + (q+1)(delta-q-1)].

**Lemma 3 (clique of PG cores).** Take cores C_1..C_m, C_k = PG(2, s_k) (points A-side, lines B-side), with
b_k = delta - s_k - 1 spare slots per vertex. For each ordered pair (k, j), k != j, core k picks a centre c(k,j), a
point of C_k, and a line l(k,j) of C_k. Let Pen(k,j) = lines of C_k through c(k,j) (s_k+1 lines) and Pts(k,j) =
points of C_k on l(k,j) (s_k+1 points). For each unordered pair {i,j}, add two cross-edge sets:
- E_B(i,j): join Pen(i,j) (lines of C_i) with Pts(j,i) (points of C_j). Let a = s_i+1, b = s_j+1, e = max(a,b); edge
  t (0 <= t < e) joins Pen[t mod a] and Pts[t mod b].
- E_A(i,j): join Pts(i,j) (points of C_i) with Pen(j,i) (lines of C_j), same rule.

Every core vertex receives at most b_k cross edges, so max degree <= delta.

*Proof of the hub property.* Same-core pairs are at distance 2. Let p in C_i and p' in C_j be points. The pencil
Pen(i,j) covers all points of C_i, so some line x of Pen(i,j) contains p. Edge t of E_B(i,j) gives x a neighbour q in
Pts(j,i), a set of points of C_j, and in C_j the points q and p' are at distance <= 2. Path p - x - q - (line) - p' has
length 4. Two lines m in C_i and m' in C_j: the line l(i,j) meets m at a point y; y has a cross neighbour z among the
lines of Pen(j,i) (E_A), and z meets m' at a point. Path m - y - z - (point) - m' has length 4. Pairs of points or
lines in opposite cores are handled by the other cross-edge set in the same way. (The lemma uses only: pencils cover
points, a line meets every line, and all cross edges are as stated, so any extra edges are harmless.)

For the clique of m cores with sizes N_{s_k}: K_A = K_B = sum_k N_{s_k}. Only balanced sizes come out of this lemma.

## 2. Verified ranges

All entries below were verified by `hub4` (bad = 0, valid = 1, nA = nB = K). Degrees are <= delta.

| delta | balanced K covered contiguously (verified) | sources |
|---|---|---|
| 6 | [7, 48] | PG(2,2) [7,28], PG(2,3) [13,39], PG(2,4) [21,42], W(3) [40,48] (W(2) [15,24] inside) |
| 8 | **[7, 153]** (154 open) and [155, 168] | PG windows [7,93]; W(4) [94,100]; cliques (Lemma 3) [101,153] and K=155; W(5) [156,168] |
| 9 | [7, 124] | PG(2,s), s=2,3,4,5,7,8 windows; cliques not yet extended to 125..155 |
| 10 | [7, 180] | PG windows [7,171], W(5) [172,180] |

Delta 8, the score: every balanced K in [7,153] is realized explicitly. K = 154 is not: the search failed for
[5,5,5,3,3,2,2,2,2,2], [5,4,4,4,4,3,3,3], [4,4,4,4,4,4,2,2,2,2] and the six greedy candidates of `extend.py`.
K = 154 may be infeasible for these core multisets; not proven. K = 155 = 5 x PG(2,5) (clique) is verified.

Delta 8 clique multisets used (core orders s, sizes N_s = 7, 13, 21, 31 for s = 2, 3, 4, 5), e.g. K = 101 = {5,4,4,4,2},
K = 128 = {5,5,5,4,2,2}, K = 153 = {5,5,5,4,3,3,3}. The full table is `cliques_d8.json` (sizes + seed).
Cores used in the verified table for K <= 153: at most 8 cores.

## 3. Unbalanced coverage

Unbalanced pairs (K_A, K_B) come from the windows only (Lemma 1, 2): the pair is covered iff both entries lie in one
window interval. With delta = 8 the full square {7..42} x {7..42} is covered; the first uncovered pair is (7,43).
Further covered rectangles: [13,65]^2, [21,84]^2, [31,93]^2, W(4) [85,100]^2 and others (see `unbal.py`). Clique members
are balanced only. Sample verified unbalanced members at delta 8: (K_A,K_B) = (50,77) [PG(2,4)+pendants],
(7,42), (31,93), (50,70). Delta 6 unbalanced square: {7..28}^2 (and rectangles inside [7,48]).

## 4. What is not done / caveats

- The clique members are found by a seeded randomized local search (`clique.py`, objective = total capacity overflow).
  The rules above are explicit; the particular centres and lines are the output of that deterministic search, and each
  member is BFS-verified. The search also fails for some multisets (e.g. thirteen PG(2,3) cores, 154 at delta 8), so
  "explicit" here means: rules + a reproducible seeded choice + an independent check.
- Delta 9 and 10: windows only (clique extension not run). Delta 6: cliques of PG(2,2) cores (cap 3) not tested.
- No unbalanced constructions beyond the window rectangles.

## 5. Reproduce

```
cd research/squads/gqd5-r2/c9
python3 gen_hubs.py 153 153 8 out.edges && ./hub4 out.edges      # clique member
python3 verify_windows.py 8 7 170 cliques                           # all K in the table, delta 8
python3 verify_windows.py 6 7 60; python3 verify_windows.py 9 7 130; python3 verify_windows.py 10 7 185
```
Clique table generation: `sweep_clique.py` (plan files `plan_d8.json`, `plan_d8_ext.json`), greedy extension
`extend.py`, assembly `build_table.py`.
