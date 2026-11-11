# h1 notes (card h1: 684 graph + one vertex pair, by design)

Code: h1.c (built as ./h1; scorer ./score65 = shared/score65.c, ./apsp = shared/apsp.c, both built here).
Model: base = shared/h684.edges (A = 0..341, B = 342..683). Delete a matching of K edges (x_i,y_i); a = 684 (side A)
gets y_i; b = 685 (side B) gets x_i; optional a-b edge (AB=1). Env: AB=0/1 (a-b edge), NA / NBX (how many deleted
edges attach a / b, default all). bad = pairs at distance > 5 (exact bit-parallel BFS, equals score65; checked on 3 files).
Speed: about 6400 exact evaluations per second on one core.

## Results (bad pairs, lower is better; 144 = best known)
| family | search | best bad |
|---|---|---|
| K=6, AB=0 (a~6 y, b~6 x, no a-b) | SA, 5 seeds, T0 8..40 -> 0.4..1, 85-95 s each | 144 (all 5 seeds) |
| K=6, AB=0 | beam width 25 | 168 |
| K=6, AB=0, all six x_i = N(w) (star6, all 46656 tuples) | exhaustive | 205 |
| K=6, AB=0, b attached to only 5 x (NA=6 NBX=5) | SA 80 s | 176 |
| K=6, AB=0, 12-cycles x1 y1 .. x6 y6 through x1=0 | random DFS, 403k cycles | 161 |
| K=5, AB=1 (card family, a~b) | SA, 3 runs 60-95 s | 150 (seed 3), 152, 153 |
| K=5, AB=1 | beam W=12 / W=40 | 154 / 154 |
| K=5, AB=1 | star (i): x_1..x_5 in N(w), all 37500 tuples | 187 |
| K=5, AB=1 | alternating 10-cycles through x1=0 (ii), all 30030 | 178 |
| K=5, AB=0 | SA 80 s | 158 |
| K=4, AB=0 / AB=1 | SA 45 s | 183 / 170 |
| K=3, AB=0 / AB=1 | SA 40 s | 234 / 211 |

Best design (K=6, AB=0), edges x_i:y_i (A:B vertex ids in shared/h684.edges numbering):
  46:380 89:474 289:511 84:418 325:468 4:455 ; file best144_k6.edges (686 vertices, 2058 edges, score65 bad=144).
  Other 144 designs from seeds 5, 7, 12, 17 have the same breakdown (not identical sets).

Breakdown of the 144 design (before insertion, the 6 deletions damage 294 old pairs; ~49 per deletion):
  unrepaired old pairs = 117, all same-side with base distance 4; by kind (near,far) of the deleted edge on a base
  shortest path: (0,3): 54, (1,2): 63; cross-side old pairs unrepaired: 0.
  new bad pairs = 27: a with 15 A-vertices (a-A), b with 12 B-vertices (b-B); none cross.
  repaired = 177.
The 144 design is a 1-exchange local optimum (best neighbour 145, 3 ties; `./h1 nbr 6 ...`).
Plateau walk from it at T=1.0-1.2 (85 s) stayed at 144.

## Commands (all single-threaded, each under 105 s)
  AB=0 ./h1 sa 6 90 4 15 0.5 k6a.edges   -> 144 (and seeds 5, 7, 12, 17 with other T0/T1, also 144)
  ./h1 star 95; AB=0 ./h1 star6 95; ./h1 cycle 90; AB=0 ./h1 cycle6 80 1
  ./h1 beam 5 40 bm40.edges; AB=0 ./h1 beam 6 25 bk6.edges
  ./h1 sa 5 95 2 10 0.3 s2.edges ; ./h1 sa 5 95 3 40 1 s3.edges
  AB=0 ./h1 sa 5 80 6 15 0.5 k5a.edges ; AB=0 ./h1 sa 4 45 8 ... ; AB=1 ./h1 sa 4 45 9 ... ; sa 3 40 ...
  NA=6 NBX=5 AB=0 ./h1 sa 6 80 15 15 0.5 k6f.edges -> 176

Not done: apsp (only needed at bad=0); 2-exchange or tabu beyond SA (too costly in the time box).
Conclusion: within this card's family (matching deletions + a,b attachments) SA reaches 144 repeatedly and
nothing below it was found. The gain over the card's a-b design (150) comes from dropping a-b and using degree 6 on both a and b.

## Later checks
- 2-exchange on the 144 design: `AB=0 T=120 ./h1 two 6 46 380 89 474 289 511 84 418 325 468 4 455` evaluated 198,804 pairs
  of replacements drawn from the top 120 single-exchange edges: best 144. `T=200`: 569,834 evaluated, best 144.
- Half-attached variant NA=6 NBX=5 (b degree 5): 176. Full-attachment K=6, AB=0 (both degree 6) is the best found.
- Scoreboard: appended the 144 line and a final line to ../scoreboard.jsonl.
