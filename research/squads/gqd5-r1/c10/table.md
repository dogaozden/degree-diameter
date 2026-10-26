# Hub graphs at D = 5 (squad gqd5-r1, card c10)

Hub graph: bipartite Y, colour classes K_A, K_B, max degree <= delta, every two same-colour vertices at distance <= 4 (in Y).
Every graph below was checked by `hub4` (research/squads/gqd5-r1/c10/hub4.c): simple, bipartite, connected, all
same-colour pairs within distance 4 (BFS to depth 4 from every vertex). Balanced means K_A = K_B = K.

## (1) Explicit families, balanced K (all verified by hub4, bad = 0)

Families: K_{d,d} and C_10 (small cases); PG(2,p) incidence (p prime), and with one pendant per vertex (degree s+2, balanced);
incidence graph of GQ W(q) (order (q,q), K = (q+1)(q^2+1), degree q+1); level graph of (2r+1) copies of the W(q) incidence graph
with all levels type H and cyclic random bijections M_(j,k), k = 1..r, degree q+1+r, K = (2r+1)(q+1)(q^2+1).
Level graphs with r = delta - q - 1 are the largest members for each q.

| delta | best balanced K (explicit) | family | GQ incidence alone (best) | level graphs (best two) | PG(2,p) incidence / with pendants (p prime) |
|---|---|---|---|---|---|
| 2 | 5 | C_10 | - | - | - |
| 3 | 15 | GQ W(2) incidence | 15 (W(2)) | - | 7 / - |
| 4 | 45 | level W(2), r=1 (3 copies) | 40 (W(3)) | 45 (W(2) r=1) | 13 / 14 (PG(2,2)+pendants) |
| 5 | 120 | level W(3), r=1 (3 copies) | 85 (W(4)) | 120 (W(3) r=1), 75 (W(2) r=2) | - / 26 (PG(2,3)+pendants) |
| 6 | 255 | level W(4), r=1 (3 copies) | 156 (W(5)) | 255 (W(4) r=1), 200 (W(3) r=2) | 31 / - |
| 7 | 468 | level W(5), r=1 (3 copies) | 156 (W(5)) | 468 (W(5) r=1), 425 (W(4) r=2) | - / 62 (PG(2,5)+pendants) |
| 8 | **780** | level W(5), r=2 (5 copies) | 400 (W(7)) | 780 (W(5) r=2), 595 (W(4) r=3) | 57 / - |
| 9 | 1200 | level W(7), r=1 (3 copies) | 585 (W(8)) | 1200 (W(7) r=1), 1092 (W(5) r=3) | 57 / 114 (PG(2,7)+pendants) |
| 10 | 2000 | level W(7), r=2 (5 copies) | 820 (W(9)) | 2000 (W(7) r=2), 1755 (W(8) r=1) | 57 / 114 (PG(2,7)+pendants) |
| 11 | 2925 | level W(8), r=2 (5 copies) | 820 (W(9)) | 2925 (W(8) r=2), 2800 (W(7) r=3) | 133 / - |
| 12 | 4100 | level W(9), r=2 (5 copies) | 820 (W(9)) | 4100 (W(9) r=2), 4095 (W(8) r=3) | 133 / - |

PG(2,p) with pendants: one pendant at every point (line class) and at every line (point class), degree p+2, K = 2(p^2+p+1). Never the best.
Column "level graphs" lists the two largest level-graph members for the delta (the W(2) r=1 entry for delta 4 is 45, verified).
W(q) for q = 2,3,4,5,7,8,9 from gqlib.W. The score for delta = 8 is 780.

Note: a level graph with L = 2r+1 levels keeps the hub property when only a consecutive prefix of levels is kept
(verified for W(5) r=2 at 156, 312, 468, 624, 780; W(4) r=3; W(9) r=2), giving K = m(q+1)(q^2+1) for m = 1..2r+1, all verified.

## (2) Random delta-regular bipartite K+K (union of delta random perfect matchings; dense cases fall back to a random maximal graph with max degree <= delta)

Largest K with success in at least 1 of 10 trials (script random_threshold.py, log random_threshold.log):

| delta | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| max K | 5 | 13 | 29 | 57 | 108 | 178 | 271 | 413 | not finished | not finished | not finished |

delta 10-12 were not finished within the time box (search killed). Values for delta 2-9 are in random_max.json and random_threshold.log. The delta 10-12 values are not measured.

## (3) Are all K in [1, max] reachable?

- delta = 8, random: a random maximal K+K graph (max degree <= 8) passed for every K in 1..275 and for 277..280 (coverage.py, random_reached_count = 279 of 280).
  K = 276 failed in 10 trials (not disproved; more seeds would likely find one). So K in [1, 275] is reached (verified), and random graphs give no K above about 275-280.
- delta = 8, explicit: reached values are 780 (W(5) r=2), 595, 400, 360, 255 etc. and the prefixes 156, 312, 468, 624, 780 of the level graph.
- Gap: K in (280, 780] apart from those prefix/family values is NOT reached by this squad. Greedy deletion of one (A,B) vertex pair at a
  time from the 780 graph fails immediately (15 random pairs per step all break a same-colour distance), so the level graph is tight.
  Dropping whole levels works (see above), but partial levels were not tested.
- So at delta = 8: all K in [1, 275] (plus 277..280), then 312, 360, 400, 468, 595, 624, 780 are reached; the other K in between are unresolved.

## Unbalanced examples (verified by hub4; edge lists in the c10 folder)

- K_B = 126, K_A = 115, delta = 8: random maximal bipartite graph with max degree <= 8 (seed 0), 920 edges.
  File: research/squads/gqd5-r1/c10/unbalanced_KB126_KA115_d8.edges (first line comment gives class sizes).
  hub4: valid, nA = 115, nB = 126, maxdeg = 8, bad = 0.
- K_B = 86, K_A = 77, delta = 6: random maximal graphs (3000 seeds) all failed; obtained from a 6-regular 86+86 random graph
  (union of 6 random matchings) by deleting 9 A-vertices (seed 40). 462 edges.
  File: research/squads/gqd5-r1/c10/unbalanced_KB86_KA77_d6.edges.
  hub4: valid, nA = 77, nB = 86, maxdeg = 6, bad = 0.
