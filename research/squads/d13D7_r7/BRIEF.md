# Squad round 7 (job cell-13-7): more pairwise-opposite points of H(13), for (16,7)

Goal: a set of more than 500 pairwise-opposite points of the split Cayley hexagon H(13). Every extra point adds 4
vertices to (16,7) (now 4,024,340 = 5 copies of H(13) + 4 * 500; table 4,022,340). Upper bound q^3 + 1 = 2198 (not
attained for q prime > 3). For comparison q = 11 reached 756 of 1332 and q = 7 reached 288 of 344, so 500 of 2198 at
q = 13 is probably far from the best.

Problem, scorer and rules: read research/squads/d13D7_r4/BRIEF.md. Points of H(13) = points of
Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,13); x, y opposite iff
B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 != 0 mod 13. Hexagon file research/d13D7/hex/hex_q13.bin
(402,234 points; format in the round 4 brief). Scorer (1 s):
  research/d13D7/tools/oppcheck research/d13D7/hex/hex_q13.bin P FILE   -> RESULT VALID pairwise_opposite m
FILE = one point index per line ('#' lines ignored).

Current best 500: research/squads/d13D7_r4/c2/best500_idx.txt, the union of orbits of a cyclic group of order 30
(generator research/squads/d13D7_r4/c2/best500_gen.txt = gens/f87769f8eb811fb6.txt), K = 4,749 good orbits; the exact
clique search was cut, so 500 is NOT proven optimal even for that group. Code for q = 13 (reuse it):
research/squads/d13D7_r4/c2/run13.py (driver: --mode cyc|pair), orbq13.py (orbits, good orbits, compatibility),
wclq2.c (exact weighted branch and bound + tabu; can warm start), replay13.py, runlog13.jsonl (98 groups tried; best
others 434 (pair 28 x 2), 417, 414, 405).
What worked at q = 11: 720 = exact clique for <a> x <b> (a order 15 on a 5-dim U, b order 5 on U^perp), then 756 =
warm-started tabu on the orbit graph of the smaller subgroup <a b^2> of order 15, seeded with the 720 solution
(research/squads/d13D7_r4/c1/sweep.py), and 756 again from a non-abelian block group of order 72
(research/squads/d13D7_r6/c1/nonab.py). At q = 9, a seeded point-level ILS added 9 points to an orbit union.

Rules: one heavy process at a time per card, single thread, `timeout 900 nice -n 10`, <= 600 s CPU per run, <= 1.5 GB
RAM, no git, write only in research/squads/d13D7_r7/<card>/. Save your best as <card>/best_idx.txt (point indices,
checked with oppcheck) plus generators if any. Append ONE JSON line to research/squads/d13D7_r7/scoreboard.jsonl:
{"card": "cN", "q": 13, "idea": "...", "code": "...", "command": "...", "score": m, "valid": true|false, "file": "...", "next": "..."}
and reply in at most 5 lines. HARD time box: 25 minutes of wall time from your start, then write the scoreboard line
and stop (Opus must rebuild and check a 4-million-vertex graph afterwards). Do not leave anything running.

c1 WARM-STARTED SUBGROUPS of the 500 group: h of order 30; its subgroups <h^2> (15), <h^3> (10), <h^5> (6), <h^6>
   (5), <h^10> (3) have bigger orbit graphs that still contain the 500 solution as a clique. Seed wclq2's tabu with
   that clique and look for heavier ones (the q = 11 step 720 -> 756). Also give the order-30 group itself a longer
   exact/tabu run.
c2 BLOCK PAIRS designed from q - 1 = 12 = 4*3 and q + 1 = 14 = 2*7 (the q = 11 winner had a of order 15 = 3*5 mixing a
   q+1 part and a q-1 part on a 5-dim U, b of order 5 on the 2-dim U^perp): run13.py --mode pair with |a| in {21, 42,
   12, 24, 28, 84, 6, 7, 14} and |b| in {3, 7, 2, 4, 6, 12, 14}, product 20..300, skipping pairs already in
   runlog13.jsonl; also k = 4 (4 + 3 blocks). Exact clique where the orbit graph is small, tabu otherwise.
c3 NON-ABELIAN groups at q = 13: port research/squads/d13D7_r6/c1/nonab.py (two non-commuting isometries of small
   order, closure <= 2000 by BFS on matrices; dihedral, A4, S3 x Z7, Frobenius groups 7:3, 13:3, 13:4 ...) to q = 13
   using orbq13.py's arithmetic; orbits, exact/tabu max-weight clique.
c4 POINT-LEVEL LOCAL SEARCH seeded from the 500 set: tabu/ILS on single points (add a point opposite to all; 1-swap
   and 2-for-1 swaps using counts of conflicting set members; plateau moves; perturbation), all in C for speed (B is
   a 7x7 bilinear form; precompute coordinates). The 500 set may be locally improvable because it was only a cut
   search on a symmetric orbit graph.
