# w19 NOTES (handsoff-49): refinement ladder from the best Haar near misses

Start: 01:12 UTC. Stop: 02:55 UTC. Card: cards.md, "## w19".

## Setup (done)
- Haar seeds (read from the edge lists, vertex 0's neighbours give S):
  - G = meta 101 25 5 (N = 2,525, n = 5,050, Haar cost 2): S = {(0,0),(0,3),(1,7),(49,15)}  [index a + 101 j]
  - G = meta 104 24 7 (N = 2,496, n = 4,992, Haar cost 4): S = {(0,0),(70,11),(43,14),(17,22)}
- quot19.py (w19): for every normal subgroup K containing G' = [G,G] (G/K abelian), writes the k+k base
  (k = [G:K]) and the group table of K (identity = 0). Lift convention = flift/wl2: edge (u,x) ~ (v, g x).
  Initial voltages are the Haar voltages, so the lift IS the Haar graph (checked: cost scales as k times Haar cost).
- lann.c (SA, uniform voltage moves + base 2-switches) and ltabu.c (full-neighbourhood tabu over voltages, plus base
  2-switches, kicks after NOIMP steps). Cost = sum over base roots of far lift vertices; Haar-equivalent cost =
  cost / k (per-fibre average). Cost 0 = diameter 9.

## Calibration
- Z_101 quotients: K0 (whole group, base 1+1) cost 2 = Haar cost 2; K1 (5+5 over order 505) starts at 10 = 5 x 2;
  K2 (25+25 over Z_101) starts at 50 = 25 x 2. As expected.
- Speed: about 5,600 evaluations/s for lann (early exit), about 2,500/s for ltabu full scans.

## Results so far
- SA (lann), 5+5 over Z_101 x| Z_5 (order 505), T 1.5 to 0.1 for 60 s, and T 20 to 2 for 25 s: best stays at the
  Haar start (10). Random voltage moves are big jumps (a new voltage replaces a whole perfect matching between two
  fibres), so the walk leaves the cost-10 basin and does not come back.
- ltabu (full neighbourhood, TT 10): 15 steps in 60 s, no improvement below 10.

## Update 02:10 (all results: no lift below the Haar floor)
- ltabu, 5+5 over order 505 (Z_101 x| Z_5), start = Haar S0 cost 10 (lann units = 5 x Haar 2): 470 s, no improvement.
- ltabu from other cost-2 Haar sets S7, S15 (140 s each): stuck at 10. 48 cost-2 sets exist (w11/hits); quotients in q/m101_K5/.
- ltabu, 3+3 over order 832 (4992 group), start 12 = 3 x 4: S0, S30, S60 (130 s each): stuck at 12.
- fa (far-pair-aimed moves, q/ = new voltages that shortcut sampled far pairs, exact check of the top ones):
  5+5 Z_101: 470 s, 1,805 steps, stuck at 10. 25+25 over Z_101 (start 50): 150 s, stuck at 50.
  4+4, 6+6, 8+8 over the 4992 group (start 16, 24, 32): 110 s each, stuck at the start.
- Reading: a single voltage change replaces a whole matching of |K| lift edges. At a Haar optimum it costs +30..+90
  in lann units (the cost is 10 at the optimum), so every 1-move neighbour is much worse; greedy and tabu walks wander
  at 50..100 and never return below the start. The Haar optima look like isolated deep minima of the k+k voltage space.
- Verdict for this card: no n > 4,970 and no cost below the Haar floor at n = 5,050 or 4,992 from the k+k lifts tried.
- Next idea (not run): pair moves (two voltages changed together, chosen so that the new edges shortcut the same far
  pair), or a symmetric ansatz (a Z_5 or Z_3 automorphism of the base) to shrink the voltage space.

## Update 02:18 (checks and two-step lookahead)
- Verified the quotient lifts are the Haar graphs: score48 on the rebuilt 5+5 lift of S0 gives far = 2,525 (= N x cost / 2
  with Haar cost 2), and the 3+3 lift of the 4992 set gives far = 4,992 (= 2,496 x 4 / 2), identical to score48 on
  w11/out/m101_k25_r5_c2.edges (far 2,525) and on w13/best_haar_104_24_7_c4.edges (far 4,992).
- fa2 (two-step lookahead: change one voltage, then the best repair on another edge, exact cost of the pair):
  5+5 Z_101 from S0 and S7, 80 s each, 3,200-3,400 pairs each: best stays 10. 3+3 over 4992 group from S0: best stays 12.
  (First version scored the repair on the same edge only; fixed by excluding the changed edge.)
- Totals this run: about 2 hours of search, roughly 4 CPU-hours-equivalent of single-core evaluation in ltabu, lann, fa, fa2.
  No cost below the Haar floor at any n tried; no record. Files: runs/ (best bases), q/ (quotient bases and tables).

## Final table (lowest cost found per group and k; lann units = k x Haar cost; cost 0 = record)
| group (n) | k (base) | Haar start | lowest found | tools |
|---|---|---|---|---|
| Z_101 x| Z_25 (5,050) | k=1 | 2 (Haar floor) | - |
| same | 5 (5+5, order 505) | 10 | 10 | ltabu x4 sets, fa x5 sets, fa2 x4 sets |
| same | 25 (25+25, order 101) | 50 | 50 | fa 150 s |
| Z_104 x| Z_24 (4,992) | k=3 | 12 | 12 | ltabu x3, fa2 x1, fa x1 |
| same | 4 (4+4, order 624) | 16 | 16 | fa x3, fa2 x1 |
| same | 6 (6+6, order 416) | 24 | 24 | fa x1 |
| same | 8 (8+8, order 312) | 32 | 32 | fa x2 |
Scoreboard: no line appended (no improvement below the Haar start at any n).

## Rebuild
- `python3 quotm.py 101 25 5 ../w11/hits/m101_k25_r5.txt q/m101_K5 5` (bases S<i>.base over the order-505 subgroup),
  same with `104 24 7 ../w11/hits/m104_k24_r7.txt q/m104_K<k> k` for k = 3, 4, 6, 8.
- `./lann q/m101_K5/K.bin q/m101_K5/S0.base 9 SECS SEED OUT` (SA); `./ltabu ...` (tabu); `./fa ...` (far-pair moves);
  `./fa2 ...` (two-step lookahead). Each writes OUT.best.txt; cost 0 writes OUT.edges and prints RESULT FOUND.
- Lift of a base file: edges (u,x) ~ (v, g x) with u*|K|+x labels (checked against score48, see above).
