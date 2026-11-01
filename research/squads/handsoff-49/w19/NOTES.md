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
