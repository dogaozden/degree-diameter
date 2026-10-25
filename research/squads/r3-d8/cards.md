# Round r3-d8 (job thm-d8table, resumed session, 2026-10-25)

Goal: structured lifts of the split Cayley hexagon H(q) plus j = 2 hop matchings with diameter 8 and many copies M.
DGQ's table formula is M = 5*floor((q+5)/2): 20 at q = 4, 25 at q = 5, 30 at q = 7 (M >= 31 at q = 7 beats (10,8)).
Known so far: random lifts reach M about 12 (q = 4) and 10 to 12 (q = 5); best structured at q = 5 is M = 14 with 2
unreached; exact-cost annealing at q = 4, M = 20 reached 212 unreached pairs. Scorer: research/theorems/d8/liftdiam.

- c1 near-duality hops: anneal bijections points -> lines so that collinear points go to concurrent (or at least
  non-opposite) lines; use two of them as hops; lift test at q = 4, 5 against random matchings.
- c2 holonomy design: anneal Z_K flag voltages so that the q+1 geodesics between opposite elements carry >= K-1
  distinct voltages; use as the Z_K part of a Z_5 x Z_K lift (Z_5 = polygon cover).
- c3 calibration q = 4: push the M = 20 annealed lift (212 unreached) to 0, then M = 21, 22.
- c4 calibration q = 5: exact-cost annealing at M = 15, 18, 20.
- c5 structure analysis of valid / near-valid annealed lifts (q = 2, 3, 4): find the most non-random statistic.
- c6 duality hops at q = 3 with annealed labels (fixed duality matchings) against random matchings + annealed labels.
- c7 exact SAT search (pysat) for zero-holonomy "guaranteed-walk" label designs, j = 1 and j = 2, q = 2, 3, 4.
- c8 wildcard: an approach none of the other cards uses.
