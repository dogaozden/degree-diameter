# Problem 4, diameter 4 (p4-d4-opus) — interim, saved by the main session from the agent's message (23:35)

1. NOTE.md open problem 3 is answered NO: q²+1 line copies with stand-ins cannot exist for odd q. Dual form: M = point
   set of W(3,q), at most 1 point on each totally isotropic line outside the spread S, at most 2 on each S-line. Double
   counting over points outside M forces no S-line to hold 2 points, so M would be an ovoid of W(3,q), which does not
   exist for odd q. The same argument covers the j ≥ 3 relaxation.
2. Exact optima (CP-SAT): q=3: 8; q=5: 21 (matches the old ILP). q=7: ≥ 40 by tabu and Singer-subgroup ILP, so
   890 > AS(7) = 882. That cell is a Moore cell (GQ exists), so it is only evidence.
3. q=9 is the live case: |M| ≥ 61 is needed to beat 1782. The antipodal-pair subfamily gives only 50 so far. General
   tabu search running.
4. Δ = 6, 8, 9, 10, 12, 14 are Moore cells at D = 4 (GQ(Δ−1,Δ−1) exists), so the table is optimal there. In table
   range the only open D = 4 cells are 7, 11, 13, 15, 16. Next: tabulate Δ > 16 against our own constructions.
Code: research/p4/d4 (w3k.py, cp_m.py, pq.py, hs.c, groups.py).
