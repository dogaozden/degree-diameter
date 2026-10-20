# Problem 4, diameter 4 (p4-d4-opus) — interim, saved by the main session from the agent's message (23:35)

1. NOTE.md open problem 3 is answered NO: q²+1 line copies with stand-ins cannot exist for odd q. Dual form: M = point
   set of W(3,q), at most 1 point on each totally isotropic line outside the spread S, at most 2 on each S-line. Double
   counting over points outside M forces no S-line to hold 2 points, so M would be an ovoid of W(3,q), which does not
   exist for odd q. The same argument covers the j ≥ 3 relaxation only for 0/1 sets. (Correction, ~00:20: weighted 3-covers of Q(4,q) exist for q = 3, 5, 7, so at odd j ≥ 3 the gap closes: n_b(q+1+j,4) ≥ 2(q²+1)(q+1+j) for those q.)
2. Exact optima (CP-SAT): q=3: 8; q=5: 21 (matches the old ILP). q=7: ≥ 40 by tabu and Singer-subgroup ILP, so
   890 > AS(7) = 882. That cell is a Moore cell (GQ exists), so it is only evidence.
3. q=9 is the live case: |M| ≥ 61 is needed to beat 1782. The antipodal-pair subfamily gives only 50 so far. General
   tabu search running.
4. Δ = 6, 8, 9, 10, 12, 14 are Moore cells at D = 4 (GQ(Δ−1,Δ−1) exists), so the table is optimal there. In table
   range the only open D = 4 cells are 7, 11, 13, 15, 16. Next: tabulate Δ > 16 against our own constructions.
Code: research/p4/d4 (w3k.py, cp_m.py, pq.py, hs.c, groups.py).

## Update ~00:20 (from the agent's messages)
- Upper bound, proved: with stand-ins, |M| ≤ q²−q+2 for odd q. If a spread line holds 2 points of M, its q−1 other
  points each see at most q points of M, and together they see all of M except those 2. If no spread line holds 2,
  Tallini's q²−q+1 applies.
- Weighted 3-ovoids of W(3,q) exist for q = 3, 5, 7 (CP-SAT; q = 5 even has a 0/1 3-ovoid). They are weighted 3-covers
  of Q(4,q), so Cor. B1 gives n_b(q+4,4) ≥ 2(q²+1)(q+4) with no stand-ins; with 2-ovoids added, for every odd j ≥ 3.
  If this holds for all odd q, B2's odd case improves from 2q²Δ to 2(q²+1)Δ for Δ ≥ q+4 (first such cell Δ = 41;
  no table cell ≤ 16 affected).
- q = 9 stand-in best 56 (needs 61 to beat 1782). q = 11, 13 runs started. Cloud: C (weighted 3-ovoids, branch
  p4-d4-3) session_01FXg91CE77JRUHqDm5hMWFJ; A and B launching.
- Theorem B dual builder works end to end: graphs/q4st_q7_n890.json passes verify_record (9,4) (a Moore cell; pipeline
  check only).
