# Handoff: job cell-16-7 (resume session session_01SiFUa6yem3dNwLbHS2XdrE, 2026-10-25)

Branch claude/cell-16-7-search-63p1wj (draft PR #311). Verified bests (apsp_autw VALID, numpy rebuild byte-identical):
- **(16,7) 4,052,108**: research/frontier/sols/d16D7_hex13_typed61_K244_n4052108.sol (+ check file in
  research/squads/cells/d16D7/checks/). Earlier 4,051,254 (same construction, smaller sets).
- spin-offs: **(14,7) 1,788,052** (d14D7_hex11_typed133_K62_n1788052), **(15,7) 2,497,075** (d15D7_hex11_typed133_K62_n2497075).
Theory and files: research/squads/cells/d16D7.md (typed levels; n = 4,022,340 + 2·61·(K + 2), K = min of the two
orbit-graph independent sets; 242 points / 243 lines now).

To raise (16,7): larger independent sets in research/squads/d16D7_r2/og_pts.txt (points are the bottleneck at 242) and
og_lines.txt. What works: sets symmetric under the order-9 group <h, F> (quotients research/squads/d16D7_r3/quot/, from
cells/d16D7/ogquot.py), annealed (research/squads/d16D7_r3/c1/wsa, source r2/c8/wsa.c), expanded, then k-fixed tabu polish
(r2/c2/ktabu). The order-9 quotient of the points seems capped at 240; polishing gave 242. Order 18 is too constrained.
Build and check: hexgen2 13; og2el.py; typed5s make (UNFP/UNFS = the 2 + 4 orbit partial ovoid/spread from popp.c);
hubcheck; typed5s edges; apsp_autw EDGES 16 7 2 AUT (6-17 min).
Squad rounds r2, r3 done and logged in research/squads/LOG.md.
