# Handoff: job cell-16-7 (resume session session_01SiFUa6yem3dNwLbHS2XdrE, 2026-10-25)

Branch claude/cell-16-7-search-63p1wj (draft PR #311). Verified best: **(16,7) 4,051,254**
(research/frontier/sols/d16D7_hex13_typed61_K237_n4051254.sol, check in research/squads/cells/d16D7/checks/).
Theory and files: research/squads/cells/d16D7.md (typed levels HDHDH; n = 4,022,340 + 2·61·(K + 2), K = min of the two
orbit-graph independent sets).

To raise it: find larger independent sets in research/squads/d16D7_r2/og_pts.txt and og_lines.txt (orbit graphs;
scorer ogscore.py). Best known: 240 / 240 (squad r2 card c8, symmetric under the order-9 group <h, F>; quotients in
research/squads/d16D7_r3/quot/, regenerate with cells/d16D7/ogquot.py). Then build and check in a scratch dir:
  hexgen2 13; typed5s (cells/d16D7/typed5s.c) make with og2el.py-expanded sets and UNFP/UNFS = the 2+4 orbit
  partial ovoid/spread from popp.c; hubcheck; typed5s edges; apsp_autw EDGES 16 7 2 AUT (about 11-17 min, 2 threads).
Squad rounds: r2 (done, logged), r3 (symmetric quotients, launched 04:21 UTC).
