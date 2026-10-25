# Handoff: job cell-16-7 (resume session session_01SiFUa6yem3dNwLbHS2XdrE, 2026-10-25): finished

Branch claude/cell-16-7-search-63p1wj (draft PR #311). Verified results (apsp_autw VALID, numpy rebuild byte-identical):
- **(16,7) 4,052,108**: research/frontier/sols/d16D7_hex13_typed61_K244_n4052108.sol (+ check file in
  research/squads/cells/d16D7/checks/); first version 4,051,254.
- spin-offs: **(14,7) 1,788,052** (d14D7_hex11_typed133_K62_n1788052), **(15,7) 2,497,075** (d15D7_hex11_typed133_K62_n2497075).
Theory and files: research/squads/cells/d16D7.md. Squad rounds r2, r3 and the follow-up are in research/squads/LOG.md.

Where it stopped: n = 4,022,340 + 2·61·(K + 2) with K = min(points, lines) = min(242, 243). Every method tried
(symmetric quotients of order 3, 9, 18; k-fixed tabu; ARW ILS; exhaustive light-vertex starts + polish) stops at 242
points, so more of the same is unlikely to pay. A different collineation group G (or no symmetry, with a heavier check)
might allow larger sets; the Hoffman ceiling is 471 orbits.
