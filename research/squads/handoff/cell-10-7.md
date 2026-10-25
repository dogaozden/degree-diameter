# Handoff: job "cell-10-7" (bipartite (10,7) and the hexagon-cover spin-offs)

Branch `claude/bipartite-10-7-uvpxk9`, draft PR #305. Sessions on 2026-10-24/25. Full notes:
research/squads/cells/d10D7.md (§9 covers this job), squad rounds 1–6 in research/squads/LOG.md, check files in
research/d10D7/checks/.

## State

| cell | table | ours | status |
|---|---|---|---|
| (7,7) | 23,436 | 23,580 | apsp VALID |
| (9,7) | 117,648 | 118,224 | apsp VALID |
| (10,7) | 224,694 | 225,128 | apsp VALID |
| (11,7) | 398,580 | 407,162 | apsp VALID |
| (12,7) | 664,300 | 680,068 | apsp VALID |
| (13,7) | 1,062,936 | 1,064,448 | apsp VALID (source ranges, apsp_range.c) |
| (14,7) | 1,771,560 | 1,774,584 | apsp VALID (source ranges) |
| (15,7) | 2,480,184 | 2,484,720 | symmetric check VALID (level 0 + hubs); full apsp not run |
| (16,7) | 4,022,340 | 4,025,508 | candidate: partial check only (hubs + 12,800 base vertices) |

All of these are the table's hexagon covers with every matching equal to one bijection M, plus hub vertices for
"freed pairs" (B2 condition, research/d10D7/checks/B2_hubs_CHECK.md). The gain is set by a partial ovoid of H(q):
pairwise opposite points, or for q = 9 (where a duality exists) pairwise non-collinear points. Lines are free, since a
Hermitian spread gives q³+1 opposite lines.

## The point sets and what limits them

- q = 8 (10,7): 217 = {v_i} ∪ {v_a + ω v_b + ω³ v_c}, an S7 × C3-invariant set on a W(5,2) subgeometry (§9.7). It
  is robust: every search, kick and subgroup orbit union tried returns 217 or less. The upper bound is 457 (§9.6). This
  is the (10,7) bottleneck; each extra point is +2 vertices.
- q = 7: 288, one W(E7)-orbit mod 7. Every E7-subsystem union caps at 288.
- q = 11: 756, the only pairwise opposite W(E7)-orbit mod 11, and maximal.
- q = 13: 792, from unions of W(E6)-orbits mod 13. It has not been extended by tabu; that is worth trying.
- q = 5: 72 by tabu; the E7 unions give at most 60.
- q = 9 (non-collinear): 4,291 (orbits of an element of order 7 in SL(3,9)); the Hoffman bound is 6,643. If it ever
  reaches 5,895, the (12,7) hub graph can be the 3-level cover of H(5) (11,790 hubs per side), giving 687,880.

## Tools

- d7hex.c `b2` / `b2dual`: builds M for freed sets.
- dual/xgen.c: (2j+1)-level cover with a hub layout.
- dual/mkhubs_*.py: hub layouts.
- ovoid/potabu2.c: tabu for partial ovoids of any H(q).
- ovoid/e7/run_e7q.py, subq.py: E7 orbit unions for any prime q.
- ovoid/subgeo.py, orbsearch.py: the q = 8 subgeometry and orbit unions.
- checks/apsp_range.c and checks/run_ranges.sh: all-pairs check split over source ranges, so several processes can
  share it.

## Ideas not done

- Relaxed B2 (freed points at distance 4, with line pairs that have an isomorphic midpoint structure). This is the only
  route left beyond 217 at q = 8; the q = 5 trial (r4/c7) did worse than opposite sets.
- Tabu from the 792 set at q = 13, and E7 unions at q = 17, 19 (outside the table range).
- (8,7) 40,586 and the Δ = q+1 cells use other constructions, which we did not touch.
