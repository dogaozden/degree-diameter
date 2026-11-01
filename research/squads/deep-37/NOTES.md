# deep-37 working notes (Opus, Nov 1 2026, branch claude/deep-37-d3d7-c59pr7)

Start 2026-11-01T22:39:08Z. Target: bipartite (3,7) graph on 170 vertices (table 168).

## 22:39-23:20 setup, exact solver, first results
- Far-60 D5 graphs of handsoff-37 (r3a, r3b fresh56; non-isomorphic) have |Aut| = 20: F20 = C5 x| C4 with the C4
  colour-reversing (its square is the D5 involution, 3 fixed vertices per side). Far pairs: 5 orbits (10, 20, 10, 10, 10),
  all same-side at distance 8, on 100 of the 170 vertices.
- src/orbdfs.c: exact search for G-invariant cubic bipartite graphs of diameter <= D on a given G-set (any finite
  permutation group, non-free orbits and colour-reversing elements allowed). Generalises jsearch: BFS orbit discovery,
  gauge fixing of untouched orbits by the G-equivariant maps (centraliser), collision pruning (delta = 127 - n/2).
  Validated against brute force (src/brute_ginv.py) on 13 small G-sets (S3 free/non-free, D5, colour-reversing C4, D5,
  F20): identical isomorphism classes for D = 5, 7 and 13.
- Calibration: F21 (r2f's G-set, n = 168): exhaustive in 8.5 s (619k nodes), 96 solutions in TWO isomorphism classes:
  C168.1 and a NEW (3,7) graph on 168 vertices: girth 8, |Aut| = 168 = AGammaL(1,8) = SmallGroup(168,43), vertex orbits
  56 (stab C3), 28 (stab C6), 84 (stab C2). apsp: VALID at D = 7, INVALID at D = 6. records/n168_new_girth8_aut168.edges.
- F20 colour-reversing G-sets at 170 (a regular orbits + b orbits of size 10, 2a + b = 17): b = 1, 3: complete, none.
