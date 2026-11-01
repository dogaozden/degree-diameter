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

## 23:20-23:55 lead (a), minimal groups, squad round 1
- Lead (a): src/insert.c (exhaustive pair insertion, bit-parallel scoring) reproduces c1's floors on C168.1: 2-edge
  best 46 (252 of the 31,626 choices), 3-edge best 48. On the new AGammaL(1,8) graph: 2-edge best 96.
  Why: C168.1 is uniformly loaded. Every edge is the only geodesic for exactly 36 same-side pairs at distance 6
  (each vertex has 53 same-side vertices at distance 6: 18 with one geodesic, 27 with two, 8 with three). Removing
  two edges loses 72 such pairs; the detour through the new pair (a - y - x - b) is 2 longer, so a lost pair is
  rescued only if one end is near the other removed edge. The best geometry (removed edges at distance 5-6) rescues 30:
  far = 72 - 30 + 4 (pairs at the new vertices) = 46. In the new 168 graph edges carry 60 or 80 such pairs.
- Minimal groups. If Aut(G) contains an element of order 5 (generating P = C5, which acts freely at 170) and
  Aut(G) != P, then Aut(G) contains a minimal overgroup M of P: either P is normal in M and |M:P| is prime (M = C10,
  D5 or C15), or M = K:P with K a minimal P-invariant {2,3}-subgroup, elementary abelian of order 2^4 or 3^4
  ((C2)^4:C5 = SmallGroup(80,49), (C3)^4:C5 = SmallGroup(405,15)). The last cannot act: a 3-group vertex stabiliser in
  a connected cubic graph has order <= 3, so its orbits have size >= 135 > 85. So settling all G-sets of D5, C10, C15
  and (C2)^4:C5 at 170 settles every graph with an automorphism of order 5 other than |Aut| = 5.
- Exclusions built into orbdfs: non-faithful G-sets; twin lemma (a non-identity colour-preserving element fixing all of
  one side makes two vertices twins; a vertex with a twin sees at most 65 < 85 same-side vertices within distance 6).
- Knuth estimates (300 probes; unreliable by 10-30x either way): C15: 25 G-sets left after exclusions, ~5e6 nodes in
  total. D5: 82 G-sets, ~1.5e11 (one G-set 1e11). C10: 65 left, ~9e10 (one 8e10). The far-60 family's D5 G-set
  (3 orbits of size 5 + 7 of size 10 per side) ~2.3e8: running.
- Fail-first fill order (DYN=1): same 96 solutions at 168, 3.6M vs 4.7M nodes on F20rev b=3; not a real gain.
- Squad round 1 launched at 23:45Z (7 cards, squad/r1/CARDS.md).
