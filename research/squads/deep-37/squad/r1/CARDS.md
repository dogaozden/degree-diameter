# deep-37 round 1 cards (one line each)
- c1 census168: all (3,7) graphs at n = 168 invariant under groups with an element of order 7 (orders 14, 21, 28, 42, 56, 84, 168), via gen_gsets.sh + orbdfs; count isomorphism classes (we know 2). Score: number of classes.
- c2 grow: seeds (C168.1, the new AGammaL(1,8) 168 graph, c1's census) -> 170 by insertion (bin/insert) + a repair local search; also "designed" insertion that removes the edges carrying the fewest unique geodesics. Score: far at 170 (beat 46).
- c3 n169: n = 169 (85 + 84, three perfect degree-2 vertices in A) with a symmetry rotating the deficient vertices; symmetric local search or an orbdfs variant with per-orbit degrees. Score: far at 169 (prior 144).
- c4 hubs: G-invariant graphs at 170 for {2,3}-groups with hub stabilisers (A4, C2xA4, S4, SL(2,3), C3xS3, ...); orbdfs on small trees, symmetric SA/breakout on big ones. Score: far at 170 / families settled.
- c5 n180: exact orbdfs sweeps at n = 180 (90 per side) for groups of order 20, 30, 36, 60, 120 with non-free parts. Score: families settled / any far 0.
- c6 lns-exact: large-neighbourhood search with exact completion (delete the edges in a region around the far pairs or a union of automorphism orbits; enumerate all cubic completions; keep the best) on the far-46 and far-60 graphs. Score: far at 170.
- c7 wildcard: an approach none of c1-c6 uses (list given). Score: far at n >= 169.
